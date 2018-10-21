#include <iostream>
#include <string>
#include <vector>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <fstream>

using namespace std;

union semun
{
    int val;
    struct semid_ds *buf;
    unsigned short *arry;
};

static int set_semvalue(int& sem_id);
static void del_semvalue(int& sem_id);
static int semaphore_p(int& sem_id);
static int semaphore_v(int& sem_id);

void attach_shared_memory();
void detach_shared_memory();

int  sem_id            = 0;
int  shm_refinement_id = 0;
int  shm_clause_id     = 0;
int  shm_process_id    = 0;
char *refinement_buf   = NULL;
int  *clause_buf       = NULL;
int  *process_id_buf      = NULL;  // buf[0] for process_id, 
								   // buf[1] for process_num, 
								   // buf[2] and buf[3] for sync
								   // buf[4] for verification results
								   // buf[5] for write verification result
								   // buf[6] and buf[7] for sync of detach
								   // buf[8] for total number of refinements
								   // buf[9] for solving time, buf[10] for total time

#define IPCKEY_REFINEMENT  0x366378
#define IPCKEY_CLAUSE      0x176435
#define IPCKEY_PROCESS     0x265471
#define SHARED_MEMORY_SIZE 10485760

string cmm = "./yogar-cbmc --no-unwinding-assertions --32 --parallel ";
int thread_num = 2;

string get_file_name(int thread_num, string share_manner)
{
	char strbuf[10];
	sprintf(strbuf, "%d", thread_num);
	return "results_" + share_manner + "_" + string(strbuf);
}

string get_org_file(string file_name)
{
	bool again = false;
	int i;
	for (i = file_name.size() - 1; i >= 0; i--)
	{
		if (file_name[i] == '/')
		{
			if (again)
				break;
			else
				again = true;
		}
	}
	return file_name.substr(i + 1, file_name.size() - i - 1);
}

int main(int argc, char* argv[])
{
	string share_manner = "RCS";
	// check the parameters
	if(argc < 2)
	{
		std::cout << "Parameter Error! Using ./parallel-yogar-cbmc --help for more information \n";
		return 0;
	}
	
	if (string(argv[1]) == "--help")
	{
		std::cout << " COMMAND: ./parallel-yogar-cbmc <input_file> [--thread-num n] [--share SM]\n";
		std::cout << " Default value of n is 2;\n";
		std::cout << " SM can be NS, RS, CS and RCS, Default value is RCS;\n";
		return 0;
	}
	
	string file = argv[1];
	
	for (int i = 2; i < argc; i++)
	{
		if (string(argv[i]) == "--thread-num")
		{
			thread_num = atoi(argv[i+1]);
			i++;
		}
		if (string(argv[i]) == "--share")
		{
			share_manner = string(argv[i+1]);
			i++;
		}
	}
	
	cmm += "--share " + share_manner + " ";
	
	// obtain the parallel verification command	
	
	string parallel_cmm;
	system("mkdir tmp");
	for (int i = 0; i < thread_num; i++)
	{
		char buf[20];
		sprintf(buf, "%i", i);
		string temp_file = "tmp/temp_file" + string(buf) + ".i";
		
		system(("cp " + file + " " + temp_file).c_str());
		
		parallel_cmm += cmm + temp_file + " & ";
	}
		
	std::cout << parallel_cmm << "\n";
	
	// create and initial shared memory	
	attach_shared_memory();
	
	string result_file = get_file_name(thread_num, share_manner);
	ofstream out(result_file.c_str(), ios::app);
	out << get_org_file(file) << " ";	
	out.close();
	
	// execute the parallel verification
	system(parallel_cmm.c_str());

	// wait until all processes terminate
	while(1)
	{
		if (refinement_buf[0] == '0' + thread_num)
		{
			usleep(100000);
			break;
		}
		usleep(5000);
	}

	// delete the shared memory
	detach_shared_memory();
	
	system("rm -rf temp");
	
	return 0;	
}

static int set_semvalue(int& sem_id)
{
    //用于初始化信号量，在使用信号量前必须这样做
    union semun sem_union;

    sem_union.val = 1;
    if(semctl(sem_id, 0, SETVAL, sem_union) == -1)
        return 0;
    return 1;
}

static void del_semvalue(int& sem_id)
{
    //删除信号量
    union semun sem_union;

    if(semctl(sem_id, 0, IPC_RMID, sem_union) == -1)
        fprintf(stderr, "Failed to delete semaphore\n");
}

static int semaphore_p(int& sem_id)
{
    //对信号量做减1操作，即等待P（sv）
    struct sembuf sem_b;
    sem_b.sem_num = 0;
    sem_b.sem_op = -1;//P()
    sem_b.sem_flg = SEM_UNDO;
    if(semop(sem_id, &sem_b, 1) == -1)
    {
        fprintf(stderr, "semaphore_p failed\n");
        return 0;
    }
    return 1;
}

static int semaphore_v(int& sem_id)
{
    //这是一个释放操作，它使信号量变为可用，即发送信号V（sv）
    struct sembuf sem_b;
    sem_b.sem_num = 0;
    sem_b.sem_op = 1;//V()
    sem_b.sem_flg = SEM_UNDO;
    if(semop(sem_id, &sem_b, 1) == -1)
    {
        fprintf(stderr, "semaphore_v failed\n");
        return 0;
    }
    return 1;
}

void attach_shared_memory()
{
    // create semaphore
    if ((sem_id = semget((key_t)1234, 1, 0666)) != -1)
    	del_semvalue(sem_id);
	sem_id = semget((key_t)1234, 1, 0666 | IPC_CREAT | IPC_EXCL);

	// initial semaphore
	if(!set_semvalue(sem_id))
	{
		fprintf(stderr, "Failed to initialize semaphore\n");
		exit(EXIT_FAILURE);
	}

	// create 10MB shared memory
	if ((shm_refinement_id = shmget(IPCKEY_REFINEMENT, SHARED_MEMORY_SIZE, 0666)) != -1)
		shmctl(shm_refinement_id, IPC_RMID, NULL);
	shm_refinement_id = shmget(IPCKEY_REFINEMENT, SHARED_MEMORY_SIZE, 0666 | IPC_CREAT | IPC_EXCL);
	if(shm_refinement_id == -1)
	{
		printf("shmget error\n");
		exit(EXIT_FAILURE);
	}

	// attach shared memory
	refinement_buf = (char *)shmat(shm_refinement_id, NULL, 0);
	
	// initial refinement_buf
	refinement_buf[0] = '0';
	refinement_buf[1] = '\0';
	
	// create 10MB shared memory
	if ((shm_clause_id = shmget(IPCKEY_CLAUSE, SHARED_MEMORY_SIZE, 0666)) != -1)
		shmctl(shm_clause_id, IPC_RMID, NULL);
	shm_clause_id = shmget(IPCKEY_CLAUSE, SHARED_MEMORY_SIZE, 0666 | IPC_CREAT | IPC_EXCL);
	if(shm_clause_id == -1)
	{
		printf("shmget error\n");
		exit(EXIT_FAILURE);
	}

	// attach shared memory
	clause_buf = (int *)shmat(shm_clause_id, NULL, 0);
	
	// initial clause_buf
	clause_buf[0] = 1;
	
	// create 4 int shared memory
	if ((shm_process_id = shmget(IPCKEY_PROCESS, 4 * sizeof(int), 0666)) != -1)
		shmctl(shm_process_id, IPC_RMID, NULL);
	shm_process_id = shmget(IPCKEY_PROCESS, 11 * sizeof(int), 0666 | IPC_CREAT | IPC_EXCL);
	if(shm_process_id == -1)
	{
		printf("shmget error\n");
		exit(EXIT_FAILURE);
	}

	// attach shared memory
	process_id_buf = (int *)shmat(shm_process_id, NULL, 0);
	
	// initial clause_buf
	process_id_buf[0] = 0;
	process_id_buf[1] = thread_num;
	process_id_buf[2] = 0;
	process_id_buf[3] = 0;
	process_id_buf[4] = 2;
	process_id_buf[5] = 0;
	process_id_buf[6] = 0;
	process_id_buf[7] = 0;
	process_id_buf[8] = 0;
	process_id_buf[9] = 0;
	process_id_buf[10] = 0;
}


void detach_shared_memory()
{
    // detach shared memory
    if(shmdt(refinement_buf) == -1)
       perror(" detach error ");
       
    if(shmdt(clause_buf) == -1)
       perror(" detach error ");
       
    if(shmdt(process_id_buf) == -1)
       perror(" detach error ");

    // delete shared memory and semaphore
    del_semvalue(sem_id);
    
    if (shmctl(shm_refinement_id, IPC_RMID, NULL) == -1)
        perror(" delete error ");
    if (shmctl(shm_clause_id, IPC_RMID, NULL) == -1)
        perror(" delete error ");
    if (shmctl(shm_process_id, IPC_RMID, NULL) == -1)
        perror(" delete error ");
}
