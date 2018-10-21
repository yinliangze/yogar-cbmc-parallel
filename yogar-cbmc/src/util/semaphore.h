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

extern int  sem_id;
extern int  shm_refinement_id;
extern int  shm_clause_id;
extern int  shm_process_id;
extern char *refinement_buf;
extern int  *clause_buf;
extern int  *process_id_buf;  // buf[0] for process_id, buf[1] for process_num, buf[2] for sync

#define IPCKEY_REFINEMENT  0x366378
#define IPCKEY_CLAUSE      0x176435
#define IPCKEY_PROCESS     0x265471
#define SHARED_MEMORY_SIZE 10485760

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

