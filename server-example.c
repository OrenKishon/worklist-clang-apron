#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <pthread.h>

#define RX_PACKET_SIZE 1024
#define RX_BUFFER_SIZE (RX_PACKET_SIZE * 8)
#define MAX_CONSUMER_READ_SIZE 500

static char rx_buff[RX_BUFFER_SIZE];
static int buff_ind;

static void sleep_seconds_with_deviation(int sec)
{
    int max_deviation = 1000;

    /* random deviation in usec */
    useconds_t deviation = rand() % (2 * max_deviation) - max_deviation;

    /* Simulate byte rate of a packet in 1 second with up to 1 msec deviation */
    usleep(1000000 * sec + deviation);
}

static void receive_request(int *ind_from, int *size)
{
    *ind_from = rand() % RX_BUFFER_SIZE;
    *size = rand() % MAX_CONSUMER_READ_SIZE;

    sleep_seconds_with_deviation(2);
}

static void *consumer_func(void *arg)
{
    char buf[MAX_CONSUMER_READ_SIZE];
    /* XXX: Should later be absolute times instead of indices */
    int ind_from, size, size_temp;

    while (1)
    {
        receive_request(&ind_from, &size);        
        if (ind_from+size < RX_BUFFER_SIZE)
            memcpy(buf, rx_buff + ind_from, size);
        else
        {
            size_temp = RX_BUFFER_SIZE - ind_from;
            memcpy(buf, rx_buff + ind_from, size_temp);
            memcpy(buf + size_temp, rx_buff, size - size_temp);
        }
        printf("Consumer\n");
    }
}

static int fill_buffer_with_rx(char *p)
{
    int i;

    sleep_seconds_with_deviation(1);
    printf("RX\n");

    for (i = 0; i < RX_PACKET_SIZE; i++)
        *p = i;

    return i;
}

int main(void)
{
    pthread_t consumer_thr;
    int ret;
    buff_ind = 0;

    if (pthread_create(&consumer_thr, NULL, consumer_func, NULL))
    {
        perror("pthread_create");
        return 1;
    }

    while (1)
    {
        ret = fill_buffer_with_rx(rx_buff + buff_ind);
        buff_ind = buff_ind + ret;
        buff_ind = buff_ind % RX_BUFFER_SIZE;
    }
}
