package test;

public class Sort_Bubble {
	
	public static void main(String[] args) 
    {               
		int[] numbers=new int[100];
        for(int i=0;i<100;i++)
        	numbers[i] = (int)(Math.random()*(100000+1));//0-10000
        
//        System.out.println("排序前:");
//       printArr(numbers);

		//long setdataBegin = System.nanoTime();
        bubbleSort(numbers);
       
        //long setdataEnd = System.nanoTime();
//        System.out.println("运行时间:"+(setdataEnd-setdataBegin)+"ns");
       // System.out.println("运行时间:"+((double)(setdataEnd-setdataBegin)/(double)1000000)+"ms");
        
//        System.out.println("冒泡排序后：");
//        printArr(numbers);
    }
 
	//标记numbers
	 public static void bubbleSort(int[] numbers)
	    {
		    //System.out.println("bubbleSort(): ");
	        int temp = 0;
	        int size = numbers.length;
	        
	       //for(int x=0;x<100;x++){

			//long setdataBegin = System.nanoTime();
	        for(int i = 0 ; i < size-1; i ++)
	        {
	        for(int j = 0 ;j < size-1-i ; j++)
	        {
	            if(numbers[j] > numbers[j+1])  //交换两数位置
	            {
	            temp = numbers[j];
	            numbers[j] = numbers[j+1];
	            numbers[j+1] = temp;
	            }
	        }
	        }
	        
	       // }
	    }
	 
//	 public static void printArr(int[] numbers)
//	    {
//		    //System.out.println("printArr(): ");
//	        for(int i = 0 ; i < numbers.length ; i++ )
//	        {
////		        System.out.println("No"+i+": ");
//		        System.out.print(numbers[i] + " ");
//	        }
//	        System.out.println();
//	    }


}
