package test;

public class Sort_Quick {
	
	static int quickSortCount = 1;
	
	public static void main(String[] args) 
    {	       
		int[] numbers=new int[10];		
		for(int i=0;i<10;i++)
			numbers[i] = (int)(Math.random()*(100000+1));//0-10000
		
		int x=0;
		if(x>0){
			x++;
		}
		numbers[0]=x;
        
//		int [] numbers = new int[]{2956,5470,8024,3708,1188,2404,9345,4551,8677,3981};
//		int [] numbers = {58,50,30,70,83,40,95,21,76,56};
//		int [] numbers = new int[]{1,2,3,4,5,6,7,8,9,10};

		
        System.out.println("排序前:");
        printArr(numbers);
//
		//long setdataBegin = System.nanoTime();
        quick(numbers);
        //long setdataEnd = System.nanoTime();
        //System.out.println("运行时间:"+((double)(setdataEnd-setdataBegin)/(double)1000000)+"ms");
        
       System.out.println("快速排序后：");
       printArr(numbers);
        
    }
	
	 //标记numbers
	 public static int getMiddle(int[] numbers, int low,int high)
	    {
		 	
//		 	System.out.println("coming getMiddle");
	        int temp = numbers[low]; //数组的第一个作为中轴
	       // System.out.println("low = " + low+"  high = "+high);
	        while(low < high)
	        {
		        while(low < high && numbers[high] >= temp)
		        {
		            high--;
		        }
	//	        printArr(numbers);
		        //System.out.println("change high = "+high);
		        numbers[low] = numbers[high];//比中轴小的记录移到低端
		        while(low < high && numbers[low] <= temp)
		        {
		            low++;
		        }
	//	        printArr(numbers);
		        //System.out.println("change low = "+low);
		        numbers[high] = numbers[low] ; //比中轴大的记录移到高端
	        }
	        numbers[low] = temp ; //中轴记录到尾
	        return low ; // 返回中轴的位置
	    }
	 
	 /**
	     * 
	     * @param numbers 带排序数组
	     * @param low  开始位置
	     * @param high 结束位置
	     */
	    public static void quickSort(int[] numbers,int low,int high)
	    {
//	    	System.out.println("quick_Sort count:" + quickSortCount++);
	        if(low < high)
	        {
	          int middle = getMiddle(numbers,low,high); //将numbers数组进行一分为二
	          
	          //System.out.println("go left : "+low+"-" + (middle-1));
	          quickSort(numbers, low, middle-1);   //对低字段表进行递归排序
	          //System.out.println("go right : "+(middle)+"-" + high);
	          quickSort(numbers, middle+1, high); //对高字段表进行递归排序
	        }
	    
	    }
	    /**
	     * 快速排序
	     * @param numbers 带排序数组
	     */
	    public static void quick(int[] numbers)
	    {
	    	
	    	//System.out.println("coming quick");
	        if(numbers.length > 0)   //查看数组是否为空
	        {
	        quickSort(numbers, 0, numbers.length-1);
	        }
	    }
	    
	 
	 public static void printArr(int[] numbers)
	    {
	        for(int i = 0 ; i < numbers.length ; i++ )
	        {
		        System.out.print(numbers[i] + " ");
	        }
	        System.out.println();
	    }


}
