package test;

public class ArrayTest {
	
	public static void main(String[] args) {
//		System.out.println("main(): ");
		int[] src=new int[5000];//1000000
		for(int i=0;i<5000;i++){//1000000
			src[i] = i;
        }
		//binarySearch(src, 49);
		int x=1;
		if(x>1){
			x++;
		}
		
		src[0]=x;
		x=binarySearch(src, 49,0);
		//x=binarySearch(src, 49);
	
        System.out.println(x);//490000
        //System.out.println(binarySearch(src,3,0,src.length-1));
    }

    /**
     * * 二分查找算法 * *
     * 
     * @param srcArray
     *            有序数组 *
     * @param des
     *            查找元素 *
     * @return des的数组下标，没找到返回-1
     */
	//标记srcArray
   public static int binarySearch(int[] srcArray, int des,int x){ 
	   srcArray[x]=1000;
//	   System.out.println("binarySearch(int[], int): ");
        int low = 0; 
        int high = srcArray.length-1; 
        while(low <= high) { 
            int middle = (low + high)/2; 
            if(des == srcArray[middle]) { 
                return middle; 
            }else if(des <srcArray[middle]) { 
                high = middle - 1; 
            }else { 
                low = middle + 1; 
            }
        }
        return -1;
   }

      /**  
     *二分查找特定整数在整型数组中的位置(递归)  
     *@paramdataset  
     *@paramdata  
     *@parambeginIndex  
     *@paramendIndex  
     *@returnindex  
     
    public static int binarySearch(int[] dataset,int data,int beginIndex,int endIndex){ 
 	   System.out.println("binarySearch:(int[], int, int, int) ");
       int midIndex = (beginIndex+endIndex)/2;  
       if(data <dataset[beginIndex]||data>dataset[endIndex]||beginIndex>endIndex){
           return -1;  
       }
       if(data <dataset[midIndex]){  
           return binarySearch(dataset,data,beginIndex,midIndex-1);  
       }else if(data>dataset[midIndex]){  
           return binarySearch(dataset,data,midIndex+1,endIndex);  
       }else {  
           return midIndex;  
       }  
   } */

}

