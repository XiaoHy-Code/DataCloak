package test;

import java.awt.geom.Arc2D;

/**
 * 二分查找又称折半查找，它是一种效率较高的查找方法。 
　　【二分查找要求】：1.必须采用顺序存储结构 2.必须按关键字大小有序排列。
 * @author wzj
 *
 */
public class BS { 
	public static void main(String[] args) {
		
//		int[] src={1,2};//1000000
//		int a=10;
//		if(a>10){
//			a++;
//		}
//		src[0]=a;
		int src=1;
		if(src>1){
			src++;
		}
		int x = binarySearch(src, 49);
		x = binarySearch(src, 49);
		x = binarySearch(src, 49);
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
   public static int binarySearch(int src, int des){ 
//	   System.out.println("binarySearch(int[], int): ");
//        int low = 0; 
//        int high = srcArray.length-1; 
//        while(low <= high) { 
//            int middle = (low + high)/2; 
//            if(des == srcArray[middle]) { 
//                return middle; 
//            }else if(des <srcArray[middle]) { 
//                high = middle - 1; 
//            }else { 
//                low = middle + 1; 
//            }
      //  }
	    
        return src;
   }

}
