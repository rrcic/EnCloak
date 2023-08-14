package invoker;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.UUID;


// 用到hotcall的 initvalue,deletevalue,commitInt,commitBranch; commitFloat开始似乎就没有走hotcall框架了
public class sgx_invoker{
  	public static final int N=20;
  	// public static final int Temp=100;
	public static native int print_ms();
	public static native int init();
	public static native int destroy();
	// get
	public static native int commitInt(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid, String ouuid, String cuuid);
	public static native float commitFloat(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid);
	public static native double commitDouble(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid);
	public static native char commitChar(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid);
	public static native byte commitByte(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid);
	public static native long commitLong(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid);
	public static native int[] commitIntArray(long counter,String uuid);
	public static native double[] commitDoubleArray(long counter,String uuid);
	public static native byte[] commitByteArray(long counter,String uuid);
	// branch
	public static native int commitBranch(long counter, int[] intArray, int intTail, double[] doubleArray, int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray,int charTail, byte[] byteArray,int byteTail, String uuid, String ouuid, String cuuid);
	// update
	public static native int commitUpdate(long counter, int[] intArray,int intTail, double[] doubleArray,int doubleTail,float[] floatArray, int floatTail, long[] longArray, int longTail, char[] charArray, int charTail,byte[] byteArray,int byteTail, String uuid, String ouuid, String cuuid);
	
	public static native int initValue(String uuid,String calluuid,long LineNo, String ouuid, String cuuid);
	public static native int deleteValue(String uuid,String ouuid,String cuuid,long status);
	public static native void initNode(String uuid,int type,int size);
    
    // 原方案
	// public static native void initArray(String uuid,int index,int size,int isSens);
	// public static native int commitUpdateMutliArray(long counter,String uuid,String cuuid);
	
	static {
		try{
			System.out.println("invoker: "+ System.getProperty("java.library.path"));
			System.loadLibrary("SGX");
		}
		catch (Exception e) {
			System.out.println("invoker: " + System.getProperty("java.library.path"));
			e.printStackTrace();
		}
	} 
	

	int[] intArray = new int[N];
	int intTail = 0;
	
	double[] doubleArray = new double[N];
	int doubleTail = 0;
	
	float[] floatArray = new float[N];
	int floatTail = 0;
	
	long[] longArray = new long[N];
	int longTail = 0;
	
	char[] charArray = new char[N];
	int charTail = 0;
	
	byte[] byteArray = new byte[N];
	int byteTail = 0;
	
	int[] iarr = new int[100];
	double[] darr = new double[100];
	float[] farr = new float[100];
	char[] carr = new char[100];
	long[] larr = new long[100];
	byte[] barr = new byte[100];
	
	int[][] miarr = new int[100][100];
	double[][] mdarr = new double[100][100];
	float[][] mfarr = new float[100][100];
	char[][] mcarr = new char[100][100];
	long[][] mlarr = new long[100][100];
	byte[][] mbarr = new byte[100][100];
	
	int size_i=0;
	int size_d=0;
	int size_f=0;
	int size_c=0;
	int size_l=0;
	int size_b=0;
	
	long counter = -1;

	// 0719[hyr] add ouuid, cuuid 
	String ouuid = null;
	String cuuid = null;
	//long invokecounter = -1;
	public void sgx_invoker(){
		
		//objects = new ArrayList<Object>();
	}
	
	public void clear(){
		intTail = 0;
		doubleTail = 0;
		floatTail = 0;
		longTail = 0;
		charTail = 0;
		byteTail = 0;
		
		size_i=0;
		size_d=0;
		size_f=0;
		size_c=0;
		size_l=0;
		size_b=0;
	}
	
	public void add(Object o){
		if(o==null)
			intArray[intTail++]=0;
		else
			intArray[intTail++]=o.hashCode();
		//objArray[objTail++] = o;
	}

	public void add(int o){
		intArray[intTail++] = o;
//		System.out.println(String.valueOf(o)+" is added to list;");
	}
	
	public void add(double o){
		doubleArray[doubleTail++] = o;
	}
	public void add(float o){
		floatArray[floatTail++] = o;
	}
	
	public void add(long o){
		longArray[longTail++] = o;
	}
	public void add(char o){
		charArray[charTail++] = o;
	}
	public void add(byte o){
		intArray[intTail++] = o;
	}
	
	public void add(int[] o){
		//iarr = o;
		size_i = o.length;
		System.arraycopy(o, 0, iarr, 0, size_i);
	}
	public void add(double[] o){
		//darr = o;
		size_d = o.length;
		System.arraycopy(o, 0, darr, 0, size_d);
	}
	public void add(float[] o){
		//farr = o;
		size_f = o.length;
		System.arraycopy(o, 0, farr, 0, size_f);
	}
	public void add(char[] o){
		//carr = o;
		size_c = o.length;
		System.arraycopy(o, 0, carr, 0, size_c);
	}
	public void add(long[] o){
		//larr = o;
		size_l = o.length;
		System.arraycopy(o, 0, larr, 0, size_l);
	}
	public void add(byte[] o){
		//barr = o;
		size_b = o.length;
		System.arraycopy(o, 0, barr, 0, size_b);
	}
	
	public void add(int[][] o){
	}
	public void add(double[][] o){
	}
	public void add(float[][] o){
	}
	public void add(char[][] o){
	}
	public void add(long[][] o){
	}
	public void add(byte[][] o){
		
	}
	public void add(int[][][] o){
	}
	public void add(double[][][] o){
	}
	public void add(float[][][] o){
	}
	public void add(char[][][] o){
	}
	public void add(long[][][] o){
	}
	public void add(byte[][][] o){	
	}
	
	public void setCounter(long counter){
		this.counter = counter;
	}

	// 0719[hyr] 这两个函数是插入ouuid和cuuid的一种手段，但如果重构了updateValueInEnclave等函数，参数中添加ouuid和cuuid，这两个函数或许也可以删除
	public void setOuuid(String ouuid){
		this.ouuid = ouuid;
	}

	public void setCuuid(String cuuid){
		this.cuuid = cuuid;
	}

	public void clearOuuid(){
		this.ouuid = null;
	}

	public void clearCuuid(){
		this.cuuid = null;
	}
	
	
	public boolean initenclave(){
		System.out.println("----enter initenclave()----");
		//init_total++;
		if(1==init()) return true;
		else return false;
	}
	
	public boolean closeenclave(){
		System.out.println("----enter closeenclave()----");
		if(0==destroy()) return true;
		else return false;
	}
	
	public java.lang.String getUUID() {
		String idsString = UUID.randomUUID().toString().replace("-", "").toLowerCase();
		System.out.println(idsString);
		return idsString;
	}
	
	// 原方案
	// public void initArrayInEnclave(String uuid, int index, int size, int isSens){
	// 	System.out.println("----enter initArray()----");
	// 	initArray(uuid, index, size, isSens);
	// }
	
	//add gpf
	public void initNodeInEnclave(String uuid, int type, int size){
		System.out.println("----enter initNode()----");
 		//7: int type array  8: double type array
		initNode(uuid, type, size);
	
	}
	
	public boolean initValueInEnclave(String uuid, String calluuid, long LineNO){
		//System.out.println("uuid="+uuid);
		if(1==initValue(uuid, calluuid, LineNO, ouuid, cuuid)){
			System.out.println("----initValue true----");
			return true;
		}
		
		else{
			System.out.println("----initValue true----");
			return false;
		}
	}
	
	// [hyr]0814 TODO cuuid? 这里cuuid是从java接收的，还需要再进一步处理
	public boolean deleteValueInEnclave(String getuuid, String cuuid, long status){
		System.out.println("status: " + status);
		if(1==deleteValue(getuuid, cuuid, status)){
			System.out.println("----deleteValue true----");
			return true;
		}
		else{
			System.out.println("----deleteValue false----");
			return false;
		}
	}
	
	// update(getUUID, 0L)	status->maybe to identify uuid/cuuid
	public void updateValueInEnclave(String uuid, int status, long counter){
		//edit 20210526gxc merge continuous update function

		System.out.println("----enter commitUpdate()----");
		int ret = -1;
		if (status == 0) {
			ret = commitUpdate(counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,
					longArray,longTail,charArray,charTail,byteArray,byteTail,uuid,ouuid,cuuid);
			System.out.println("status: " + status);
		}else if (status == 1) {
			int[] newi = new int[size_i];
			double [] newd = new double[size_d];
			float [] newf = new float[size_f];
			char [] newc = new char[size_c];
			long [] newl = new long[size_l];
			byte [] newb = new byte[size_b];
			
			for (int i = 0; i < size_i; i++) {
				newi[i] = iarr[i];
			}
			for (int i = 0; i < size_d; i++) {
				newd[i] = darr[i];
			}
			for (int i = 0; i < size_f; i++) {
				newf[i] = farr[i];
			}
			for (int i = 0; i < size_c; i++) {
				newc[i] = carr[i];
			}
			for (int i = 0; i < size_l; i++) {
				newl[i] = larr[i];
			}
			for (int i = 0; i < size_b; i++) {
				newb[i] = barr[i];
			}
			// [hyr]cuuid不放在char数组中，但注意initVaule中在用到hotcall_request函数时，calluuid是放在char数组中的
			ret = commitUpdate(counter,newi,size_i,newd,size_d,newf,size_f,
					newl,size_l,newc,size_c,newb,size_b,uuid,ouuid,cuuid);
			System.out.println("status: " + status);
		}
		
		if (ret != 1000) {
			System.out.println("update wrong: " + ret);
		}
		clear();
	}
	
	// 原方案
	// public void updateMultArray(String uuid, int width, int high, long counter) {
	// 	System.out.println("----enter commitUpdateMutliArray()----");
	// 	commitUpdateMutliArray(counter, uuid, cuuid);
	// 	clear();
	// }
	
	public boolean getBooleanValue(String uuid, long counter){ 
		int ret = -1;
		ret = commitBranch(counter, intArray, intTail, doubleArray, doubleTail, floatArray, floatTail, longArray, longTail, charArray, charTail, byteArray, byteTail, uuid, ouuid, cuuid);
		if(ret == 1){
			System.out.println("----commitBranch true----");
			clear();
			return true;
		}else if(ret == 0){
			System.out.println("----commitBranch false----");
			clear();
			return false;
		}else{
			//throw new Exception("error");
			System.out.println("branch ret: " + ret);
			System.out.println("branch error");
			System.exit(1);
		}
		clear();
		return false;
	}


	public int getIntValue(String uuid, int status, long counter){ 
		System.out.println("----enter getIntValue()----");
		int ret = -1;
		ret = commitInt(counter, intArray, intTail, doubleArray, doubleTail, floatArray, floatTail, longArray, longTail, charArray, charTail, byteArray, byteTail, uuid, ouuid, cuuid);
		System.out.println("ret: " + ret);
		clear();
		return ret;
	}
	
	public double getDoubleValue(String getuuid, int status, long counter){ 
		System.out.println("----enter getDoubleValue()----");
		double ret = -1;
		ret = commitDouble(counter, intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,longArray,longTail,charArray,charTail,byteArray,byteTail,getuuid);
		clear();
		return ret;
	}

	
	public float getFloatValue(String getuuid,int status,long counter){
		System.out.println("----enter getFloatValue()----"); 
		float ret = -1;
		//ret = commitFloat(counter, intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,longArray,longTail,charArray,charTail,byteArray,byteTail);
		clear();
		return ret;
	
	}

	public char getCharValue(String getuuid, int status, long counter){
		System.out.println("----enter getCharValue()----"); 
		char ret = 0;
		//ret = commitChar(counter, intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,longArray,longTail,charArray,charTail,byteArray,byteTail);
		clear();
		return ret;
	}
	
	public long getLongValue(String getuuid,int status,long counter){ 
		System.out.println("----enter getLongValue()----");
		long ret = -1;
		ret = commitLong(counter, intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,longArray,longTail,charArray,charTail,byteArray,byteTail,getuuid);
		clear();
		return ret;
	
	}

	public byte getByteValue(String getuuid,int status,long counter){ 
		System.out.println("----enter getByteValue()----");
		byte ret=0;
		//ret = commitByte(counter, intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,longArray,longTail,charArray,charTail,byteArray,byteTail);
		clear();
		return ret;
	}

	public int[] getIntArray(String uuid, int status, long counter){ 
		
		int[] ret;
		System.out.println("----enter getIntArray()----");
		if (status==1) {
			System.out.println("cuuid: "+ cuuid + "; status: " + status);
			ret = commitIntArray(counter, cuuid);
		}else {
			System.out.println("uuid: "+ uuid + "; status: " + status);
			ret = commitIntArray(counter, uuid);
		}
		clear();
		return ret;
	}
	
	public double[] getDoubleArray(String uuid, int status, long counter){ 
		
		double[] ret;
		System.out.println("----enter getDoubleArray()----");
		if (status==1) {
			System.out.println("cuuid: "+ cuuid + "; status: " + status);
			ret = commitDoubleArray(counter, cuuid);
		}else{
			System.out.println("uuid: "+ uuid + "; status: " + status);
			ret = commitDoubleArray(counter, uuid);
		}
		clear();
		return ret;
	}
	
	public byte[] getByteArray(String uuid,int status,long counter){ 
		
		byte[] ret;
		System.out.println("----enter getByteArray()----");
		
		ret = commitByteArray(counter, uuid);
		clear();
		return ret;
	}

	
	
}