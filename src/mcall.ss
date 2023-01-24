class Super {
    int val;

	virtual void foo (int a, int b) 
	static
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v+e+r> & a = e & b = r & res = v+e+r;
	dynamic
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v+e+r> & a = e & b = r & res = v+e+r;
	{
	
		int temp = this.val;
		int temp1 = a + temp;
		int temp2 = b + temp1;
		this.val = temp2;
		return temp2;
	}

	virtual int get () 
	static
		presumes this::Super<val:v>  achieves this::Super<val:v> & res = v;
	dynamic
		presumes this::Super<val:v>  achieves this::Super<val:v> & res = v;
	{
	
		int temp = this.val;
		return temp;
	}

    virtual void test () 
	static
		presumes this::Super<val:v> * o::Super<val:b> achieves this::Super<val:v+b+3> * o::Super<val:b+3> ;
	dynamic
		presumes this::Super<val:v> * o::Super<val:b>  achieves this::Super<val:v+b+3> * o::Super<val:b+3> ;
	{   
        int temp1 = 1;
        int temp2 = 2;
		int temp3 = o.foo(temp1, temp2);
		int temp4 = this.val;
		int temp5 = temp4 + temp3;
		this.val = temp5;
	}

	virtual void test2 () 
	static
		presumes this::Super<val:b+1> achieves this::Super<val:b+1> & res = b+1;
	dynamic
		presumes this::Super<val:b+1> achieves this::Super<val:b+1> & res = b+1;
	{   
        int temp = this.get();
        return temp;
	}
}