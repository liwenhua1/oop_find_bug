class Super {
    int val;

	virtual void foo (int a, int b) 
	static
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v+e+r> & a = e & b = r;
	dynamic
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v+e+r> & a = e & b = r;
	{
	
		int temp = this.val;
		int temp1 = a + temp;
		int temp2 = b + temp1;
		this.val = temp2;
	}

    virtual void test (int a, int b) 
	static
		presumes this::Super<val:v> * o::Super<val:v+1> achieves this::Super<val:v> * o::Super<val:v+3> ;
	dynamic
		presumes this::Super<val:v> * o::Super<val:v+1>  achieves this::Super<val:v> * o::Super<val:v+3> ;
	{   
        int temp1 = 1;
        int temp2 = 2;
		o.foo(temp1, temp2);
	}
}