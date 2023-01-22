class Super {
    int val;

	virtual void foo (int a, int b) 
	static
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v> & a = e & b = r;
	dynamic
		presumes this::Super<val:v> & a = e & b = r achieves this::Super<val:v> & a = e & b = r;
	{
		int temp = a;
        int temp1 = b;
	}

    virtual void test (int a, int b) 
	static
		presumes this::Super<val:v> * o::Super<val:v> achieves this::Super<val:v> * o::Super<val:v> ;
	dynamic
		presumes this::Super<val:v> * o::Super<val:v>  achieves this::Super<val:v> * o::Super<val:v> ;
	{   
        int temp1 = 1;
        int temp2 = 2;
		o.foo(temp1, temp2);
	}
}