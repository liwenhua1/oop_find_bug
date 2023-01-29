
class ErrorMessage {
    int location;

     virtual Builder setLocation(int value) 
     static presumes this::ErrorMessage<location:v> & value = null achieves err this::ErrorMessage<location:v> & value = null;
     
     {
            int y = 1;
            if (y) {
                value.foo();
            } else {
                this.location_ = value;
                return this;
            }
        }

}
class ErrorCode {

     virtual AxonException convert()
     static presumes this::ErrorCode<> achieves this::ErrorCode<> & res = null;
     {
        int y;
        return y;
    }

    virtual void convert1(int source, Throwable throwable)
    static presumes this::ErrorCode<> * z::ErrorMessage<location:v1> achieves err this::ErrorCode<> * z::ErrorMessage<location:v1>;
    {
        int q = this.convert();
        z.setLocation(q);
        }
}
