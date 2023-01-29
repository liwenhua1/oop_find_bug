 class ChannelPipeline{

 }
 
 class Channel {

     virtual ChannelPipeline getPipeline()
     static presumes this::Channel<> achieves this::Channel<> * res::ChannelPipeline<>;
     {

     }

 }
 
 
 class Test{

   virtual DeviceSession getDeviceSession(Channel channel) 
        static presumes this::Test<> & channel = null achieves this::Test<> & channel = null;
    {
        ChannelPipeline x = channel.getPipeline();
    }
 }       