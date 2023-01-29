class EventSubscription {
    int created;
    int activity;
    int execution;

    EventSubscription (int a) 
    static presumes a = vx achieves new_this::EventSubscription<created:vx,activity:null,execution:null> & a=vx; 
    {
        new_this.created = a;
    }

    virtual int getExecution() 
    static presumes this::EventSubscription<created:v1,activity:v2,execution:v3> achieves this::EventSubscription<created:v1,activity:v2,execution:v3> & res = v3;
    {
    int x = this.execution;
    return x;
    }

    virtual int getActivity() 
    static presumes this::EventSubscription<created:v1,activity:v2,execution:v3> achieves this::EventSubscription<created:v1,activity:v2,execution:v3> & res = v2;
    {
    int x = this.activity;
    return x;
    }

}

class AbstractEventHandler {

    virtual void handleEvent(EventSubscription eventSubscription)
    static presumes this::AbstractEventHandler<> * eventSubscription::EventSubscription<created:v5,activity:null,execution:null> achieves err this::AbstractEventHandler<> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null>;
    dynamic presumes this::AbstractEventHandler<>* eventSubscription::EventSubscription<created:v5,activity:null,execution:null> achieves err this::AbstractEventHandler<> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null>;

    {
        int execution = eventSubscription.getExecution();
        int activities = eventSubscription.getActivity();
        int y = 1;
        if (y) {
         execution.setActivity(activity);
        }
    } 

}

class SignalEventHandler extends AbstractEventHandler {
  
   int event;

   virtual int getEventHandlerType() 
   static presumes this::SignalEventHandler<event:v> achieves this::SignalEventHandler<event:v> & res = v;
   {
    int x = this.event;
    return x;
  }

    inherit void handleEvent(EventSubscription eventSubscription)
    static presumes this::SignalEventHandler<event:v5> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null> achieves err this::SignalEventHandler<event:v5> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null>;
    dynamic presumes this::AbstractEventHandler<>SignalEventHandler<event:v5> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null> achieves err this::AbstractEventHandler<>SignalEventHandler<event:v5> * eventSubscription::EventSubscription<created:v6,activity:null,execution:null>;
    {
        int execution = eventSubscription.getExecution();
        int activities = eventSubscription.getActivity();
        int y = 1;
        if (y) {
         execution.setActivity(activity);
        }
    } 

}

class Test {

    virtual void foo(AbstractEventHandler b) 
    static presumes this::Test<> * b::AbstractEventHandler<>SignalEventHandler<event:v1> achieves err this::Test<> * b::AbstractEventHandler<>SignalEventHandler<event:v1> * a::EventSubscription<created:1,activity:null,execution:null>;
    {
        int c = 1;
        EventSubscription a = new EventSubscription(c);
        b.handleEvent(a);
    }
}