// Evaluator for Lego formulas
package lego;

import java.util.ListIterator;
import java.util.Stack;
import lego.parser.*;

// data structure to store values of free variables
// This is the data structure that stores the free varaiables and thier corresponding domain. 
//It pushes the values into a stack and then any time it is called with a varaible, it uses the lookup method to return the corresponding value
 class Env { 
  public static Stack<Environ> stack = new Stack<>(); // stack declaration
	public void push(Environ envv  ) { //method to push stack of type Environ
	    stack.push(envv);
	}
	public  int lookUpForVariable(String vars) throws IndexOutOfBoundsException{// the look up method 
		ListIterator<Environ> litr = stack.listIterator(); // creating the list  
		while(litr.hasNext()){
			litr.next();
			}
		Environ element1 =null;
		while(litr.hasPrevious()){
			element1 = (Environ)litr.previous(); // looping through to return the most recent variable vars
			if(vars.equals(element1.s)){
				return element1.value;
			}
		}
		
		 System.out.println( element1.s+ "is a free variable, hence cannot evaluate");
		 System.exit(0); // need more efficient way to exit// exit if the variable is a free variable
		 return 0; // never reached 
		
}

 }


public class Eval {
   static boolean bValue = false;
   private static Environ environment;
   
    public static boolean eval(Formula f) {
    	return eval(f, new Env());
    }
	
	
    public static boolean eval(Formula f, Env e) throws ArithmeticException {
   try{
    	if(f instanceof Atomic){
    		System.out.println("Atomic");
    		  return evalAtomic(f,e);
    	}
    	
    	if (f instanceof Binary  ){
    		System.out.println( "Binary");
    	    switch (((Binary)f).bin_conn) {
			  case "&&"   :   bValue = eval( ((Binary)f).f1) && eval( ((Binary)f).f2);//System.out.println(bValue);
			  break;
			  case "||"   :   bValue = eval( ((Binary)f).f1)  || eval( ((Binary)f).f2);
			  break;
			  case "->"   :   bValue = (!(eval( ((Binary)f).f1))) || ( eval( ((Binary)f).f2));// check th
			  break;
			  case "<->"  :   bValue = ((eval( ((Binary)f).f1) && eval( ((Binary)f).f2)) || (!eval( ((Binary)f).f1) && !eval( ((Binary)f).f2)));  // check this 
			  break;
	          default     :  System.out.println("Wrong relational operator"); 
	          
	  }		
    	    return bValue;
    		
    	}
    	
    	
           if (f instanceof Unary  ){
               System.out.println( "Unary");
                 System.out.println( !(eval(((Unary)f).f)));   // System.out.println( "Unary");
    		return  !(eval(((Unary)f).f));
           }
           
           
    	if(f instanceof Quantified){
    		if (((Quantified)f).quant.equals("forall"))  {
    			
    			System.out.println( "forall");
    			String var = ((Quantified)f).var.s;
    		         int from =  (((Quantified)f).dom.from).n;
    		         int to =  (((Quantified)f).dom.to).n;
    		         for(int  d = from ; d <=to ; d++){
    		    	  environment = new Environ(var, d);
    		          e.push(environment);
    		      if(eval(((Quantified)f).f,  e)== false){
                          return  false;
                     } 
                         }
                      return true;
                    
                         } 
    		
           if (((Quantified)f).quant.equals("exists"))  {
    			System.out.println( "exists");
    			String var = ((Quantified)f).var.s;
    		         int from =  (((Quantified)f).dom.from).n;
    		         int to =  (((Quantified)f).dom.to).n;
    		         for(int  d = from ; d <=to ; d++){
    		    	  environment = new Environ(var, d);
    		          e.push(environment);
    		      if(eval(((Quantified)f).f,  e)== true){
                          return  true;
                     } 
                         }
                      return false;
                    
                         } 
    	}} catch(ArithmeticException ex){
    		System.out.println("Can not evaluate: modula by zero is not possible in lego formula evaluation");
    		
    	}
         System.out.println( "No Value Found ... Exiting with a false value");
		return false;	
    }


	private static boolean evalAtomic(Formula f, Env freeVar)throws ArithmeticException {
    boolean boolValue = true;
    try{
	switch (((Atomic)f).rel_op) {
		  case ">"  :  boolValue =evalExp(((Atomic)f).e1,freeVar) > evalExp(((Atomic)f).e2,freeVar); //System.out.print( ">" + boolValue);
		  break;
		  case ">=" :  boolValue = evalExp(((Atomic)f).e1,freeVar) >= evalExp(((Atomic)f).e2,freeVar);
		  break;
		  case "="  :  boolValue = evalExp(((Atomic)f).e1,freeVar) == evalExp(((Atomic)f).e2,freeVar); //System.out.print( "=" +  boolValue);
          break;
          default   : System.out.println("Wrong relational operator"); 
    }}
    catch(ArithmeticException e){
    	
    	System.out.println("Can not evaluate: modula by zero is not possible in lego formula evaluation");
    }
	 return boolValue;
	}


	private static int evalExp(Exp e, Env end)throws ArithmeticException {
		
		int binBoolValue = 0;
		try{
		if ((e instanceof Int)){
			binBoolValue = evalInt( (Int)(e));
            return binBoolValue;
	
		}
		 
		
		if (e instanceof Var){
		
		    System.out.print(((Var) e).s + "");
		   
			binBoolValue = end.lookUpForVariable(((Var) e).s);
		 System.out.print( binBoolValue + " ");
		}
		
	if (e instanceof BinExp){
			switch (((BinExp)e).bin_op) {
			  case "*"   :  binBoolValue = evalExp(((BinExp)e).e1,end) * evalExp(((BinExp)e).e2,end);
			  break;
			  case "/"   :  binBoolValue = evalDivision(evalExp(((BinExp)e).e1,end) , evalExp(((BinExp)e).e2,end));
			  break;
			  case "mod" :  binBoolValue = evalMod( evalExp(((BinExp)e).e1,end) , evalExp(((BinExp)e).e2,end));  
			  break;
			  case "+"   :  binBoolValue = evalExp(((BinExp)e).e1,end) + evalExp(((BinExp)e).e2,end);
			  break;
			  case "-"   :  binBoolValue = evalExp(((BinExp)e).e1,end) - evalExp(((BinExp)e).e2,end); 
	          break;
	          default      : System.out.println("Wrong relational operator"); 
	  }
			
		
	}}catch (ArithmeticException e1) {
		System.out.println("Can not evaluate: modula by zero is not possible in lego formula evaluation");
		// TODO: handle exception
	}
		return binBoolValue;
	}

	private static int evalInt(Int integerValue) throws ArithmeticException {
	  return (integerValue.n);
		
	}
	
	
	private static int evalDivision(int evalExp1, int evalExp2) throws ArithmeticException {
		   
		   
		try {
		
			return evalExp1 / evalExp2;
		
		}
		catch(ArithmeticException f){
		// TODO Auto-generated method stub
		System.out.println("Can not evaluate: Division by zero is not possible in lego formulas ");
		System.exit(0);
		}
		return 0; // fix 2 forall x : [0..10] . forall y : [0..10] . x >= (x/y)
	
	
	}
	private static int evalMod(int evalExp1, int evalExp2)throws ArithmeticException {
		
		try{
		
			return evalExp1 % evalExp2;
			
		}catch(ArithmeticException e) {
		System.out.println("Can not evaluate: modula by zero is not possible in lego formula evaluation");
		System.exit(0);
	//	e.printStackTrace();
		}
		return 0; // fix 1 forall x : [0..10] . forall y : [0..10] . x >= (x mod y)
	}
}


