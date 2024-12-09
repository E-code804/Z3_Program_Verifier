# Z3_Program_Verifier

## Example commands in after running "stack ghci"
prop_checkFile "dafny/IsSorted.dfy" -> Passes 100 tests.

prop_checkFile "dafny/Square-Mistakes/Square-HalfInv.dfy -> Failed! Falsified (after 9 tests): [IntVal 3].

prop_checkFile "dafny/IntDiv.dfy" -> Passes 100 tests.

## Write-up on what I did
To start, I needed expand what we previously had at the end of CMSC433 from the past semester. Specifically, I needed to  
extend the DafnyParser, WP, and Z3 files to include array in their implementations. Without that, I could not have been  
able to do non-trivial method testing. A lot of work needed to be done in the DafnyParser file specifically. I needed to extend  
the previous implementation to properly parse "forall" quantifiers which are the foundations to allowing the WP and Z3  
files to run correctly for arrays. The previous WP file initially had us ignore arrays during CMSC433, so I needed to update  
it to include constructing the weakest preconditions for arrays. This was done in the instance declaration of Subst to  
handle the newly parseable Forall expression type (added to the Syntax file). Finally, in Z3, I needed to carefully follow  
Z3 syntax in order for the solver to be able to run on forall quantifiers and arrays. In my "toSMTAux" function, I needed to  
implement the proper Z3 syntax for "forall" and ArrayVal _ expressions. After adding some helper functions, the Z3 file was finished  
and I could then shift my focus to property based testing with QuickCheck.  


Within the PBT.hs file, I created a lot of helper functions that were crucial to effectively extract parts of the method and generate  
values that would be used in the property based testing functions. These included helpers such as extracting the parameters and specifications  
of a functions, generating an arbitrary value based on "Type", generating values for the parameters of a method based on their types,  
and functions to check pre/post conditions of a method hold for given parameters/result. Initially, I made a naive function to test a method.  
It was for simple functions without arrays, and all it did was generate values for its parameters and if it held with the precondition,  
execute the method with the generated values to see if the resulting value would hold with the postcondition. Moving on to the function that  
was also capable of testing methods with arrays, again, the program automatically generate random input parameters for methods, check their  
preconditions using Z3 to ensure the generated inputs are valid, and then run the method. After execution, we verified the method's postconditions   
with Z3 again. This setup allowed us to repeatedly test the correctness of the method over a broad range of automatically generated inputs, whether they  
were arrays or not. The example commands above show how to run the code in the repository. 
