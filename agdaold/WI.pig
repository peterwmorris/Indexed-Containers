load /home/pwm/darcs/Pig09/test/TaggedInduction.pig ;

data W (S : Set) (P : S -> Set) : Set := ('sup : (s : S) -> (f : P s -> W S P) -> W S P) ;


 
