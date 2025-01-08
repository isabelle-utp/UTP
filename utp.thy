section \<open> UTP Meta-theory \<close>

theory utp
  imports 
    utp_rel_laws 
    utp_healthy
    utp_assertional
    utp_hoare
    utp_wlp
    utp_sp
    utp_wprespec
    utp_concurrency
    utp_theory
begin 

bundle UTP_Syntax
begin

unbundle UTP_Logic_Syntax

no_notation Set.member ("(_/ : _)" [51, 51] 50)

no_notation Equiv_Relations.quotient (infixl "'/'/" 90)

end

end