theory utp
  imports 
    utp_rel_laws 
    utp_healthy
    utp_hoare
    utp_wlp
    utp_concurrency
    utp_theory
begin 

bundle UTP_Syntax
begin

unbundle UTP_Logic_Syntax

end

end