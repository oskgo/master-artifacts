(******************************************************************************)
(***              Require and import necessary theories                     ***)
(******************************************************************************)
require import AllCore List Distr DBool DInterval IntDiv DMap DList. 
require (*  *) Subtype PKE StdOrder. 
require LorR MLWE.
require PolyReduce.


import StdOrder.RealOrder.

(******************************************************************************)
(**  Instantiation of the ring Z/pZ[X]/<x^n-1> and matrices over this ring   **)
(******************************************************************************)

clone PolyReduce.PolyReduceZp as PolyReduceZp
rename [theory] "Subtype" as "PolySubtype".

section Distr.

import PolyReduceZp.ComRing.

import PolyReduceZp.

(* modulus *)
abbrev p = p.
(* order of quotient polynomial *)
abbrev n = n.

type Zp = Zp.

(* Size of error terms *)
op bet : { int | 0 <= bet < p %/ 2 } as bet_0_p.

(* Uniform bounded distribution in Zp *)
op dintermod (k:int): Zp distr = dmap [-k..k] Zp.inzmod.

lemma dintermod_ll (k: int): 0 <= k => is_lossless (dintermod k).
proof. move => ge0_k. apply/dmap_ll/dinter_ll => /#. qed.

(* Uniform bounded distribution in the polynomial ring *)
op dinterpoly (k:int) = dmap (BasePoly.dpoly n (dintermod k)) pinject.

op dnoise = dinterpoly bet.

lemma dnoise_ll': is_lossless dnoise.
proof. apply/dmap_ll/BasePoly.dpoly_ll/dintermod_ll. by elim bet_0_p. qed.

(* uniform distribution over our polynomial factor ring *)

locate bet_0_p.

op duni = dmap (BasePoly.dpoly n Zp.DZmodP.dunifin) pinject.

lemma duni_ll': is_lossless duni.
proof. apply/dmap_ll/BasePoly.dpoly_ll/Zp.DZmodP.dunifin_ll. qed.

lemma duni_uni': is_uniform duni.
proof.
apply/dmap_uni_in_inj/BasePoly.dpoly_uni/Zp.DZmodP.dunifin_uni/ge0_n => x y.
do 2! (rewrite BasePoly.supp_dpoly; first apply ge0_n).
move => [deg_x _] [deg_y _].
rewrite -eqv_pi -reduce_eqP.
by do 2! (rewrite reduce_reduced; first apply reducedP => //).
qed.

lemma duni_fu': is_full duni.
proof.
apply/dmap_fu_in => x.
exists (reduce (prepr x)). 
rewrite BasePoly.supp_dpoly; first apply ge0_n.
split.
- split => [| i bound].
  + apply/deg_reduced/reduced_reduce. 
  + apply/is_fullP/Zp.DZmodP.dunifin_fu.
- have pinj_prepr: x = pinject (prepr x) by rewrite reprK.
  by rewrite {1} pinj_prepr -eqv_pi -reduce_eqP reduceK.
qed.

lemma duni_funi': is_funiform duni.
proof. apply/is_full_funiform/duni_uni'/duni_fu'. qed.

end section Distr.


(* Instantiation of MLWE problem *)
import PolyReduceZp.


(********************************************************************************)
(***          Operator giving distance between two numbers modulo p           ***)
(********************************************************************************)

section Distance.

import Zp.

op distmodp (a b : Zp) = min (`|asint a - asint b|) (p - `|asint a - asint b|).

lemma mod_exists a q: exists m, a %% q = a - m * q by smt(divzE).

lemma abs_asint a: `|asint a| = asint a by smt(rg_asint).

lemma asint_inzmod_half: asint (inzmod (p %/ 2)) = p %/ 2.
proof. rewrite inzmodK. smt(ge2_p). qed.

lemma add_asint a c: exists b, (b = 0 \/ b = 1) /\ asint a + asint c = asint (a + c) + b * p.
proof.
elim (mod_exists (asint a + asint c) p) => b' H0.
exists b' => />.
split.
- case (asint a + asint c < p) => [| asint_big]; 1:smt(rg_asint).
  have /#: (p <= asint a + asint c < 2*p) by smt(rg_asint).
rewrite addE H0. 
algebra.
qed.

lemma sub_asint a c: exists b, (b = 0 \/ b = 1) /\ asint a - asint c = asint (a - c) - b * p.
proof.
elim (add_asint (a - c) c) => m [H0 H1].
exists m => />.
rewrite -ZModpRing.addrA (ZModpRing.addrC _ c) ZModpRing.subrr ZModpRing.addr0 in H1.
smt().
qed.

lemma distmodp_zero a b: distmodp a b = distmodp (a - b) zero.
proof.
rewrite /distmodp zeroE /=.
elim (sub_asint a b) => c [[-> | ->] /= H] //=; 1:by rewrite H.
have rel_asint: asint a - asint b < 0.
  smt(rg_asint).
rewrite StdOrder.IntOrder.ltr0_norm // H /= abs_asint /#.
qed.

lemma dist_asint_low a: distmodp a zero < p %/ 4 => 
        distmodp a zero < distmodp a (inzmod (p %/ 2)).
proof.
rewrite /distmodp zeroE /= abs_asint {1}/min.
case (asint a < p - asint a) => H1; 
rewrite /min H1 /= asint_inzmod_half; smt(rg_asint).
qed.

lemma asint_neg (a: Zp): a <> zero => asint (-a) = p - asint a.
proof. 
move => H.
rewrite oppE.
have: asint a <> 0; 1: by rewrite -asint_eq zeroE in H.
smt(rg_asint ge2_p).
qed.

lemma dist_neg (a b: Zp): distmodp (-a) (-b) = distmodp a b.
proof.
rewrite eq_sym distmodp_zero eq_sym distmodp_zero ZModpRing.addrC.
rewrite ZModpRing.opprK /distmodp zeroE /= 2!abs_asint.
case (a - b = zero) => H.
- have ->: b - a = zero by smt(@ZModpRing).
  by rewrite H.
- apply asint_neg in H.
  smt(@ZModpRing).
qed.

lemma inzmod0: inzmod 0 = zero by rewrite -zeroE asintK.

op distpoly p1 p2: int = listmax Int.(<=) witness (map (fun i => distmodp p1.[i] p2.[i]) (range 0 n)).

end section Distance.


(********************************************************************************)
(***                 Embedding the plaintexts into our ring                   ***)
(********************************************************************************)

section Embedding.

import BigXnD1.XnD1CA.

op bit_to_zp (b: bool): Zp = if b then Zp.one else Zp.zero.

op bits_to_poly (x: bool list): polyXnD1 = bigi predT (fun (i: int) => bit_to_zp (nth witness x i) ** ComRing.exp iX i) 0 n.

end section Embedding.

(********************************************************************************)
(***              Decoding plaintexts from noisy ring elements                ***)
(********************************************************************************)

section Decoding.

import BigXnD1.XnD1CA.

(* If d is closer to zero than to p/2, the   *)
(* the encrypted bit was (probably) 0 and    *)
(* vice versa                                *)    

op decode_coeff d = distmodp d (Zp.inzmod (p %/ 2)) <= distmodp d Zp.zero.

op decode d: bool list = map (fun i => decode_coeff d.[i]) (range 0 n).

lemma size_decode d: size (decode d) = n.
proof.
rewrite /decode size_map size_range /=. smt(ge0_n).
qed.

end section Decoding.

section Finite.

import PolyReduceZp.BigXnD1.XnD1CA.
import PolyReduceZp.Zp.DZmodP.Support.
import PolyReduceZp.Zp.DZmodP.

op list_prod (n: int): Zp list list = iter n (fun xss => flatten (map (fun xs => (map (fun a => a :: xs) (PolyReduceZp.Zp.DZmodP.Support.enum))) xss)) [[]].

lemma list_prodS n: 0 <= n => list_prod (n+1) = flatten (map (fun xs => map (fun a => a :: xs) (PolyReduceZp.Zp.DZmodP.Support.enum)) (list_prod n)).
proof. move => bound. by rewrite /list_prod iterS. qed.

lemma uniq_list_prod n: uniq (list_prod n).
proof.
move :n; elim/natind => n bound; 1: by rewrite /list_prod iter0.
rewrite (list_prodS n) //.
pose xss:= list_prod n.
move => uniq_xss; apply uniq_flatten_map => //.
- move => yss /=; rewrite map_inj_in_uniq => //.
  exact PolyReduceZp.Zp.DZmodP.Support.enum_uniq.
move => xs ys _ _ /=; rewrite hasP => -[] [| b zs]; 1:rewrite mapP => //.
rewrite 2!mapP => //. 
qed.

lemma size_list_prod n: 0 <= n => size (list_prod n) = p^n.
proof.
move: n; elim/natind => n bound.
- rewrite /list_prod iter0 //= => bound2.
  have ->: n = 0 by smt().
  by rewrite expr0.
rewrite bound /=.
have -> /=: 0 <= n + 1 by smt().
rewrite (list_prodS n) // size_flatten -map_comp /= /(\o).
rewrite StdBigop.Bigint.sumzE StdBigop.Bigint.BIA.big_map /(\o) /predT. 
have ->: (fun (_: Zp list) => true) = predT by done.
have ->: (fun (x: Zp list) => size (map (fun (a: Zp) => a :: x) PolyReduceZp.Zp.DZmodP.Support.enum)) = fun _ => p.
- apply fun_ext => xs.
  by rewrite size_map -PolyReduceZp.Zp.DZmodP.cardE.
rewrite StdBigop.Bigint.big_constz count_predT => ->.
by rewrite exprS.
qed.

lemma list_prod_n_supp xs n: 0 <= n => xs \in list_prod n => size xs = n.
proof.
move: xs n; elim => [| x xs indH []].
- case => //.
  move => i bound _; rewrite /list_prod iterS //=.
  rewrite -flatten_mapP => -[] [[] _ | x xs [_]]; rewrite mapP //. 
  rewrite /list_prod iter0 //.
- move => i bound _; rewrite (list_prodS i) //.
  rewrite -flatten_mapP => [[ys [ys_in /=]]].
  rewrite mapP => [[y [_ /= [_ xs_eq_ys]]]].
  rewrite (indH i) // 1:xs_eq_ys //.
  algebra.
qed.

lemma list_prod_nP (xs: Zp list) n: 0 <= n => size xs = n => xs \in list_prod n.
proof.
move: xs n; elim => [n bound /= <- | x xs indH [| n n_ge0 _] /=].
- by rewrite /list_prod iter0.
- smt(List.size_ge0).
rewrite list_prodS // => eq.
rewrite -flatten_mapP => [].
exists xs => /=.
split; 1:apply indH => /#.
rewrite mapP.
exists x.
by rewrite PolyReduceZp.Zp.DZmodP.Support.enumP.
qed.

op zmod_list_to_poly xs = bigi predT (fun (i: int) => (fun (j: int) => nth witness xs j) i ** PolyReduceZp.ComRing.exp PolyReduceZp.iX i) 0 n.

lemma zmod_list_to_poly_inj (xs ys: Zp list): size xs = n => size ys = n => 
    zmod_list_to_poly xs = zmod_list_to_poly ys => xs = ys.
proof.
move => size_xs size_ys eq; apply (eq_from_nth witness).
- by rewrite size_xs size_ys.
rewrite size_xs => i bound.
rewrite /zmod_list_to_poly polyXnD1_eqP in eq.
have: (bigi predT
         (fun (i0 : int) =>
            (fun (j : int) => nth witness xs j) i0 ** ComRing.exp iX i0) 0
         n).[i] =
      (bigi predT
         (fun (i0 : int) =>
            (fun (j : int) => nth witness ys j) i0 ** ComRing.exp iX i0) 0
         n).[i] by apply eq.
by rewrite !rcoeffZ_sum.
qed.

op poly_enum = map zmod_list_to_poly (list_prod n).

lemma size_enum: size poly_enum = p^n.
proof. rewrite /poly_enum size_map size_list_prod // ge0_n. qed.

lemma enum_uniq: uniq poly_enum.
proof.
rewrite map_inj_in_uniq => [xs ys xs_in ys_in |].
- apply/zmod_list_to_poly_inj/list_prod_n_supp => //. 
  apply list_prod_n_supp => //. 
- apply uniq_list_prod.
qed.

clone FinType.FinType as FTPoly with
   type t    <- polyXnD1,
   op   enum <- poly_enum
   proof *.

realize enum_spec.
proof.
move => pol; rewrite count_uniq_mem 1:enum_uniq // /b2i.
have -> //: pol \in poly_enum.
rewrite /poly_enum mapP.
exists (map (fun i => pol.[i]) (range 0 n)).
split. 
- apply list_prod_nP; 1:exact ge0_n.
  rewrite size_map size_range. 
  smt(ge0_n).
rewrite polyXnD1_eqP => i bound.
by rewrite rcoeffZ_sum //= (nth_map witness) 1:size_range 1:/# nth_range.
qed.

clone include MLWE with
  type ZR.t     <- polyXnD1,
   op  ZR.zeror <- zeroXnD1,
   op  ZR.oner  <- oneXnD1,
   op  ZR.(+)   <- PolyReduceZp.(+),
   op  ZR.( * ) <- PolyReduceZp.( * ),
   op  ZR.([-]) <- PolyReduceZp.([-]),
   op  ZR.invr  <- invr,
  pred ZR.unit  <- unit,
   op  duni     <- duni,
   op  dnoise   <- dnoise
  rename [type] "vector" as "zpvector"
  rename [type] "matrix" as "zpmatrix"
remove abbrev ZR.(-)
proof ZR.addrA by exact/ComRing.addrA, 
      ZR.addrC by exact/ComRing.addrC, 
      ZR.add0r by exact/ComRing.add0r, 
      ZR.addNr by exact/ComRing.addNr,
      ZR.oner_neq0 by exact/ComRing.oner_neq0, 
      ZR.mulrA by exact/ComRing.mulrA, 
      ZR.mulrC by exact/ComRing.mulrC, 
      ZR.mul1r by exact/ComRing.mul1r, 
      ZR.mulrDl by exact/ComRing.mulrDl, 
      ZR.mulVr by exact/ComRing.mulVr, 
      ZR.unitP by exact/ComRing.unitP, 
      ZR.unitout by exact/ComRing.unitout,
      duni_ll by exact/duni_ll',
      duni_uni by exact/duni_uni',
      duni_funi by exact/duni_funi',
      duni_fu by exact/duni_fu',
      dnoise_ll by exact/dnoise_ll'.

lemma mu1_duni (q: polyXnD1): mu1 duni q = 1%r/(p%r^n).
proof.
rewrite mu1_uni_ll.
- apply duni_uni.
- apply duni_ll.
rewrite is_fullP /=. 
- apply duni_fu.
congr.
have ->: support duni = predT.
- apply fun_ext => x. 
  by rewrite duni_fu.
by rewrite -FTPoly.card_size_to_seq /FTPoly.card size_enum RField.fromintXn.
qed.

end section Finite.

(** Locally defined LWE parameters: **) 
(** m is the number of LWE samples. **)
(** Other parameters are inherited from the cloned theories, e.g. p from zmod *)

op m : { int | 0 <= m } as m_ge0.

(********************************************************************************)
(***      Instantiation of the PKE library with correct types for LWE         ***)
(********************************************************************************)

type pkey  = zpmatrix * zpvector. 
type skey  = zpvector. 
type ptext = bool list. 
type ctext = zpvector * polyXnD1. 

clone import PKE as PKElwe with
  type pkey       <- pkey,
  type skey       <- skey,
  type plaintext  <- ptext,
  type ciphertext <- ctext.

(********************************************************************************)
(***            Sampling lemmas to be used in the security proof              ***)
(********************************************************************************)

(* Sampling a matrix and a vector is the same as sampling a larger matrix *)
module Sampler1 = {
  proc main() = {
    var mA, t;
    mA <$ dmatrix duni m m;
    t <$ dvector duni m;
    return (mA, t);
  }
}.

module Sampler2 = {
  proc main() = {
    var mA, t, mAt_tr;
    mAt_tr <$ dmatrix duni (m+1) m;
    mA <- trmx (subm mAt_tr 0 m 0 m);
    t <- row mAt_tr m;
    return (mA, t);
  }
}.

lemma pred_split (q p: 'a -> bool) : p = predU (predI p q) (predI p (predC q)).
proof. rewrite @fun_ext /predU /predI /predC => x. by elim (q x). qed.

equiv sampler_equiv: Sampler1.main ~ Sampler2.main: true ==> ={res} /\ 
    (size res.`1 = (m, m) /\ size res.`2 = m){1}.
proof.
bypr (res, size res.`1 = (m, m) /\ size res.`2 = m){1} (res{2}, true) => // [/#|].
move => /> &1 &2 [[m0 v0] b]; case (b) => _.
- byphoare => //; proc => /=. 
  case (size v0 = m /\ size m0 = (m, m)).
  + seq 1: (#pre /\ mA = m0 /\ size mA = (m, m)) ((1%r/p%r)^(n*m*m)) ((1%r/p%r)^(n*m)) (1%r-((1%r/p%r)^(n*m*m))) 0%r => // />.
    * rnd; skip => /> H0 H1 H2.
      have ->: (fun (x : zpmatrix) => x = m0 /\ rows x = m /\ cols x = m) = pred1 m0 by smt().
      rewrite -{1}H1 -{1}H2 mu1_dmatrix_fu; 1:apply duni_funi.
      rewrite mu1_duni H1 H2 /= RField.exprVn; 1:smt(m_ge0).
      rewrite RField.exprVn; 1: smt(m_ge0 gt0_n).
      rewrite -RField.exprM => /#.
    * rnd; skip => /> H0 H1 H2 _ _.
      have ->: ((fun (x : zpvector) => x = v0 /\ (size x = m) = true)) = pred1 v0.
      - apply fun_ext => v. 
        rewrite /pred1 /#.
      rewrite -H0 mu1_dvector_fu; 1:apply duni_funi.
      rewrite mu1_duni H0 RField.exprVn /=; 1:smt(m_ge0 gt0_n).
      rewrite RField.exprVn /=; 1:smt(m_ge0).
      by rewrite -RField.exprM.
    * hoare => //=; rnd; auto => /> &hr H0 v cont.
      rewrite 5!negb_and in H0.
      apply size_dvector in cont.
      smt(m_ge0 eq_vectorP eq_matrixP).
    * move => H0 H1 H2; byphoare => //; proc.
      wp; rnd; skip => />.
      rewrite (pred_split (fun (x: zpmatrix) => size x = (m+1, m))) mu_disjointL.
      - by rewrite /predI /predC. 
      have ->: predI (fun (x : zpmatrix) => trmx (subm x 0 m 0 m) = m0 /\ row x m = v0)
      (fun (x : zpmatrix) => size x = (m + 1, m)) = pred1 (trmx m0 / rowmx v0).
      - apply fun_ext => m1.
        rewrite /pred1 eq_iff => />.
        rewrite 3!submT catmcT 2!trmxK; split => [H3 H4 H5 H6 |].
        + rewrite rowmx_row_eq_subm -H5 -{2}H6 catmc_subm /#.
        split. 
        + split; 1: rewrite -{1}H1 -H2 subm_catmrCl // rows_tr cols_rowmx /#.
          rewrite row_catmcR /=. 
          * rewrite cols_tr cols_rowmx /#. 
          * rewrite rows_tr /#.
          by rewrite rows_tr H2 addrN rowK.
        rewrite rows_catmc /= cols_catmc /= cols_tr 1:cols_rowmx.
        rewrite rows_tr rows_rowmx /#.
      have [H3 H4]: size (trmx m0 / rowmx v0) = (m+1, m). 
      - rewrite rows_catmc /= cols_catmc /=.
        rewrite rows_tr rows_rowmx cols_tr cols_rowmx /#.
      rewrite -{1}H3 -{1}H4 mu1_dmatrix_fu; 1: exact duni_funi.
      rewrite H3 H4 mu1_duni /= mu0_false /= => [x cont |].
      - apply size_dmatrix in cont.
        rewrite /predI /predC /#.
      rewrite mulzDl /= RField.exprD.
      - rewrite RField.unitrV.
        apply/gtr_eqF/expr_gt0.
        smt(ge2_p).
      rewrite -RField.exprVn. smt(gt0_n).
      rewrite -2!RField.exprM /#.
  + hoare => /> => [H |].
    * byphoare => //; hoare; proc.
      auto => /> mA_tr cont.
      smt(size_subm size_tr size_row eq_vectorP eq_matrixP m_ge0 size_dmatrix).
    * seq 1: (#pre /\ size mA = (m, m)).
      - auto => /> H mA.
        smt(size_dmatrix m_ge0).
      auto => /> &hr H0 H1 H2 v.
      smt(size_dvector m_ge0).
- byphoare => //; hoare => />.
  + byphoare => //.
  proc.
  seq 1: (size mA = (m, m)); 1: (auto => /> mA; smt(size_dmatrix m_ge0)).
  auto => /> &hr H0 H1 H2 v.
  smt(size_dvector m_ge0).
qed.

import StdBigop.Bigreal.BRM.

(* Sampling a vector and one additional element is equivalent to sampling a larger vector *)
module VecSampler1 = {
  proc main() = {
    var e2, e3;
    e2 <$ dvector dnoise m;
    e3 <$ dnoise;
    return (e2, e3);
  }
}.

module VecSampler2 = {
  proc main() = {
    var e;
    e <$ dvector dnoise (m+1);
    return e;
  }
}.

equiv vec_sampler_equiv: VecSampler1.main ~ VecSampler2.main: true ==> (res.`1{1} || vectc 1 res.`2{1}) = res{2} /\ 
    (size res{2} = (m + 1)).
proof.
bypr (res.`1{1} || vectc 1 res.`2{1}, size res.`1{1}) (res{2}, m); progress.
- by rewrite size_catv -H size_vectc /max.
case (size a.`1 = m + 1 /\ a.`2 = m) => Ha.
- byphoare => //.
  proc.
  seq 1: (subv a.`1 0 m = e2) (bigi predT (fun x => mu1 dnoise a.`1.[x]) 0 m) (mu1 dnoise a.`1.[m]) (1%r-(bigi predT (fun x => mu1 dnoise a.`1.[x]) 0 m)) 0%r => // />.
  + rnd; skip => />.
    have ->: (=) (subv a.`1 0 m) = pred1 (subv a.`1 0 m) by smt().
    have size_sub: size (subv a.`1 0 m) = m by simplify; smt(m_ge0 size_subv).
    rewrite -{1}size_sub dvector1E /= size_subv /=.
    have ->: max 0 m = m by smt(m_ge0).
    apply eq_big_seq => x range_cont /=.
    rewrite mem_range in range_cont.
    rewrite get_subv /#.
  + rnd; auto => />.
    rewrite size_subv /=.
    have -> //:(fun x => (subv a.`1 0 m || vectc 1 x, max 0 m) = a) = pred1 a.`1.[m].
    rewrite fun_ext => x />.
    rewrite eq_iff. 
    have ->: ((subv a.`1 0 m || vectc 1 x, max 0 m) = a) <=> 
              (subv a.`1 0 m || vectc 1 x) = a.`1 by smt(m_ge0).
    split => [H0 | H1].
    * rewrite eq_vectorP in H0.
      elim H0 => /= H0 H1.
      rewrite -H1; 1:smt(m_ge0).
      rewrite get_catv' getv0E /= size_subv; 1:smt(m_ge0).
      rewrite ComRing.add0r.
      rewrite get_vectc; smt(m_ge0).
    have ->: vectc 1 x = subv a.`1 m (m+1).
    * apply eq_vectorP => /=.
      split => [| i bound]. 
      - rewrite size_subv size_vectc; smt(m_ge0).
      have ->: i = 0 by smt(size_vectc).
      rewrite get_vectc // get_subv /#.
    elim Ha => Ha _.
    rewrite -Ha catv_subvC; smt(m_ge0).
  + hoare.
    rnd; skip => /> &hr neq e3 _.
    rewrite -negP => H1.
    apply neq.
    rewrite -(subv_catvCl e2{hr} (vectc 1 e3)) => /#.
  + byphoare => //.
    proc.
    rnd; skip => />.
    have ->: (fun (x : zpvector) => (x, m) = a) = pred1 a.`1 by smt().
    elim Ha => H0 H1.
    rewrite -{1}H0 dvector1E H0.
    rewrite big_int_recr; 1:exact m_ge0.
    by congr.
- byphoare => //.
  hoare => />.
  + byphoare => //.
    hoare; proc.
    auto => /> e /size_dvector size_e.
    rewrite -negP => H0.
    apply Ha. 
    smt(m_ge0).
  + proc; auto => /> e2 /size_dvector size_e2 e3 _.
    rewrite -negP => H1.
    apply Ha.
    rewrite -H1 /= size_catv /=.
    smt(size_vectc m_ge0).
qed.

(********************************************************************************)
(** We now model the proper LWE public key encryption scheme with error terms  **)
(** as described by Lyubashevsky.                                              **)
(********************************************************************************)

abbrev (-) = PolyReduceZp.ComRing.(-).

module LWEpke = {
  (*** Key generation ***)
  proc kg() = {
      var pk, sk, mA, t, s, e1;
      (* Uniformly random vector with elements      *)
      (* having coefficients between -beta and beta *)
      s  <$ dvector dnoise m;

      (* Error vector with elements having          *)
      (* coefficients between -beta and beta        *)
      e1 <$ dvector dnoise m; 
      
      (* Uniformly random matrix over Z/pZ          *)
      mA <$ dmatrix duni m m; 
      (* Matrix times vector s plus error vector    *)
      t  <- mA *^ s + e1;
      
      (* The secret key is s and the public key     *)
      (* is the matrix and the vector t             *)
      sk <- s;
      pk <- (mA, t);
      return (pk, sk);
  }

  (*** Encryption ***)
  proc enc(pk:pkey, pt:ptext) = {
    var r, e2, e3, mA, t,  u, v;
    var x: bool;

    if (size pt <> n) { (* Validate the length of the plaintext *)
         x <$ dnull;
    }

    (mA, t) <- pk;

    (* Random vectors r and e2 with elements having      *)
    (* coefficients between -beta and beta, and a random *)
    (* element in Z_p/<x^n-1> with coefficients          *)
    (* between -beta and beta                            *)
    r  <$ dvector dnoise m;
    e2 <$ dvector dnoise m;
    e3 <$ dnoise;
    
    (* u is the vector r times the matrix plus e2        *)
    u <- r ^* mA + e2;

    (* Compute v as the dot product of r and t           *)
    (* plus e3 plus the plaintext bit times p/2          *)
    v <- dotp r t + e3 + Zp.inzmod (p %/ 2) ** bits_to_poly pt;

    (* The ciphertext is (u,v)                           *)
    return (u,v);
  }

  (*** Decryption ***)
  proc dec(sk:skey, c:ctext) = {
    var u, v, d;

    (u, v) <- c;

    (* First compute d = v - < u,sk >            *)
    d <- v - (dotp u sk);

    return Some (decode d);

  }
}.

(********************************************************************************)
(*** Key generation, encryption and decryption terminate on correct input     ***)
(********************************************************************************)

lemma kg_ll: islossless LWEpke.kg.
proc.
auto => />.
rewrite dvector_ll. rewrite dnoise_ll.
rewrite dmatrix_ll // duni_ll.
qed.

lemma enc_valid_ll: phoare[LWEpke.enc: size arg.`2 = n ==> true] = 1%r.
proc.
rcondf 1 => //.
auto => />.
by rewrite dvector_ll dnoise_ll.
qed.

lemma dec_ll: islossless LWEpke.dec by proc; auto.

(********************************************************************************)
(*** Slight modification of LWEpke, where we now store the total error in a   ***)
(*** variable we call er. The rest of the game is identical to LWEpke.        ***)
(********************************************************************************)

module LWEpke' = {

  var er : polyXnD1
  var r  : zpvector
  var e1 : zpvector
  var e2 : zpvector
  var e3 : polyXnD1
  var s  : zpvector

  proc kg() = {
    var pk, sk, mA, t;

    s  <$ dvector dnoise m;

    e1 <$ dvector dnoise m; 

    mA <$ dmatrix duni m m; 
    t  <- mA *^ s + e1;

    sk <- s;
    pk <- (mA, t);
    
    return (pk, sk);
  }

  proc enc(pk:pkey, pt:ptext) = {
    var  mA, t,  u, v; 
    var x: bool;

    if (size pt <> n) { (* Validate the length of the plaintext *)
         x <$ dnull;
    }
    (mA, t) <- pk;

    r  <$ dvector dnoise m;
    e2 <$ dvector dnoise m;
    e3 <$ dnoise;
    
    u <- r ^* mA + e2;
    v <- dotp r t + e3 + Zp.inzmod (p %/ 2) ** bits_to_poly pt;

    return (u,v);
  }

  proc dec(sk:skey, c:ctext) = {
    var u, v, d;

    (u, v) <- c;

   (****************************************)
   (** Here we compute the total error    **)
   (****************************************)
    er <- dotp r e1 + e3 - (dotp e2 s);
   (****************************************)
   (****************************************)

    d <- v - (dotp u sk);
    
    return Some (decode d);

  }
}.  

(********************************************************************************)
(*** Show that LWEpke is correct if and only if LWEpke' is correct            ***)
(********************************************************************************)

equiv LWEpke_LWEpke'_equiv : 
    Correctness(LWEpke).main ~ Correctness(LWEpke').main : ={m} ==> ={res} by sim.

(********************************************************************************)
(*** Show that if the total error in LWEpke' is less than p/4, the decryption ***)
(*** algorithm is always correct.                                             ***)
(********************************************************************************)

hoare LWEpke'_small_error_correct : Correctness(LWEpke').main: 
          true ==> distpoly LWEpke'.er zeroXnD1 < p %/ 4 => res.  
proof. 
proc;inline*. 
(*** We show that d = total error plus encrypted bit times p/2              ***)
seq 22 : (d = LWEpke'.er + Zp.inzmod (p %/ 2) ** bits_to_poly m /\ size m = n) => //.
- case (size m <> n) => /=; auto => />.
  + rcondt 10; 1: auto => />.
    rnd; auto => /> _ _ _ _ _ _ _ _ x; 1: by rewrite supp_dnull.
  rcondf 10; auto.
  auto => /> &hr _ s /size_dvector size_s e1 /size_dvector size_e1 mA1
          /size_dmatrix size_mA1 r /size_dvector size_r e2 /size_dvector
          size_e2 e3 _.
  move: (Zp.inzmod (p%/ 2) ** bits_to_poly m {hr}) => x. 
  clear &hr.
  rewrite dotpDr dotpDl. (* dotpDl very slow for some reason *)
  rewrite dotp_mulmxv.
  move: (dotp (r ^* mA1) s). move: (dotp r e1). move: (dotp e2 s). move => u z y.
  (* Feeding these moves in one by one takes ages for some reason *)
  clear size_s size_e2 size_e1 size_r size_mA1 s e1 mA1 r e2.
  rewrite ComRing.subr_eq -ComRing.addrA -ComRing.addrA ComRing.addrC.
  rewrite -5!ComRing.addrA. 
  do 2! congr.
  rewrite (ComRing.addrC (-u)) -ComRing.addrA.
  congr. 
  by rewrite -ComRing.addrA (ComRing.addrN u) ComRing.addr0.
auto => &hr [d_eqn size_m] err_bound.
congr.
apply (eq_from_nth witness); 1: by rewrite size_decode size_m.
rewrite size_decode /decode => i bound.
rewrite (nth_map witness) /= 1:size_range 1:/#.
rewrite /decode_coeff nth_range //= d_eqn rcoeffD rcoeffZ.
have ->: (bits_to_poly m{hr}).[i] = bit_to_zp (nth witness m{hr} i).
- by rewrite /ptext_to_poly rcoeffZ_sum.
case (nth witness m{hr} i) => _.
- rewrite /bit_to_zp /= Zp.ZModpRing.mulr1 distmodp_zero -Zp.ZModpRing.addrA.
  rewrite Zp.ZModpRing.addrN Zp.ZModpRing.addr0.
  rewrite -(Zp.ZModpRing.opprK (Zp.inzmod _)) -distmodp_zero.
  rewrite -{1}dist_neg -(dist_neg LWEpke'.er{hr}.[i]) Zp.ZModpRing.oppr0.
  rewrite Zp.ZModpRing.opprK StdOrder.IntOrder.ltrW // dist_asint_low.
  rewrite -dist_neg Zp.ZModpRing.opprK Zp.ZModpRing.oppr0.
  apply (StdOrder.IntOrder.ler_lt_trans (distpoly LWEpke'.er{hr} zeroXnD1)).
  + rewrite /distpoly.
    apply listmax_gt_in; 1,2: smt().
    rewrite mapP.
    exists i.
    by rewrite mem_range bound /= rcoeff0.
  + apply err_bound.
- rewrite /bit_to_zp /= Zp.ZModpRing.mulr0 Zp.ZModpRing.addr0.
  suff : distmodp LWEpke'.er{hr}.[i] Zp.zero < 
         distmodp LWEpke'.er{hr}.[i] ((Zp.inzmod (p %/ 2))) by smt().
  have err_i_bound: distmodp LWEpke'.er{hr}.[i] Zp.zero < p %/ 4.
  + apply (StdOrder.IntOrder.ler_lt_trans (distpoly LWEpke'.er{hr} zeroXnD1)).
    * rewrite /distpoly.
      apply listmax_gt_in; 1,2: smt().
      rewrite mapP.
      exists i.
      by rewrite mem_range bound /= rcoeff0.
    * apply err_bound.
  + by apply dist_asint_low.
qed. 

(********************************************************************************)
(*** Prove that the probability of decrypting correctly in LWEpke is greater  ***)
(*** than or equal to the probability of the total error being below p/4.     ***)
(********************************************************************************)

lemma LWEpke'_correct_bounded_error &m pt : 
    Pr[Correctness(LWEpke').main(pt) @ &m : distpoly LWEpke'.er zeroXnD1 < p %/ 4] <=
     Pr[Correctness(LWEpke').main(pt) @ &m : res]. 
byequiv => //.
conseq (_: ={m} /\ m{1} = pt ==> ={res, LWEpke'.er}) (_: true ==> true) 
       (_: true ==>  distpoly LWEpke'.er zeroXnD1 < p %/ 4 => res) => // />.
- exact LWEpke'_small_error_correct.
proc.
call (: ={arg, LWEpke'.s, LWEpke'.r, LWEpke'.e1, LWEpke'.e2, LWEpke'.e3} ==> 
        ={res, LWEpke'.er}); 1: sim.
call (: ={arg, LWEpke'.s, LWEpke'.e1} ==> 
        ={res, LWEpke'.s, LWEpke'.r, LWEpke'.e1, LWEpke'.e2, LWEpke'.e3}); 1: sim.
call (: ={arg} ==> ={res, LWEpke'.s, LWEpke'.e1}); 1: sim.
auto.
qed.

lemma LWEpke_correct_bounded_error &m pt : 
    Pr[Correctness(LWEpke').main(pt) @ &m : distpoly LWEpke'.er zeroXnD1 < p %/ 4] <=
     Pr[Correctness(LWEpke).main(pt) @ &m : res]. 
proof. 
have -> :  Pr[Correctness(LWEpke).main(pt) @ &m : res] = Pr[Correctness(LWEpke').main(pt) @ &m : res]
  by byequiv (LWEpke_LWEpke'_equiv). 
exact/LWEpke'_correct_bounded_error. 
qed.

(********************************************************************************)
(***                            Security proof                                ***)
(********************************************************************************) 

section Security. 

(* PKE adversary which always terminates and only chooses valid plaintexts *)
declare module A <: PKElwe.Adversary. 
declare axiom Ac_ll : islossless A.choose. 
declare axiom Ag_ll : islossless A.guess. 
declare axiom Ac_valid : hoare[A.choose: true ==> size res.`1 = n /\ size res.`2 = n].

(** Adversary Reductions **)

(* Reduction: from a PKE adversary, construct a MLWE adversary *)
module RedLWEAdv: AdvMLWE = {
  proc guess(mA, t) : bool = {
    var m0, m1, b, b', r, e2, e3, pt;
    var x: bool;
    (m0, m1) <@ A.choose(mA, t);
       b     <$ {0,1};
       pt    <- if b then m1 else m0;
       if (size pt <> n) {
         x <$ dnull;
       }
       r     <$ dvector dnoise m;
       e2    <$ dvector dnoise m;
       e3    <$ dnoise;
       b'    <@ A.guess(r ^* mA + e2, (dotp r t) + e3 + Zp.inzmod (p %/ 2) ** bits_to_poly pt);
    return b = b';
  }
}.

(* Reduction terminates *)
lemma red_guess_ll: islossless RedLWEAdv.guess.
proof.
proc; call (:true); 1: apply Ag_ll.
auto => /=; conseq (:true) => />; 1: by rewrite dvector_ll dnoise_ll.
rcondf 4 => />; auto; 1: (call Ac_valid; by auto => /> result size_m0 size_m1 []).
call Ac_ll; auto => />.
apply dbool_ll.
qed.

(* Reduction: from a PKE adversary, construct a higher dimensional LWE adversary *)
module LiftLWEAdv: AdvMLWE = {
  proc guess(mAt_tr, rmAt: zpvector) : bool = {
    var mAt, mA, t, m0, m1, b, b', rmA, rt, pt;
    var x: bool;
    mAt <- trmx mAt_tr;
    mA <- subm mAt 0 (rows mAt) 0 (cols mAt -1);
    t  <- col mAt (cols mAt -1);
    (m0, m1) <@ A.choose(mA, t);
    b <$ {0,1};
    pt <- if b then m1 else m0;
    if (size pt <> n) {
      x <$ dnull;
    }
    rmA <- subv rmAt 0 (size rmAt -1);
    rt <- rmAt.[size rmAt -1];
    b'    <@ A.guess(rmA, rt + Zp.inzmod (p %/ 2) ** bits_to_poly pt);
    return b = b';
  }
}. 

(* Reduction terminates *)
lemma lift_guess_ll: islossless LiftLWEAdv.guess.
proof.
proc; call (:true); 1: apply Ag_ll.
auto => /=; sp.
rcondf 4 => />; auto.
- call Ac_valid.
  by auto => /> result size_m0 size_m1 [].
call Ac_ll; auto => />.
apply dbool_ll.
qed.

(* Bridging step to prepare for further modifications    *)
(* This is simply IND-CPA for LWEpke written out *)
module G0 = {
  proc main() : bool = {
    var pk, sk, mA, t, s, r, u, v, e1, e2, e3;
    var m0, m1, pt, c;
    var b, b';
    var x: bool;

    (* Key generation *)
    s  <$ dvector dnoise m;
    e1 <$ dvector dnoise m; 
    mA <$ dmatrix duni m m;
    t  <- mA *^ s + e1;
    sk <- s;
    pk <- (mA, t);

    (* Adversary chooses two messages *)
    (m0, m1) <@ A.choose(pk);

    (* Randomly choose which message to encrypt *)
    b <$ {0,1};
    pt <- if b then m1 else m0;
    if (size pt <> n) {
      x <$ dnull;
    }
    
    (* Encrypt mb *)
    r <$ dvector dnoise m;
    e2 <$ dvector dnoise m;
    e3 <$ dnoise;
    
    (* u is the vector r times the matrix plus e2 *)
    u <- r ^* mA + e2;
 
    v <- (dotp r t) + e3 + Zp.inzmod (p %/ 2) ** bits_to_poly pt;
    c <- (u,v);
  
    (* Adversary makes a guess *)
    b' <@ A.guess(c);

    return (b = b');
  }
}. 

(* Prove that G0 is equivalent to the original security experiment *)
lemma LWE_cpa_G0_equiv &m : 
  Pr[CPA(LWEpke, A).main() @ &m : res] = Pr[G0.main() @ &m : res]. 
proof. 
byequiv (_: ={glob A} ==> ={res}) => //.  
proc;inline*. 
call(_:true); auto.
seq 3 3: (={glob A, s, e1, mA}); 1:sim.
sp; seq 1 1: (#pre /\ ={m0, m1}).
- call(_:true); auto.
seq 1 1: (#pre /\ ={b}); auto.
sp; if; auto => />. 
- by move => /> &1 _ b; rewrite supp_dnull.
move => /> &1 size_pt _ _ _ _ _ e3 b /#.
qed. 

(* Prove that G0 is equivalent to LWE0, the LWE game where the adversary gets *)
(* the real LWE sample *)
lemma G0_LWEadv0_equiv &m: Pr[G0.main() @ &m : res] = 
  Pr[MLWE0(RedLWEAdv).main(dvector dnoise m,m,m) @ &m : res]. 
proof.    
byequiv (_: ={glob A} /\ arg{2} = (dvector dnoise m,m,m) ==> _) => //. 
proc;inline*. 
swap{1} 3 -2. 
seq 3 3: (#pre /\ ={mA, s} /\ e1{1} = e{2}); 1: auto.
wp; call(_:true); auto.
sp; seq 1 1: (#pre /\ ={m0, m1}); 1: (call (: true); auto => />).
seq 1 1: (#pre /\ b{1} = b0{2}); 1: auto. 
sp; if; auto.
qed.

(* We now make the first change to G0, namely that we sample a random public key *)
(* rather than computing the public key as (mA, mA *^ s).                        *)
(* By the DLWE assumption, this is indistinguishable from G0.                    *)
module G1(A:PKElwe.Adversary) = {
  proc main() : bool = {
    var pk, mA, t, r, u, v, e2, e3;
    var m0, m1, c, pt;
    var b, b';
    var x: bool;

    (* Key generation, now with uniformly random keys *)
    mA <$ dmatrix duni m m;
    t  <$ dvector duni m;
    pk <- (mA, t);

    (* Adversary chooses two messages *)
    (m0, m1) <@ A.choose(pk);

    (* Randomly choose which message to encrypt *)
    b <$ {0,1};
    pt <- if b then m1 else m0;
    if (size pt <> n) {
      x <$ dnull;
    }
    
    (* Encrypt mb *)
    r <$ dvector dnoise m;
    e2 <$ dvector dnoise m;
    e3 <$ dnoise;
    
    u <- r ^* mA + e2;
    v <- (dotp r t) + e3 + Zp.inzmod (p %/ 2) ** bits_to_poly pt;
    c <- (u,v);
  
    (* Adversary makes a guess *)
    b' <@ A.guess(c);

    return (b = b');
  }
}. 

(* Show that G1 is equivalent to LWE1, the LWE game with randomly sampled LWE sample *)
lemma G1_LWEadv1_equiv &m : Pr[G1(A).main() @ &m : res] = 
  Pr[MLWE1(RedLWEAdv).main(dvector dnoise m,m,m) @ &m : res]. 
proof. 
byequiv (_: ={glob A} /\ arg{2} = (dvector dnoise m,m,m) ==> _) => //. 
proc; inline*; wp. 
call(_:true); 1: auto. 
seq 6 7 : (={glob A, mA, t, m0, m1, pt} /\ b{1} = b0{2} /\ mA{1} = mA0{2}); first last.
- if; auto. 
wp; rnd.
call(_:true); auto. 
qed.

lemma G1_LiftLWEadv0_equiv &m : Pr[G1(A).main() @ &m : res] = 
  Pr[MLWE0(LiftLWEAdv).main(dvector dnoise m,m+1,m) @ &m : res]. 
proof.
byequiv (_: ={glob A} /\ arg{2} = (dvector dnoise m,m+1,m) ==> _) => //. 
proc;inline*. 
swap{2} 5 3; swap{2} [2..3] 4.
seq 2 5: (={glob A, t} /\ mA{1} = mA0{2} /\ (mA = (trmx mA0 / rowmx t) /\ (r, c) = (m+1, m)){2} /\ size mA{1} = (m, m) /\ size mA{2} = (m+1, m) /\ size t{2} = m /\ ds{2} = dvector dnoise m).
- transitivity*{1} {(mA, t) <@ Sampler1.main();} => //; 1: smt().
  + inline*; auto.
  transitivity{2} {(mA0, t) <@ Sampler2.main(); mA <- (trmx mA0 / rowmx t);}
(={glob A} /\ (ds,r,c){2} = (dvector dnoise m,m + 1, m) ==> 
  ={glob A, t} /\
  mA{1} = mA0{2} /\
  mA{2} = trmx mA0{2} / rowmx t{2} /\
  size mA{1} = (m, m) /\ size mA{2} = (m + 1, m) /\
  (ds,r,c){2} = (dvector dnoise m,m + 1, m) /\
  size t{1} = m)
(={glob A, mAt_tr, mA} /\ (ds,r,c){2} = (dvector dnoise m,m + 1, m) ==>  
  ={glob A, t, mA, mA0} /\ (
  mA = trmx mA0 / rowmx t /\
  mAt_tr = mA /\
  size mA = (m + 1, m) /\ 
  (ds,r,c){2} = (dvector dnoise m,m + 1, m) /\
  size t = m){2}); first 2 smt().
  + wp; call (sampler_equiv) => //. 
    skip => /> [mx v] /= rows_mx cols_mx size_v.
    rewrite rows_catmc rows_tr rows_rowmx cols_catmc cols_tr cols_rowmx /#.
  inline*.
  auto => /> mAt_tr /size_dmatrix size_mAt_tr. 
  have [rows_mAt_tr cols_mAt_tr]: size mAt_tr = (m + 1, m) by smt(m_ge0).
  clear size_mAt_tr.
  rewrite rows_mAt_tr /= cols_mAt_tr /=.
  split.
  + rewrite rowmx_row_eq_subm trmxK -rows_mAt_tr -cols_mAt_tr.
    rewrite submT catmc_subm 1:/# /=.
    rewrite col_trmx cols_tr; split => [/# |].
    rewrite rows_tr /#.
  + rewrite submT trmxK col_trmx rowmx_row_eq_subm size_row cols_mAt_tr /=.
    rewrite cols_tr rows_mAt_tr /= -rows_mAt_tr -cols_mAt_tr rows_tr.
    rewrite catmc_subm /#.
swap{1} [7..8] -6.
swap{2} 2 -1.
seq 2 1 :(#pre /\ (e2{1} || vectc 1 e3{1}) = e{2} /\ size e2{1} = m). 
- transitivity*{1} {(e2, e3) <@ VecSampler1.main();} => // />; 1: smt().
  + inline*; auto.
  transitivity{2} {e <@ VecSampler2.main();}
 (={glob A, t}  /\ mA{1} = mA0{2} /\ mA{2} = trmx mA0{2} / rowmx t{2} /\ (r, c){2} = (m+1, m) /\ size mA{1} = (m, m) /\ size mA{2} = (m+1, m) /\ size t{2} = m ==> ={glob A, t}  /\ mA{1} = mA0{2} /\ mA{2} = trmx mA0{2} / rowmx t{2} /\ (r, c){2} = (m+1, m) /\ size mA{1} = (m, m) /\ size mA{2} = (m+1, m) /\ size t{2} = m /\ (e2{1} || vectc 1 e3{1}) = e{2} /\ size e{2} = m + 1)
(={glob A, t, mA} /\ r{2} = m + 1 ==> ={glob A, t, mA, e}) => // />; 1: smt().
  + move => &1 &2 &3 _ _ _ _ _. rewrite size_catv size_vectc /#.
  + call vec_sampler_equiv; auto.
  + inline*; auto => />.
wp; call(_: true); wp. 
swap{1} 6 -4.
swap{1} 2 -1.
seq 4 4 : (#pre /\ ={m0, m1} /\ b{1} = b0{2} /\ mA{1} = mA0{2} /\ r{1} = s{2} /\
          (rmAt = mA *^ s + e){2} /\ size s{2} = m).
- rnd.
  call(_: true).
  auto => /> _ _ _ _ _ _ _ _ r /size_dvector -> _ _; 1: smt(m_ge0).
sp; if => //.
- auto => /> &1 &2 _ _ _ _ _ _ _ _ x.
  by rewrite supp_dnull.
auto => /> &1 &2 rows_mA0 cols_mA0 rows_tr' cols_tr' size_t size_e2 size_s.
move: (if b0{2} then m1{2} else m0{2}) => pt size_pt.
split.
- rewrite size_addv /= size_catv size_e2 size_col rows_mulmx /=.
  rewrite rows_catmc rows_tr rows_rowmx size_vectc cols_mA0 /max /= subv_addv.
  + rewrite /= size_catv size_vectc size_col rows_mulmx rows_catmc.
    rewrite rows_tr rows_rowmx /#.
  rewrite mulmxvE catmcDl col_catmc.
  have {1}->: m = size (trmx mA0{2} *^s{2}). 
  + rewrite size_col rows_mulmx rows_tr /#.
  rewrite -size_e2 !subv_catvCl -mulmxvE mulmxTv.
congr.
rewrite size_addv size_col rows_mulmx rows_catmc size_catv rows_tr cols_mA0.
rewrite size_e2 /= mulmxvE catmcDl rows_rowmx size_vectc /max /= col_catmc.
rewrite get_addv get_catv size_col rows_mulmx rows_tr. 
have -> /=:!m < cols mA0{2} by smt().
rewrite cols_mA0 get_col /= -dotp_eqv_mul dotpC get_catv.
have -> /=:!m < size e2{1} by smt().
by rewrite size_e2 /= get_vectc.
qed.

(* We now replace the ciphertext input to the adversary with random elements *)
module G2(A:PKElwe.Adversary) = {
  proc main() : bool = {
    var pk, mA, mAt_tr, mAt, t, u, u', v, pt;
    var m0, m1;
    var b, b';
    var x: bool;

    (* Key generation, now with uniformly random keys *)
    mAt_tr <$ dmatrix duni (m+1) m;
    mAt <- trmx mAt_tr;
    mA <- subm mAt 0 (rows mAt) 0 (cols mAt -1);
    t <- col mAt (cols mAt -1);
    pk <- (mA, t);

    (* Adversary chooses two messages *)
    (m0, m1) <@ A.choose(pk);

    (* output random ciphertext *)
    u'  <$ dvector duni (m+1);
    u <- subv u' 0 (size u' -1);
    v <- u'.[size u' -1];
  
    (* Adversary makes a guess *)
    b' <@ A.guess(u, v);

    b <$ {0,1};
    pt <- if b then m1 else m0;
    if (size pt <> n) {
      x <$ dnull;
    }
    return b = b';
  }
}.

(* G2 is equivalent to the LWE1 game with m+1 rows, where we give the adversary a random LWE sample *)
lemma G2_LiftLWEadv0_equiv &m : Pr[G2(A).main() @ &m : res] =
  Pr[MLWE1(LiftLWEAdv).main(dvector dnoise m,m+1,m) @ &m : res].
proof.
byequiv => //.
proc.
inline*.
wp.
swap{1} [11..13] -4.
call(_: true).
wp.
swap{2} 4 7.
swap{2} 2 8.
wp.
rnd (fun (u: zpvector) => u - (zerov m || vectc 1 ( (Zp.inzmod (p %/ 2)) ** bits_to_poly pt{2})))
(fun (u: zpvector) => u + (zerov m || vectc 1 ( (Zp.inzmod (p %/ 2)) ** bits_to_poly pt{2}))) => //.
seq 1 1: (#pre /\ mAt_tr{1} = mA{2}); 1: auto.
wp; seq 7 7: (={pt} /\ (size pt{1} = n => #post)); wp.
- rnd.
  call(_: true).
  wp.
  auto => /> [pt0 pt1] b _ /=.
  move: (if b then pt1 else pt0) => pt. 
  clear pt1 pt0 b => size_pt.
  split => [u /size_dvector size_u | _].
    (* Much slower than it should be *)
  + rewrite -addvA (addvN (zerov m || vectc 1 ((Zp.inzmod (Top.p %/ 2)) ** bits_to_poly pt))). 
    rewrite size_catv !size_vectc lin_addv0; smt(m_ge0).
  split => [u /size_dvector size_u | _ u /size_dvector size_u].
  + apply dvector_uni; 1: exact duni_uni.
    * have ->: m + 1 = size u by smt(m_ge0).
      apply/dvector_fu/duni_fu.
    have ->: m + 1 = size (u + (zerov m || vectc 1 ((Zp.inzmod (p %/ 2)) ** bits_to_poly pt))).
    * rewrite size_addv /= size_catv /= !size_vectc; smt(m_ge0).
    apply/dvector_fu/duni_fu.
  split => [| _].
  + have ->: m + 1 = size (u - (zerov m || vectc 1 ((Zp.inzmod (p %/ 2)) ** bits_to_poly pt))).
    * rewrite size_addv /= size_oppv size_catv !size_vectc; smt(m_ge0).
    apply/dvector_fu/duni_fu.
  split => [| _].
  + rewrite -addvA (addvC (Vectors.([-]) _)).
    (* Much slower than it should be *)
    rewrite (addvN (zerov m || vectc 1 ((Zp.inzmod (Top.p %/ 2)) ** bits_to_poly pt))).
    rewrite size_catv /= !size_vectc lin_addv0; smt(m_ge0).
  split.
  + rewrite subv_addv /=.
    * rewrite size_oppv size_catv !size_vectc; smt(m_ge0).
    rewrite size_addv size_oppv  size_catv !size_vectc.
    have -> /=: size u = max 0 m + max 0 1 by smt(m_ge0). 
    rewrite oppv_catv /max /=. 
    have ->: (if 0 < m then m else 0) = m by smt(m_ge0). 
    have {4}->: m = size (- zerov m); 1:(rewrite size_oppv size_vectc; smt(m_ge0)).
    rewrite subv_catvCl oppv_zerov lin_addv0; smt(m_ge0 size_subv).
  rewrite get_addv size_addv size_oppv size_catv !size_vectc.
  have -> /=: size u = max 0 m + max 0 1 by smt(m_ge0).
  rewrite /max /=.
  have ->: (if 0 < m then m else 0) = m by smt(m_ge0).  
  rewrite getvN get_catv size_vectc.
  have -> /=: !m < max 0 m by smt(m_ge0).
  rewrite get_vectc; 1: smt(m_ge0).
  move: u.[m] (Zp.inzmod (p%/2) ** bits_to_poly pt) => x y.
  clear u size_u &m pt size_pt. 
  by rewrite -ComRing.addrA ComRing.addNr ComRing.addr0.
if => //. 
auto => /> &1 &2 _ _ x.
by rewrite supp_dnull.
qed.


(* Prove that the probability of winning in G2 is equal to 1/2 *)
lemma G2_half &m : 
    Pr[G2(A).main() @ &m : res] = 1%r/2%r. 
proof. 
byphoare => //. 
proc. 
rcondf 13.
- wp; rnd.
  call(_: true); wp.
  rnd.
  call(_: true ==> size res.`1 = n /\ size res.`2 = n).
  + apply Ac_valid.
  auto => /> _ _ [m0 m1] /= size_m0 size_m1 _ _ [] _ //=.
wp; rnd (pred1 b'). 
call(Ag_ll). 
auto. 
call(Ac_ll). 
auto => />. 
smt(dmatrix_ll dvector_ll duni_ll dbool1E).
qed.      

(*******************************************************************)
(***      Proving a bound for the advantage in the CPA game      ***)
(*******************************************************************)
lemma LWE_bound_advantage &mem:
   Pr[CPA(LWEpke, A).main() @ &mem : res] <=  1%r/2%r 
           + 2%r * `|Pr[DMLWE( RedLWEAdv).main(dvector dnoise m,m  ,m) @ &mem : res] - 1%r/2%r|
           + 2%r * `|Pr[DMLWE(LiftLWEAdv).main(dvector dnoise m,m+1,m) @ &mem : res] - 1%r/2%r|.
proof.
rewrite LWE_cpa_G0_equiv G0_LWEadv0_equiv.
rewrite -(ler_add2r (-Pr[MLWE1(RedLWEAdv).main(dvector dnoise m,m, m) @ &mem : res])).
apply (ler_trans (`|Pr[MLWE0(RedLWEAdv).main(dvector dnoise m,m, m) @ &mem : res] -
Pr[MLWE1(RedLWEAdv).main(dvector dnoise m,m, m) @ &mem : res]|)); 1:smt().
rewrite (pr_MLWE_LR &mem (RedLWEAdv)); 1:apply (red_guess_ll).
rewrite -{1}(RField.addr0 (2%r * _)) (RField.addrC (1%r / _)) -(RField.addrA) -(RField.addrA _ (1%r /_)) ler_add2l.
rewrite RField.addrA ler_subr_addr RField.add0r.
rewrite -G1_LWEadv1_equiv G1_LiftLWEadv0_equiv.
rewrite -(ler_add2r (-Pr[MLWE1(LiftLWEAdv).main(dvector dnoise m,m+1, m) @ &mem : res])).
apply (ler_trans (`|Pr[MLWE0(LiftLWEAdv).main(dvector dnoise m,m+1, m) @ &mem : res] -
Pr[MLWE1(LiftLWEAdv).main(dvector dnoise m,m+1, m) @ &mem : res]|)); 1: smt().
rewrite (pr_MLWE_LR &mem (LiftLWEAdv)); 1: apply (lift_guess_ll).
rewrite -{1}(RField.addr0 (2%r * _)) (RField.addrC (1%r / _)) -(RField.addrA) ler_add2l.
by rewrite ler_subr_addr RField.add0r -G2_LiftLWEadv0_equiv G2_half.
qed.

end section Security.
