(*This file is meant to accompany the main report. To run it, one must have installed the Coq-HoTT library beforehand, linked in the report.*)



From HoTT Require Import Basics.
From HoTT Require Import Types.
From HoTT Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.
From HoTT Require Import HSet.
From HoTT Require Import Colimits.Coeq.
From HoTT Require Import Truncations.Core Truncations.Connectedness.
From HoTT Require Import Circle.
From HoTT Require Import Spaces.Nat.Core.
From HoTT Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable Basics.Equivalences Basics.PathGroupoids Types.Paths Types.Universe.
From HoTT Require Basics.Numerals.Decimal.
From HoTT Require Import HIT.Interval.

(* We will use this definition of booleans. Although induction is more cumbersome (we have to perform it on the coproduct and on the unit types), it will be immediate to get zero_neq_one from inl_eq_inr.*)

Definition Bool := Unit + Unit.

Definition zero2 := inl Unit tt.

Definition one2 := inr Unit tt.

(*groupoid operations and coherence laws*)

Definition inv: 
forall {A : Type} {x y : A}, x = y -> y = x :=
fun A x => paths_ind x (fun  y p => y = x) (reflexivity x).

Definition conc: 
forall {A : Type} {x y z : A}, x = y -> y = z -> x = z.
Proof.
intros A x y z p q.
induction p.
induction q.
reflexivity.
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y): 
(reflexivity x) @ p = p.
Proof.
    induction p.
    reflexivity.
Defined.

Definition concat_p1 {A : Type} {x y : A} (p : x = y): 
 p @ (reflexivity y) = p.
Proof.
    induction p.
    reflexivity.
Defined.

Definition concat_assoc {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w):
(p @ q) @ r = p @ (q @ r).
Proof.
    induction p.
    induction q.
    induction r.
    reflexivity.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y):
 p^ @ p = reflexivity y.
Proof.
    induction p.
    reflexivity.
Defined.

Definition concat_pV {A : Type} {x y : A} (p : x = y):
 p @ p^ = reflexivity x.
Proof.
    induction p.
    reflexivity.
Defined.


Definition whiskerL' {A : Type} {x y z : A} (r : x = y) {p q : y = z}:
p = q -> r @ p = r @ q.
Proof.
    intro H.
    induction H.
    reflexivity.
Defined.


Definition whiskerR' {A : Type} {x y z : A} (r : y = z) {p q : x = y}:
p = q -> p @ r = q @ r.
Proof.
    intro H.
    induction H.
    reflexivity.
Defined.


(* functoriality of functions*)

Definition ap {A B : Type} (f : A -> B) {a b : A}: (a = b) -> ((f a) = (f b)).
Proof.
    intro p.
    induction p.
    reflexivity.
Defined.

Definition transport' {A : Type} {P : A -> Type} {a b : A} (p : a = b) : P a -> P b.
Proof.
    induction p.
    exact idmap.
Defined.

Definition apd {A : Type} {P : A -> Type} (f : forall (x : A), P x) {a b : A} (p : a = b): transport P p (f a) = (f b).
Proof.
    induction p.
    reflexivity.
Defined.

Definition transport_const' {A : Type} (B : Type) {a b : A}: forall (p : a = b) (x : B), transport (fun _ => B) p x = x.
Proof.
    induction p.
    reflexivity.
Defined.

Definition apd_const {A B : Type} (f : A -> B) {a b : A} :
forall (p : a = b), apd f p = transport_const' B p (f a) @ ap f p.
Proof.
    induction p.
    reflexivity.
Defined.

(* Naturality results *)

Definition concat_ap_hmt {A B : Type}  (f g : A -> B) (H : f == g) {a b : A} (p : a = b) :
ap f p @ H b = H a @ ap g p.
Proof.
    induction p.
    exact ((concat_1p (H a)) @ (concat_p1 (H a))^).
Defined.

Definition transport_arrow {X : Type} (A B : X -> Type) {x y : X}  
(p : x = y) (f : A x -> B x):
 p # f = (fun u => transport B p (f (transport A p^ u))).
Proof.
    induction p.
    reflexivity.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x y : A} (p : x = y):
forall (q : f x = g x), transport (fun z => f z = g z) p q = (ap f p)^ @ q @ (ap g p).
Proof.
    induction p.
    intro q.
    refine (_ @ (whiskerR (concat_1p q) (reflexivity (g x)))^).
    exact ((concat_p1 q)^).
Defined.

(*equality in function types*)

Definition happly' {A : Type} {B : A -> Type} (f g : forall (x : A), B x) :
f = g -> f == g.
Proof.
    intro p.
    induction p.
    exact (fun x => reflexivity (f x)).
Defined.


(*equality in universes*)

Definition equiv_path' (A B : Type):
A = B -> A <~> B.
Proof.
    intro p.
    refine (Build_Equiv A B (transport idmap p) _).
    refine (isequiv_adjointify (transport idmap p) (transport idmap p^) _ _).
    * induction p.
      reflexivity.
    * induction p.
      reflexivity.
Defined.


(* Encode decode for coproduct *)

Definition code
{A B : Type} (a0: A) :  A + B -> Type.
Proof.
  intro x.
  induction x as [a | b].
  * exact (a0 = a).
  * exact Empty.
Defined.

Definition encode {A B : Type} (a0 : A) (x : A + B): 
 (inl B a0) = x -> code a0 x.
Proof.
    intro p.
    exact (transport (code a0) p (reflexivity a0)).
Defined.

Definition decode {A B : Type} (a0 : A) (x : A + B) : 
code a0 x -> (inl B a0) = x.
Proof.
    induction x.
    * exact (ap (fun c => inl B c)).
    * contradiction.
Defined.

Definition encode_decode {A B : Type} (a0 : A) (x : A + B): 
(encode a0 x) o (decode a0 x) == idmap.
Proof.
    intro c.
    induction x.
    * induction c.
      reflexivity.
    * contradiction.
Defined.

Definition decode_encode {A B : Type} (a0 : A) (x : A + B):
(decode a0 x) o (encode a0 x) == idmap.
Proof.
    intro p.
    induction p.
    reflexivity.
Defined.

Definition inl_neq_inr {A B : Type} (a : A) (b : B) : 
inl a = inr b -> Empty := encode a (inr b).

Definition zero_neq_one : zero2 <> one2 := inl_neq_inr tt tt.

(*Consequences of univalence*)
  
Definition e0: Bool -> Bool.
Proof.
    intro b.
    induction b.
    * exact one2.
    * exact zero2.
Defined.

Definition e : Bool <~> Bool.
Proof.
    refine (Build_Equiv Bool Bool e0 _ ).
    refine (isequiv_adjointify e0 e0 _ _).
    * intro b.
    induction b.
    + induction a.
      reflexivity.
    + induction b.
      reflexivity.
    * intro b.
    induction b.
    + induction a.
      reflexivity.
    + induction b.
      reflexivity.
Defined.

Section Univalence.
Context `{Univalence}.

Definition p := path_universe e.


Definition p_neq_refl : (p = reflexivity Bool) -> Empty.
Proof.
    intro c.
    pose (r1 := ap (equiv_path Bool Bool) c).
    pose (transport_idmap_path_universe e)^.
    pose (r2 := (equiv_path_path_universe e)^ @ r1).
    pose (r3 := ap equiv_fun r2).
    pose (r4 := apD10 r3 (inr tt)).
    exact (zero_neq_one r4).
Defined.

Definition neg_is_prop {A : Type} (u v : ~ A) : u = v.
Proof.
    apply (path_arrow).
    intro f.
    contradiction.
Defined.

Definition nn := fun X => ~~X.

Definition f2_precomposed (f : forall (A : Type), (~~A) -> A) (u : ~~Bool) : f Bool u = e 
(f Bool (transport nn p^ u)).
Proof.
    pose (q := apd f p).
    pose (r := q^ @ transport_arrow nn idmap p (f Bool)).
    pose (s := happly (transport_idmap_path_universe e) (f Bool (transport nn p^ u))).
    exact (happly r u @ s).
Defined.


Definition contr_hmt (f : forall (A : Type), (~~A) -> A) : f Bool == e o f Bool.
Proof.
    intro u.
    refine (f2_precomposed f u @ _).
    refine (ap (e o (f Bool)) _).
    exact (neg_is_prop (transport nn p^ u) u).
Defined.


Definition no_fixed_points: forall (b : Bool), b <> e b.
Proof.
    induction b.
    * induction a.
      exact zero_neq_one.
    * induction b.
      exact (fun p => zero_neq_one p^).
Defined.

Definition no_double_neg: ~(forall (A : Type), (~~A) -> A).
Proof.
    intro f.
    refine (no_fixed_points (f Bool _) (contr_hmt f _)).
    exact (fun g => g zero2).
Defined.

End Univalence.

(*The interval*)


Check interval_ind.

Definition interval_rec' {C : Type} {a b : C} (s : (a = b)) : interval -> C.
Proof.
    refine (interval_ind (fun (x : interval) => C) a b _).
    exact ((transport_const seg a) @ s).
Defined.

Definition interval_rec_beta_seg {C : Type} {b0 b1 : C} (s : b0 = b1) : ap (interval_rec' s) seg = s.
Proof.
    pose (p := interval_ind_beta_seg (fun _ => C) b0 b1 (transport_const seg b0 @ s)).
    pose (q := apD_const (interval_rec' s) seg).
    exact (cancelL (transport_const seg b0) (ap (interval_rec' s) seg) s (q^ @ p)).
Defined.


Definition interval_is_contractible : {b : interval & forall (x : interval), b = x}.
Proof.
    refine (exist _ zero _).
    refine (interval_ind (fun x => zero = x) (reflexivity zero) seg _).
    refine (transport_paths_r seg (reflexivity zero) @ _).
    exact (concat_1p seg).
Defined.

(*The circle*)

Definition uniqueness_circle  {A : Type} (f g : Circle -> A) (p :f base = g base) 
(q :transport (fun (x : A) => x = x) p (ap f loop) = (ap g loop)) : 
forall (x : Circle), f x = g x. 
Proof.
    refine (Circle_ind (fun x => f x = g x) p _).
    rewrite (transport_paths_FlFr loop p).
    rewrite (whiskerL ((ap f loop)^ @ p) (q^ @ (transport_paths_lr p (ap f loop)))).
    rewrite (concat_p_pp ((ap f loop)^ @ p) (p^ @ ap f loop) p).
    rewrite (concat_pp_p (ap f loop)^  p (p^ @ ap f loop)).
    rewrite (whiskerL (ap f loop)^ (concat_p_Vp p(ap f loop))).
    exact (whiskerR (concat_Vp (ap f loop)) p @ (concat_1p p)).
Defined.

Definition univ_prop_circle `{Funext}(A : Type): 
  (Circle -> A) <~> {x : A & x = x}.
Proof.
    pose (f := fun (h : Circle -> A) => exist (fun x => x = x) (h base) (ap h loop)).
    pose (g := sig_ind (fun _ => Circle -> A) (Circle_rec A)).
    refine (Build_Equiv (Circle -> A) {x : A & x = x} f  (isequiv_adjointify f g _ _)).
    * intro y.
        induction y as (x,p).
        refine (path_sigma(fun x => x = x) _ _ (reflexivity x) _).
        exact (Circle_rec_beta_loop A x p).
    * intro h.
        apply path_arrow.
        refine (uniqueness_circle (g (f h)) h (reflexivity (h base)) _).
        exact (Circle_rec_beta_loop A (h base) (ap h loop)).
Defined.
      
  
Definition loop_eq_refl_implies_is_hset_Type : 
loop = reflexivity base -> forall (A : Type), IsTrunc 0 A.
Proof.
    intros G A.
    apply istrunc_S.
    intros x y.
    apply hprop_allpath.
    induction x0.
    intro l.
    exact((ap (ap (Circle_rec _ _ l)) G)^ @ (Circle_rec_beta_loop _ _ l)).
Defined.

Definition nontrivial_loops : forall (x : Circle), x = x.
Proof.
    refine (Circle_ind (fun (x : Circle) => x = x) loop _).
    exact (transport_paths_lr loop loop @ whiskerR (concat_Vp loop) loop @ concat_1p loop).
Defined.

Section Univalence.
Context `{Univalence}.

Check not_hset_Type.

Definition Lemma6_4_1 : ~(loop = reflexivity base) := 
fun c => (not_hset_Type (loop_eq_refl_implies_is_hset_Type c Type)).

Check apD10.

Definition Lemma6_4_2 : {f : forall (x : Circle), x = x & ~(f = fun x => reflexivity x)}.
Proof.
    refine (exist _ nontrivial_loops _).
    exact (fun p => Lemma6_4_1 (apD10 p base)).
Defined.
    


(*Universal property of the circle*)

From HoTT Require Import Spaces.Int.


Definition Lemma_6_10_12zero (P : Int -> Type) (d0 : P zero) (dp : forall (n : nat), P n -> P (int_succ n)) (dn : forall (n : nat), P (int_neg n) -> P (int_pred (int_neg n))) :
Int_ind P d0 dp dn (zero) = d0.
Proof.
    reflexivity.
Defined.

Definition Lemma_6_10_12pos (P : Int -> Type) (d0 : P zero) (dp : forall (n : nat), P n -> P (int_succ n)) (dn : forall (n : nat), P (int_neg n) -> P (int_pred (int_neg n))) : forall (n : nat),
Int_ind P d0 dp dn (int_succ n) = dp n (Int_ind P d0 dp dn n).
Proof.
  intro n.
  destruct n as [|n]; reflexivity.
Defined.

Definition Lemma_6_10_12neg (P : Int -> Type) (d0 : P zero) (dp : forall (n : nat), P n -> P (int_succ n)) (dn : forall (n : nat), P (int_neg n) -> P (int_pred (int_neg n))) : forall (n : nat),
Int_ind P d0 dp dn (int_pred (int_neg n)) = dn n (Int_ind P d0 dp dn (int_neg n)).
Proof.
  intro n.
  destruct n as [|n]; reflexivity.
Defined.

Definition eq_succ : Int <~> Int := 
(Build_Equiv Int Int int_succ isequiv_int_succ).

Definition code' : Circle -> Type := 
(Circle_rec Type Int (path_universe eq_succ)).

Definition transport_postcompose {A B : Type} (P : B -> Type) (f : A -> B)  {x y : A} (p : x = y) : 
transport (P o f) p == transport P (ap f p).
Proof.
    induction p.
    reflexivity.
Defined.

Definition transport_eq {A : Type} (P : A -> Type) {x y : A} {p q : x = y} :
p = q -> transport P p == transport P q.
Proof.
    intro G.
    exact (happly (ap (transport P) G)).
Defined.

Definition trans_code_loop : transport code' loop == int_succ.
Proof.
    intro x.
    refine ((transport_postcompose idmap code' loop x) @ _).
    pose (r := Circle_rec_beta_loop Type Int (path_universe eq_succ)).
    refine (((happly (ap (transport idmap) r))) x @ _).
    exact (happly (transport_idmap_path_universe eq_succ) x).
Defined.

Definition trans_code_loop_inv : transport code' loop^ == int_pred.
Proof.
    intro x.
    pose (H0 := (trans_code_loop  (transport code' loop^ x))^).
    pose (H1 := ap int_pred H0).
    refine ((int_succ_pred (transport code' loop^ x))^ @ H1 @ _).
    exact (ap int_pred (transport_pV code' loop x)).
Defined.


Definition encode' : forall {x : Circle}, (base = x) -> code' x := 
fun x p => transport code' p zero.

Definition decode_base := Int_ind (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^).

Definition decode_base_succ : forall (k : Int), decode_base k.+1%int = decode_base k @ loop.
Proof.
    induction k.
    * reflexivity.
    * rewrite (int_nat_succ n).
      unfold decode_base.
      exact (Lemma_6_10_12pos (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) n.+1).
    * rewrite (int_pred_succ (int_neg n)).
      unfold decode_base.
      rewrite ((Lemma_6_10_12neg (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) n)).
      exact ((concat_pV_p (decode_base (int_neg n)) loop)^).
Defined.


Definition decode_base_pred : forall (k : Int), decode_base k.-1%int = decode_base k @ loop^.
Proof.
    induction k.
    * reflexivity.
    * rewrite (int_succ_pred n).
      unfold decode_base.
      rewrite(Lemma_6_10_12pos (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) n).
      exact ((concat_pp_V (decode_base n) loop)^).
    * unfold decode_base.
      rewrite (Lemma_6_10_12neg (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) n).
      rewrite ((int_neg_succ n)^).
      rewrite (int_nat_succ n).
      rewrite (Lemma_6_10_12neg (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) (n.+1)).
      rewrite ((int_nat_succ n)^).
      rewrite ((int_neg_succ n)).
      rewrite (Lemma_6_10_12neg (fun _ => base = base) (reflexivity base) (fun n l => l @ loop) (fun n l => l @ loop^) (n)).
      reflexivity.
Defined.


Definition decode' : forall {x : Circle}, code' x -> base = x.
Proof.
    refine (Circle_ind (fun x => code' x -> base = x) decode_base _).
    refine (transport_arrow code' (fun x => base = x) loop(decode_base)  @ _).
    apply path_arrow.
    intro k.
    refine (transport_paths_r loop (decode_base (transport code' loop^ k)) @ _).
    rewrite (trans_code_loop_inv k).
    refine (cancelR ((decode_base) k.-1%int @ loop) ((decode_base) k) loop^ _).
    refine (concat_pp_V ((decode_base) k.-1%int) loop @ _).
    exact (decode_base_pred k).
Defined.


Definition decode_encode' (x : Circle) : forall (p : base = x), (decode' (encode' p)) = p.
Proof.
    intro p.
    induction p.
    reflexivity.
Defined.

Definition encode_decode_base : forall k : code' base, encode' (decode' k) = k.
Proof.
    intro k.
    unfold encode'.
    induction k.
    *   reflexivity.
    *   refine (ap encode' (decode_base_succ n) @ _).
        refine (transport_pp code' (decode_base n) loop zero @ _).
        refine (trans_code_loop (transport code' (decode_base n) zero) @ _).
        exact (ap int_succ IHk).
    *   refine (ap encode' (decode_base_pred (int_neg n)) @ _).
        refine (transport_pp code' (decode_base (int_neg n)) loop^ zero @ _).
        refine (trans_code_loop_inv (transport code' (decode_base (int_neg n)) zero) @ _).
        exact (ap int_pred IHk).
Defined.

Definition encode_decode' : forall (x : Circle) (k : code' x), (encode' (decode' k)) = k.
Proof.
    refine (Circle_ind (fun x => (forall (k : code' x), (encode' (decode' k)) = k)) encode_decode_base _ ).
    apply path_ishprop.
Defined.

Definition circle_paths (x : Circle): base = x <~> code' x.
Proof.
    refine (Build_Equiv (base = x) (code' x) encode' _).
    exact (isequiv_adjointify encode' decode' (encode_decode' x) (decode_encode' x)).
Defined.

Definition loop_space_circle: (base = base) <~> Int := circle_paths base.

End Univalence.
