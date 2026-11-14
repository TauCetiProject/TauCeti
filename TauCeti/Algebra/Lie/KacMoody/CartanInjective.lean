/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic
import TauCeti.Algebra.Lie.Basic

/-!
# Cartan injectivity for the Kac–Moody algebra of a realization

For a generalized Cartan matrix `A` and a realization `R` of `A` on `H` over any field `K`, this
file proves that the canonical linear map `TauCeti.KacMoody.cartanElement R` from `H` into the
Kac–Moody algebra `TauCeti.KacMoody.PresentedLieAlgebra R`, presented by the Chevalley and Serre
relations, is injective. In particular the simple coroots and the generators `eᵢ`, `fᵢ` are
nonzero there. No symmetrizability, invertibility of `A` or characteristic hypothesis is needed.

The proof follows Kac. Fix a functional `μ` on `H`. On the tensor algebra `T(V)` of a vector space
with basis `(vᵢ)`, modelled as `List I →₀ K`, let `fⱼ` act by left multiplication by `vⱼ`, let
`x ∈ H` act on `vⱼ₁ ⊗ ⋯ ⊗ vⱼₙ` by the scalar `μ x - Σₖ αⱼₖ x`, and define `eᵢ` recursively by
`eᵢ 1 = 0` and `eᵢ (vⱼ ⊗ w) = vⱼ ⊗ eᵢ w + δᵢⱼ hᵢ w`. These operators satisfy the Chevalley
relations: they define a representation of Kac's auxiliary Lie algebra $\tilde{\mathfrak g}(A)$
[Kac, proof of Theorem 1.2]. For a generalized Cartan matrix, each `fₖ` commutes with the raising
Serre relator `(ad eᵢ) ^ (1 - Aᵢⱼ) eⱼ` and each `eₖ` with the lowering one
(`TauCeti.KacMoody.SatisfiesChevalleyRelations.lie_negative_ad_pow_lie_positive_positive`, the
`sl₂`-computation of [Kac, §3.3]). Hence the raising relators vanish on `T(V)`, which is generated
from `1` by the `fⱼ`, and the subspace generated from the images of the lowering relators by the
`fⱼ` is stable under every operator and does not contain `1`. On the quotient all defining relations
hold, so the universal property gives a representation of the Kac–Moody algebra in which `x ∈ H`
acts on the class of `1`, which is nonzero, by `μ x`. If `x` maps to zero, then `μ x = 0` for
every `μ`, so `x = 0`.

## Main results

* `TauCeti.KacMoody.SatisfiesChevalleyRelations.swap`: the Chevalley relations, the relations of
  $\tilde{\mathfrak g}(A)$, are symmetric under exchanging the raising and lowering families.
* `TauCeti.KacMoody.SatisfiesChevalleyRelations.lie_negative_ad_pow_lie_positive_positive` and
  `TauCeti.KacMoody.SatisfiesChevalleyRelations.lie_positive_ad_pow_lie_negative_negative`: for a
  generalized Cartan matrix, Serre's relators commute with the opposite generators modulo the
  Chevalley relations.
* `TauCeti.KacMoody.cartanElement_injective`: Cartan injectivity.
* `TauCeti.KacMoody.positiveGenerator_ne_zero` and `TauCeti.KacMoody.negativeGenerator_ne_zero`:
  the generators `eᵢ` and `fᵢ` are nonzero.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press,
  1990: the proof of Theorem 1.2 (the representation of $\tilde{\mathfrak g}(A)$ on `T(V)`) and
  §3.3 (Serre's relators commute with the opposite generators).
-/

public section

open LieAlgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
variable {L : Type*} [LieRing L] [LieAlgebra K L]

variable {R} {φ : H →ₗ[K] L} {E F : I → L}

namespace SatisfiesChevalleyRelations

/-- The Chevalley relations are symmetric under exchanging the raising and lowering families and
negating the Cartan map. -/
theorem swap (h : SatisfiesChevalleyRelations R φ E F) :
    SatisfiesChevalleyRelations R (-φ) F E where
  lie_cartan_cartan x y := by simp [h.lie_cartan_cartan]
  lie_cartan_positive x j := by simp [h.lie_cartan_negative]
  lie_cartan_negative x j := by simp [h.lie_cartan_positive]
  lie_positive_negative_self i := by
    rw [← lie_skew, h.lie_positive_negative_self, LinearMap.neg_apply]
  lie_positive_negative_of_ne i j hij := by
    rw [← lie_skew, h.lie_positive_negative_of_ne j i hij.symm, neg_zero]

variable (h : SatisfiesChevalleyRelations R φ E F)
include h

/-- The element `(ad Eᵢ) ^ n Eⱼ` has weight `αⱼ + n αᵢ`. -/
theorem lie_cartan_ad_pow_positive (x : H) (i j : I) (n : ℕ) :
    ⁅φ x, (ad K L (E i) ^ n) (E j)⁆ = (R.root j x + n * R.root i x) • (ad K L (E i) ^ n) (E j) := by
  induction n with
  | zero => simp [h.lie_cartan_positive]
  | succ n ih =>
    rw [ad_pow_succ_apply', leibniz_lie, h.lie_cartan_positive, ih,
      smul_lie, lie_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- The element `(ad Fᵢ) ^ n Fⱼ` has weight `-(αⱼ + n αᵢ)`. -/
theorem lie_cartan_ad_pow_negative (x : H) (i j : I) (n : ℕ) :
    ⁅φ x, (ad K L (F i) ^ n) (F j)⁆ =
      -((R.root j x + n * R.root i x) • (ad K L (F i) ^ n) (F j)) := by
  have hw := h.swap.lie_cartan_ad_pow_positive x i j n
  rwa [LinearMap.neg_apply, neg_lie, neg_eq_iff_eq_neg] at hw

/-- For `k ≠ i`, the lowering generator `F k` commutes with `ad (E i)`. -/
theorem lie_negative_ad_pow_of_ne {i k : I} (hki : k ≠ i) (y : L) (n : ℕ) :
    ⁅F k, (ad K L (E i) ^ n) y⁆ = (ad K L (E i) ^ n) ⁅F k, y⁆ := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [ad_pow_succ_apply', leibniz_lie, ← lie_skew (F k),
      h.lie_positive_negative_of_ne i k hki.symm, neg_zero, zero_lie, zero_add, ih,
      ad_pow_succ_apply']

/-- The `sl₂`-computation behind Serre's relations: for `i ≠ j` and `Aᵢᵢ = 2`, the element `Eⱼ` is
killed by `Fᵢ`, so lowering `(ad Eᵢ) ^ (n + 1) Eⱼ` by `Fᵢ` gives
`-(n + 1) (Aᵢⱼ + n) (ad Eᵢ) ^ n Eⱼ`. -/
theorem lie_negative_ad_pow_succ_self {i j : I} (hij : i ≠ j) (hii : A i i = 2) (n : ℕ) :
    ⁅F i, (ad K L (E i) ^ (n + 1)) (E j)⁆ =
      -(((n + 1 : ℕ) : K) * (A i j + n)) • (ad K L (E i) ^ n) (E j) := by
  -- Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f` would need `φ hᵢ ≠ 0`,
  -- which arbitrary data need not satisfy, so the computation is done by hand.
  have hFE : ⁅F i, E i⁆ = -φ (R.coroot i) := by
    rw [← lie_skew, h.lie_positive_negative_self]
  induction n with
  | zero =>
    rw [zero_add, pow_one, ad_apply, leibniz_lie, hFE, ← lie_skew (F i),
      h.lie_positive_negative_of_ne j i hij.symm]
    simp [neg_lie, h.lie_cartan_positive]
  | succ n ih =>
    rw [ad_pow_succ_apply' _ _ (n + 1), leibniz_lie, hFE, neg_lie,
      h.lie_cartan_ad_pow_positive, ih, lie_smul, ← ad_pow_succ_apply', ← neg_smul, ← add_smul]
    congr 1
    simp only [CartanRealization.root_coroot, Matrix.map_apply, hii]
    push_cast
    ring

/-- **Serre's relators on the raising family are lowest weight vectors.** If `Aᵢᵢ = 2`, `Aᵢⱼ ≤ 0`
for `i ≠ j` and `Aⱼᵢ = 0` whenever `Aᵢⱼ = 0`, as for a generalized Cartan matrix, every lowering
generator `F k` commutes with the relator `(ad Eᵢ) ^ (-Aᵢⱼ) ⁅Eᵢ, Eⱼ⁆` modulo the Chevalley
relations. -/
theorem lie_negative_ad_pow_lie_positive_positive {i j : I} (hii : A i i = 2)
    (hij : i ≠ j → A i j ≤ 0) (hji : A i j = 0 → A j i = 0) (k : I) :
    ⁅F k, (ad K L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆⁆ = 0 := by
  rcases eq_or_ne i j with rfl | hne
  · simp
  have hm : ((-A i j).toNat : ℤ) = -A i j := Int.toNat_of_nonneg (by linarith [hij hne])
  rw [← ad_pow_succ_apply]
  rcases eq_or_ne k i with rfl | hki
  · rw [h.lie_negative_ad_pow_succ_self hne hii]
    have hAz : A k j + ((-A k j).toNat : ℤ) = 0 := by omega
    have hA : (A k j : K) + ((-A k j).toNat : K) = 0 := by
      rw [← Int.cast_natCast, ← Int.cast_add, hAz, Int.cast_zero]
    rw [hA, mul_zero, neg_zero, zero_smul]
  rw [h.lie_negative_ad_pow_of_ne hki]
  rcases eq_or_ne k j with rfl | hkj
  · rw [← lie_skew, h.lie_positive_negative_self, map_neg, ad_pow_succ_apply, ← lie_skew,
      h.lie_cartan_positive, map_neg, neg_neg, map_smul]
    rcases hn : (-A i k).toNat with _ | n
    · rw [CartanRealization.root_coroot, Matrix.map_apply, hji (by omega), Int.cast_zero,
        zero_smul]
    · rw [ad_pow_succ_apply, lie_self, map_zero, smul_zero]
  · rw [← lie_skew, h.lie_positive_negative_of_ne j k hkj.symm, neg_zero, map_zero]

/-- **Serre's relators on the lowering family are highest weight vectors.** Under the hypotheses of
`TauCeti.KacMoody.SatisfiesChevalleyRelations.lie_negative_ad_pow_lie_positive_positive`, every
raising generator `E k` commutes with the relator `(ad Fᵢ) ^ (-Aᵢⱼ) ⁅Fᵢ, Fⱼ⁆` modulo the Chevalley
relations. -/
theorem lie_positive_ad_pow_lie_negative_negative {i j : I} (hii : A i i = 2)
    (hij : i ≠ j → A i j ≤ 0) (hji : A i j = 0 → A j i = 0) (k : I) :
    ⁅E k, (ad K L (F i) ^ (-A i j).toNat) ⁅F i, F j⁆⁆ = 0 :=
  h.swap.lie_negative_ad_pow_lie_positive_positive hii hij hji k

end SatisfiesChevalleyRelations

/-! ## Kac's representation on the tensor algebra

The space `List I →₀ K` is the tensor algebra on a vector space with basis indexed by `I`, the
word `j₁ ⋯ jₙ` standing for `vⱼ₁ ⊗ ⋯ ⊗ vⱼₙ`. For a functional `μ` on `H`, Kac lets `fⱼ` act by
prepending `j`, the element `x ∈ H` act on a word `w` by the scalar `μ x - Σ_{j ∈ w} αⱼ x`, and
`eᵢ` act by `eᵢ ∅ = 0`, `eᵢ (j w) = j (eᵢ w) + δᵢⱼ hᵢ w`. -/

section Tensor

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K) in
/-- The lowering operator: prepending the letter `j`. -/
private noncomputable def lowerOp (j : I) : Module.End K (List I →₀ K) :=
  Finsupp.lmapDomain K K (List.cons j)

private theorem lowerOp_single (j : I) (w : List I) (a : K) :
    lowerOp K j (Finsupp.single w a) = Finsupp.single (j :: w) a := by
  simp [lowerOp]

variable (R) (μ : Module.Dual K H)

/-- The weight `μ - Σ_{j ∈ w} αⱼ` of a word `w`. -/
private def wordWeight (w : List I) : Module.Dual K H := μ - (w.map R.root).sum

private theorem wordWeight_cons (j : I) (w : List I) :
    wordWeight R μ (j :: w) = wordWeight R μ w - R.root j := by
  simp only [wordWeight, List.map_cons, List.sum_cons]
  abel

/-- The Cartan operators, acting diagonally on words by their weights. -/
private noncomputable def cartanOp : H →ₗ[K] Module.End K (List I →₀ K) where
  toFun x := Finsupp.lsum K fun w => wordWeight R μ w x • Finsupp.lsingle w
  map_add' x y := Finsupp.lhom_ext fun w a => by simp [add_smul]
  map_smul' c x := Finsupp.lhom_ext fun w a => by simp [mul_assoc]

private theorem cartanOp_single (x : H) (w : List I) (a : K) :
    cartanOp R μ x (Finsupp.single w a) = wordWeight R μ w x • Finsupp.single w a := by
  simp [cartanOp]

private theorem cartanOp_lowerOp (x : H) (j : I) (v : List I →₀ K) :
    cartanOp R μ x (lowerOp K j v) =
      lowerOp K j (cartanOp R μ x v) - R.root j x • lowerOp K j v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, hv, hv', smul_add]
    abel
  | single w a => simp [lowerOp_single, cartanOp_single, wordWeight_cons, sub_smul]

/-- The empty word, the highest weight vector of the representation. -/
private noncomputable abbrev vacuum : List I →₀ K := Finsupp.single [] 1

private theorem cartanOp_vacuum (x : H) : cartanOp R μ x vacuum = μ x • vacuum := by
  simp [cartanOp_single, wordWeight]

/-- Every word in the image of a lowering operator is nonempty. -/
private theorem lowerOp_apply_nil (k : I) (v : List I →₀ K) : lowerOp K k v [] = 0 :=
  Finsupp.mapDomain_of_notMem_range v [] (by simp)

variable (K A) in
/-- The lowering Serre operator `(ad fᵢ) ^ (-Aᵢⱼ) ⁅fᵢ, fⱼ⁆`. -/
private noncomputable def serreOp (i j : I) : Module.End K (List I →₀ K) :=
  (ad K _ (lowerOp K i) ^ (-A i j).toNat) ⁅lowerOp K i, lowerOp K j⁆

private theorem serreOp_apply_nil (i j : I) (v : List I →₀ K) : serreOp K A i j v [] = 0 := by
  suffices ∀ (n : ℕ) (Y : Module.End K (List I →₀ K)), (∀ v, Y v [] = 0) →
      ∀ v, (ad K _ (lowerOp K i) ^ n) Y v [] = 0 from
    this _ _ (fun v => by simp [lowerOp_apply_nil]) v
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro Y hY v
    rw [ad_pow_succ_apply', Module.End.lie_apply_apply, Finsupp.sub_apply,
      lowerOp_apply_nil, ih Y hY, sub_zero]

variable (K A) in
/-- The smallest subspace containing the images of the lowering Serre operators and stable under
the lowering operators: the two-sided ideal of the tensor algebra generated by the Serre
elements. -/
private noncomputable def serreSubmodule : Submodule K (List I →₀ K) :=
  sInf {N | (∀ i j, LinearMap.range (serreOp K A i j) ≤ N) ∧ ∀ k, N ≤ N.comap (lowerOp K k)}

private theorem serreOp_mem (i j : I) (v : List I →₀ K) :
    serreOp K A i j v ∈ serreSubmodule K A :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 i j ⟨v, rfl⟩

private theorem lowerOp_mem {v : List I →₀ K} (hv : v ∈ serreSubmodule K A) (k : I) :
    lowerOp K k v ∈ serreSubmodule K A :=
  Submodule.mem_sInf.2 fun N hN => hN.2 k (Submodule.mem_sInf.1 hv N hN)

private theorem serreSubmodule_le {N : Submodule K (List I →₀ K)}
    (h₁ : ∀ i j v, serreOp K A i j v ∈ N) (h₂ : ∀ k v, v ∈ N → lowerOp K k v ∈ N) :
    serreSubmodule K A ≤ N :=
  sInf_le ⟨fun i j => by rintro _ ⟨v, rfl⟩; exact h₁ i j v, fun k v hv => h₂ k v hv⟩

/-- The empty word does not lie in the Serre submodule. -/
private theorem vacuum_notMem_serreSubmodule : (vacuum : List I →₀ K) ∉ serreSubmodule K A := by
  intro h
  have := serreSubmodule_le (N := LinearMap.ker (Finsupp.lapply [])) (A := A)
    (fun i j v => serreOp_apply_nil i j v) (fun k v _ => lowerOp_apply_nil k v) h
  simp at this

/-- The class of the empty word in the quotient is nonzero. -/
private theorem mk_vacuum_ne_zero :
    Submodule.Quotient.mk (p := serreSubmodule K A) (vacuum : List I →₀ K) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact vacuum_notMem_serreSubmodule

variable [DecidableEq I]

/-- The image of a word under the raising operator `eᵢ`. -/
private noncomputable def raiseVec (i : I) : List I → (List I →₀ K)
  | [] => 0
  | j :: w => lowerOp K j (raiseVec i w) +
      if j = i then Finsupp.single w (wordWeight R μ w (R.coroot i)) else 0

/-- The raising operator `eᵢ`. -/
private noncomputable def raiseOp (i : I) : Module.End K (List I →₀ K) :=
  Finsupp.linearCombination K (raiseVec R μ i)

private theorem raiseOp_single (i : I) (w : List I) (a : K) :
    raiseOp R μ i (Finsupp.single w a) = a • raiseVec R μ i w :=
  Finsupp.linearCombination_single K a w

/-- Each `eᵢ w` is a weight vector, of weight `αᵢ` plus the weight of `w`. -/
private theorem cartanOp_raiseVec (x : H) (i : I) (w : List I) :
    cartanOp R μ x (raiseVec R μ i w) = (wordWeight R μ w x + R.root i x) • raiseVec R μ i w := by
  induction w with
  | nil => simp [raiseVec]
  | cons j w ih =>
    simp only [raiseVec]
    rw [map_add, cartanOp_lowerOp, ih, map_smul]
    split_ifs with hji
    · subst hji
      simp only [cartanOp_single, wordWeight_cons, LinearMap.sub_apply, smul_add]
      module
    · simp only [wordWeight_cons, LinearMap.sub_apply, map_zero, add_zero]
      module

private theorem satisfiesChevalleyRelations_tensor :
    SatisfiesChevalleyRelations R (cartanOp R μ) (raiseOp R μ) (lowerOp K) where
  lie_cartan_cartan x y := Finsupp.lhom_ext fun w a => by
    simp [cartanOp_single, mul_left_comm]
  lie_cartan_positive x j := Finsupp.lhom_ext fun w a => by
    simp only [Module.End.lie_apply_apply, raiseOp_single, cartanOp_single, map_smul,
      cartanOp_raiseVec, LinearMap.smul_apply]
    module
  lie_cartan_negative x j := Finsupp.lhom_ext fun w a => by
    simp [cartanOp_lowerOp]
  lie_positive_negative_self i := Finsupp.lhom_ext fun w a => by
    simp [lowerOp_single, raiseOp_single, raiseVec, cartanOp_single,
      Finsupp.smul_single, mul_comm]
  lie_positive_negative_of_ne i j hij := Finsupp.lhom_ext fun w a => by
    simp [lowerOp_single, raiseOp_single, raiseVec, hij.symm]

private theorem raiseOp_vacuum (i : I) : raiseOp R μ i vacuum = 0 := by
  simp [raiseOp_single, raiseVec]

variable {R μ}
variable (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
  (hzero : ∀ i j, A i j = 0 → A j i = 0)
include hdiag hoff hzero

/-- The raising Serre operators vanish on the tensor algebra: they kill the empty word and
commute with the lowering operators, which generate every word from it. -/
private theorem raiseOp_serre_eq_zero (i j : I) :
    (ad K _ (raiseOp R μ i) ^ (-A i j).toNat) ⁅raiseOp R μ i, raiseOp R μ j⁆ = 0 := by
  have h := satisfiesChevalleyRelations_tensor R μ
  have hc := fun k => h.lie_negative_ad_pow_lie_positive_positive (hdiag i)
    (hoff i j) (hzero i j) k
  set X := (ad K _ (raiseOp R μ i) ^ (-A i j).toNat) ⁅raiseOp R μ i, raiseOp R μ j⁆
  have hvac : ∀ n, (ad K _ (raiseOp R μ i) ^ n) (raiseOp R μ j) vacuum = 0 := by
    intro n
    induction n with
    | zero => simp [raiseOp_vacuum]
    | succ n ih =>
      rw [ad_pow_succ_apply', Module.End.lie_apply_apply, ih, raiseOp_vacuum,
        map_zero, map_zero, sub_zero]
  have hX : X vacuum = 0 := by
    simp only [X]
    rw [← ad_pow_succ_apply]
    exact hvac _
  refine Finsupp.lhom_ext fun w a => ?_
  rw [LinearMap.zero_apply]
  induction w with
  | nil =>
    have hsingle : Finsupp.single [] a = a • (vacuum : List I →₀ K) := by simp
    rw [hsingle, map_smul, hX, smul_zero]
  | cons k w ih =>
    rw [← lowerOp_single, Module.End.apply_apply_eq_apply_apply_add_lie, ← lie_skew, hc, neg_zero,
      LinearMap.zero_apply, add_zero, ih, map_zero]

/-- The Serre submodule is stable under the raising and the Cartan operators. -/
private theorem raiseOp_mem_and_cartanOp_mem {v : List I →₀ K} (hv : v ∈ serreSubmodule K A) :
    (∀ k, raiseOp R μ k v ∈ serreSubmodule K A) ∧ ∀ x, cartanOp R μ x v ∈ serreSubmodule K A := by
  have h := satisfiesChevalleyRelations_tensor R μ
  set N := serreSubmodule K A
  let N' : Submodule K (List I →₀ K) :=
    N ⊓ (⨅ k, N.comap (raiseOp R μ k)) ⊓ ⨅ x, N.comap (cartanOp R μ x)
  have hN' : ∀ v, v ∈ N' ↔ v ∈ N ∧ (∀ k, raiseOp R μ k v ∈ N) ∧ ∀ x, cartanOp R μ x v ∈ N := by
    simp [N', and_assoc]
  suffices N ≤ N' from ((hN' v).1 (this hv)).2
  refine serreSubmodule_le (fun i j t => (hN' _).2 ⟨serreOp_mem i j t, fun k => ?_, fun x => ?_⟩)
    fun k t ht => ?_
  · rw [Module.End.apply_apply_eq_apply_apply_add_lie, serreOp,
      h.lie_positive_ad_pow_lie_negative_negative (hdiag i) (hoff i j) (hzero i j) k,
      LinearMap.zero_apply, add_zero]
    exact serreOp_mem i j _
  · have hw : ⁅cartanOp R μ x, serreOp K A i j⁆ =
        -((R.root j x + ((-A i j).toNat + 1 : ℕ) * R.root i x) • serreOp K A i j) := by
      rw [serreOp, ← ad_pow_succ_apply, h.lie_cartan_ad_pow_negative]
    rw [Module.End.apply_apply_eq_apply_apply_add_lie, hw, LinearMap.neg_apply,
      LinearMap.smul_apply]
    exact add_mem (serreOp_mem i j _) (neg_mem (Submodule.smul_mem _ _ (serreOp_mem i j t)))
  · obtain ⟨htN, hraise, hcartan⟩ := (hN' t).1 ht
    refine (hN' _).2 ⟨lowerOp_mem htN k, fun l => ?_, fun x => ?_⟩
    · rw [Module.End.apply_apply_eq_apply_apply_add_lie]
      refine add_mem (lowerOp_mem (hraise l) k) ?_
      rcases eq_or_ne l k with rfl | hlk
      · rw [h.lie_positive_negative_self]
        exact hcartan _
      · rw [h.lie_positive_negative_of_ne l k hlk, LinearMap.zero_apply]
        exact zero_mem _
    · rw [cartanOp_lowerOp]
      exact sub_mem (lowerOp_mem (hcartan x) k) (Submodule.smul_mem _ _ (lowerOp_mem htN k))

omit [DecidableEq I] in
/-- **Kac's argument for Cartan injectivity.** For every functional `μ`, the quotient of the tensor
algebra by the Serre submodule is a representation of the Kac–Moody algebra in which `x ∈ H`
acts on the class of the empty word by `μ x`. -/
private theorem apply_eq_zero_of_cartanElement_eq_zero {x : H} (hx : cartanElement R x = 0) :
    μ x = 0 := by
  classical
  -- The operators preserve the Serre submodule, so they lie in its stabilizer, where they still
  -- satisfy the Chevalley relations.
  have hT := satisfiesChevalleyRelations_tensor R μ
  set N := serreSubmodule K A
  have hstab := fun v (hv : v ∈ N) =>
    raiseOp_mem_and_cartanOp_mem (R := R) (μ := μ) hdiag hoff hzero hv
  let φS : H →ₗ[K] N.lieStabilizer :=
    { toFun y := ⟨cartanOp R μ y, N.mem_lieStabilizer.2 fun v hv => (hstab v hv).2 y⟩
      map_add' y z := Subtype.ext (map_add _ y z)
      map_smul' c y := Subtype.ext (map_smul _ c y) }
  let ES : I → N.lieStabilizer := fun i =>
    ⟨raiseOp R μ i, N.mem_lieStabilizer.2 fun v hv => (hstab v hv).1 i⟩
  let FS : I → N.lieStabilizer := fun i =>
    ⟨lowerOp K i, N.mem_lieStabilizer.2 fun v hv => lowerOp_mem hv i⟩
  have hS : SatisfiesChevalleyRelations R φS ES FS :=
    ⟨fun y z => Subtype.ext (hT.lie_cartan_cartan y z),
      fun y j => Subtype.ext (hT.lie_cartan_positive y j),
      fun y j => Subtype.ext (hT.lie_cartan_negative y j),
      fun i => Subtype.ext (hT.lie_positive_negative_self i),
      fun i j hij => Subtype.ext (hT.lie_positive_negative_of_ne i j hij)⟩
  -- The raising Serre relators vanish already in the stabilizer.
  have hpos : ∀ i j, (ad K _ (ES i) ^ (-A i j).toNat) ⁅ES i, ES j⁆ = 0 := fun i j =>
    Subtype.ext <| by
      simp only [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket, ES, ZeroMemClass.coe_zero]
      exact raiseOp_serre_eq_zero hdiag hoff hzero i j
  -- The lowering Serre relators map the tensor algebra into the Serre submodule, so they act by
  -- zero on the quotient.
  have hneg : ∀ i j,
      N.lieStabilizerQuotientAction ((ad K _ (FS i) ^ (-A i j).toNat) ⁅FS i, FS j⁆) = 0 :=
    fun i j => by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.lieStabilizerQuotientAction_mk, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero]
    simp only [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket, FS]
    exact serreOp_mem i j v
  -- On the quotient every defining relation holds; evaluate the induced representation of the
  -- Kac–Moody algebra at the class of the empty word.
  have hrel := SatisfiesRelations.mk (hS.map N.lieStabilizerQuotientAction) (fun i j => ?_)
    (fun i j => ?_)
  · have h0 := congr(lift hrel $hx)
    rw [lift_cartanElement, map_zero] at h0
    have h1 := LinearMap.congr_fun h0 (Submodule.Quotient.mk vacuum)
    rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, Submodule.lieStabilizerQuotientAction_mk,
      LinearMap.zero_apply] at h1
    simp only [φS, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [cartanOp_vacuum, Submodule.Quotient.mk_smul] at h1
    exact (smul_eq_zero.1 h1).resolve_right mk_vacuum_ne_zero
  · have h := congr_arg N.lieStabilizerQuotientAction (hpos i j)
    rw [LieHom.map_ad_pow, LieHom.map_lie, map_zero] at h
    exact h
  · simpa only [Function.comp_apply, LieHom.map_ad_pow, LieHom.map_lie] using hneg i j

end Tensor

section Injective

variable (R) (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
  (hzero : ∀ i j, A i j = 0 → A j i = 0)
include hdiag hoff hzero

/-- **Cartan injectivity.** For a generalized Cartan matrix `A`, the canonical map from the
realization `H` into the Kac–Moody algebra presented on it is injective, over any field. -/
theorem cartanElement_injective : Function.Injective (cartanElement R) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  exact (Module.forall_dual_apply_eq_zero_iff K x).1 fun μ =>
    apply_eq_zero_of_cartanElement_eq_zero (μ := μ) hdiag hoff hzero hx

/-- For a generalized Cartan matrix, the simple coroot `hᵢ` is nonzero in the Kac–Moody
algebra. -/
theorem cartanElement_coroot_ne_zero (i : I) : cartanElement R (R.coroot i) ≠ 0 :=
  ((map_ne_zero_iff _ (cartanElement_injective R hdiag hoff hzero)).2
    (R.coroot_linearIndependent.ne_zero i))

/-- For a generalized Cartan matrix, the raising generator `eᵢ` is nonzero. -/
theorem positiveGenerator_ne_zero (i : I) : positiveGenerator R i ≠ 0 := fun h =>
  cartanElement_coroot_ne_zero R hdiag hoff hzero i <| by
    rw [← lie_positiveGenerator_negativeGenerator_self, h, zero_lie]

/-- For a generalized Cartan matrix, the lowering generator `fᵢ` is nonzero. -/
theorem negativeGenerator_ne_zero (i : I) : negativeGenerator R i ≠ 0 := fun h =>
  cartanElement_coroot_ne_zero R hdiag hoff hzero i <| by
    rw [← lie_positiveGenerator_negativeGenerator_self, h, lie_zero]

end Injective

end KacMoody

end TauCeti
