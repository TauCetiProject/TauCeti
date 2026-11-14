/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.RegularSequence
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Triangular polynomial substitutions and variable elimination

Let `f : σ → MvPolynomial σ R` be a family of polynomials over a commutative ring `R`, and let
`prec` be a relation on the index type `σ`. The family `f` is **triangular** for `prec`
(`MvPolynomial.IsTriangular`) if each `f i` has the form `uᵢ Xᵢ + gᵢ` where `uᵢ` is a unit of `R`
and every variable occurring in `gᵢ` precedes `i` under `prec`.

When `prec` is well-founded, back-substitution along `prec` inverts `aeval f`: solving
`f i = uᵢ Xᵢ + gᵢ` recursively for `Xᵢ` produces an `R`-algebra automorphism
`MvPolynomial.IsTriangular.algEquiv` of `MvPolynomial σ R` sending `Xᵢ` to `f i`. Consequently:

* the `f i` are algebraically independent and generate `MvPolynomial σ R` over `R`;
* for any subset `s : Set σ`, the quotient `MvPolynomial σ R ⧸ Ideal.span (f '' s)` is isomorphic
  as an `R`-algebra to the polynomial ring `MvPolynomial {i : σ // i ∉ s} R` in the remaining
  variables (`MvPolynomial.IsTriangular.quotientSpanImageEquiv`), so `Ideal.span (f '' s)` is prime
  over any nontrivial ring without zero divisors (`MvPolynomial.IsTriangular.isPrime_span_image`);
* any duplicate-free finite list of elements of `f` forms a regular sequence on `MvPolynomial σ R`
  when `R` is nontrivial (`MvPolynomial.IsTriangular.isRegular_map`).

In positively weighted polynomial rings (`w : σ → ℕ` with `0 < w i` for all `i`), every variable
occurring in a weighted homogeneous polynomial of weight `m` that lies in the square of the
augmentation ideal `idealOfVars σ R ^ 2` has weight strictly less than `m`
(`MvPolynomial.vars_weight_lt_of_isWeightedHomogeneous_of_mem_pow_idealOfVars`). Thus any family
`f i` congruent to `uᵢ Xᵢ` modulo `idealOfVars σ R ^ 2` and weighted homogeneous of weight `w i` is
automatically triangular for the well-founded weight order `w j < w i`
(`MvPolynomial.isTriangular_of_isWeightedHomogeneous_sub_mem_sq`). This is the mechanism by which
generators of a graded polynomial algebra, such as Landweber's `vⱼ` in `L ⧸ p L ≃ 𝔽ₚ[x₁, x₂, …]`,
replace polynomial variables of matching degree.

## Main definitions

* `MvPolynomial.IsTriangular`: triangularity of `f : σ → MvPolynomial σ R` with respect to `prec`.
* `MvPolynomial.IsTriangular.algEquiv`: the `R`-algebra automorphism `aeval f` of
  `MvPolynomial σ R` when `prec` is well-founded.
* `MvPolynomial.IsTriangular.quotientSpanImageEquiv`: the `R`-algebra isomorphism
  `(MvPolynomial σ R ⧸ Ideal.span (f '' s)) ≃ₐ[R] MvPolynomial {i : σ // i ∉ s} R`.

## Main results

* `MvPolynomial.IsTriangular.isPrime_span_image`: over a nontrivial ring without zero divisors,
  `Ideal.span (f '' s)` is prime.
* `MvPolynomial.IsTriangular.notMem_span_image`: for `i ∉ s` over a nontrivial ring,
  `f i ∉ Ideal.span (f '' s)`.
* `MvPolynomial.IsTriangular.isWeaklyRegular_map` and `MvPolynomial.IsTriangular.isRegular_map`:
  duplicate-free lists of `f i` form weakly regular (and, over nontrivial `R`, regular) sequences.
* `MvPolynomial.vars_weight_lt_of_isWeightedHomogeneous_of_mem_pow_idealOfVars` and
  `MvPolynomial.isTriangular_of_isWeightedHomogeneous_sub_mem_sq`: positive-weight decomposable
  perturbations of unit multiples of the variables are triangular.
-/

public section

namespace MvPolynomial

open Finsupp RingTheory.Sequence

section Triangular

variable {R σ : Type*} [CommRing R]

/-- A family of polynomials `f : σ → MvPolynomial σ R` is **triangular** with respect to a relation
`prec` on `σ` if each `f i` is a unit scalar multiple of `X i` plus a polynomial whose variables
all precede `i` under `prec`. -/
def IsTriangular (prec : σ → σ → Prop) (f : σ → MvPolynomial σ R) : Prop :=
  ∀ i, ∃ (u : Rˣ) (g : MvPolynomial σ R),
    (∀ j ∈ g.vars, prec j i) ∧ f i = C (u : R) * X i + g

/-- Unfolded characterization of `MvPolynomial.IsTriangular`. -/
theorem isTriangular_def {prec : σ → σ → Prop} {f : σ → MvPolynomial σ R} :
    IsTriangular prec f ↔
      ∀ i, ∃ (u : Rˣ) (g : MvPolynomial σ R),
        (∀ j ∈ g.vars, prec j i) ∧ f i = C (u : R) * X i + g :=
  Iff.rfl

/-- The variables themselves form a triangular family for every relation on `σ`. -/
theorem isTriangular_X (prec : σ → σ → Prop) :
    IsTriangular prec (X : σ → MvPolynomial σ R) :=
  fun i ↦ ⟨1, 0, by simp, by simp⟩

namespace IsTriangular

variable {prec prec' : σ → σ → Prop} {f : σ → MvPolynomial σ R}

/-- Weakening the precedence relation preserves triangularity. -/
theorem mono (h : ∀ ⦃j i⦄, prec j i → prec' j i) (hf : IsTriangular prec f) :
    IsTriangular prec' f := by
  intro i
  obtain ⟨u, g, hg, hfi⟩ := hf i
  exact ⟨u, g, fun j hj ↦ h (hg j hj), hfi⟩

/-- Mapping coefficients along a ring homomorphism preserves triangularity. -/
theorem map {S : Type*} [CommRing S] (φ : R →+* S) (hf : IsTriangular prec f) :
    IsTriangular prec (fun i ↦ MvPolynomial.map φ (f i)) := by
  intro i
  obtain ⟨u, g, hg, hfi⟩ := hf i
  exact ⟨Units.map φ.toMonoidHom u, MvPolynomial.map φ g,
    fun j hj ↦ hg j (vars_map g φ hj), by simp [hfi]⟩

/-- Recursive back-substitution inverting a triangular family along a well-founded relation. -/
private noncomputable def invFamily (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    σ → MvPolynomial σ R :=
  hprec.fix fun i ih ↦ by
    classical
    exact C (((hf i).choose⁻¹ : Rˣ) : R) *
      (X i - aeval (fun j ↦ if hj : prec j i then ih j hj else 0) (hf i).choose_spec.choose)

private theorem invFamily_eq (hprec : WellFounded prec) (hf : IsTriangular prec f) (i : σ) :
    hf.invFamily hprec i =
      C (((hf i).choose⁻¹ : Rˣ) : R) *
        (X i - aeval (hf.invFamily hprec) (hf i).choose_spec.choose) := by
  classical
  let g := (hf i).choose_spec.choose
  have hg : ∀ j ∈ g.vars, prec j i := (hf i).choose_spec.choose_spec.1
  rw [invFamily, hprec.fix_eq]
  congr 2
  rw [aeval_def, aeval_def]
  refine eval₂_congr _ _ _ fun {j} {d} hjd hcd ↦ ?_
  have hj : prec j i :=
    hg j ((mem_vars_iff_mem_support j).mpr ⟨d, mem_support_iff.mpr hcd, hjd⟩)
  simp [hj]

private theorem aeval_invFamily_apply (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (i : σ) : aeval (hf.invFamily hprec) (f i) = X i := by
  have hfi := (hf i).choose_spec.choose_spec.2
  rw [hfi, map_add, map_mul, aeval_C, algebraMap_eq, aeval_X, hf.invFamily_eq hprec i,
    ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul, sub_add_cancel]

private theorem aeval_self_invFamily (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (i : σ) : aeval f (hf.invFamily hprec i) = X i := by
  refine hprec.induction (C := fun i ↦ aeval f (hf.invFamily hprec i) = X i) i fun i ih ↦ ?_
  let g := (hf i).choose_spec.choose
  have hg : ∀ j ∈ g.vars, prec j i := (hf i).choose_spec.choose_spec.1
  have hsub : f i - g = C ((hf i).choose : R) * X i := by
    have hfi := (hf i).choose_spec.choose_spec.2
    exact (eq_sub_iff_add_eq.mpr hfi.symm).symm
  have hg_eval : aeval f (aeval (hf.invFamily hprec) g) = g := by
    rw [comp_aeval_apply, aeval_def, algebraMap_eq]
    refine (eval₂_congr C (aeval f ∘ hf.invFamily hprec) X fun {j} {d} hjd hcd ↦ ?_).trans
      (eval₂_eta g)
    exact ih j (hg j ((mem_vars_iff_mem_support j).mpr ⟨d, mem_support_iff.mpr hcd, hjd⟩))
  rw [hf.invFamily_eq hprec i, map_mul, aeval_C, algebraMap_eq, map_sub, aeval_X, hg_eval, hsub,
    ← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]

/-- **Triangular polynomial substitutions are automorphisms.** When `prec` is well-founded,
`aeval f` is an `R`-algebra automorphism of `MvPolynomial σ R`. -/
noncomputable def algEquiv (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval f) (aeval (hf.invFamily hprec))
    (algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, aeval_X, hf.aeval_self_invFamily hprec i, AlgHom.id_apply])
    (algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, aeval_X, hf.aeval_invFamily_apply hprec i, AlgHom.id_apply])

/-- As an `R`-algebra homomorphism, `hf.algEquiv hprec` is `aeval f`. -/
@[simp]
theorem algEquiv_toAlgHom (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    (hf.algEquiv hprec : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) = aeval f :=
  (rfl)

/-- Evaluating `hf.algEquiv hprec` on a polynomial applies `aeval f`. -/
theorem algEquiv_apply (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (p : MvPolynomial σ R) : hf.algEquiv hprec p = aeval f p :=
  (rfl)

/-- `hf.algEquiv hprec` sends each variable `X i` to `f i`. -/
@[simp]
theorem algEquiv_X (hprec : WellFounded prec) (hf : IsTriangular prec f) (i : σ) :
    hf.algEquiv hprec (X i) = f i := by
  simp [algEquiv_apply]

/-- The inverse of `hf.algEquiv hprec` sends `f i` back to `X i`. -/
@[simp]
theorem algEquiv_symm_apply_self (hprec : WellFounded prec) (hf : IsTriangular prec f) (i : σ) :
    (hf.algEquiv hprec).symm (f i) = X i :=
  (hf.algEquiv hprec).symm_apply_eq.mpr (hf.algEquiv_X hprec i).symm

/-- Substituting `f` after `(hf.algEquiv hprec).symm` is the identity. -/
theorem aeval_algEquiv_symm (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (p : MvPolynomial σ R) : aeval f ((hf.algEquiv hprec).symm p) = p :=
  (hf.algEquiv hprec).apply_symm_apply p

/-- `(hf.algEquiv hprec).symm` after `aeval f` is the identity. -/
theorem algEquiv_symm_aeval (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (p : MvPolynomial σ R) : (hf.algEquiv hprec).symm (aeval f p) = p :=
  (hf.algEquiv hprec).symm_apply_apply p

/-- Substitution of a well-founded triangular family is bijective. -/
theorem aeval_bijective (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    Function.Bijective (aeval (R := R) f) :=
  (hf.algEquiv hprec).bijective

/-- A well-founded triangular family is algebraically independent over `R`. -/
theorem algebraicIndependent (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    AlgebraicIndependent R f :=
  algebraicIndependent_iff_injective_aeval.mpr (hf.aeval_bijective hprec).injective

/-- A well-founded triangular family generates `MvPolynomial σ R` as an `R`-algebra. -/
theorem adjoin_range_eq_top (hprec : WellFounded prec) (hf : IsTriangular prec f) :
    Algebra.adjoin R (Set.range f) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
  exact (hf.aeval_bijective hprec).surjective

/-- When each `f i` is weighted homogeneous of weight `w i`, `hf.algEquiv hprec` preserves and
reflects weighted homogeneity. -/
theorem isWeightedHomogeneous_algEquiv_iff {M : Type*} [AddCommMonoid M] {w : σ → M}
    (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (hw : ∀ i, (f i).IsWeightedHomogeneous w (w i)) {p : MvPolynomial σ R} {m : M} :
    (hf.algEquiv hprec p).IsWeightedHomogeneous w m ↔ p.IsWeightedHomogeneous w m := by
  classical
  refine ⟨fun hp ↦ ?_, fun hp ↦ hp.aeval hw⟩
  have hcomp : aeval f p = aeval f (weightedHomogeneousComponent w m p) :=
    (weightedHomogeneousComponent_eq_self hp).symm.trans
      (weightedHomogeneousComponent_aeval hw p m)
  rw [(hf.algEquiv hprec).injective hcomp]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m p

/-- Under `hf.algEquiv hprec`, the monomial ideal spanned by `X '' s` maps to
`Ideal.span (f '' s)`. -/
theorem map_algEquiv_span_X_image (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (s : Set σ) :
    (Ideal.span ((X : σ → MvPolynomial σ R) '' s)).map
        (hf.algEquiv hprec : MvPolynomial σ R →+* MvPolynomial σ R) =
      Ideal.span (f '' s) := by
  rw [Ideal.map_span, Set.image_image]
  simp

/-- **Eliminating a subset of a triangular family.** Quotienting `MvPolynomial σ R` by the ideal
spanned by `f '' s` gives the polynomial ring `MvPolynomial {i : σ // i ∉ s} R` in the remaining
variables. -/
noncomputable def quotientSpanImageEquiv (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (s : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span (f '' s)) ≃ₐ[R] MvPolynomial {i : σ // i ∉ s} R :=
  (Ideal.quotientEquivAlg (Ideal.span ((X : σ → MvPolynomial σ R) '' s)) (Ideal.span (f '' s))
    (hf.algEquiv hprec) (hf.map_algEquiv_span_X_image hprec s).symm).symm.trans
      (quotientSpanXImageEquiv R s)

/-- On a representative polynomial, `quotientSpanImageEquiv` applies `(hf.algEquiv hprec).symm`
and discards the variables in `s`. -/
theorem quotientSpanImageEquiv_mk (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (s : Set σ) (p : MvPolynomial σ R) :
    hf.quotientSpanImageEquiv hprec s (Ideal.Quotient.mk _ p) =
      killCompl (Subtype.val_injective (p := (· ∉ s))) ((hf.algEquiv hprec).symm p) := by
  simp [quotientSpanImageEquiv, quotientSpanXImageEquiv_mk]

/-- For `i ∉ s`, `quotientSpanImageEquiv` sends the class of `f i` to `X ⟨i, hi⟩`. -/
@[simp]
theorem quotientSpanImageEquiv_mk_apply_of_notMem (hprec : WellFounded prec)
    (hf : IsTriangular prec f) {s : Set σ} {i : σ} (hi : i ∉ s) :
    hf.quotientSpanImageEquiv hprec s (Ideal.Quotient.mk _ (f i)) = X ⟨i, hi⟩ := by
  let j : {k : σ // k ∉ s} := ⟨i, hi⟩
  rw [quotientSpanImageEquiv_mk, algEquiv_symm_apply_self, ← rename_X (f := Subtype.val) j]
  exact killCompl_rename_app (Subtype.val_injective (p := (· ∉ s))) (X j)

/-- The inverse of `quotientSpanImageEquiv` sends each variable `X i` (`i ∉ s`) to the class of
`f i.1`. -/
@[simp]
theorem quotientSpanImageEquiv_symm_X (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (s : Set σ) (i : {i : σ // i ∉ s}) :
    (hf.quotientSpanImageEquiv hprec s).symm (X i) = Ideal.Quotient.mk _ (f i.1) := by
  apply (hf.quotientSpanImageEquiv hprec s).injective
  rw [AlgEquiv.apply_symm_apply, hf.quotientSpanImageEquiv_mk_apply_of_notMem hprec i.2]

/-- Over a nontrivial ring without zero divisors, the ideal generated by any subset of a
well-founded triangular family is prime. -/
theorem isPrime_span_image [Nontrivial R] [NoZeroDivisors R] (hprec : WellFounded prec)
    (hf : IsTriangular prec f) (s : Set σ) : (Ideal.span (f '' s)).IsPrime := by
  rw [← hf.map_algEquiv_span_X_image hprec s]
  have := span_X_image_isPrime (R := R) s
  exact Ideal.map_isPrime_of_equiv (hf.algEquiv hprec)

/-- Over a nontrivial ring, no `f i` with `i ∉ s` lies in the ideal generated by `f '' s`. -/
theorem notMem_span_image [Nontrivial R] (hprec : WellFounded prec) (hf : IsTriangular prec f)
    {s : Set σ} {i : σ} (hi : i ∉ s) : f i ∉ Ideal.span (f '' s) := by
  rw [← hf.map_algEquiv_span_X_image hprec s, ← hf.algEquiv_X hprec i]
  intro hmem
  let e : MvPolynomial σ R →+* MvPolynomial σ R := hf.algEquiv hprec
  have hX : (X i : MvPolynomial σ R) ∈ Ideal.span ((X : σ → MvPolynomial σ R) '' s) := by
    have hc : (X i : MvPolynomial σ R) ∈
        ((Ideal.span ((X : σ → MvPolynomial σ R) '' s)).map e).comap e := hmem
    rwa [Ideal.comap_map_of_bijective e (hf.algEquiv hprec).bijective] at hc
  obtain ⟨j, hjs, hj0⟩ := mem_ideal_span_X_image.mp hX (single i 1) (by simp [support_X])
  have hji : j = i := by
    by_contra hne
    exact hj0 (single_eq_of_ne hne)
  exact hi (hji ▸ hjs)

/-- Any duplicate-free list from a well-founded triangular family is weakly regular on
`MvPolynomial σ R`. -/
theorem isWeaklyRegular_map (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (l.map f) := by
  have hcongr : IsWeaklyRegular (MvPolynomial σ R) (l.map (X (R := R))) ↔
      IsWeaklyRegular (MvPolynomial σ R) ((l.map (X (R := R))).map (hf.algEquiv hprec)) :=
    (hf.algEquiv hprec).toRingEquiv.toAddEquiv.isWeaklyRegular_congr <|
      List.forall₂_map_right_iff.mpr <|
        List.forall₂_same.mpr fun _ _ _ ↦ map_mul (hf.algEquiv hprec) _ _
  simpa [List.map_map, Function.comp_def] using hcongr.mp (isWeaklyRegular_map_X l hl)

/-- Over a nontrivial ring, any duplicate-free list from a well-founded triangular family is a
regular sequence on `MvPolynomial σ R`. -/
theorem isRegular_map [Nontrivial R] (hprec : WellFounded prec) (hf : IsTriangular prec f)
    (l : List σ) (hl : l.Nodup) :
    IsRegular (MvPolynomial σ R) (l.map f) := by
  have hcongr : IsRegular (MvPolynomial σ R) (l.map (X (R := R))) ↔
      IsRegular (MvPolynomial σ R) ((l.map (X (R := R))).map (hf.algEquiv hprec)) :=
    (hf.algEquiv hprec).toRingEquiv.toAddEquiv.isRegular_congr <|
      List.forall₂_map_right_iff.mpr <|
        List.forall₂_same.mpr fun _ _ _ ↦ map_mul (hf.algEquiv hprec) _ _
  simpa [List.map_map, Function.comp_def] using hcongr.mp (isRegular_map_X l hl)

end IsTriangular

end Triangular

section PositiveWeight

variable {R σ : Type*}

/-- **Positive-weight bound on decomposable monomials.** If every variable has positive weight
`0 < w i`, and `q` is weighted homogeneous of weight `m` and lies in `idealOfVars σ R ^ 2`, then
every variable occurring in `q` has weight strictly less than `m`. -/
theorem vars_weight_lt_of_isWeightedHomogeneous_of_mem_pow_idealOfVars [CommSemiring R]
    {w : σ → ℕ} (hw : ∀ i, 0 < w i) {q : MvPolynomial σ R} {m : ℕ}
    (hq : q.IsWeightedHomogeneous w m) (hq2 : q ∈ idealOfVars σ R ^ 2) {j : σ} (hj : j ∈ q.vars) :
    w j < m := by
  classical
  obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
  have hwm : Finsupp.weight w d = m := hq (mem_support_iff.mp hd)
  have hdeg : 2 ≤ d.degree := (mem_pow_idealOfVars_iff 2 q).mp hq2 d hd
  have hdj : 1 ≤ d j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjd)
  rw [← hwm, Finsupp.weight_apply, Finsupp.sum]
  rcases le_or_gt 2 (d j) with hdj2 | hdj1
  · have hle : d j • w j ≤ ∑ k ∈ d.support, d k • w k :=
      Finset.single_le_sum (f := fun k ↦ d k • w k) (fun _ _ ↦ Nat.zero_le _) hjd
    have hlt : w j < d j • w j := by
      simpa [nsmul_eq_mul] using (Nat.lt_mul_iff_one_lt_left (hw j)).mpr hdj2
    exact hlt.trans_le hle
  · have hdj_eq : d j = 1 := by omega
    -- Since `∑ k ∈ d.support, d k ≥ 2` and `d j = 1`, another variable `k ≠ j` appears in `d`.
    have hex : ∃ k ∈ d.support.erase j, 0 < d k := by
      by_contra! h0
      have hsum : ∑ k ∈ d.support.erase j, d k = 0 :=
        Finset.sum_eq_zero fun k hk ↦ Nat.le_zero.mp (h0 k hk)
      have hdeg' : d.degree = d j + ∑ k ∈ d.support.erase j, d k := by
        rw [Finsupp.degree_apply, ← Finset.add_sum_erase _ _ hjd]
      omega
    obtain ⟨k, hk_erase, hdk⟩ := hex
    have hpair : d j • w j + d k • w k ≤ ∑ l ∈ d.support, d l • w l := by
      rw [← Finset.add_sum_erase _ _ hjd]
      exact Nat.add_le_add_left
        (Finset.single_le_sum (f := fun l ↦ d l • w l) (fun _ _ ↦ Nat.zero_le _) hk_erase) _
    have hwk : 0 < d k • w k := by
      simpa [nsmul_eq_mul] using Nat.mul_pos hdk (hw k)
    calc w j = d j • w j := by simp [hdj_eq]
      _ < d j • w j + d k • w k := Nat.lt_add_of_pos_right hwk
      _ ≤ ∑ l ∈ d.support, d l • w l := hpair

/-- **Triangularity from positive weights modulo decomposables.** Let `w : σ → ℕ` assign positive
weights to all variables. If each `f i` has the form `uᵢ Xᵢ` modulo `idealOfVars σ R ^ 2` for a
unit `uᵢ : Rˣ` and `f i - uᵢ Xᵢ` is weighted homogeneous of weight `w i`, then `f` is triangular
with respect to the well-founded weight relation `w j < w i`. -/
theorem isTriangular_of_isWeightedHomogeneous_sub_mem_sq [CommRing R] {w : σ → ℕ}
    (hw : ∀ i, 0 < w i) {f : σ → MvPolynomial σ R}
    (hf : ∀ i, ∃ u : Rˣ, (f i - C (u : R) * X i).IsWeightedHomogeneous w (w i) ∧
      f i - C (u : R) * X i ∈ idealOfVars σ R ^ 2) :
    IsTriangular (fun j i ↦ w j < w i) f := by
  intro i
  obtain ⟨u, hwh, hmem⟩ := hf i
  refine ⟨u, f i - C (u : R) * X i, fun j hj ↦ ?_, by abel⟩
  exact vars_weight_lt_of_isWeightedHomogeneous_of_mem_pow_idealOfVars hw hwh hmem hj

end PositiveWeight

end MvPolynomial
