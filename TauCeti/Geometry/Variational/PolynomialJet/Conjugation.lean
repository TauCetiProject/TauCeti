/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.Tactic.LinearCombination

/-!
# Conjugation of polynomial jets

A complex field theory is written either in real field components or in a complex field `ψ`
together with its conjugate `ψ*`. This file extends complex conjugation from the coefficients to
polynomial jet expressions and compares the two presentations.

An involution `σ` of the field labels records which generators are conjugate to each other: the
identity for real fields, and the swap of `ψ` and `ψ*` for a conjugate-paired field.
`PolynomialJet.conjugation σ` conjugates the coefficients, fixes the base coordinates and sends
`uᵃ_I` to `u^(σ a)_I`. Base coordinates are real, and conjugation does not change the jet
multi-index. The main results are:

* `PolynomialJet.totalDeriv_conjugation`: conjugation commutes with every total derivative.
* `PolynomialJet.star_aeval_eq_aeval_conjugation_iff`: in a commutative star algebra, evaluation
  intertwines conjugation of expressions with `star` exactly when the base values are
  self-adjoint and the field values satisfy the reality condition `star (u a I) = u (σ a) I`.
* `PolynomialJet.mem_realPoints_conjugationₛₗ_id_iff` and
  `PolynomialJet.realPolynomialJetEquiv`: the complex polynomial jets fixed by conjugation of
  real fields are precisely the real polynomial jets. Combined with
  `TauCeti.realPointsEquiv`, this is real descent for polynomial jets.
* `PolynomialJet.realPairEquiv`: the change of generators `ψ = y + i z`, `ψ* = y - i z` from a
  conjugate-paired field to its real and imaginary parts. It commutes with total derivatives,
  intertwines the two conjugations, and compares the paired evaluation at `(φ, star φ)` with the
  real evaluation at the real and imaginary parts of `φ`
  (`PolynomialJet.aeval_star_eq_aeval_realPairEquiv`).

No Hermitian metric enters: the conjugation is a coefficient-and-label operation, and the
evaluations are algebra homomorphisms.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for symmetric jet
  coordinates and total derivatives.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, for real
  structures given by conjugations.
-/

public section

open MvPolynomial
open scoped ComplexStarModule

namespace TauCeti
namespace PolynomialJet

noncomputable section

section Conjugation

variable {R ι α : Type*} [CommSemiring R] [StarRing R]

/-- Conjugation of polynomial jets along a relabelling `σ` of the fields: coefficients are
conjugated, base coordinates are fixed and the field jet `uᵃ_I` goes to `u^(σ a)_I`. In the
intended use `σ` is an involution pairing each field with its conjugate. -/
def conjugation (σ : α → α) : PolynomialJet R ι α →+* PolynomialJet R ι α :=
  eval₂Hom (C.comp (starRingEnd R)) fun v ↦ X (Sum.map id (Prod.map σ id) v)

@[simp]
theorem conjugation_C (σ : α → α) (c : R) :
    conjugation (ι := ι) σ (C c) = C (star c) := by
  simp [conjugation, starRingEnd_apply]

@[simp]
theorem conjugation_X_base (σ : α → α) (j : ι) :
    conjugation (R := R) σ (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [conjugation]

@[simp]
theorem conjugation_X_field (σ : α → α) (a : α) (I : ι →₀ ℕ) :
    conjugation (R := R) σ (X (Sum.inr (a, I))) = X (Sum.inr (σ a, I)) := by
  simp [conjugation]

/-- Conjugation is semilinear for `star`. -/
@[simp]
theorem conjugation_smul (σ : α → α) (c : R) (p : PolynomialJet R ι α) :
    conjugation σ (c • p) = star c • conjugation σ p := by
  rw [smul_eq_C_mul, map_mul, conjugation_C, smul_eq_C_mul]

/-- Conjugation conjugates the coefficients and then relabels the conjugate field jets. -/
theorem conjugation_eq_rename_map (σ : α → α) (p : PolynomialJet R ι α) :
    conjugation σ p = rename (Sum.map id (Prod.map σ id)) (map (starRingEnd R) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [starRingEnd_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩ <;> simp [hp]

/-- For real fields, conjugation of polynomial jets is conjugation of coefficients. -/
theorem conjugation_id (p : PolynomialJet R ι α) :
    conjugation id p = map (starRingEnd R) p := by
  rw [conjugation_eq_rename_map, Prod.map_id, Sum.map_id_id, rename_id_apply]

/-- Conjugation along an involution of the field labels is an involution. -/
theorem conjugation_conjugation {σ : α → α} (hσ : Function.Involutive σ)
    (p : PolynomialJet R ι α) : conjugation σ (conjugation σ p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩
    · simp [hp]
    · simp [hp, hσ a]

/-- Conjugation along an involution of the field labels is an involutive map of polynomial
jets. -/
theorem conjugation_involutive {σ : α → α} (hσ : Function.Involutive σ) :
    Function.Involutive (conjugation (R := R) (ι := ι) σ) :=
  conjugation_conjugation hσ

/-- **Conjugation commutes with total differentiation.** -/
@[simp]
theorem totalDeriv_conjugation (σ : α → α) (i : ι) (p : PolynomialJet R ι α) :
    totalDeriv i (conjugation σ p) = conjugation σ (totalDeriv i p) :=
  totalDeriv_eval₂Hom_relabel (starRingEnd R) σ i p

/-- Conjugation preserves each finite stage. -/
theorem conjugation_mem_stage (σ : α → α) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : conjugation σ p ∈ stage R ι α r := by
  classical
  rw [mem_stage_iff] at hp ⊢
  intro a I h
  rw [conjugation_eq_rename_map] at h
  obtain ⟨v, hv, hva⟩ := Finset.mem_image.1 (vars_rename _ _ h)
  rcases v with j | ⟨b, J⟩
  · simp at hva
  · simp only [Sum.map_inr, Prod.map_apply, id_eq, Sum.inr.injEq, Prod.mk.injEq] at hva
    obtain ⟨-, rfl⟩ := hva
    exact hp b J (vars_map _ _ hv)

/-- Along an involution of the field labels, an expression lies in stage `r` exactly when its
conjugate does: conjugation neither raises nor lowers the jet order. -/
theorem conjugation_mem_stage_iff {σ : α → α} (hσ : Function.Involutive σ) {r : ℕ}
    {p : PolynomialJet R ι α} : conjugation σ p ∈ stage R ι α r ↔ p ∈ stage R ι α r :=
  ⟨fun h ↦ conjugation_conjugation hσ p ▸ conjugation_mem_stage σ h, conjugation_mem_stage σ⟩

/-- Conjugation of polynomial jets as a conjugate-linear map, the form used by real descent. -/
def conjugationₛₗ (σ : α → α) : PolynomialJet R ι α →ₛₗ[starRingEnd R] PolynomialJet R ι α where
  toFun := conjugation σ
  map_add' := map_add _
  map_smul' := conjugation_smul σ

@[simp]
theorem coe_conjugationₛₗ (σ : α → α) :
    ⇑(conjugationₛₗ (R := R) (ι := ι) σ) = conjugation σ :=
  (rfl)

end Conjugation

section Evaluation

variable {R ι α A : Type*} [CommSemiring R] [StarRing R]
  [CommSemiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- **Conjugation and field evaluation.** If the base values are self-adjoint and the field values
satisfy the reality condition `star (u a I) = u (σ a) I`, then evaluating the conjugate of an
expression gives the `star` of its evaluation. -/
theorem star_aeval_eq_aeval_conjugation (σ : α → α) (x : ι → A) (u : α → (ι →₀ ℕ) → A)
    (hx : ∀ j, star (x j) = x j) (hu : ∀ a I, star (u a I) = u (σ a) I)
    (p : PolynomialJet R ι α) :
    star (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) =
      aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) (conjugation σ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [algebraMap_star_comm]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩ <;> simp [hp, hx, hu]

/-- Evaluation intertwines conjugation with `star` on all expressions exactly when the base values
are self-adjoint and the field values satisfy the reality condition. -/
theorem star_aeval_eq_aeval_conjugation_iff (σ : α → α) (x : ι → A) (u : α → (ι →₀ ℕ) → A) :
    (∀ p : PolynomialJet R ι α, star (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) =
      aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) (conjugation σ p)) ↔
      (∀ j, star (x j) = x j) ∧ ∀ a I, star (u a I) = u (σ a) I := by
  refine ⟨fun h ↦ ⟨fun j ↦ by simpa using h (X (Sum.inl j)),
    fun a I ↦ by simpa using h (X (Sum.inr (a, I)))⟩, fun ⟨hx, hu⟩ ↦
    star_aeval_eq_aeval_conjugation σ x u hx hu⟩

/-- A conjugation-invariant expression has self-adjoint values at fields satisfying the reality
condition. -/
theorem isSelfAdjoint_aeval_of_conjugation_eq_self {σ : α → α} {x : ι → A}
    {u : α → (ι →₀ ℕ) → A} (hx : ∀ j, star (x j) = x j) (hu : ∀ a I, star (u a I) = u (σ a) I)
    {p : PolynomialJet R ι α} (hp : conjugation σ p = p) :
    IsSelfAdjoint (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) := by
  rw [IsSelfAdjoint, star_aeval_eq_aeval_conjugation σ x u hx hu, hp]

end Evaluation

section RealDescent

variable {ι α : Type*}

/-- **Real polynomial jets.** A complex polynomial jet of real fields is fixed by conjugation if
and only if it has real coefficients. -/
theorem mem_realPoints_conjugationₛₗ_id_iff (p : PolynomialJet ℂ ι α) :
    p ∈ realPoints (conjugationₛₗ id) ↔ p ∈ Set.range (map (algebraMap ℝ ℂ)) := by
  rw [mem_realPoints, coe_conjugationₛₗ, conjugation_id, mem_range_map_iff_coeffs_subset]
  constructor
  · intro h c hc
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 (by rw [← coeff_map (starRingEnd ℂ) p m, h])
    exact ⟨r, hr.symm⟩
  · intro h
    ext m
    rw [coeff_map]
    by_cases hm : m ∈ p.support
    · obtain ⟨r, hr⟩ := h (coeff_mem_coeffs m (mem_support_iff.1 hm))
      rw [← hr, Complex.coe_algebraMap, Complex.conj_ofReal]
    · rw [notMem_support_iff.1 hm, map_zero]

/-- The real polynomial jets are the real points of conjugation on complex polynomial jets of
real fields, by extension of scalars. -/
def realPolynomialJetEquiv :
    PolynomialJet ℝ ι α ≃ₗ[ℝ] realPoints (conjugationₛₗ (R := ℂ) (ι := ι) (α := α) id) :=
  LinearEquiv.ofBijective
    { toFun q := ⟨map (algebraMap ℝ ℂ) q,
        (mem_realPoints_conjugationₛₗ_id_iff _).2 (Set.mem_range_self q)⟩
      map_add' q q' := Subtype.ext (map_add _ q q')
      map_smul' c q := Subtype.ext <| by
        simp [Complex.coe_algebraMap, Algebra.smul_def] }
    ⟨fun q q' h ↦ map_injective _ (algebraMap ℝ ℂ).injective (congrArg Subtype.val h),
      fun p ↦ by
        obtain ⟨q, hq⟩ := (mem_realPoints_conjugationₛₗ_id_iff p.val).1 p.property
        exact ⟨q, Subtype.ext hq⟩⟩

@[simp]
theorem coe_realPolynomialJetEquiv_apply (q : PolynomialJet ℝ ι α) :
    (realPolynomialJetEquiv q : PolynomialJet ℂ ι α) = map (algebraMap ℝ ℂ) q :=
  (rfl)

/-- Real descent for polynomial jets is compatible with total differentiation. -/
theorem coe_realPolynomialJetEquiv_totalDeriv (i : ι) (q : PolynomialJet ℝ ι α) :
    (realPolynomialJetEquiv (totalDeriv i q) : PolynomialJet ℂ ι α) =
      totalDeriv i (realPolynomialJetEquiv q : PolynomialJet ℂ ι α) := by
  simp

end RealDescent

section RealPair

variable {ι α : Type*}

/-- The images of the generators under `realPairEquiv`: a conjugate pair `(ψ, ψ*)` of field jets
becomes `(y + i z, y - i z)`, with `y` and `z` the real and imaginary parts. -/
private def realPairField : α ⊕ α → (ι →₀ ℕ) → PolynomialJet ℂ ι (α ⊕ α)
  | Sum.inl a, I => X (Sum.inr (Sum.inl a, I)) + Complex.I • X (Sum.inr (Sum.inr a, I))
  | Sum.inr a, I => X (Sum.inr (Sum.inl a, I)) - Complex.I • X (Sum.inr (Sum.inr a, I))

/-- The images of the generators under `realPairEquiv.symm`: the real and imaginary parts are
`y = (ψ + ψ*) / 2` and `z = -i (ψ - ψ*) / 2`. -/
private def pairField : α ⊕ α → (ι →₀ ℕ) → PolynomialJet ℂ ι (α ⊕ α)
  | Sum.inl a, I => (2⁻¹ : ℂ) • (X (Sum.inr (Sum.inl a, I)) + X (Sum.inr (Sum.inr a, I)))
  | Sum.inr a, I => (-(Complex.I / 2)) • (X (Sum.inr (Sum.inl a, I)) - X (Sum.inr (Sum.inr a, I)))

private theorem aeval_realPairField_pairField (a : α ⊕ α) (I : ι →₀ ℕ) :
    aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ realPairField aI.1 aI.2)
      (pairField a I) = X (Sum.inr (a, I)) := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases a with a | a
  · simp only [pairField, realPairField, map_smul, map_add, aeval_X, Sum.elim_inr]
    module
  · simp only [pairField, realPairField, map_smul, map_sub, aeval_X, Sum.elim_inr]
    match_scalars
    · ring
    · linear_combination (-1 : ℂ) * h

private theorem aeval_pairField_realPairField (a : α ⊕ α) (I : ι →₀ ℕ) :
    aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ pairField aI.1 aI.2)
      (realPairField a I) = X (Sum.inr (a, I)) := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases a with a | a
  · simp only [pairField, realPairField, map_smul, map_add, aeval_X, Sum.elim_inr]
    match_scalars
    · linear_combination (-1 / 2 : ℂ) * h
    · linear_combination (1 / 2 : ℂ) * h
  · simp only [pairField, realPairField, map_smul, map_sub, aeval_X, Sum.elim_inr]
    match_scalars
    · linear_combination (1 / 2 : ℂ) * h
    · linear_combination (-1 / 2 : ℂ) * h

/-- **Real and imaginary parts of a conjugate-paired field.** The field labels `α ⊕ α` are read in
the source as a complex field `ψ` (`Sum.inl`) and its conjugate `ψ*` (`Sum.inr`), and in the target
as real fields `y` (`Sum.inl`) and `z` (`Sum.inr`). The equivalence substitutes
`ψ_I = y_I + i z_I` and `ψ*_I = y_I - i z_I` and fixes the base coordinates. -/
def realPairEquiv : PolynomialJet ℂ ι (α ⊕ α) ≃ₐ[ℂ] PolynomialJet ℂ ι (α ⊕ α) :=
  AlgEquiv.ofAlgHom (aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ realPairField aI.1 aI.2))
    (aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ pairField aI.1 aI.2))
    (by
      ext (j | ⟨a, I⟩) : 1
      · simp [pairField]
      · simpa using aeval_realPairField_pairField a I)
    (by
      ext (j | ⟨a, I⟩) : 1
      · simp [realPairField]
      · simpa using aeval_pairField_realPairField a I)

private theorem realPairEquiv_apply (p : PolynomialJet ℂ ι (α ⊕ α)) :
    realPairEquiv p =
      aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ realPairField aI.1 aI.2) p :=
  (rfl)

private theorem realPairEquiv_symm_apply (p : PolynomialJet ℂ ι (α ⊕ α)) :
    realPairEquiv.symm p =
      aeval (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ pairField aI.1 aI.2) p :=
  (rfl)

@[simp]
theorem realPairEquiv_C (c : ℂ) : realPairEquiv (ι := ι) (α := α) (C c) = C c := by
  simp [realPairEquiv_apply]

@[simp]
theorem realPairEquiv_X_base (j : ι) :
    realPairEquiv (α := α) (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [realPairEquiv_apply]

@[simp]
theorem realPairEquiv_X_field_inl (a : α) (I : ι →₀ ℕ) :
    realPairEquiv (X (Sum.inr (Sum.inl a, I))) =
      X (Sum.inr (Sum.inl a, I)) + Complex.I • X (Sum.inr (Sum.inr a, I)) := by
  simp [realPairEquiv_apply, realPairField]

@[simp]
theorem realPairEquiv_X_field_inr (a : α) (I : ι →₀ ℕ) :
    realPairEquiv (X (Sum.inr (Sum.inr a, I))) =
      X (Sum.inr (Sum.inl a, I)) - Complex.I • X (Sum.inr (Sum.inr a, I)) := by
  simp [realPairEquiv_apply, realPairField]

@[simp]
theorem realPairEquiv_symm_C (c : ℂ) :
    (realPairEquiv (ι := ι) (α := α)).symm (C c) = C c := by
  simp [realPairEquiv_symm_apply]

@[simp]
theorem realPairEquiv_symm_X_base (j : ι) :
    (realPairEquiv (ι := ι) (α := α)).symm (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [realPairEquiv_symm_apply]

@[simp]
theorem realPairEquiv_symm_X_field_inl (a : α) (I : ι →₀ ℕ) :
    realPairEquiv.symm (X (Sum.inr (Sum.inl a, I))) =
      (2⁻¹ : ℂ) • (X (Sum.inr (Sum.inl a, I)) + X (Sum.inr (Sum.inr a, I))) := by
  simp [realPairEquiv_symm_apply, pairField]

@[simp]
theorem realPairEquiv_symm_X_field_inr (a : α) (I : ι →₀ ℕ) :
    realPairEquiv.symm (X (Sum.inr (Sum.inr a, I))) =
      (-(Complex.I / 2)) • (X (Sum.inr (Sum.inl a, I)) - X (Sum.inr (Sum.inr a, I))) := by
  simp [realPairEquiv_symm_apply, pairField]

/-- Passing to real and imaginary parts commutes with total differentiation. -/
@[simp]
theorem totalDeriv_realPairEquiv (i : ι) (p : PolynomialJet ℂ ι (α ⊕ α)) :
    totalDeriv i (realPairEquiv p) = realPairEquiv (totalDeriv i p) := by
  classical
  rw [realPairEquiv_apply, realPairEquiv_apply]
  refine (totalDeriv i).aeval_polynomialJet i _ _ (fun j ↦ by simp) (fun a I ↦ ?_) p
  rcases a with a | a <;> simp [realPairField]

/-- Recovering the conjugate-paired field `(ψ, ψ*)` from its real and imaginary parts also
commutes with total differentiation. -/
@[simp]
theorem totalDeriv_realPairEquiv_symm (i : ι) (p : PolynomialJet ℂ ι (α ⊕ α)) :
    totalDeriv i (realPairEquiv.symm p) = realPairEquiv.symm (totalDeriv i p) := by
  apply realPairEquiv.injective
  rw [← totalDeriv_realPairEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- Passing to real and imaginary parts turns conjugation of a conjugate-paired field, which
swaps `ψ` and `ψ*`, into conjugation of real fields. -/
@[simp]
theorem conjugation_id_realPairEquiv (p : PolynomialJet ℂ ι (α ⊕ α)) :
    conjugation id (realPairEquiv p) = realPairEquiv (conjugation Sum.swap p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [realPairEquiv_C, conjugation_C, conjugation_C, realPairEquiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with j | ⟨a | a, I⟩ <;> simp [sub_eq_add_neg]

/-- **Real expressions in a conjugate-paired field.** An expression in `ψ` and `ψ*` is invariant
under conjugation if and only if it is a real polynomial jet in the real and imaginary parts. -/
theorem conjugation_swap_eq_self_iff (p : PolynomialJet ℂ ι (α ⊕ α)) :
    conjugation Sum.swap p = p ↔ realPairEquiv p ∈ Set.range (map (algebraMap ℝ ℂ)) := by
  rw [← mem_realPoints_conjugationₛₗ_id_iff, mem_realPoints, coe_conjugationₛₗ,
    conjugation_id_realPairEquiv, realPairEquiv.injective.eq_iff]

section Evaluation

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Evaluating the real-part expression at real fields `(y, z)` is evaluating the paired
expression at `(y + i z, y - i z)`. -/
theorem aeval_realPairEquiv (x : ι → A) (y z : α → (ι →₀ ℕ) → A)
    (p : PolynomialJet ℂ ι (α ⊕ α)) :
    aeval (Sum.elim x fun aI ↦ Sum.elim y z aI.1 aI.2) (realPairEquiv p) =
      aeval (Sum.elim x fun aI ↦
        Sum.elim (fun a I ↦ y a I + Complex.I • z a I)
          (fun a I ↦ y a I - Complex.I • z a I) aI.1 aI.2) p := by
  rw [realPairEquiv_apply, comp_aeval_apply]
  congr 1
  ext (j | ⟨a | a, I⟩) <;> simp [realPairField]

/-- **Real and conjugate-paired evaluations agree.** Evaluating an expression in `ψ` and `ψ*` at a
complex field `φ` and its conjugate `star φ` is evaluating its real-part expression at the real
and imaginary parts of `φ`. -/
theorem aeval_star_eq_aeval_realPairEquiv [StarRing A] [StarModule ℂ A] (x : ι → A)
    (φ : α → (ι →₀ ℕ) → A) (p : PolynomialJet ℂ ι (α ⊕ α)) :
    aeval (Sum.elim x fun aI ↦ Sum.elim φ (fun a I ↦ star (φ a I)) aI.1 aI.2) p =
      aeval (Sum.elim x fun aI ↦
        Sum.elim (fun a I ↦ (ℜ (φ a I) : A)) (fun a I ↦ (ℑ (φ a I) : A))
          aI.1 aI.2) (realPairEquiv p) := by
  rw [aeval_realPairEquiv]
  refine congrArg (fun f ↦ aeval f p) (funext fun v ↦ ?_)
  rcases v with j | ⟨a | a, I⟩
  · rfl
  · exact (realPart_add_I_smul_imaginaryPart (φ a I)).symm
  · dsimp only [Sum.elim_inr, Sum.elim_inl]
    calc star (φ a I) = star ((ℜ (φ a I) : A) + Complex.I • (ℑ (φ a I) : A)) := by
          rw [realPart_add_I_smul_imaginaryPart]
      _ = (ℜ (φ a I) : A) - Complex.I • (ℑ (φ a I) : A) := by simp [sub_eq_add_neg]

end Evaluation

end RealPair

end

end PolynomialJet
end TauCeti
