/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Localization.Integral

/-!
# Unramified Kummer witnesses at every multiple

Suppose `K₁ = K(α)` with `α ^ e = π`, where `π` is a uniformizer of the discrete
valuation ring `A` with fraction field `K`. If a finite separable extension `L₁/K₁`
is unramified over the integral closure of `A` in `K₁`, then adjoining a `d`-th root
`β` of `α` gives another such witness at exponent `e * d`:

* `K₁(β) = K(β)` has degree `e * d` over `K`;
* the integral closure of `A` in `K₁(β)` is a discrete valuation ring;
* `L₁(β)/K₁(β)` is finite and unramified over that integral closure.

Thus the existence of one unramified Kummer witness implies existence at every positive
multiple of its exponent. This is implication (2) ⇒ (3) of Stacks, Lemma 15.116.7
(Tag 0EXW). In fact this implication needs no invertibility condition on either exponent:
the original and enlarged root extractions may be wild. The unramifiedness follows from
base change (Stacks, Lemma 15.116.9), and the integral closures are identified using the
Kummer DVR theorem (Stacks, Lemma 15.116.2).

The constructions use the canonical integral closure of `A` in the enlarged field, rather
than an iterated integral closure. The inclusion `L₁ → L₁(β)` retains any original extension
contained in the witness `L₁`.
-/

public section

open _root_.IntermediateField

namespace TauCeti.Algebra

variable {A K K₁ L₁ Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field K₁] [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
  [Field L₁] [Algebra K₁ L₁]
  [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
  [Field Ω] [Algebra K Ω] [Algebra K₁ Ω] [Algebra L₁ Ω] [Algebra A Ω]
  [IsScalarTower K K₁ Ω] [IsScalarTower K₁ L₁ Ω] [IsScalarTower A K₁ Ω]
  [IsLocalRing (integralClosure A K₁)]

/-- Enlarge an unramified Kummer witness by a chosen root. The new base field has the
multiplied degree, and the extension of the enlarged base is still finite and unramified.
The base ring in the conclusion is the integral closure of the original `A`.
The local-ring instance on the original integral closure is needed only to state `h`;
it is supplied by the Kummer DVR theorem from `hπ`, `he`, `hα` and `hgen`. -/
theorem IsUnramifiedWRT.kummer_multiple
    (h : IsUnramifiedWRT (integralClosure A K₁) L₁)
    {π : A} (hπ : Irreducible π) {e : ℕ} (he : e ≠ 0) {α : K₁}
    (hα : α ^ e = algebraMap A K₁ π) (hgen : K⟮α⟯ = ⊤)
    {d : ℕ} (hd : d ≠ 0) {β : Ω} (hβ : β ^ d = algebraMap K₁ Ω α) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K₁ L₁ β).toAlgebra
    β ^ (e * d) = algebraMap A Ω π ∧
      K⟮AdjoinSimple.gen K₁ β⟯ = ⊤ ∧
      Module.finrank K K₁⟮β⟯ = e * d ∧
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁⟮β⟯),
        letI := hDVR
        IsUnramifiedWRT (integralClosure A K₁⟮β⟯) L₁⟮β⟯ ∧
          FiniteDimensional K₁⟮β⟯ L₁⟮β⟯ := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K₁ L₁ β).toAlgebra
  -- Identify the enlarged base as the single root extraction of degree `e * d` over `K`.
  have hβπ : β ^ (e * d) = algebraMap A Ω π := by
    rw [Nat.mul_comm, pow_mul, hβ, ← map_pow, hα, ← IsScalarTower.algebraMap_apply]
  have hβK : AdjoinSimple.gen K₁ β ^ (e * d) = algebraMap A K₁⟮β⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K₁ K₁⟮β⟯,
      IsScalarTower.algebraMap_apply A K₁ Ω] using hβπ)
  have : IsScalarTower A K Ω := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K₁ Ω, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ Ω]
  have : IsScalarTower A K K₁⟮β⟯ := .of_algebraMap_eq fun a ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A K Ω a)
  have hgenβ : K⟮AdjoinSimple.gen K₁ β⟯ = ⊤ :=
    TauCeti.IntermediateField.adjoin_gen_eq_top_of_pow_eq hgen hβ
  have hdegree := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible
    hπ hβK hgenβ
  have : FiniteDimensional K K₁⟮β⟯ :=
    Module.finite_of_finrank_pos (hdegree ▸ Nat.mul_pos (Nat.pos_of_ne_zero he)
      (Nat.pos_of_ne_zero hd))
  have := IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
    hπ hβK hgenβ
  -- Use the canonical integral closures over `A` on both sides of base change.
  have : IsFractionRing (integralClosure A K₁) K₁ := by
    have hdegree₁ := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hα hgen
    have : FiniteDimensional K K₁ :=
      Module.finite_of_finrank_pos (hdegree₁ ▸ Nat.pos_of_ne_zero he)
    exact IsIntegralClosure.isFractionRing_of_finite_extension A K K₁ _
  have : IsDiscreteValuationRing (integralClosure A K₁) :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hα hgen
  have : IsFractionRing (integralClosure A K₁⟮β⟯) K₁⟮β⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K₁⟮β⟯ _
  let := integralClosureMapAlgebra A K₁ A K₁⟮β⟯
  have := isScalarTower_integralClosureMapAlgebra_right A K₁ A K₁⟮β⟯
  have : IsScalarTower (integralClosure A K₁) K₁⟮β⟯ L₁⟮β⟯ :=
    IsScalarTower.of_algHom
      ((TauCeti.IntermediateField.adjoinBaseChange K₁ L₁ β).restrictScalars (integralClosure A K₁))
  have hβint : IsIntegral L₁ β :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hd) (hβ ▸ isIntegral_algebraMap)).tower_top
  have hsurj := TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K₁ L₁ hβint
  refine ⟨hβπ, hgenβ, hdegree, inferInstance, ?_, ?_⟩
  · exact h.baseChange (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K₁ L₁ β) hsurj
  · exact Module.Finite.of_surjective
      (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K₁ L₁ β).toLinearMap hsurj

/-- If one finite unramified Kummer witness exists, an algebraically closed overfield supplies
such a witness at every positive multiple of the exponent. The enlarged witness contains
`L₁` through its canonical inclusion into `L₁(β)`. -/
@[stacks 0EXW "(2) ⇒ (3), without requiring the multiple to be invertible"]
theorem IsUnramifiedWRT.exists_kummer_multiple [IsAlgClosed Ω]
    (h : IsUnramifiedWRT (integralClosure A K₁) L₁)
    {π : A} (hπ : Irreducible π) {e : ℕ} (he : e ≠ 0) {α : K₁}
    (hα : α ^ e = algebraMap A K₁ π) (hgen : K⟮α⟯ = ⊤) {d : ℕ} (hd : d ≠ 0) :
    ∃ β : Ω,
      letI := (TauCeti.IntermediateField.adjoinBaseChange K₁ L₁ β).toAlgebra
      β ^ (e * d) = algebraMap A Ω π ∧
        K⟮AdjoinSimple.gen K₁ β⟯ = ⊤ ∧
        Module.finrank K K₁⟮β⟯ = e * d ∧
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁⟮β⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K₁⟮β⟯) L₁⟮β⟯ ∧
            FiniteDimensional K₁⟮β⟯ L₁⟮β⟯ := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₁ Ω α) (Nat.pos_of_ne_zero hd)
  exact ⟨β, h.kummer_multiple hπ he hα hgen hd hβ⟩

end TauCeti.Algebra
