/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified

/-!
# Enlarging a root extraction under an unramified extension

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let
`L/K` be finite separable and unramified with respect to `A`. Adjoining an `n`-th root `α` of
`π` to both fields gives an extension `L(α)/K(α)` unramified with respect to the integral
closure of `A` in `K(α)`. The root extraction itself can be wildly ramified: no invertibility
condition on `n` is needed.

Applied with `A` the integral closure in a Kummer extension `K₀(π₀^(1/e))`, and `π` its root
uniformizer, this enlarges the exponent from `e` to `en`. It is the base-change step in the
implication (2) ⇒ (3) of Stacks, Lemma 15.116.7. The two inputs are the Kummer DVR theorem
(Stacks 15.116.2) and stability of unramified extensions under base change (Stacks 15.116.9).

## References

* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

open scoped TensorProduct
open _root_.IntermediateField

namespace TauCeti.Algebra

variable {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
  [IsScalarTower A K Ω]

/-- Adjoining a root of a uniformizer to both fields preserves unramifiedness. The integral
closure in the new base field is a discrete valuation ring, even for a wild root extraction.
The algebra structure on `L(α)` is induced by the canonical inclusion `K(α) → L(α)`. -/
theorem IsUnramifiedWRT.adjoin_root (h : IsUnramifiedWRT A L) {π : A}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) {α : Ω}
    (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have hgen : K⟮AdjoinSimple.gen K α⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  have := IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
    hπ hn hαK hgen
  have hdegree := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hn hαK hgen
  have : FiniteDimensional K K⟮α⟯ :=
    Module.finite_of_finrank_pos (hdegree ▸ Nat.pos_of_ne_zero hn)
  have : IsFractionRing (integralClosure A K⟮α⟯) K⟮α⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α⟯ _
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
  have hint : IsIntegral K α :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap (R := A))).tower_top
  refine ⟨inferInstance, ?_⟩
  exact h.baseChange (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α)
    (TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hint.tower_top)

/-- In an algebraically closed ambient extension, every positive root degree admits an
unramified extension after adjoining a root of the uniformizer to both fields. In particular,
one may enlarge a Kummer exponent by any positive multiple. -/
theorem IsUnramifiedWRT.exists_adjoin_root [IsAlgClosed Ω] (h : IsUnramifiedWRT A L)
    {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) :
    ∃ α : Ω, α ^ n = algebraMap A Ω π ∧
      letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
        letI := hDVR
        IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  exact ⟨α, hα, h.adjoin_root hπ hn.ne' hα⟩

end TauCeti.Algebra
