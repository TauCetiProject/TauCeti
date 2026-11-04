/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.TranslationDifference.Basic
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Quotient

/-!
# Translation difference on the p-adic units modulo torsion

On `Γ = ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ`, multiplication by the class of
`padicUnitsGenerator p` corresponds to translation by `+1` in the logarithmic coordinate.
Consequently `f ↦ (x ↦ f (x γ) - f x)` has kernel the constants and is surjective for complete
ultrametric normed modules with bounded `ℤ_[p]` action. Its continuous linear right inverse is
normalized to vanish at the identity. We transport `mahlerPrimitive`, rather than choosing
preimages abstractly. These are the continuous-function difference equations used in
height-one descent.

The generator matters: replacing it by its inverse changes the operator to
`f (x γ⁻¹) - f x`, not to the same operator. Here it is pinned to `padicUnitsGenerator p`.
The full torsion quotient works at every prime; at `2` its finite subgroup is `{±1}`.

## References

* Douglas–Francis–Henriques–Hill (eds.), *Topological Modular Forms*, Chapter 6.
* The additive construction is `TauCeti.mahlerPrimitive`, built from Mathlib's
  `PadicInt.mahlerEquiv`.
-/

public section

namespace TauCeti

open Multiplicative

variable {p : ℕ} [Fact p.Prime]
variable (E : Type*) [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

private noncomputable def pullbackCoordinate :
    C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) →L[ℤ_[p]] C(ℤ_[p], E) :=
  ContinuousMap.compCLM ℤ_[p] E
    ⟨fun x ↦ (padicIntUnitsQuotientTorsionEquiv p).symm (ofAdd x),
      (padicIntUnitsQuotientTorsionEquiv p).symm.continuous.comp continuous_ofAdd⟩

private noncomputable def pushforwardCoordinate :
    C(ℤ_[p], E) →L[ℤ_[p]] C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) :=
  ContinuousMap.compCLM ℤ_[p] E
    ⟨fun x ↦ (padicIntUnitsQuotientTorsionEquiv p x).toAdd,
      continuous_toAdd.comp (padicIntUnitsQuotientTorsionEquiv p).continuous⟩

private theorem pullbackCoordinate_apply
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) (x : ℤ_[p]) :
    pullbackCoordinate E f x = f ((padicIntUnitsQuotientTorsionEquiv p).symm (ofAdd x)) := (rfl)

private theorem pushforwardCoordinate_apply (f : C(ℤ_[p], E))
    (x : ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ) :
    pushforwardCoordinate E f x = f (padicIntUnitsQuotientTorsionEquiv p x).toAdd := (rfl)

private theorem pushforward_pullback
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    pushforwardCoordinate E (pullbackCoordinate E f) = f := by
  ext x
  simp only [pushforwardCoordinate_apply, pullbackCoordinate_apply, ofAdd_toAdd,
    ContinuousMulEquiv.symm_apply_apply]

private theorem pullback_pushforward (f : C(ℤ_[p], E)) :
    pullbackCoordinate E (pushforwardCoordinate E f) = f := by
  ext x
  simp only [pullbackCoordinate_apply, pushforwardCoordinate_apply,
    ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- Multiplication by the chosen principal generator minus the identity, on functions on the
units modulo torsion. -/
noncomputable def unitsQuotientDiff :
    C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) →L[ℤ_[p]]
      C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) :=
  ContinuousMap.compCLM ℤ_[p] E
    ⟨fun x ↦ x * QuotientGroup.mk (padicUnitsGenerator p),
      continuous_id.mul continuous_const⟩ - ContinuousLinearMap.id ℤ_[p] _

@[simp]
theorem unitsQuotientDiff_apply (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E))
    (x : ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ) :
    unitsQuotientDiff E f x = f (x * QuotientGroup.mk (padicUnitsGenerator p)) - f x := (rfl)

/-- The generator difference kills constant functions. -/
@[simp]
theorem unitsQuotientDiff_const (c : E) :
    unitsQuotientDiff (p := p) E (ContinuousMap.const _ c) = 0 := by
  ext x
  simp

private theorem pullbackCoordinate_diff
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    pullbackCoordinate E (unitsQuotientDiff E f) = fwdDiffCLM E (pullbackCoordinate E f) := by
  ext x
  simp only [pullbackCoordinate_apply, unitsQuotientDiff_apply, fwdDiffCLM_apply]
  congr 2
  apply (padicIntUnitsQuotientTorsionEquiv p).injective
  simp only [map_mul, ContinuousMulEquiv.apply_symm_apply,
    padicIntUnitsQuotientTorsionEquiv_mk, padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator,
    ofAdd_add]

/-- The kernel of the generator difference consists precisely of constant functions. No
completeness or ultrametric hypothesis is needed for this assertion. -/
theorem unitsQuotientDiff_eq_zero_iff
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    unitsQuotientDiff E f = 0 ↔
      f = ContinuousMap.const _ (f 1) := by
  constructor
  · intro hf
    have h := (fwdDiffCLM_eq_zero_iff E (pullbackCoordinate E f)).mp (by
      rw [← pullbackCoordinate_diff, hf, map_zero])
    have h' := congrArg (pushforwardCoordinate E) h
    ext x
    simpa [pushforward_pullback, pushforwardCoordinate_apply, pullbackCoordinate_apply] using
      congrArg (fun g ↦ g x) h'
  · intro hf
    rw [hf]
    ext x
    simp

/-- Constants and the generator difference form an exact sequence of continuous linear maps. -/
theorem exact_const_unitsQuotientDiff :
    Function.Exact (ContinuousLinearMap.const ℤ_[p]
      (ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ) :
        E →L[ℤ_[p]] C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E))
      (unitsQuotientDiff E) := by
  intro f
  rw [unitsQuotientDiff_eq_zero_iff]
  exact ⟨fun h ↦ ⟨f 1, h.symm⟩, fun ⟨c, hc⟩ ↦ by rw [← hc]; rfl⟩

section Complete

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The normalized continuous primitive on the units modulo torsion, obtained by transporting
the Mahler primitive through the logarithmic coordinate. -/
noncomputable def unitsQuotientPrimitive :
    C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) →L[ℤ_[p]]
      C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E) :=
  (pushforwardCoordinate E).comp
    ((mahlerPrimitive E).toContinuousLinearMap.comp (pullbackCoordinate E))

/-- Evaluation of the primitive in the logarithmic coordinate. -/
theorem unitsQuotientPrimitive_apply
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E))
    (x : ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ) :
    unitsQuotientPrimitive E f x =
      mahlerPrimitive E (f.comp
        ⟨fun t ↦ (padicIntUnitsQuotientTorsionEquiv p).symm (ofAdd t),
          (padicIntUnitsQuotientTorsionEquiv p).symm.continuous.comp continuous_ofAdd⟩)
        (padicIntUnitsQuotientTorsionEquiv p x).toAdd := (rfl)

@[simp]
theorem unitsQuotientPrimitive_apply_one
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    unitsQuotientPrimitive E f 1 = 0 := by
  simp [unitsQuotientPrimitive_apply]

/-- The normalized primitive is a continuous linear right inverse of the generator difference. -/
@[simp]
theorem unitsQuotientDiff_primitive
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    unitsQuotientDiff E (unitsQuotientPrimitive E f) = f := by
  apply Function.LeftInverse.injective (pushforward_pullback E)
  simp only [pullbackCoordinate_diff, unitsQuotientPrimitive, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, pullback_pushforward, fwdDiffCLM_mahlerPrimitive]

/-- The generator difference is onto, at every prime, including `2`. -/
theorem unitsQuotientDiff_surjective : Function.Surjective (unitsQuotientDiff (p := p) E) :=
  fun f ↦ ⟨unitsQuotientPrimitive E f, unitsQuotientDiff_primitive E f⟩

/-- A continuous difference equation on the quotient has a unique solution vanishing at the
identity. -/
theorem existsUnique_unitsQuotientDiff_eq
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    ∃! g, unitsQuotientDiff E g = f ∧ g 1 = 0 := by
  refine ⟨unitsQuotientPrimitive E f, ⟨by simp, by simp⟩, fun g hg ↦ ?_⟩
  have h : unitsQuotientDiff E (g - unitsQuotientPrimitive E f) = 0 := by
    simp [hg.1]
  have hc := (unitsQuotientDiff_eq_zero_iff E _).mp h
  simp only [ContinuousMap.sub_apply, hg.2, unitsQuotientPrimitive_apply_one, sub_self,
    ContinuousMap.const_zero] at hc
  exact sub_eq_zero.mp hc

/-- Integration after the generator difference recovers the function modulo its value at the
identity. -/
@[simp]
theorem unitsQuotientPrimitive_diff
    (f : C(ℤ_[p]ˣ ⧸ CommGroup.torsion ℤ_[p]ˣ, E)) :
    unitsQuotientPrimitive E (unitsQuotientDiff E f) = f - ContinuousMap.const _ (f 1) := by
  exact (existsUnique_unitsQuotientDiff_eq E (unitsQuotientDiff E f)).unique
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩

end Complete

end TauCeti
