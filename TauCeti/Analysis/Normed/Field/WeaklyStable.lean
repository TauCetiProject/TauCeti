/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Trace
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.PurelyInseparable
import TauCeti.FieldTheory.Normal.FixedField

/-!
# Weakly stable fields

An ultrametric normed field is weakly stable if every linear functional on each finite
extension is bounded for the spectral norm. This is the bounded-functional formulation of
weak cartesianness.

## Main results

* `TauCeti.IsWeaklyStable.exists_bound_spectralNorm`: the boundedness property of a weakly stable
  field `K` extends to finite extensions of `K` in any universe.
* `RingEquiv.isWeaklyStable_iff_of_norm_eq`: weak stability is invariant under norm-preserving
  ring isomorphisms across universes.
* `TauCeti.isWeaklyStable_iff_isPurelyInseparable`: an ultrametric normed field is weakly stable
  if and only if every linear functional on each finite purely inseparable extension is bounded
  by the spectral norm ([bosch-guntzer-remmert], §3.5.2, Proposition 2).
* `TauCeti.isWeaklyStable_of_perfectField`: every perfect ultrametric normed field is weakly
  stable, even when incomplete.
* `TauCeti.isWeaklyStable_of_completeSpace`: every complete nontrivially normed ultrametric field
  is weakly stable, including in positive characteristic.

## Attribution and references

`IsWeaklyStable`, `isWeaklyStable_of_perfectField`, and `isWeaklyStable_of_completeSpace` adapt
William Coram's definitions and proofs in `PhD/TauCeti/Code/RigidAnalyticGeometry/WeaklyStable.lean`
at commit `eefb3d91f34b27d0bc7822140fa85fecae029884` of <https://github.com/WilliamCoram/PhD>.
The mathematical references are Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*,
§§2.3.1–2.3.2, §3.5.1, Proposition 4, and §3.5.2, Definition 1 and Proposition 2.
-/

public section

namespace TauCeti

universe u v

/-- Every functional on a finite extension is bounded with respect to the spectral norm.
For an ultrametric normed field this is the bounded-functional formulation of **weak stability**. -/
def IsWeaklyStable (K : Type u) [NormedField K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (φ : Module.Dual K L), ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y

/-- Unfolding lemma: `IsWeaklyStable K` says every functional on a finite extension is bounded
by the spectral norm. -/
theorem isWeaklyStable_iff (K : Type u) [NormedField K] :
    IsWeaklyStable K ↔ ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      (φ : Module.Dual K L), ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := Iff.rfl

/-- On a weakly stable field `K`, every `K`-linear functional on a finite extension `L` in any
universe is bounded by the spectral norm. -/
theorem IsWeaklyStable.exists_bound_spectralNorm {K : Type u} [NormedField K]
    (hK : IsWeaklyStable K) {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    (φ : Module.Dual K L) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by
  have : Small.{u} L := Module.Finite.small K L
  let e : Shrink.{u} L ≃ₐ[K] L := Shrink.algEquiv K L
  obtain ⟨C, hC⟩ := hK (Shrink.{u} L) (φ.comp e.toLinearMap)
  refine ⟨C, fun y ↦ ?_⟩
  have hφ : (φ.comp e.toLinearMap) (e.symm y) = φ y := by
    rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e.apply_symm_apply]
  have hspec : spectralNorm K (Shrink.{u} L) (e.symm y) = spectralNorm K L y := by
    rw [← AlgEquiv.coe_toAlgHom, e.symm.toAlgHom.spectralNorm_map]
  rw [← hφ, ← hspec]
  exact hC (e.symm y)

/-- **Purely inseparable criterion for weak stability.** An ultrametric normed field `K` is weakly
stable as soon as every `K`-linear functional on each finite purely inseparable extension of `K` is
bounded by the spectral norm ([bosch-guntzer-remmert], §3.5.2, Proposition 2). -/
theorem IsWeaklyStable.of_isPurelyInseparable {K : Type u} [NormedField K] [IsUltrametricDist K]
    (h : ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M] [IsPurelyInseparable K M]
      (ψ : Module.Dual K M), ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C * spectralNorm K M x) :
    IsWeaklyStable K := by
  intro L _ _ _ φ
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let M := IntermediateField.fixedField (⊤ : Subgroup (N ≃ₐ[K] N))
  have : IsPurelyInseparable K M := IntermediateField.isPurelyInseparable_fixedField_top K N
  have : IsGalois M N := IsGalois.of_fixed_field N (⊤ : Subgroup (N ≃ₐ[K] N))
  exact φ.exists_bound_spectralNorm_of_tower N fun ψ ↦
    ψ.exists_bound_spectralNorm_of_isPurelyInseparable_of_isSeparable (h M)

/-- An ultrametric normed field `K` is weakly stable if and only if every `K`-linear functional on
each finite purely inseparable extension of `K` is bounded by the spectral norm. -/
theorem isWeaklyStable_iff_isPurelyInseparable (K : Type u) [NormedField K] [IsUltrametricDist K] :
    IsWeaklyStable K ↔
      ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M] [IsPurelyInseparable K M]
        (ψ : Module.Dual K M), ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C * spectralNorm K M x :=
  ⟨fun h M _ _ _ _ ψ ↦ h M ψ, IsWeaklyStable.of_isPurelyInseparable⟩

/-- Every perfect ultrametric normed field is weakly stable, even when incomplete. -/
theorem isWeaklyStable_of_perfectField (K : Type u) [NormedField K] [IsUltrametricDist K]
    [PerfectField K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact φ.exists_bound_spectralNorm_of_isSeparable

/-- Every complete nontrivially normed ultrametric field is weakly stable, including in
positive characteristic. No separability hypothesis is imposed on finite extensions. -/
theorem isWeaklyStable_of_completeSpace (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  let := spectralNorm.normedField K L
  let := spectralNorm.normedAlgebra K L
  refine ⟨‖LinearMap.toContinuousLinearMap φ‖, fun y ↦ ?_⟩
  rw [← NormedAlgebra.norm_eq_spectralNorm K y]
  exact (LinearMap.toContinuousLinearMap φ).le_opNorm y

end TauCeti

namespace RingEquiv

private theorem isWeaklyStable_of_norm_eq {K : Type*} {K' : Type*} [NormedField K] [NormedField K']
    (e : K ≃+* K') (he : ∀ a, ‖e a‖ = ‖a‖) (hK : TauCeti.IsWeaklyStable K) :
    TauCeti.IsWeaklyStable K' := by
  intro L' _ _ _ φ'
  let _ : Algebra K K' := e.toRingHom.toAlgebra
  have : Module.Finite K K' := RingHom.Finite.of_surjective _ e.surjective
  let _ : Algebra K L' := ((algebraMap K' L').comp e.toRingHom).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq' <| by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  have : FiniteDimensional K L' := Module.Finite.trans K' L'
  have heAlg (x : K) : e (algebraMap K K x) = algebraMap K K' x := by
    simp [RingHom.algebraMap_toAlgebra]
  let eAlg : K ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := e) heAlg
  let φ : Module.Dual K L' := eAlg.symm.toLinearMap.comp (φ'.restrictScalars K)
  obtain ⟨C, hC⟩ := hK.exists_bound_spectralNorm φ
  refine ⟨C, fun y ↦ ?_⟩
  have hnorm : ‖φ y‖ = ‖φ' y‖ := by
    dsimp only [φ, eAlg]
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
      AlgEquiv.ofRingEquiv_symm_apply, ← he (e.symm (φ' y)), e.apply_symm_apply]
  have hcomp : (algebraMap K' L').comp e.toRingHom =
      (RingEquiv.refl L').toRingHom.comp (algebraMap K L') := by
    simp [RingHom.algebraMap_toAlgebra]
  have hspec : spectralNorm K' L' y = spectralNorm K L' y :=
    e.spectralNorm_eq_of_norm_eq he (RingEquiv.refl L') hcomp y
  rw [← hnorm, hspec]
  exact hC y

/-- Weak stability is invariant under norm-preserving ring isomorphisms across universes. -/
theorem isWeaklyStable_iff_of_norm_eq {K : Type*} {K' : Type*} [NormedField K] [NormedField K']
    (e : K ≃+* K') (he : ∀ a, ‖e a‖ = ‖a‖) :
    TauCeti.IsWeaklyStable K ↔ TauCeti.IsWeaklyStable K' :=
  ⟨e.isWeaklyStable_of_norm_eq he, e.symm.isWeaklyStable_of_norm_eq fun b ↦ by
    rw [← he (e.symm b), e.apply_symm_apply]⟩

end RingEquiv
