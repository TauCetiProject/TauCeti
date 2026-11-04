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
import Mathlib.LinearAlgebra.Dimension.Free
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

namespace RingEquiv

/-- Compatible ring isomorphisms whose base map is norm-preserving preserve `spectralNorm`. -/
theorem spectralNorm_eq_of_norm_eq {K K' L L' : Type*}
    [NormedField K] [NormedField K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (e : K ≃+* K') (he : ∀ a, ‖e a‖ = ‖a‖) (g : L ≃+* L')
    (hcomp : (algebraMap K' L').comp e.toRingHom = g.toRingHom.comp (algebraMap K L)) (x : L) :
    spectralNorm K' L' (g x) = spectralNorm K L x := by
  by_cases hx : IsIntegral K x
  · have hmin : Polynomial.map (e : K →+* K') (minpoly K x) = minpoly K' (g x) :=
      minpoly.eq_of_irreducible_of_monic
        (by rw [← Polynomial.mapEquiv_apply, MulEquiv.irreducible_iff]
            exact minpoly.irreducible hx)
        (by simpa using (Polynomial.map_aeval_eq_aeval_map hcomp (minpoly K x) x).symm)
        ((minpoly.monic hx).map _)
    rw [spectralNorm, ← hmin, TauCeti.spectralValue_map_of_norm_eq (e : K →+* K') he,
      ← spectralNorm]
  · have hgx : ¬ IsIntegral K' (g x) := by
      rintro ⟨P, hPm, hP0⟩
      refine hx ⟨P.map (e.symm : K' →+* K), hPm.map _, ?_⟩
      have hcomp' : (algebraMap K L).comp e.symm.toRingHom =
          g.symm.toRingHom.comp (algebraMap K' L') := by
        ext b
        apply g.injective
        simpa [RingHom.comp_apply] using (RingHom.congr_fun hcomp (e.symm b)).symm
      rw [← Polynomial.aeval_def] at hP0 ⊢
      simpa [hP0] using (Polynomial.map_aeval_eq_aeval_map hcomp' P (g x)).symm
    rw [spectralNorm, spectralNorm, minpoly.eq_zero hx, minpoly.eq_zero hgx,
      ← Polynomial.map_zero (e : K →+* K'), TauCeti.spectralValue_map_of_norm_eq (e : K →+* K') he]

end RingEquiv

namespace Module.Dual

/-- In a tower of fields `K → L → N`, if every `K`-linear functional on `N` is bounded by
`spectralNorm K N`, then every `K`-linear functional on `L` is bounded by `spectralNorm K L`. -/
theorem exists_bound_spectralNorm_of_tower {K L : Type*} (N : Type*)
    [NormedField K] [Field L] [Algebra K L] [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N]
    (hN : ∀ ψ : Module.Dual K N, ∃ C : ℝ, ∀ z, ‖ψ z‖ ≤ C * spectralNorm K N z)
    (φ : Module.Dual K L) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by
  let ι : L →ₗ[K] N := (IsScalarTower.toAlgHom K L N).toLinearMap
  have hker : LinearMap.ker ι = ⊥ := LinearMap.ker_eq_bot.mpr (algebraMap L N).injective
  obtain ⟨π, hπ⟩ := ι.exists_leftInverse_of_injective hker
  obtain ⟨C, hC⟩ := hN (φ.comp π)
  refine ⟨C, fun y ↦ ?_⟩
  have hy : (φ.comp π) (algebraMap L N y) = φ y :=
    congrArg φ (LinearMap.congr_fun hπ y)
  rw [spectralNorm.eq_of_tower (L := N) y, ← hy]
  exact hC (algebraMap L N y)

/-- In a tower `K → M → N` over an ultrametric normed field `K` with `M / K` purely inseparable
and `N / M` finite separable, if every `K`-linear functional on `M` is bounded by
`spectralNorm K M`, then every `K`-linear functional on `N` is bounded by `spectralNorm K N`. -/
theorem exists_bound_spectralNorm_of_isPurelyInseparable_of_isSeparable {K M N : Type*}
    [NormedField K] [IsUltrametricDist K]
    [Field M] [Algebra K M] [IsPurelyInseparable K M]
    [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [FiniteDimensional M N] [Algebra.IsSeparable M N]
    (hM : ∀ ψ : Module.Dual K M, ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C * spectralNorm K M x)
    (φ : Module.Dual K N) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K N y := by
  let M' := WithAbs (TauCeti.spectralAbsoluteValue K M)
  let b := Module.finBasis M' N
  choose C₁ hC₁ using fun i ↦ Module.Dual.exists_bound_spectralNorm_of_isSeparable (b.coord i)
  let ψ (i : Fin (Module.finrank M' N)) : Module.Dual K M :=
    { toFun := fun x ↦ φ (x • b i)
      map_add' := fun x y ↦ by rw [add_smul, map_add]
      map_smul' := fun c x ↦ by rw [smul_assoc, map_smul, RingHom.id_apply] }
  choose C₂ hC₂ using fun i ↦ hM (ψ i)
  let D₂ (i : Fin (Module.finrank M' N)) : ℝ := max (C₂ i) 0
  refine ⟨∑ i, D₂ i * C₁ i, fun y ↦ ?_⟩
  have hy : φ y = ∑ i, ψ i (b.repr y i).ofAbs := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rfl
  calc ‖φ y‖ = ‖∑ i, ψ i (b.repr y i).ofAbs‖ := by rw [hy]
    _ ≤ ∑ i, ‖ψ i (b.repr y i).ofAbs‖ := norm_sum_le _ _
    _ ≤ ∑ i, D₂ i * spectralNorm K M (b.repr y i).ofAbs :=
        Finset.sum_le_sum fun i _ ↦ (hC₂ i _).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (spectralNorm_nonneg _))
    _ = ∑ i, D₂ i * ‖b.coord i y‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Module.Basis.coord_apply, WithAbs.norm_eq_apply_ofAbs,
          TauCeti.spectralAbsoluteValue_apply]
    _ ≤ ∑ i, D₂ i * (C₁ i * spectralNorm M' N y) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hC₁ i y) (le_max_right _ _)
    _ = (∑ i, D₂ i * C₁ i) * spectralNorm K N y := by
        rw [TauCeti.spectralNorm_withAbs_spectralAbsoluteValue (K := K) (M := M) y,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm

end Module.Dual

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
  simpa only [AlgEquiv.apply_symm_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    spectralNorm, minpoly.algEquiv_eq] using hC (e.symm y)

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
  have : IsScalarTower K K' L' := .of_algebraMap_eq' rfl
  have : FiniteDimensional K L' := Module.Finite.trans K' L'
  let φ : Module.Dual K L' :=
    { toFun := fun y ↦ e.symm (φ' y)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun a y ↦ by
        rw [← IsScalarTower.algebraMap_smul K', map_smul, RingHom.id_apply]
        change e.symm (e a * φ' y) = a * e.symm (φ' y)
        rw [map_mul, e.symm_apply_apply] }
  obtain ⟨C, hC⟩ := hK.exists_bound_spectralNorm φ
  refine ⟨C, fun y ↦ ?_⟩
  have hnorm : ‖φ y‖ = ‖φ' y‖ := by
    change ‖e.symm (φ' y)‖ = ‖φ' y‖
    rw [← he (e.symm (φ' y)), e.apply_symm_apply]
  have hspec : spectralNorm K' L' y = spectralNorm K L' y :=
    e.spectralNorm_eq_of_norm_eq he (RingEquiv.refl L') rfl y
  rw [← hnorm, hspec]
  exact hC y

/-- Weak stability is invariant under norm-preserving ring isomorphisms across universes. -/
theorem isWeaklyStable_iff_of_norm_eq {K : Type*} {K' : Type*} [NormedField K] [NormedField K']
    (e : K ≃+* K') (he : ∀ a, ‖e a‖ = ‖a‖) :
    TauCeti.IsWeaklyStable K ↔ TauCeti.IsWeaklyStable K' :=
  ⟨e.isWeaklyStable_of_norm_eq he, e.symm.isWeaklyStable_of_norm_eq fun b ↦ by
    rw [← he (e.symm b), e.apply_symm_apply]⟩

end RingEquiv
