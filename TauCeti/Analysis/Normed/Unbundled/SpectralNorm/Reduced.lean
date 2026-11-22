/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import TauCeti.Analysis.Normed.Field.WeaklyStable

import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Artinian.Module
import TauCeti.Analysis.Normed.Unbundled.CoordinateNorm
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# Spectral norms on finite reduced algebras

Let `K` be an ultrametric normed field and `E` a finite reduced commutative `K`-algebra. Because `E`
is Artinian and reduced, `IsArtinianRing.equivPi` decomposes `E` into the finite product of its
residue fields `E ⧸ m` over `m : MaximalSpectrum E`, each of which is a finite field extension of
`K`.

This file shows that for every `x : E`, the spectral value `spectralValue (minpoly K x)` equals the
supremum over `m : MaximalSpectrum E` of `spectralNorm K (E ⧸ m.asIdeal)` on the residue of `x`, and
bundles `x ↦ spectralValue (minpoly K x)` into a power-multiplicative nonarchimedean `K`-algebra
norm `TauCeti.reducedSpectralAlgNorm K E`. Over a weakly stable field `K`, every `K`-linear
functional on `E` is bounded by `reducedSpectralAlgNorm K E`, and `reducedSpectralAlgNorm K E` is
equivalent to every finite-basis coordinate norm `b.norm`.

No completeness or nontriviality of the valuation on `K` is assumed. This supplies the
fraction-field tensor-product algebra norm in Bosch–Güntzer–Remmert, §3.8.3, Theorem 7, without
restricting `E` to be a field.

## Main definitions

* `TauCeti.reducedSpectralAlgNorm K E`: the `K`-algebra norm `x ↦ spectralValue (minpoly K x)` on a
  finite reduced commutative `K`-algebra `E`.

## Main results

* `TauCeti.spectralValue_minpoly_eq_iSup_spectralNorm`: `spectralValue (minpoly K x)` is the
  supremum of the residue-field spectral norms across `MaximalSpectrum E`.
* `TauCeti.isPowMul_reducedSpectralAlgNorm` and `TauCeti.isNonarchimedean_reducedSpectralAlgNorm`:
  power-multiplicativity and ultrametricity of `reducedSpectralAlgNorm K E`.
* `TauCeti.IsWeaklyStable.exists_bound_reducedSpectralAlgNorm` and
  `TauCeti.IsWeaklyStable.exists_basis_reducedSpectralAlgNorm_comparison`: over a weakly stable
  field `K`, linear functionals and basis coordinate norms on `E` are controlled by
  `reducedSpectralAlgNorm K E`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.1.2, 3.2.1, 3.5.1, and 3.8.3.
-/

public section

open Polynomial

namespace TauCeti

section ReducedAlgebra

variable {K E : Type*} [NormedField K] [CommRing E] [Algebra K E]

private noncomputable local instance instFieldQuotient (m : MaximalSpectrum E) :
    Field (E ⧸ m.asIdeal) :=
  Ideal.Quotient.field m.asIdeal

private theorem iSup_quotient_spectralNorm_nonneg (x : E) :
    0 ≤ ⨆ m : MaximalSpectrum E, spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) :=
  Real.iSup_nonneg fun _ ↦ spectralNorm_nonneg _

private theorem spectralNorm_quotient_le_iSup [Finite (MaximalSpectrum E)] (x : E)
    (m : MaximalSpectrum E) :
    spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) ≤
      ⨆ n : MaximalSpectrum E,
        spectralNorm K (E ⧸ n.asIdeal) (Ideal.Quotient.mk n.asIdeal x) :=
  le_ciSup (f := fun n : MaximalSpectrum E ↦
    spectralNorm K (E ⧸ n.asIdeal) (Ideal.Quotient.mk n.asIdeal x))
    (Set.finite_range _).bddAbove m

variable [IsUltrametricDist K] [IsReduced E] [Module.Finite K E]

/-- **Residue-field formula for the spectral value of a minimal polynomial.** In a finite reduced
commutative `K`-algebra `E` over an ultrametric normed field `K`, `spectralValue (minpoly K x)` is
the supremum over `m : MaximalSpectrum E` of the spectral norm of `x mod m` in `E ⧸ m`. -/
theorem spectralValue_minpoly_eq_iSup_spectralNorm (x : E) :
    spectralValue (minpoly K x) =
      ⨆ m : MaximalSpectrum E,
        letI := Ideal.Quotient.field m.asIdeal
        spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) := by
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  let _ : Fintype (MaximalSpectrum E) := Fintype.ofFinite (MaximalSpectrum E)
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hxm (m : MaximalSpectrum E) : IsIntegral K (Ideal.Quotient.mk m.asIdeal x) :=
    hx.map (Ideal.Quotient.mkₐ K m.asIdeal)
  refine le_antisymm ?_ ?_
  · let Q : K[X] := ∏ m : MaximalSpectrum E, minpoly K (Ideal.Quotient.mk m.asIdeal x)
    have hQ_monic : Q.Monic := monic_prod_of_monic _ _ fun m _ ↦ minpoly.monic (hxm m)
    have hQ_aeval : aeval x Q = 0 := by
      apply (IsArtinianRing.equivPi E).injective
      ext m
      rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply,
        ← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, ← aeval_algHom_apply]
      obtain ⟨R, hR⟩ := Finset.dvd_prod_of_mem
        (fun n : MaximalSpectrum E ↦ minpoly K (Ideal.Quotient.mk n.asIdeal x))
        (Finset.mem_univ m)
      dsimp only [Q]
      rw [hR, map_mul, Ideal.Quotient.mkₐ_eq_mk, minpoly.aeval, zero_mul]
    exact ((minpoly.monic hx).spectralValue_le_of_dvd hQ_monic (minpoly.dvd K x hQ_aeval)).trans
      (Monic.spectralValue_prod_le (fun m _ ↦ minpoly.monic (hxm m))
        (iSup_quotient_spectralNorm_nonneg x) fun m _ ↦
        spectralNorm_quotient_le_iSup x m)
  · rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · rw [Real.iSup_of_isEmpty]
      exact spectralValue_nonneg _
    · refine ciSup_le fun m ↦ ?_
      have hdvd : minpoly K (Ideal.Quotient.mk m.asIdeal x) ∣ minpoly K x := by
        refine minpoly.dvd K _ ?_
        rw [← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, aeval_algHom_apply, minpoly.aeval, map_zero]
      exact (minpoly.monic (hxm m)).spectralValue_le_of_dvd (minpoly.monic hx) hdvd

variable (K E) in
/-- **The spectral algebra norm on a finite reduced `K`-algebra.** Sends `x : E` to
`spectralValue (minpoly K x)`, equivalently the supremum of `spectralNorm K (E ⧸ m)` across
`m : MaximalSpectrum E`. -/
noncomputable def reducedSpectralAlgNorm : AlgebraNorm K E where
  toFun x := spectralValue (minpoly K x)
  map_zero' := by
    rw [spectralValue_minpoly_eq_iSup_spectralNorm]
    simp_rw [map_zero, spectralNorm_zero]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · exact Real.iSup_of_isEmpty _
    · exact ciSup_const
  add_le' x y := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm,
      spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, add_zero, le_rfl]
    · refine ciSup_le fun m ↦ ?_
      rw [map_add]
      exact (isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg).trans
        (add_le_add (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m))
  neg' x := by
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm]
    congr 1 with m
    rw [map_neg, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
  mul_le' x y := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm,
      spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, mul_zero, le_rfl]
    · refine ciSup_le fun m ↦ ?_
      rw [map_mul]
      exact (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _)
        (Algebra.IsAlgebraic.isAlgebraic _)).trans
        (mul_le_mul (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m)
          (spectralNorm_nonneg _) (iSup_quotient_spectralNorm_nonneg x))
  smul' k x := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, mul_zero]
    · rw [Real.mul_iSup_of_nonneg (norm_nonneg k)]
      congr 1 with m
      rw [← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, map_smul, Ideal.Quotient.mkₐ_eq_mk,
        spectralNorm_smul k (Algebra.IsAlgebraic.isAlgebraic _), coe_nnNorm]
  eq_zero_of_map_eq_zero' x hx := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm] at hx
    apply (IsArtinianRing.equivPi E).injective
    ext m
    rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply]
    have hm0 : spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) = 0 :=
      le_antisymm ((spectralNorm_quotient_le_iSup x m).trans hx.le) (spectralNorm_nonneg _)
    exact eq_zero_of_map_spectralNorm_eq_zero hm0 (Algebra.IsAlgebraic.isAlgebraic _)

/-- `reducedSpectralAlgNorm K E x` is defined as `spectralValue (minpoly K x)`. -/
theorem reducedSpectralAlgNorm_def (x : E) :
    reducedSpectralAlgNorm K E x = spectralValue (minpoly K x) := (rfl)

/-- `reducedSpectralAlgNorm K E x` is the supremum of the residue-field spectral norms across
`MaximalSpectrum E`. -/
theorem reducedSpectralAlgNorm_eq_iSup_spectralNorm (x : E) :
    reducedSpectralAlgNorm K E x =
      ⨆ m : MaximalSpectrum E,
        letI := Ideal.Quotient.field m.asIdeal
        spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) :=
  spectralValue_minpoly_eq_iSup_spectralNorm x

/-- `reducedSpectralAlgNorm K E` is nonarchimedean. -/
theorem isNonarchimedean_reducedSpectralAlgNorm :
    IsNonarchimedean (reducedSpectralAlgNorm K E) := by
  intro x y
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  simp only [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
  · simp only [Real.iSup_of_isEmpty, max_self, le_rfl]
  · refine ciSup_le fun m ↦ ?_
    rw [map_add]
    exact (isNonarchimedean_spectralNorm _ _).trans
      (max_le_max (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m))

/-- `reducedSpectralAlgNorm K E` is power-multiplicative. -/
theorem isPowMul_reducedSpectralAlgNorm :
    IsPowMul (reducedSpectralAlgNorm K E) := by
  intro x n hn
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  simp only [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
  · rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  · refine le_antisymm (ciSup_le fun m ↦ ?_) ?_
    · rw [map_pow, isPowMul_spectralNorm _ hn]
      exact pow_le_pow_left₀ (spectralNorm_nonneg _) (spectralNorm_quotient_le_iSup x m) n
    · obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite
        (f := fun m : MaximalSpectrum E ↦
          spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x))
      rw [← hm, ← isPowMul_spectralNorm _ hn, ← map_pow]
      exact spectralNorm_quotient_le_iSup (x ^ n) m

/-- On a nontrivial finite reduced `K`-algebra, `reducedSpectralAlgNorm K E` extends the norm on
`K`. -/
@[simp]
theorem reducedSpectralAlgNorm_algebraMap [Nontrivial E] (k : K) :
    reducedSpectralAlgNorm K E (algebraMap K E k) = ‖k‖ := by
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  obtain ⟨M, hM⟩ := Ideal.exists_maximal E
  have : Nonempty (MaximalSpectrum E) := ⟨⟨M, hM⟩⟩
  rw [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  simp_rw [Ideal.Quotient.mk_algebraMap, spectralNorm_extends]
  exact ciSup_const

/-- On a nontrivial finite reduced `K`-algebra, `reducedSpectralAlgNorm K E 1 = 1`. -/
@[simp]
theorem reducedSpectralAlgNorm_one [Nontrivial E] :
    reducedSpectralAlgNorm K E 1 = 1 := by
  simpa using reducedSpectralAlgNorm_algebraMap (K := K) (E := E) 1

/-- On a finite field extension `L / K`, `reducedSpectralAlgNorm K L` coincides with
`spectralAlgNorm K L`. -/
@[simp]
theorem reducedSpectralAlgNorm_eq_spectralAlgNorm (K L : Type*) [NormedField K]
    [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    reducedSpectralAlgNorm K L = spectralAlgNorm K L := by
  ext x
  rw [reducedSpectralAlgNorm_def, spectralAlgNorm_def, spectralNorm]

end ReducedAlgebra

end TauCeti

section Morphisms

variable {K E E' : Type*} [NormedField K] [IsUltrametricDist K]
  [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
  [CommRing E'] [IsReduced E'] [Algebra K E'] [Module.Finite K E']

/-- Any `K`-algebra homomorphism between finite reduced `K`-algebras is contractive for
`TauCeti.reducedSpectralAlgNorm`. -/
theorem AlgHom.reducedSpectralAlgNorm_map_le (φ : E →ₐ[K] E') (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (φ x) ≤ TauCeti.reducedSpectralAlgNorm K E x := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hφx : IsIntegral K (φ x) := Algebra.IsIntegral.isIntegral (φ x)
  refine (minpoly.monic hφx).spectralValue_le_of_dvd (minpoly.monic hx) (minpoly.dvd K (φ x) ?_)
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

/-- An injective `K`-algebra homomorphism between finite reduced `K`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
theorem AlgHom.reducedSpectralAlgNorm_map_of_injective (φ : E →ₐ[K] E')
    (hφ : Function.Injective φ) (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (φ x) = TauCeti.reducedSpectralAlgNorm K E x := by
  rw [TauCeti.reducedSpectralAlgNorm_def, TauCeti.reducedSpectralAlgNorm_def,
    minpoly.algHom_eq φ hφ]

/-- A `K`-algebra isomorphism between finite reduced `K`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
@[simp]
theorem AlgEquiv.reducedSpectralAlgNorm_map (e : E ≃ₐ[K] E') (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (e x) = TauCeti.reducedSpectralAlgNorm K E x :=
  e.toAlgHom.reducedSpectralAlgNorm_map_of_injective e.injective x

end Morphisms

namespace TauCeti.IsWeaklyStable

universe u v

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- **Spectral boundedness of linear functionals on finite reduced algebras.** Over a weakly stable
ultrametric normed field `K`, every `K`-linear functional on a finite reduced commutative
`K`-algebra `E` (in any universe) is bounded by `reducedSpectralAlgNorm K E`. -/
theorem exists_bound_reducedSpectralAlgNorm (hK : IsWeaklyStable K)
    {E : Type v} [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
    (φ : Module.Dual K E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖φ x‖ ≤ C * reducedSpectralAlgNorm K E x := by
  classical
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  let _ : Fintype (MaximalSpectrum E) := Fintype.ofFinite (MaximalSpectrum E)
  let _ (m : MaximalSpectrum E) : Field (E ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let e : E ≃ₐ[K] ∀ m : MaximalSpectrum E, E ⧸ m.asIdeal :=
    (IsArtinianRing.equivPi E).restrictScalars K
  let ψ (m : MaximalSpectrum E) : Module.Dual K (E ⧸ m.asIdeal) :=
    (φ.comp e.symm.toLinearMap).comp (LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m)
  choose C hC using fun m ↦ hK.exists_bound_spectralNorm (ψ m)
  refine ⟨1 + ∑ m : MaximalSpectrum E, |C m|, by positivity, fun x ↦ ?_⟩
  have hx : φ x = ∑ m : MaximalSpectrum E, ψ m (e x m) := by
    have hsum : ∑ m : MaximalSpectrum E,
        LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m (e x m) = e x := by
      simp_rw [LinearMap.single_apply]
      exact Finset.univ_sum_single (e x)
    calc
      φ x = (φ.comp e.symm.toLinearMap) (e x) := by
        rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e.symm_apply_apply]
      _ = (φ.comp e.symm.toLinearMap)
            (∑ m : MaximalSpectrum E, LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m (e x m)) := by
        rw [hsum]
      _ = ∑ m : MaximalSpectrum E, ψ m (e x m) := map_sum _ _ _
  calc
    ‖φ x‖ = ‖∑ m : MaximalSpectrum E, ψ m (e x m)‖ := by rw [hx]
    _ ≤ ∑ m : MaximalSpectrum E, ‖ψ m (e x m)‖ := norm_sum_le _ _
    _ ≤ ∑ m : MaximalSpectrum E, |C m| * spectralNorm K (E ⧸ m.asIdeal) (e x m) := by
      refine Finset.sum_le_sum fun m _ ↦ (hC m (e x m)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self (C m)) (spectralNorm_nonneg _)
    _ ≤ ∑ m : MaximalSpectrum E, |C m| * reducedSpectralAlgNorm K E x := by
      refine Finset.sum_le_sum fun m _ ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
      dsimp only [e]
      rw [AlgEquiv.coe_restrictScalars, IsArtinianRing.equivPi_apply]
      exact spectralNorm_quotient_le_iSup x m
    _ = (∑ m : MaximalSpectrum E, |C m|) * reducedSpectralAlgNorm K E x := by
      rw [← Finset.sum_mul]
    _ ≤ (1 + ∑ m : MaximalSpectrum E, |C m|) * reducedSpectralAlgNorm K E x :=
      mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)

/-- **Equivalence of basis coordinate norms and `reducedSpectralAlgNorm`.** On every finite reduced
algebra over a weakly stable ultrametric field `K`, `reducedSpectralAlgNorm K E` is equivalent to
the coordinate norm of any finite `K`-basis. -/
theorem exists_basis_reducedSpectralAlgNorm_comparison (hK : IsWeaklyStable K)
    {E : Type v} [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (b : Module.Basis ι K E) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x : E,
      b.norm x ≤ C * reducedSpectralAlgNorm K E x ∧
        reducedSpectralAlgNorm K E x ≤ D * b.norm x :=
  b.exists_norm_comparison_of_forall_exists_bound (reducedSpectralAlgNorm K E) fun φ ↦
    let ⟨C, _, hC⟩ := hK.exists_bound_reducedSpectralAlgNorm φ
    ⟨C, hC⟩

end TauCeti.IsWeaklyStable
