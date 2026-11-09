/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MaximumModulus
public import TauCeti.RingTheory.Dagger.MaximalSpectrum

/-!
# The supremum seminorm of Monsky–Washnitzer and dagger algebras

Let `K` be a complete nontrivially normed ultrametric field. The supremum seminorm
`|f|sup = sup_x |f(x)|` of an element `f` of a `K`-algebra is the supremum of its absolute values
at the classical points (`TauCeti.supSeminorm`). This file computes it on the Monsky–Washnitzer
algebra `W = K⟨X₁, …, Xₙ⟩†` and bounds it on every dagger algebra, a quotient of some `W`.

On `W` the supremum seminorm is the Gauss norm, and it is attained at a classical point. The
classical points of `W` are those of the Tate algebra `T = K⟨X₁, …, Xₙ⟩`, with the same residue
fields (`TauCeti.Dagger.washnitzerAlgebra.maximalSpectrumComap_toTate_bijective`), so this is the
maximum modulus principle for `T` (`TauCeti.MvPowerSeries.supSeminorm_eq_norm`) read through the
isometric inclusion `W ⊆ T`. Since the power-bounded elements of `W` are its Gauss unit ball
(`TauCeti.Dagger.washnitzerAlgebra.isPowerBounded_iff_norm_le_one`), an overconvergent series is
power-bounded exactly when its supremum seminorm is at most one.

For a surjection `φ : W ↠ A`, every classical point of `A` pulls back to one of `W` with the same
values, so `|φ f|sup ≤ ‖f‖`: the supremum seminorm of a dagger algebra is bounded by the residue
seminorm of every presentation. In particular its values at classical points are bounded, and
`1 - a` is a unit whenever `|a|sup < 1`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.supSeminorm_eq_norm`: on `W` the supremum seminorm is the
  Gauss norm, which is attained at a classical point
  (`TauCeti.Dagger.washnitzerAlgebra.exists_pointNorm_eq_norm`).
* `TauCeti.Dagger.washnitzerAlgebra.isPowerBounded_iff_supSeminorm_le_one`: the power-bounded
  elements of `W` are the elements with `|f|sup ≤ 1`.
* `TauCeti.Dagger.washnitzerAlgebra.supSeminorm_map_le_norm`: `|φ f|sup ≤ ‖f‖` for every
  surjection `φ : W ↠ A`.
* `TauCeti.Dagger.IsDaggerAlgebra.pointNorm_le_supSeminorm`: on a dagger algebra the supremum
  seminorm bounds the value at every classical point.
* `TauCeti.Dagger.IsDaggerAlgebra.isUnit_one_sub_of_supSeminorm_lt_one`: in a dagger algebra,
  `1 - a` is a unit whenever `|a|sup < 1`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and §1.9.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4 and
  §6.2.3 (the same statements for Tate and affinoid algebras).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "W " σ:max => washnitzerAlgebra σ K
local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

namespace washnitzerAlgebra

variable [CompleteSpace K] [Finite σ]

/-- The absolute value of an overconvergent series at a classical point is at most its Gauss
norm. -/
theorem pointNorm_le_norm (x : MaximalSpectrum (W σ)) (f : W σ) : pointNorm K x f ≤ ‖f‖ := by
  obtain ⟨y, rfl⟩ := (maximalSpectrumComap_toTate_bijective (σ := σ) (K := K)).surjective x
  rw [IsAffinoidAlgebra.pointNorm_maximalSpectrumComap, ← norm_toTate]
  exact isAffinoidAlgebra_tate.pointNorm_le_norm y _

/-- **Maximum modulus principle for overconvergent series.** Every `f ∈ K⟨X₁, …, Xₙ⟩†` attains
its Gauss norm at a classical point: `|f(x)| = ‖f‖` for some maximal ideal `x`. -/
theorem exists_pointNorm_eq_norm (f : W σ) :
    ∃ x : MaximalSpectrum (W σ), pointNorm K x f = ‖f‖ := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  -- Reindex the variables by `Fin n`, where the maximum modulus principle for `T` is stated.
  let e' : T σ ≃ₐ[K] T (Fin n) := IsRestricted.renameAlgEquiv e fun _ ↦ 1
  have he' (g : T σ) : ‖e' g‖ = ‖g‖ := IsRestricted.norm_renameAlgEquiv e (fun _ ↦ 1) g
  let ψ : W σ →ₐ[K] T (Fin n) := e'.toAlgHom.comp (toTate σ K)
  obtain ⟨y, hy⟩ := TauCeti.MvPowerSeries.exists_pointNorm_eq_norm (ψ f)
  refine ⟨isAffinoidAlgebra_tate.maximalSpectrumComap ψ y, ?_⟩
  rw [IsAffinoidAlgebra.pointNorm_maximalSpectrumComap, hy]
  exact (he' _).trans (norm_toTate f)

/-- **On the Monsky–Washnitzer algebra the supremum seminorm is the Gauss norm**:
`|f|sup = ‖f‖`. -/
@[simp]
theorem supSeminorm_eq_norm (f : W σ) : supSeminorm K f = ‖f‖ := by
  obtain ⟨x, hx⟩ := exists_pointNorm_eq_norm f
  refine le_antisymm (supSeminorm_le (norm_nonneg f) fun y ↦ pointNorm_le_norm y f) ?_
  rw [← hx]
  exact pointNorm_le_supSeminorm_of_bddAbove
    ⟨‖f‖, Set.forall_mem_range.mpr fun y ↦ pointNorm_le_norm y f⟩ x

/-- An overconvergent series is power-bounded iff its supremum seminorm is at most one. -/
theorem isPowerBounded_iff_supSeminorm_le_one {f : W σ} :
    Huber.IsPowerBounded f ↔ supSeminorm K f ≤ 1 := by
  rw [supSeminorm_eq_norm, isPowerBounded_iff_norm_le_one]

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The absolute value of `φ f` at a classical point of `A` is at most the Gauss norm of `f`, for
a surjection `φ : W ↠ A`. -/
theorem pointNorm_map_le_norm {φ : W σ →ₐ[K] A} (hφ : Function.Surjective φ)
    (x : MaximalSpectrum A) (f : W σ) : pointNorm K x (φ f) ≤ ‖f‖ := by
  -- The pullback of `x` is a classical point of `W` at which `f` has the same absolute value.
  have hx : (x.asIdeal.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  rw [← pointNorm_comap φ x hx]
  exact pointNorm_le_norm _ f

/-- **The supremum seminorm is bounded by residue norms.** For a surjection `φ : W ↠ A`,
`|φ f|sup ≤ ‖f‖`; so on a dagger algebra `|a|sup` is at most the residue seminorm
`inf {‖f‖ : φ f = a}` of every presentation. -/
theorem supSeminorm_map_le_norm {φ : W σ →ₐ[K] A} (hφ : Function.Surjective φ) (f : W σ) :
    supSeminorm K (φ f) ≤ ‖f‖ :=
  supSeminorm_le (norm_nonneg f) fun x ↦ pointNorm_map_le_norm hφ x f

end washnitzerAlgebra

namespace IsDaggerAlgebra

variable [CompleteSpace K] {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The absolute values of an element of a dagger algebra at its classical points are bounded. -/
theorem bddAbove_range_pointNorm (a : A) :
    BddAbove (Set.range fun x : MaximalSpectrum A ↦ pointNorm K x a) := by
  obtain ⟨n, φ, hφ⟩ := exists_surjective (K := K) (A := A)
  obtain ⟨f, rfl⟩ := hφ a
  exact ⟨‖f‖, Set.forall_mem_range.mpr fun x ↦ washnitzerAlgebra.pointNorm_map_le_norm hφ x f⟩

/-- On a dagger algebra the supremum seminorm bounds the absolute value at every classical
point: `|a(x)| ≤ |a|sup`. -/
theorem pointNorm_le_supSeminorm (x : MaximalSpectrum A) (a : A) :
    pointNorm K x a ≤ supSeminorm K a :=
  pointNorm_le_supSeminorm_of_bddAbove (bddAbove_range_pointNorm a) x

/-- **Perturbations of `1` by elements of supremum seminorm `< 1` are units.** In a dagger
algebra, `1 - a` is a unit whenever `|a|sup < 1`. -/
theorem isUnit_one_sub_of_supSeminorm_lt_one {a : A} (ha : supSeminorm K a < 1) :
    IsUnit (1 - a) :=
  _root_.TauCeti.isUnit_one_sub_of_supSeminorm_lt_one (bddAbove_range_pointNorm a) ha

end IsDaggerAlgebra

end TauCeti.Dagger
