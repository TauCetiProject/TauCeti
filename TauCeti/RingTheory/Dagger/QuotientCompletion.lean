/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Quotient.Isometry
public import TauCeti.RingTheory.Dagger.ClosedIdeal
public import TauCeti.Analysis.Normed.Algebra.Completion

/-!
# Residue norms and completions of dagger presentation quotients

For an ideal `I` in the Monsky–Washnitzer algebra `W`, the canonical map
`W/I → T/IT` into the corresponding quotient of the unit-radius Tate algebra is an isometry
for the residue Gauss norms and has dense image. Consequently `T/IT` is the metric completion
of `W/I`, as an algebra over the coefficient field. This includes nonreduced and zero quotients;
the norm is the quotient Gauss norm, not the supremum seminorm on classical points.

The comparison extends `TauCeti.Dagger.washnitzerAlgebra.completionAlgEquiv` from the
relation-free case to arbitrary presentation ideals. Its equation on completion classes fixes
the map under `W/I`, and hence identifies the completion for each dagger presentation.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), Proposition 1.6(1).
-/

public section

noncomputable section

open UniformSpace
open TauCeti.Dagger
open TauCeti.Dagger.washnitzerAlgebra
open _root_.MvPowerSeries

namespace Ideal

section Density

variable {σ K : Type*} [NormedCommRing K] [IsUltrametricDist K]

/-- Every Tate quotient class can be approximated by overconvergent quotient classes. -/
theorem denseRange_quotientMap_toTate (I : Ideal (washnitzerAlgebra σ K)) :
    DenseRange (quotientMapₐ (I.map (toTate σ K)) (toTate σ K) le_comap_map) :=
  RingHom.denseRange_quotientMap (toTate σ K).toRingHom denseRange_toTate I

/-- The canonical map from a dagger presentation quotient to its affinoid quotient preserves
residue Gauss distances. No reducedness hypothesis is needed. -/
theorem isometry_quotientMap_toTate (I : Ideal (washnitzerAlgebra σ K)) :
    Isometry (quotientMapₐ (I.map (toTate σ K)) (toTate σ K) le_comap_map) :=
  RingHom.isometry_quotientMap (toTate σ K).toRingHom isometry_toTate denseRange_toTate I

end Density

variable {σ K : Type*} [Finite σ] [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K
local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- The metric completion of a dagger presentation quotient `W/I` is the affinoid quotient
`T/IT`, as an algebra over the coefficient field. -/
def washnitzerCompletionAlgEquiv (I : Ideal W) :
    Completion (W ⧸ I) ≃ₐ[K] T ⧸ I.map (toTate σ K) :=
  AlgHom.completionAlgEquiv (R := K) (A := W ⧸ I) (B := T ⧸ I.map (toTate σ K))
    (quotientMapₐ (I.map (toTate σ K)) (toTate σ K) le_comap_map)
    I.isometry_quotientMap_toTate I.denseRange_quotientMap_toTate

/-- The completion comparison extends the canonical map on every dagger quotient class. -/
@[simp]
theorem washnitzerCompletionAlgEquiv_coe (I : Ideal W) (x : W ⧸ I) :
    I.washnitzerCompletionAlgEquiv (x : Completion (W ⧸ I)) =
      quotientMapₐ (I.map (toTate σ K)) (toTate σ K) le_comap_map x :=
  AlgHom.completionAlgEquiv_coe _ _ _ x

/-- The inverse comparison recovers the completion class of each dagger quotient class. -/
@[simp]
theorem washnitzerCompletionAlgEquiv_symm_quotientMap (I : Ideal W) (x : W ⧸ I) :
    I.washnitzerCompletionAlgEquiv.symm
      (quotientMapₐ (I.map (toTate σ K)) (toTate σ K) le_comap_map x) =
        (x : Completion (W ⧸ I)) := by
  rw [← washnitzerCompletionAlgEquiv_coe, AlgEquiv.symm_apply_apply]

/-- The algebraic completion comparison is an isometry for the residue Gauss norms. -/
theorem isometry_washnitzerCompletionAlgEquiv (I : Ideal W) :
    Isometry I.washnitzerCompletionAlgEquiv :=
  AlgHom.isometry_completionAlgEquiv _ _ _

/-- The completion comparison preserves the norm of every completed quotient element. -/
@[simp]
theorem norm_washnitzerCompletionAlgEquiv (I : Ideal W) (x : Completion (W ⧸ I)) :
    ‖I.washnitzerCompletionAlgEquiv x‖ = ‖x‖ :=
  AlgHom.norm_completionAlgEquiv _ _ _ x

end Ideal

section Examples

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra (Fin 1) K
local notation "T" => IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ (1 : ℝ))

-- The relation-free comparison fixes the coefficient field.
example (c : K) :
    (⊥ : Ideal W).washnitzerCompletionAlgEquiv
      (algebraMap K (W ⧸ (⊥ : Ideal W)) c : Completion (W ⧸ (⊥ : Ideal W))) =
        algebraMap K (T ⧸ (⊥ : Ideal W).map (toTate (Fin 1) K)) c := by
  simp

-- The full relation ideal gives the zero algebra, also after metric completion.
example (x : Completion (W ⧸ (⊤ : Ideal W))) :
    (⊤ : Ideal W).washnitzerCompletionAlgEquiv x = 0 := by
  have h : (⊤ : Ideal W).map (toTate (Fin 1) K) = ⊤ := Ideal.map_top _
  have : Subsingleton (T ⧸ (⊤ : Ideal W).map (toTate (Fin 1) K)) := by
    rw [h]
    infer_instance
  exact Subsingleton.elim _ _

-- The nilpotent coordinate remains nonzero: the extended relation is still `(X²)`, not `(X)`.
example :
    let I : Ideal W := Ideal.span {X (Fin 1) K 0 ^ 2}
    let x : Completion (W ⧸ I) := Ideal.Quotient.mk I (X (Fin 1) K 0)
    I.washnitzerCompletionAlgEquiv x ≠ 0 ∧ (I.washnitzerCompletionAlgEquiv x) ^ 2 = 0 := by
  dsimp only
  rw [Ideal.washnitzerCompletionAlgEquiv_coe, Ideal.quotient_map_mkₐ]
  constructor
  · intro hz
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.map_span, Set.image_singleton, map_pow] at hm
    have hd : (toTate (Fin 1) K (X (Fin 1) K 0)) ^ 2 ∣
        toTate (Fin 1) K (X (Fin 1) K 0) := Ideal.mem_span_singleton.mp hm
    have hdiv : (_root_.MvPowerSeries.X 0 : MvPowerSeries (Fin 1) K) ^ 2 ∣
        _root_.MvPowerSeries.X 0 := by
      have h := map_dvd (IsRestricted.subring
        (R := K) (fun _ : Fin 1 ↦ (1 : ℝ))).subtype hd
      simpa only [map_pow, Subring.subtype_apply, coe_toTate, coe_X] using h
    have hc := X_pow_dvd_iff.mp hdiv (Finsupp.single 0 1) (by simp)
    simp [coeff_X] at hc
  · rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))

end Examples
