/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.ExteriorPower.BaseChange

/-!
# Degrees and slopes of hermitian vector bundles

The Arakelov degree of a hermitian vector bundle is the degree of its determinant line. Any
nonzero integral section of the determinant computes it, and rescaling the bundle metric acts
on degree with a factor of the rank. Dividing by the absolute degree of the ground field gives
a normalized degree invariant under finite extensions. The slope divides the unnormalized
degree by the rank and is defined for positive-rank bundles.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3.
* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §§1.1–1.2.
-/

public noncomputable section

open NumberField

namespace TauCeti.HermitianBundle

universe u v w

variable {K : Type u} [Field K]

variable [NumberField K]

/-- The Arakelov degree of a hermitian vector bundle is the degree of its determinant line. -/
def degree (E : HermitianBundle K) : ℝ :=
  E.det.metric.lineDegree

theorem degree_def (E : HermitianBundle K) : E.degree = E.det.metric.lineDegree := (rfl)

/-- Each nonzero integral section of the determinant computes the Arakelov degree. -/
theorem degree_eq_sectionDegree (E : HermitianBundle K) {s : E.det} (hs : s ≠ 0) :
    E.degree = E.det.metric.sectionDegree s :=
  E.det.metric.lineDegree_eq_sectionDegree (E.det.rank_eq_finrank_tensorProduct ▸ E.rank_det) hs

/-- For a line bundle the degree is the degree of the original metric on the line. -/
theorem degree_eq_lineDegree (E : HermitianBundle K) (hE : E.rank = 1) :
    E.degree = E.metric.lineDegree := by
  rw [degree_def, det_def, hE, exteriorPower_metric]
  have hrank : (E.exteriorPower 1).rank = 1 := by simp [hE]
  exact E.metric.isometryEquivExteriorPowerOne.lineDegree_eq
    ((E.exteriorPower 1).rank_eq_finrank_tensorProduct ▸ hrank)

/-- A rank-zero bundle has degree zero since its determinant is the trivial line. -/
theorem degree_eq_zero_of_rank_eq_zero (E : HermitianBundle K) (hE : E.rank = 0) :
    E.degree = 0 := by
  rw [degree_def, det_def, hE, exteriorPower_metric, ← HermitianMetric.lineDegree_trivial (K := K)]
  have hrank : (E.exteriorPower 0).rank = 1 := by simp
  exact E.metric.isometryEquivExteriorPowerZero.lineDegree_eq
    ((E.exteriorPower 0).rank_eq_finrank_tensorProduct ▸ hrank)

@[simp]
theorem degree_zero : (zero.{u, v} K).degree = 0 :=
  (zero K).degree_eq_zero_of_rank_eq_zero (rank_zero K)

@[simp]
theorem degree_trivial : (trivial K).degree = 0 :=
  ((trivial K).degree_eq_lineDegree (rank_trivial K)).trans HermitianMetric.lineDegree_trivial

/-- Isometric hermitian vector bundles have the same Arakelov degree. -/
theorem degree_eq_of_isometryEquiv {E : HermitianBundle.{u, v} K}
    {F : HermitianBundle.{u, w} K}
    (e : HermitianMetric.IsometryEquiv E.metric F.metric) :
    E.degree = F.degree := by
  have h : F.rank = E.rank := by
    simpa only [rank_def] using e.toLinearEquiv.finrank_eq.symm
  rw [degree_def, degree_def, det_def E, det_def F, h, exteriorPower_metric, exteriorPower_metric]
  exact (e.exteriorPower E.rank).lineDegree_eq (E.det.rank_eq_finrank_tensorProduct ▸ E.rank_det)

/-- Rescaling the norms by `exp (-c)` adds `rank(E) [K : ℚ] c` to the degree. -/
@[simp]
theorem degree_rescale (E : HermitianBundle K) (c : ℝ) :
    (E.rescale c).degree = E.degree + E.rank * Module.finrank ℚ K * c := by
  have : Nontrivial (⋀[𝓞 K]^E.rank E) :=
    Module.nontrivial_of_finrank_eq_succ (E.det.rank_def ▸ E.rank_det)
  calc
    (E.rescale c).degree = ((E.metric.rescale c).exteriorPower E.rank).lineDegree := by
      rw [degree_def, det_def, rank_rescale, exteriorPower_metric, rescale_metric]
      rfl
    _ = E.degree + E.rank * Module.finrank ℚ K * c := by
      rw [HermitianMetric.exteriorPower_rescale, HermitianMetric.lineDegree_rescale,
        degree_def, det_def, exteriorPower_metric]
      ac_rfl

/-- The normalized Arakelov degree is the degree divided by the absolute field degree. -/
def normalizedDegree (E : HermitianBundle K) : ℝ :=
  E.degree / Module.finrank ℚ K

theorem normalizedDegree_def (E : HermitianBundle K) :
    E.normalizedDegree = E.degree / Module.finrank ℚ K := (rfl)

/-- The slope of a positive-rank hermitian bundle is its Arakelov degree divided by its rank. -/
def slope (E : HermitianBundle K) (_hE : 0 < E.rank) : ℝ :=
  E.degree / E.rank

theorem slope_def (E : HermitianBundle K) (hE : 0 < E.rank) : E.slope hE = E.degree / E.rank :=
  (rfl)

/-- Rescaling the norms by `exp (-c)` shifts the normalized degree by `rank(E) c`. -/
@[simp]
theorem normalizedDegree_rescale (E : HermitianBundle K) (c : ℝ) :
    (E.rescale c).normalizedDegree = E.normalizedDegree + E.rank * c := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [normalizedDegree_def, normalizedDegree_def, degree_rescale]
  field_simp

/-- Rescaling the norms by `exp (-c)` shifts the slope by `[K : ℚ] c`. -/
@[simp]
theorem slope_rescale (E : HermitianBundle K) (c : ℝ) (hE : 0 < (E.rescale c).rank) :
    (E.rescale c).slope hE = E.slope (E.rank_rescale c ▸ hE) + Module.finrank ℚ K * c := by
  have hr : (E.rank : ℝ) ≠ 0 := by exact_mod_cast (E.rank_rescale c ▸ hE).ne'
  rw [slope_def, slope_def, rank_rescale, degree_rescale]
  field_simp

variable {L : Type*} [Field L] [NumberField L] [Algebra K L]

/-- Under base change, the Arakelov degree is multiplied by the relative field degree. -/
theorem degree_baseChange (E : HermitianBundle K) :
    (E.baseChange (L := L)).degree = Module.finrank K L * E.degree := by
  rw [degree_def, degree_def, ← (E.isometryEquivDetBaseChange (L := L)).lineDegree_eq
    ((E.det.baseChange (L := L)).rank_eq_finrank_tensorProduct ▸
      ((E.det.rank_baseChange (L := L)).trans E.rank_det))]
  exact E.det.metric.lineDegree_baseChange (E.det.rank_def ▸ E.rank_det)

/-- The normalized Arakelov degree is invariant under finite extensions. -/
@[simp]
theorem normalizedDegree_baseChange (E : HermitianBundle K) :
    (E.baseChange (L := L)).normalizedDegree = E.normalizedDegree := by
  let : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have hd : (Module.finrank K L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have ht : (Module.finrank ℚ L : ℝ) = (Module.finrank ℚ K : ℝ) * Module.finrank K L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K L).symm
  rw [normalizedDegree_def, normalizedDegree_def, degree_baseChange, ht, mul_comm _ E.degree,
    mul_div_mul_right _ _ hd]

end TauCeti.HermitianBundle
