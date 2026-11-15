/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map
public import TauCeti.Algebra.PositiveDegrees.Ray.Basic

/-!
# Transport of supported primitive rays

A positive degree map sends a supported primitive generator to a positive integer
multiple of a unique target supported generator. The generator itself need not be
allowed in either monoid. The induced ray map and its integer multiplier respect
identity and composition, and carry actual ray degrees to actual ray degrees, with
the cutoff modulus of the positive degree map controlling truncation.

Only the target integer module must be free; neither finite rank nor injectivity
of the additive map is required. Primitive decomposition uses
`exists_eq_zsmul_isPrimitive`.

Adapted from `Mei/Algebra/PositiveDegrees/Ray/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`, released under Apache 2.0.
-/

public section

namespace TauCeti.SupportedRay

variable {N M K : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup K]
variable {d : PositiveDegrees N} {e : PositiveDegrees M} {q : PositiveDegrees K}

/-- A positive degree map cannot kill a supported generator, even if that generator does
not belong to the allowed monoid. -/
theorem map_generator_ne_zero (w : SupportedRay d) (T : PositiveDegreeMap d e) :
    T w.generator ≠ 0 := by
  obtain ⟨n, hn⟩ := w.rayDegrees_nonempty
  obtain ⟨hnP, a, _, rfl⟩ := mem_rayDegrees.mp hn
  have hTn := T.map_ne_zero hnP (ne_zero_of_mem_rayDegrees hn)
  intro h
  exact hTn (by simp [map_zsmul, h])

section FreeTarget

variable [Module.Free ℤ M]

private theorem exists_map_generator (w : SupportedRay d) (T : PositiveDegreeMap d e) :
    ∃ v : SupportedRay e, ∃ b : ℤ, 0 < b ∧ T w.generator = b • v.generator := by
  obtain ⟨b, v, hb, hv, hTv⟩ := exists_eq_zsmul_isPrimitive (w.map_generator_ne_zero T)
  obtain ⟨a, ha, ham⟩ := w.supported
  have hab : (a * b) • v ∈ e.monoid := by
    simpa [map_zsmul, hTv, mul_smul] using T.map_mem ham
  exact ⟨⟨v, hv, a * b, mul_pos ha hb, hab⟩, b, hb, hTv⟩

/-- The target supported ray of a supported ray under a positive degree map. -/
noncomputable def map (w : SupportedRay d) (T : PositiveDegreeMap d e) : SupportedRay e :=
  (exists_map_generator w T).choose

/-- The positive integer multiplier of the target primitive generator. -/
noncomputable def mapMultiplier (w : SupportedRay d) (T : PositiveDegreeMap d e) : ℤ :=
  (exists_map_generator w T).choose_spec.choose

/-- The multiplier of a transported supported ray is positive. -/
theorem mapMultiplier_pos (w : SupportedRay d) (T : PositiveDegreeMap d e) :
    0 < w.mapMultiplier T :=
  (exists_map_generator w T).choose_spec.choose_spec.1

/-- The image of the ambient generator is the multiplier times the target generator, including
when the generator is not an allowed degree. -/
theorem map_generator (w : SupportedRay d) (T : PositiveDegreeMap d e) :
    T w.generator = w.mapMultiplier T • (w.map T).generator :=
  (exists_map_generator w T).choose_spec.choose_spec.2

/-- Integer multiples are reindexed by multiplying their integer multipliers. -/
theorem map_zsmul_generator (w : SupportedRay d) (T : PositiveDegreeMap d e) (a : ℤ) :
    T (a • w.generator) = (a * w.mapMultiplier T) • (w.map T).generator := by
  rw [map_zsmul, w.map_generator T, mul_smul]

/-- Actual allowed degrees map into the degrees of the transported ray. -/
theorem map_mem_rayDegrees (w : SupportedRay d) (T : PositiveDegreeMap d e) {n : N}
    (hn : n ∈ w.rayDegrees) : T n ∈ (w.map T).rayDegrees := by
  obtain ⟨hnP, a, ha, rfl⟩ := mem_rayDegrees.mp hn
  exact mem_rayDegrees.mpr ⟨T.map_mem hnP, a * w.mapMultiplier T,
    mul_pos ha (w.mapMultiplier_pos T), w.map_zsmul_generator T a⟩

/-- A positive-multiple equation characterizes the transported primitive ray. -/
theorem map_eq_iff (w : SupportedRay d) (T : PositiveDegreeMap d e) (v : SupportedRay e) :
    w.map T = v ↔ ∃ b : ℤ, 0 < b ∧ T w.generator = b • v.generator := by
  let : HasUniqueDiv M := .of_isTorsionFree ℤ M
  constructor
  · rintro rfl
    exact ⟨_, w.mapMultiplier_pos T, w.map_generator T⟩
  · rintro ⟨b, hb, hTv⟩
    exact ext ((w.map T).isPrimitive.eq_of_pos_zsmul_eq v.isPrimitive
      (w.mapMultiplier_pos T) hb ((w.map_generator T).symm.trans hTv))

/-- The integer multiplier is characterized by its generator equation. -/
theorem mapMultiplier_eq_iff (w : SupportedRay d) (T : PositiveDegreeMap d e) (b : ℤ) :
    w.mapMultiplier T = b ↔ T w.generator = b • (w.map T).generator := by
  rw [w.map_generator T]
  exact ⟨fun h => congrArg (fun a : ℤ => a • (w.map T).generator) h,
    fun h => (w.map T).isPrimitive.zsmul_left_injective h⟩

/-- The transported ray and its positive multiplier are jointly unique. -/
theorem existsUnique_map_generator (w : SupportedRay d) (T : PositiveDegreeMap d e) :
    ∃! p : SupportedRay e × ℤ, 0 < p.2 ∧ T w.generator = p.2 • p.1.generator := by
  refine ⟨(w.map T, w.mapMultiplier T), ⟨w.mapMultiplier_pos T, w.map_generator T⟩, ?_⟩
  rintro ⟨v, b⟩ ⟨hb, hTv⟩
  obtain rfl := (w.map_eq_iff T v).mpr ⟨b, hb, hTv⟩
  exact Prod.ext rfl ((w.mapMultiplier_eq_iff T b).mpr hTv).symm

/-- Two rays agree after transport exactly when an actual degree maps to the second ray. -/
theorem map_eq_iff_exists_mem_rayDegrees (w : SupportedRay d) (T : PositiveDegreeMap d e)
    (v : SupportedRay e) : w.map T = v ↔ ∃ n ∈ w.rayDegrees, T n ∈ v.rayDegrees := by
  let : HasUniqueDiv M := .of_isTorsionFree ℤ M
  constructor
  · rintro rfl
    obtain ⟨n, hn⟩ := w.rayDegrees_nonempty
    exact ⟨n, hn, w.map_mem_rayDegrees T hn⟩
  · rintro ⟨n, hn, hv⟩
    exact eq_of_mem_rayDegrees (w.map_mem_rayDegrees T hn) hv

end FreeTarget

/-- Truncating the image of a ray uses exactly the cutoff modulus of the map. Only actual
allowed source degrees are cut off, even for nonsaturated monoids. -/
theorem image_rayDegrees_inter_cutoff (w : SupportedRay d) (T : PositiveDegreeMap d e) (k : ℕ) :
    (T '' w.rayDegrees) ∩ e.cutoff k =
      (T '' (w.rayDegrees ∩ d.cutoff (T.modulus k))) ∩ e.cutoff k := by
  ext m
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    have hnP := (mem_rayDegrees.mp hn).1
    exact ⟨⟨n, ⟨hn, d.mem_cutoff.mpr ⟨hnP, T.degree_le k hnP (e.mem_cutoff.mp hk).2⟩⟩, rfl⟩, hk⟩
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    exact ⟨⟨n, hn.1, rfl⟩, hk⟩

section Identity

variable [Module.Free ℤ N] (w : SupportedRay d)

/-- The identity map fixes supported rays. -/
@[simp]
theorem map_id : w.map (PositiveDegreeMap.id d) = w :=
  (w.map_eq_iff _ _).mpr ⟨1, one_pos, by simp⟩

/-- The identity map has primitive multiplier one. -/
@[simp]
theorem mapMultiplier_id : w.mapMultiplier (PositiveDegreeMap.id d) = 1 :=
  (w.mapMultiplier_eq_iff _ _).mpr (by simp)

end Identity

section Composition

variable [Module.Free ℤ M] [Module.Free ℤ K]
variable (w : SupportedRay d) (T : PositiveDegreeMap d e) (U : PositiveDegreeMap e q)

/-- Transport of supported rays respects composition, including nonprimitive images. -/
@[simp]
theorem map_comp : w.map (U.comp T) = (w.map T).map U := by
  refine (w.map_eq_iff _ _).mpr
    ⟨w.mapMultiplier T * (w.map T).mapMultiplier U,
      mul_pos (w.mapMultiplier_pos T) ((w.map T).mapMultiplier_pos U), ?_⟩
  rw [PositiveDegreeMap.comp_apply, w.map_generator T, map_zsmul, (w.map T).map_generator U,
    mul_smul]

/-- Primitive multipliers multiply under composition in the original order. -/
@[simp]
theorem mapMultiplier_comp :
    w.mapMultiplier (U.comp T) = w.mapMultiplier T * (w.map T).mapMultiplier U := by
  refine (w.mapMultiplier_eq_iff _ _).mpr ?_
  rw [map_comp, PositiveDegreeMap.comp_apply, w.map_generator T, map_zsmul,
    (w.map T).map_generator U, mul_smul]

end Composition

end TauCeti.SupportedRay
