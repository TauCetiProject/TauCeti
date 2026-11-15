/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.LinearMap

/-!
# Capped record reflection and dilation of paths

`PLPath.cappedReflection f x c` reflects the increasing records of a path up to height `c`,
keeping equal-height excursions. It is the presentation-independent version of
`PLPath.reflectRecords`. Lowering is capped reflection at the minimum height plus one,
when the lowering operator is defined.

Positive dilation multiplies all heights and caps by the same scalar, leaving the relative
cut positions unchanged. The covariance theorem `PLPath.cappedReflection_map_smul` is useful
for comparing stretching with iterated root operators. It does not identify a capped
reflection with an iterated root operator: that additionally requires a composition theorem
for successive record reflections.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 5 (root operators and similarity).
-/

public section

namespace TauCeti.PLPath

open Module Relation

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

/-- Normalizing a presentation before record reflection does not change the resulting path. -/
@[simp]
theorem normalize_reflectRecords_normalize (c : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c (normalize 𝕜 l)) =
      normalize 𝕜 (reflectRecords f x c l) := by
  suffices ∀ m, ReflTransGen (Move 𝕜) l m →
      normalize 𝕜 (reflectRecords f x c m) = normalize 𝕜 (reflectRecords f x c l) from
    this _ (reflTransGen_move_normalize l)
  intro m h
  induction h with
  | refl => rfl
  | tail _ h ih => exact (h.normalize_reflectRecords c).symm.trans ih

/-- Reflect the increasing records up to the cap `c`, retaining equal-height excursions.
The operation is independent of the segment presentation. -/
noncomputable def cappedReflection (f : Dual 𝕜 V) (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    PLPath 𝕜 V :=
  ofSegments 𝕜 (reflectRecords f x c p.segments)

/-- Compute capped reflection on any segment presentation, without normalizing it first. -/
@[simp]
theorem cappedReflection_ofSegments (c : 𝕜) (l : List V) :
    cappedReflection f x c (ofSegments 𝕜 l) = ofSegments 𝕜 (reflectRecords f x c l) := by
  apply PLPath.ext
  simp only [cappedReflection, segments_ofSegments, normalize_reflectRecords_normalize]

@[simp]
theorem cappedReflection_one (c : 𝕜) : cappedReflection f x c (1 : PLPath 𝕜 V) = 1 := by
  rw [← ofSegments_nil, cappedReflection_ofSegments, reflectRecords_nil]

/-- A cap below the minimum height reflects no part of the path. -/
@[simp]
theorem cappedReflection_eq_self {c : 𝕜} (p : PLPath 𝕜 V) (hc : c ≤ p.minHeight f) :
    cappedReflection f x c p = p := by
  rw [minHeight_def] at hc
  rw [cappedReflection, reflectRecords_of_le_listMinHeight hc, ofSegments_segments]

/-- The endpoint change is the capped increase from the minimum to the final height. -/
@[simp]
theorem endpoint_cappedReflection (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).endpoint =
      p.endpoint - (min (f p.endpoint) c - min (p.minHeight f) c) • x := by
  rw [cappedReflection, endpoint_ofSegments, sum_reflectRecords, endpoint_def, minHeight_def]

/-- For a normalized root-coroot pair, capped reflection lowers the minimum by the capped
increase from the minimum to the final height. -/
@[simp]
theorem minHeight_cappedReflection (hx : f x = 2) (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).minHeight f =
      p.minHeight f - (min (f p.endpoint) c - min (p.minHeight f) c) := by
  rw [cappedReflection, minHeight_ofSegments, listMinHeight_reflectRecords hx,
    endpoint_def, minHeight_def]

/-- Capped reflection of a concatenation uses the tail minimum for the first cap and translates
by the first factor's final height for the second cap. -/
theorem cappedReflection_mul (c : 𝕜) (p q : PLPath 𝕜 V) :
    cappedReflection f x c (p * q) =
      cappedReflection f x (min c (f p.endpoint + q.minHeight f)) p *
        cappedReflection f x (c - f p.endpoint) q := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  rw [← ofSegments_append, cappedReflection_ofSegments, reflectRecords_append,
    ofSegments_append]
  simp only [cappedReflection_ofSegments, endpoint_ofSegments, minHeight_ofSegments]

/-- Capped reflection is natural for linear maps preserving the height form and carrying the
root to the target root, including maps that collapse segments. -/
theorem cappedReflection_map {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {g : V →ₗ[𝕜] W} {f' : Dual 𝕜 W} (hf : f'.comp g = f)
    (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f' (g x) c (p.map g) = (cappedReflection f x c p).map g := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [map_ofSegments, cappedReflection_ofSegments, reflectRecords_map hf]

/-- Lowering is capped reflection at the minimum plus one, provided the height string has
at least one step left. -/
theorem lower_eq_some_cappedReflection (p : PLPath 𝕜 V)
    (hp : 1 ≤ f p.endpoint - p.minHeight f) :
    lower f x p = some (cappedReflection f x (p.minHeight f + 1) p) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [endpoint_ofSegments, minHeight_ofSegments] at hp
  rw [lower_ofSegments, listLower_def, ite_eq_left hp, Option.map_some,
    cappedReflection_ofSegments, minHeight_ofSegments]

/-! ## Positive dilation -/

/-- Dilation by a positive scalar preserves every cut fraction in capped record reflection.
This is an equality of raw segment lists, before normalization. -/
theorem reflectRecords_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (l : List V) :
    reflectRecords f x (a * c) (l.map (a • ·)) = (reflectRecords f x c l).map (a • ·) := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hcap : min (f (a • v) + listMinHeight f (l.map (a • ·))) (a * c) =
        a * min (f v + listMinHeight f l) c := by
      rw [map_smul, smul_eq_mul, listMinHeight_map_smul ha.le, ← mul_add,
        mul_min_of_nonneg _ _ ha.le]
    have hshift : a * c - f (a • v) = a * (c - f v) := by
      simp only [map_smul, smul_eq_mul, mul_sub]
    have hcut : (a * min (f v + listMinHeight f l) c) / (a * f v) =
        min (f v + listMinHeight f l) c / f v := mul_div_mul_left _ _ ha.ne'
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons, reflectRecords_cons_of_pos (by rw [hcap]; exact mul_pos ha h),
        reflectRecords_cons_of_pos h]
      simp only [hcap, hshift]
      simp only [map_smul, smul_eq_mul, hcut, ih, List.map_cons]
      congr 1
      · rw [smul_comm]
      · rw [smul_comm]
    · rw [List.map_cons, reflectRecords_cons_of_nonpos (by
          rw [hcap]; exact mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)),
        reflectRecords_cons_of_nonpos (le_of_not_gt h), hshift, ih, List.map_cons]

/-- Positive dilation commutes with capped reflection when the cap is dilated as well.
Unlike height-preserving naturality, this keeps the root and coroot fixed. -/
theorem cappedReflection_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f x (a * c) (p.map (a • LinearMap.id)) =
      (cappedReflection f x c p).map (a • LinearMap.id) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simpa only [map_ofSegments, cappedReflection_ofSegments, LinearMap.coe_smul,
    Pi.smul_def, LinearMap.id_apply] using
    congrArg (ofSegments 𝕜) (reflectRecords_map_smul (f := f) ha c l)

end TauCeti.PLPath
