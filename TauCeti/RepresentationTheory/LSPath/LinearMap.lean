/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Linear images of piecewise-linear paths

A linear map sends a path to the path obtained by applying it to each segment. This is
well-defined even for noninjective maps: merging positively collinear segments and deleting
stationary segments remain valid elementary moves after taking a linear image.

The operators `lower` and `raise` commute with a linear map `g` when the target coroot form
pulls back to the source form and the target root is the image of the source root. The equality
of forms preserves all running heights, so the record cuts, not just the endpoints, agree.
This permits changes of weight space and linear transformations of time–weight graphs.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (paths, reparametrizations and root operators).
-/

public section

namespace TauCeti.PLPath

open Module Relation

variable {𝕜 V W U : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
  [AddCommGroup U] [Module 𝕜 U]

section Images

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Taking a linear image preserves elementary path moves, including when segments collapse. -/
theorem Move.map {l m : List V} (h : Move 𝕜 l m) (g : V →ₗ[𝕜] W) :
    Move 𝕜 (l.map g) (m.map g) := by
  cases h with
  | merge l m hvw => simpa using Move.merge (l.map g) (m.map g) (hvw.map g)
  | erase_zero l m => simpa using Move.erase_zero (l.map g) (m.map g)

/-- Normalizing a presentation before taking its linear image does not change the path. -/
theorem ofSegments_map_normalize (g : V →ₗ[𝕜] W) (l : List V) :
    ofSegments 𝕜 ((normalize 𝕜 l).map g) = ofSegments 𝕜 (l.map g) := by
  apply ofSegments_eq_ofSegments_iff.mpr
  exact (EqvGen.reflTransGen_le_eqvGen _ _ _
    ((reflTransGen_move_normalize l).lift _ fun _ _ h ↦ h.map g)).symm _ _

/-- The linear image of a piecewise-linear path, with any collapsed segments removed. -/
noncomputable def map (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) : PLPath 𝕜 W :=
  ofSegments 𝕜 (p.segments.map g)

/-- A linear image can be computed on any segment presentation. -/
@[simp]
theorem map_ofSegments (l : List V) (g : V →ₗ[𝕜] W) :
    (ofSegments 𝕜 l).map g = ofSegments 𝕜 (l.map g) := by
  simp only [map, segments_ofSegments, ofSegments_map_normalize]

@[simp]
theorem map_id (p : PLPath 𝕜 V) : p.map (LinearMap.id : V →ₗ[𝕜] V) = p := by
  simp [map]

/-- Linear images respect composition. -/
@[simp]
theorem map_map (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) (h : W →ₗ[𝕜] U) :
    (p.map g).map h = p.map (h.comp g) := by
  simp [map, ofSegments_map_normalize, List.map_map]

@[simp]
theorem map_one (g : V →ₗ[𝕜] W) : (1 : PLPath 𝕜 V).map g = 1 := by
  simp [map]

/-- Linear images preserve concatenation. -/
@[simp]
theorem map_mul (p q : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) :
    (p * q).map g = p.map g * q.map g := by
  simp [map, ofSegments_map_normalize, List.map_append]

@[simp]
theorem map_straight (v : V) (g : V →ₗ[𝕜] W) :
    (straight 𝕜 v).map g = straight 𝕜 (g v) := by
  simp [straight_def]

@[simp]
theorem endpoint_map (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) :
    (p.map g).endpoint = g p.endpoint := by
  simp [map, endpoint_def, map_list_sum]

/-- Linear images commute with reversal. -/
@[simp]
theorem map_reverse (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) :
    p.reverse.map g = (p.map g).reverse := by
  simp [map, segments_reverse, List.map_reverse, List.map_map, reverse_ofSegments,
    Function.comp_def]

end Images

section Heights

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V →ₗ[𝕜] W} {f : Dual 𝕜 V} {f' : Dual 𝕜 W}

/-- Minimum height is natural under arbitrary linear maps. -/
theorem minHeight_map (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) (f' : Dual 𝕜 W) :
    (p.map g).minHeight f' = p.minHeight (f'.comp g) := by
  simp [map, listMinHeight_map, minHeight_def]

omit [IsStrictOrderedRing 𝕜] in
/-- Capped record reflection commutes with a linear map preserving the height form.
No normalization or injectivity assumption is needed. -/
theorem reflectRecords_map (hf : f'.comp g = f) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) c (l.map g) = (reflectRecords f x c l).map g := by
  have he (v : V) : f' (g v) = f v := LinearMap.congr_fun hf v
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hm : listMinHeight f' (l.map g) = listMinHeight f l := by
      rw [listMinHeight_map, hf]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons, reflectRecords_cons_of_pos (f := f') (by
        simpa only [he, hm] using h), reflectRecords_cons_of_pos h]
      simp [he, hm, ih, preReflection_apply, map_sub, map_smul]
    · rw [List.map_cons, reflectRecords_cons_of_nonpos (f := f') (by
        simpa only [he, hm] using le_of_not_gt h),
        reflectRecords_cons_of_nonpos (le_of_not_gt h)]
      simp [he, ih]

omit [IsStrictOrderedRing 𝕜] in
/-- Lowering on lists is natural for maps preserving the root and coroot form. -/
theorem listLower_map (hf : f'.comp g = f) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) := by
  have he : f' (l.map g).sum = f l.sum := by
    rw [← map_list_sum, ← LinearMap.comp_apply, hf]
  simp only [listLower_def, listMinHeight_map, hf, he]
  split_ifs <;> simp [reflectRecords_map hf]

/-- Lowering commutes with a linear image preserving the root and the coroot form. -/
theorem lower_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    lower f' (g x) (p.map g) = (lower f x p).map (fun q ↦ q.map g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [map_ofSegments, lower_ofSegments, listLower_map hf, Option.map_map]
  congr 1
  funext l
  exact (map_ofSegments l g).symm

/-- Raising commutes with a linear image preserving the root and the coroot form. -/
theorem raise_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    raise f' (g x) (p.map g) = (raise f x p).map (fun q ↦ q.map g) := by
  simp only [raise_def, ← map_reverse, lower_map _ hf, Option.map_map]
  congr 1
  funext q
  exact (map_reverse q g).symm

end Heights

end TauCeti.PLPath
