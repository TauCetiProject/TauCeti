/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators and injectivity under linear maps

The linear-image construction `TauCeti.PLPath.map` is defined in
`TauCeti.RepresentationTheory.LSPath.PLPath`, including for noninjective maps and collapsed
segments. This file proves naturality of root operators and injectivity of `PLPath.map` for
injective linear maps.

The operators `lower` and `raise` commute with a linear map `g` when the target coroot form
pulls back to the source form and the target root is the image of the source root. The equality
of forms preserves all running heights, so the record cuts, not just the endpoints, agree.
When `g` is injective (in particular for nonzero scalar dilations `a • LinearMap.id`), it also
commutes with `consMerge` and `normalize`, hence preserves reduced segment lists and acts
injectively on `PLPath 𝕜 V` (`TauCeti.PLPath.map_injective`,
`TauCeti.PLPath.map_smul_id_injective`).

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (paths, reparametrizations and root operators).
-/

public section

namespace TauCeti.PLPath

open Module

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

section Injective

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Mapping by the zero linear map collapses every piecewise-linear path to the constant path
`1`. -/
@[simp]
theorem map_zero_linearMap (p : PLPath 𝕜 V) : p.map (0 : V →ₗ[𝕜] W) = 1 := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  apply PLPath.ext
  simp [segments_ofSegments, normalize_eq_nil_iff]

/-- An injective linear map commutes with the single normalization step `consMerge`, since it
preserves and reflects both zero segments and collinear rays. -/
theorem consMerge_map_of_injective {g : V →ₗ[𝕜] W} (hg : Function.Injective g)
    (v : V) (l : List V) :
    consMerge 𝕜 (g v) (l.map g) = (consMerge 𝕜 v l).map g := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hgv : g v ≠ 0 := by simpa [map_zero] using hg.ne hv
  cases l with
  | nil => simp [consMerge_nil_of_ne_zero hv, consMerge_nil_of_ne_zero hgv]
  | cons w l =>
    by_cases hvw : SameRay 𝕜 v w
    · rw [List.map_cons, consMerge_cons_of_sameRay (hg.sameRay_map_iff.mpr hvw),
        consMerge_cons_of_sameRay hvw, List.map_cons, map_add]
    · rw [List.map_cons, consMerge_cons_of_not_sameRay (mt hg.sameRay_map_iff.mp hvw),
        consMerge_cons_of_not_sameRay hvw, List.map_cons, List.map_cons]

/-- Segment normalization commutes with any injective linear map. -/
theorem normalize_map_of_injective {g : V →ₗ[𝕜] W} (hg : Function.Injective g) (l : List V) :
    normalize 𝕜 (l.map g) = (normalize 𝕜 l).map g := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, normalize_cons, normalize_cons, ih, consMerge_map_of_injective hg]

/-- An injective linear map preserves the reduced segment list of a path without further merging or
erasure. -/
theorem segments_map_of_injective {g : V →ₗ[𝕜] W} (hg : Function.Injective g) (p : PLPath 𝕜 V) :
    (p.map g).segments = p.segments.map g := by
  rw [map_def, segments_ofSegments, normalize_map_of_injective hg, p.isReduced.normalize_eq]

/-- An injective linear map acts injectively on piecewise-linear paths. -/
theorem map_injective {g : V →ₗ[𝕜] W} (hg : Function.Injective g) :
    Function.Injective (fun p : PLPath 𝕜 V ↦ p.map g) := by
  intro p q (h : p.map g = q.map g)
  apply PLPath.ext
  apply List.map_injective_iff.mpr hg
  rw [← segments_map_of_injective hg, ← segments_map_of_injective hg, h]

/-- Nonzero scalar dilation acts injectively on piecewise-linear paths. -/
theorem map_smul_id_injective {a : 𝕜} (ha : a ≠ 0) :
    Function.Injective (fun p : PLPath 𝕜 V ↦ p.map (a • LinearMap.id)) :=
  map_injective fun _ _ h ↦ smul_right_injective V ha h

end Injective

section Heights

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V →ₗ[𝕜] W} {f : Dual 𝕜 V} {f' : Dual 𝕜 W}

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
