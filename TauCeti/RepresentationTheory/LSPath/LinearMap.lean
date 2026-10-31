/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators under linear maps

The linear-image construction `TauCeti.PLPath.map` is defined in
`TauCeti.RepresentationTheory.LSPath.PLPath`, including for noninjective maps and collapsed
segments. This file proves naturality of root operators.

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

open Module

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

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
