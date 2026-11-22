/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators under linear and semilinear maps

This file proves naturality of `PLPath.lower` and `PLPath.raise` (extending the minimum-height
naturality in `TauCeti.RepresentationTheory.LSPath.RootOperator`) under semilinear maps
`g : V →ₛₗ[σ] W` along a monotone ring homomorphism `σ : 𝕜 →+* 𝕜'` carrying the source root `x` to
the target root `g x` and intertwining the height forms (`f' (g v) = σ (f v)`), and specializes to
`σ = RingHom.id 𝕜` for linear maps.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (paths, reparametrizations and root operators).
-/

public section

namespace TauCeti.PLPath

open Module

section Semilinear

variable {𝕜 𝕜' V W : Type*} [Field 𝕜] [LinearOrder 𝕜] [Field 𝕜'] [LinearOrder 𝕜']
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜' W] {σ : 𝕜 →+* 𝕜'}
  {g : V →ₛₗ[σ] W} {f : Dual 𝕜 V} {f' : Dual 𝕜' W}

/-- Capped record reflection commutes with a semilinear map along a monotone ring homomorphism
when the target height form pulls back along `g` to the source height form followed by `σ`. -/
theorem reflectRecords_mapSemilinear (hσ : Monotone σ) (hf : ∀ v, f' (g v) = σ (f v))
    (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) (σ c) (l.map g) = (reflectRecords f x c l).map g := by
  have hσ_strict : StrictMono σ := hσ.strictMono_of_injective σ.injective
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hmin : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) =
        σ (min (f v + listMinHeight f l) c) := by
      rw [hf v, listMinHeight_mapSemilinear hσ hf l, ← map_add, hσ.map_min]
    have hcond : 0 < min (f' (g v) + listMinHeight f' (l.map g)) (σ c) ↔
        0 < min (f v + listMinHeight f l) c := by
      rw [hmin, ← map_zero σ, hσ_strict.lt_iff_lt]
    have hc : σ c - f' (g v) = σ (c - f v) := by rw [hf v, map_sub]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · simp only [List.map_cons, reflectRecords_cons_of_pos h,
        reflectRecords_cons_of_pos (hcond.mpr h), hmin, hc, ih (c - f v)]
      refine congrArg₂ List.cons (by simp [preReflection_apply, map_sub, map_smulₛₗ, hf])
        (congrArg₂ List.cons ?_ rfl)
      rw [hf v, ← map_div₀, ← _root_.map_one σ, ← map_sub, map_smulₛₗ]
    · simp only [List.map_cons, reflectRecords_cons_of_nonpos (le_of_not_gt h),
        reflectRecords_cons_of_nonpos (le_of_not_gt (mt hcond.mp h)), hc, ih (c - f v)]

/-- Lowering on lists is natural for semilinear maps along a monotone ring homomorphism when the
target height form pulls back along `g` to the source height form followed by `σ`. -/
theorem listLower_mapSemilinear (hσ : Monotone σ) (hf : ∀ v, f' (g v) = σ (f v))
    (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) := by
  have hσ_strict : StrictMono σ := hσ.strictMono_of_injective σ.injective
  have hsum : f' (l.map g).sum = σ (f l.sum) := by rw [← map_list_sum, hf]
  have hm := listMinHeight_mapSemilinear hσ hf l
  have hcond : (1 : 𝕜') ≤ f' (l.map g).sum - listMinHeight f' (l.map g) ↔
      1 ≤ f l.sum - listMinHeight f l := by
    rw [hsum, hm, ← map_sub, ← _root_.map_one σ, hσ_strict.le_iff_le]
  rw [listLower_def, listLower_def]
  by_cases h : 1 ≤ f l.sum - listMinHeight f l
  · simp only [h, hcond.mpr h, ↓reduceIte, Option.map_some]
    rw [hm, ← _root_.map_one σ, ← map_add, reflectRecords_mapSemilinear hσ hf]
  · simp only [h, mt hcond.mp h, ↓reduceIte, Option.map_none]

/-- Lowering commutes with a semilinear image along a monotone ring homomorphism when the target
height form pulls back along `g` to the source height form followed by `σ`. -/
theorem lower_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (hσ : Monotone σ) (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    lower f' (g x) (p.mapSemilinear g) = (lower f x p).map (fun q ↦ q.mapSemilinear g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [mapSemilinear_ofSegments l g hσ, lower_ofSegments, listLower_mapSemilinear hσ hf,
    Option.map_map]
  exact congrArg (Option.map · _) (funext fun m ↦ (mapSemilinear_ofSegments m g hσ).symm)

/-- Raising commutes with a semilinear image along a monotone ring homomorphism when the target
height form pulls back along `g` to the source height form followed by `σ`. -/
theorem raise_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (hσ : Monotone σ) (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    raise f' (g x) (p.mapSemilinear g) = (raise f x p).map (fun q ↦ q.mapSemilinear g) := by
  simp only [raise_def, ← mapSemilinear_reverse, lower_mapSemilinear _ hσ hf, Option.map_map]
  exact congrArg (Option.map · _) (funext fun q ↦ (mapSemilinear_reverse q g).symm)

end Semilinear

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

section Heights

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V →ₗ[𝕜] W} {f : Dual 𝕜 V} {f' : Dual 𝕜 W}

omit [IsStrictOrderedRing 𝕜] in
/-- Capped record reflection commutes with a linear map preserving the height form.
No normalization or injectivity assumption is needed. -/
theorem reflectRecords_map (hf : f'.comp g = f) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) c (l.map g) = (reflectRecords f x c l).map g :=
  reflectRecords_mapSemilinear monotone_id (LinearMap.congr_fun hf) x c l

omit [IsStrictOrderedRing 𝕜] in
/-- Lowering on lists is natural for maps preserving the root and coroot form. -/
theorem listLower_map (hf : f'.comp g = f) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) :=
  listLower_mapSemilinear monotone_id (LinearMap.congr_fun hf) x l

/-- Lowering commutes with a linear image preserving the root and the coroot form. -/
theorem lower_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    lower f' (g x) (p.map g) = (lower f x p).map (fun q ↦ q.map g) := by
  simpa only [mapSemilinear_eq_map] using
    lower_mapSemilinear p monotone_id (LinearMap.congr_fun hf) x

/-- Raising commutes with a linear image preserving the root and the coroot form. -/
theorem raise_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    raise f' (g x) (p.map g) = (raise f x p).map (fun q ↦ q.map g) := by
  simpa only [mapSemilinear_eq_map] using
    raise_mapSemilinear p monotone_id (LinearMap.congr_fun hf) x

end Heights

end TauCeti.PLPath
