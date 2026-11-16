/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators under linear and semilinear maps

The linear-image construction `TauCeti.PLPath.map` is defined in
`TauCeti.RepresentationTheory.LSPath.PLPath`, including for noninjective maps and collapsed
segments. This file extends it to semilinear images `TauCeti.PLPath.mapSemilinear` along a
monotone ring homomorphism `σ : 𝕜 →+* 𝕜'` between linearly ordered fields, and proves naturality
of minimum heights and root operators under both semilinear and linear maps.

The operators `lower` and `raise` commute with a semilinear map `g : V →ₛₗ[σ] W` when the target
coroot form intertwines the source form (`f' (g v) = σ (f v)`) and the target root is the image
of the source root. Since `σ` is strictly monotone, all running heights and record-cut comparisons
are preserved. Specializing to `σ = RingHom.id 𝕜` recovers linear naturality.

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

/-- A semilinear image along a monotone ring homomorphism preserves elementary path moves,
including when segments collapse. -/
theorem Move.mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    {l m : List V} (h : Move 𝕜 l m) (g : V →ₛₗ[σ] W) (hσ : Monotone σ) :
    Move 𝕜' (l.map g) (m.map g) := by
  have hσ_strict : StrictMono σ := hσ.strictMono_of_injective σ.injective
  cases h with
  | @merge l m v w hvw =>
    have hray : SameRay 𝕜' (g v) (g w) := by
      rcases hvw with h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, heq⟩
      · simp [h0]
      · simp [h0]
      · exact Or.inr (Or.inr ⟨σ r₁, σ r₂, map_zero σ ▸ hσ_strict hr₁, map_zero σ ▸ hσ_strict hr₂,
          by rw [← map_smulₛₗ, ← map_smulₛₗ, heq]⟩)
    simpa using Move.merge (l.map g) (m.map g) hray
  | erase_zero l m => simpa using Move.erase_zero (l.map g) (m.map g)

/-- Normalizing a presentation before taking its semilinear image along a monotone ring
homomorphism does not change the path. -/
theorem ofSegments_map_normalize_semilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (g : V →ₛₗ[σ] W) (hσ : Monotone σ) (l : List V) :
    ofSegments 𝕜' ((normalize 𝕜 l).map g) = ofSegments 𝕜' (l.map g) := by
  apply ofSegments_eq_ofSegments_iff.mpr
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    ((reflTransGen_move_normalize l).lift _ fun _ _ h ↦ h.mapSemilinear g hσ)).symm _ _

/-- The semilinear image of a piecewise-linear path along `g : V →ₛₗ[σ] W`, with any collapsed
segments removed. -/
noncomputable def mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] W) : PLPath 𝕜' W :=
  ofSegments 𝕜' (p.segments.map g)

/-- Definitional unfolding of `PLPath.mapSemilinear` in terms of `ofSegments` and `segments`. -/
theorem mapSemilinear_def [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] W) :
    p.mapSemilinear g = ofSegments 𝕜' (p.segments.map g) :=
  (rfl)

/-- For a `𝕜`-linear map, `mapSemilinear` coincides with `PLPath.map`. -/
@[simp]
theorem mapSemilinear_eq_map [IsStrictOrderedRing 𝕜] {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) : p.mapSemilinear g = p.map g := by
  rw [mapSemilinear_def, map_def]

/-- A semilinear image along a monotone ring homomorphism can be computed on any segment
presentation. -/
theorem mapSemilinear_ofSegments [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (l : List V) (g : V →ₛₗ[σ] W) (hσ : Monotone σ) :
    (ofSegments 𝕜 l).mapSemilinear g = ofSegments 𝕜' (l.map g) := by
  simp only [mapSemilinear, segments_ofSegments, ofSegments_map_normalize_semilinear g hσ]

/-- Semilinear images preserve the endpoint. -/
@[simp]
theorem endpoint_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] W) : (p.mapSemilinear g).endpoint = g p.endpoint := by
  simp [mapSemilinear, endpoint_def, map_list_sum]

/-- Semilinear images commute with reversal. -/
@[simp]
theorem mapSemilinear_reverse [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] W) :
    p.reverse.mapSemilinear g = (p.mapSemilinear g).reverse := by
  simp [mapSemilinear, segments_reverse, List.map_reverse, List.map_map, reverse_ofSegments,
    Function.comp_def]

/-- Running minimum height commutes with a semilinear map along a monotone ring homomorphism
intertwining the height forms. -/
theorem listMinHeight_mapSemilinear {g : V →ₛₗ[σ] W} (hσ : Monotone σ)
    {f : Dual 𝕜 V} {f' : Dual 𝕜' W} (hf : ∀ v, f' (g v) = σ (f v)) (l : List V) :
    listMinHeight f' (l.map g) = σ (listMinHeight f l) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, listMinHeight_cons, listMinHeight_cons, hf v, ih, ← map_add, ← map_zero σ,
      ← hσ.map_min]

/-- Minimum height commutes with a semilinear image along a monotone ring homomorphism
intertwining the height forms. -/
theorem minHeight_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    {g : V →ₛₗ[σ] W} (hσ : Monotone σ) {f : Dual 𝕜 V} {f' : Dual 𝕜' W}
    (hf : ∀ v, f' (g v) = σ (f v)) (p : PLPath 𝕜 V) :
    (p.mapSemilinear g).minHeight f' = σ (p.minHeight f) := by
  rw [mapSemilinear, minHeight_ofSegments, listMinHeight_mapSemilinear hσ hf, ← minHeight_def]

/-- Capped record reflection commutes with a semilinear map along a monotone ring homomorphism
intertwining the height forms. No normalization or injectivity assumption is needed. -/
theorem reflectRecords_mapSemilinear {g : V →ₛₗ[σ] W} (hσ : Monotone σ)
    {f : Dual 𝕜 V} {f' : Dual 𝕜' W} (hf : ∀ v, f' (g v) = σ (f v)) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) (σ c) (l.map g) = (reflectRecords f x c l).map g := by
  have hσ_strict : StrictMono σ := hσ.strictMono_of_injective σ.injective
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hmin : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) =
        σ (min (f v + listMinHeight f l) c) := by
      rw [hf v, listMinHeight_mapSemilinear hσ hf l, ← map_add, hσ.map_min]
    have hc : σ c - f' (g v) = σ (c - f v) := by rw [hf v, map_sub]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons,
        reflectRecords_cons_of_pos (f := f') (hmin ▸ map_zero σ ▸ hσ_strict h),
        reflectRecords_cons_of_pos h, List.map_cons, List.map_cons, hmin, hc, ih (c - f v)]
      congr 1
      · simp [preReflection_apply, map_sub, map_smulₛₗ, hf]
      · rw [List.cons.injEq]
        refine ⟨?_, rfl⟩
        rw [hf v, ← map_div₀, ← _root_.map_one σ, ← map_sub, map_smulₛₗ]
    · rw [List.map_cons,
        reflectRecords_cons_of_nonpos (f := f') (hmin ▸ map_zero σ ▸ hσ (le_of_not_gt h)),
        reflectRecords_cons_of_nonpos (le_of_not_gt h), List.map_cons, hc, ih (c - f v)]

/-- Lowering on lists is natural for semilinear maps along a monotone ring homomorphism
intertwining the root and height form. -/
theorem listLower_mapSemilinear {g : V →ₛₗ[σ] W} (hσ : Monotone σ)
    {f : Dual 𝕜 V} {f' : Dual 𝕜' W} (hf : ∀ v, f' (g v) = σ (f v)) (x : V) (l : List V) :
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

/-- Lowering commutes with a semilinear image along a monotone ring homomorphism intertwining the
root and height form. -/
theorem lower_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) {g : V →ₛₗ[σ] W} (hσ : Monotone σ) {f : Dual 𝕜 V} {f' : Dual 𝕜' W}
    (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    lower f' (g x) (p.mapSemilinear g) = (lower f x p).map (fun q ↦ q.mapSemilinear g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [mapSemilinear_ofSegments l g hσ, lower_ofSegments, listLower_mapSemilinear hσ hf,
    Option.map_map]
  congr 1
  funext m
  exact (mapSemilinear_ofSegments m g hσ).symm

/-- Raising commutes with a semilinear image along a monotone ring homomorphism intertwining the
root and height form. -/
theorem raise_mapSemilinear [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜']
    (p : PLPath 𝕜 V) {g : V →ₛₗ[σ] W} (hσ : Monotone σ) {f : Dual 𝕜 V} {f' : Dual 𝕜' W}
    (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    raise f' (g x) (p.mapSemilinear g) = (raise f x p).map (fun q ↦ q.mapSemilinear g) := by
  simp only [raise_def, ← mapSemilinear_reverse, lower_mapSemilinear _ hσ hf, Option.map_map]
  congr 1
  funext q
  exact (mapSemilinear_reverse q g).symm

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
