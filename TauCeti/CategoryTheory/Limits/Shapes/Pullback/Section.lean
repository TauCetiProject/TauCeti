/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of the second factor of a pullback, and sections

Fix `π : Y ⟶ S`. A morphism `k : T' ⟶ T` with `k ≫ a = a'` induces the base-change morphism

```
pullback.mapSnd π a a' k hk : pullback π a' ⟶ pullback π a
```

which is the identity on the first factor `Y` and `k` on the second. A lift `s : T ⟶ Y` of
`a : T ⟶ S` through `π` induces a section `pullbackSection π a s hs : T ⟶ pullback π a` of the
second projection `pullback.snd π a`, with first projection `s`.

When `s = a ≫ σ` for a section `σ` of `π`, `pullbackSection π a s hs` is the section underlying
`CategoryTheory.SplitEpi.pullback`.

## Main definitions

* `CategoryTheory.Limits.pullback.mapSnd`: the morphism `pullback π a' ⟶ pullback π a` induced
  by a morphism `k : T' ⟶ T` over `S`.
* `CategoryTheory.Limits.pullbackSection`: the section of `pullback.snd π a` induced by a lift of
  `a` through `π`.

## Main results

* `CategoryTheory.Limits.pullback.mapSnd_id` and `CategoryTheory.Limits.pullback.mapSnd_comp`:
  `pullback.mapSnd` preserves identities and composition.
* `CategoryTheory.Limits.pullbackSection_comp_mapSnd`: `pullbackSection` is natural across
  `pullback.mapSnd`.

## Provenance

`pullback.mapSnd`, `pullbackSection` and their lemmas generalise declarations of AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`,
file `projects/ModularCurves/ModularCurves/Picard/RelativePic.lean`:
`AlgebraicGeometry.Scheme.Modules.baseChangeMap`, `baseChangeMap_id`, `baseChangeMap_comp`,
`baseChangeZero`, `baseChangeZero_snd`, and `baseChangeZero_baseChangeMap`. There the category is
that of schemes and the section is induced by a section of `π`; here the category is arbitrary
and the section is induced by any lift of `a` through `π`.
-/

public section

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] {Y S T T' T'' : C}

/-- Base change of the second factor along `k : T' ⟶ T` with `k ≫ a = a'`: the morphism
`pullback π a' ⟶ pullback π a` that is the identity on the first factor `Y` and `k` on the second,
namely `pullback.map` with identities on `Y` and `S`. -/
noncomputable def pullback.mapSnd (π : Y ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S) (k : T' ⟶ T)
    (hk : k ≫ a = a') [HasPullback π a] [HasPullback π a'] : pullback π a' ⟶ pullback π a :=
  pullback.map π a' π a (𝟙 Y) k (𝟙 S) (by simp) (by simp [hk])

/-- Base change of the second factor is the identity on the first factor `Y`: it commutes with
the first projections. -/
@[reassoc (attr := simp)]
theorem pullback.mapSnd_fst (π : Y ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S) (k : T' ⟶ T) (hk : k ≫ a = a')
    [HasPullback π a] [HasPullback π a'] :
    pullback.mapSnd π a a' k hk ≫ pullback.fst π a = pullback.fst π a' := by
  simp [pullback.mapSnd]

/-- Base change of the second factor along `k` is `k` on second factors: followed by the second
projection of `pullback π a`, it is the second projection of `pullback π a'` followed by `k`. -/
@[reassoc (attr := simp)]
theorem pullback.mapSnd_snd (π : Y ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S) (k : T' ⟶ T) (hk : k ≫ a = a')
    [HasPullback π a] [HasPullback π a'] :
    pullback.mapSnd π a a' k hk ≫ pullback.snd π a = pullback.snd π a' ≫ k := by
  simp [pullback.mapSnd]

/-- Base change of the second factor along the identity is the identity. -/
@[simp]
theorem pullback.mapSnd_id (π : Y ⟶ S) (a : T ⟶ S) [HasPullback π a] :
    pullback.mapSnd π a a (𝟙 T) (by simp) = 𝟙 (pullback π a) := by
  rw [pullback.mapSnd, pullback.map_id]

/-- Base change of the second factor is compatible with composition: base change along
`l : T'' ⟶ T'` followed by base change along `k : T' ⟶ T` is base change along `l ≫ k`. -/
@[reassoc (attr := simp)]
theorem pullback.mapSnd_comp (π : Y ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S) (a'' : T'' ⟶ S) (k : T' ⟶ T)
    (hk : k ≫ a = a') (l : T'' ⟶ T') (hl : l ≫ a' = a'') [HasPullback π a] [HasPullback π a']
    [HasPullback π a''] :
    pullback.mapSnd π a' a'' l hl ≫ pullback.mapSnd π a a' k hk =
      pullback.mapSnd π a a'' (l ≫ k) (by rw [Category.assoc, hk, hl]) := by
  ext <;> simp

/-- The section of `pullback.snd π a` induced by a lift `s` of `a` through `π`: its first
projection is `s` and its second projection is the identity of `T`. -/
noncomputable def pullbackSection (π : Y ⟶ S) (a : T ⟶ S) (s : T ⟶ Y) (hs : s ≫ π = a)
    [HasPullback π a] : T ⟶ pullback π a :=
  pullback.lift s (𝟙 T) (by simp [hs])

/-- The first projection of the section induced by a lift `s` is `s`. -/
@[reassoc (attr := simp)]
theorem pullbackSection_fst (π : Y ⟶ S) (a : T ⟶ S) (s : T ⟶ Y) (hs : s ≫ π = a) [HasPullback π a] :
    pullbackSection π a s hs ≫ pullback.fst π a = s :=
  pullback.lift_fst _ _ _

/-- The section induced by a lift is a section of the second projection. -/
@[reassoc (attr := simp)]
theorem pullbackSection_snd (π : Y ⟶ S) (a : T ⟶ S) (s : T ⟶ Y) (hs : s ≫ π = a) [HasPullback π a] :
    pullbackSection π a s hs ≫ pullback.snd π a = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- Naturality of `pullbackSection` across `pullback.mapSnd`: base change along `k` carries the
section induced by the lift `k ≫ s` of `a'` to `k` followed by the section induced by `s`. -/
@[reassoc]
theorem pullbackSection_comp_mapSnd (π : Y ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S) (k : T' ⟶ T)
    (hk : k ≫ a = a') (s : T ⟶ Y) (hs : s ≫ π = a) [HasPullback π a] [HasPullback π a'] :
    pullbackSection π a' (k ≫ s) (by rw [Category.assoc, hs, hk]) ≫ pullback.mapSnd π a a' k hk =
      k ≫ pullbackSection π a s hs := by
  ext <;> simp

end CategoryTheory.Limits
