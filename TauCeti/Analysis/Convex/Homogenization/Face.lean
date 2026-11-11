/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Homogenization
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

/-!
# Exposed faces and homogenization

Intersecting a closed convex set with a nonempty affine zero slice commutes
with closed homogenization. Consequently, nonempty exposed faces homogenize
to faces of the closed homogenized cone, including its height-zero directions.
`PointedCone.IsFaceOf.lineal_congr` then shows that a nonempty
exposed face has the same recession lineality as its ambient closed convex set.

Adapted from `Mei/Geometry/Convex/Homogenization/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
The zero-slice statements use an arbitrary continuous linear functional on the
product, without introducing an affine-functional homogenization API.
-/

public section

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

namespace Convex

/-- Intersecting a closed convex base with a nonempty affine zero slice commutes
with actual homogenization, including at height zero. -/
theorem homogenization_inter_ker_eq {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (f : (V × ℝ) →L[ℝ] ℝ)
    (hne : {x ∈ P | f (x, 1) = 0}.Nonempty) :
    homogenization {x ∈ P | f (x, 1) = 0} = homogenization P ⊓
      PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap) := by
  let D := homogenization P ⊓
    PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap)
  have hDclosed : IsClosed (D : Set (V × ℝ)) :=
    (isClosed_homogenization P).inter
      (isClosed_eq f.continuous continuous_const)
  have hslice : {x : V | (x, (1 : ℝ)) ∈ D} = {x ∈ P | f (x, 1) = 0} := by
    ext x
    simp only [D, Set.mem_ofPred_eq, Submodule.mem_inf, PointedCone.mem_ofSubmodule_iff,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      hconv.mem_homogenization_one_iff hclosed]
  have hDne : {x : V | (x, (1 : ℝ)) ∈ D}.Nonempty := by rwa [hslice]
  have hrec := D.homogenization_slice_one hDclosed
    (fun z hz => homogenization_height_nonneg hz.1) hDne
  rwa [hslice] at hrec

/-- A nonpositive affine support cuts out a genuine cone face after actual homogenization. -/
theorem homogenization_inter_ker_isFaceOf {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (f : (V × ℝ) →L[ℝ] ℝ) (hg : ∀ x ∈ P, f (x, 1) ≤ 0)
    (hne : {x ∈ P | f (x, 1) = 0}.Nonempty) :
    (homogenization {x ∈ P | f (x, 1) = 0}).IsFaceOf (homogenization P) := by
  rw [hconv.homogenization_inter_ker_eq hclosed f hne]
  have hf : homogenization P ≤ (PointedCone.positive ℝ ℝ).comap (-f.toLinearMap) :=
    (homogenization_le_iff (isClosed_le continuous_const (-f).continuous)).mpr
      (fun x hx => neg_nonneg.mpr (hg x hx))
  have hface := PointedCone.isFaceOf_inf_ker (φ := -f.toLinearMap) (fun z hz => hf hz)
  have hker : LinearMap.ker (-f.toLinearMap) =
      LinearMap.ker f.toLinearMap := by ext z; simp
  rwa [hker] at hface

end Convex

namespace IsExposed

/-- Every nonempty exposed face of a closed convex set homogenizes to a face
of its actual closed homogenization. -/
theorem homogenization_isFaceOf {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.homogenization F).IsFaceOf (Set.homogenization P) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨l, hl⟩ := hF ⟨p, hp⟩
  have hpmax : p ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by rwa [← hl]
  let f : (V × ℝ) →L[ℝ] ℝ :=
    l.comp (ContinuousLinearMap.fst ℝ V ℝ) - (l p) • ContinuousLinearMap.snd ℝ V ℝ
  have hg : ∀ x ∈ P, f (x, 1) ≤ 0 := by
    intro x hx
    simpa [f] using sub_nonpos.mpr (hpmax.2 x hx)
  have hzero : F = {x ∈ P | f (x, 1) = 0} := by
    ext x
    rw [hl]
    constructor
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, ?_⟩
      simpa [f] using sub_eq_zero.mpr
        (le_antisymm (hpmax.2 x hx) (hmax p hpmax.1))
    · rintro ⟨hx, hzero⟩
      have heq : l x = l p := sub_eq_zero.mp (by simpa [f] using hzero)
      exact ⟨hx, fun y hy => (hpmax.2 y hy).trans_eq heq.symm⟩
  rw [hzero]
  exact hconv.homogenization_inter_ker_isFaceOf hclosed f hg (hzero ▸ ⟨p, hp⟩)

/-- Every nonempty exposed face of a closed convex set has the same lineality
space, measured by the lineality of its recession cone.

This follows from `PointedCone.IsFaceOf.lineal_congr` applied to
the actual homogenizations; no polyhedral or finite-dimensional hypothesis is needed. -/
theorem lineal_recessionCone_eq {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.recessionCone ℝ F).lineal = (Set.recessionCone ℝ P).lineal := by
  rw [(hF.convex hconv).lineal_recessionCone_eq_comap hne (hF.isClosed hclosed),
    hconv.lineal_recessionCone_eq_comap (hne.mono hF.subset) hclosed,
    (hF.homogenization_isFaceOf hconv hclosed hne).lineal_congr]

end IsExposed
