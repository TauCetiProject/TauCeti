/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Homogenization.Basic
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

/-!
# Exposed faces and homogenization

For a closed convex set `P` and a continuous linear functional `f : (V × ℝ) →L[ℝ] ℝ`,
the homogenization of `{x ∈ P | f (x, 1) = 0}` is the intersection of the homogenization
of `P` with the kernel of `f`, provided that the set `{x ∈ P | f (x, 1) = 0}` is nonempty.
In particular, a nonempty exposed face homogenizes to a face of the homogenized cone
and has the same recession lineality as the ambient closed convex set.

Adapted from `Mei/Geometry/Convex/Homogenization/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
The affine constraint `f (x, 1) = 0` on `V` becomes the homogeneous constraint
`z ∈ LinearMap.ker f.toLinearMap` on `V × ℝ`.
-/

public section

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

namespace Convex

/-- For a closed convex set `P` and continuous linear functional `f` on `V × ℝ`,
if `{x ∈ P | f (x, 1) = 0}` is nonempty, its homogenization is the intersection of
the homogenization of `P` with the kernel of `f`. -/
theorem homogenization_setOf_eq_zero_eq_inf_ker {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (f : (V × ℝ) →L[ℝ] ℝ)
    (hne : {x ∈ P | f (x, 1) = 0}.Nonempty) :
    homogenization {x ∈ P | f (x, 1) = 0} = homogenization P ⊓
      PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap) := by
  let D := homogenization P ⊓
    PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap)
  have hDclosed : IsClosed (D : Set (V × ℝ)) := by
    simp only [D, Submodule.coe_inf, PointedCone.coe_ofSubmodule]
    exact (isClosed_homogenization P).inter f.isClosed_ker
  have hslice : {x : V | (x, (1 : ℝ)) ∈ D} = {x ∈ P | f (x, 1) = 0} := by
    ext x
    simp only [D, Set.mem_ofPred_eq, Submodule.mem_inf, PointedCone.mem_ofSubmodule_iff,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      hconv.mem_homogenization_one_iff hclosed]
  have hDne : {x : V | (x, (1 : ℝ)) ∈ D}.Nonempty := by rwa [hslice]
  have hrec := D.homogenization_slice_one hDclosed
    (fun z hz => homogenization_height_nonneg hz.1) hDne
  rwa [hslice] at hrec

/-- Let `P` be closed and convex and let `f` be a continuous linear functional on `V × ℝ`
with `f (x, 1) ≤ 0` for every `x ∈ P`. If `{x ∈ P | f (x, 1) = 0}` is nonempty, its
homogenization is a face of the homogenization of `P`. -/
theorem homogenization_setOf_eq_zero_isFaceOf {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (f : (V × ℝ) →L[ℝ] ℝ) (hg : ∀ x ∈ P, f (x, 1) ≤ 0)
    (hne : {x ∈ P | f (x, 1) = 0}.Nonempty) :
    (homogenization {x ∈ P | f (x, 1) = 0}).IsFaceOf (homogenization P) := by
  rw [hconv.homogenization_setOf_eq_zero_eq_inf_ker hclosed f hne]
  have hmem (z : V × ℝ) :
      z ∈ (PointedCone.positive ℝ ℝ).comap (-f.toLinearMap) ↔ f z ≤ 0 := by
    simp only [PointedCone.mem_comap, PointedCone.mem_positive, LinearMap.neg_apply,
      ContinuousLinearMap.coe_coe, neg_nonneg]
  have hclosedCone : IsClosed ((PointedCone.positive ℝ ℝ).comap (-f.toLinearMap) :
      Set (V × ℝ)) := by
    have heq : ((PointedCone.positive ℝ ℝ).comap (-f.toLinearMap) : Set (V × ℝ)) =
        {z | f z ≤ 0} := Set.ext hmem
    rw [heq]
    exact isClosed_le f.continuous continuous_const
  have hf := (homogenization_le_iff hclosedCone).mpr fun x hx => (hmem (x, 1)).mpr (hg x hx)
  have hface := PointedCone.isFaceOf_inf_ker (C := homogenization P) (φ := -f.toLinearMap)
    fun z hz => by simpa only [PointedCone.mem_comap, PointedCone.mem_positive] using hf hz
  rwa [LinearMap.ker_neg] at hface

end Convex

namespace IsExposed

/-- Every nonempty exposed face of a closed convex set homogenizes to a face
of its homogenization. -/
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
  exact hconv.homogenization_setOf_eq_zero_isFaceOf hclosed f hg (hzero ▸ ⟨p, hp⟩)

/-- A nonempty exposed face of a closed convex set and the ambient set have the same
recession-cone lineality space, without polyhedral or finite-dimensional assumptions. -/
theorem lineal_recessionCone_eq {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.recessionCone ℝ F).lineal = (Set.recessionCone ℝ P).lineal := by
  rw [(hF.convex hconv).lineal_recessionCone_eq_comap hne (hF.isClosed hclosed),
    hconv.lineal_recessionCone_eq_comap (hne.mono hF.subset) hclosed,
    (hF.homogenization_isFaceOf hconv hclosed hne).lineal_congr]

end IsExposed
