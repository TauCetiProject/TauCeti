/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Homogenization.Basic
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

/-!
# Extreme subsets and homogenization

Intersecting a closed convex set with the height-one slice of a closed cone commutes
with homogenization when the intersection is nonempty. In particular, for a closed
convex set `P` and a continuous linear functional `f : (V × ℝ) →L[ℝ] ℝ`,
the homogenization of `{x ∈ P | f (x, 1) = 0}` is the intersection of the homogenization
of `P` with the kernel of `f`, provided that the set `{x ∈ P | f (x, 1) = 0}` is nonempty.
Every nonempty closed convex extreme subset of `P` homogenizes to a cone face.
Every nonempty extreme subset has the same recession lineality as `P`, even when
the subset is neither closed nor convex. These conclusions apply to nonempty exposed faces.

Adapted from `Mei/Geometry/Convex/Homogenization/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
The affine constraint `f (x, 1) = 0` on `V` becomes the homogeneous constraint
`z ∈ LinearMap.ker f.toLinearMap` on `V × ℝ`.
-/

public section

open Set Filter
open scoped Topology

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
  have hslice : {x ∈ P | (x, (1 : ℝ)) ∈ PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap)} =
      {x ∈ P | f (x, 1) = 0} := by
    ext x
    simp only [Set.mem_sep_iff, PointedCone.mem_ofSubmodule_iff, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
  rw [← hslice] at hne ⊢
  exact hconv.homogenization_setOf_mem_eq_inf hclosed
    (C := PointedCone.ofSubmodule (LinearMap.ker f.toLinearMap)) f.isClosed_ker hne

/-- Let `P` be closed and convex and let `f` be a continuous linear functional on `V × ℝ`
with `f (x, 1) ≤ 0` for every `x ∈ P`. If `{x ∈ P | f (x, 1) = 0}` is nonempty, its
homogenization is a face of the homogenization of `P`. -/
theorem isFaceOf_homogenization_setOf_eq_zero {P : Set V}
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

namespace IsExtreme

/-- At positive heights, dehomogenizing a sum gives a point of the open segment
between the dehomogenized summands. Extremality recovers its first endpoint. -/
private theorem mem_homogenization_of_pos {P F : Set V} (hF : IsExtreme ℝ P F)
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hFconv : Convex ℝ F)
    (hFclosed : IsClosed F) {x y : V × ℝ}
    (hx : x ∈ homogenization P) (hy : y ∈ homogenization P)
    (ht : 0 < x.2) (hs : 0 < y.2) (h : x + y ∈ homogenization F) :
    x ∈ homogenization F := by
  obtain ⟨u, t⟩ := x
  obtain ⟨v, s⟩ := y
  simp only at ht hs
  rw [Prod.mk_add_mk] at h
  have hw := add_pos ht hs
  apply (hFconv.mem_homogenization_pos_iff hFclosed ht).2
  apply hF.left_mem_of_mem_openSegment ((hPconv.mem_homogenization_pos_iff hPclosed ht).1 hx)
    ((hPconv.mem_homogenization_pos_iff hPclosed hs).1 hy)
    ((hFconv.mem_homogenization_pos_iff hFclosed hw).1 h)
  rw [mem_openSegment_iff_div]
  refine ⟨t, s, ht, hs, ?_⟩
  simp only [smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

/-- The homogenization of a nonempty closed convex extreme subset is a face of the
homogenization of the ambient closed convex set, including at height zero. -/
theorem isFaceOf_homogenization {P F : Set V} (hF : IsExtreme ℝ P F)
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hFconv : Convex ℝ F)
    (hFclosed : IsClosed F) (hne : F.Nonempty) :
    (homogenization F).IsFaceOf (homogenization P) := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left (homogenization_mono hF.subset)
  intro x y hx hy h
  obtain ⟨p, hp⟩ := hne
  let q : V × ℝ := (p, 1)
  have hq : q ∈ homogenization F := mem_homogenization_one hp
  have hlim : Tendsto (fun ε : ℝ => x + ε • q) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun ε : ℝ => x + ε • q) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply (isClosed_homogenization F).mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpos : 0 < ε := hε
  have hshift := (homogenization F).smul_mem hpos.le hq
  have hamb := homogenization_mono hF.subset hshift
  have hheight (z : V × ℝ) (hz : z ∈ homogenization P) : 0 < (z + ε • q).2 := by
    simpa [q] using add_pos_of_nonneg_of_pos (homogenization_height_nonneg hz) hpos
  apply hF.mem_homogenization_of_pos hPconv hPclosed hFconv hFclosed
    ((homogenization P).add_mem hx hamb) ((homogenization P).add_mem hy hamb)
    (hheight x hx) (hheight y hy)
  rw [add_add_add_comm]
  exact (homogenization F).add_mem h ((homogenization F).add_mem hshift hshift)

/-- A nonempty extreme subset of a closed convex set inherits its recession lineality,
even when the subset itself is neither closed nor convex. -/
theorem lineal_recessionCone_eq {P F : Set V} (hF : IsExtreme ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (recessionCone ℝ F).lineal = (recessionCone ℝ P).lineal := by
  have hle : recessionCone ℝ F ≤ recessionCone ℝ P := fun _ hv =>
    hconv.mem_recessionCone_of_mem_homogenization_zero hclosed
      (homogenization_mono hF.subset (mem_homogenization_zero_of_mem_recessionCone hne hv))
  have hback {v : V} (hv : v ∈ recessionCone ℝ P) (hn : -v ∈ recessionCone ℝ P) :
      v ∈ recessionCone ℝ F := by
    rw [mem_recessionCone]
    intro p hp t ht
    apply hF.left_mem_of_mem_openSegment ((mem_recessionCone.mp hv) p (hF.subset hp) t ht)
      (by simpa only [smul_neg, sub_eq_add_neg] using
        (mem_recessionCone.mp hn) p (hF.subset hp) t ht) hp
      (mem_openSegment_add_sub (𝕜 := ℝ) p (t • v))
  ext v
  simp only [PointedCone.mem_lineal]
  exact ⟨fun h => ⟨hle h.1, hle h.2⟩, fun h => ⟨hback h.1 h.2, hback h.2 (by simpa using h.1)⟩⟩

end IsExtreme

namespace IsExposed

/-- Every nonempty exposed face of a closed convex set homogenizes to a face
of its homogenization. -/
theorem isFaceOf_homogenization {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.homogenization F).IsFaceOf (Set.homogenization P) :=
  hF.isExtreme.isFaceOf_homogenization hconv hclosed (hF.convex hconv) (hF.isClosed hclosed) hne

/-- A nonempty exposed face of a closed convex set and the ambient set have the same
recession-cone lineality space, without polyhedral or finite-dimensional assumptions. -/
theorem lineal_recessionCone_eq {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.recessionCone ℝ F).lineal = (Set.recessionCone ℝ P).lineal :=
  hF.isExtreme.lineal_recessionCone_eq hconv hclosed hne

end IsExposed
