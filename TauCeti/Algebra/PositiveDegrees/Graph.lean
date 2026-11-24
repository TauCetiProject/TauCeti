/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
public import TauCeti.Algebra.PositiveDegrees.Map
import TauCeti.Data.Set.Prod

/-!
# Positive degrees on swapped graphs

The image of an allowed exponent `n` under `n ↦ (f n, n)` has the same numerical
degree as `n`. The cutoffs are the images of the original cutoffs, and both
inclusion and second-coordinate projection have identity cutoff modulus.
The second coordinate retains the original exponent even when `f` has a kernel.

Adapted from `Mei/Algebra/PositiveDegrees/Graph.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegrees

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  (d : PositiveDegrees N) (f : N →+ M)

/-- Positive degrees on the image of `n ↦ (f n, n)`, with degree read from
the second coordinate. -/
def swappedGraph : PositiveDegrees (M × N) where
  monoid := d.monoid.map (f.prod (AddMonoidHom.id N))
  degree := d.degree.comp (AddMonoidHom.snd M N)
  degree_pos := by
    rintro _ ⟨n, hn, rfl⟩ hne
    exact d.degree_pos hn (by rintro rfl; exact hne (by simp))
  finite_le k := by
    apply ((d.finite_cutoff k).image (fun n => (f n, n))).subset
    rintro x ⟨hx, hk⟩
    have h := (Set.mem_image_prodMk_self_snd_iff f d.monoid x).mp hx
    exact (Set.mem_image_prodMk_self_snd_iff f (d.cutoff k) x).mpr ⟨d.mem_cutoff.mpr ⟨h.1, hk⟩, h.2⟩

/-- An allowed graph exponent has its first coordinate determined by its second. -/
@[simp]
theorem mem_swappedGraph_monoid (x : M × N) :
    x ∈ (d.swappedGraph f).monoid ↔ x.2 ∈ d.monoid ∧ x.1 = f x.2 :=
  Set.mem_image_prodMk_self_snd_iff f d.monoid x

/-- The graph monoid is saturated exactly when the source monoid is saturated, provided
nonzero natural multiples are injective in the first coordinate. -/
theorem nsmulSaturated_swappedGraph_monoid [HasUniqueDiv M] :
    (d.swappedGraph f).monoid.NSMulSaturated ↔ d.monoid.NSMulSaturated :=
  d.monoid.nsmulSaturated_map_prod_id f

/-- The graph degree is the degree of the second coordinate. -/
@[simp]
theorem swappedGraph_degree (x : M × N) :
    (d.swappedGraph f).degree x = d.degree x.2 := (rfl)

/-- Inclusion into the graph preserves cutoffs with identity modulus. -/
def swappedGraphMap : PositiveDegreeMap d (d.swappedGraph f) :=
  PositiveDegreeMap.ofBound (f.prod (AddMonoidHom.id N))
    (by
      intro n hn
      simpa only [AddMonoidHom.prod_apply, AddMonoidHom.id_apply, mem_swappedGraph_monoid,
        and_true] using hn)
    1 (by intro n _; simp)

/-- Graph inclusion pairs each mapped exponent with the original exponent. -/
@[simp]
theorem swappedGraphMap_apply (n : N) : d.swappedGraphMap f n = (f n, n) := by
  simp only [swappedGraphMap, PositiveDegreeMap.ofBound_apply, AddMonoidHom.prod_apply,
    AddMonoidHom.id_apply]

/-- Graph inclusion has the identity cutoff modulus. -/
@[simp]
theorem swappedGraphMap_modulus (k : ℕ) : (d.swappedGraphMap f).modulus k = k := by
  rw [swappedGraphMap, PositiveDegreeMap.ofBound_modulus, one_mul]

/-- Membership in a graph inclusion image is determined by the second coordinate
and the graph equation. -/
theorem mem_image_swappedGraphMap (s : Set N) (x : M × N) :
    x ∈ d.swappedGraphMap f '' s ↔ x.2 ∈ s ∧ x.1 = f x.2 := by
  have hmap : (d.swappedGraphMap f : N → M × N) = fun n => (f n, n) :=
    funext (d.swappedGraphMap_apply f)
  rw [hmap]
  exact Set.mem_image_prodMk_self_snd_iff f s x

/-- Graph cutoffs are exactly images of the original cutoffs under graph inclusion. -/
theorem swappedGraph_cutoff (k : ℕ) :
    (d.swappedGraph f).cutoff k = d.swappedGraphMap f '' d.cutoff k := by
  ext x
  simp only [mem_cutoff, mem_swappedGraph_monoid, swappedGraph_degree, mem_image_swappedGraphMap]
  exact and_right_comm

/-- Projection from the allowed graph exponents preserves cutoffs with identity modulus. -/
def swappedGraphProjection : PositiveDegreeMap (d.swappedGraph f) d :=
  PositiveDegreeMap.ofBound (AddMonoidHom.snd M N)
    (by
      intro x hx
      rw [AddMonoidHom.coe_snd]
      exact ((d.mem_swappedGraph_monoid f x).mp hx).1)
    1 (by intro x _; simp)

/-- Projection reads the original exponent in the second coordinate. -/
@[simp]
theorem swappedGraphProjection_apply (x : M × N) : d.swappedGraphProjection f x = x.2 := by
  simp only [swappedGraphProjection, PositiveDegreeMap.ofBound_apply, AddMonoidHom.coe_snd]

/-- Graph projection has the identity cutoff modulus. -/
@[simp]
theorem swappedGraphProjection_modulus (k : ℕ) : (d.swappedGraphProjection f).modulus k = k := by
  rw [swappedGraphProjection, PositiveDegreeMap.ofBound_modulus, one_mul]

/-- Projecting after graph inclusion gives the identity positive degree map. -/
@[simp]
theorem swappedGraphProjection_comp_swappedGraphMap :
    (d.swappedGraphProjection f).comp (d.swappedGraphMap f) = PositiveDegreeMap.id d := by
  apply PositiveDegreeMap.ext
  · intro n
    simp only [PositiveDegreeMap.comp_apply, swappedGraphProjection_apply, swappedGraphMap_apply,
      PositiveDegreeMap.id_apply]
  · intro k
    simp only [PositiveDegreeMap.comp_modulus, swappedGraphProjection_modulus,
      swappedGraphMap_modulus, PositiveDegreeMap.id_modulus]

/-- On allowed graph exponents, inclusion also inverts the projection. -/
theorem swappedGraphMap_swappedGraphProjection_of_mem {x : M × N}
    (hx : x ∈ (d.swappedGraph f).monoid) :
    d.swappedGraphMap f (d.swappedGraphProjection f x) = x := by
  simp only [swappedGraphProjection_apply, swappedGraphMap_apply]
  exact Prod.ext ((d.mem_swappedGraph_monoid f x).mp hx).2.symm rfl

end TauCeti.PositiveDegrees
