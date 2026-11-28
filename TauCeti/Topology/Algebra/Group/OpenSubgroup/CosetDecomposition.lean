/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite coset expansions with compact projected support

A function constant on cosets of an open additive subgroup has a finite coset expansion if
its support has compact image under a continuous map that preserves those cosets. The support
itself need not be compact. This is useful for functions on a restricted product that depend
only on a selected set of coordinates.

The result supplies the coset expansion used for Schwartz–Bruhat functions above a set of
places. That statement is `New.IsSchwartzBruhat.eq_sum_cosetIndicator` in [ShortProof],
grh-lean (https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207`,
`src/Lib/Weil/MixedModel/SchwartzBruhat.lean` (Apache 2.0). The argument here uses compactness
of the image in the discrete coset space.
-/

public section

open Function Set

namespace AddSubgroup

variable {V M : Type*} [AddGroup V] [Zero M]

/-- Invariance under a subgroup on the support of a function implies invariance everywhere. -/
theorem add_eq_of_add_eq_on_support (H : AddSubgroup V) {f : V → M}
    (hf : ∀ x ∈ support f, ∀ u ∈ H, f (x + u) = f x) (x : V) {u : V} (hu : u ∈ H) :
    f (x + u) = f x := by
  by_cases hx : f x = 0
  · by_cases hxu : f (x + u) = 0
    · simp [hx, hxu]
    · have h := hf (x + u) hxu (-u) (H.neg_mem hu)
      simp only [add_neg_cancel_right, hx] at h
      exact (hxu h.symm).elim
  · exact hf x hx u hu

end AddSubgroup

namespace OpenAddSubgroup

variable {V M : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommMonoid M]

open scoped Classical in
/-- A function invariant under `H` is a finite sum of coset indicators with coefficients its
values, if its support has compact image under a continuous map preserving the `H`-cosets.
Representatives can all be chosen in the support. No compactness of `H` is required. -/
theorem exists_eq_sum_indicator_sub_mem (H : OpenAddSubgroup V) {f : V → M}
    (hf : ∀ x ∈ support f, ∀ u ∈ H, f (x + u) = f x)
    (p : C(V, V)) (hp : ∀ x, x - p x ∈ H) (hc : IsCompact (p '' support f)) :
    ∃ s : Finset V, (∀ y ∈ s, f y ≠ 0) ∧
      (∀ y ∈ s, ∀ z ∈ s, y - z ∈ H → y = z) ∧
      ∀ x, f x = ∑ y ∈ s, if x - y ∈ H then f y else 0 := by
  classical
  let q : V → V ⧸ H.toAddSubgroup := QuotientAddGroup.mk
  have hq (x y : V) : q x = q y ↔ x - y ∈ H := by
    exact QuotientAddGroup.eq_iff_sub_mem
  have hinv (x y : V) (h : q x = q y) : f x = f y := by
    have hxy := H.toAddSubgroup.add_eq_of_add_eq_on_support hf y ((hq x y).1 h)
    simpa only [add_sub_cancel] using hxy
  let g : V ⧸ H.toAddSubgroup → M := Quotient.lift f fun x y h ↦ hinv x y (Quotient.sound h)
  -- Quotient.lift computes on the class of a representative.
  have hg (x : V) : g (q x) = f x := (rfl)
  have hfinite : (support g).Finite := by
    have hcompact := hc.image (QuotientAddGroup.continuous_mk (N := H.toAddSubgroup))
    refine hcompact.finite_of_discrete.subset ?_
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
    refine ⟨p x, ⟨x, ?_, rfl⟩, ?_⟩
    · exact ha
    · exact (hq x (p x)).2 (hp x) |>.symm
  let t := hfinite.toFinset
  refine ⟨t.image Quotient.out, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    have ha' : g a ≠ 0 := hfinite.mem_toFinset.1 ha
    simpa only [← hg, q, QuotientAddGroup.out_eq'] using ha'
  · intro y hy z hz hyz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hz
    have hab : a = b := by
      simpa only [q, QuotientAddGroup.out_eq'] using (hq a.out b.out).2 hyz
    exact congrArg Quotient.out hab
  · intro x
    rw [Finset.sum_image (fun a _ b _ h ↦ Quotient.out_injective h)]
    have hterm (a : V ⧸ H.toAddSubgroup) :
        (if x - a.out ∈ H then f a.out else 0) = if q x = a then g a else 0 := by
      rw [← hq, ← hg]
      simp only [q, QuotientAddGroup.out_eq']
    simp_rw [hterm]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hg x).symm
    · exact notMem_support.1 (fun h ↦ hx (hfinite.mem_toFinset.2 h))

end OpenAddSubgroup
