/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Collapsing cellular fibres does not change a compact manifold

Let `M` be a compact metric space which is a topological manifold modelled on a
finite-dimensional real normed space `E`. If a cellular subset `X ⊆ M` (`TauCeti.IsCellularSet`)
is collapsed to a point, the result is again `M`. This file states it for maps. If a continuous
surjection `g : M → N` onto a Hausdorff space has `X` as its only fibre with more than one point,
then `M` is homeomorphic to `N`. The homeomorphism can be chosen equal to `g` outside any given
open neighbourhood of `X` (`TauCeti.IsCellularSet.exists_homeomorph`). The same holds when `g`
identifies two distinct points exactly when they lie in a common member of a finite family of
pairwise disjoint cellular sets (`TauCeti.exists_homeomorph_of_isCellularSet`), in particular of
two of them (`TauCeti.IsCellularSet.exists_homeomorph_of_disjoint`).

This is the step of M. Brown's proof of the generalized Schoenflies theorem in which a map of a
sphere onto itself whose only nondegenerate fibres are two cellular sets is turned into a
homeomorphism. Applied to the collapse of the outside of a bicollared sphere onto two poles
(`TauCeti.IsBicollar.exists_collapse`), once its two outer pieces are known to be cellular, it
gives a homeomorphism of the sphere carrying the closure of each complementary domain onto a closed
hemisphere.

The basic step is a factorization (`TauCeti.IsCellularSet.exists_collapse_comp_eq`). Every
continuous map `g` which is constant on `X` factors as `k ∘ c` through the collapse `c` of `X`
(`TauCeti.IsCellularSet.exists_collapse`), with `k` continuous. Since `M` is compact, `c` is a
quotient map, and `c` and `g` identify the same pairs of points of `X`. The collapse fixes every
point outside the chosen neighbourhood of `X`, so `k` agrees with `g` there. Collapsing the
cellular fibres of `g` one at a time, each inside a neighbourhood missing the others, leaves a
continuous bijection from the compact space `M` onto `N`, which is a homeomorphism.

## Main results

* `TauCeti.IsCellularSet.exists_collapse_comp_eq`: a continuous map constant on a cellular set
  factors continuously through its collapse.
* `TauCeti.exists_homeomorph_of_isCellularSet`: a continuous surjection onto a Hausdorff space
  whose nondegenerate fibres lie in finitely many pairwise disjoint cellular sets, each of which
  it collapses, agrees off any neighbourhood of those sets with a homeomorphism.
* `TauCeti.IsCellularSet.exists_homeomorph`: the case of one cellular fibre.
* `TauCeti.IsCellularSet.exists_homeomorph_of_disjoint`: the case of two cellular fibres.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0–2 and the proof of Theorem 5.
-/

public section

open Set Function Topology

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M] [TopologicalSpace N]

namespace TauCeti

/-- **Factoring through the collapse of a cellular set.** Let `M` be a compact metric space which
is a topological manifold modelled on a finite-dimensional real normed space `E`, `X ⊆ M` a
cellular set and `U ⊇ X` open. There is a continuous surjection `c : M → M` collapsing `X` to a
single point, whose other fibres are singletons and which fixes every point outside `U`, such that
every continuous map `g` which is constant on `X` is `k ∘ c` for a continuous `k`. -/
theorem IsCellularSet.exists_collapse_comp_eq {X : Set M} (hX : IsCellularSet E X) {U : Set M}
    (hU : IsOpen U) (hXU : X ⊆ U) :
    ∃ c : M → M, Continuous c ∧ Surjective c ∧ (∀ x y, c x = c y ↔ x = y ∨ x ∈ X ∧ y ∈ X) ∧
      (∀ x ∉ U, c x = x) ∧ ∀ g : M → N, Continuous g → (∀ x ∈ X, ∀ y ∈ X, g x = g y) →
        ∃ k : M → N, Continuous k ∧ k ∘ c = g := by
  obtain ⟨c, hcc, hcs, hcf, hcU⟩ := hX.exists_collapse hU hXU
  have hq : IsQuotientMap (ContinuousMap.mk c hcc) := .of_surjective_continuous hcs hcc
  refine ⟨c, hcc, hcs, hcf, hcU, fun g hg hgX ↦ ?_⟩
  -- `g` is constant on the fibres of `c`, so it descends along the quotient map `c`.
  have hf : FactorsThrough g c := fun x y hxy ↦ by
    rcases (hcf x y).1 hxy with rfl | ⟨hx, hy⟩
    exacts [rfl, hgX x hx y hy]
  exact ⟨hq.lift ⟨g, hg⟩ hf, (hq.lift ⟨g, hg⟩ hf).continuous,
    congrArg DFunLike.coe (hq.lift_comp ⟨g, hg⟩ hf)⟩

/-- **Collapsing finitely many cellular sets.** Let `M` be a compact metric space which is a
topological manifold modelled on a finite-dimensional real normed space `E`, and `X i`, `i ∈ s`,
finitely many pairwise disjoint cellular subsets of `M`, all contained in an open set `U`. If
`g : M → N` is a continuous surjection onto a Hausdorff space which identifies two distinct points
exactly when they lie in a common `X i`, then there is a homeomorphism `h : M ≃ₜ N` equal to `g`
outside `U`. -/
theorem exists_homeomorph_of_isCellularSet [T2Space N] {ι : Type*} (s : Finset ι)
    {X : ι → Set M} (hX : ∀ i ∈ s, IsCellularSet E (X i)) (hXd : (s : Set ι).PairwiseDisjoint X)
    {U : Set M} (hU : IsOpen U) (hXU : ∀ i ∈ s, X i ⊆ U) {g : M → N} (hg : Continuous g)
    (hgs : Surjective g) (hgf : ∀ x y, g x = g y ↔ x = y ∨ ∃ i ∈ s, x ∈ X i ∧ y ∈ X i) :
    ∃ h : M ≃ₜ N, ∀ x ∉ U, h x = g x := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
    -- With no cellular fibres, `g` is a continuous bijection of a compact space onto a Hausdorff
    -- space.
    have hgi : Injective g := fun x y hxy ↦ by simpa using (hgf x y).1 hxy
    exact ⟨(isHomeomorph_iff_continuous_bijective.2 ⟨hg, hgi, hgs⟩).homeomorph g,
      fun _ _ ↦ rfl⟩
  | insert a s ha ih =>
    -- Collapse `X a` inside a neighbourhood `V` missing the other sets `X i`.
    set V := U ∩ (⋃ i ∈ s, X i)ᶜ
    have hcl : IsClosed (⋃ i ∈ s, X i) := isClosed_biUnion_finset fun i hi ↦
      (hX i (Finset.mem_insert_of_mem hi)).isClosed
    have hV : IsOpen V := hU.inter hcl.isOpen_compl
    have hXV : X a ⊆ V := subset_inter (hXU a (Finset.mem_insert_self a s)) <|
      subset_compl_comm.1 <| iUnion₂_subset fun i hi ↦ (hXd (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_self a s) (ne_of_mem_of_not_mem hi ha)).subset_compl_right
    obtain ⟨c, -, hcs, hcf, hcV, hfac⟩ :=
      (hX a (Finset.mem_insert_self a s)).exists_collapse_comp_eq (N := N) hV hXV
    obtain ⟨k, hk, hkc⟩ := hfac g hg fun x hx y hy ↦
      (hgf x y).2 (.inr ⟨a, Finset.mem_insert_self a s, hx, hy⟩)
    have hkc' (x : M) : k (c x) = g x := congrFun hkc x
    -- The collapse fixes the other sets `X i`, and `k` identifies exactly the points of each.
    have hcX {i : ι} (hi : i ∈ s) {x : M} (hx : x ∈ X i) : c x = x :=
      hcV x fun h ↦ h.2 (mem_biUnion hi hx)
    have hkf (y y' : M) : k y = k y' ↔ y = y' ∨ ∃ i ∈ s, y ∈ X i ∧ y' ∈ X i := by
      refine ⟨fun hyy ↦ ?_, ?_⟩
      · obtain ⟨x, rfl⟩ := hcs y
        obtain ⟨x', rfl⟩ := hcs y'
        rw [hkc', hkc', hgf] at hyy
        rcases hyy with rfl | ⟨i, hi, hx, hx'⟩
        · exact .inl rfl
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact .inl ((hcf x x').2 (.inr ⟨hx, hx'⟩))
        · exact .inr ⟨i, hi, by rwa [hcX hi hx], by rwa [hcX hi hx']⟩
      · rintro (rfl | ⟨i, hi, hy, hy'⟩)
        · rfl
        rw [← hcX hi hy, ← hcX hi hy', hkc', hkc', hgf]
        exact .inr ⟨i, Finset.mem_insert_of_mem hi, hy, hy'⟩
    obtain ⟨h, hh⟩ := ih (fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))
      (hXd.subset (by simp)) (fun i hi ↦ hXU i (Finset.mem_insert_of_mem hi)) hk
      (fun z ↦ let ⟨x, hx⟩ := hgs z; ⟨c x, (hkc' x).trans hx⟩) hkf
    refine ⟨h, fun x hx ↦ ?_⟩
    rw [hh x hx, ← hkc', hcV x fun h ↦ hx h.1]

/-- **Collapsing a cellular set does not change a compact manifold.** Let `M` be a compact metric
space which is a topological manifold modelled on a finite-dimensional real normed space `E`,
`X ⊆ M` a cellular set and `U ⊇ X` open. If `g : M → N` is a continuous surjection onto a Hausdorff
space which identifies two distinct points exactly when both lie in `X`, then there is a
homeomorphism `h : M ≃ₜ N` equal to `g` outside `U`. -/
theorem IsCellularSet.exists_homeomorph [T2Space N] {X : Set M} (hX : IsCellularSet E X)
    {U : Set M} (hU : IsOpen U) (hXU : X ⊆ U) {g : M → N} (hg : Continuous g)
    (hgs : Surjective g) (hgf : ∀ x y, g x = g y ↔ x = y ∨ x ∈ X ∧ y ∈ X) :
    ∃ h : M ≃ₜ N, ∀ x ∉ U, h x = g x :=
  exists_homeomorph_of_isCellularSet (Finset.univ : Finset Unit) (X := fun _ ↦ X) (fun _ _ ↦ hX)
    (fun i _ j _ hij ↦ (hij (Subsingleton.elim i j)).elim) hU (fun _ _ ↦ hXU) hg hgs
    (by simpa using hgf)

/-- **Collapsing two disjoint cellular sets does not change a compact manifold.** Let `M` be a
compact metric space which is a topological manifold modelled on a finite-dimensional real normed
space `E`, `A` and `B` disjoint cellular subsets of `M` and `U ⊇ A ∪ B` open. If `g : M → N` is a
continuous surjection onto a Hausdorff space which identifies two distinct points exactly when
both lie in `A` or both lie in `B`, then there is a homeomorphism `h : M ≃ₜ N` equal to `g`
outside `U`. -/
theorem IsCellularSet.exists_homeomorph_of_disjoint [T2Space N] {A B : Set M}
    (hA : IsCellularSet E A) (hB : IsCellularSet E B) (hAB : Disjoint A B) {U : Set M}
    (hU : IsOpen U) (hAU : A ⊆ U) (hBU : B ⊆ U) {g : M → N} (hg : Continuous g)
    (hgs : Surjective g) (hgf : ∀ x y, g x = g y ↔ x = y ∨ x ∈ A ∧ y ∈ A ∨ x ∈ B ∧ y ∈ B) :
    ∃ h : M ≃ₜ N, ∀ x ∉ U, h x = g x := by
  refine exists_homeomorph_of_isCellularSet (Finset.univ : Finset Bool)
    (X := fun b ↦ bif b then B else A) (E := E) (by simp [hA, hB]) ?_ hU (by simp [hAU, hBU]) hg hgs
    (by simpa using hgf)
  rintro (_ | _) - (_ | _) - h
  exacts [(h rfl).elim, hAB, hAB.symm, (h rfl).elim]

end TauCeti
