/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Topology.Sets.Opens

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Lattice.Prod

/-!
# Mayer–Vietoris induction on open sets

A property of open sets holds everywhere if it holds on an intersection-stable basis,
passes from two opens and their intersection to their union, and passes to countable
disjoint unions. This principle applies to cohomological comparison and duality maps.

The topological ingredient is a cover by finite unions of basis members, with disjoint
members in each of three residue classes. It comes from finite basis covers of the compact
shells of an exhaustion. Intersections of disjoint families remain disjoint families after
reindexing, so no continuity assumption for increasing unions is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 18,
  proof of the de Rham theorem (Theorem 18.14).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §5,
  the Mayer–Vietoris argument for Poincaré duality.

The construction uses Mathlib's `CompactExhaustion` and finite subcover API.
-/

public section

open Set TopologicalSpace

namespace TopologicalSpace.Opens.IsBasis

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] {B : Set (Opens X)}

/-- Every open set has a countable cover by finite unions of basis members, in which
members separated by at least three indices are disjoint. In particular, each residue
class modulo three is a disjoint family. -/
theorem exists_nat_cover_finite_sup (hB : Opens.IsBasis B) (U : Opens X) :
    ∃ s : ℕ → Finset (Opens X), (∀ n V, V ∈ s n → V ∈ B) ∧
      (∀ i j, i + 3 ≤ j → Disjoint ((s i).sup id) ((s j).sup id)) ∧
      (⨆ n, (s n).sup id) = U := by
  classical
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let K := (CompactExhaustion.choice U).shiftr
  let C (n : ℕ) : Set X := Subtype.val '' K n
  let V (n : ℕ) : Opens X :=
    ⟨Subtype.val '' interior (K n), U.isOpen.isOpenMap_subtype_val _ isOpen_interior⟩
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCV (n : ℕ) : C n ⊆ V (n + 1) := image_mono (K.subset_interior_succ n)
  have hVC (n : ℕ) : (V n : Set X) ⊆ C n := image_mono interior_subset
  have hmono {i j : ℕ} (hij : i ≤ j) : C i ⊆ C j := image_mono (K.subset hij)
  -- shiftr prepends the empty set, so the first shell also covers the innermost points.
  have hKzero : K 0 = ∅ := rfl
  have hzero : C 0 = ∅ := by simp only [C, hKzero, image_empty]
  let W (n : ℕ) : Opens X :=
    ⟨(V (n + 2) : Set X) \ C (n - 1), (V (n + 2)).isOpen.sdiff (hC (n - 1)).isClosed⟩
  have hshell (n : ℕ) : C (n + 1) \ (V n : Set X) ⊆ W n := by
    intro x hx
    refine ⟨hCV (n + 1) hx.1, ?_⟩
    cases n with
    | zero => simp [hzero]
    | succ n => exact fun hxC ↦ hx.2 (hCV n hxC)
  choose s hsB hsK hsW using fun n ↦
    hB.exists_finset_sup_le_of_isCompact ((hC (n + 1)).diff (V n).isOpen) (hshell n)
  refine ⟨s, hsB, ?_, ?_⟩
  · intro i j hij
    apply Disjoint.mono (hsW i) (hsW j)
    apply Opens.coe_disjoint.mp
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxj.2 (hmono (by omega : i + 2 ≤ j - 1) (hVC (i + 2) hxi.1))
  · apply le_antisymm
    · exact iSup_le fun n x hx ↦ by
        obtain ⟨y, _, rfl⟩ := (hsW n hx).1
        exact y.2
    · intro x hx
      let y : U := ⟨x, hx⟩
      have hpos : 0 < K.find y := by
        have h := K.mem_find y
        by_contra hnot
        have hz : K.find y = 0 := by omega
        simp only [hz, hKzero, notMem_empty] at h
      have hyC : x ∈ C (K.find y - 1 + 1) := by
        exact ⟨y, by simpa [Nat.sub_add_cancel hpos] using K.mem_find y, rfl⟩
      have hyV : x ∉ V (K.find y - 1) := by
        rintro ⟨z, hz, heq⟩
        have hzy : z = y := Subtype.ext heq
        subst z
        have hle := K.mem_iff_find_le.mp (interior_subset hz)
        omega
      exact Opens.mem_iSup.mpr ⟨K.find y - 1, hsK _ ⟨hyC, hyV⟩⟩

end TopologicalSpace.Opens.IsBasis

namespace TauCeti

/-- **Mayer–Vietoris induction.** A property of opens in a second-countable locally compact
Hausdorff space holds on every open if it holds on an intersection-stable basis and on the
empty set, is preserved by binary unions when it holds on the intersection, and is preserved
by countable disjoint unions. No hypothesis about increasing unions is required. -/
theorem mayerVietoris_induction {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] (P : Opens X → Prop)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hB_inf : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (hbot : P ⊥) (hbase : ∀ U ∈ B, P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens X, (∀ i j, i ≠ j → Disjoint (s i) (s j)) →
      (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U, P U := by
  classical
  -- First handle finite unions of basis members, including their intersections.
  have hbase_fin (s : Finset (Opens X)) (hs : ∀ V ∈ s, V ∈ B) :
      ∀ U ∈ B, P (U ⊓ s.sup id) := by
    induction s using Finset.induction_on with
    | empty => simpa using fun U (_ : U ∈ B) ↦ hbot
    | @insert V s hVs ih =>
      intro U hU
      have hV := hs V (Finset.mem_insert_self V s)
      have hs' : ∀ W ∈ s, W ∈ B := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      simp only [Finset.sup_insert, id_eq, inf_sup_left]
      apply hsup _ _ (hbase _ (hB_inf U hU V hV)) (ih hs' U hU)
      simpa [inf_assoc, inf_left_comm, inf_comm] using ih hs' (U ⊓ V)
        (hB_inf U hU V hV)
  have hfin (s : Finset (Opens X)) (hs : ∀ V ∈ s, V ∈ B) : P (s.sup id) := by
    induction s using Finset.induction_on with
    | empty => simpa using hbot
    | @insert V s hVs ih =>
      have hV := hs V (Finset.mem_insert_self V s)
      have hs' : ∀ W ∈ s, W ∈ B := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      simpa only [Finset.sup_insert, id_eq] using
        hsup V (s.sup id) (hbase V hV) (ih hs') (hbase_fin s hs' V hV)
  let F (U : Opens X) : Prop :=
    ∃ s : Finset (Opens X), (∀ V ∈ s, V ∈ B) ∧ s.sup id = U
  have hFP {U : Opens X} (hU : F U) : P U := by
    obtain ⟨s, hs, rfl⟩ := hU
    exact hfin s hs
  have hF_inf {U V : Opens X} (hU : F U) (hV : F V) : F (U ⊓ V) := by
    obtain ⟨s, hs, rfl⟩ := hU
    obtain ⟨t, ht, rfl⟩ := hV
    refine ⟨(s ×ˢ t).image (fun p ↦ p.1 ⊓ p.2), ?_, ?_⟩
    · intro W hW
      obtain ⟨⟨U, V⟩, hp, rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨hU, hV⟩ := Finset.mem_product.mp hp
      exact hB_inf U (hs U hU) V (ht V hV)
    · simpa only [Finset.sup_image, Function.comp_def, id_eq] using
        (Finset.sup_inf_sup s t id id).symm
  -- Disjoint countable unions of finite basis unions still have the property.
  -- Their intersections have the same form, indexed by pairs of natural numbers.
  let D (U : Opens X) : Prop := ∃ s : ℕ → Opens X,
    Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (∀ n, F (s n)) ∧ iSup s = U
  have hDP {U : Opens X} (hU : D U) : P U := by
    obtain ⟨s, hs, hF, rfl⟩ := hU
    exact hdisjoint s hs (fun n ↦ hFP (hF n))
  have hD_inf {U V : Opens X} (hU : D U) (hV : D V) : D (U ⊓ V) := by
    obtain ⟨s, hs, hFs, rfl⟩ := hU
    obtain ⟨t, ht, hFt, rfl⟩ := hV
    let f (p : ℕ × ℕ) := s p.1 ⊓ t p.2
    refine ⟨f ∘ Nat.unpair, ?_, fun n ↦ hF_inf (hFs _) (hFt _), ?_⟩
    · intro i j hij
      by_cases hfst : (Nat.unpair i).1 = (Nat.unpair j).1
      · have hsnd : (Nat.unpair i).2 ≠ (Nat.unpair j).2 := by
          intro heq
          exact hij (Nat.pairEquiv.symm.injective (Prod.ext hfst heq))
        exact Disjoint.mono inf_le_right inf_le_right (ht hsnd)
      · exact Disjoint.mono inf_le_left inf_le_left (hs hfst)
    · rw [Function.comp_def, Nat.surjective_unpair.iSup_comp]
      exact iSup_inf_iSup.symm
  -- Three disjoint families suffice for the shell cover. All intersections needed
  -- by the two binary Mayer–Vietoris steps are covered by hD_inf.
  intro U
  obtain ⟨s, hsB, hsdisj, hsU⟩ := hB.exists_nat_cover_finite_sup U
  let A (r : ℕ) : Opens X := ⨆ n, (s (3 * n + r)).sup id
  have hDA (r : ℕ) : D (A r) := by
    refine ⟨fun n ↦ (s (3 * n + r)).sup id, ?_, fun n ↦ ⟨_, hsB _, rfl⟩, rfl⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hsdisj _ _ (by omega)
    · exact (hsdisj _ _ (by omega)).symm
  have hcover : (A 0 ⊔ A 1) ⊔ A 2 = U := by
    rw [← hsU]
    apply le_antisymm
    · exact sup_le (sup_le (iSup_mono' fun n ↦ ⟨_, le_rfl⟩)
        (iSup_mono' fun n ↦ ⟨_, le_rfl⟩)) (iSup_mono' fun n ↦ ⟨_, le_rfl⟩)
    · apply iSup_le
      intro n
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h | h | h
      · apply le_sup_of_le_left
        apply le_sup_of_le_left
        have hn : 3 * (n / 3) + 0 = n := by omega
        exact le_iSup_of_le (n / 3) (by rw [hn])
      · apply le_sup_of_le_left
        apply le_sup_of_le_right
        have hn : 3 * (n / 3) + 1 = n := by omega
        exact le_iSup_of_le (n / 3) (by rw [hn])
      · apply le_sup_of_le_right
        have hn : 3 * (n / 3) + 2 = n := by omega
        exact le_iSup_of_le (n / 3) (by rw [hn])
  rw [← hcover]
  apply hsup _ _ (hsup _ _ (hDP (hDA 0)) (hDP (hDA 1))
    (hDP (hD_inf (hDA 0) (hDA 1)))) (hDP (hDA 2))
  rw [inf_sup_right]
  exact hsup _ _ (hDP (hD_inf (hDA 0) (hDA 2)))
    (hDP (hD_inf (hDA 1) (hDA 2)))
    (hDP (hD_inf (hD_inf (hDA 0) (hDA 2)) (hD_inf (hDA 1) (hDA 2))))

end TauCeti
