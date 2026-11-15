/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Topology.Sets.Opens

import TauCeti.Order.SupClosed

/-!
# Mayer–Vietoris induction on open sets

In a second-countable locally compact Hausdorff space, a property of open sets holds on
every open set if it holds on the empty set and on an intersection-stable basis, passes
from two opens and their intersection to their union, and passes to countable disjoint unions.
This principle applies to cohomological comparison and duality maps.

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
  let K₀ := CompactExhaustion.choice U
  let K := K₀.shiftr
  let C (n : ℕ) : Set X := Subtype.val '' K n
  let V (n : ℕ) : Opens X :=
    ⟨Subtype.val '' interior (K n), U.isOpen.isOpenMap_subtype_val _ isOpen_interior⟩
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCV (n : ℕ) : C n ⊆ V (n + 1) := image_mono (K.subset_interior_succ n)
  have hVC (n : ℕ) : (V n : Set X) ⊆ C n := image_mono interior_subset
  have hmono {i j : ℕ} (hij : i ≤ j) : C i ⊆ C j := image_mono (K.subset hij)
  -- shiftr prepends the empty set, so the first shell also covers the innermost points.
  have hzero : C 0 = ∅ := image_empty Subtype.val
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
      have hy := K₀.mem_sdiff_shiftr_find y
      have hyC : x ∈ C (K₀.find y + 1) := ⟨y, hy.1, rfl⟩
      have hyV : x ∉ V (K₀.find y) := by
        rintro ⟨z, hz, heq⟩
        have hzy : z = y := Subtype.ext heq
        subst z
        exact hy.2 (interior_subset hz)
      exact Opens.mem_iSup.mpr ⟨K₀.find y, hsK _ ⟨hyC, hyV⟩⟩

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
  let F (U : Opens X) : Prop :=
    ∃ s : Finset (Opens X), (∀ V ∈ s, V ∈ B) ∧ s.sup id = U
  have hFP {U : Opens X} (hU : F U) : P U := by
    obtain ⟨s, hs, rfl⟩ := hU
    exact finset_sup_of_inf_closed P (fun _ hU _ hV ↦ hB_inf _ hU _ hV)
      hbot hbase hsup s hs
  have hF_inf : InfClosed {U | F U} := by
    rintro U ⟨s, hs, rfl⟩ V ⟨t, ht, rfl⟩
    exact InfClosed.exists_finset_sup_inf (fun _ hU _ hV ↦ hB_inf _ hU _ hV) hs ht
  -- Disjoint countable unions of finite basis unions still have the property.
  -- Their intersections have the same form, indexed by pairs of natural numbers.
  let D (U : Opens X) : Prop := ∃ s : ℕ → Opens X,
    Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (∀ n, F (s n)) ∧ iSup s = U
  have hDP {U : Opens X} (hU : D U) : P U := by
    obtain ⟨s, hs, hF, rfl⟩ := hU
    exact hdisjoint s hs (fun n ↦ hFP (hF n))
  have hD_inf : InfClosed {U | D U} := by
    rintro U ⟨s, hs, hFs, rfl⟩ V ⟨t, ht, hFt, rfl⟩
    exact hF_inf.exists_disjoint_iSup_inf hs ht hFs hFt
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
      have hle : (s n).sup id ≤ A (n % 3) := by
        have hn : 3 * (n / 3) + n % 3 = n := by omega
        exact le_iSup_of_le (n / 3) (by rw [hn])
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h | h | h
      · exact hle.trans (by rw [h]; exact le_sup_of_le_left le_sup_left)
      · exact hle.trans (by rw [h]; exact le_sup_of_le_left le_sup_right)
      · exact hle.trans (by rw [h]; exact le_sup_right)
  rw [← hcover]
  apply hsup _ _ (hsup _ _ (hDP (hDA 0)) (hDP (hDA 1))
    (hDP (hD_inf (hDA 0) (hDA 1)))) (hDP (hDA 2))
  rw [inf_sup_right]
  exact hsup _ _ (hDP (hD_inf (hDA 0) (hDA 2)))
    (hDP (hD_inf (hDA 1) (hDA 2)))
    (hDP (hD_inf (hD_inf (hDA 0) (hDA 2)) (hD_inf (hDA 1) (hDA 2))))

end TauCeti
