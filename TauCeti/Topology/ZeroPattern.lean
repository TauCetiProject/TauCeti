/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Separation.Basic

/-!
# Coordinate zero-pattern strata

For a subset `A` of an index type, the corresponding zero-pattern stratum consists of families
that vanish exactly on `A`, paired with an unrestricted second component. This file records the
product description of these strata, their local closedness when only finitely many coordinates
are required to be nonzero, and their closure when zero is not isolated.

## Main declarations

* `TauCeti.zeroPatternSet`: the coordinate stratum with zero set exactly `A`.
* `TauCeti.isLocallyClosed_zeroPatternSet`: a zero-pattern stratum with finitely many nonzero
  coordinates is locally closed.
* `TauCeti.closure_zeroPatternSet`: its closure allows additional coordinates to vanish.
* `TauCeti.zeroPatternSetHomeomorph`: its nonzero coordinates give product coordinates.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {α β K : Type*}

variable (α β K) in
/-- The coordinate stratum attached to a subset `A` of an index type: precisely those pairs whose
first coordinates vanish on `A` and nowhere else. The second component is unrestricted. -/
def zeroPatternSet [Zero K] (A : Set α) : Set ((α → K) × β) :=
  {z | ∀ a, z.1 a = 0 ↔ a ∈ A}

/-- A coordinate pair belongs to the stratum attached to `A` exactly when its first coordinate
vanishes precisely on `A`. -/
@[simp]
theorem mem_zeroPatternSet [Zero K] {A : Set α} {z : (α → K) × β} :
    z ∈ zeroPatternSet α β K A ↔ ∀ a, z.1 a = 0 ↔ a ∈ A :=
  Iff.rfl

/-- The coordinate stratum is a product of single-coordinate conditions with an unrestricted
second factor. -/
theorem zeroPatternSet_eq_pi_prod [Zero K] (A : Set α) :
    zeroPatternSet α β K A =
      (Set.pi Set.univ fun a ↦ {z : K | z = 0 ↔ a ∈ A}) ×ˢ Set.univ := by
  ext z
  simp

variable (α β K) in
/-- A zero-pattern stratum is the space of nonzero coordinates outside its zero set, together
with its unrestricted second factor. This description retains the subspace topology. -/
noncomputable def zeroPatternSetHomeomorph [Zero K] [TopologicalSpace K] [TopologicalSpace β]
    (A : Set α) :
    zeroPatternSet α β K A ≃ₜ (({a : α // a ∉ A} → {z : K // z ≠ 0}) × β) := by
  classical
  exact {
    toFun z := (fun a ↦ ⟨z.1.1 a.1, fun hz ↦ a.2 ((z.2 a.1).mp hz)⟩, z.1.2)
    invFun w := ⟨(fun a ↦ if ha : a ∈ A then 0 else (w.1 ⟨a, ha⟩).1, w.2), fun a ↦ by
      by_cases ha : a ∈ A <;> simp [ha, (w.1 _).2]⟩
    left_inv z := by
      ext a
      · by_cases ha : a ∈ A <;> simp [ha, (z.2 a).mpr]
      · rfl
    right_inv w := by
      ext a
      · simp [a.2]
      · rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by
      refine .subtype_mk (.prodMk (continuous_pi fun a ↦ ?_) continuous_snd) _
      split_ifs <;> fun_prop }

/-- The homeomorphism retains each coordinate outside the prescribed zero set. -/
@[simp]
theorem val_zeroPatternSetHomeomorph_fst_apply [Zero K] [TopologicalSpace K]
    [TopologicalSpace β] {A : Set α} (z : zeroPatternSet α β K A) (a : {a : α // a ∉ A}) :
    ((zeroPatternSetHomeomorph α β K A z).1 a).1 = z.1.1 a.1 := by
  simp [zeroPatternSetHomeomorph]

/-- The unrestricted factor is unchanged by the zero-pattern homeomorphism. -/
@[simp]
theorem zeroPatternSetHomeomorph_snd_apply [Zero K] [TopologicalSpace K] [TopologicalSpace β]
    {A : Set α} (z : zeroPatternSet α β K A) :
    (zeroPatternSetHomeomorph α β K A z).2 = z.1.2 := by
  simp [zeroPatternSetHomeomorph]

/-- The inverse fills the prescribed zero coordinates with zero. -/
@[simp]
theorem zeroPatternSetHomeomorph_symm_fst_apply_of_mem [Zero K] [TopologicalSpace K]
    [TopologicalSpace β] {A : Set α} (w : ({a : α // a ∉ A} → {z : K // z ≠ 0}) × β) {a : α}
    (ha : a ∈ A) :
    ((zeroPatternSetHomeomorph α β K A).symm w).1.1 a = 0 := by
  simp [zeroPatternSetHomeomorph, ha]

/-- Outside the zero set, the inverse restores the retained coordinate. -/
@[simp]
theorem zeroPatternSetHomeomorph_symm_fst_apply_of_notMem [Zero K] [TopologicalSpace K]
    [TopologicalSpace β] {A : Set α} (w : ({a : α // a ∉ A} → {z : K // z ≠ 0}) × β) {a : α}
    (ha : a ∉ A) :
    ((zeroPatternSetHomeomorph α β K A).symm w).1.1 a = (w.1 ⟨a, ha⟩).1 := by
  simp [zeroPatternSetHomeomorph, ha]

/-- The inverse also leaves the unrestricted factor unchanged. -/
@[simp]
theorem zeroPatternSetHomeomorph_symm_snd_apply [Zero K] [TopologicalSpace K]
    [TopologicalSpace β] {A : Set α} (w : ({a : α // a ∉ A} → {z : K // z ≠ 0}) × β) :
    ((zeroPatternSetHomeomorph α β K A).symm w).1.2 = w.2 := by
  simp [zeroPatternSetHomeomorph]

/-- A coordinate stratum is locally closed when only finitely many first coordinates are required
to be nonzero. -/
theorem isLocallyClosed_zeroPatternSet [Zero K] [TopologicalSpace K] [T1Space K]
    [TopologicalSpace β] {A : Set α} (hA : Aᶜ.Finite) :
    IsLocallyClosed (zeroPatternSet α β K A) := by
  refine ⟨(Set.pi Aᶜ fun _ ↦ {0}ᶜ) ×ˢ Set.univ, (Set.pi A fun _ ↦ {0}) ×ˢ Set.univ,
    (isOpen_set_pi hA fun _ _ ↦ isOpen_compl_singleton).prod isOpen_univ,
    (isClosed_set_pi fun _ _ ↦ isClosed_singleton).prod isClosed_univ, ?_⟩
  ext z
  simp only [mem_zeroPatternSet, Set.mem_inter_iff, Set.mem_prod, Set.mem_pi, Set.mem_compl_iff,
    Set.mem_singleton_iff, Set.mem_univ, and_true, ← forall_and]
  exact forall_congr' fun a ↦ by tauto

/-- The closure of a coordinate stratum permits additional first coordinates to vanish, while
retaining the coordinates already forced to be zero. -/
theorem closure_zeroPatternSet [Zero K] [TopologicalSpace K] [T1Space K]
    [NeBot (𝓝[≠] (0 : K))] [TopologicalSpace β] (A : Set α) :
    closure (zeroPatternSet α β K A) = {z | ∀ a ∈ A, z.1 a = 0} := by
  rw [zeroPatternSet_eq_pi_prod, closure_prod_eq, closure_pi_set, closure_univ]
  ext z
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, and_true]
  refine ⟨fun hz a ha ↦ by simpa [ha] using hz a, fun hz a ↦ ?_⟩
  by_cases ha : a ∈ A
  · simpa [ha] using hz a ha
  · simp [ha, ← Set.compl_ofPred]

end TauCeti
