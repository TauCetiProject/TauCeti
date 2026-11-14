/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Cutoff
public import TauCeti.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Cutoff averaging on groupoids

A cutoff function averages functions on the objects by summing their values at targets of
arrows with a fixed source. The resulting linear operator fixes arrow-invariant functions
and has arrow-invariant image. Every arrow contributes, including ineffective isotropy.

The source is proper on the inverse image of the topological support of the cutoff. This
also controls the topological support of averaged functions, as needed to preserve
subordination when averaging partitions of unity.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2.

The reindexing of source fibers is `Quiver.Total.finsum_mem_preimage_left_singleton_eq_of_iso`.
-/

public noncomputable section

open CategoryTheory Function Set Topology

namespace TauCeti.Quiver.IsCutoff

variable {C : Type*} [Quiver C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  {c : C → ℝ} (hc : IsCutoff c)

include hc

/-- The cutoff weights have finite support on each source fiber, in sigma coordinates. -/
theorem hasFiniteSupport (x : C) :
    HasFiniteSupport (fun a : Σ y, x ⟶ y ↦ c a.1) := by
  apply hasFiniteSupport_of_finsum_eq_one
  simpa only [Quiver.Total.finsum_mem_preimage_left_singleton] using hc.finsum_eq_one x

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- Average an object function over all arrows from each object, using cutoff weights at their
targets. This is a linear operator, even when source fibers are infinite. -/
def average : (C → A) →ₗ[ℝ] (C → A) where
  toFun f x := ∑ᶠ a : Σ y, x ⟶ y, c a.1 • f a.1
  map_add' f g := by
    ext x
    simp only [Pi.add_apply, smul_add]
    exact finsum_add_distrib ((hc.hasFiniteSupport x).fun_smul_left _)
      ((hc.hasFiniteSupport x).fun_smul_left _)
  map_smul' r f := by
    ext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_comm _ r]
    exact (smul_finsum' r ((hc.hasFiniteSupport x).fun_smul_left _)).symm

/-- The average in source-fiber sigma coordinates. -/
@[simp]
theorem average_apply (f : C → A) (x : C) :
    hc.average f x = ∑ᶠ a : Σ y, x ⟶ y, c a.1 • f a.1 := (rfl)

/-- The average is the sum over actual total arrows with the prescribed source. -/
theorem average_eq_finsum (f : C → A) (x : C) :
    hc.average f x = ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, c a.right • f a.right := by
  rw [average_apply]
  exact (Quiver.Total.finsum_mem_preimage_left_singleton (fun a ↦ c a.right • f a.right) x).symm

/-- Cutoff averaging commutes with a pointwise finitely supported sum of object functions. -/
theorem finsum_average {ι : Type*} (f : ι → C → A)
    (hf : ∀ x, HasFiniteSupport fun i ↦ f i x) (x : C) :
    ∑ᶠ i, hc.average (f i) x = hc.average (fun y ↦ ∑ᶠ i, f i y) x := by
  classical
  let S := (hc.hasFiniteSupport x).toFinset
  calc
    ∑ᶠ i, hc.average (f i) x = ∑ᶠ i, ∑ a ∈ S, c a.1 • f i a.1 :=
      finsum_congr fun i ↦ finsum_smul_eq_sum (hc.hasFiniteSupport x) _
    _ = ∑ a ∈ S, ∑ᶠ i, c a.1 • f i a.1 :=
      finsum_sum_comm S _ fun a _ ↦ (hf a.1).subset fun _ hi ↦ right_ne_zero_of_smul hi
    _ = ∑ a ∈ S, c a.1 • ∑ᶠ i, f i a.1 := by
      simp only [← smul_finsum' _ (hf _)]
    _ = hc.average (fun y ↦ ∑ᶠ i, f i y) x :=
      (finsum_smul_eq_sum (hc.hasFiniteSupport x) _).symm

/-- Averaging fixes a function that takes equal values at the endpoints of every arrow. -/
theorem average_eq_self (f : C → A) (hf : ∀ ⦃x y : C⦄, (x ⟶ y) → f y = f x) :
    hc.average f = f := by
  ext x
  calc
    hc.average f x = ∑ᶠ a : Σ y, x ⟶ y, c a.1 • f x :=
      finsum_congr fun a ↦ congrArg (c a.1 • ·) (hf a.2)
    _ = (∑ᶠ a : Σ y, x ⟶ y, c a.1) • f x :=
      (finsum_smul' (hc.hasFiniteSupport x) (f x)).symm
    _ = f x := by
      have h := hc.finsum_eq_one x
      rw [Quiver.Total.finsum_mem_preimage_left_singleton] at h
      rw [h, one_smul]

/-- An averaged function can be nonzero only at the source of an arrow on which both the
cutoff and the original function are nonzero at the target. -/
theorem support_average_subset (f : C → A) :
    support (hc.average f) ⊆ Quiver.Total.left ''
      (Quiver.Total.right ⁻¹' (support c ∩ support f)) := by
  intro x hx
  obtain ⟨a, ha⟩ : ∃ a : Σ y, x ⟶ y, c a.1 • f a.1 ≠ 0 := by
    by_contra! h
    exact hx (by simp [h])
  exact ⟨⟨x, a.1, a.2⟩, ⟨left_ne_zero_of_smul ha, right_ne_zero_of_smul ha⟩, rfl⟩

/-- Source is proper on the inverse image of the topological support of the cutoff. -/
theorem isProperMap_left_preimage [T2Space C] [CompactlyCoherentSpace C]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    IsProperMap fun a : Quiver.Total.right ⁻¹' tsupport c ↦ (a : Quiver.Total C).left := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hs.comp continuous_subtype_val, fun K hK ↦ ?_⟩
  have heq : (fun a : Quiver.Total.right ⁻¹' tsupport c ↦ (a : Quiver.Total C).left) ⁻¹' K =
      Subtype.val ⁻¹' (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c) := by
    ext a
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h ↦ ⟨h, a.2⟩, fun h ↦ h.1⟩
  rw [heq]
  exact ((isClosed_tsupport c).preimage ht).isClosedEmbedding_subtypeVal.isCompact_preimage
    (hc.isCompact_preimage_inter hK)

/-- With continuous source and target, the topological support of an average is contained
in the sources of arrows whose targets lie in both topological supports. -/
theorem tsupport_average_subset [T2Space C] [CompactlyCoherentSpace C]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) (f : C → A) :
    tsupport (hc.average f) ⊆ Quiver.Total.left ''
      (Quiver.Total.right ⁻¹' (tsupport c ∩ tsupport f)) := by
  have hclosed : IsClosed (Quiver.Total.left ''
      (Quiver.Total.right ⁻¹' (tsupport c ∩ tsupport f))) := by
    convert (hc.isProperMap_left_preimage hs ht).isClosedMap _
      ((isClosed_tsupport f).preimage (ht.comp continuous_subtype_val)) using 1
    ext x
    constructor
    · rintro ⟨a, ⟨hac, haf⟩, rfl⟩
      exact ⟨⟨a, hac⟩, haf, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ⟨a.2, ha⟩, rfl⟩
  exact closure_minimal ((hc.support_average_subset f).trans <| image_mono <|
    preimage_mono <| inter_subset_inter (subset_tsupport c) (subset_tsupport f)) hclosed

end TauCeti.Quiver.IsCutoff

namespace TauCeti.Quiver.IsCutoff

variable {C : Type*} [Category C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] {c : C → ℝ} (hc : IsCutoff c)
  {A : Type*} [AddCommGroup A] [Module ℝ A]

include hc

/-- An average takes equal values at the endpoints of every arrow. -/
theorem average_target_eq_source (f : C → A) {x y : C} (g : x ⟶ y) :
    hc.average f y = hc.average f x := by
  simpa only [average_eq_finsum] using
    (Quiver.Total.finsum_mem_preimage_left_singleton_eq_of_iso
      (fun x ↦ c x • f x) (asIso g)).symm

/-- Cutoff averaging is a projection onto arrow-invariant functions. -/
@[simp]
theorem average_average (f : C → A) : hc.average (hc.average f) = hc.average f :=
  hc.average_eq_self _ fun _ _ g ↦ hc.average_target_eq_source f g

end TauCeti.Quiver.IsCutoff
