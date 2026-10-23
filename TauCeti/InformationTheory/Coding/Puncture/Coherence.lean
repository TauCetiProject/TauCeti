/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Equiv.Pi
public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.InformationTheory.Coding.Puncture.Basic
public import TauCeti.InformationTheory.Coding.Reindex

/-!
# Coordinate coherence of puncturing and shortening

Puncturing and shortening of additive codes commute with coordinate equivalences. Applying
either operation twice retains the flattened subset of the original coordinates. The equalities
use the canonical equivalences between the coordinate types, so no identification of function
types is implicit. In every statement, the specified sets are the coordinates retained.

The additive results use `AddEquiv.arrowCongr` for coordinate transport and require no scalar
closure or finiteness. Their linear-code specializations use `TauCeti.reindex`.
These identities combine repeated puncturings or repeated shortenings and make both operations
independent of coordinate labels.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.7.
-/

public section

namespace TauCeti
namespace AdditiveCode

variable {A ι κ : Type*} [AddCommGroup A]

/-- Puncturing commutes with coordinate transport. The equivalence points from the new
coordinates to the old ones, and the retained set is its preimage. -/
@[simp]
theorem puncture_map_arrowCongr (C : AdditiveCode A ι) (e : κ ≃ ι) (s : Set ι) :
    puncture (C.map (AddMonoidHom.ofClass (AddEquiv.arrowCongr e.symm (AddEquiv.refl A))))
        (e ⁻¹' s) =
      (puncture C s).map
        (AddMonoidHom.ofClass (AddEquiv.arrowCongr (e.subtypeEquiv fun _ ↦ Iff.rfl).symm
          (AddEquiv.refl A))) := by
  rw [puncture_def, puncture_def, AddSubgroup.map_map, AddSubgroup.map_map]
  apply congrArg C.map
  ext x i
  simp [AddEquiv.arrowCongr_apply, Equiv.subtypeEquiv_apply]

/-- Shortening commutes with coordinate transport, with the retained set pulled back along
the equivalence from the new coordinates to the old ones. -/
@[simp]
theorem shorten_map_arrowCongr (C : AdditiveCode A ι) (e : κ ≃ ι) (s : Set ι) :
    shorten (C.map (AddMonoidHom.ofClass (AddEquiv.arrowCongr e.symm (AddEquiv.refl A))))
        (e ⁻¹' s) =
      (shorten C s).map
        (AddMonoidHom.ofClass (AddEquiv.arrowCongr (e.subtypeEquiv fun _ ↦ Iff.rfl).symm
          (AddEquiv.refl A))) := by
  ext y
  simp only [← AddEquiv.toAddMonoidHom_eq_coe]
  rw [mem_shorten_iff_extend_mem, AddSubgroup.mem_map_equiv,
    AddSubgroup.mem_map_equiv, mem_shorten_iff_extend_mem]
  apply Iff.of_eq
  congr 1
  funext i
  simp only [AddEquiv.arrowCongr_symm, AddEquiv.refl_symm, Equiv.symm_symm]
  simp only [AddEquiv.arrowCongr_apply, AddEquiv.refl_apply]
  by_cases hi : i ∈ s
  · have hpre : e.symm i ∈ e ⁻¹' s := by simpa using hi
    rw [Function.extend_val_apply hpre, Function.extend_val_apply hi]
    simp
  · have hpre : e.symm i ∉ e ⁻¹' s := by simpa using hi
    rw [Function.extend_val_apply' hpre, Function.extend_val_apply' hi]
    rfl

/-- Puncturing twice is puncturing once to the flattened retained subset, after transport
along the canonical equivalence from a subtype of a subtype. -/
@[simp]
theorem puncture_puncture (C : AdditiveCode A ι) (s : Set ι) (t : Set s) :
    (puncture (puncture C s) t).map
        (AddMonoidHom.ofClass
          (AddEquiv.arrowCongr (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t))
            (AddEquiv.refl A))) =
      puncture C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  rw [puncture_def, puncture_def, puncture_def, AddSubgroup.map_map, AddSubgroup.map_map]
  apply congrArg C.map
  ext x i
  simp [AddEquiv.arrowCongr_apply, Equiv.subtypeSubtypeEquivSubtypeExists_symm_apply_coe_coe]

/-- Shortening twice is shortening once to the flattened retained subset, after transport
along the canonical subtype equivalence. -/
@[simp]
theorem shorten_shorten (C : AdditiveCode A ι) (s : Set ι) (t : Set s) :
    (shorten (shorten C s) t).map
        (AddMonoidHom.ofClass
          (AddEquiv.arrowCongr (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t))
            (AddEquiv.refl A))) =
      shorten C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  ext y
  simp only [← AddEquiv.toAddMonoidHom_eq_coe]
  rw [AddSubgroup.mem_map_equiv, mem_shorten_iff_extend_mem,
    mem_shorten_iff_extend_mem, mem_shorten_iff_extend_mem]
  apply Iff.of_eq
  congr 1
  let e := Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)
  let v := (AddEquiv.arrowCongr e (AddEquiv.refl A)).symm y
  have hv : Function.extend e v (0 : {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} → A) = y := by
    funext j
    obtain ⟨a, rfl⟩ := e.surjective j
    rw [e.injective.extend_apply]
    simp [v, AddEquiv.arrowCongr_symm]
  calc
    _ = Function.extend ((Subtype.val : s → ι) ∘ (Subtype.val : t → s)) v 0 :=
      (Subtype.val_injective.extend_comp Subtype.val_injective v (0 : ι → A)).symm
    _ = Function.extend ((Subtype.val : {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} → ι) ∘ e)
        v 0 := rfl -- Flattening preserves the underlying original coordinate.
    _ = Subtype.val.extend (Function.extend e v 0) 0 :=
      e.injective.extend_comp Subtype.val_injective v (0 : ι → A)
    _ = Subtype.val.extend y 0 := by rw [hv]

end AdditiveCode

variable {F : Type*} [Field F] {ι : Type*}

/-- Puncturing commutes with a change of coordinates. The retained set is pulled back along the
coordinate equivalence. -/
@[simp]
theorem puncture_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (s : Set ι) :
    puncture (reindex C e) (e ⁻¹' s) =
      reindex (puncture C s) (e.subtypeEquiv fun _ ↦ Iff.rfl) := by
  apply Submodule.toAddSubgroup_injective
  simpa only [reindex_def, Submodule.map_toAddSubgroup,
    LinearCode.puncture_toAddSubgroup, LinearEquiv.funCongrLeft_toAddMonoidHom, Equiv.symm_symm]
    using AdditiveCode.puncture_map_arrowCongr C.toAddSubgroup e s

/-- Shortening commutes with a change of coordinates. -/
@[simp]
theorem shorten_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (s : Set ι) :
    shorten (reindex C e) (e ⁻¹' s) =
      reindex (shorten C s) (e.subtypeEquiv fun _ ↦ Iff.rfl) := by
  apply Submodule.toAddSubgroup_injective
  simpa only [reindex_def, Submodule.map_toAddSubgroup,
    LinearCode.shorten_toAddSubgroup, LinearEquiv.funCongrLeft_toAddMonoidHom, Equiv.symm_symm]
    using AdditiveCode.shorten_map_arrowCongr C.toAddSubgroup e s

/-- Puncturing at one coordinate commutes with a change of coordinates: the deleted coordinate is
carried along the coordinate equivalence. -/
@[simp]
theorem punctureAt_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (k : κ) :
    punctureAt (reindex C e) k =
      reindex (punctureAt C (e k)) (e.subtypeEquiv fun _ ↦ by simp) := by
  ext y
  simp only [mem_punctureAt, mem_reindex]
  constructor
  · rintro ⟨z, ⟨x, hxC, hxz⟩, hzy⟩
    exact ⟨fun j ↦ x j, ⟨x, hxC, fun _ ↦ rfl⟩, fun j ↦ (hxz j).trans (hzy j)⟩
  · rintro ⟨u, ⟨x, hxC, hxu⟩, huy⟩
    exact ⟨fun j ↦ x (e j), ⟨x, hxC, fun _ ↦ rfl⟩, fun j ↦ (hxu _).trans (huy j)⟩

/-- Shortening at one coordinate commutes with a change of coordinates: the deleted coordinate is
carried along the coordinate equivalence. -/
@[simp]
theorem shortenAt_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (k : κ) :
    shortenAt (reindex C e) k =
      reindex (shortenAt C (e k)) (e.subtypeEquiv fun _ ↦ by simp) := by
  ext y
  simp only [mem_shortenAt, mem_reindex]
  constructor
  · rintro ⟨z, ⟨x, hxC, hxz⟩, hzk, hzy⟩
    exact ⟨fun j ↦ x j, ⟨x, hxC, (hxz k).trans hzk, fun _ ↦ rfl⟩,
      fun j ↦ (hxz j).trans (hzy j)⟩
  · rintro ⟨u, ⟨x, hxC, hxk, hxu⟩, huy⟩
    exact ⟨fun j ↦ x (e j), ⟨x, hxC, fun _ ↦ rfl⟩, hxk, fun j ↦ (hxu _).trans (huy j)⟩

/-- Puncturing twice is puncturing once to the flattened set of retained coordinates, up to the
canonical equivalence between a subtype of a subtype and the corresponding subtype. -/
@[simp]
theorem puncture_puncture (C : LinearCode F ι) (s : Set ι) (t : Set s) :
    reindex (puncture (puncture C s) t)
        (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm =
      puncture C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  apply Submodule.toAddSubgroup_injective
  rw [LinearCode.puncture_toAddSubgroup C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t}]
  simpa only [reindex_def, Submodule.map_toAddSubgroup,
    LinearCode.puncture_toAddSubgroup, LinearEquiv.funCongrLeft_toAddMonoidHom, Equiv.symm_symm]
    using AdditiveCode.puncture_puncture C.toAddSubgroup s t

/-- Shortening twice is shortening once to the flattened set of retained coordinates, up to the
canonical subtype equivalence. -/
@[simp]
theorem shorten_shorten (C : LinearCode F ι) (s : Set ι) (t : Set s) :
    reindex (shorten (shorten C s) t)
        (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm =
      shorten C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  apply Submodule.toAddSubgroup_injective
  rw [LinearCode.shorten_toAddSubgroup C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t}]
  simpa only [reindex_def, Submodule.map_toAddSubgroup,
    LinearCode.shorten_toAddSubgroup, LinearEquiv.funCongrLeft_toAddMonoidHom, Equiv.symm_symm]
    using AdditiveCode.shorten_shorten C.toAddSubgroup s t

end TauCeti
