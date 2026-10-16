/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Completion by extension of scalars from a ring of definition

If `(B, I)` is a pair of definition for a Huber ring `A`, the canonical map
`A ⊗[B] Completion B → Completion A` is an isomorphism. No Noetherian, Tate, or separation
hypothesis is imposed on `A`.

The proof uses an algebraic normal form: every tensor is a sum of an element of `A` and an
element of `Completion B`. To obtain this form, approximate a completed coefficient modulo
`Iⁿ`, choosing `n` large enough that multiplication by the tensor's other factor takes `Iⁿ`
into `B`. The equality between completed ideal powers and closures lets tensor balancing
move the remaining error into the completed coefficient factor.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.9(1).
* R. Huber, *Continuous valuations*, Mathematische Zeitschrift 212 (1993), Lemma 1.6.
  The algebraic normal-form argument here is an adaptation of the completion comparison;
  it avoids putting a topology on the tensor product.
-/

public section

open Filter Topology UniformSpace TensorProduct

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The canonical map obtained by extending the completion map on `A` along the completion
of its ring of definition. -/
noncomputable def completionTensorMap (P : PairOfDefinition A) :
    A ⊗[P.ringOfDefinition] Completion P.ringOfDefinition →ₐ[A] Completion A :=
  Algebra.TensorProduct.lift
    { __ := Completion.coeRingHom
      commutes' := fun _ ↦ rfl }
    { __ := Completion.mapRingHom P.ringOfDefinition.subtype (by fun_prop)
      commutes' := fun b ↦
        (Completion.mapRingHom_coe (f := P.ringOfDefinition.subtype) (by fun_prop) b).trans
          (by rfl) }
    fun _ _ ↦ Commute.all _ _

/-- The canonical comparison multiplies the two completed factors on pure tensors. -/
@[simp] theorem completionTensorMap_tmul (P : PairOfDefinition A) (a : A)
    (b : Completion P.ringOfDefinition) :
    P.completionTensorMap (a ⊗ₜ[P.ringOfDefinition] b) =
      (a : Completion A) * Completion.map ((↑) : P.ringOfDefinition → A) b := (rfl)

private noncomputable def completionRingEquiv (P : PairOfDefinition A) :
    Completion P.ringOfDefinition ≃+* P.completionRingOfDefinition :=
  P.ringOfDefinition.completionEquivClosure.trans (RingEquiv.subringCongr (by
    ext x
    rw [← SetLike.mem_coe, Completion.coe_topologicalClosure_map_coeRingHom,
      P.mem_completionRingOfDefinition_iff]))

private theorem coe_completionRingEquiv (P : PairOfDefinition A)
    (b : Completion P.ringOfDefinition) :
    (P.completionRingEquiv b : Completion A) =
      Completion.mapRingHom P.ringOfDefinition.subtype (by fun_prop) b := by
  simp only [completionRingEquiv, RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply,
    Subring.coe_completionEquivClosure]

private theorem completionEquivClosure_symm_toCompletionRingOfDefinition
    (P : PairOfDefinition A) (b : P.ringOfDefinition) :
    P.completionRingEquiv.symm (P.toCompletionRingOfDefinition b) =
      (b : Completion P.ringOfDefinition) := by
  apply P.completionRingEquiv.injective
  rw [RingEquiv.apply_symm_apply]
  ext
  rw [P.coe_completionRingEquiv, P.toCompletionRingOfDefinition_apply]
  exact (Completion.mapRingHom_coe (f := P.ringOfDefinition.subtype) (by fun_prop) b).symm

private theorem exists_tmul_completionIdeal_eq (P : PairOfDefinition A) (a : A) (n : ℕ)
    (hn : ∀ b ∈ P.idealOfDefinition ^ n, a * (b : A) ∈ P.ringOfDefinition)
    (y : P.completionRingOfDefinition) (hy : y ∈ P.completionIdeal ^ n) :
    ∃ d : Completion P.ringOfDefinition,
      a ⊗ₜ[P.ringOfDefinition] P.completionRingEquiv.symm y = 1 ⊗ₜ d := by
  rw [P.completionIdeal_def, ← Ideal.map_pow] at hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, rfl⟩
    let ab : P.ringOfDefinition := ⟨a * (b : A), hn b hb⟩
    refine ⟨(ab : Completion P.ringOfDefinition), ?_⟩
    rw [completionEquivClosure_symm_toCompletionRingOfDefinition]
    calc
      a ⊗ₜ[P.ringOfDefinition] (b : Completion P.ringOfDefinition) =
          (b • a) ⊗ₜ[P.ringOfDefinition] (1 : Completion P.ringOfDefinition) := by
        simpa [Algebra.smul_def, Completion.algebraMap_def,
          Algebra.algebraMap_ofSubsemiring_apply] using
          (TensorProduct.tmul_smul (R := P.ringOfDefinition) b a
            (1 : Completion P.ringOfDefinition)).trans
              (TensorProduct.smul_tmul' (R := P.ringOfDefinition) b a
                (1 : Completion P.ringOfDefinition))
      _ = 1 ⊗ₜ[P.ringOfDefinition] (ab : Completion P.ringOfDefinition) := by
        simpa [ab, Algebra.smul_def, Completion.algebraMap_def,
          Algebra.algebraMap_ofSubsemiring_apply, mul_comm] using
          TensorProduct.smul_tmul (R := P.ringOfDefinition) ab (1 : A)
            (1 : Completion P.ringOfDefinition)
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨d, hd⟩ ⟨e, he⟩
    exact ⟨d + e, by simp [hd, he, TensorProduct.tmul_add]⟩
  · rintro c x _ ⟨d, hd⟩
    refine ⟨P.completionRingEquiv.symm c * d, ?_⟩
    have h := congrArg (fun t ↦ (1 ⊗ₜ[P.ringOfDefinition]
      P.completionRingEquiv.symm c) * t) hd
    simp only [Algebra.TensorProduct.tmul_mul_tmul (R := P.ringOfDefinition), one_mul] at h
    simpa only [smul_eq_mul, map_mul] using h

private theorem exists_tmul_eq_normalForm (P : PairOfDefinition A) (a : A)
    (c : Completion P.ringOfDefinition) :
    ∃ b : A, ∃ d : Completion P.ringOfDefinition,
      a ⊗ₜ[P.ringOfDefinition] c = b ⊗ₜ[P.ringOfDefinition] 1 + 1 ⊗ₜ d := by
  obtain ⟨n, hn⟩ := P.exists_pow_idealOfDefinition_mul_mem P.isOpen_ringOfDefinition a
  let y := P.completionRingEquiv c
  have hy : (y : Completion A) ∈ P.completionRingOfDefinition := y.2
  obtain ⟨b, hby⟩ := P.exists_coe_sub_mem_completionIdealImage n (y : Completion A)
  have hbB : b ∈ P.ringOfDefinition := by
    have hcoe : (b : Completion A) ∈ P.completionRingOfDefinition := by
      simpa using P.completionRingOfDefinition.add_mem (P.completionIdealImage_le n hby) hy
    rw [P.mem_completionRingOfDefinition_iff] at hcoe
    have hpre := Completion.preimage_closure_image_coe
      (G := P.ringOfDefinition.toAddSubgroup) P.isOpen_ringOfDefinition
    simp only [Subring.coe_toAddSubgroup] at hpre
    have hb : b ∈ ((↑) : A → Completion A) ⁻¹'
        closure (((↑) : A → Completion A) '' (P.ringOfDefinition : Set A)) := hcoe
    rwa [hpre] at hb
  let b' : P.ringOfDefinition := ⟨b, hbB⟩
  let e : P.completionRingOfDefinition := y - P.toCompletionRingOfDefinition b'
  have he : e ∈ P.completionIdeal ^ n := by
    rw [P.completionIdeal_pow, P.mem_completionIdealImageIdeal_iff]
    simpa [e, b'] using (P.completionIdealImage n).neg_mem hby
  obtain ⟨d, hd⟩ := P.exists_tmul_completionIdeal_eq a n hn e he
  refine ⟨a * b, d, ?_⟩
  have hce : c = (b' : Completion P.ringOfDefinition) +
      P.completionRingEquiv.symm e := by
    apply P.completionRingEquiv.injective
    simp [e, y, completionEquivClosure_symm_toCompletionRingOfDefinition]
  rw [hce, TensorProduct.tmul_add, hd]
  congr 1
  simpa [b', Algebra.smul_def, Completion.algebraMap_def,
    Algebra.algebraMap_ofSubsemiring_apply, mul_comm] using
    (TensorProduct.tmul_smul (R := P.ringOfDefinition) b' a
      (1 : Completion P.ringOfDefinition)).trans
        (TensorProduct.smul_tmul' (R := P.ringOfDefinition) b' a
          (1 : Completion P.ringOfDefinition))

/-- Every tensor has a normal form consisting of one original-ring term and one completed
coefficient term. This is the algebraic comparison underlying completion by base change. -/
theorem exists_eq_tmul_one_add_one_tmul (P : PairOfDefinition A)
    (x : A ⊗[P.ringOfDefinition] Completion P.ringOfDefinition) :
    ∃ a : A, ∃ b : Completion P.ringOfDefinition,
      x = a ⊗ₜ[P.ringOfDefinition] 1 + 1 ⊗ₜ b := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact P.exists_tmul_eq_normalForm a b
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by simp [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel⟩

/-- The canonical base-change comparison to the completion is surjective. -/
theorem completionTensorMap_surjective (P : PairOfDefinition A) :
    Function.Surjective P.completionTensorMap := by
  intro x
  obtain ⟨a, ha⟩ := P.exists_coe_sub_mem_completionIdealImage 0 x
  let c : P.completionRingOfDefinition := ⟨x - (a : Completion A),
    P.completionIdealImage_le 0 (by
      rw [SetLike.mem_coe]
      simpa only [neg_sub] using (P.completionIdealImage 0).neg_mem ha)⟩
  have hjc : Completion.mapRingHom P.ringOfDefinition.subtype (by fun_prop)
      (P.completionRingEquiv.symm c) = x - (a : Completion A) := by
    rw [← P.coe_completionRingEquiv, RingEquiv.apply_symm_apply]
  have hjc' : Completion.map ((↑) : P.ringOfDefinition → A)
      (P.completionRingEquiv.symm c) = x - (a : Completion A) := by
    exact (Completion.mapRingHom_apply (f := P.ringOfDefinition.subtype)
      (hf := by fun_prop)).symm.trans hjc
  have hOne : Completion.map ((↑) : P.ringOfDefinition → A)
      (1 : Completion P.ringOfDefinition) = 1 := by
    rw [← P.ringOfDefinition.coe_subtype,
      ← Completion.mapRingHom_apply (f := P.ringOfDefinition.subtype) (hf := by fun_prop)]
    exact map_one _
  refine ⟨a ⊗ₜ[P.ringOfDefinition] 1 + 1 ⊗ₜ P.completionRingEquiv.symm c, ?_⟩
  simp only [map_add, P.completionTensorMap_tmul, Completion.coe_one,
    mul_one, one_mul, hjc', hOne]
  abel

/-- The canonical base-change comparison to the completion is injective. -/
theorem completionTensorMap_injective (P : PairOfDefinition A) :
    Function.Injective P.completionTensorMap := by
  refine (injective_iff_map_eq_zero P.completionTensorMap).mpr fun x hx ↦ ?_
  obtain ⟨a, b, rfl⟩ := P.exists_eq_tmul_one_add_one_tmul x
  have hzero : (a : Completion A) +
      Completion.mapRingHom P.ringOfDefinition.subtype (by fun_prop) b = 0 := by
    simpa only [map_add, P.completionTensorMap_tmul, map_one, Completion.coe_one,
      mul_one, one_mul, ← P.ringOfDefinition.coe_subtype,
      ← Completion.mapRingHom_apply (f := P.ringOfDefinition.subtype) (hf := by fun_prop)] using hx
  have haC : (a : Completion A) ∈ P.completionRingOfDefinition := by
    rw [eq_neg_of_add_eq_zero_left hzero, ← P.coe_completionRingEquiv]
    exact P.completionRingOfDefinition.neg_mem (P.completionRingEquiv b).2
  have hpre := Completion.preimage_closure_image_coe
    (G := P.ringOfDefinition.toAddSubgroup) P.isOpen_ringOfDefinition
  simp only [Subring.coe_toAddSubgroup] at hpre
  have haB : a ∈ P.ringOfDefinition := by
    rw [← SetLike.mem_coe, ← hpre]
    exact P.mem_completionRingOfDefinition_iff.mp haC
  let a' : P.ringOfDefinition := ⟨a, haB⟩
  have hjcoe : Completion.mapRingHom P.ringOfDefinition.subtype (by fun_prop)
      (a' : Completion P.ringOfDefinition) = (a : Completion A) :=
    Completion.mapRingHom_coe (f := P.ringOfDefinition.subtype) (by fun_prop) a'
  have hsum : (a' : Completion P.ringOfDefinition) + b = 0 := by
    apply P.ringOfDefinition.isUniformEmbedding_mapRingHom_subtype.injective
    simpa only [map_add, map_zero, hjcoe] using hzero
  have hbalance : a ⊗ₜ[P.ringOfDefinition] (1 : Completion P.ringOfDefinition) =
      1 ⊗ₜ[P.ringOfDefinition] (a' : Completion P.ringOfDefinition) := by
    simpa [a', Algebra.smul_def, Completion.algebraMap_def,
      Algebra.algebraMap_ofSubsemiring_apply] using
        TensorProduct.smul_tmul (R := P.ringOfDefinition) a' (1 : A)
          (1 : Completion P.ringOfDefinition)
  rw [hbalance, ← TensorProduct.tmul_add, hsum, TensorProduct.tmul_zero]

/-- Completion of a Huber ring is extension of scalars from the completion of any ring of
definition (Wedhorn, Proposition 6.9(1)). -/
noncomputable def completionTensorEquiv (P : PairOfDefinition A) :
    A ⊗[P.ringOfDefinition] Completion P.ringOfDefinition ≃ₐ[A] Completion A :=
  AlgEquiv.ofBijective P.completionTensorMap
    ⟨P.completionTensorMap_injective, P.completionTensorMap_surjective⟩

/-- The base-change equivalence has the canonical comparison as its underlying map. -/
theorem completionTensorEquiv_toAlgHom (P : PairOfDefinition A) :
    P.completionTensorEquiv.toAlgHom = P.completionTensorMap := (rfl)

/-- The completion base-change equivalence multiplies pure tensors in the ambient completion. -/
@[simp] theorem completionTensorEquiv_tmul (P : PairOfDefinition A) (a : A)
    (b : Completion P.ringOfDefinition) :
    P.completionTensorEquiv (a ⊗ₜ[P.ringOfDefinition] b) =
      (a : Completion A) * Completion.map ((↑) : P.ringOfDefinition → A) b :=
  P.completionTensorMap_tmul a b

/-- The inverse comparison takes an original element of `A` to its pure tensor with `1`. -/
@[simp] theorem completionTensorEquiv_symm_coe (P : PairOfDefinition A) (a : A) :
    P.completionTensorEquiv.symm (a : Completion A) = a ⊗ₜ[P.ringOfDefinition] 1 := by
  apply P.completionTensorEquiv.injective
  rw [AlgEquiv.apply_symm_apply, P.completionTensorEquiv_tmul,
    ← P.ringOfDefinition.coe_subtype,
    ← Completion.mapRingHom_apply (f := P.ringOfDefinition.subtype) (hf := by fun_prop),
    map_one, mul_one]

/-- The inverse comparison takes a completed coefficient to its pure tensor with `1`. -/
@[simp] theorem completionTensorEquiv_symm_map (P : PairOfDefinition A)
    (b : Completion P.ringOfDefinition) :
    P.completionTensorEquiv.symm
      (Completion.map ((↑) : P.ringOfDefinition → A) b) =
        1 ⊗ₜ[P.ringOfDefinition] b := by
  apply P.completionTensorEquiv.injective
  simp only [AlgEquiv.apply_symm_apply, P.completionTensorEquiv_tmul, Completion.coe_one,
    one_mul]

end TauCeti.Huber.PairOfDefinition
