/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Topology

/-!
# Continuous maps out of the tensor topology

The tensor topology along adic structure maps represents compatible continuous ring maps
with commuting images into nonarchimedean topological rings. A ring map out of the algebraic tensor
product is continuous if and only if its restrictions to the two factors are continuous. Neither
restriction has to be adic, and the target need not be a Huber ring.

The continuity argument splits a power of the base ideal between the two factors. An open
additive subgroup in the target contains the products of two sufficiently small factor
neighbourhoods, hence the image of a sufficiently deep tensor neighbourhood. This is the
ring-level input for extending compatible maps to the separated completed tensor product.

## References

* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7.
-/

public section

open TensorProduct Algebra.TensorProduct Topology Filter

namespace TauCeti.Huber

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

namespace TensorDatum

variable (D : TensorDatum A B C)

variable {R : Type*} [Ring R] (f : B ⊗[A] C →+* R)

/-- Splitting a base-ideal power between the two factors controls the image of an entire
tensor neighbourhood by the images of pure tensors: if `f (b ⊗ c) ∈ H` whenever `b` lies in
`(I B₀)ⁿ` and `c` in `(I C₀)ᵐ`, then `f` maps the image of `Jⁿ⁺ᵐ` into `H`. -/
theorem map_idealImage_le (H : AddSubgroup R) (n m : ℕ)
    (h : ∀ b : D.left.ringOfDefinition, b ∈ D.left.idealOfDefinition ^ n →
      ∀ c : D.right.ringOfDefinition, c ∈ D.right.idealOfDefinition ^ m →
        f ((b : B) ⊗ₜ[A] (c : C)) ∈ H) :
    D.idealImage (n + m) ≤ H.comap f.toAddMonoidHom := by
  have hbase (a : D.base.ringOfDefinition) (ha : a ∈ D.base.idealOfDefinition ^ (n + m)) :
      ∀ r ∈ D.ringOfDefinition, f (algebraMap A (B ⊗[A] C) a * r) ∈ H := by
    rw [pow_add] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) ?_
    swap
    · intro x y hx hy r hr
      simpa only [Subring.coe_add, map_add, add_mul] using H.add_mem (hx r hr) (hy r hr)
    let L : B ⊗[A] C →+ R :=
      { toFun := fun r ↦ f (algebraMap A (B ⊗[A] C) (x * y) * r)
        map_zero' := by simp
        map_add' := by simp [mul_add] }
    apply (D.ringOfDefinition_le_addSubgroup_iff (H.comap L)).mpr
    intro b hb c hc
    let xb : D.left.ringOfDefinition :=
      (algebraMap A B).restrict _ _ D.algebraMap_mem_left x * ⟨b, hb⟩
    let yc : D.right.ringOfDefinition :=
      (algebraMap A C).restrict _ _ D.algebraMap_mem_right y * ⟨c, hc⟩
    have hxb : xb ∈ D.left.idealOfDefinition ^ n := by
      rw [← D.map_idealOfDefinition_left, ← Ideal.map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)
    have hyc : yc ∈ D.right.idealOfDefinition ^ m := by
      rw [← D.map_idealOfDefinition_right, ← Ideal.map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy)
    have heq : algebraMap A (B ⊗[A] C) (↑x * ↑y) * (b ⊗ₜ[A] c) =
        (xb : B) ⊗ₜ[A] (yc : C) := by
      simp only [map_mul, algebraMap_apply, tmul_mul_tmul, mul_one]
      simp [xb, yc, Algebra.algebraMap_eq_smul_one, smul_tmul, tmul_smul, smul_smul, mul_comm]
    exact (congrArg (fun z ↦ f z ∈ H) heq).mpr (h xb hxb yc hyc)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := D.mem_idealImage.mp hx
  have haux := D.idealOfDefinition_pow_induction
    (p := fun y ↦ ∀ r ∈ D.ringOfDefinition, f (r * (y : B ⊗[A] C)) ∈ H)
    (by simp) (fun y z hy hz r hr ↦ by simpa [mul_add] using H.add_mem (hy r hr) (hz r hr))
    (fun s y hy r hr ↦ by simpa [mul_assoc] using hy (r * s) (mul_mem hr s.2))
    (fun a ha r hr ↦ by simpa [mul_comm] using hbase a ha r hr) hy
  simpa using haux 1 (one_mem _)

variable [IsTopologicalRing B] [IsTopologicalRing C]
  [TopologicalSpace R] [NonarchimedeanRing R]

/-- A ring homomorphism from the tensor topology to a nonarchimedean ring is continuous
whenever its restrictions to both factors are continuous. -/
theorem continuous (hB : Continuous (f.comp includeLeftRingHom))
    (hC : Continuous (f.comp (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)) :
    letI := D.topology
    Continuous f := by
  let _ := D.topology
  have _ := D.isTopologicalRing
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨H, hH⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  have hmul : Continuous (fun p : B × C ↦
      (f.comp includeLeftRingHom) p.1 *
        (f.comp (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) p.2) :=
    (hB.comp continuous_fst).mul (hC.comp continuous_snd)
  have hnb := hmul.continuousAt (x := (0, 0)) |>.preimage_mem_nhds
    (by simpa using H.isOpen.mem_nhds H.zero_mem)
  rw [nhds_prod_eq] at hnb
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_prod_iff.mp hnb
  obtain ⟨n, -, hn⟩ := D.left.hasBasis_nhds_zero.mem_iff.mp hV
  obtain ⟨m, -, hm⟩ := D.right.hasBasis_nhds_zero.mem_iff.mp hW
  refine mem_of_superset (D.hasBasis_nhds_zero.mem_of_mem (i := n + m) trivial) ?_
  intro x hx
  apply hH
  apply D.map_idealImage_le f H.toAddSubgroup n m ?_ hx
  intro b hb c hc
  have hp := hVW (Set.mk_mem_prod
    (hn ((D.left.mem_idealImage n).mpr ⟨b, hb, rfl⟩))
    (hm ((D.right.mem_idealImage m).mpr ⟨c, hc, rfl⟩)))
  have hp' : f ((b : B) ⊗ₜ[A] (1 : C)) * f ((1 : B) ⊗ₜ[A] (c : C)) ∈ H := hp
  rw [← map_mul, tmul_mul_tmul, mul_one, one_mul] at hp'
  exact hp'

end TensorDatum

variable [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  {R : Type*} [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]

/-- The tensor topology is the final ring topology for its two coprojections, when tested
against nonarchimedean rings. -/
theorem _root_.RingHom.continuous_tensorTopology_iff (f : B ⊗[A] C →+* R) :
    letI := tensorTopology A B C
    Continuous f ↔ Continuous (f.comp includeLeftRingHom) ∧
      Continuous (f.comp (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) := by
  let _ := tensorTopology A B C
  have _ := isTopologicalRing_tensorTopology A B C
  refine ⟨fun h ↦ ⟨h.comp (isAdicHom_includeLeft_tensorTopology A B C).continuous,
    h.comp (isAdicHom_includeRight_tensorTopology A B C).continuous⟩, fun ⟨hB, hC⟩ ↦ ?_⟩
  rw [tensorTopology_eq A B C (TensorDatum.nonempty A B C).some]
  exact (TensorDatum.nonempty A B C).some.continuous f hB hC

end TauCeti.Huber
