/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Elementary
public import Mathlib.GroupTheory.Complement
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OppositeBorel

/-!
# Unipotent and torus factors of a Kostant Borel subgroup

For a Kostant-stable lattice with a weight basis, the torus normalizes each root-generated
subsystem subgroup `U`. Thus adjoining the torus gives the product `B = U T`. If the roots move
strictly towards the beginning of a finite ordered weight basis, the existing triangularity
argument gives `U ∩ T = 1`. Consequently the two factors are complementary inside `B`, and
`B / U` is canonically isomorphic to `T`.

Here `T` is the image of `kostantTorusPoints`, not its parameter group. No injectivity of that
parametrization is assumed. In particular, using weights in the full weight lattice for an
adjoint representation does not assert that its torus image is the full group of points of the
adjoint torus. To describe that full torus, use coordinates in the actual character lattice.

This file combines the factorization theorem in `RootSubgroup.Torus.Elementary` and the
trivial-intersection theorem in `RootSubgroup.OppositeBorel` with Mathlib's subgroup-complement
quotient equivalence.
The results hold over every commutative value ring, including nonreduced rings.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17 and 18.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open TensorProduct
open scoped Pointwise

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι κ : Type*} [Fintype κ]
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable (α : ι → κ → ℤ) (S : Set ι)
variable (hα : ∀ i ∈ S, ∀ j, ⁅h j, e i⁆ = (α i j : ℚ) • e i)

-- Match tensor products to the module instance stored by the value algebra.
attribute [local instance high] Algebra.toModule

variable [LinearOrder η] [Finite η]
variable (hpos : ∀ i ∈ S, ∀ {r s : η} {m : ℕ},
  0 < m → wt r = wt s + m • α i → r < s)
variable (A : Type w) [CommRing A]

include hwt hα hpos in
/-- The positive subsystem subgroup and the torus image are complementary inside the subgroup
that they generate. This expresses existence and uniqueness of the unipotent and torus factors,
without requiring unique torus parameters. -/
theorem isComplement'_kostantSubsystemSubgroup_range_kostantTorusPoints :
    ((kostantSubsystemSubgroup e h ρ M hM hnil S (CommAlgCat.of ℤ A)).subgroupOf
      (kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A))).IsComplement'
    (((kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range).subgroupOf
      (kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A))) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp <| (kostantSubsystemSubgroup_inf_range_kostantTorusPoints_eq_bot
      e h ρ M hM hnil b wt α hwt S hα hpos A) ▸ ⟨hg.1, hg.2⟩
  · apply Set.eq_univ_of_forall
    intro g
    obtain ⟨u, hu, t, ht, hmul⟩ :=
      (mem_kostantTorusSubsystemSubgroup_iff e h ρ M hM hnil b wt hwt α S hα
        (CommAlgCat.of ℤ A) g).mp g.property
    rw [kostantTorusSubgroup_eq_range] at ht
    exact Set.mem_mul.mpr ⟨⟨u,
      kostantSubsystemSubgroup_le_kostantTorusSubsystemSubgroup
        e h ρ M hM hnil b wt S _ hu⟩, hu,
      ⟨t, range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
        e h ρ M hM hnil b wt S _ ht⟩, ht, Subtype.ext hmul⟩

/-- Quotienting a positive torus subsystem subgroup by its root-generated subgroup leaves exactly
the torus image. The normality instance is the one supplied by torus normalization. -/
noncomputable def kostantTorusSubsystemQuotientEquiv :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    (kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A)) ⧸
      (kostantSubsystemSubgroup e h ρ M hM hnil S (CommAlgCat.of ℤ A)).subgroupOf
        (kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A)) ≃*
      (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range := by
  letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  exact ((isComplement'_kostantSubsystemSubgroup_range_kostantTorusPoints
    e h ρ M hM hnil b wt hwt α S hα hpos A).symm.QuotientMulEquiv).trans
    (Subgroup.subgroupOfEquivOfLe
      (range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S _))

/-- The inverse quotient comparison sends a torus point to its class in the Borel-type group. -/
@[simp]
theorem kostantTorusSubsystemQuotientEquiv_symm_apply
    (t : (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range) :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    (kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A).symm t =
      QuotientGroup.mk ⟨t.val, range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
        e h ρ M hM hnil b wt S _ t.property⟩ := by
  let := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  rw [kostantTorusSubsystemQuotientEquiv, MulEquiv.symm_trans_apply,
    Subgroup.IsComplement'.QuotientMulEquiv_symm_apply]
  -- The inverse complement map takes the quotient class of the included torus element.
  change QuotientGroup.mk ((Subgroup.subgroupOfEquivOfLe
    (range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt S _)).symm t).val = _
  exact congrArg QuotientGroup.mk
    (Subtype.ext (Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe _ t))

/-- The class of a torus point is sent back to that same torus point. -/
@[simp]
theorem kostantTorusSubsystemQuotientEquiv_apply_mk
    (t : (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range) :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A
      (QuotientGroup.mk ⟨t.val, range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
        e h ρ M hM hnil b wt S _ t.property⟩) = t := by
  let := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  rw [← kostantTorusSubsystemQuotientEquiv_symm_apply e h ρ M hM hnil b wt hwt α S hα hpos A,
    MulEquiv.apply_symm_apply]

/-- The quotient comparison extracts the torus factor of a product `u * t`. -/
@[simp]
theorem kostantTorusSubsystemQuotientEquiv_mk_mul
    (u : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M))
    (hu : u ∈ kostantSubsystemSubgroup e h ρ M hM hnil S (CommAlgCat.of ℤ A))
    (t : (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range) :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A
      (QuotientGroup.mk ⟨u * t.val, mul_mem
        (kostantSubsystemSubgroup_le_kostantTorusSubsystemSubgroup
          e h ρ M hM hnil b wt S _ hu)
        (range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
          e h ρ M hM hnil b wt S _ t.property)⟩) = t := by
  let := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  let u' : kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A) :=
    ⟨u, kostantSubsystemSubgroup_le_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt S _ hu⟩
  let t' : kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S (CommAlgCat.of ℤ A) :=
    ⟨t.val, range_kostantTorusPoints_le_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt S _ t.property⟩
  change kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A
    (QuotientGroup.mk (u' * t')) = t
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff u').mpr hu, one_mul]
  exact kostantTorusSubsystemQuotientEquiv_apply_mk e h ρ M hM hnil b wt hwt α S hα hpos A t

end TauCeti.UniversalEnvelopingAlgebra
