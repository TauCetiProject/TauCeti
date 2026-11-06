/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Borel
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

This file combines the normalization theorem in `RootSubgroup.Borel` and the trivial-intersection
theorem in `RootSubgroup.OppositeBorel` with Mathlib's subgroup-complement quotient equivalence.
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

include hwt hα in
/-- An element of a torus subsystem subgroup is a root-generated element times a torus point.
No positivity assumption is required for existence of this factorization. -/
theorem mem_kostantTorusSubsystemSubgroup_iff_exists_mul (A : CommAlgCat.{w} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) :
    g ∈ kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S A ↔
      ∃ u ∈ kostantSubsystemSubgroup e h ρ M hM hnil S A,
        ∃ s : κ → Aˣ, u * kostantTorusPoints M b wt A s = g := by
  have hnorm : (kostantTorusPoints M b wt A).range ≤
      Subgroup.normalizer (kostantSubsystemSubgroup e h ρ M hM hnil S A : Set _) := by
    rintro _ ⟨s, rfl⟩
    exact kostantTorusPoints_mem_normalizer_kostantSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα A s
  rw [kostantTorusSubsystemSubgroup_eq_sup, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]
  simp only [Set.mem_mul]
  aesop

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
    obtain ⟨u, hu, s, hmul⟩ :=
      (mem_kostantTorusSubsystemSubgroup_iff_exists_mul e h ρ M hM hnil b wt hwt α S hα
        (CommAlgCat.of ℤ A) g).mp g.property
    exact Set.mem_mul.mpr ⟨⟨u,
      kostantSubsystemSubgroup_le_kostantTorusSubsystemSubgroup
        e h ρ M hM hnil b wt S _ hu⟩, hu,
      ⟨kostantTorusPoints M b wt _ s,
        kostantTorusPoints_mem_kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S _ s⟩,
      ⟨s, rfl⟩, Subtype.ext hmul⟩

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
    (Subgroup.subgroupOfEquivOfLe (by
      rw [kostantTorusSubsystemSubgroup_eq_sup]
      exact le_sup_right))

/-- The inverse quotient comparison sends a torus point to its class in the Borel-type group. -/
@[simp]
theorem kostantTorusSubsystemQuotientEquiv_symm_apply
    (t : (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range) :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    (kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A).symm t =
      QuotientGroup.mk ⟨t.val, (by
        rw [kostantTorusSubsystemSubgroup_eq_sup]
        exact Subgroup.mem_sup_right t.property)⟩ := by
  let := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  rw [kostantTorusSubsystemQuotientEquiv, MulEquiv.symm_trans_apply,
    Subgroup.IsComplement'.QuotientMulEquiv_symm_apply]
  rfl

/-- The class of a torus point is sent back to that same torus point. -/
@[simp]
theorem kostantTorusSubsystemQuotientEquiv_apply_mk
    (t : (kostantTorusPoints M b wt (CommAlgCat.of ℤ A)).range) :
    letI := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
      e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
    kostantTorusSubsystemQuotientEquiv e h ρ M hM hnil b wt hwt α S hα hpos A
      (QuotientGroup.mk ⟨t.val, (by
        rw [kostantTorusSubsystemSubgroup_eq_sup]
        exact Subgroup.mem_sup_right t.property)⟩) = t := by
  let := kostantSubsystemSubgroup_normal_subgroupOf_kostantTorusSubsystemSubgroup
    e h ρ M hM hnil b wt hwt α S hα (CommAlgCat.of ℤ A)
  rw [← kostantTorusSubsystemQuotientEquiv_symm_apply e h ρ M hM hnil b wt hwt α S hα hpos A,
    MulEquiv.apply_symm_apply]

end TauCeti.UniversalEnvelopingAlgebra
