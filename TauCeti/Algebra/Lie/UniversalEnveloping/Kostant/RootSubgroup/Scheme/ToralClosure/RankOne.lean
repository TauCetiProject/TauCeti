/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# The rank-one square relation in a Kostant toral closure

For an opposite root pair forming an `sl₂` triple at Cartan coordinate `c`, the
word `xᵢ(u) xⱼ(-u⁻¹) xᵢ(u)` squares to the coordinate cocharacter at `-1`.
This file carries that relation from automorphisms of the base-changed admissible
lattice to the matrix-valued points of its toral closure. The value algebra may be
any commutative ring, and the root parameter may be any unit.

The algebraic identity is `kostantWeylParam_sq`; the comparison uses the chosen
lattice basis and the existing root-subgroup and torus matrix identifications.
No identification of the toral closure with a reductive group is required.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ a ∈ kostantForm e h, ∀ m ∈ M, ρ a m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

/-- The pinned rank-one word at any unit squares to the coroot value at `-1`,
inside the toral closure's matrix-valued points. -/
theorem kostantToralRootSubgroupPoints_weylWord_sq
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i j : I} {c : κ} {α : κ → ℤ}
    (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hα : ∀ q, ⁅h q, e i⁆ = (α q : ℚ) • e i)
    (hαneg : ∀ q, ⁅h q, e j⁆ = -((α q : ℚ) • e j))
    (A : Type v) [CommRing A] (u : Aˣ) :
    (kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
        (Multiplicative.ofAdd (u : A)) *
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
        (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
        (Multiplicative.ofAdd (u : A))) ^ 2 =
      kostantToralWeightTorusPoints e h ρ M hM hnil b wt A (Pi.mulSingle c (-1)) := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_kostantToralRootSubgroupPoints, coe_kostantToralRootSubgroupPoints,
    coe_kostantToralWeightTorusPoints]
  have hsq := kostantWeylParam_sq e h ρ M hM (hnil i) (hnil j) b wt hwt hT hα hαneg
    (CommAlgCat.of ℤ A) u
  rw [kostantWeylParam_def, kostantCoordinateCocharacter_apply] at hsq
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hsq
  simpa only [map_pow, map_mul, MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A,
    basisMatrix_kostantTorusPoints] using hmatrix

end TauCeti.UniversalEnvelopingAlgebra
