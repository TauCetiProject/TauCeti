/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Coordinate

/-!
# Steinberg's rank-one quotient in matrix coordinates

Transport `kostantWeylParam_mul_inv_kostantWeylParam` through an arbitrary finite lattice basis.
The resulting identity uses only root-subgroup matrices and the weight-torus matrix, so it can
be used in different represented point groups without repeating the basis transport.

The proof factors the calculation in
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.Weyl.Products`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable {i j : ι} {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ q, ⁅h q, e i⁆ = (α q : ℚ) • e i)
variable (hαneg : ∀ q, ⁅h q, e j⁆ = -((α q : ℚ) • e j))
variable [Fintype κ] [DecidableEq κ]

include hwt hT hα hαneg

/-- In any finite lattice basis, the quotient `nᵢ(u) nᵢ(v)⁻¹` of Steinberg's root-matrix
products is the coordinate-coroot value at `u v⁻¹`. No group-scheme hypothesis is needed. -/
theorem kostantRootSubgroupMatrix_mul_mul_mul_inv (A : Type*) [CommRing A] (u v : Aˣ) :
    let x := fun k (a : Multiplicative A) =>
      kostantRootSubgroupMatrix e h ρ M hM k (hnil k) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm a)
    (x i (Multiplicative.ofAdd (u : A)) *
        x j (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        x i (Multiplicative.ofAdd (u : A))) *
      (x i (Multiplicative.ofAdd (v : A)) *
        x j (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        x i (Multiplicative.ofAdd (v : A)))⁻¹ =
      kostantTorusMatrix M b wt (Pi.mulSingle c (u * v⁻¹)) := by
  have hquot := kostantWeylParam_mul_inv_kostantWeylParam e h ρ M hM (hnil i) (hnil j)
    b wt hwt hT hα hαneg (CommAlgCat.of ℤ A) u v
  rw [kostantCoordinateCocharacter_apply] at hquot
  have hm := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hquot
  rw [MulEquiv.toMonoidHom_eq_coe, basisMatrix_kostantTorusPoints] at hm
  simpa only [kostantWeylParam_def, map_mul, map_inv,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A] using hm

end TauCeti.UniversalEnvelopingAlgebra
