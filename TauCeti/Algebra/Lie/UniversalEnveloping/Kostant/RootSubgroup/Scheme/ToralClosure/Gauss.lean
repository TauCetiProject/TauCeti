/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Group.OneParameterGauss
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss

/-!
# Opposite-root Gauss factorization in the Kostant toral closure

Let `(eᵢ, eⱼ)` be an `sl₂` root pair of weights `α` and `-α` with Cartan coroot coordinate `c` in a
Kostant-stable lattice `M` equipped with a finite Cartan weight basis `(b, wt)`. Over any
commutative ring `A`, the represented root subgroups and split weight torus define homomorphisms
`kostantToralRootSubgroupPoints` and `kostantToralWeightTorusPoints` into the point group
`kostantToralPointsSubgroup` of the toral Kostant closure.

This file transports the opposite-root Gauss factorizations from
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss` into the point group of
the toral closure: whenever `u = 1 + r s` is a unit of `A`,

```text
xᵢ(r) xⱼ(s) = xⱼ(s u⁻¹) t(Pi.mulSingle c u) xᵢ(r u⁻¹),
xⱼ(s) xᵢ(r) = xᵢ(r u⁻¹) t(Pi.mulSingle c u⁻¹) xⱼ(s u⁻¹).
```

## Main results

* `kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_e_f`:
  the raising-times-lowering Gauss factorization in `kostantToralPointsSubgroup`.
* `kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_f_e`:
  the lowering-times-raising Gauss factorization in `kostantToralPointsSubgroup`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable {i j : I} {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ q, ⁅h q, e i⁆ = (α q : ℚ) • e i)
variable (hαneg : ∀ q, ⁅h q, e j⁆ = -((α q : ℚ) • e j))

include hwt hT hα hαneg

/-- **Opposite-root Gauss factorization in the Kostant toral closure (raising times lowering).**
Whenever `u = 1 + r s` is a unit of the commutative ring `A`, the product `xᵢ(r) xⱼ(s)` in
`kostantToralPointsSubgroup` factors through the represented coroot torus point at `c`. -/
theorem kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_e_f
    (A : Type v) [CommRing A] (r s : A) (u : Aˣ) (hu : (u : A) = 1 + r * s) :
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A (Multiplicative.ofAdd r) *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd s) =
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd (s * ↑u⁻¹)) *
        kostantToralWeightTorusPoints e h ρ M hM hnil b wt A (Pi.mulSingle c u) *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
          (Multiplicative.ofAdd (r * ↑u⁻¹)) := by
  have hmul := kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f (c := c) (α := α)
    e h ρ M hM (hnil i) (hnil j) b wt hwt hT hα hαneg (CommAlgCat.of ℤ A) r s u hu
  rw [kostantCoordinateCocharacter_apply] at hmul
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hmul
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_kostantToralRootSubgroupPoints,
    coe_kostantToralWeightTorusPoints, map_mul, MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A j,
    basisMatrix_kostantTorusPoints M b wt (A := A)] using hmatrix

/-- **Opposite-root Gauss factorization in the Kostant toral closure (lowering times raising).**
Whenever `u = 1 + r s` is a unit of the commutative ring `A`, the product `xⱼ(s) xᵢ(r)` in
`kostantToralPointsSubgroup` factors through the inverse coroot torus point at coordinate `c`. -/
theorem kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_f_e
    (A : Type v) [CommRing A] (r s : A) (u : Aˣ) (hu : (u : A) = 1 + r * s) :
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd s) *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A (Multiplicative.ofAdd r) =
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A (Multiplicative.ofAdd (r * ↑u⁻¹)) *
        kostantToralWeightTorusPoints e h ρ M hM hnil b wt A (Pi.mulSingle c u⁻¹) *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
          (Multiplicative.ofAdd (s * ↑u⁻¹)) := by
  simpa only [Pi.mulSingle_inv] using
    map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq
      (kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_e_f (c := c) (α := α)
        e h ρ M hM hnil b wt hwt hT hα hαneg A (-r) (-s) u (by rwa [neg_mul_neg]))

end TauCeti.UniversalEnvelopingAlgebra
