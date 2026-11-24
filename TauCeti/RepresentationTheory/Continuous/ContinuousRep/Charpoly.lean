/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
import TauCeti.RepresentationTheory.BaseChange.Charpoly
import TauCeti.Topology.Instances.Matrix

/-!
# Characteristic polynomials of continuous representations

For a continuous representation `ρ : ContinuousRep Γ A M` on a finite free module `M` over a
commutative ring `A`, the characteristic polynomial at `g : Γ` is `(ρ g).charpoly = det(X - ρ(g))`
in `A[X]`.

On the algebraic side, `(ρ g).charpoly` is invariant under isomorphism of continuous representations
(`TauCeti.ContinuousRep.Iso.charpoly_apply_eq`) and cyclic permutation `g * h ↔ h * g`
(`TauCeti.ContinuousRep.charpoly_apply_mul_comm`, hence conjugation in a group), multiplicative on
products (`TauCeti.ContinuousRep.charpoly_prod_apply`), equal to `(X - 1) ^ finrank A M` on the
trivial representation (`TauCeti.ContinuousRep.charpoly_trivial_apply`), equal to `X - C (χ g)` on
the character line `ofCharacter χ` (`TauCeti.ContinuousRep.charpoly_ofCharacter_apply`), equal to
`(ρ g⁻¹).charpoly` on the contragredient `ρ.dual` (`TauCeti.ContinuousRep.charpoly_dual_apply`),
and compatible with scalar extension (`TauCeti.ContinuousRep.charpoly_baseChange_apply`, together
with `TauCeti.ContinuousRep.linearMap_det_baseChange_apply` for determinants).

On the topological side, when `A` is a topological commutative ring and `M` carries its `A`-module
topology, every coefficient `g ↦ (ρ g).charpoly.coeff k` is continuous
(`TauCeti.ContinuousRep.continuous_charpoly_coeff`): in a finite basis of `M` the matrix of `ρ g`
is continuous (`TauCeti.ContinuousRep.continuous_toMatrix`), and each characteristic coefficient is
a universal polynomial in the matrix entries (`Matrix.continuous_charpoly_coeff`). Consequently, two
continuous representations whose characteristic polynomials agree (after mapping into a common
Hausdorff ring) on a dense subset of `Γ` have equal characteristic polynomials everywhere on `Γ`
(`TauCeti.ContinuousRep.charpoly_map_eq_of_dense`, `TauCeti.ContinuousRep.charpoly_eq_of_dense`).

## Main results

* `TauCeti.ContinuousRep.Iso.charpoly_apply_eq`: isomorphic continuous representations have equal
  characteristic polynomials.
* `TauCeti.ContinuousRep.charpoly_apply_mul_comm` and `TauCeti.ContinuousRep.charpoly_apply_conj`:
  cyclic and conjugation invariance of `(ρ g).charpoly`.
* `TauCeti.ContinuousRep.charpoly_ofCharacter_apply`: `(ofCharacter χ g).charpoly = X - C (χ g)`.
* `TauCeti.ContinuousRep.charpoly_baseChange_apply` and
  `TauCeti.ContinuousRep.linearMap_det_baseChange_apply`: the characteristic polynomial and
  determinant of `g` on `ρ.baseChange B` are the images of those of `ρ g`.
* `TauCeti.ContinuousRep.charpoly_dual_apply`: `(ρ.dual g).charpoly = (ρ g⁻¹).charpoly`.
* `TauCeti.ContinuousRep.continuous_charpoly_coeff`: each coefficient `g ↦ (ρ g).charpoly.coeff k`
  is continuous when `M` carries its module topology over a topological commutative ring `A`.
* `TauCeti.ContinuousRep.charpoly_map_eq_of_dense` and `TauCeti.ContinuousRep.charpoly_eq_of_dense`:
  equality of characteristic polynomials into a Hausdorff ring propagates from a dense subset of `Γ`
  to all of `Γ`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, p. 52.
* J. Newton and J. A. Thorne, *Symmetric power functoriality for holomorphic modular forms*, §1.2,
  p. 7.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *Potential automorphy of `G`-local systems*,
  §2, p. 5.
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti.ContinuousRep

/-! ### Algebraic properties of `(ρ g).charpoly` -/

section Algebraic

variable {Γ A M N : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [Module.Free A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [TopologicalSpace N] [Module.Free A N] [Module.Finite A N]

/-- **Isomorphic continuous representations have the same characteristic polynomials.** -/
theorem Iso.charpoly_apply_eq {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N}
    (e : Iso ρ σ) (g : Γ) : (ρ g).charpoly = (σ g).charpoly :=
  e.toRepresentationEquiv.charpoly_apply_eq g

/-- Cyclic invariance of the characteristic polynomial:
`(ρ (g * h)).charpoly = (ρ (h * g)).charpoly` for any elements `g, h` of the acting monoid `Γ`. -/
theorem charpoly_apply_mul_comm (ρ : ContinuousRep Γ A M) (g h : Γ) :
    (ρ (g * h)).charpoly = (ρ (h * g)).charpoly :=
  ρ.toRepresentation.charpoly_apply_mul_comm g h

/-- The characteristic polynomial is multiplicative on products of continuous representations. -/
@[simp]
theorem charpoly_prod_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ) :
    (ρ.prod σ g).charpoly = (ρ g).charpoly * (σ g).charpoly := by
  rw [← coe_toRepresentation, toRepresentation_prod]
  exact Representation.charpoly_prod_apply ρ.toRepresentation σ.toRepresentation g

variable (Γ A M) in
/-- In the trivial representation every element acts with characteristic polynomial
`(X - 1) ^ rank`. -/
@[simp]
theorem charpoly_trivial_apply (g : Γ) :
    (trivial Γ A M g).charpoly = (X - 1) ^ Module.finrank A M := by
  rw [← coe_toRepresentation, toRepresentation_trivial]
  exact Representation.charpoly_trivial_apply A Γ M g

/-- **The characteristic polynomial of a character line.** The element `g` acts on
`ofCharacter χ` with characteristic polynomial `X - χ g`; the contragredient action would give
`X - (χ g)⁻¹` instead. -/
@[simp]
theorem charpoly_ofCharacter_apply [TopologicalSpace A] [ContinuousMul A] (χ : Γ →ₜ* Aˣ)
    (g : Γ) : (ofCharacter χ g).charpoly = X - C (χ g : A) := by
  rw [← coe_toRepresentation, toRepresentation_ofCharacter]
  exact Representation.charpoly_ofLinearCharacter_apply (χ : Γ →* Aˣ) g

section BaseChange

variable [TopologicalSpace A] [IsModuleTopology A M] (B : Type*) [CommRing B] [TopologicalSpace B]
  [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)]
  [IsModuleTopology B (B ⊗[A] M)]

/-- **The characteristic polynomial of a base change.** The element `g` acts on
`ρ.baseChange B` with characteristic polynomial the image in `B[X]` of that of `ρ g`. -/
theorem charpoly_baseChange_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.baseChange B g).charpoly = (ρ g).charpoly.map (algebraMap A B) := by
  rw [← coe_toRepresentation, toRepresentation_baseChange]
  exact Representation.charpoly_baseChange_apply ρ.toRepresentation B g

/-- **The determinant of a base change.** The element `g` acts on `ρ.baseChange B` with
determinant the image in `B` of that of `ρ g`. -/
theorem linearMap_det_baseChange_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    LinearMap.det (ρ.baseChange B g) = algebraMap A B (LinearMap.det (ρ g)) := by
  rw [baseChange_apply, LinearMap.det_baseChange]

end BaseChange

end Algebraic

section Group

variable {G A M : Type*} [Group G] [TopologicalSpace G] [CommRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [Module.Free A M] [Module.Finite A M]

/-- Conjugation invariance of the characteristic polynomial for a continuous group
representation. -/
theorem charpoly_apply_conj (ρ : ContinuousRep G A M) (g h : G) :
    (ρ (g * h * g⁻¹)).charpoly = (ρ h).charpoly :=
  ρ.toRepresentation.charpoly_apply_conj g h

/-- In a continuous group representation on a finite free module of rank `d`, the characteristic
polynomial of `g⁻¹` is `(-1) ^ d * det (ρ g⁻¹)` times `(ρ g).charpoly.reverse`. -/
theorem charpoly_apply_inv (ρ : ContinuousRep G A M) (g : G) :
    (ρ g⁻¹).charpoly =
      (-1) ^ Module.finrank A M * C (LinearMap.det (ρ g⁻¹)) * (ρ g).charpoly.reverse :=
  ρ.toRepresentation.charpoly_apply_inv g

/-- In the contragredient representation `ρ.dual`, `g` acts with the characteristic polynomial of
`g⁻¹` in `ρ`. -/
theorem charpoly_dual_apply [ContinuousInv G] [TopologicalSpace A] [IsTopologicalRing A]
    [IsModuleTopology A M] [TopologicalSpace (Module.Dual A M)]
    [IsModuleTopology A (Module.Dual A M)] (ρ : ContinuousRep G A M) (g : G) :
    (ρ.dual g).charpoly = (ρ g⁻¹).charpoly := by
  rw [← coe_toRepresentation, toRepresentation_dual]
  exact ρ.toRepresentation.charpoly_dual_apply g

end Group

/-! ### Continuity of characteristic coefficients and density propagation -/

section Continuity

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ]

/-- **Continuity of characteristic coefficients.** When `M` is finite free over a topological
commutative ring `A` and carries its `A`-module topology, every coefficient
`g ↦ (ρ g).charpoly.coeff k` is continuous on `Γ`. -/
@[continuity, fun_prop]
theorem continuous_charpoly_coeff {A M : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M] (ρ : ContinuousRep Γ A M) (k : ℕ) :
    Continuous fun g => (ρ g).charpoly.coeff k := by
  classical
  let b := Module.Free.chooseBasis A M
  simpa only [Function.comp_def, ← LinearMap.charpoly_toMatrix _ b] using
    (Matrix.continuous_charpoly_coeff k).comp (ρ.continuous_toMatrix b)

/-- **Density propagation for characteristic polynomials across coefficient rings.** Let `ρ₁` and
`ρ₂` be continuous representations on finite free modules with their module topologies over
topological commutative rings `A₁` and `A₂`, and let `f₁ : A₁ →+* B`, `f₂ : A₂ →+* B` be continuous
homomorphisms into a Hausdorff commutative ring `B`. If
`((ρ₁ g).charpoly).map f₁ = ((ρ₂ g).charpoly).map f₂` for all `g` in a dense subset `s ⊆ Γ`, then
equality holds for all `g : Γ`. -/
theorem charpoly_map_eq_of_dense {A₁ A₂ B M₁ M₂ : Type*}
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [CommRing B] [TopologicalSpace B] [T2Space B]
    [AddCommGroup M₁] [Module A₁ M₁] [Module.Free A₁ M₁] [Module.Finite A₁ M₁]
    [TopologicalSpace M₁] [IsModuleTopology A₁ M₁]
    [AddCommGroup M₂] [Module A₂ M₂] [Module.Free A₂ M₂] [Module.Finite A₂ M₂]
    [TopologicalSpace M₂] [IsModuleTopology A₂ M₂]
    (ρ₁ : ContinuousRep Γ A₁ M₁) (ρ₂ : ContinuousRep Γ A₂ M₂)
    {f₁ : A₁ →+* B} {f₂ : A₂ →+* B} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    {s : Set Γ} (hs : Dense s)
    (h : ∀ g ∈ s, ((ρ₁ g).charpoly).map f₁ = ((ρ₂ g).charpoly).map f₂) (g : Γ) :
    ((ρ₁ g).charpoly).map f₁ = ((ρ₂ g).charpoly).map f₂ := by
  ext k
  have hc₁ : Continuous fun x : Γ => (((ρ₁ x).charpoly).map f₁).coeff k := by
    simpa only [coeff_map, Function.comp_def] using hf₁.comp (ρ₁.continuous_charpoly_coeff k)
  have hc₂ : Continuous fun x : Γ => (((ρ₂ x).charpoly).map f₂).coeff k := by
    simpa only [coeff_map, Function.comp_def] using hf₂.comp (ρ₂.continuous_charpoly_coeff k)
  exact congrFun (hc₁.ext_on hs hc₂ fun x hx => congrArg (fun p => p.coeff k) (h x hx)) g

/-- **Density propagation for characteristic polynomials** over a Hausdorff topological commutative
ring: agreement on a dense subset `s ⊆ Γ` implies agreement on all of `Γ`. -/
theorem charpoly_eq_of_dense {A M₁ M₂ : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [TopologicalSpace M₁] [IsModuleTopology A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] [Module.Finite A M₂]
    [TopologicalSpace M₂] [IsModuleTopology A M₂]
    (ρ₁ : ContinuousRep Γ A M₁) (ρ₂ : ContinuousRep Γ A M₂)
    {s : Set Γ} (hs : Dense s) (h : ∀ g ∈ s, (ρ₁ g).charpoly = (ρ₂ g).charpoly) (g : Γ) :
    (ρ₁ g).charpoly = (ρ₂ g).charpoly := by
  simpa using charpoly_map_eq_of_dense ρ₁ ρ₂ (f₁ := RingHom.id A) (f₂ := RingHom.id A)
    continuous_id continuous_id hs (fun x hx => by simp [h x hx]) g

end Continuity

end TauCeti.ContinuousRep
