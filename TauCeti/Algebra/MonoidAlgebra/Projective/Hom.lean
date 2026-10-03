/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Equiv
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Untwisting a regular tensor representation

Let `G` be a group, `k` a commutative ring, and `S` a `k`-linear representation of `G`.  The
diagonal action on `k[G] ⊗ S` is equivalent to the action on the regular factor alone.  The
equivalence sends

`g ⊗ s ↦ g ⊗ g⁻¹s`.

This Hopf-module calculation is the structural input for proving that the conjugation module
`Hom_k(P, S)` is projective when `P` is finitely generated projective over a finite group algebra.
That projectivity, in turn, is needed in Swan's rational detection theorem for projective
`\mathbb Z_p[G]`-lattices.

## Main results

* `Representation.leftRegularTensorEquivTrivial`: untwists the diagonal action on
  `k[G] ⊗ S` to the action on the regular factor alone.
* `Representation.dualLeftRegularEquiv`: identifies the regular representation of a
  finite group with its dual.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14–16.
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

open scoped MonoidAlgebra TensorProduct

noncomputable section

namespace Representation

universe u v w

variable {k : Type u} [CommRing k] {G : Type v} [Group G]
  {W : Type w} [AddCommGroup W] [Module k W]

/-- The pointwise change of coordinates on finitely supported functions which sends the value at
`g` through `σ(g⁻¹)`.  Its inverse sends the value at `g` through `σ(g)`. -/
private def finsuppTwistEquiv (σ : Representation k G W) :
    (G →₀ W) ≃ₗ[k] (G →₀ W) :=
  LinearEquiv.ofLinearMap
    (Finsupp.lsum k fun g ↦ (Finsupp.lsingle g).comp (σ g⁻¹))
    (Finsupp.lsum k fun g ↦ (Finsupp.lsingle g).comp (σ g))
    (by
      ext g x h
      simp)
    (by
      ext g x h
      simp)

@[simp]
private theorem finsuppTwistEquiv_single (σ : Representation k G W) (g : G) (w : W) :
    finsuppTwistEquiv σ (Finsupp.single g w) = Finsupp.single g (σ g⁻¹ w) := by
  simp [finsuppTwistEquiv]

/-- The standard identification `k[G] ⊗ W ≃ G →₀ W`. -/
private def monoidAlgebraTensorEquivFinsupp :
    MonoidAlgebra k G ⊗[k] W ≃ₗ[k] G →₀ W :=
  by
  classical
  exact (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k)
    (LinearEquiv.refl k W)).trans (TensorProduct.finsuppScalarLeft k W G)

omit [Group G] in
@[simp]
private theorem monoidAlgebraTensorEquivFinsupp_single_tmul
    (g : G) (r : k) (w : W) :
    monoidAlgebraTensorEquivFinsupp (G := G) (MonoidAlgebra.single g r ⊗ₜ[k] w) =
      Finsupp.single g (r • w) := by
  simp [monoidAlgebraTensorEquivFinsupp,
    TensorProduct.finsuppScalarLeft_apply_tmul]

/-- The linear equivalence underlying regular-tensor untwisting. -/
private def leftRegularTensorLinearEquiv (σ : Representation k G W) :
    MonoidAlgebra k G ⊗[k] W ≃ₗ[k] MonoidAlgebra k G ⊗[k] W :=
  monoidAlgebraTensorEquivFinsupp (k := k) (G := G) (W := W) |>.trans <|
    (finsuppTwistEquiv σ).trans
      (monoidAlgebraTensorEquivFinsupp (k := k) (G := G) (W := W)).symm

@[simp]
private theorem leftRegularTensorLinearEquiv_single_tmul (σ : Representation k G W)
    (g : G) (r : k) (w : W) :
    leftRegularTensorLinearEquiv σ (MonoidAlgebra.single g r ⊗ₜ[k] w) =
      MonoidAlgebra.single g r ⊗ₜ[k] σ g⁻¹ w := by
  apply (monoidAlgebraTensorEquivFinsupp (k := k) (G := G) (W := W)).injective
  simp [leftRegularTensorLinearEquiv, monoidAlgebraTensorEquivFinsupp_single_tmul,
    finsuppTwistEquiv_single]

/-- **Untwisting the regular tensor factor.**  The diagonal action on `k[G] ⊗ S` is equivalent
to the action on the regular factor alone.  On pure tensors the equivalence is
`g ⊗ s ↦ g ⊗ g⁻¹s`.

No finiteness hypothesis on `G` or `S` is needed. -/
def leftRegularTensorEquivTrivial (σ : Representation k G W) :
    ((leftRegular k G).tprod σ).Equiv
      ((leftRegular k G).tprod (trivial k G W)) :=
  .mk
    (leftRegularTensorLinearEquiv σ)
    (fun h ↦ by
      ext g w
      simp [leftRegularTensorLinearEquiv_single_tmul,
        Representation.inv_self_apply])

/-- Untwisting sends `g ⊗ s` to `g ⊗ g⁻¹s`. -/
@[simp]
theorem leftRegularTensorEquivTrivial_single_tmul (σ : Representation k G W)
    (g : G) (r : k) (w : W) :
    leftRegularTensorEquivTrivial σ (MonoidAlgebra.single g r ⊗ₜ[k] w) =
      MonoidAlgebra.single g r ⊗ₜ[k] σ g⁻¹ w := by
  exact leftRegularTensorLinearEquiv_single_tmul σ g r w

/-- The inverse of untwisting sends `g ⊗ s` to `g ⊗ gs`. -/
@[simp]
theorem leftRegularTensorEquivTrivial_symm_single_tmul (σ : Representation k G W)
    (g : G) (r : k) (w : W) :
    (leftRegularTensorEquivTrivial σ).symm (MonoidAlgebra.single g r ⊗ₜ[k] w) =
      MonoidAlgebra.single g r ⊗ₜ[k] σ g w := by
  apply (leftRegularTensorEquivTrivial σ).injective
  simp [Representation.inv_self_apply]

section Finite

variable [Finite G]

/-- **The regular representation is self-dual.** The coefficient pairing identifies the dual of
the left regular representation with the left regular representation. -/
def dualLeftRegularEquiv :
    (leftRegular k G).dual.Equiv (leftRegular k G) := by
  classical
  let b := MonoidAlgebra.basis G k
  exact .mk b.toDualEquiv.symm (fun g ↦ by
    ext f h
    change b.coord h (b.toDualEquiv.symm ((leftRegular k G).dual g f)) =
      b.coord h ((leftRegular k G) g (b.toDualEquiv.symm f))
    rw [b.coord_toDualEquiv_symm_apply]
    have hcoeff (m : MonoidAlgebra k G) :
        ((leftRegular k G) g m).coeff h = m.coeff (g⁻¹ * h) := by
      induction m using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | single x r =>
        rw [ofMulAction_single]
        by_cases hx : x = g⁻¹ * h
        · subst x
          simp
        · have hgx : g * x ≠ h := by
            intro heq
            apply hx
            calc
              x = g⁻¹ * (g * x) := by simp
              _ = g⁻¹ * h := by rw [heq]
          simp [hx, hgx]
    rw [show b.coord h ((leftRegular k G) g (b.toDualEquiv.symm f)) =
      b.coord (g⁻¹ * h) (b.toDualEquiv.symm f) by exact hcoeff _]
    rw [b.coord_toDualEquiv_symm_apply]
    simp [b, Module.Dual.transpose_apply])

/-- Under regular self-duality, the coefficient at `g` is evaluation on the basis vector `g`. -/
@[simp]
theorem dualLeftRegularEquiv_coeff (f : Module.Dual k (MonoidAlgebra k G)) (g : G) :
    (dualLeftRegularEquiv (k := k) (G := G) f).coeff g =
      f (MonoidAlgebra.single g 1) := by
  classical
  let b := MonoidAlgebra.basis G k
  change b.coord g (b.toDualEquiv.symm f) = f (b g)
  rw [b.coord_toDualEquiv_symm_apply]
  simp [b]

end Finite

end Representation
