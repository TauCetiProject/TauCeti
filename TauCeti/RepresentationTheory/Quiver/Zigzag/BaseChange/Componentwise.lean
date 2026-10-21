/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Multiplication
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Scalar extension of the public zigzag algebra

For a finite simple graph `G` and a commutative-ring algebra `k → l`, the comparison
`l ⊗[k] zigzagAlgebra k G ≃ₐ[l] zigzagAlgebra l G` preserves the vertex, arrow and volume
basis. In particular, the volume at an isolated vertex remains the infinitesimal generator
of its dual-number factor. Disconnected and empty graphs are included, without flatness
or injectivity assumptions on the coefficient map.

The comparison uses `Algebra.TensorProduct.basis` and the coefficient-independent
multiplication table of the componentwise algebra. Its coefficient formula describes all
pure tensors; its inverse expands an element in the vertex–arrow–volume basis.

## References

* Huerfano–Khovanov, *A category for the adjoint representation*, Section 3, for zigzag
  algebras and the exceptional one-vertex convention.
* Ehrig–Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2, for the basis
  and multiplication table.
-/

public section

namespace SimpleGraph

open TauCeti
open scoped TensorProduct

universe u w z

variable {k : Type w} {l : Type z} [CommRing k] [CommRing l] [Algebra k l]
  {V : Type u} (G : SimpleGraph V) [Finite V]

private noncomputable def scalarExtensionLinearEquiv :
    l ⊗[k] zigzagAlgebra k G ≃ₗ[l] zigzagAlgebra l G :=
  (Algebra.TensorProduct.basis l (zigzagAlgebraBasis k G)).equiv
    (zigzagAlgebraBasis l G) (Equiv.refl _)

private theorem scalarExtensionLinearEquiv_tmul_basis (b : ZigzagBasisIndex G) :
    scalarExtensionLinearEquiv (k := k) (l := l) G
      (1 ⊗ₜ[k] zigzagAlgebraBasis k G b) = zigzagAlgebraBasis l G b := by
  rw [← Algebra.TensorProduct.basis_apply]
  exact Module.Basis.equiv_apply _ _ _ _

private theorem scalarExtensionLinearEquiv_mul
    (x y : l ⊗[k] zigzagAlgebra k G) :
    scalarExtensionLinearEquiv G (x * y) =
      scalarExtensionLinearEquiv G x * scalarExtensionLinearEquiv G y := by
  let e := scalarExtensionLinearEquiv (k := k) (l := l) G
  let b := Algebra.TensorProduct.basis l (zigzagAlgebraBasis k G)
  refine (LinearMap.map_mul_iff e.toLinearMap).2 ?_ x y
  apply b.ext
  intro i
  apply b.ext
  intro j
  simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearMap.mul_apply', LinearEquiv.coe_coe, b, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, zigzagAlgebraBasis_mul]
  cases hmul : zigzagBasisMul G i j <;>
    simp [e, hmul, scalarExtensionLinearEquiv_tmul_basis]

/-- Scalar extension of the public componentwise zigzag algebra, including its dual-number
factors at isolated vertices. It fixes every vertex, arrow and volume basis vector. -/
noncomputable def zigzagAlgebraScalarExtensionEquiv :
    l ⊗[k] zigzagAlgebra k G ≃ₐ[l] zigzagAlgebra l G :=
  let e := scalarExtensionLinearEquiv (k := k) (l := l) G
  -- A bijective multiplicative map preserves the unit, by `MulEquiv.map_one`.
  let m : (l ⊗[k] zigzagAlgebra k G) ≃* zigzagAlgebra l G :=
    { e.toEquiv with map_mul' := scalarExtensionLinearEquiv_mul G }
  AlgEquiv.ofLinearEquiv e m.map_one (scalarExtensionLinearEquiv_mul G)

/-- The scalar-extension comparison on a pure tensor with a basis vector. The volume case
includes the infinitesimal generator at every isolated vertex. -/
@[simp]
theorem zigzagAlgebraScalarExtensionEquiv_tmul_zigzagAlgebraBasis
    (a : l) (b : ZigzagBasisIndex G) :
    zigzagAlgebraScalarExtensionEquiv G (a ⊗ₜ[k] zigzagAlgebraBasis k G b) =
      a • zigzagAlgebraBasis l G b := by
  calc
    zigzagAlgebraScalarExtensionEquiv G (a ⊗ₜ[k] zigzagAlgebraBasis k G b) =
        zigzagAlgebraScalarExtensionEquiv G
          (a • (1 ⊗ₜ[k] zigzagAlgebraBasis k G b)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = a • zigzagAlgebraScalarExtensionEquiv G
        (1 ⊗ₜ[k] zigzagAlgebraBasis k G b) := map_smul _ _ _
    _ = a • zigzagAlgebraBasis l G b :=
      congrArg (a • ·) (scalarExtensionLinearEquiv_tmul_basis G b)

/-- The inverse comparison sends each basis vector to its unit pure tensor. -/
@[simp]
theorem zigzagAlgebraScalarExtensionEquiv_symm_zigzagAlgebraBasis
    (b : ZigzagBasisIndex G) :
    (zigzagAlgebraScalarExtensionEquiv (k := k) (l := l) G).symm
      (zigzagAlgebraBasis l G b) = 1 ⊗ₜ[k] zigzagAlgebraBasis k G b := by
  apply (zigzagAlgebraScalarExtensionEquiv G).injective
  simp

private theorem zigzagAlgebraScalarExtensionEquiv_repr (y : l ⊗[k] zigzagAlgebra k G) :
    (zigzagAlgebraBasis l G).repr (zigzagAlgebraScalarExtensionEquiv G y) =
      (Algebra.TensorProduct.basis l (zigzagAlgebraBasis k G)).repr y := by
  have h : (zigzagAlgebraBasis l G).repr.toLinearMap.comp
      (zigzagAlgebraScalarExtensionEquiv (k := k) (l := l) G).toLinearMap =
      (Algebra.TensorProduct.basis l (zigzagAlgebraBasis k G)).repr.toLinearMap := by
    apply (Algebra.TensorProduct.basis l (zigzagAlgebraBasis k G)).ext
    intro b
    simp [Algebra.TensorProduct.basis_apply]
  exact LinearMap.congr_fun h y

/-- On an arbitrary pure tensor, every basis coefficient is extended along the algebra map
and multiplied by the tensor's coefficient. -/
@[simp]
theorem zigzagAlgebraScalarExtensionEquiv_repr_tmul (a : l) (x : zigzagAlgebra k G)
    (b : ZigzagBasisIndex G) :
    (zigzagAlgebraBasis l G).repr (zigzagAlgebraScalarExtensionEquiv G (a ⊗ₜ[k] x)) b =
      a * algebraMap k l ((zigzagAlgebraBasis k G).repr x b) := by
  rw [zigzagAlgebraScalarExtensionEquiv_repr, Algebra.TensorProduct.basis_repr_tmul]
  simp

/-- The inverse scalar-extension comparison is the basis expansion with coefficients in the
left tensor factor. -/
theorem zigzagAlgebraScalarExtensionEquiv_symm_apply (x : zigzagAlgebra l G) :
    (zigzagAlgebraScalarExtensionEquiv (k := k) (l := l) G).symm x =
      ((zigzagAlgebraBasis l G).repr x).sum
        (fun b a => a ⊗ₜ[k] zigzagAlgebraBasis k G b) := by
  apply (zigzagAlgebraScalarExtensionEquiv G).injective
  rw [AlgEquiv.apply_symm_apply, Finsupp.sum, map_sum]
  simp only [zigzagAlgebraScalarExtensionEquiv_tmul_zigzagAlgebraBasis]
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
    ((zigzagAlgebraBasis l G).linearCombination_repr x).symm

end SimpleGraph
