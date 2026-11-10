/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra
public import TauCeti.LinearAlgebra.TensorAlgebra.Grading

/-!
# Koszul-signed derivations of the tensor algebra

Let `G` be an internal `ℤ`-grading of a module `M`, so that the tensor algebra `T(M)` is graded by
input degree (`TauCeti.tensorAlgebraPiece`), and let `σ` be its Koszul sign automorphism, which
multiplies an element of degree `p` by `(-1) ^ p`.  An *odd derivation* of `T(M)` is a linear map
`D` satisfying the Koszul-signed Leibniz rule

`D (x * y) = D x * y + σ x * D y`,

which for `x` of degree `p` is the rule `D (x * y) = D x * y + (-1) ^ p • (x * D y)` of a
differential graded algebra.  Since `T(M)` is free, every linear map `f : M → T(M)` extends
uniquely to such a derivation, `TauCeti.tensorAlgebraDerivation G f`.  It is built from the
universal property: the algebra map `T(M) → Mat₂(T(M))` lifting
`v ↦ !![σ (ι v), f v; 0, ι v]` sends `x` to `!![σ x, D x; 0, x]`, and the Leibniz rule is the
upper right entry of the multiplicativity of this algebra map.

If `f` raises degrees by one then so does `D`; it then anticommutes with `σ`, and the two signed
middle terms of `D (D (x * y))` cancel, so `D ∘ D` is an unsigned derivation.  Hence `D ∘ D = 0`
as soon as `D (f v) = 0` for every generator `v`, and `T(M)` is then a differential graded
algebra.  This is how free differential graded algebras, such as cobar constructions, are
presented: by the values of the differential on generators.  The same construction for path
algebras of graded quivers, whose generators are arrows rather than the elements of a graded
module, is `TauCeti.PathAlgebra.liftDerivation`.

## Main definitions

* `TauCeti.tensorAlgebraDerivation`: the odd derivation of the tensor algebra extending a linear
  map on generators.

## Main results

* `TauCeti.tensorAlgebraDerivation_ι` and `TauCeti.tensorAlgebraDerivation_mul`: the derivation
  extends `f` and satisfies the Koszul-signed Leibniz rule; `TauCeti.tensorAlgebraDerivation_unique`
  says that it is the only such map.
* `TauCeti.tensorAlgebraDerivation_mem_tensorAlgebraPiece`: it raises degrees by `r` when `f` does.
* `TauCeti.tensorAlgebraDerivation_tensorAlgebraDerivation`: for `f` of degree one, its square
  vanishes as soon as it vanishes on generators.
* `TauCeti.isDGAlgebra_tensorAlgebraDerivation`: the resulting differential graded algebra.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, where the differential of the cobar construction is the
  derivation of a tensor algebra determined by its values on generators.
-/

public section

namespace TauCeti

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  (G : InternalGrading R M)

open TensorAlgebra InternalGrading

variable (f : M →ₗ[R] TensorAlgebra R M)

/-- The upper triangular matrix `!![σ (ι v), f v; 0, ι v]` attached to a generator `v`; the algebra
map out of the tensor algebra it induces carries the derivation in its upper right entry. -/
private noncomputable def derivationMatrix :
    M →ₗ[R] Matrix (Fin 2) (Fin 2) (TensorAlgebra R M) where
  toFun v := !![koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 (ι R v), f v; 0, ι R v]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' r v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The algebra map out of the tensor algebra lifting `derivationMatrix`. -/
private noncomputable abbrev derivationLift : TensorAlgebra R M →ₐ[R] Matrix (Fin 2) (Fin 2)
    (TensorAlgebra R M) :=
  lift R (derivationMatrix G f)

/-- The lift has `σ x` and `x` on the diagonal and zero below it. -/
private theorem derivationLift_apply (x : TensorAlgebra R M) :
    derivationLift G f x 0 0 = koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 x ∧
      derivationLift G f x 1 0 = 0 ∧ derivationLift G f x 1 1 = x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
  | ι v => simp [derivationMatrix]
  | mul x y hx hy =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1,
      hy.2.2]
    simp
  | add x y hx hy => simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]

/-- The **odd derivation of the tensor algebra** extending a linear map `f : M → T(M)` on
generators: the unique linear map `D` with `D (ι v) = f v` satisfying the Koszul-signed Leibniz
rule `D (x * y) = D x * y + σ x * D y`, where `σ` multiplies an element of input degree `p` by
`(-1) ^ p`.  See `tensorAlgebraDerivation_ι`, `tensorAlgebraDerivation_mul` and
`tensorAlgebraDerivation_unique`. -/
noncomputable def tensorAlgebraDerivation : TensorAlgebra R M →ₗ[R] TensorAlgebra R M where
  toFun x := derivationLift G f x 0 1
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The derivation takes the prescribed values on generators. -/
@[simp]
theorem tensorAlgebraDerivation_ι (v : M) : tensorAlgebraDerivation G f (ι R v) = f v := by
  simp [tensorAlgebraDerivation, derivationMatrix]

/-- **The Koszul-signed Leibniz rule** for an arbitrary left factor, whose Koszul automorphism
records the sign. -/
theorem tensorAlgebraDerivation_mul (x y : TensorAlgebra R M) :
    tensorAlgebraDerivation G f (x * y) =
      tensorAlgebraDerivation G f x * y +
        koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 x * tensorAlgebraDerivation G f y := by
  obtain ⟨hx₀, -, -⟩ := derivationLift_apply G f x
  obtain ⟨-, -, hy₂⟩ := derivationLift_apply G f y
  simp only [tensorAlgebraDerivation, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Matrix.mul_apply,
    Fin.sum_univ_two, hx₀, hy₂]
  rw [add_comm]

/-- **The graded Leibniz rule** for a left factor of input degree `p`. -/
theorem tensorAlgebraDerivation_mul_of_mem {p : ℤ} {x : TensorAlgebra R M}
    (hx : x ∈ tensorAlgebraPiece G p) (y : TensorAlgebra R M) :
    tensorAlgebraDerivation G f (x * y) =
      tensorAlgebraDerivation G f x * y + p.negOnePow • (x * tensorAlgebraDerivation G f y) := by
  rw [tensorAlgebraDerivation_mul, koszulTwistAlgEquiv_apply_of_mem _ 1 hx, one_mul,
    smul_mul_assoc]

/-- The derivation annihilates the image of the ground ring. -/
@[simp]
theorem tensorAlgebraDerivation_algebraMap (r : R) :
    tensorAlgebraDerivation G f (algebraMap R (TensorAlgebra R M) r) = 0 := by
  simp [tensorAlgebraDerivation, Matrix.algebraMap_matrix_apply]

/-- The derivation annihilates the unit. -/
@[simp]
theorem tensorAlgebraDerivation_one : tensorAlgebraDerivation G f 1 = 0 := by
  simpa using tensorAlgebraDerivation_algebraMap G f 1

/-- **An odd derivation of the tensor algebra is determined by its values on generators**: a linear
map satisfying the Koszul-signed Leibniz rule and agreeing with `f` on generators is
`tensorAlgebraDerivation G f`. -/
theorem tensorAlgebraDerivation_unique (D : TensorAlgebra R M →ₗ[R] TensorAlgebra R M)
    (hmul : ∀ x y, D (x * y) = D x * y + koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 x * D y)
    (hι : ∀ v, D (ι R v) = f v) : D = tensorAlgebraDerivation G f := by
  have hone : D 1 = 0 := by simpa using hmul 1 1
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorAlgebra.induction with
  | algebraMap r => rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, hone,
      tensorAlgebraDerivation_one]
  | ι v => rw [hι, tensorAlgebraDerivation_ι]
  | mul x y hx hy => rw [hmul, tensorAlgebraDerivation_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {G f}

/-- On a product of homogeneous generators the derivation raises the total degree by `r`, when
`f` does on generators. -/
private theorem tensorAlgebraDerivation_tprod_mem {r : ℤ}
    (hf : ∀ {p : ℤ} {v : M}, v ∈ G.piece p → f v ∈ tensorAlgebraPiece G (p + r)) :
    ∀ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M), (∀ i, x i ∈ G.piece (d i)) →
      tensorAlgebraDerivation G f (TensorAlgebra.tprod R M n x) ∈
        tensorAlgebraPiece G (∑ i, d i + r)
  | 0, _, _, _ => by simp
  | n + 1, d, x, hx => by
    have hprod : TensorAlgebra.tprod R M (n + 1) x =
        ι R (x 0) * TensorAlgebra.tprod R M n (fun i ↦ x i.succ) := by
      simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
    have htail := tprod_mem_tensorAlgebraPiece G (fun i ↦ d i.succ) (fun i ↦ x i.succ)
      fun i ↦ hx i.succ
    rw [hprod, tensorAlgebraDerivation_mul_of_mem G f (ι_mem_tensorAlgebraPiece G (hx 0)),
      tensorAlgebraDerivation_ι, Fin.sum_univ_succ]
    refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
    · have h : d 0 + r + ∑ i : Fin n, d i.succ = d 0 + ∑ i : Fin n, d i.succ + r := by abel
      exact h ▸ SetLike.GradedMul.mul_mem (hf (hx 0)) htail
    · have h : d 0 + (∑ i : Fin n, d i.succ + r) = d 0 + ∑ i : Fin n, d i.succ + r := by abel
      exact h ▸ SetLike.GradedMul.mul_mem (ι_mem_tensorAlgebraPiece G (hx 0))
        (tensorAlgebraDerivation_tprod_mem hf n (fun i ↦ d i.succ) (fun i ↦ x i.succ)
          fun i ↦ hx i.succ)

/-- **The derivation raises degrees by `r`** when `f` sends generators of degree `p` to elements
of degree `p + r`. -/
theorem tensorAlgebraDerivation_mem_tensorAlgebraPiece {r : ℤ}
    (hf : ∀ {p : ℤ} {v : M}, v ∈ G.piece p → f v ∈ tensorAlgebraPiece G (p + r)) {p : ℤ}
    {x : TensorAlgebra R M} (hx : x ∈ tensorAlgebraPiece G p) :
    tensorAlgebraDerivation G f x ∈ tensorAlgebraPiece G (p + r) :=
  tensorAlgebraPiece_le
    (C := (tensorAlgebraPiece G (p + r)).comap (tensorAlgebraDerivation G f))
    (fun n d y hy hd ↦ by
      rw [Submodule.mem_comap, ← hd]
      exact tensorAlgebraDerivation_tprod_mem hf n d y hy) hx

variable (hf : ∀ {p : ℤ} {v : M}, v ∈ G.piece p → f v ∈ tensorAlgebraPiece G (p + 1))
include hf

/-- For `f` of degree one, the derivation anticommutes with the Koszul automorphism. -/
theorem koszulTwistAlgEquiv_tensorAlgebraDerivation (x : TensorAlgebra R M) :
    koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 (tensorAlgebraDerivation G f x) =
      -tensorAlgebraDerivation G f (koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 x) := by
  have hhom : LinearMap.IsHomogeneous (tensorAlgebraDerivation G f)
      (ofDecomposition (tensorAlgebraPiece G)).piece
      (ofDecomposition (tensorAlgebraPiece G)).piece 1 := by
    rw [ofDecomposition_piece]
    exact LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦
      tensorAlgebraDerivation_mem_tensorAlgebraPiece hf hx
  simp only [koszulTwistAlgEquiv_apply, hhom.koszulTwist_apply 1 x, mul_one, Int.negOnePow_one,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul]

/-- For `f` of degree one, the square of the derivation is an unsigned derivation: the signed
middle terms of `D (D (x * y))` cancel because `D` anticommutes with the Koszul automorphism. -/
private theorem tensorAlgebraDerivation_sq_mul (x y : TensorAlgebra R M) :
    tensorAlgebraDerivation G f (tensorAlgebraDerivation G f (x * y)) =
      tensorAlgebraDerivation G f (tensorAlgebraDerivation G f x) * y +
        x * tensorAlgebraDerivation G f (tensorAlgebraDerivation G f y) := by
  have hσσ : koszulTwistAlgEquiv (tensorAlgebraPiece G) 1
      (koszulTwistAlgEquiv (tensorAlgebraPiece G) 1 x) = x := by
    simp
  rw [tensorAlgebraDerivation_mul, map_add, tensorAlgebraDerivation_mul,
    tensorAlgebraDerivation_mul, koszulTwistAlgEquiv_tensorAlgebraDerivation hf, hσσ, neg_mul]
  abel

/-- **The square of the derivation vanishes** as soon as it vanishes on generators, for `f` of
degree one. -/
theorem tensorAlgebraDerivation_tensorAlgebraDerivation
    (hsq : ∀ v, tensorAlgebraDerivation G f (f v) = 0) (x : TensorAlgebra R M) :
    tensorAlgebraDerivation G f (tensorAlgebraDerivation G f x) = 0 := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp
  | ι v => rw [tensorAlgebraDerivation_ι, hsq]
  | mul x y hx hy => rw [tensorAlgebraDerivation_sq_mul hf, hx, hy, zero_mul, mul_zero, add_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **The tensor algebra, graded by input degree, is a differential graded algebra** for the odd
derivation extending a degree-one map `f` whose derivation vanishes on the values of `f`. -/
theorem isDGAlgebra_tensorAlgebraDerivation (hsq : ∀ v, tensorAlgebraDerivation G f (f v) = 0) :
    IsDGAlgebra (tensorAlgebraPiece G) (tensorAlgebraDerivation G f) where
  map_mem hx := tensorAlgebraDerivation_mem_tensorAlgebraPiece hf hx
  sq_zero := tensorAlgebraDerivation_tensorAlgebraDerivation hf hsq
  leibniz hx y := tensorAlgebraDerivation_mul_of_mem G f hx y

end TauCeti
