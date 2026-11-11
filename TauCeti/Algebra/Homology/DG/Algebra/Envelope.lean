/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# The differential of a free bimodule over a differential graded algebra

Let `(A, d)` be an internally `ℤ`-graded differential graded algebra over a commutative ring `R`,
and `σ : a ↦ (-1) ^ |a| a` its Koszul twist `TauCeti.InternalGrading.koszulTwist`. The free
`A`-bimodule `A s A` on one generator `s` of degree `n` which is a cycle is identified with the
enveloping algebra `A ⊗[R] Aᵐᵒᵖ` by `x s y ↦ x ⊗ y`, and its differential is

`x ⊗ y ↦ d x ⊗ y + (-1) ^ n σ x ⊗ d y`.

The twist `σ` makes this formula meaningful for inhomogeneous `x`; for `x` of degree `p` the sign is
`(-1) ^ (p + n)`. The differential squares to zero and satisfies a Leibniz rule for the
multiplication of the enveloping algebra, in which the Koszul twist acts on the tensor factors of
the left factor.

## Main definitions

* `TauCeti.envelopeDifferential`: the differential of the free bimodule on a cycle of degree `n`,
  on the enveloping algebra.

## Main results

* `TauCeti.envelopeDifferential_tmul` and `TauCeti.envelopeDifferential_tmul_of_mem`: the
  differential on pure tensors.
* `TauCeti.envelopeDifferential_mul` and `TauCeti.envelopeDifferential_mul_of_sign`: the Leibniz
  rule for the multiplication of the enveloping algebra.
* `TauCeti.envelopeDifferential_envelopeDifferential`: **the differential squares to zero**.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
* B. Keller, *Deformed Calabi--Yau completions*, J. Reine Angew. Math. 654 (2011), 125--180,
  arXiv:0908.3499, for free bimodules over differential graded algebras.
-/

public section

open MulOpposite
open scoped TensorProduct

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A linear endomorphism, transported to the opposite, in this file. -/
local notation "op[" f "]" =>
  LinearMap.comp (LinearEquiv.toLinearMap (opLinearEquiv R))
    (LinearMap.comp f (LinearEquiv.toLinearMap (LinearEquiv.symm (opLinearEquiv R))))

section Def

variable (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] (d : A →ₗ[R] A)

/-- The Koszul twist `x ↦ (-1) ^ |x| x` of the grading `𝒜`, in this file. -/
local notation "σ" => InternalGrading.koszulTwist (InternalGrading.ofDecomposition 𝒜) 1

/-- **The differential of the free bimodule on one generator of degree `n`**, written on the
enveloping algebra `A ⊗[R] Aᵐᵒᵖ` of a differential graded algebra `(A, d)` graded by `𝒜`: for `x`
homogeneous of degree `|x|`, it sends `x ⊗ y` to `d x ⊗ y + (-1) ^ (|x| + n) x ⊗ d y`
(`TauCeti.envelopeDifferential_tmul_of_mem`). It is the differential of `x s y ↦ x ⊗ y` for a
generator `s` of degree `n` which is a cycle, and it squares to zero
(`TauCeti.envelopeDifferential_envelopeDifferential`). -/
noncomputable def envelopeDifferential (n : ℤ) : A ⊗[R] Aᵐᵒᵖ →ₗ[R] A ⊗[R] Aᵐᵒᵖ :=
  TensorProduct.map d LinearMap.id + negOnePowCast R n • TensorProduct.map σ op[d]

variable {𝒜 d}

/-- **The differential of the free bimodule on a generator of degree `n`** on a pure tensor:
`d (x ⊗ y) = d x ⊗ y + (-1) ^ n σ x ⊗ d y`, for `σ` the Koszul twist `x ↦ (-1) ^ |x| x`. -/
@[simp]
theorem envelopeDifferential_tmul (n : ℤ) (x y : A) :
    envelopeDifferential 𝒜 d n (x ⊗ₜ[R] op y) =
      d x ⊗ₜ[R] op y + negOnePowCast R n • (σ x ⊗ₜ[R] op (d y)) := by
  simp [envelopeDifferential]

/-- The differential of the free bimodule on a generator of degree `n` on a pure tensor with
homogeneous left factor: `d (x ⊗ y) = d x ⊗ y + (-1) ^ (|x| + n) x ⊗ d y`. -/
theorem envelopeDifferential_tmul_of_mem (n : ℤ) {p : ℤ} {x : A} (hx : x ∈ 𝒜 p) (y : A) :
    envelopeDifferential 𝒜 d n (x ⊗ₜ[R] op y) =
      d x ⊗ₜ[R] op y + negOnePowCast R (p + n) • (x ⊗ₜ[R] op (d y)) := by
  rw [envelopeDifferential_tmul, InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hx,
    one_mul, ← negOnePowCast_eq_intCast, ← TensorProduct.smul_tmul', smul_smul,
    ← negOnePowCast_add, add_comm n p]

/-- Expand the enveloping-action Leibniz expression on a pure tensor with homogeneous left
factor. The two module elements may be chosen independently; in a Leibniz rule they are an
element and its differential. -/
theorem envelopeDifferential_tmul_smul_add {M : Type*} [AddCommGroup M]
    [Module R M] [Module (A ⊗[R] Aᵐᵒᵖ) M] [IsScalarTower R (A ⊗[R] Aᵐᵒᵖ) M]
    (n : ℤ) {p : ℤ} {x : A} (hx : x ∈ 𝒜 p) (y : A) (z z' : M) :
    envelopeDifferential 𝒜 d n (x ⊗ₜ[R] op y) • z +
        TensorProduct.map σ LinearMap.id (x ⊗ₜ[R] op y) • z' =
      (d x ⊗ₜ[R] op y) • z + negOnePowCast R p • ((x ⊗ₜ[R] op y) • z') +
        negOnePowCast R (p + n) • ((x ⊗ₜ[R] op (d y)) • z) := by
  simp only [envelopeDifferential_tmul_of_mem n hx, add_smul,
    TensorProduct.map_tmul, LinearMap.id_apply,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hx, one_mul,
    ← negOnePowCast_eq_intCast, ← TensorProduct.smul_tmul', smul_assoc,
    add_right_comm]

end Def

section DG

variable {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A}

/-- The Koszul twist `x ↦ (-1) ^ |x| x` of the grading `𝒜`, in this file. -/
local notation "σ" => InternalGrading.koszulTwist (InternalGrading.ofDecomposition 𝒜) 1

/-- **The Leibniz rule of the enveloping differential**, with the sign of the right factor spelled
out by the Koszul twist on both of its tensor factors. -/
theorem envelopeDifferential_mul (hd : IsNonUnitalDGAlgebra 𝒜 d) (n : ℤ) (u v : A ⊗[R] Aᵐᵒᵖ) :
    envelopeDifferential 𝒜 d n (u * v) =
      TensorProduct.map d LinearMap.id u * v +
        TensorProduct.map σ LinearMap.id u * envelopeDifferential 𝒜 d n v +
          negOnePowCast R n • (TensorProduct.map σ op[d] u * TensorProduct.map σ op[σ] v) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [add_mul, map_add, hu, hu', smul_add]; abel
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp only [mul_add, map_add, hv, hv', smul_add]; abel
    | tmul x' y' =>
      obtain ⟨y, rfl⟩ := (opLinearEquiv R).surjective y
      obtain ⟨y', rfl⟩ := (opLinearEquiv R).surjective y'
      simp only [coe_opLinearEquiv, Algebra.TensorProduct.tmul_mul_tmul, ← op_mul,
        envelopeDifferential_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, coe_opLinearEquiv_symm, unop_op,
        hd.leibniz_koszulTwist, InternalGrading.koszulTwist_ofDecomposition_mul, op_add,
        TensorProduct.tmul_add, TensorProduct.add_tmul, smul_add, mul_add, mul_smul_comm]
      abel

/-- The Leibniz rule of the enveloping differential against a right factor `v` on which the Koszul
twist of both tensor factors acts as the sign `(-1) ^ m`: the left factor then sees the
differential of a generator of degree `n + m`. -/
theorem envelopeDifferential_mul_of_sign (hd : IsNonUnitalDGAlgebra 𝒜 d) (n m : ℤ)
    {v : A ⊗[R] Aᵐᵒᵖ} (hv : TensorProduct.map σ op[σ] v = negOnePowCast R m • v)
    (u : A ⊗[R] Aᵐᵒᵖ) :
    envelopeDifferential 𝒜 d n (u * v) =
      envelopeDifferential 𝒜 d (n + m) u * v +
        TensorProduct.map σ LinearMap.id u * envelopeDifferential 𝒜 d n v := by
  rw [envelopeDifferential_mul hd, hv, mul_smul_comm, smul_smul, ← negOnePowCast_add]
  simp only [envelopeDifferential, LinearMap.add_apply, LinearMap.smul_apply, add_mul,
    smul_mul_assoc]
  abel

/-- The Leibniz rule against a homogeneous enveloping element of total degree `m`.
The differential on the left factor has generator degree `n + m`. -/
theorem envelopeDifferential_mul_of_mem (hd : IsNonUnitalDGAlgebra 𝒜 d) (n : ℤ)
    {m : ℤ} {v : A ⊗[R] Aᵐᵒᵖ}
    (hv : v ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition 𝒜).opposite).piece m) (u : A ⊗[R] Aᵐᵒᵖ) :
    envelopeDifferential 𝒜 d n (u * v) =
      envelopeDifferential 𝒜 d (n + m) u * v +
        TensorProduct.map σ LinearMap.id u * envelopeDifferential 𝒜 d n v := by
  apply envelopeDifferential_mul_of_sign hd n m (u := u)
  have hop : op[σ] = (InternalGrading.ofDecomposition 𝒜).opposite.koszulTwist 1 := by
    ext x
    simp
  rw [hop, ← InternalGrading.koszulTwist_tensorProduct]
  simpa only [one_mul, negOnePowCast_eq_intCast] using
    InternalGrading.koszulTwist_apply_of_mem _ hv (q := 1)

omit [SetLike.GradedMul 𝒜] in
/-- The enveloping differential raises total tensor degree by one whenever the original
endomorphism does, independently of the degree of its free generator. The bundled grading
may carry any decomposition of the original homogeneous pieces. -/
theorem isHomogeneous_envelopeDifferential (G : InternalGrading R A) (hG : G.piece = 𝒜)
    (hdeg : LinearMap.IsHomogeneous d G.piece G.piece 1) (n : ℤ) :
    LinearMap.IsHomogeneous (envelopeDifferential 𝒜 d n)
      (G.tensorProduct G.opposite).piece (G.tensorProduct G.opposite).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro q z hz
  refine G.tensorProduct_piece_le G.opposite
    (C := ((G.tensorProduct G.opposite).piece (q + 1)).comap
      (envelopeDifferential 𝒜 d n)) (fun p x hx y hy ↦ ?_) hz
  rw [Submodule.mem_comap, ← op_unop y,
    envelopeDifferential_tmul_of_mem n (by simpa only [hG] using hx)]
  have hy' := (G.mem_opposite_piece_iff _ _).mp hy
  have hl := G.tmul_mem_tensorProduct G.opposite (hdeg.map_mem hx)
    ((G.op_mem_opposite_piece_iff _ _).mpr hy')
  have hr := G.tmul_mem_tensorProduct G.opposite hx
    ((G.op_mem_opposite_piece_iff _ _).mpr (hdeg.map_mem hy'))
  exact add_mem (by convert hl using 1; congr 1; omega)
    (Submodule.smul_mem _ _ (by convert hr using 1; congr 1; omega))

/-- **The enveloping differential squares to zero.** -/
@[simp]
theorem envelopeDifferential_envelopeDifferential (hd : IsNonUnitalDGAlgebra 𝒜 d) (n : ℤ)
    (u : A ⊗[R] Aᵐᵒᵖ) :
    envelopeDifferential 𝒜 d n (envelopeDifferential 𝒜 d n u) = 0 := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', add_zero]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := (opLinearEquiv R).surjective y
    simp only [coe_opLinearEquiv, envelopeDifferential_tmul, map_add, map_smul, hd.sq_zero,
      hd.koszulTwist_map, InternalGrading.koszulTwist_koszulTwist, op_zero, TensorProduct.tmul_zero,
      TensorProduct.zero_tmul, smul_zero, add_zero, zero_add, TensorProduct.neg_tmul, smul_neg]
    abel

end DG

end TauCeti
