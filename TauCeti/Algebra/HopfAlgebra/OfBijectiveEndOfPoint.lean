/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Antipodes from the universal point action

Let `B` be a commutative bialgebra over a commutative semiring `R`. The regular comodule `B`
carries the action of the universal point `AlgHom.id R B`, the `B`-linear endomorphism

```text
T : B ⊗[R] B → B ⊗[R] B,    a ⊗ b ↦ a • ∑ b₍₂₎ ⊗ b₍₁₎
```

(`TauCeti.Comodule.endOfPoint B (AlgHom.id R B)`). When `B` is a Hopf algebra, `T` is invertible,
with inverse given by the antipode. This file proves the converse: if `T` is bijective, then

```text
S b = (id ⊗ ε) (T⁻¹ (1 ⊗ b))
```

satisfies both antipode identities, so `B` is a Hopf algebra with antipode `S`. No other
hypothesis is imposed: neither finiteness nor a field of scalars.

The first identity `∑ S(b₍₁₎) b₍₂₎ = ε(b)` is the equation `T⁻¹ (T (1 ⊗ b)) = 1 ⊗ b`, read
through `id ⊗ ε`. For the second, the first identity and coassociativity show that
`a ⊗ b ↦ a • ∑ S(b₍₂₎) ⊗ b₍₁₎` is a left inverse of `T`; since `T` is bijective it is `T⁻¹`.
Since `(id ⊗ ε) ∘ T` is multiplication, `T (T⁻¹ (1 ⊗ b)) = 1 ⊗ b` read through `id ⊗ ε` is
`∑ b₍₁₎ S(b₍₂₎) = ε(b)`.

This is how rigidity of finite comodules produces an antipode in Tannakian reconstruction: rigidity
makes the point action invertible on every finite comodule, hence on the regular comodule.

## Main declarations

* `TauCeti.HopfAlgebra.antipodeOfBijective`: the antipode `b ↦ (id ⊗ ε) (T⁻¹ (1 ⊗ b))`.
* `TauCeti.HopfAlgebra.mul_antipodeOfBijective_rTensor_comul` and
  `TauCeti.HopfAlgebra.mul_antipodeOfBijective_lTensor_comul`: the two antipode identities.
* `TauCeti.HopfAlgebra.ofBijective`: the resulting Hopf algebra structure on `B`.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), proof of Proposition 2.16 and Theorem 2.11.
* J. S. Milne, *Algebraic Groups* (2017), §§3.c and 9.4, for the dictionary between antipodes
  and inverses of points.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

variable {R : Type u} {B : Type v} [CommSemiring R] [CommSemiring B] [Bialgebra R B]

/-- The universal point acts on the regular comodule by `a ⊗ b ↦ a • ∑ b₍₂₎ ⊗ b₍₁₎`. -/
private theorem endOfPoint_id_tmul (a b : B) :
    Comodule.endOfPoint B (AlgHom.id R B) (a ⊗ₜ[R] b) =
      a • TensorProduct.comm R B B (comul (R := R) b) := by
  rw [Comodule.endOfPoint_tmul, AlgHom.toLinearMap_id, LinearMap.lTensor_id,
    LinearMap.id_apply, Comodule.instSelf_coact]

/-- Counit evaluation after the universal point action is multiplication. -/
private theorem baseChange_counit_endOfPoint_id (x : B ⊗[R] B) :
    Module.Dual.baseChange B (counit (R := R) (A := B))
        (Comodule.endOfPoint B (AlgHom.id R B) x) = LinearMap.mul' R B x := by
  have hcomm : (Module.Dual.baseChange B (counit (R := R) (A := B))).restrictScalars R ∘ₗ
      (TensorProduct.comm R B B).toLinearMap =
        (TensorProduct.lid R B).toLinearMap ∘ₗ (counit (R := R) (A := B)).rTensor B := by
    refine TensorProduct.ext' fun x y ↦ ?_
    simp
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | tmul a b =>
      have hb := LinearMap.congr_fun hcomm (comul (R := R) b)
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] at hb
      rw [endOfPoint_id_tmul, LinearMap.map_smul, hb, LinearMap.mul'_apply, smul_eq_mul]

variable (h : Function.Bijective (Comodule.endOfPoint B (AlgHom.id R B)))

/-- The antipode of a commutative bialgebra on which the universal point acts bijectively:
`S b = (id ⊗ ε) (T⁻¹ (1 ⊗ b))`, where `T` is the action of the universal point on the regular
comodule. -/
noncomputable def antipodeOfBijective : B →ₗ[R] B :=
  (Module.Dual.baseChange B (counit (R := R) (A := B))).restrictScalars R ∘ₗ
    ((LinearEquiv.ofBijective _ h).symm.toLinearMap.restrictScalars R) ∘ₗ
      TensorProduct.mk R B B 1

/-- The antipode is counit evaluation of the inverse universal point action on `1 ⊗ b`. -/
theorem antipodeOfBijective_apply (b : B) :
    antipodeOfBijective h b =
      Module.Dual.baseChange B (counit (R := R) (A := B))
        ((LinearEquiv.ofBijective _ h).symm (1 ⊗ₜ[R] b)) :=
  (rfl)

/-- Multiplication after applying the antipode to the left tensor factor is counit evaluation of
the inverse universal point action, after swapping the factors. -/
private theorem mul'_rTensor_antipodeOfBijective (x : B ⊗[R] B) :
    LinearMap.mul' R B ((antipodeOfBijective h).rTensor B x) =
      Module.Dual.baseChange B (counit (R := R) (A := B))
        ((LinearEquiv.ofBijective _ h).symm (TensorProduct.comm R B B x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | tmul c d =>
      have hdc : d ⊗ₜ[R] c = d • ((1 : B) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, hdc,
        LinearEquiv.map_smul, LinearMap.map_smul, smul_eq_mul, mul_comm,
        antipodeOfBijective_apply]

/-- The first antipode identity: `∑ S(b₍₁₎) b₍₂₎ = ε(b)`. -/
theorem mul_antipodeOfBijective_rTensor_comul :
    LinearMap.mul' R B ∘ₗ (antipodeOfBijective h).rTensor B ∘ₗ comul =
      Algebra.linearMap R B ∘ₗ counit := by
  refine LinearMap.ext fun b ↦ ?_
  have hT : TensorProduct.comm R B B (comul (R := R) b) =
      Comodule.endOfPoint B (AlgHom.id R B) ((1 : B) ⊗ₜ[R] b) := by
    rw [endOfPoint_id_tmul, one_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mul'_rTensor_antipodeOfBijective, hT,
    LinearEquiv.ofBijective_symm_apply_apply, Module.Dual.baseChange_apply_tmul,
    LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

/-- The candidate inverse `a ⊗ b ↦ a • ∑ S(b₍₂₎) ⊗ b₍₁₎` of the universal point action. -/
private noncomputable def inverseCandidate : B ⊗[R] B →ₗ[B] B ⊗[R] B :=
  LinearMap.liftBaseChange B
    ((TensorProduct.comm R B B).toLinearMap ∘ₗ (antipodeOfBijective h).lTensor B ∘ₗ comul)

private theorem inverseCandidate_tmul (a b : B) :
    inverseCandidate h (a ⊗ₜ[R] b) =
      a • TensorProduct.comm R B B ((antipodeOfBijective h).lTensor B (comul (R := R) b)) :=
  rfl

/-- The candidate inverse, precomposed with the swap of the factors, as a composite of
comultiplication, the antipode and multiplication. -/
private theorem inverseCandidate_comm (x y : B) :
    inverseCandidate h (TensorProduct.comm R B B (x ⊗ₜ[R] y)) =
      TensorProduct.comm R B B
        (((LinearMap.mul' R B ∘ₗ (antipodeOfBijective h).rTensor B).lTensor B)
          (TensorProduct.assoc R B B B (comul (R := R) x ⊗ₜ[R] y))) := by
  rw [TensorProduct.comm_tmul, inverseCandidate_tmul]
  induction comul (R := R) x using TensorProduct.inductionOn with
  | add z w hz hw => rw [map_add, map_add, smul_add, hz, hw, TensorProduct.add_tmul, map_add,
      map_add, map_add]
  | tmul p q =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_tmul,
        LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

/-- The candidate inverse is a left inverse of the universal point action. -/
private theorem inverseCandidate_endOfPoint_id (x : B ⊗[R] B) :
    inverseCandidate h (Comodule.endOfPoint B (AlgHom.id R B) x) = x := by
  have hb (b : B) : inverseCandidate h (TensorProduct.comm R B B (comul (R := R) b)) =
      (1 : B) ⊗ₜ[R] b := by
    have hlin : (inverseCandidate h).restrictScalars R ∘ₗ
        (TensorProduct.comm R B B).toLinearMap =
          (TensorProduct.comm R B B).toLinearMap ∘ₗ
            ((LinearMap.mul' R B ∘ₗ (antipodeOfBijective h).rTensor B).lTensor B) ∘ₗ
              (TensorProduct.assoc R B B B).toLinearMap ∘ₗ comul.rTensor B :=
      TensorProduct.ext' fun x y ↦ by
        simpa using inverseCandidate_comm h x y
    have hb := LinearMap.congr_fun hlin (comul (R := R) b)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      coassoc_apply] at hb
    rw [hb, ← LinearMap.comp_apply (LinearMap.lTensor B _), ← LinearMap.lTensor_comp,
      LinearMap.comp_assoc, mul_antipodeOfBijective_rTensor_comul, LinearMap.lTensor_comp,
      LinearMap.comp_apply, lTensor_counit_comul, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
      map_one, TensorProduct.comm_tmul]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
      rw [endOfPoint_id_tmul, LinearMap.map_smul, hb, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]

/-- The inverse of the universal point action is `a ⊗ b ↦ a • ∑ S(b₍₂₎) ⊗ b₍₁₎`. -/
private theorem ofBijective_symm_one_tmul (b : B) :
    (LinearEquiv.ofBijective _ h).symm ((1 : B) ⊗ₜ[R] b) =
      TensorProduct.comm R B B ((antipodeOfBijective h).lTensor B (comul (R := R) b)) := by
  rw [← one_smul B (TensorProduct.comm R B B _), ← inverseCandidate_tmul,
    ← inverseCandidate_endOfPoint_id h ((LinearEquiv.ofBijective _ h).symm _),
    LinearEquiv.apply_ofBijective_symm_apply]

/-- The second antipode identity: `∑ b₍₁₎ S(b₍₂₎) = ε(b)`. -/
theorem mul_antipodeOfBijective_lTensor_comul :
    LinearMap.mul' R B ∘ₗ (antipodeOfBijective h).lTensor B ∘ₗ comul =
      Algebra.linearMap R B ∘ₗ counit := by
  refine LinearMap.ext fun b ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.mul'_comm,
    ← ofBijective_symm_one_tmul, ← baseChange_counit_endOfPoint_id,
    LinearEquiv.apply_ofBijective_symm_apply, Module.Dual.baseChange_apply_tmul,
    LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

/-- A commutative bialgebra on which the universal point acts bijectively is a Hopf algebra, with
antipode `TauCeti.HopfAlgebra.antipodeOfBijective`. This is not an instance because it depends
on the bijectivity proof. -/
-- Exposed so that, once installed with `letI`, its bialgebra structure is recognised as the given
-- one by instance synthesis.
@[expose, instance_reducible]
noncomputable def ofBijective : HopfAlgebra R B where
  antipode := antipodeOfBijective h
  mul_antipode_rTensor_comul := mul_antipodeOfBijective_rTensor_comul h
  mul_antipode_lTensor_comul := mul_antipodeOfBijective_lTensor_comul h

/-- The antipode of `TauCeti.HopfAlgebra.ofBijective` is
`TauCeti.HopfAlgebra.antipodeOfBijective`. -/
@[simp]
theorem antipode_ofBijective :
    letI := ofBijective h
    HopfAlgebra.antipode R (A := B) = antipodeOfBijective h :=
  rfl

end TauCeti.HopfAlgebra
