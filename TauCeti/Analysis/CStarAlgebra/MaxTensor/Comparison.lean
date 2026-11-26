/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Norm
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion

/-!
# C*-norms on the tensor product of unital C*-algebras are bounded by the maximal norm

Let `A` and `B` be unital C*-algebras. A C*-norm on the algebraic tensor product `A ⊗[ℂ] B` is
presented here as the norm of a normed star algebra `D` satisfying the C*-identity together with
a star homomorphism `Φ : A ⊗[ℂ] B → D`: the C*-norm is `x ↦ ‖Φ x‖` (a norm when `Φ` is
injective, a seminorm in general). Every such seminorm is bounded by the maximal norm
`TauCeti.maxTensorNorm` (`TauCeti.norm_le_maxTensorNorm`).

The proof: `a ↦ Φ (a ⊗ 1)` and `b ↦ Φ (1 ⊗ b)` are star homomorphisms with commuting values,
since `(a ⊗ 1) (1 ⊗ b) = a ⊗ b = (1 ⊗ b) (a ⊗ 1)`, whose integrated form is `Φ`. Composing with
the completion of `D`, a C*-algebra, the bound is the universal bound
`TauCeti.norm_liftNonUnitalStarAlgHom_le_maxTensorNorm`. In particular every C*-seminorm on
`A ⊗[ℂ] B` is subcross, `‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖` (`TauCeti.norm_map_tmul_le`).

The algebra `D` lives in the universe `max u v` of `A ⊗[ℂ] B`, as does the completion of
`A ⊗[ℂ] B` in a given C*-norm.

The nonunital case, the lower bound by the minimal norm and the cross-norm property, which
complete the comparison of C*-norms, are not in this file.

## Main declarations

* `TauCeti.norm_le_maxTensorNorm`: `‖Φ x‖ ≤ ‖x‖_max` for a star homomorphism `Φ` from
  `A ⊗[ℂ] B` into a normed star algebra with the C*-identity.
* `TauCeti.norm_map_tmul_le`: `‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.5.1–II.9.5.2.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

section CStarAlgebra

variable {C : Type (max u v)} [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)

/-- The restriction `a ↦ Φ (a ⊗ 1)` of a star homomorphism on `A ⊗[ℂ] B` to `A`. -/
private def restrictLeft : A →⋆ₙₐ[ℂ] C where
  toFun a := Φ (a ⊗ₜ 1)
  map_smul' c a := by rw [← smul_tmul', map_smul]; rfl
  map_zero' := by rw [zero_tmul, map_zero]
  map_add' a a' := by rw [add_tmul, map_add]
  map_mul' a a' := by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_star' a := by rw [← map_star, star_tmul, star_one]

/-- The restriction `b ↦ Φ (1 ⊗ b)` of a star homomorphism on `A ⊗[ℂ] B` to `B`. -/
private def restrictRight : B →⋆ₙₐ[ℂ] C where
  toFun b := Φ (1 ⊗ₜ b)
  map_smul' c b := by rw [tmul_smul, map_smul]; rfl
  map_zero' := by rw [tmul_zero, map_zero]
  map_add' b b' := by rw [tmul_add, map_add]
  map_mul' b b' := by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_star' b := by rw [← map_star, star_tmul, star_one]

private theorem restrictLeft_mul_restrictRight (a : A) (b : B) :
    restrictLeft Φ a * restrictRight Φ b = Φ (a ⊗ₜ b) := by
  change Φ (a ⊗ₜ 1) * Φ (1 ⊗ₜ b) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem commute_restrictLeft_restrictRight (a : A) (b : B) :
    Commute (restrictLeft Φ a) (restrictRight Φ b) := by
  change Φ (a ⊗ₜ 1) * Φ (1 ⊗ₜ b) = Φ (1 ⊗ₜ b) * Φ (a ⊗ₜ 1)
  rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]

/-- A star homomorphism on `A ⊗[ℂ] B` is the integrated form of its restrictions to `A ⊗ 1` and
`1 ⊗ B`. -/
private theorem liftNonUnitalStarAlgHom_restrict :
    Algebra.TensorProduct.liftNonUnitalStarAlgHom (restrictLeft Φ) (restrictRight Φ)
      (commute_restrictLeft_restrictRight Φ) = Φ := by
  refine NonUnitalStarAlgHom.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul, restrictLeft_mul_restrictRight]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A star homomorphism from `A ⊗[ℂ] B` into a C*-algebra is bounded by the maximal norm. -/
private theorem norm_le_maxTensorNorm_of_cstarAlgebra (x : A ⊗[ℂ] B) :
    ‖Φ x‖ ≤ maxTensorNorm A B x := by
  have h := norm_liftNonUnitalStarAlgHom_le_maxTensorNorm (restrictLeft Φ) (restrictRight Φ)
    (commute_restrictLeft_restrictRight Φ) x
  rwa [liftNonUnitalStarAlgHom_restrict] at h

end CStarAlgebra

variable {D : Type (max u v)} [NonUnitalNormedRing D] [StarRing D] [CStarRing D]
  [NormedSpace ℂ D] [IsScalarTower ℂ D D] [SMulCommClass ℂ D D] [StarModule ℂ D]

/-- **C*-seminorms on `A ⊗[ℂ] B` are bounded by the maximal norm.** For unital C*-algebras `A`
and `B` and a star homomorphism `Φ` from `A ⊗[ℂ] B` into a normed star algebra satisfying the
C*-identity, `‖Φ x‖ ≤ ‖x‖_max`. -/
theorem norm_le_maxTensorNorm (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (x : A ⊗[ℂ] B) :
    ‖Φ x‖ ≤ maxTensorNorm A B x := by
  let : CStarRing (Completion D) :=
    Completion.cstarRing fun y ↦ (CStarRing.norm_star_mul_self (x := y)).ge
  let : NonUnitalCStarAlgebra (Completion D) := {}
  let ι : D →⋆ₙₐ[ℂ] Completion D :=
    { toFun := (↑)
      map_smul' := fun c y ↦ Completion.coe_smul c y
      map_zero' := Completion.coe_zero
      map_add' := fun y y' ↦ Completion.coe_add y y'
      map_mul' := fun y y' ↦ Completion.coe_mul' y y'
      map_star' := fun y ↦ Completion.coe_star y }
  have h := norm_le_maxTensorNorm_of_cstarAlgebra (ι.comp Φ) x
  rwa [NonUnitalStarAlgHom.comp_apply, show ‖ι (Φ x)‖ = ‖Φ x‖ from Completion.norm_coe _] at h

/-- **C*-seminorms on `A ⊗[ℂ] B` are subcross.** For unital C*-algebras `A` and `B` and a star
homomorphism `Φ` from `A ⊗[ℂ] B` into a normed star algebra satisfying the C*-identity,
`‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖`. -/
theorem norm_map_tmul_le (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (a : A) (b : B) :
    ‖Φ (a ⊗ₜ b)‖ ≤ ‖a‖ * ‖b‖ :=
  (norm_le_maxTensorNorm Φ _).trans (maxTensorNorm_tmul a b).le

end TauCeti
