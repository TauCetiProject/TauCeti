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
`TauCeti.maxTensorNorm` (`NonUnitalStarAlgHom.norm_apply_le_maxTensorNorm`).

The proof: `Φ` is the integrated form of its restrictions `a ↦ Φ (a ⊗ 1)` and `b ↦ Φ (1 ⊗ b)`
(`liftNonUnitalStarAlgHom_comp_includeLeftNonUnitalStarAlgHom_includeRightNonUnitalStarAlgHom`
in `Algebra.TensorProduct`), so a star homomorphism into a C*-algebra in the universe `max u v`
of `A ⊗[ℂ] B` is bounded by the universal bound
`TauCeti.norm_liftNonUnitalStarAlgHom_le_maxTensorNorm`. For general `D`, the completion of
`A ⊗[ℂ] B` in the seminorm `y ↦ ‖Φ y‖` is such a C*-algebra. In particular every C*-seminorm on
`A ⊗[ℂ] B` is subcross, `‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖` (`NonUnitalStarAlgHom.norm_apply_tmul_le`).

The nonunital case, the lower bound by the minimal norm and the cross-norm property, which
complete the comparison of C*-norms, are not in this file.

## Main declarations

* `NonUnitalStarAlgHom.norm_apply_le_maxTensorNorm`: `‖Φ x‖ ≤ ‖x‖_max` for a star homomorphism
  `Φ` from `A ⊗[ℂ] B` into a normed star algebra with the C*-identity.
* `NonUnitalStarAlgHom.norm_apply_tmul_le`: `‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.5.1–II.9.5.2.
-/

public section

noncomputable section

open UniformSpace TensorProduct TauCeti

universe u v

namespace NonUnitalStarAlgHom

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

open Algebra.TensorProduct in
/-- A star homomorphism from `A ⊗[ℂ] B` into a C*-algebra in the universe `max u v` is bounded by
the maximal norm. -/
private theorem norm_apply_le_maxTensorNorm_of_nonUnitalCStarAlgebra {C : Type (max u v)}
    [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (x : A ⊗[ℂ] B) :
    ‖Φ x‖ ≤ maxTensorNorm A B x := by
  have h := norm_liftNonUnitalStarAlgHom_le_maxTensorNorm _ _
    (commute_comp_includeLeftNonUnitalStarAlgHom_includeRightNonUnitalStarAlgHom Φ) x
  rwa [liftNonUnitalStarAlgHom_comp_includeLeftNonUnitalStarAlgHom_includeRightNonUnitalStarAlgHom]
    at h

variable {D : Type*} [NonUnitalNormedRing D] [StarRing D] [CStarRing D] [NormedSpace ℂ D]

/-- **C*-seminorms on `A ⊗[ℂ] B` are bounded by the maximal norm.** For unital C*-algebras `A`
and `B` and a star homomorphism `Φ` from `A ⊗[ℂ] B` into a normed star algebra satisfying the
C*-identity, `‖Φ x‖ ≤ ‖x‖_max`. -/
theorem norm_apply_le_maxTensorNorm (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (x : A ⊗[ℂ] B) :
    ‖Φ x‖ ≤ maxTensorNorm A B x := by
  -- Give `A ⊗[ℂ] B` the seminorm `y ↦ ‖Φ y‖`; its completion is a C*-algebra in `max u v`, and
  -- the embedding into the completion preserves this seminorm.
  let := NonUnitalSeminormedRing.induced (A ⊗[ℂ] B) D Φ
  let := NormedSpace.induced ℂ (A ⊗[ℂ] B) D Φ
  have : NormedStarGroup (A ⊗[ℂ] B) :=
    ⟨fun y ↦ (congrArg norm (map_star Φ y)).trans_le (norm_star (Φ y)).le⟩
  let : CStarRing (Completion (A ⊗[ℂ] B)) := Completion.cstarRing fun y ↦
    (CStarRing.norm_star_mul_self (x := Φ y)).ge.trans_eq
      (by rw [map_mul, map_star] : ‖star (Φ y) * Φ y‖ = ‖Φ (star y * y)‖)
  let : NonUnitalCStarAlgebra (Completion (A ⊗[ℂ] B)) := {}
  have h := norm_apply_le_maxTensorNorm_of_nonUnitalCStarAlgebra
    (Completion.coeNonUnitalStarAlgHom ℂ) x
  rw [Completion.coe_coeNonUnitalStarAlgHom, Completion.norm_coe] at h
  -- `‖x‖` is `‖Φ x‖` by definition of the induced seminorm.
  exact h

/-- **C*-seminorms on `A ⊗[ℂ] B` are subcross.** For unital C*-algebras `A` and `B` and a star
homomorphism `Φ` from `A ⊗[ℂ] B` into a normed star algebra satisfying the C*-identity,
`‖Φ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖`. -/
theorem norm_apply_tmul_le (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (a : A) (b : B) :
    ‖Φ (a ⊗ₜ b)‖ ≤ ‖a‖ * ‖b‖ :=
  (Φ.norm_apply_le_maxTensorNorm _).trans (maxTensorNorm_tmul a b).le

end NonUnitalStarAlgHom
