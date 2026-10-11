/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum
import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.TensorPower
import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent

/-!
# The character of a Weyl module as a sum of power sums

The Weyl module `𝕊_t(kⁿ) = c_t · (kⁿ)^{⊗d}` of a `μ`-tableau `t` is the image of the Young
symmetrizer `c_t` acting on the tensor power by permuting tensor factors. This file computes its
character on the diagonal torus of `GL n k` in terms of the coefficients of `c_t` and the power
sums `p_k = ∑ᵢ xᵢ^k`:

`char 𝕊_t(kⁿ) (diag x) = (f^μ / d!) · ∑_{σ ∈ S_d} c_t(σ) · p_{ρ(σ)}(x)`,

where `ρ(σ)` is the cycle type of `σ`, `p_ρ = ∏ᵢ p_{ρᵢ}`, and `f^μ` is the dimension of the
Specht module `ℚ[S_d] c_t`.

Two facts combine. First, a permutation `σ` composed with a diagonal matrix `diag x` acting on
`(kⁿ)^{⊗d}` has trace `p_{ρ(σ)}(x)`: in the monomial basis `e_f = e_{f 1} ⊗ ⋯ ⊗ e_{f d}` the
diagonal entry at `e_f` is `∏ⱼ x_{f j}` when `f` is constant on the cycles of `σ` and zero
otherwise, and summing over such `f` expands the product of power sums
(`TauCeti.psumPart_partition_eq_sum_prod_X`). Second, `c_t` is essentially idempotent,
`c_t² = (d! / f^μ) c_t` (`TauCeti.YoungTableau.youngSymmetrizerOver_sq`), and it commutes with the
action of `GL n k`, so the trace of `g` on the image of `c_t` is `f^μ / d!` times the trace of
`c_t g` on the whole tensor power (`TauCeti.LinearMap.trace_mul_eq_mul_trace_restrict_range`).

Every ingredient of the right-hand side lives in the symmetric group: the coefficients of `c_t`,
the dimension `f^μ`, and the cycle types. So the classical statement that this character is the
Schur polynomial `s_μ` becomes an identity about the symmetric group alone, between the Young
symmetrizer and the power-sum expansion of `s_μ`. That identity is Frobenius's, and the
conclusion is drawn in `TauCeti/RepresentationTheory/ClassicalGroups/WeylModule/Character.lean`
(`TauCeti.char_weylRepOfShape_diagramOf_diagonal`).

## Main results

* `TauCeti.trace_permTensorAction_mul_tensorPowerRep_diagGL`: **the trace of a permutation of the
  tensor factors composed with a diagonal matrix is the power-sum product over the cycle type of
  the permutation.**
* `TauCeti.YoungTableau.char_weylRep_eq_sum`: the character of a Weyl module at any element of
  `GL n k`, as a combination of traces on the tensor power weighted by the coefficients of the
  Young symmetrizer.
* `TauCeti.YoungTableau.char_weylRep_diagonal`: **the character of a Weyl module on the diagonal
  torus is the power-sum expansion displayed above.**
* `TauCeti.char_weylRepOfShape_diagonal`: the same for the Weyl module of a shape, with the Young
  symmetrizer of any tableau of that shape.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, §6.1.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
-/

public section

open Module MvPolynomial
open scoped TensorProduct

universe u

namespace TauCeti

/-! ### Permutations composed with diagonal matrices on the tensor power -/

section Trace

variable {k : Type u} [CommRing k] {n d : ℕ}

/-- **The trace of a permutation of the tensor factors composed with a diagonal matrix** is the
product of power sums over the cycle type of the permutation, evaluated at the diagonal entries:
`tr(σ ∘ (diag x)^{⊗d}) = p_{ρ(σ)}(x)`. At `σ = 1` this is the character of the tensor power on
the torus, `(x₁ + ⋯ + xₙ)^d`. -/
theorem trace_permTensorAction_mul_tensorPowerRep_diagGL (σ : Equiv.Perm (Fin d))
    (x : Fin n → kˣ) :
    LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d (diagGL x)) =
      eval (fun i => (x i : k)) (psumPart (Fin n) k σ.partition) := by
  classical
  -- the diagonal entry of `σ ∘ diag x` at `e_f` is `∏ⱼ x_{f j}` exactly when `f ∘ σ⁻¹ = f`
  have hdiag : ∀ f : Fin d → Fin n,
      (tensorPowerBasis k n d).repr
          ((permTensorAction k n d σ * tensorPowerRep k n d (diagGL x))
            (tensorPowerBasis k n d f)) f =
        if f ∘ σ = f then ∏ j, (x (f j) : k) else 0 := fun f => by
    have hσ : (fun j => f (σ.symm j)) = f ↔ f ∘ σ = f := by
      rw [funext_iff, funext_iff, ← σ.forall_congr_right]
      simp [eq_comm]
    rw [Module.End.mul_apply, tensorPowerRep_diagGL_apply_basis, map_smul,
      permTensorAction_tensorPowerBasis]
    simp [-tensorPowerBasis_apply, Finsupp.single_apply, ← hσ]
  rw [LinearMap.trace_eq_matrix_trace k (tensorPowerBasis k n d), Matrix.trace,
    psumPart_partition_eq_sum_prod_X, map_sum, Finset.sum_filter]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hdiag, eval_prod, eval_X]

end Trace

/-! ### The character of a Weyl module -/

namespace YoungTableau

variable {k : Type u} [Field k] [Algebra ℚ k] {n : ℕ} {μ : YoungDiagram}

/-- **The character of a Weyl module** at `g` is `f^μ / d!` times the sum, over the permutations
`σ` of the tensor factors, of the coefficient of `σ` in the Young symmetrizer `c_t` times the trace
of `σ ∘ g^{⊗d}` on the tensor power. Here `f^μ` is the dimension of the Specht module
`ℚ[S_d] c_t`. -/
theorem char_weylRep_eq_sum (t : YoungTableau μ) (g : GL (Fin n) k) :
    Representation.character (V := (weylModule k n t).toSubmodule) (weylRep k n t) g =
      ((finrank ℚ (spechtIdeal t) : k) / μ.card.factorial) *
        ∑ σ, (youngSymmetrizerOver k t).coeff σ *
          LinearMap.trace k _ (permTensorAction k n μ.card σ * tensorPowerRep k n μ.card g) := by
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  -- `c_t` squares to `(d! / f^μ) • c_t` and commutes with `g^{⊗d}`, so the trace of `c_t g^{⊗d}`
  -- is `d! / f^μ` times the trace of `g` on the range of `c_t`, which is the Weyl module
  have hc : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) *
      permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) =
        ((μ.card.factorial : k) / finrank ℚ (spechtIdeal t)) •
          permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) := by
    rw [← map_mul, youngSymmetrizerOver_sq, map_smul, map_div₀, map_natCast, map_natCast]
  have htrace := LinearMap.trace_mul_eq_mul_trace_restrict_range hc
    (commute_permTensorActionAlgHom_tensorPowerRep k n μ.card _ g)
  rw [LinearMap.trace_restrict_congr (weylModule_toSubmodule k n t).symm _ _
    ((weylModule k n t).apply_mem_toSubmodule g)] at htrace
  -- the trace of `c_t g^{⊗d}` is linear in `c_t`
  rw [permTensorActionAlgHom_eq_sum, Finset.sum_mul, map_sum] at htrace
  simp only [smul_mul_assoc, map_smul, smul_eq_mul] at htrace
  have hfact : (μ.card.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr μ.card.factorial_ne_zero
  have hdim : (finrank ℚ (spechtIdeal t) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (finrank_spechtIdeal_pos t).ne'
  have hrep : weylRep k n t g = (tensorPowerRep k n μ.card g).restrict
      ((weylModule k n t).apply_mem_toSubmodule g) :=
    LinearMap.ext fun v => Subtype.ext <| by rw [weylRep_apply_coe, LinearMap.coe_restrict_apply]
  rw [Representation.character, hrep, htrace, ← mul_assoc, div_mul_div_cancel₀ hfact,
    div_self hdim, one_mul]

/-- **The character of a Weyl module on the diagonal torus is a sum of power-sum products**:

`char 𝕊_t(kⁿ) (diag x) = (f^μ / d!) · ∑_σ c_t(σ) · p_{ρ(σ)}(x)`,

where `c_t(σ)` is the coefficient of `σ` in the Young symmetrizer, `ρ(σ)` is the cycle type of
`σ`, and `f^μ` is the dimension of the Specht module `ℚ[S_d] c_t`. -/
theorem char_weylRep_diagonal (t : YoungTableau μ) (x : Fin n → kˣ) :
    Representation.character (V := (weylModule k n t).toSubmodule) (weylRep k n t) (diagGL x) =
      ((finrank ℚ (spechtIdeal t) : k) / μ.card.factorial) *
        eval (fun i => (x i : k))
          (∑ σ, (youngSymmetrizerOver k t).coeff σ • psumPart (Fin n) k σ.partition) := by
  simp only [char_weylRep_eq_sum, trace_permTensorAction_mul_tensorPowerRep_diagGL, map_sum,
    smul_eval]

end YoungTableau

variable {k : Type u} [Field k] [Algebra ℚ k] {n : ℕ} {μ : YoungDiagram}

/-- **The character of the Weyl module of a shape on the diagonal torus** is the power-sum
expansion of `TauCeti.YoungTableau.char_weylRep_diagonal`, computed with the Young symmetrizer of
any tableau `t` of that shape. -/
theorem char_weylRepOfShape_diagonal (t : YoungTableau μ) (x : Fin n → kˣ) :
    Representation.character (V := (weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL x) =
      ((finrank ℚ (YoungTableau.spechtIdeal t) : k) / μ.card.factorial) *
        eval (fun i => (x i : k)) (∑ σ, (YoungTableau.youngSymmetrizerOver k t).coeff σ •
          psumPart (Fin n) k σ.partition) := by
  rw [← Representation.char_iso (V := (YoungTableau.weylModule k n t).toSubmodule)
    (W := (weylModuleOfShape k n μ).toSubmodule) (YoungTableau.weylRepEquivOfShape k n t),
    YoungTableau.char_weylRep_diagonal]

end TauCeti
