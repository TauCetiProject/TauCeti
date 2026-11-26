/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.Basic
import TauCeti.Data.Fin.VecNotation

/-!
# Skew-adjoint endomorphisms and the Hodge star in dimension four

Let `V` be an oriented real inner product space of dimension four. A skew-adjoint endomorphism,
an infinitesimal rotation, annihilates the volume form when it acts on one argument at a time
(`Orientation.sum_volumeForm_update_eq_zero`, in `TauCeti.Analysis.InnerProductSpace.Orientation`).
This file draws the consequences for the Hodge star of two-forms.

The Hodge dual of a two-form `F` with values in a vector space is given in an orthonormal basis
`(eₖ)` by `(⋆F)(u ∧ w) = ½ ∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) F(eₖ ∧ eₗ)`
(`Orientation.vectorFormHodgeStar_apply_ιMulti_two`). Two facts about this frame expression hold
for an arbitrary bilinear map `Θ` in place of `F`:

* the frame expression of `Θ` is the bilinear map with the given values on the basis, which may
  be any basis `(eₖ)` (`Orientation.apply_eq_sum_sum_volumeForm_smul`): a bilinear map `Φ` with
  `Φ(eᵢ, eⱼ) = ∑ₖ ∑ₗ vol(eᵢ, eⱼ, eₖ, eₗ) cₖₗ` satisfies `Φ(u, w) = ∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) cₖₗ` for
  all `u`, `w`;
* it commutes with the derivation action of a skew-adjoint `A`, which applies `A` to one argument
  at a time (`Orientation.sum_sum_volumeForm_smul_add_eq_sum_sum_add_smul`):
  `∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) (Θ(A eₖ, eₗ) + Θ(eₖ, A eₗ)) =
    ∑ₖ ∑ₗ (vol(A u, w, eₖ, eₗ) + vol(u, A w, eₖ, eₗ)) Θ(eₖ, eₗ)`.

The second fact is the pointwise reason why the covariant derivative of a metric-compatible
connection commutes with the Hodge star: in an orthonormal frame, such a connection differentiates
the frame by a skew-adjoint endomorphism. It is the frame form of the commutation of the Hodge star
with skew-adjoint derivations (`Orientation.hodgeStar_lieMap`).
-/

public section

noncomputable section

open Module
open scoped RealInnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [AddCommGroup W] [Module ℝ W]

namespace Orientation

section Four

variable {ι : Type*} [Fintype ι] [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4))

/-- The volume of four vectors as a linear function of the vector in slot `i`. -/
private def volumeSlot (v : Fin 4 → V) (i : Fin 4) : V →ₗ[ℝ] ℝ :=
  o.volumeForm.toMultilinearMap.toLinearMap v i

private theorem volumeSlot_apply (v : Fin 4 → V) (i : Fin 4) (p : V) :
    volumeSlot o v i p = o.volumeForm (Function.update v i p) :=
  MultilinearMap.toLinearMap_apply _ _ _ _

private theorem volumeForm_eq_volumeSlot_one (u w c d : V) :
    o.volumeForm ![u, w, c, d] = volumeSlot o ![u, 0, c, d] 1 w := by
  rw [volumeSlot_apply, Matrix.update_vec4_one]

/-- A bilinear map whose values on a basis are given by the frame expression
`Φ(eᵢ, eⱼ) = ∑ₖ ∑ₗ vol(eᵢ, eⱼ, eₖ, eₗ) cₖₗ` is given by the same expression on all vectors. -/
theorem apply_eq_sum_sum_volumeForm_smul (b : Basis ι ℝ V) (Φ : V →ₗ[ℝ] V →ₗ[ℝ] W) (c : ι → ι → W)
    (h : ∀ i j, Φ (b i) (b j) = ∑ k, ∑ l, o.volumeForm ![b i, b j, b k, b l] • c k l)
    (u w : V) : Φ u w = ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • c k l := by
  let Ψ : V →ₗ[ℝ] V →ₗ[ℝ] W := LinearMap.mk₂ ℝ
    (fun u w ↦ ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • c k l)
    (fun u u' w ↦ by
      simp only [AlternatingMap.map_vecCons_add, add_smul, Finset.sum_add_distrib])
    (fun a u w ↦ by
      simp only [AlternatingMap.map_vecCons_smul, smul_eq_mul, mul_smul, Finset.smul_sum])
    (fun u w w' ↦ by
      simp only [o.volumeForm_eq_volumeSlot_one, map_add, add_smul, Finset.sum_add_distrib])
    (fun a u w ↦ by
      simp only [o.volumeForm_eq_volumeSlot_one, map_smul, smul_eq_mul, mul_smul,
        Finset.smul_sum])
  have hΦΨ : Φ = Ψ :=
    LinearMap.ext_basis b b fun i j ↦ by simpa [Ψ] using h i j
  simpa [Ψ] using LinearMap.congr_fun₂ hΦΨ u w

private theorem volumeSlot_two_apply (u w d p : V) :
    volumeSlot o ![u, w, 0, d] 2 p = o.volumeForm ![u, w, p, d] := by
  rw [volumeSlot_apply, Matrix.update_vec4_two]

private theorem volumeSlot_three_apply (u w c p : V) :
    volumeSlot o ![u, w, c, 0] 3 p = o.volumeForm ![u, w, c, p] := by
  rw [volumeSlot_apply, Matrix.update_vec4_three]

/-- A skew-adjoint `A` acting on the four arguments of the volume form one at a time sums to zero,
written for the arguments `(u, w, c, d)`. -/
private theorem volumeForm_add_volumeForm_eq_neg {A : V →ₗ[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (u w c d : V) :
    o.volumeForm ![A u, w, c, d] + o.volumeForm ![u, A w, c, d] =
      -(o.volumeForm ![u, w, A c, d] + o.volumeForm ![u, w, c, A d]) := by
  have h := o.sum_volumeForm_update_eq_zero hA ![u, w, c, d]
  simp only [Fin.sum_univ_four, Matrix.cons_val, Matrix.update_vec4_zero, Matrix.update_vec4_one,
    Matrix.update_vec4_two, Matrix.update_vec4_three] at h
  linarith

/-- **The frame expression of the Hodge dual commutes with skew-adjoint derivations.** For a
skew-adjoint endomorphism `A`, an orthonormal basis `(eₖ)` and a bilinear map `Θ`,
`∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) (Θ(A eₖ, eₗ) + Θ(eₖ, A eₗ)) =
  ∑ₖ ∑ₗ (vol(A u, w, eₖ, eₗ) + vol(u, A w, eₖ, eₗ)) Θ(eₖ, eₗ)`. For a two-form `Θ` the left side is
twice the Hodge dual of `Θ ∘ A`, with `A` acting as a derivation on two-vectors, evaluated on
`u ∧ w`, and the right side is twice the Hodge dual of `Θ` evaluated on `A u ∧ w + u ∧ A w`. -/
theorem sum_sum_volumeForm_smul_add_eq_sum_sum_add_smul
    (b : OrthonormalBasis ι ℝ V) {A : V →ₗ[ℝ] V} (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫)
    (Θ : V →ₗ[ℝ] V →ₗ[ℝ] W) (u w : V) :
    ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • (Θ (A (b k)) (b l) + Θ (b k) (A (b l))) =
      ∑ k, ∑ l, (o.volumeForm ![A u, w, b k, b l] + o.volumeForm ![u, A w, b k, b l]) •
        Θ (b k) (b l) := by
  -- Move `A` from the arguments of `Θ` to the last two slots of the volume form.
  have h₁ : ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • Θ (A (b k)) (b l) =
      -∑ k, ∑ l, o.volumeForm ![u, w, A (b k), b l] • Θ (b k) (b l) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simpa [volumeSlot_two_apply] using
      b.sum_smul_apply_eq_neg_sum_smul hA (volumeSlot o ![u, w, 0, b l] 2) (Θ.flip (b l))
  have h₂ : ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • Θ (b k) (A (b l)) =
      -∑ k, ∑ l, o.volumeForm ![u, w, b k, A (b l)] • Θ (b k) (b l) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simpa [volumeSlot_three_apply] using
      b.sum_smul_apply_eq_neg_sum_smul hA (volumeSlot o ![u, w, b k, 0] 3) (Θ (b k))
  simp only [smul_add, Finset.sum_add_distrib, h₁, h₂,
    o.volumeForm_add_volumeForm_eq_neg hA, neg_smul, add_smul, Finset.sum_neg_distrib, neg_add]

end Four

end Orientation

end
