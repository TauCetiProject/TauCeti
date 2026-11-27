/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Normalization
import Mathlib.Topology.Subpath
import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Zero
import TauCeti.LinearAlgebra.Eigenspace.Matrix
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The crossing form formula for the Conley–Zehnder index

Let `Ψ : [0, 1] → Sp(2n, ℝ)` be a path of symplectic matrices. Its *crossings* are the parameters
`t` at which `Ψ t` has the eigenvalue `1`, that is, at which the graph of `Ψ t` meets the diagonal.
At a crossing `t` where `Ψ` has derivative `Ψ' t`, the *crossing form* of Robbin and Salamon is the
quadratic form

`Γ(Ψ, t) (v) = -v ⬝ᵥ J Ψ'(t) v`, `v ∈ ker (Ψ t - 1)`,

that is, `Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`. Writing `Ψ' = J S Ψ` with `S` symmetric,
as for the linearized flow of a Hamiltonian, this is the form `v ↦ v ⬝ᵥ S v` of `S` on the fixed
vectors of `Ψ t` (`Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`). A crossing is *regular*
when its crossing form is nondegenerate.

This file proves the crossing form formula for the Conley–Zehnder index
`TauCeti.GLSymplectic.conleyZehnderIndex` of a path whose crossings are regular and at whose
crossings the matrix does not have the eigenvalue `-1`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum`):

`CZ(Ψ) = -((sign Γ(Ψ, 0) + sign Γ(Ψ, 1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(Ψ, t))`.

The crossings at the endpoints count one half, parameters that are not crossings contribute zero,
and the sign is the convention `CZ = -μ_RS` of `TauCeti.GLSymplectic.conleyZehnderIndex`. For the
path `t ↦ exp (t J S)` with `S` small, symmetric and nondegenerate, the only crossing is `t = 0`,
where the crossing form is the form of `S` on the whole space, and the formula returns the
normalization `-signature(S) / 2` of
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`.

The proof runs through the symmetric matrices `K t = (Ψ t)ᵀ J - J Ψ t`. For a path avoiding `-1`,
the index is half the drop of the signature of `K`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one`), and the change
of the signature of a path of symmetric matrices with regular crossings is given by the signatures
of its crossing forms (`Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`). The
path `K` is linear in `Ψ`, so its derivative is `(Ψ' t)ᵀ J - J Ψ' t`. Its crossings are those of
`Ψ`: a symplectic `Ψ` satisfies `Ψᵀ J - J Ψ = (Ψ + 1)ᵀ (-J (Ψ - 1))`, so `K t` and `Ψ t - 1`
have the same kernel when `Ψ t + 1` is invertible
(`Matrix.ker_mulVecLin_transpose_mul_J_sub_J_mul`). On every vector `v`,
`v ⬝ᵥ (Bᵀ J - J B) v = 2 (-v ⬝ᵥ J B v)`, so the crossing form of `K` is twice the crossing form
`Γ(Ψ, t)`, with the same signature.

Away from its crossings the path may have the eigenvalue `-1`; for instance the rotation path
`t ↦ exp (t α J)` with `π < α < 2π` has the eigenvalue `-1` at `t = π / α` and its only crossing
at `t = 0`. The formula is local. Near a crossing `Ψ + 1` stays invertible, so the crossings are
the singular parameters of `K`, which are isolated because they are regular; the crossings are
therefore finitely many. The two open sets of parameters at which
`Ψ` does not have the eigenvalue `1`, respectively `-1`, cover `[0, 1]`, and the Lebesgue number
lemma subdivides `[0, 1]` into intervals each contained in one of them. On an interval of the
first kind the index vanishes by the zero axiom
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`) and there is no
crossing; on an interval of the second kind the argument through `K` applies. The index is
additive under catenation, and so is the crossing sum, an interior subdivision point counting one
half on each side. At a crossing where `Ψ` also has the eigenvalue `-1` the graph of `Ψ` meets the
graph of `-1`, so the matrix `K` no longer describes the graph near the diagonal, and this
argument does not apply.

## Main results

* `Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`: for `Ψ' = J S Ψ`, the crossing form is the
  form of `S` on the fixed vectors of `Ψ`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum`:
  the crossing form formula for the Conley–Zehnder index of a path with regular crossings, at
  which it does not have the eigenvalue `-1`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index of a path of symplectic matrices, its crossing form
  `Γ(Ψ, t) = ω₀(v, Ψ'(t) v)` on `ker (Ψ(t) - 1)` and the formula for paths with regular
  crossings).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the crossing form of a path `Ψ' = J S Ψ` as the form of
  `S` on the fixed vectors).
-/

public section

open Set
open scoped unitInterval Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **The crossing form of a Hamiltonian path.** If `Ψ' = J S Ψ`, the crossing form of `Ψ` with
derivative `Ψ'` is the quadratic form of `S` on the fixed vectors of `Ψ`. -/
theorem crossingForm_sub_one_neg_J_mul_J_mul_mul (Ψ S : Matrix (n ⊕ n) (n ⊕ n) R) :
    crossingForm (Ψ - 1) (-(J n R * (J n R * S * Ψ))) = crossingForm (Ψ - 1) S := by
  ext x
  have hfix : Ψ *ᵥ (x : n ⊕ n → R) = x := by
    simpa [sub_mulVec, sub_eq_zero] using LinearMap.mem_ker.1 x.property
  simp [crossingForm_apply, ← Matrix.mul_assoc, J_squared, ← mulVec_mulVec, hfix]

/-- Away from the eigenvalue `-1`, the crossing form of `Ψᵀ J - J Ψ` with derivative
`Ψ'ᵀ J - J Ψ'` is isometric to twice the crossing form of `Ψ` with derivative `Ψ'`. -/
private noncomputable def crossingFormIsometryEquivSymplectic {Ψ : Matrix (n ⊕ n) (n ⊕ n) R}
    (hΨ : Ψ ∈ symplecticGroup n R) (h : IsUnit (Ψ + 1).det) (Ψ' : Matrix (n ⊕ n) (n ⊕ n) R) :
    (crossingForm (Ψᵀ * J n R - J n R * Ψ) (Ψ'ᵀ * J n R - J n R * Ψ')).IsometryEquiv
      ((2 : R) • crossingForm (Ψ - 1) (-(J n R * Ψ'))) :=
  ⟨LinearEquiv.ofEq _ _ (ker_mulVecLin_transpose_mul_J_sub_J_mul hΨ h), fun v ↦ by
    simp [dotProduct_transpose_mul_J_sub_J_mul_mulVec]⟩

end Matrix

open Matrix Filter Topology

namespace TauCeti

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signature of the crossing form of `Ψ` at `t`, for the derivative `Ψ' t`. -/
private noncomputable def crossingSig (Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (t : ℝ) : ℤ :=
  (sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
    sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))

/-- Where `Ψ t` does not have the eigenvalue `1` the crossing form lives on the zero space, so its
signature vanishes. -/
private theorem crossingSig_eq_zero {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {t : ℝ}
    (h : (Ψ t - 1).det ≠ 0) : crossingSig Ψ Ψ' t = 0 := by
  have hfin : Module.finrank ℝ (LinearMap.ker (Ψ t - 1).mulVecLin) = 0 :=
    Submodule.finrank_eq_zero.2 (LinearMap.ker_eq_bot.2 (mulVec_injective_of_det_ne_zero h))
  simp [crossingSig, QuadraticForm.sigPos_eq_zero_of_finrank_eq_zero _ hfin,
    QuadraticForm.sigNeg_eq_zero_of_finrank_eq_zero _ hfin]

/-- The entries of `Ψᵀ J - J Ψ` have the derivatives of the entries of `Ψ'ᵀ J - J Ψ'`. -/
private theorem hasDerivWithinAt_transpose_mul_J_sub_J_mul
    {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ} {s : Set ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' i j) s t) (i j : n ⊕ n) :
    HasDerivWithinAt (fun r ↦ ((Ψ r)ᵀ * J n ℝ - J n ℝ * Ψ r) i j)
      ((Ψ'ᵀ * J n ℝ - J n ℝ * Ψ') i j) s t := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact (HasDerivWithinAt.fun_sum fun k _ ↦ (h k i).mul_const _).sub
    (HasDerivWithinAt.fun_sum fun k _ ↦ (h k j).const_mul _)

/-- The signature of the crossing form of `Ψᵀ J - J Ψ` is that of the crossing form of `Ψ`. -/
private theorem sigPos_sub_sigNeg_crossingForm_transpose_mul_J_sub_J_mul
    {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ) (h : IsUnit (Ψ + 1).det)
    (Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (sigPos (crossingForm (Ψᵀ * J n ℝ - J n ℝ * Ψ) (Ψ'ᵀ * J n ℝ - J n ℝ * Ψ')) : ℤ) -
        sigNeg (crossingForm (Ψᵀ * J n ℝ - J n ℝ * Ψ) (Ψ'ᵀ * J n ℝ - J n ℝ * Ψ')) =
      (sigPos (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) : ℤ) -
        sigNeg (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) := by
  have e : QuadraticMap.Equivalent _ _ := ⟨crossingFormIsometryEquivSymplectic hΨ h Ψ'⟩
  rw [e.sigPos_eq, e.sigNeg_eq, QuadraticForm.sigPos_smul_of_pos _ two_pos,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- Away from the eigenvalue `-1`, a regular crossing of `Ψ` is a regular crossing of
`Ψᵀ J - J Ψ`. -/
private theorem nondegenerate_crossingForm_transpose_mul_J_sub_J_mul
    {Ψ Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ) (h : IsUnit (Ψ + 1).det)
    (hreg : (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))).Nondegenerate) :
    (crossingForm (Ψᵀ * J n ℝ - J n ℝ * Ψ) (Ψ'ᵀ * J n ℝ - J n ℝ * Ψ')).Nondegenerate :=
  (crossingFormIsometryEquivSymplectic hΨ h Ψ').nondegenerate_iff.2
    ((QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 two_ne_zero) _).2 hreg)

/-- Along a path `Ψ` of symplectic matrices avoiding the eigenvalue `-1` on `[a, b]`, with regular
crossings, the signature of `Ψᵀ J - J Ψ` changes by the signatures of the crossing forms of `Ψ`,
counted twice at the interior crossings and once at the endpoints. -/
private theorem signature_transpose_mul_J_sub_J_mul_sub_signature {a b : ℝ} (hab : a < b)
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨc : ContinuousOn Ψ (Icc a b))
    (hmem : ∀ t ∈ Icc a b, Ψ t ∈ symplecticGroup n ℝ)
    (h₁ : ∀ t ∈ Icc a b, IsUnit (Ψ t + 1).det)
    (hd : ∀ t ∈ Icc a b, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc a b) t)
    (hreg : ∀ t ∈ Icc a b, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    signature ((Ψ b)ᵀ * J n ℝ - J n ℝ * Ψ b) - signature ((Ψ a)ᵀ * J n ℝ - J n ℝ * Ψ a) =
      crossingSig Ψ Ψ' a + 2 * ∑ᶠ t ∈ Ioo a b, crossingSig Ψ Ψ' t + crossingSig Ψ Ψ' b := by
  -- The symmetric matrices `K t = Ψᵀ J - J Ψ` and their derivatives.
  obtain ⟨K, hK⟩ : ∃ K : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, ∀ t, K t = (Ψ t)ᵀ * J n ℝ - J n ℝ * Ψ t :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ,
      ∀ t, K' t = (Ψ' t)ᵀ * J n ℝ - J n ℝ * Ψ' t :=
    ⟨_, fun _ ↦ rfl⟩
  have hKc : ContinuousOn K (Icc a b) := by
    have h : ContinuousOn (fun t ↦ (Ψ t)ᵀ * J n ℝ - J n ℝ * Ψ t) (Icc a b) :=
      ((continuous_id.matrix_transpose.matrix_mul continuous_const).continuousOn.comp hΨc
        (mapsTo_univ _ _)).sub ((continuous_const.matrix_mul continuous_id).continuousOn.comp hΨc
        (mapsTo_univ _ _))
    exact h.congr fun t _ ↦ hK t
  have hKsymm (t : ℝ) (_ : t ∈ Icc a b) : (K t).IsSymm := by
    rw [hK]
    exact transpose_transpose_mul_J_sub_J_mul (Ψ t)
  -- The crossings of `K` are those of `Ψ`.
  have hdet (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) : (Ψ t - 1).det = 0 := by
    rwa [hK, det_transpose_mul_J_sub_J_mul_eq_zero_iff (hmem t ht) (h₁ t ht)] at hKt
  have hKd (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) (i j : n ⊕ n) :
      HasDerivWithinAt (fun r ↦ K r i j) (K' t i j) (Icc a b) t := by
    simpa only [hK, hK'] using
      hasDerivWithinAt_transpose_mul_J_sub_J_mul (hd t ht (hdet t ht hKt)) i j
  -- The crossing forms of `K` are twice those of `Ψ`.
  have hcross (t : ℝ) (ht : t ∈ Icc a b) :
      (sigPos (crossingForm (K t) (K' t)) : ℤ) - sigNeg (crossingForm (K t) (K' t)) =
        crossingSig Ψ Ψ' t := by
    rw [hK, hK']
    exact sigPos_sub_sigNeg_crossingForm_transpose_mul_J_sub_J_mul (hmem t ht) (h₁ t ht) (Ψ' t)
  have hKreg (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) :
      (crossingForm (K t) (K' t)).Nondegenerate := by
    rw [hK, hK']
    exact nondegenerate_crossingForm_transpose_mul_J_sub_J_mul (hmem t ht) (h₁ t ht)
      (hreg t ht (hdet t ht hKt))
  rw [← hK, ← hK, signature_sub_signature_eq_crossingForm_add_two_mul_finsum hab hKc
    hKsymm hKd hKreg, hcross a (left_mem_Icc.2 hab.le), hcross b (right_mem_Icc.2 hab.le),
    finsum_mem_congr rfl fun t ht ↦ hcross t (Ioo_subset_Icc_self ht)]

/-- **Regular crossings away from `-1` are isolated.** If at a regular crossing `t ∈ [0, 1]` the
symplectic matrix `Ψ t` does not have the eigenvalue `-1`, then `Ψ s` does not have the eigenvalue
`1` at the parameters `s ≠ t` of `[0, 1]` close to `t`: near `t` the crossings of `Ψ` are those of
the symmetric matrices `Ψᵀ J - J Ψ`, and regular crossings of a path of symmetric matrices are
isolated. -/
private theorem eventually_nhdsWithin_Icc_diff_det_sub_one_ne_zero
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨc : ContinuousOn Ψ (Icc 0 1))
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hunit : IsUnit (Ψ t + 1).det)
    (hd : ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    ∀ᶠ s in 𝓝[Icc 0 1 \ {t}] t, (Ψ s - 1).det ≠ 0 := by
  -- The crossings of the path of symmetric matrices `Ψᵀ J - J Ψ` are isolated.
  obtain ⟨V, hV⟩ : ∃ V : ℝ → (n ⊕ n → ℝ) →L[ℝ] (n ⊕ n → ℝ) →L[ℝ] ℝ,
      V = fun s ↦ ((Ψ s)ᵀ * J n ℝ - J n ℝ * Ψ s).toContinuousLinearMap₂' :=
    ⟨_, rfl⟩
  have hsymm (s : ℝ) : (V s).toBilinForm.IsSymm := by
    rw [hV]
    exact isSymm_toBilinForm_toContinuousLinearMap₂' (transpose_transpose_mul_J_sub_J_mul (Ψ s))
  have hVd : HasDerivWithinAt V ((Ψ' t)ᵀ * J n ℝ - J n ℝ * Ψ' t).toContinuousLinearMap₂'
      (Icc 0 1) t := by
    rw [hV]
    exact hasDerivWithinAt_toContinuousLinearMap₂' (hasDerivWithinAt_transpose_mul_J_sub_J_mul hd)
  have hΓ : (ContinuousLinearMap.crossingForm (V t)
      ((Ψ' t)ᵀ * J n ℝ - J n ℝ * Ψ' t).toContinuousLinearMap₂').Nondegenerate := by
    rw [hV]
    exact (crossingFormIsometryEquiv (transpose_transpose_mul_J_sub_J_mul (Ψ t))
      _).nondegenerate_iff.2 (nondegenerate_crossingForm_transpose_mul_J_sub_J_mul (hmem t ht)
        hunit hreg)
  have hK :=
    ContinuousLinearMap.eventually_nhdsWithin_Icc_diff_nondegenerate_of_crossingForm_nondegenerate
      ht (fun s _ ↦ hsymm s) hVd hΓ
  -- Near `t` in `[0, 1]` the matrix `Ψ + 1` stays invertible, so those are the crossings of `Ψ`.
  have hnear : ∀ᶠ s in 𝓝[Icc 0 1 \ {t}] t, (Ψ s + 1).det ≠ 0 :=
    nhdsWithin_mono _ Set.sdiff_subset ((continuous_id.matrix_det.comp_continuousOn
      (hΨc.add continuousOn_const) t ht).eventually (isOpen_ne.mem_nhds hunit.ne_zero))
  filter_upwards [hK, hnear, self_mem_nhdsWithin] with s hs hs' hsI
  rw [hV, nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero] at hs
  exact fun h ↦ hs ((det_transpose_mul_J_sub_J_mul_eq_zero_iff (hmem s hsI.1)
    (isUnit_iff_ne_zero.2 hs')).2 h)

/-- **Regular crossings away from `-1` are finite in number.** If at every crossing `t ∈ [0, 1]`
the symplectic matrix `Ψ t` does not have the eigenvalue `-1` and the crossing is regular, then
there are finitely many crossings: they form a closed subset of `[0, 1]` whose points are
isolated. -/
private theorem finite_setOf_det_sub_one_eq_zero {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨc : ContinuousOn Ψ (Icc 0 1)) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 → IsUnit (Ψ t + 1).det)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite := by
  have hclosed : IsClosed {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0} :=
    ContinuousOn.preimage_isClosed_of_isClosed
      (continuous_id.matrix_det.comp_continuousOn (hΨc.sub continuousOn_const)) isClosed_Icc
      isClosed_singleton
  refine (isCompact_Icc.of_isClosed_subset hclosed fun t ht ↦ ht.1).finite
    (isDiscrete_iff_nhdsNE.2 fun t ht ↦ ?_)
  rw [inf_principal_eq_bot]
  have h := eventually_nhdsWithin_iff.1 (eventually_nhdsWithin_Icc_diff_det_sub_one_ne_zero hΨc
    hmem ht.1 (h₁ t ht.1 ht.2) (hd t ht.1 ht.2) (hreg t ht.1 ht.2))
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with s hs hne hsC
  exact hs ⟨hsC.1, hne⟩ hsC.2

/-- The crossing sum of `Ψ` over `[a, b]`: minus the sum of the signatures of the crossing forms
at the parameters of `[a, b]`, those at `a` and `b` counting one half. It is written through
`[a, b)`, so that it is additive in the interval and vanishes for `a = b`. -/
private noncomputable def crossingSum (Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (a b : ℝ) : ℝ :=
  -(((∑ᶠ t ∈ Ico a b, crossingSig Ψ Ψ' t : ℤ) : ℝ) - (crossingSig Ψ Ψ' a : ℝ) / 2 +
    (crossingSig Ψ Ψ' b : ℝ) / 2)

section CrossingSum

variable {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}

/-- With finitely many crossings in `[0, 1]`, a subset of `[0, 1]` contains finitely many
parameters at which the crossing form has nonzero signature. -/
private theorem finite_inter_support_crossingSig
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {s : Set ℝ} (hs : s ⊆ Icc 0 1) :
    (s ∩ Function.support (crossingSig Ψ Ψ')).Finite :=
  hfin.subset fun _ ht ↦ ⟨hs ht.1, not_not.1 fun h ↦ ht.2 (crossingSig_eq_zero h)⟩

/-- The crossing sum is additive over adjacent intervals of `[0, 1]`. -/
private theorem crossingSum_add_crossingSum
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    crossingSum Ψ Ψ' a b + crossingSum Ψ Ψ' b c = crossingSum Ψ Ψ' a c := by
  have h := finsum_mem_union' (f := crossingSig Ψ Ψ') Ico_disjoint_Ico_same
    (finite_inter_support_crossingSig hfin
      (Ico_subset_Icc_self.trans (Icc_subset_Icc ha (hbc.trans hc))))
    (finite_inter_support_crossingSig hfin
      (Ico_subset_Icc_self.trans (Icc_subset_Icc (ha.trans hab) hc)))
  rw [Ico_union_Ico_eq_Ico hab hbc] at h
  simp only [crossingSum, h]
  push_cast
  ring

/-- On a nondegenerate interval of `[0, 1]` the crossing sum is minus the sum of the signatures
of the crossing forms in the open interval and half those at the endpoints. -/
private theorem crossingSum_eq
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    crossingSum Ψ Ψ' a b = -(((crossingSig Ψ Ψ' a + crossingSig Ψ Ψ' b : ℤ) : ℝ) / 2 +
      ((∑ᶠ t ∈ Ioo a b, crossingSig Ψ Ψ' t : ℤ) : ℝ)) := by
  rw [crossingSum, ← insert_left_Ioo hab, finsum_mem_insert' _
    (fun h : a ∈ Ioo a b ↦ lt_irrefl a h.1)
    (finite_inter_support_crossingSig hfin (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb)))]
  push_cast
  ring

/-- Without crossings in `[a, b]` the crossing sum vanishes. -/
private theorem crossingSum_eq_zero {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ t ∈ Icc a b, (Ψ t - 1).det ≠ 0) : crossingSum Ψ Ψ' a b = 0 := by
  rw [crossingSum, crossingSig_eq_zero (hne a (left_mem_Icc.2 hab)),
    crossingSig_eq_zero (hne b (right_mem_Icc.2 hab)),
    finsum_mem_of_eqOn_zero fun t ht ↦ crossingSig_eq_zero (hne t (Ico_subset_Icc_self ht))]
  simp

end CrossingSum

/-- If `Ψ` does not have the eigenvalues `1` and `-1` at once, then `[0, 1]` subdivides into
intervals on each of which `Ψ` avoids the eigenvalue `1` or avoids the eigenvalue `-1`: the two
open sets of such parameters cover `[0, 1]`. -/
private theorem exists_monotone_det_sub_one_ne_zero_or_det_add_one_ne_zero
    {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨI : Continuous fun t : I ↦ Ψ t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 → IsUnit (Ψ t + 1).det) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m = 1) ∧ ∀ m,
      (∀ r ∈ Icc (t m : ℝ) (t (m + 1)), (Ψ r - 1).det ≠ 0) ∨
        ∀ r ∈ Icc (t m : ℝ) (t (m + 1)), (Ψ r + 1).det ≠ 0 := by
  obtain ⟨t, ht0, htm, hN, htc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun i : Bool ↦ {t : I | (Ψ t + bif i then -1 else 1).det ≠ 0})
    (fun _ ↦ isOpen_ne_fun (hΨI.add continuous_const).matrix_det continuous_const)
    fun t _ ↦ mem_iUnion.2 <| by
      by_cases ht : (Ψ t - 1).det = 0
      · exact ⟨false, by simpa using (h₁ t t.property ht).ne_zero⟩
      · exact ⟨true, by simpa [← sub_eq_add_neg] using ht⟩
  refine ⟨t, ht0, htm, hN, fun m ↦ ?_⟩
  obtain ⟨i, hi⟩ := htc m
  have hpt {r : ℝ} (hr : r ∈ Icc (t m : ℝ) (t (m + 1))) :
      (Ψ r + bif i then -1 else 1).det ≠ 0 := by
    simpa using hi (a := ⟨r, Icc_subset_Icc (unitInterval.nonneg _) (unitInterval.le_one _) hr⟩)
      ⟨Subtype.coe_le_coe.1 hr.1, Subtype.coe_le_coe.1 hr.2⟩
  cases i
  · exact Or.inr fun r hr ↦ by simpa using hpt hr
  · exact Or.inl fun r hr ↦ by simpa [← sub_eq_add_neg] using hpt hr

section Subpath

variable {A B : GLSymplectic n ℝ} (γ : Path A B) {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}

/-- The matrices along the subpath of `γ` from `a` to `b ≥ a` are the matrices `Ψ t`,
`t ∈ [a, b]`. -/
private theorem exists_mem_Icc_coe_subpath_eq
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t) {a b : I}
    (hab : a ≤ b) (s : I) :
    ∃ t ∈ Icc (a : ℝ) b, ((γ.subpath a b s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t := by
  obtain ⟨t, ht, hts⟩ := (γ.range_subpath_of_le a b hab).le (mem_range_self s)
  exact ⟨t, ⟨Subtype.coe_le_coe.2 ht.1, Subtype.coe_le_coe.2 ht.2⟩, by rw [← hts, hγ]⟩

/-- On an interval `[a, b]` of `[0, 1]` without the eigenvalue `-1`, the Conley–Zehnder index of
the subpath of `γ` is the crossing sum. -/
private theorem conleyZehnderIndex_subpath_eq_crossingSum_of_isUnit_det_add_one
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (hΨc : ContinuousOn Ψ (Icc 0 1)) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate)
    {a b : I} (hab : a < b) (h₁ : ∀ t ∈ Icc (a : ℝ) b, IsUnit (Ψ t + 1).det) :
    conleyZehnderIndex (γ.subpath a b) = crossingSum Ψ Ψ' a b := by
  have hab' : (a : ℝ) < b := hab
  have hIcc : Icc (a : ℝ) b ⊆ Icc 0 1 :=
    Icc_subset_Icc (unitInterval.nonneg a) (unitInterval.le_one b)
  have hsig := congrArg (Int.cast : ℤ → ℝ)
    (signature_transpose_mul_J_sub_J_mul_sub_signature hab' (hΨc.mono hIcc)
      (fun t ht ↦ hmem t (hIcc ht)) h₁ (fun t ht h i j ↦ (hd t (hIcc ht) h i j).mono hIcc)
      fun t ht ↦ hreg t (hIcc ht))
  rw [conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one (γ.subpath a b) fun s ↦ ?_,
    hγ, hγ, crossingSum_eq hfin (unitInterval.nonneg a) hab' (unitInterval.le_one b)]
  · push_cast at hsig ⊢
    linarith
  · obtain ⟨t, ht, hts⟩ := exists_mem_Icc_coe_subpath_eq γ hγ hab.le s
    rw [hts]
    exact h₁ t ht

/-- On an interval `[a, b]` of `[0, 1]` without crossings, the Conley–Zehnder index of the
subpath of `γ` vanishes. -/
private theorem conleyZehnderIndex_subpath_eq_zero_of_det_sub_one_ne_zero
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t) {a b : I}
    (hab : a ≤ b) (hne : ∀ t ∈ Icc (a : ℝ) b, (Ψ t - 1).det ≠ 0) :
    conleyZehnderIndex (γ.subpath a b) = 0 :=
  conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq (γ.subpath a b) (k := 0) fun s ↦ by
    obtain ⟨t, ht, hts⟩ := exists_mem_Icc_coe_subpath_eq γ hγ hab s
    rw [hts]
    exact Matrix.finrank_eigenspace_toLin'_eq_zero (by
      rw [one_smul, isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 (hne t ht))

/-- On an interval `[a, b]` of `[0, 1]` without the eigenvalue `1` or without the eigenvalue `-1`,
the Conley–Zehnder index of the subpath of `γ` is the crossing sum. -/
private theorem conleyZehnderIndex_subpath_eq_crossingSum
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (hΨc : ContinuousOn Ψ (Icc 0 1)) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate)
    {a b : I} (hab : a ≤ b)
    (h : (∀ t ∈ Icc (a : ℝ) b, (Ψ t - 1).det ≠ 0) ∨ ∀ t ∈ Icc (a : ℝ) b, (Ψ t + 1).det ≠ 0) :
    conleyZehnderIndex (γ.subpath a b) = crossingSum Ψ Ψ' a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · rw [Path.subpath_self, conleyZehnderIndex_refl]
    simp [crossingSum]
  rcases h with hne | h₁
  · rw [conleyZehnderIndex_subpath_eq_zero_of_det_sub_one_ne_zero γ hγ hlt.le hne,
      crossingSum_eq_zero hlt.le hne]
  · exact conleyZehnderIndex_subpath_eq_crossingSum_of_isUnit_det_add_one γ hγ hΨc hmem hfin hd
      hreg hlt fun t ht ↦ isUnit_iff_ne_zero.2 (h₁ t ht)

/-- If on each interval `[t m, t (m + 1)]` of a subdivision of `[0, 1]` the Conley–Zehnder index
of the subpath of `γ` is the crossing sum, then so it is on each interval `[0, t m]`. -/
private theorem conleyZehnderIndex_subpath_zero_eq_crossingSum
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {t : ℕ → I} (ht0 : t 0 = 0)
    (htm : Monotone t)
    (hpiece : ∀ m, conleyZehnderIndex (γ.subpath (t m) (t (m + 1))) =
      crossingSum Ψ Ψ' (t m) (t (m + 1))) (m : ℕ) :
    conleyZehnderIndex (γ.subpath 0 (t m)) = crossingSum Ψ Ψ' 0 (t m) := by
  induction m with
  | zero =>
    rw [ht0, Path.subpath_self, conleyZehnderIndex_refl]
    simp [crossingSum]
  | succ m ih =>
    rw [← conleyZehnderIndex_eq_of_homotopic (Path.Homotopic.subpath_trans_subpath γ 0 (t m)
      (t (m + 1))), conleyZehnderIndex_trans, ih, hpiece m]
    exact crossingSum_add_crossingSum hfin le_rfl (unitInterval.nonneg _) (htm m.le_succ)
      (unitInterval.le_one _)

end Subpath

/-- **The crossing form formula for the Conley–Zehnder index.** Let `γ` be a path of symplectic
matrices, read on `[0, 1]` as a matrix-valued function `Ψ`. Suppose that at every crossing
`t ∈ [0, 1]`, where `Ψ t` has the eigenvalue `1`, the matrix `Ψ t` does not have the eigenvalue
`-1`, `Ψ` has entrywise derivative `Ψ' t` within `[0, 1]`, and the crossing form
`Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`, the form `v ↦ -v ⬝ᵥ J Ψ' t v` on the fixed vectors
of `Ψ t`, is nondegenerate. Then the Conley–Zehnder index of `γ` is minus the sum of the
signatures of the crossing forms, the crossings at the endpoints counting one half. Parameters
that are not crossings contribute zero, and away from the crossings `Ψ` may have the eigenvalue
`-1`. -/
theorem conleyZehnderIndex_eq_neg_crossingForm_add_finsum
    {A B : GLSymplectic n ℝ} (γ : Path A B)
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 → IsUnit (Ψ t + 1).det)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    conleyZehnderIndex γ =
      -((((sigPos (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) : ℤ) -
            sigNeg (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) +
          ((sigPos (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1))) : ℤ) -
            sigNeg (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1)))) : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          ((sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
            sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))) : ℤ) : ℝ)) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Ψ t ∈ symplecticGroup n ℝ := by
    simpa [← hγ ⟨t, ht⟩] using mem_iff_mem_symplecticGroup.1 (γ ⟨t, ht⟩).property
  have hΨI : Continuous fun t : I ↦ Ψ t :=
    (Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)).congr hγ
  have hΨc : ContinuousOn Ψ (Icc 0 1) := by
    refine (Units.continuous_val.comp (continuous_subtypeVal.comp
      γ.continuous_extend)).continuousOn.congr fun t ht ↦ ?_
    simp [← hγ ⟨t, ht⟩, Path.extend_extends' γ ⟨t, ht⟩]
  have hfin := finite_setOf_det_sub_one_eq_zero hΨc hmem h₁ hd hreg
  obtain ⟨t, ht0, htm, ⟨N, hN⟩, htc⟩ :=
    exists_monotone_det_sub_one_ne_zero_or_det_add_one_ne_zero hΨI h₁
  have h := conleyZehnderIndex_subpath_zero_eq_crossingSum γ hfin ht0 htm (fun m ↦
    conleyZehnderIndex_subpath_eq_crossingSum γ hγ hΨc hmem hfin hd hreg (htm m.le_succ) (htc m)) N
  rw [hN N le_rfl, conleyZehnderIndex_congr _ γ fun s ↦ by simp [Path.subpath_zero_one],
    Set.Icc.coe_one, crossingSum_eq hfin le_rfl zero_lt_one le_rfl] at h
  simpa only [crossingSig] using h

end GLSymplectic

end TauCeti
