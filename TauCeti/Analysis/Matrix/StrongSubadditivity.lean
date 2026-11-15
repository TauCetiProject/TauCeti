/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import TauCeti.Analysis.Matrix.Entropy
import TauCeti.Analysis.Matrix.Exponential.Log
import TauCeti.Analysis.Matrix.Kronecker
import TauCeti.Analysis.Matrix.OperatorJensen
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.LinearAlgebra.Matrix.Vec
import TauCeti.Topology.Instances.Matrix

/-!
# Monotonicity of the relative entropy and strong subadditivity

This file proves that the Umegaki relative entropy of positive definite matrices does not increase
under the partial trace, and deduces the strong subadditivity of the von Neumann entropy.

We follow Petz's proof through the relative modular operator. Matrices `X : Matrix m m 𝕜` form a
Hilbert space under the Hilbert–Schmidt inner product `⟪X, Y⟫ = Tr (Xᴴ * Y)`; in column-stacked
coordinates `Matrix.vec X` it is the standard inner product, `Matrix.star_vec_dotProduct_vec`.

* The *relative modular operator* of `ρ` and `σ` is `Δ(ρ, σ) : X ↦ σ * X * ρ⁻¹`, which acts on
  column-stacked matrices as the Kronecker product `(ρ⁻¹)ᵀ ⊗ₖ σ`
  (`Matrix.relativeModularOperator`). For positive definite `ρ` and `σ` it is positive definite,
  its logarithm is `X ↦ log σ * X - X * log ρ`, and the relative entropy is the quadratic form
  `D(ρ ‖ σ) = -⟪ρ^(1/2), log Δ(ρ, σ) ρ^(1/2)⟫`.
* For a positive definite `ρ` on a bipartite system indexed by `m × n`, with reduced matrix
  `ρ_A = Tr₂ ρ`, the *partial-trace isometry* `V` sends `x * ρ_A^(1/2)` to `(x ⊗ₖ 1) * ρ^(1/2)`
  (`Matrix.partialTraceIsometry`). It is an isometry, `Vᴴ * V = 1`, it sends `ρ_A^(1/2)` to
  `ρ^(1/2)`, and it compresses relative modular operators to those of the reduced matrices:
  `Vᴴ * Δ(ρ, σ) * V = Δ(ρ_A, σ_A)`.

Jensen's operator inequality for the operator concave logarithm and the isometry `V`
(`Matrix.PosDef.conjTranspose_mul_log_mul_le_log`) gives
`Vᴴ * log Δ(ρ, σ) * V ≤ log Δ(ρ_A, σ_A)`. Evaluating both quadratic forms at `ρ_A^(1/2)` is the
monotonicity `D(ρ_A ‖ σ_A) ≤ D(ρ ‖ σ)`. The logarithm is operator concave on complex matrices,
which carry a C⋆-algebra structure, so the monotonicity and its consequences are stated over `ℂ`.

Monotonicity applied to a positive definite state `ρ` of a tripartite system and the reference
`1 ⊗ₖ ρ_BC`, tracing out the third factor, is the **strong subadditivity** of the entropy,
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. Since the entropy is continuous on the Hermitian matrices,
it extends to every positive semidefinite `ρ` by letting `t → 0⁺` in `ρ + t • 1`.

## Main definitions

* `Matrix.relativeModularOperator`: the relative modular operator `Δ(ρ, σ)` on column-stacked
  matrices.
* `Matrix.partialTraceIsometry`: the partial-trace isometry of a bipartite `ρ`.

## Main results

* `Matrix.PosDef.star_vec_dotProduct_cfc_log_relativeModularOperator_mulVec_vec`: the relative
  entropy as a quadratic form of `log Δ(ρ, σ)`.
* `Matrix.PosDef.conjTranspose_mul_partialTraceIsometry`: `Vᴴ * V = 1`.
* `Matrix.PosDef.conjTranspose_mul_relativeModularOperator_mul_partialTraceIsometry`: the modular
  compression identity `Vᴴ * Δ(ρ, σ) * V = Δ(ρ_A, σ_A)`.
* `Matrix.PosDef.relativeEntropy_partialTraceRight_le`: monotonicity of the relative entropy under
  the partial trace, `D(Tr₂ ρ ‖ Tr₂ σ) ≤ D(ρ ‖ σ)`, for positive definite `ρ` and `σ`.
* `Matrix.PosSemidef.vonNeumannEntropy_strong_subadditivity`: strong subadditivity,
  `S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

## References

* D. Petz, *Quasi-entropies for finite quantum systems*, Rep. Math. Phys. **23** (1986), 57–65.
* M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Texts and Monographs in Physics, Springer
  (1993), Chapter 1 (relative entropy, its monotonicity and strong subadditivity).
* E. H. Lieb, M. B. Ruskai, *Proof of the strong subadditivity of quantum-mechanical entropy*,
  J. Math. Phys. **14** (1973), 1938–1941.
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics 529 (2010), Section 7.
-/

public section

noncomputable section

open Filter Topology
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

/-- The *relative modular operator* `Δ(ρ, σ) : X ↦ σ * X * ρ⁻¹` on the Hilbert–Schmidt space of
`m × m` matrices, as a matrix acting on column-stacked matrices `Matrix.vec X`. -/
def relativeModularOperator (ρ σ : Matrix m m 𝕜) : Matrix (m × m) (m × m) 𝕜 :=
  (ρ⁻¹)ᵀ ⊗ₖ σ

/-- The relative modular operator `Δ(ρ, σ)` is the Kronecker product `(ρ⁻¹)ᵀ ⊗ₖ σ`. -/
theorem relativeModularOperator_def (ρ σ : Matrix m m 𝕜) :
    relativeModularOperator ρ σ = (ρ⁻¹)ᵀ ⊗ₖ σ := (rfl)

/-- The relative modular operator `Δ(ρ, σ)` sends `X` to `σ * X * ρ⁻¹`. -/
@[simp]
theorem relativeModularOperator_mulVec_vec (ρ σ X : Matrix m m 𝕜) :
    relativeModularOperator ρ σ *ᵥ vec X = vec (σ * X * ρ⁻¹) := by
  rw [relativeModularOperator_def, kronecker_mulVec_vec, transpose_transpose]

/-- For positive definite `ρ` and `σ`, the logarithm of `Δ(ρ, σ)` acts by
`X ↦ log σ * X - X * log ρ`. -/
theorem PosDef.cfc_log_relativeModularOperator {ρ σ : Matrix m m 𝕜} (hρ : ρ.PosDef)
    (hσ : σ.PosDef) :
    cfc Real.log (relativeModularOperator ρ σ) =
      (1 : Matrix m m 𝕜) ⊗ₖ cfc Real.log σ - (cfc Real.log ρ)ᵀ ⊗ₖ (1 : Matrix m m 𝕜) := by
  rw [relativeModularOperator_def, hρ.inv.transpose.cfc_log_kronecker hσ, cfc_transpose,
    hρ.cfc_log_inv, transpose_neg, sub_eq_neg_add]
  congr 1
  ext
  simp

/-- **The relative entropy as a modular quadratic form.** For positive definite `ρ` and `σ`,
`⟪ρ^(1/2), log Δ(ρ, σ) ρ^(1/2)⟫ = -Tr (ρ (log ρ - log σ))`, whose real part is `-D(ρ ‖ σ)`. -/
theorem PosDef.star_vec_dotProduct_cfc_log_relativeModularOperator_mulVec_vec {ρ σ : Matrix m m 𝕜}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    star (vec (CFC.sqrt ρ)) ⬝ᵥ cfc Real.log (relativeModularOperator ρ σ) *ᵥ vec (CFC.sqrt ρ) =
      -(ρ * (cfc Real.log ρ - cfc Real.log σ)).trace := by
  have hr : (CFC.sqrt ρ).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).isHermitian
  have hrr := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  -- Vectorization: both terms are Hilbert–Schmidt inner products of matrices.
  simp only [hρ.cfc_log_relativeModularOperator hσ, sub_mulVec, dotProduct_sub,
    kronecker_mulVec_vec, star_vec_dotProduct_vec, transpose_transpose, transpose_one, hr.eq,
    Matrix.mul_one, Matrix.one_mul]
  -- Trace algebra: merge `ρ^(1/2) * ρ^(1/2) = ρ`, cycling the trace in the first term.
  rw [trace_mul_comm (CFC.sqrt ρ), Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt ρ), hrr,
    trace_mul_comm (cfc Real.log σ), mul_sub, trace_sub, neg_sub]

private theorem mulVec_vec_eq_vec_kronecker_one_mul (B : Matrix (m × n) (m × n) 𝕜)
    (Y : Matrix m m 𝕜) :
    (of fun (p : (m × n) × (m × n)) (q : m × m) ↦ if p.2.1 = q.2 then B (q.1, p.2.2) p.1 else 0) *ᵥ
      vec Y = vec ((Y ⊗ₖ (1 : Matrix n n 𝕜)) * B) := by
  ext ⟨⟨j, l⟩, ⟨i, k⟩⟩
  rw [vec_eq_uncurry, vec_eq_uncurry]
  simp only [Function.uncurry_apply_pair, mulVec, dotProduct, of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, kronecker_apply, Matrix.one_apply]
  simp [mul_comm]

/-- The *partial-trace isometry* of a positive definite `ρ` on a bipartite system indexed by
`m × n`: the matrix, on column-stacked matrices, of
`Y ↦ ((Y * ρ_A^(-1/2)) ⊗ₖ 1) * ρ^(1/2)`, where `ρ_A = Tr₂ ρ`. It sends `x * ρ_A^(1/2)` to
`(x ⊗ₖ 1) * ρ^(1/2)`. -/
def partialTraceIsometry (ρ : Matrix (m × n) (m × n) 𝕜) :
    Matrix ((m × n) × (m × n)) (m × m) 𝕜 :=
  of fun p q ↦ if p.2.1 = q.2 then
    (((CFC.sqrt ρ.partialTraceRight)⁻¹ ⊗ₖ (1 : Matrix n n 𝕜)) * CFC.sqrt ρ) (q.1, p.2.2) p.1
    else 0

/-- The partial-trace isometry of `ρ` sends `Y` to `((Y * ρ_A^(-1/2)) ⊗ₖ 1) * ρ^(1/2)`. -/
@[simp]
theorem partialTraceIsometry_mulVec_vec (ρ : Matrix (m × n) (m × n) 𝕜) (Y : Matrix m m 𝕜) :
    partialTraceIsometry ρ *ᵥ vec Y =
      vec (((Y * (CFC.sqrt ρ.partialTraceRight)⁻¹) ⊗ₖ (1 : Matrix n n 𝕜)) * CFC.sqrt ρ) := by
  rw [partialTraceIsometry, mulVec_vec_eq_vec_kronecker_one_mul, ← Matrix.mul_assoc,
    ← mul_kronecker_mul, Matrix.one_mul]

/-- The partial-trace isometry of a positive definite `ρ` sends `ρ_A^(1/2)` to `ρ^(1/2)`. -/
theorem PosDef.partialTraceIsometry_mulVec_vec_sqrt [Nonempty n]
    {ρ : Matrix (m × n) (m × n) 𝕜} (hρ : ρ.PosDef) :
    partialTraceIsometry ρ *ᵥ vec (CFC.sqrt ρ.partialTraceRight) = vec (CFC.sqrt ρ) := by
  rw [partialTraceIsometry_mulVec_vec, mul_nonsing_inv _
    (hρ.partialTraceRight.isUnit_det_sqrt), one_kronecker_one,
    Matrix.one_mul]

/-- The partial-trace isometry of a positive definite `ρ` is an isometry for the Hilbert–Schmidt
inner product: `Vᴴ * V = 1`. -/
theorem PosDef.conjTranspose_mul_partialTraceIsometry [Nonempty n]
    {ρ : Matrix (m × n) (m × n) 𝕜} (hρ : ρ.PosDef) :
    (partialTraceIsometry ρ)ᴴ * partialTraceIsometry ρ = 1 := by
  have hsH : (CFC.sqrt ρ.partialTraceRight)⁻¹ᴴ = (CFC.sqrt ρ.partialTraceRight)⁻¹ :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).isHermitian.inv.eq
  have hrH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).isHermitian.eq
  refine eq_of_star_vec_dotProduct_mulVec_vec fun X Y ↦ ?_
  rw [← Matrix.mul_one (partialTraceIsometry ρ)ᴴ, star_dotProduct_conjTranspose_mul_mul_mulVec,
    one_mulVec, one_mulVec]
  simp only [partialTraceIsometry_mulVec_vec, star_vec_dotProduct_vec, conjTranspose_mul,
    conjTranspose_kronecker, conjTranspose_one, hsH, hrH]
  set s := CFC.sqrt ρ.partialTraceRight
  have hs : IsUnit s.det := hρ.partialTraceRight.isUnit_det_sqrt
  have hss : s * s = ρ.partialTraceRight :=
    CFC.sqrt_mul_sqrt_self _ hρ.partialTraceRight.posSemidef.nonneg
  -- The trace form of `x ⊗ₖ 1` sandwiched by `ρ^(1/2)` is that of `x` against `ρ_A = Tr₂ ρ`.
  have htr (Z : Matrix m m 𝕜) : (CFC.sqrt ρ * (Z ⊗ₖ (1 : Matrix n n 𝕜)) * CFC.sqrt ρ).trace =
      (Z * ρ.partialTraceRight).trace := by
    rw [trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg, trace_mul_comm,
      ← trace_partialTraceRight, partialTraceRight_kronecker_one_mul]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (CFC.sqrt ρ), ← mul_kronecker_mul, Matrix.one_mul, htr,
    ← hss]
  -- Cancel `s⁻¹ * s` inside the product and `s * s⁻¹` after cycling the trace.
  simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hs]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, mul_nonsing_inv _ hs, Matrix.mul_one]

/-- **The modular compression identity.** Compressing the relative modular operator `Δ(ρ, σ)`
by the partial-trace isometry of `ρ` gives the relative modular operator `Δ(ρ_A, σ_A)` of the
reduced matrices `ρ_A = Tr₂ ρ` and `σ_A = Tr₂ σ`. -/
theorem PosDef.conjTranspose_mul_relativeModularOperator_mul_partialTraceIsometry [Nonempty n]
    {ρ : Matrix (m × n) (m × n) 𝕜} (hρ : ρ.PosDef) (σ : Matrix (m × n) (m × n) 𝕜) :
    (partialTraceIsometry ρ)ᴴ * relativeModularOperator ρ σ * partialTraceIsometry ρ =
      relativeModularOperator ρ.partialTraceRight σ.partialTraceRight := by
  have hsH : (CFC.sqrt ρ.partialTraceRight)⁻¹ᴴ = (CFC.sqrt ρ.partialTraceRight)⁻¹ :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).isHermitian.inv.eq
  have hrH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).isHermitian.eq
  refine eq_of_star_vec_dotProduct_mulVec_vec fun X Y ↦ ?_
  rw [star_dotProduct_conjTranspose_mul_mul_mulVec]
  simp only [relativeModularOperator_mulVec_vec, partialTraceIsometry_mulVec_vec,
    star_vec_dotProduct_vec, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hsH,
    hrH]
  set s := CFC.sqrt ρ.partialTraceRight
  set r := CFC.sqrt ρ
  have hss : s * s = ρ.partialTraceRight :=
    CFC.sqrt_mul_sqrt_self _ hρ.partialTraceRight.posSemidef.nonneg
  have hr : IsUnit r.det := hρ.isUnit_det_sqrt
  have hρinv : ρ⁻¹ = r⁻¹ * r⁻¹ := by
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
  -- Cancel `ρ^(1/2) * ρ⁻¹ = ρ^(-1/2)`, then cycle the leading `ρ^(1/2)` around the trace.
  rw [hρinv]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hr]
  rw [trace_mul_comm r]
  simp only [Matrix.mul_assoc, nonsing_inv_mul _ hr, Matrix.mul_one]
  -- Merge the two Kronecker factors and trace out the second system.
  rw [trace_mul_comm, Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul,
    ← trace_partialTraceRight, partialTraceRight_mul_kronecker_one, ← hss, Matrix.mul_inv_rev,
    trace_mul_comm Xᴴ]
  simp only [Matrix.mul_assoc]

-- Stated after the lemmas whose statements mention `Matrix.relativeModularOperator`: inside the
-- `Matrix.PosDef` namespace, that bare name would otherwise resolve to this lemma.
/-- The relative modular operator of two positive definite matrices is positive definite. -/
theorem PosDef.relativeModularOperator {ρ σ : Matrix m m 𝕜} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (Matrix.relativeModularOperator ρ σ).PosDef :=
  hρ.inv.transpose.kronecker hσ

/-- **Monotonicity of the relative entropy under the partial trace.** For positive definite
complex matrices `ρ` and `σ` on a bipartite system indexed by `m × n`, tracing out the second
factor does not increase the relative entropy: `D(Tr₂ ρ ‖ Tr₂ σ) ≤ D(ρ ‖ σ)`. -/
theorem PosDef.relativeEntropy_partialTraceRight_le {ρ σ : Matrix (m × n) (m × n) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relativeEntropy ρ.partialTraceRight σ.partialTraceRight ≤ relativeEntropy ρ σ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 (τ : Matrix (m × n) (m × n) ℂ) : τ.partialTraceRight = 0 := by
      ext
      simp
    rw [h0, h0, relativeEntropy_zero_left, Subsingleton.elim ρ σ, relativeEntropy_self]
  set V := partialTraceIsometry ρ
  have hρA := hρ.partialTraceRight
  have hσA := hσ.partialTraceRight
  -- Jensen's operator inequality for `log` and the isometry `V`, at the vector `vec ρ_A^(1/2)`.
  have hJ := (hρ.relativeModularOperator hσ).conjTranspose_mul_log_mul_le_log
    hρ.conjTranspose_mul_partialTraceIsometry
  rw [hρ.conjTranspose_mul_relativeModularOperator_mul_partialTraceIsometry, le_iff] at hJ
  have hq := hJ.dotProduct_mulVec_nonneg (vec (CFC.sqrt ρ.partialTraceRight))
  unfold CFC.log at hq
  rw [sub_mulVec, dotProduct_sub, star_dotProduct_conjTranspose_mul_mul_mulVec,
    hρ.partialTraceIsometry_mulVec_vec_sqrt,
    hρA.star_vec_dotProduct_cfc_log_relativeModularOperator_mulVec_vec hσA,
    hρ.star_vec_dotProduct_cfc_log_relativeModularOperator_mulVec_vec hσ] at hq
  rw [relativeEntropy_of_posDef hσA, relativeEntropy_of_posDef hσ, EReal.coe_le_coe_iff]
  have := (Complex.nonneg_iff.1 hq).1
  simp only [Complex.sub_re, Complex.neg_re] at this
  simp only [RCLike.re_to_complex]
  linarith

/-- Strong subadditivity for positive definite matrices, by monotonicity of the relative entropy
under the partial trace over the third factor, applied to `ρ` and `1 ⊗ₖ ρ_BC`. -/
private theorem PosDef.vonNeumannEntropy_add_le {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {ρ : Matrix ((a × b) × c) ((a × b) × c) ℂ} (hρ : ρ.PosDef) :
    ρ.vonNeumannEntropy + ρ.partialTraceRight.partialTraceLeft.vonNeumannEntropy ≤
      ρ.partialTraceRight.vonNeumannEntropy +
        vonNeumannEntropy
          (reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c) ρ).partialTraceLeft := by
  set e := Equiv.prodAssoc a b c
  -- If the first or the third factor is empty, every matrix in sight is zero.
  rcases isEmpty_or_nonempty a with ha | ha
  · rw [Subsingleton.elim ρ 0]
    simp
  rcases isEmpty_or_nonempty c with hc | hc
  · rw [Subsingleton.elim ρ 0]
    simp
  have hρ' : (reindex e e ρ).PosDef := by
    simpa only [reindex_apply] using hρ.submatrix e.symm.injective
  have hBC := hρ'.partialTraceLeft
  have hB := hρ.partialTraceRight.partialTraceLeft
  set σ := reindex e.symm e.symm ((1 : Matrix a a ℂ) ⊗ₖ (reindex e e ρ).partialTraceLeft)
  have hσ : σ.PosDef := by
    simpa only [σ, reindex_apply, Equiv.symm_symm] using
      (PosDef.one.kronecker hBC).submatrix e.injective
  have hmono := hρ.relativeEntropy_partialTraceRight_le hσ
  rw [partialTraceRight_reindex_prodAssoc_symm_kronecker,
    partialTraceRight_partialTraceLeft_reindex_prodAssoc,
    hρ.partialTraceRight.1.relativeEntropy_one_kronecker_partialTraceLeft hB,
    hρ.1.relativeEntropy_eq_neg_vonNeumannEntropy_sub (by
      rw [LinearMap.ker_eq_bot.mpr hσ.mulVec_injective]; exact bot_le)] at hmono
  -- `Tr (ρ log σ) = Tr (ρ_BC log ρ_BC)`, after regrouping the indices along `e`.
  have hlog : RCLike.re (ρ * cfc Real.log σ).trace =
      -(reindex e e ρ).partialTraceLeft.vonNeumannEntropy := by
    -- Reindexing along `e` is multiplicative: it moves onto `ρ` and cancels on `σ`.
    have hre (L : Matrix (a × b × c) (a × b × c) ℂ) :
        reindex e e (ρ * reindex e.symm e.symm L) = reindex e e ρ * L := by
      simp [reindex_apply, ← submatrix_mul_equiv _ _ _ e.symm]
    rw [cfc_reindex, cfc_one_kronecker, ← trace_reindex_self e, hre, ← trace_partialTraceLeft,
      partialTraceLeft_mul_one_kronecker, hBC.1.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log,
      neg_neg]
  rw [hlog, EReal.coe_le_coe_iff] at hmono
  linarith

/-- **Strong subadditivity of the von Neumann entropy.** For a positive semidefinite complex matrix
`ρ` on a tripartite system indexed by `(a × b) × c`, with reduced matrices `ρ_AB = Tr₃ ρ`,
`ρ_B = Tr₁ ρ_AB` and `ρ_BC = Tr₁ ρ` (after regrouping the indices to `a × (b × c)`),
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. -/
theorem PosSemidef.vonNeumannEntropy_strong_subadditivity
    {a b c : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c]
    [DecidableEq c] {ρ : Matrix ((a × b) × c) ((a × b) × c) ℂ} (hρ : ρ.PosSemidef) :
    ρ.vonNeumannEntropy + ρ.partialTraceRight.partialTraceLeft.vonNeumannEntropy ≤
      ρ.partialTraceRight.vonNeumannEntropy +
        vonNeumannEntropy
          (reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c) ρ).partialTraceLeft := by
  set e := Equiv.prodAssoc a b c
  -- Regularize `ρ` to the positive definite `ρ + t • 1`, `t > 0`, and let `t → 0⁺`.
  have hreindex (τ : Matrix ((a × b) × c) ((a × b) × c) ℂ) (hτ : τ.PosSemidef) :
      (reindex e e τ).PosSemidef := by
    simpa only [reindex_apply] using hτ.submatrix e.symm
  refine le_of_tendsto_of_tendsto
    ((hρ.tendsto_vonNeumannEntropy_add_smul_one (L := id) continuous_id fun _ h ↦ h).add
      (hρ.tendsto_vonNeumannEntropy_add_smul_one
        continuous_id.matrix_partialTraceRight.matrix_partialTraceLeft
        fun _ h ↦ h.partialTraceRight.partialTraceLeft))
    ((hρ.tendsto_vonNeumannEntropy_add_smul_one continuous_id.matrix_partialTraceRight
        fun _ h ↦ h.partialTraceRight).add
      (hρ.tendsto_vonNeumannEntropy_add_smul_one
        (continuous_id.matrix_reindex e e).matrix_partialTraceLeft
        fun τ h ↦ (hreindex τ h).partialTraceLeft))
    (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
  exact PosDef.vonNeumannEntropy_add_le (PosDef.posSemidef_add hρ (PosDef.one.smul ht))

end Matrix
