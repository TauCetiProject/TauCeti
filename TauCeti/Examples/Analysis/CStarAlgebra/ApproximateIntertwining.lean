/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Intertwining
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Concrete examples and sharpness of Elliott's approximate intertwining

Finite-dimensional C⋆-algebras (`ℂ`, `ℂ × ℂ`, and `CStarMatrix (Fin 2) (Fin 2) ℂ`) illustrate the
hypotheses, unital-forcing mechanism, and limit construction of Elliott's approximate intertwining
theorem (`TauCeti.elliott_intertwining` and `TauCeti.exists_starAlgEquiv_of_approxIntertwining`):

1. **Identity intertwining on `ℂ`**: `elliott_intertwining` applied to `id_ℂ` recovers the unique
   `ℂ`-linear `⋆`-automorphism `StarAlgEquiv.refl ℂ ℂ : ℂ ≃⋆ₐ[ℂ] ℂ`.
2. **Failure of one-sided approximate inverses on `ℂ` and `ℂ × ℂ`**:
   * For the diagonal map `diagHom : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ` (`z ↦ (z, z)`) and first projection
     `fstHom : ℂ × ℂ →⋆ₙₐ[ℂ] ℂ` (`(z, w) ↦ z`), `fstHom.comp diagHom = .id ℂ ℂ` is approximately
     unitarily equivalent to `id_ℂ`, whereas `diagHom.comp fstHom` is not injective and hence not
     approximately unitarily equivalent to `id_{ℂ × ℂ}`; indeed `ℂ` and `ℂ × ℂ` are not
     `⋆`-isomorphic (`isEmpty_starAlgEquiv_complex_prod`).
   * Replacing `diagHom` by the left corner embedding `NonUnitalStarAlgHom.inl ℂ ℂ ℂ` (`z ↦ (z, 0)`)
     still satisfies `fstHom.comp inl = .id ℂ ℂ` (forcing `fstHom 1 = 1` via
     `ApproximatelyUnitarilyEquivalent.left_map_one_eq_one_of_comp_id`) while `inl 1 = (1, 0) ≠ 1`,
     showing that one-sided approximate invertibility does not force the right factor to be unital.
3. **Unital forcing on `M₂(ℂ) = CStarMatrix (Fin 2) (Fin 2) ℂ`**: the rank-one corner embedding
   `cornerHom : ℂ →⋆ₙₐ[ℂ] M₂(ℂ)` (`z ↦ diag(z, 0)`) and the unital scalar embedding `scalarHom`
   (`z ↦ diag(z, z)`) satisfy `‖u * cornerHom 1 * star u - 1‖ = 1` for every unitary `u` and are
   therefore not approximately unitarily equivalent.
4. **Inner-automorphism intertwining with geometric errors `(1 / 2) ^ n` on `M₂(ℂ)`**: for an
   explicit sequence of rational Cayley phase unitaries `u n = diag(q (t n), 1)` with
   `t n = (1 / 4) ^ (n + 2)`, `‖u (n + 1) - u n‖ ≤ (1 / 2) ^ n`, the intertwining error on
   `Metric.closedBall 0 (n + 1)` is bounded by `(1 / 2) ^ n`, and the intertwining limit
   isomorphism is the nontrivial inner automorphism `Ad(diag(I, 1))`.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ComplexOrder CStarAlgebra

namespace TauCeti.ApproximateIntertwiningExample

/-! ### 1. Identity intertwining on `ℂ` -/

/-- Every `ℂ`-linear `⋆`-automorphism of `ℂ` is the identity. -/
theorem starAlgEquiv_complex_eq_refl (θ : ℂ ≃⋆ₐ[ℂ] ℂ) : θ = StarAlgEquiv.refl ℂ ℂ := by
  ext z
  simpa using θ.toAlgEquiv.commutes z

/-- Applying `elliott_intertwining` to `id_ℂ` yields `StarAlgEquiv.refl ℂ ℂ`. -/
theorem elliott_intertwining_id_complex :
    ∃ θ : ℂ ≃⋆ₐ[ℂ] ℂ, θ = StarAlgEquiv.refl ℂ ℂ ∧
      ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom (.id ℂ ℂ) := by
  have hid :
      ApproximatelyUnitarilyEquivalent ((NonUnitalStarAlgHom.id ℂ ℂ).comp (.id ℂ ℂ)) (.id ℂ ℂ) := by
    rw [NonUnitalStarAlgHom.comp_id]
  obtain ⟨θ, hθ⟩ := elliott_intertwining (.id ℂ ℂ) (.id ℂ ℂ) hid hid
  exact ⟨θ, starAlgEquiv_complex_eq_refl θ, hθ⟩

/-! ### 2. One-sided approximate inverses between `ℂ` and `ℂ × ℂ` -/

/-- The diagonal `⋆`-homomorphism `z ↦ (z, z)` from `ℂ` to `ℂ × ℂ`. -/
def diagHom : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ :=
  NonUnitalStarAlgHom.prod (.id ℂ ℂ) (.id ℂ ℂ)

/-- The first-coordinate projection `(z, w) ↦ z` from `ℂ × ℂ` to `ℂ`. -/
def fstHom : ℂ × ℂ →⋆ₙₐ[ℂ] ℂ :=
  NonUnitalStarAlgHom.fst ℂ ℂ ℂ

@[simp]
theorem diagHom_apply (z : ℂ) : diagHom z = (z, z) := by
  simp [diagHom]

@[simp]
theorem fstHom_apply (p : ℂ × ℂ) : fstHom p = p.1 := by
  simp [fstHom]

/-- The one-sided composite `fstHom.comp diagHom` equals `id_ℂ`, hence is approximately unitarily
equivalent to `id_ℂ`. -/
theorem approximatelyUnitarilyEquivalent_fstHom_comp_diagHom :
    ApproximatelyUnitarilyEquivalent (fstHom.comp diagHom) (.id ℂ ℂ) := by
  rw [fstHom, diagHom, NonUnitalStarAlgHom.fst_prod]

/-- The reverse composite `diagHom.comp fstHom` sends `(z, w)` to `(z, z)` and is not approximately
unitarily equivalent to `id_{ℂ × ℂ}`. -/
theorem not_approximatelyUnitarilyEquivalent_diagHom_comp_fstHom :
    ¬ ApproximatelyUnitarilyEquivalent (diagHom.comp fstHom) (.id ℂ (ℂ × ℂ)) := by
  intro h
  have hinj : Function.Injective (diagHom.comp fstHom) :=
    h.injective_iff.mpr Function.injective_id
  have heq :
      (diagHom.comp fstHom) ((1 : ℂ), (0 : ℂ)) = (diagHom.comp fstHom) ((1 : ℂ), (1 : ℂ)) := by
    simp
  exact one_ne_zero (Prod.mk.inj (hinj heq)).2.symm

/-- `ℂ` and `ℂ × ℂ` are not `⋆`-isomorphic, because `ℂ × ℂ` contains the nontrivial idempotent
`(1, 0)` whereas the domain `ℂ` has only `0` and `1` as idempotents. -/
theorem isEmpty_starAlgEquiv_complex_prod : IsEmpty (ℂ ≃⋆ₐ[ℂ] (ℂ × ℂ)) := by
  refine ⟨fun θ ↦ ?_⟩
  have he : IsIdempotentElem (θ.symm ((1 : ℂ), (0 : ℂ))) := by
    rw [IsIdempotentElem, ← map_mul]
    congr 1
    ext <;> simp
  refine (IsIdempotentElem.iff_eq_zero_or_one.mp he).elim (fun h0 ↦ ?_) (fun h1 ↦ ?_)
  · have := congrArg θ h0
    simp only [StarAlgEquiv.apply_symm_apply, map_zero] at this
    exact one_ne_zero (Prod.mk.inj this).1
  · have := congrArg θ h1
    simp only [StarAlgEquiv.apply_symm_apply, map_one] at this
    exact zero_ne_one (Prod.mk.inj this).2

/-- For the nonunital left inclusion `inl : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ` (`z ↦ (z, 0)`), the one-sided
composite `fstHom.comp inl` equals `id_ℂ` (forcing `fstHom 1 = 1`), yet `inl 1 ≠ 1`. -/
theorem fstHom_comp_inl_eq_id_and_inl_one_ne_one :
    ApproximatelyUnitarilyEquivalent
        (fstHom.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)) (.id ℂ ℂ) ∧
      fstHom 1 = 1 ∧
      (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) 1 ≠ 1 := by
  have hcomp : fstHom.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) = .id ℂ ℂ := by
    ext z
    simp [fstHom, NonUnitalStarAlgHom.inl]
  have happrox :
      ApproximatelyUnitarilyEquivalent
        (fstHom.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)) (.id ℂ ℂ) := by
    rw [hcomp]
  refine ⟨happrox, happrox.left_map_one_eq_one_of_comp_id, ?_⟩
  intro h1
  have := (Prod.mk.inj h1).2
  simp at this

/-! ### 3. Unital forcing and rank-one vs scalar embeddings into `M₂(ℂ)` -/

/-- Shorthand for the `2 × 2` complex matrix C⋆-algebra. -/
abbrev M₂ : Type := CStarMatrix (Fin 2) (Fin 2) ℂ

/-- Upper-left minimal projection `diag(1, 0)` in `M₂(ℂ)`. -/
def proj₀ : M₂ := CStarMatrix.ofMatrix !![1, 0; 0, 0]

/-- Lower-right minimal projection `diag(0, 1)` in `M₂(ℂ)`. -/
def proj₁ : M₂ := CStarMatrix.ofMatrix !![0, 0; 0, 1]

@[simp]
theorem proj₀_add_proj₁ : proj₀ + proj₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₀, proj₁]

@[simp]
theorem proj₀_mul_proj₀ : proj₀ * proj₀ = proj₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₀, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem proj₁_mul_proj₁ : proj₁ * proj₁ = proj₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₁, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem proj₀_mul_proj₁ : proj₀ * proj₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₀, proj₁, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem proj₁_mul_proj₀ : proj₁ * proj₀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₀, proj₁, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem star_proj₀ : star proj₀ = proj₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₀, CStarMatrix.star_apply]

@[simp]
theorem star_proj₁ : star proj₁ = proj₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj₁, CStarMatrix.star_apply]

/-- Rank-one corner embedding `z ↦ z • proj₀ = diag(z, 0)` from `ℂ` into `M₂(ℂ)`. -/
def cornerHom : ℂ →⋆ₙₐ[ℂ] M₂ where
  toFun z := z • proj₀
  map_smul' c z := by simp [mul_smul]
  map_zero' := zero_smul ℂ proj₀
  map_add' z w := add_smul z w proj₀
  map_mul' z w := by rw [smul_mul_smul_comm, proj₀_mul_proj₀]
  map_star' z := by rw [star_smul, star_proj₀]

/-- Unital scalar embedding `z ↦ z • 1 = diag(z, z)` from `ℂ` into `M₂(ℂ)`. -/
def scalarHom : ℂ →⋆ₙₐ[ℂ] M₂ :=
  (StarAlgHom.ofId ℂ M₂).toNonUnitalStarAlgHom

/-- `cornerHom` is isometric on `ℂ`. -/
@[simp]
theorem norm_cornerHom (z : ℂ) : ‖cornerHom z‖ = ‖z‖ := by
  refine le_antisymm (NonUnitalStarAlgHom.norm_apply_le cornerHom z) ?_
  have hentry : cornerHom z 0 0 = z := by simp [cornerHom, proj₀]
  simpa [hentry] using CStarMatrix.norm_entry_le_norm (M := cornerHom z) (i := 0) (j := 0)

/-- Every unitary conjugate of `cornerHom 1 = proj₀` sits at exact C⋆-norm distance `1` from `1`. -/
theorem norm_conj_cornerHom_one_sub_one (u : unitary M₂) :
    ‖(u : M₂) * cornerHom 1 * (star u : unitary M₂) - 1‖ = 1 := by
  have h1 : (1 : M₂) = (u : M₂) * (proj₀ + proj₁) * (star u : unitary M₂) := by
    rw [proj₀_add_proj₁, mul_one, Unitary.coe_mul_star_self]
  have hsub : (u : M₂) * cornerHom 1 * (star u : unitary M₂) - 1 =
      -((u : M₂) * proj₁ * (star u : unitary M₂)) := by
    have hc1 : cornerHom 1 = proj₀ := one_smul ℂ proj₀
    rw [hc1, h1]
    noncomm_ring
  rw [hsub, norm_neg, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hp₁ : IsStarProjection proj₁ := ⟨proj₁_mul_proj₁, star_proj₁⟩
  have hne : proj₁ ≠ 0 := by
    intro h0
    have : proj₁ 1 1 = 0 := by rw [h0]; rfl
    simp [proj₁] at this
  exact le_antisymm (IsStarProjection.norm_le proj₁ hp₁) (hp₁.isIdempotentElem.one_le_norm hne)

/-- The rank-one corner embedding `z ↦ diag(z, 0)` and the scalar embedding `z ↦ diag(z, z)` are
not approximately unitarily equivalent (`ApproximatelyUnitarilyEquivalent.map_one_eq_one_iff`). -/
theorem not_approximatelyUnitarilyEquivalent_cornerHom_scalarHom :
    ¬ ApproximatelyUnitarilyEquivalent cornerHom scalarHom := by
  intro h
  have hscalar : scalarHom 1 = 1 := map_one (StarAlgHom.ofId ℂ M₂)
  have hcorner : cornerHom 1 = 1 := h.map_one_eq_one_iff.mpr hscalar
  have : cornerHom 1 1 1 = (1 : M₂) 1 1 := congrArg (fun M : M₂ ↦ M 1 1) hcorner
  simp [cornerHom, proj₀] at this

/-! ### 4. Converging inner-automorphism intertwining on `M₂(ℂ)` with errors `(1 / 2) ^ n` -/

/-- Diagonal embedding of a scalar unitary `u : unitary ℂ` as `diag(u, 1)` in `unitary M₂(ℂ)`. -/
def phaseUnitary (u : unitary ℂ) : unitary M₂ :=
  ⟨(u : ℂ) • proj₀ + proj₁, by
    rw [Unitary.mem_iff]
    simp only [star_add, star_smul, star_proj₀, star_proj₁]
    constructor
    · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, proj₀_mul_proj₀,
        proj₀_mul_proj₁, proj₁_mul_proj₀, proj₁_mul_proj₁, smul_zero, add_zero, zero_add]
      rw [mul_comm (u : ℂ), Unitary.coe_star_mul_self, one_smul, proj₀_add_proj₁]
    · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, proj₀_mul_proj₀,
        proj₀_mul_proj₁, proj₁_mul_proj₀, proj₁_mul_proj₁, smul_zero, add_zero, zero_add,
        Unitary.coe_star_mul_self, one_smul, proj₀_add_proj₁]⟩

/-- The C⋆-norm distance between `phaseUnitary u` and `phaseUnitary v` equals `‖u - v‖`. -/
@[simp]
theorem norm_phaseUnitary_sub (u v : unitary ℂ) :
    ‖(phaseUnitary u : M₂) - (phaseUnitary v : M₂)‖ = ‖(u : ℂ) - (v : ℂ)‖ := by
  have hsub : (phaseUnitary u : M₂) - (phaseUnitary v : M₂) = cornerHom ((u : ℂ) - (v : ℂ)) := by
    simp only [phaseUnitary, cornerHom, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk]
    rw [sub_smul]
    abel
  rw [hsub, norm_cornerHom]

/-- Rational Cayley unitary `I * (1 + t I) / (1 - t I)` in `unitary ℂ`, converging to `I` as
`t → 0`. -/
def cayleyPhase (t : ℝ) : unitary ℂ :=
  ⟨Complex.I * ((1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I)), by
    let w : ℂ := 1 - (t : ℂ) * Complex.I
    have hw : w ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp [w] at this
    have hw_star : star w = 1 + (t : ℂ) * Complex.I := by simp [w]
    have hprod : w * star w ≠ 0 := mul_ne_zero hw (star_ne_zero.mpr hw)
    rw [Unitary.mem_iff_self_mul_star, ← hw_star, star_mul', star_div₀, star_star,
      Complex.star_def, Complex.conj_I]
    calc (Complex.I * (star w / w)) * (-Complex.I * (w / star w))
      _ = -(Complex.I * Complex.I) * ((star w / w) * (w / star w)) := by ring
      _ = 1 := by
            rw [div_mul_div_comm, mul_comm (star w) w, div_self hprod, mul_one,
              Complex.I_mul_I, neg_neg]⟩

@[simp]
theorem cayleyPhase_zero : (cayleyPhase 0 : ℂ) = Complex.I := by
  simp [cayleyPhase]

/-- `cayleyPhase` is `2`-Lipschitz in `t : ℝ`. -/
theorem norm_cayleyPhase_sub_le (s t : ℝ) :
    ‖(cayleyPhase s : ℂ) - (cayleyPhase t : ℂ)‖ ≤ 2 * |s - t| := by
  have hs_ge : 1 ≤ ‖(1 : ℂ) - (s : ℂ) * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ) - (s : ℂ) * Complex.I)
  have ht_ge : 1 ≤ ‖(1 : ℂ) - (t : ℂ) * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ) - (t : ℂ) * Complex.I)
  have hs_ne : (1 : ℂ) - (s : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have ht_ne : (1 : ℂ) - (t : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have key (x : ℝ) (hx : (1 : ℂ) - (x : ℂ) * Complex.I ≠ 0) :
      (cayleyPhase x : ℂ) * ((1 : ℂ) - (x : ℂ) * Complex.I) = Complex.I - x := by
    simp only [cayleyPhase]
    rw [mul_assoc, div_mul_cancel₀ _ hx]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hdiff : (cayleyPhase s : ℂ) - (cayleyPhase t : ℂ) =
      (-2 * ((s - t : ℝ) : ℂ)) /
        (((1 : ℂ) - (s : ℂ) * Complex.I) * ((1 : ℂ) - (t : ℂ) * Complex.I)) := by
    rw [eq_div_iff (mul_ne_zero hs_ne ht_ne)]
    calc ((cayleyPhase s : ℂ) - (cayleyPhase t : ℂ)) *
          (((1 : ℂ) - (s : ℂ) * Complex.I) * ((1 : ℂ) - (t : ℂ) * Complex.I))
      _ = ((cayleyPhase s : ℂ) * ((1 : ℂ) - (s : ℂ) * Complex.I)) *
            ((1 : ℂ) - (t : ℂ) * Complex.I) -
          ((cayleyPhase t : ℂ) * ((1 : ℂ) - (t : ℂ) * Complex.I)) *
            ((1 : ℂ) - (s : ℂ) * Complex.I) := by ring
      _ = (Complex.I - s) * ((1 : ℂ) - (t : ℂ) * Complex.I) -
          (Complex.I - t) * ((1 : ℂ) - (s : ℂ) * Complex.I) := by rw [key s hs_ne, key t ht_ne]
      _ = -2 * ((s - t : ℝ) : ℂ) := by
            push_cast
            ring_nf
            simp [Complex.I_sq]
            ring
  rw [hdiff, norm_div, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, norm_mul]
  exact div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hs_ge ht_ge)

/-- Explicit sequence of unitaries `u n = diag(cayleyPhase ((1 / 4) ^ (n + 2)), 1)` in `M₂(ℂ)`. -/
def cayleyMatrixUnitarySeq (n : ℕ) : unitary M₂ :=
  phaseUnitary (cayleyPhase ((1 / 4 : ℝ) ^ (n + 2)))

/-- Limit unitary `diag(I, 1)` of `cayleyMatrixUnitarySeq`. -/
def limitMatrixUnitary : unitary M₂ :=
  phaseUnitary (cayleyPhase 0)

/-- The successive unitary increments satisfy both `‖u (n + 1) - u n‖ ≤ (1 / 2) ^ n` and the
closed-ball intertwining bound `2 * (n + 1) * ‖u (n + 1) - u n‖ ≤ (1 / 2) ^ n`. -/
theorem norm_cayleyMatrixUnitarySeq_sub_le (n : ℕ) :
    2 * ((n : ℝ) + 1) * ‖(cayleyMatrixUnitarySeq (n + 1) : M₂) - (cayleyMatrixUnitarySeq n : M₂)‖ ≤
      (1 / 2 : ℝ) ^ n := by
  have hn_pow : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ k ih =>
      have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      push_cast
      linarith [show (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k by ring]
  have hstep :
      ‖(cayleyMatrixUnitarySeq (n + 1) : M₂) - (cayleyMatrixUnitarySeq n : M₂)‖ ≤
        (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ n := by
    simp only [cayleyMatrixUnitarySeq, norm_phaseUnitary_sub]
    have hlip := norm_cayleyPhase_sub_le ((1 / 4 : ℝ) ^ (n + 3)) ((1 / 4 : ℝ) ^ (n + 2))
    have habs : |(1 / 4 : ℝ) ^ (n + 3) - (1 / 4 : ℝ) ^ (n + 2)| =
        (3 / 64 : ℝ) * (1 / 4 : ℝ) ^ n := by
      have hneg : (1 / 4 : ℝ) ^ (n + 3) - (1 / 4 : ℝ) ^ (n + 2) =
          -((3 / 64 : ℝ) * (1 / 4 : ℝ) ^ n) := by ring
      rw [hneg, abs_neg, abs_of_nonneg (by positivity)]
    linarith [hlip, habs, (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n)]
  calc 2 * ((n : ℝ) + 1) *
        ‖(cayleyMatrixUnitarySeq (n + 1) : M₂) - (cayleyMatrixUnitarySeq n : M₂)‖
    _ ≤ 2 * (2 : ℝ) ^ n * ((1 / 8 : ℝ) * (1 / 4 : ℝ) ^ n) := by
          gcongr
    _ = (1 / 4 : ℝ) * ((2 : ℝ) * (1 / 4 : ℝ)) ^ n := by
          rw [mul_pow]
          ring
    _ = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by norm_num
    _ ≤ (1 / 2 : ℝ) ^ n := mul_le_of_le_one_left (by positivity) (by norm_num)

/-- `cayleyMatrixUnitarySeq` converges in `unitary M₂(ℂ)` to `limitMatrixUnitary = diag(I, 1)`. -/
theorem tendsto_cayleyMatrixUnitarySeq :
    Tendsto cayleyMatrixUnitarySeq atTop (𝓝 limitMatrixUnitary) := by
  rw [tendsto_subtype_rng]
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  simp only [cayleyMatrixUnitarySeq, limitMatrixUnitary, norm_phaseUnitary_sub]
  have hlip := norm_cayleyPhase_sub_le ((1 / 4 : ℝ) ^ (n + 2)) 0
  have hpow : (1 / 4 : ℝ) ^ (n + 2) ≤ (1 / 4 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [sub_zero, abs_of_nonneg (by positivity)] at hlip
  linarith

/-- Concrete realization of approximate intertwining on `M₂(ℂ)` with geometric error sequence
`(1 / 2) ^ n`: the inner automorphisms `Ad(cayleyMatrixUnitarySeq n)` form an approximate
intertwining whose limit isomorphism `θ : M₂(ℂ) ≃⋆ₐ[ℂ] M₂(ℂ)` equals the nontrivial inner
automorphism `Ad(diag(I, 1))` (`θ ≠ StarAlgEquiv.refl ℂ M₂`). -/
theorem cayley_approxIntertwining_example :
    ∃ θ : M₂ ≃⋆ₐ[ℂ] M₂,
      θ = Unitary.conjStarAlgAut ℂ M₂ limitMatrixUnitary ∧
      θ ≠ StarAlgEquiv.refl ℂ M₂ ∧
      (∀ a, Tendsto (fun n ↦ Unitary.conjStarAlgAut ℂ M₂ (cayleyMatrixUnitarySeq n) a)
        atTop (𝓝 (θ a))) ∧
      (∀ n : ℕ, ∀ a ∈ Metric.closedBall (0 : M₂) ((n : ℝ) + 1),
        ‖θ a - Unitary.conjStarAlgAut ℂ M₂ (cayleyMatrixUnitarySeq n) a‖ ≤
          ∑' k, ((1 / 2 : ℝ) ^ (n + k))) := by
  obtain ⟨u₀, hu₀, θ, hθ_eq, hθ_tendsto, hθ_err⟩ :=
    exists_unitary_tendsto_and_approxIntertwining cayleyMatrixUnitarySeq
      (fun n ↦ (1 / 2 : ℝ) ^ n) summable_geometric_two norm_cayleyMatrixUnitarySeq_sub_le
  have hu_eq : u₀ = limitMatrixUnitary :=
    tendsto_nhds_unique hu₀ tendsto_cayleyMatrixUnitarySeq
  rw [hu_eq] at hθ_eq
  refine ⟨θ, hθ_eq, ?_, hθ_tendsto, hθ_err⟩
  intro hrefl
  let flip : M₂ := CStarMatrix.ofMatrix !![0, 1; 1, 0]
  have happly : θ flip 0 1 = (StarAlgEquiv.refl ℂ M₂) flip 0 1 := by
    rw [hrefl]
  rw [hθ_eq] at happly
  have hlhs : Unitary.conjStarAlgAut ℂ M₂ limitMatrixUnitary flip 0 1 = Complex.I := by
    simp [Unitary.conjStarAlgAut_apply, limitMatrixUnitary, phaseUnitary, proj₀, proj₁, flip,
      CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  have hrhs : (StarAlgEquiv.refl ℂ M₂) flip 0 1 = 1 := by
    simp [flip]
  rw [hlhs, hrhs] at happly
  have := congrArg Complex.im happly
  simp at this

end TauCeti.ApproximateIntertwiningExample
