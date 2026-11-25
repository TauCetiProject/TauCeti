/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Operator.Compact.Orthonormal

/-!
# Variational eigenspaces of a compact form pair

Let `P` be a compact form pair: a compact injective inclusion `j : V → H` of dense range and a
bounded Hermitian form `a` on `V` with `c ‖u‖² ≤ re a(u, u) + ω ‖j u‖²`. For `λ ∈ ℝ` the
**variational eigenspace** (`TauCeti.CompactFormPair.formEigenspace`) is

`{u ∈ V | ∀ v, a(u, v) = λ ⟪j u, j v⟫}`,

the weak solutions of the eigenvalue problem `A u = λ u` of the operator of `a`. This file proves
the properties of these spaces that need no successive minimization:

* every variational eigenspace is finite dimensional
  (`TauCeti.CompactFormPair.finiteDimensional_formEigenspace`): on it the shifted bound reads
  `c ‖u‖² ≤ (λ + ω) ‖j u‖²`, so `j` is bounded below there, and a compact operator bounded below
  has finite-dimensional domain (`IsCompactOperator.finiteDimensional_of_norm_le_mul_norm`);
* eigenspaces of distinct eigenvalues are orthogonal in `H`
  (`TauCeti.CompactFormPair.inner_inclusion_eq_zero_of_mem_formEigenspace`), by the Hermitian law;
* a nonzero eigenspace has `λ > -ω` (`TauCeti.CompactFormPair.neg_lt_of_formEigenspace_ne_bot`);
* only finitely many eigenvalues lie below any bound
  (`TauCeti.CompactFormPair.finite_setOf_formEigenspace_ne_bot_le`): normalized eigenvectors of
  distinct eigenvalues below `M` form a bounded family in `V` whose images are orthonormal in `H`,
  and a compact operator maps no infinite such family to an orthonormal family.

## References

* V. Ivrii, *Partial Differential Equations*, Chapter 13, §13.1, Theorem 4, items 1 and 3, and its
  proof.
* J. K. Hunter, *Notes on Partial Differential Equations*, Theorem 4.25.
-/

public section

open RCLike

namespace TauCeti

namespace CompactFormPair

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : CompactFormPair 𝕜 V H)

/-- The **variational eigenspace** `{u | ∀ v, a(u, v) = λ ⟪j u, j v⟫}` of a compact form pair at
`λ ∈ ℝ`. -/
def formEigenspace (lam : ℝ) : Submodule 𝕜 V where
  carrier := {u | ∀ v, P.form u v = (lam : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v)}
  zero_mem' v := by simp
  add_mem' {u w} hu hw v := by
    simp only [Set.mem_ofPred_eq] at hu hw ⊢
    rw [map_add, add_apply, hu v, hw v, map_add, inner_add_left, mul_add]
  smul_mem' t u hu v := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [map_smulₛₗ, smul_apply, hu v, map_smul, inner_smul_left, smul_eq_mul]
    ring

variable {P} {lam mu : ℝ} {u w : V}

/-- Membership in a variational eigenspace. -/
@[simp]
theorem mem_formEigenspace :
    u ∈ P.formEigenspace lam ↔
      ∀ v, P.form u v = (lam : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) :=
  Iff.rfl

/-- On a variational eigenspace the energy is `q(u) = λ ‖j u‖²`. -/
theorem energy_eq_of_mem_formEigenspace (hu : u ∈ P.formEigenspace lam) :
    P.energy u = lam * ‖P.inclusion u‖ ^ 2 := by
  rw [energy_def, hu u, inner_self_eq_norm_sq_to_K, ← ofReal_pow, ← ofReal_mul, ofReal_re]

/-- On a variational eigenspace the shifted coercivity bound `c ‖u‖² ≤ q(u) + ω ‖j u‖²` reads
`c ‖u‖² ≤ (λ + ω) ‖j u‖²`. -/
theorem mul_norm_sq_le_of_mem_formEigenspace {c ω : ℝ}
    (h : ∀ v, c * ‖v‖ ^ 2 ≤ P.energy v + ω * ‖P.inclusion v‖ ^ 2)
    (hu : u ∈ P.formEigenspace lam) : c * ‖u‖ ^ 2 ≤ (lam + ω) * ‖P.inclusion u‖ ^ 2 := by
  have h1 := h u
  rw [energy_eq_of_mem_formEigenspace hu] at h1
  linarith

/-- **Variational eigenvectors are `H`-orthogonal across distinct eigenvalues.** -/
theorem inner_inclusion_eq_zero_of_mem_formEigenspace (hlm : lam ≠ mu)
    (hu : u ∈ P.formEigenspace lam) (hw : w ∈ P.formEigenspace mu) :
    inner 𝕜 (P.inclusion u) (P.inclusion w) = 0 := by
  have h1 : P.form u w = (mu : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion w) := by
    rw [P.hermitian, hw u, star_mul']
    simp [RCLike.star_def, inner_conj_symm]
  have h2 : ((lam : 𝕜) - mu) * inner 𝕜 (P.inclusion u) (P.inclusion w) = 0 := by
    rw [sub_mul, ← hu w, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (by exact_mod_cast hlm))

/-- **A nonzero variational eigenspace has `λ > -ω`** for any shift `ω` in a shifted coercivity
bound with constant `c > 0`. -/
theorem neg_lt_of_formEigenspace_ne_bot {c ω : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ^ 2 ≤ P.energy v + ω * ‖P.inclusion v‖ ^ 2)
    (hne : P.formEigenspace lam ≠ ⊥) : -ω < lam := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 := mul_norm_sq_le_of_mem_formEigenspace h hu
  have hpos : 0 < c * ‖u‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hu0) 2)
  by_contra hle
  nlinarith [sq_nonneg ‖P.inclusion u‖]

/-- On the variational eigenspaces with eigenvalue at most `M`, `j` is bounded below uniformly:
`‖u‖ ≤ C ‖j u‖`. -/
theorem exists_norm_le_mul_norm_inclusion_of_mem_formEigenspace (M : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ lam ≤ M, ∀ u ∈ P.formEigenspace lam, ‖u‖ ≤ C * ‖P.inclusion u‖ := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  refine ⟨Real.sqrt (max (M + ω) 0 / c), Real.sqrt_nonneg _, fun lam hlam u hu ↦ ?_⟩
  have h1 := mul_norm_sq_le_of_mem_formEigenspace h hu
  have h2 : ‖u‖ ^ 2 ≤ (max (M + ω) 0 / c) * ‖P.inclusion u‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [le_max_left (M + ω) 0, sq_nonneg ‖P.inclusion u‖]
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ Real.sqrt ((max (M + ω) 0 / c) * ‖P.inclusion u‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = _ := by rw [Real.sqrt_mul (div_nonneg (le_max_right _ _) hc.le),
      Real.sqrt_sq (norm_nonneg _)]

/-- **Variational eigenspaces are finite dimensional.** -/
instance finiteDimensional_formEigenspace (lam : ℝ) :
    FiniteDimensional 𝕜 (P.formEigenspace lam) := by
  obtain ⟨C, -, hC⟩ := P.exists_norm_le_mul_norm_inclusion_of_mem_formEigenspace lam
  set S := P.formEigenspace lam
  exact (P.isCompactOperator.comp_clm S.subtypeL).finiteDimensional_of_norm_le_mul_norm
    (K := P.inclusion.comp S.subtypeL) fun x ↦ hC lam le_rfl x x.property

/-- A nonzero variational eigenspace contains a vector `u` with `‖j u‖ = 1`. -/
theorem exists_mem_formEigenspace_norm_inclusion_eq_one (hne : P.formEigenspace lam ≠ ⊥) :
    ∃ u ∈ P.formEigenspace lam, ‖P.inclusion u‖ = 1 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hj : P.inclusion u ≠ 0 := fun h ↦ hu0 (P.injective (h.trans (map_zero _).symm))
  exact ⟨_, Submodule.smul_mem _ _ hu,
    (mem_unitConstraint.1 (inv_norm_smul_mem_unitConstraint (W := ⊤) Submodule.mem_top hj)).2⟩

/-- **Finitely many variational eigenvalues lie below any bound.** -/
theorem finite_setOf_formEigenspace_ne_bot_le (M : ℝ) :
    {lam | P.formEigenspace lam ≠ ⊥ ∧ lam ≤ M}.Finite := by
  obtain ⟨C, -, hC⟩ := P.exists_norm_le_mul_norm_inclusion_of_mem_formEigenspace M
  set s := {lam | P.formEigenspace lam ≠ ⊥ ∧ lam ≤ M}
  choose u hu hu1 using fun l : s ↦ exists_mem_formEigenspace_norm_inclusion_eq_one l.property.1
  -- The normalized eigenvectors are bounded in `V`.
  have hbound (l : s) : ‖u l‖ ≤ C := by
    simpa [hu1 l] using hC l l.property.2 (u l) (hu l)
  -- Their images are orthonormal in `H`.
  have hon : Orthonormal 𝕜 fun l : s ↦ P.inclusion (u l) :=
    ⟨hu1, fun l l' hll' ↦ inner_inclusion_eq_zero_of_mem_formEigenspace
      (fun h ↦ hll' (Subtype.ext h)) (hu l) (hu l')⟩
  have hfin := IsCompactOperator.finite_setOf_le_norm_of_apply_eq_smul
    (T := (P.inclusion : V →ₗ[𝕜] H)) P.isCompactOperator hbound hon (μ := fun _ ↦ 1)
    (fun l ↦ by simp) one_pos
  simp only [norm_one, le_refl, Set.ofPred_true] at hfin
  exact Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hfin)

end CompactFormPair

end TauCeti
