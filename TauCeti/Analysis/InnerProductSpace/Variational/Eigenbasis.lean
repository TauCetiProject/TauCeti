/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Compatibility
public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.Order.Northcott.Enumeration

/-!
# The ordered eigenbasis of a symmetric Gårding form

Let `Q` be a symmetric bounded bilinear form on a real Hilbert space `V` and `J : V → H` a
compact continuous linear map with dense range into an infinite-dimensional real Hilbert space.
Suppose `Q` satisfies **Gårding's inequality**

`C₀ ‖w‖² ≤ Q(w, w) + β ‖J w‖²` for every `w`, with `C₀ > 0`.

The variational eigenvalue problem asks for `κ` and `u ≠ 0` with `Q(u, v) = κ ⟪J u, J v⟫` for
every `v`. This file lists its solutions as a sequence: there are an orthonormal basis `(eₖ)` of
`H` indexed by `ℕ` and `uₖ ∈ V` with `J uₖ = eₖ` and `Q(uₖ, ·) = κₖ ⟪eₖ, J ·⟫`, where
`κ₀ ≤ κ₁ ≤ ⋯ → ∞`, and the `κₖ` are exactly the eigenvalues, repeated according to multiplicity
(`TauCeti.exists_hilbertBasis_nat_monotone_of_garding`).

Gårding's inequality says that the shift `Q + β ⟪J ·, J ·⟫` is coercive
(`TauCeti.isCoercive_add_smul_toSesqForm_comp_of_garding`). The eigenbasis of a coercive form
along a compact map of dense range
(`TauCeti.IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner`) is an eigenbasis of `Q`
with every eigenvalue moved by `-β`, and finitely many of its eigenvalues
lie below any bound (`TauCeti.IsCoercive.finite_setOf_le_of_orthonormal`). The basis is
infinite because `H` is infinite-dimensional, so it can be enumerated by `ℕ` in nondecreasing
order of eigenvalue (`TauCeti.exists_equiv_monotone_comp_of_finite_setOf_le`). Every eigenvalue
occurs, since an eigenfunction of any other value would be orthogonal to the whole basis.

Neither nonnegativity of `Q` nor coercivity is assumed, so the theorem covers forms, such as
the Neumann form `∫ ∇u · ∇v` on `H¹(Ω)`, that only become coercive after a shift by the inner
product of `H`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 6.11 and Theorem 9.31.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.5.1, Theorem 1.
-/

public section

noncomputable section

open Filter
open scoped InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Q : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H} {C₀ β : ℝ}

omit [CompleteSpace V] [CompleteSpace H] in
/-- **An eigenvalue of a Gårding form occurs in every eigenbasis.** If the images `J uᵢ` of
eigenfunctions of a symmetric Gårding form `Q`, with eigenvalues `κᵢ`, form an orthonormal basis
of `H`, then every variational eigenvalue `κ'` of `Q` is some `κᵢ`: its eigenfunction `w` has
`J w ≠ 0` by Gårding's inequality, and `J w` would otherwise be orthogonal to every `J uᵢ`. -/
private theorem exists_eq_of_hilbertBasis_of_garding {ι : Type*} (b : HilbertBasis ι ℝ H)
    {κ : ι → ℝ} {u : ι → V} (hJu : ∀ i, J (u i) = b i)
    (heq : ∀ i v, Q (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) (hsymm : ∀ u v, Q u v = Q v u)
    (hC₀ : 0 < C₀) (hQ : ∀ w, C₀ * ‖w‖ ^ 2 ≤ Q w w + β * ‖J w‖ ^ 2) {w : V} (hw : w ≠ 0)
    {kappa' : ℝ} (hweq : ∀ v, Q w v = kappa' * ⟪J w, J v⟫_ℝ) : ∃ i, κ i = kappa' := by
  by_contra! hne
  have hJw : J w ≠ 0 := by
    intro h0
    have h := hQ w
    rw [hweq w, h0, inner_zero_left, mul_zero, norm_zero, zero_pow two_ne_zero, mul_zero,
      add_zero] at h
    have h2 : ‖w‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (h.trans (mul_zero C₀).ge) hC₀
    exact hw (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (h2.antisymm (sq_nonneg _))))
  refine hJw (b.repr.map_eq_zero_iff.1 (lp.ext (funext fun i ↦ ?_)))
  have h := hsymm w (u i)
  rw [hweq, heq, hJu, real_inner_comm] at h
  rw [HilbertBasis.repr_apply_apply, lp.coeFn_zero, Pi.zero_apply]
  exact (mul_eq_mul_right_iff.1 h.symm).resolve_left (hne i)

/-- **The ordered eigenbasis of a symmetric Gårding form.** Let `Q` be symmetric and satisfy
Gårding's inequality `C₀ ‖w‖² ≤ Q(w, w) + β ‖J w‖²` with `C₀ > 0`, for a compact `J` of dense
range into an infinite-dimensional `H`. Then there are an orthonormal basis `(eₖ)` of `H`,
a nondecreasing sequence `κₖ → ∞` and `uₖ ∈ V` with `J uₖ = eₖ` and
`Q(uₖ, v) = κₖ ⟪J uₖ, J v⟫` for every `v`. The `κₖ` are exactly the variational eigenvalues of
`Q`, counted with multiplicity. -/
theorem exists_hilbertBasis_nat_monotone_of_garding (hJc : IsCompactOperator J)
    (hJ : DenseRange J) (hH : ¬ FiniteDimensional ℝ H) (hsymm : ∀ u v, Q u v = Q v u)
    (hC₀ : 0 < C₀) (hQ : ∀ w, C₀ * ‖w‖ ^ 2 ≤ Q w w + β * ‖J w‖ ^ 2) :
    ∃ (e : HilbertBasis ℕ ℝ H) (kappa : ℕ → ℝ) (u : ℕ → V),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧ (∀ k, J (u k) = e k) ∧
      (∀ (k : ℕ) (v : V), Q (u k) v = kappa k * ⟪J (u k), J v⟫_ℝ) ∧
      ∀ kappa' : ℝ, (∃ w : V, w ≠ 0 ∧ ∀ v, Q w v = kappa' * ⟪J w, J v⟫_ℝ) ↔
        ∃ k, kappa k = kappa' := by
  -- The shifted form `B = Q + β ⟪J ·, J ·⟫` is coercive and symmetric.
  set B : V →L[ℝ] V →L[ℝ] ℝ :=
    Q + β • ((ContinuousLinearMap.toSesqForm J).comp J : V →L[ℝ] V →L[ℝ] ℝ)
  have hB : IsCoercive B := isCoercive_add_smul_toSesqForm_comp_of_garding hC₀ hQ
  have hBQ (u v : V) : B u v = Q u v + β * ⟪J u, J v⟫_ℝ := by
    simp only [B, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSesqForm_apply_coe,
      innerSL_apply_apply, smul_eq_mul]
  have hsymmB (u v : V) : B u v = B v u := by rw [hBQ, hBQ, hsymm, real_inner_comm]
  obtain ⟨s, b, κ, u, hb, hκ, -, hJu, heq, -⟩ :=
    hB.exists_hilbertBasis_forall_apply_eq_smul_inner hJc hJ hsymmB
  have hJu' (x : s) : J (u x) = b x := by rw [hJu, hb]
  have hfin (R : ℝ) : {x : s | κ x ≤ R}.Finite :=
    hB.finite_setOf_le_of_orthonormal hJc b.orthonormal hκ hJu' heq R
  -- The eigenvalue equations of `B` are those of `Q`, moved by `β`.
  have heqQ (x : s) (v : V) : Q (u x) v = (κ x - β) * ⟪J (u x), J v⟫_ℝ := by
    have h := heq x v
    rw [hBQ] at h
    rw [sub_mul]
    linarith
  -- The basis is infinite, since `H` is infinite-dimensional.
  have : Infinite s := by
    rw [← not_finite_iff_infinite]
    intro hs
    have := Fintype.ofFinite s
    exact hH (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  obtain ⟨σ, hσ⟩ := exists_equiv_monotone_comp_of_finite_setOf_le κ hfin
  have hiff (kappa' : ℝ) : (∃ w : V, w ≠ 0 ∧ ∀ v, Q w v = kappa' * ⟪J w, J v⟫_ℝ) ↔
      ∃ k, κ (σ k) - β = kappa' := by
    refine ⟨fun ⟨w, hw, hweq⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨u (σ k), fun h0 ↦ ?_, hk ▸ heqQ (σ k)⟩⟩
    · obtain ⟨x, hx⟩ :=
        exists_eq_of_hilbertBasis_of_garding b hJu' heqQ hsymm hC₀ hQ hw hweq
      exact ⟨σ.symm x, by rw [Equiv.apply_symm_apply, hx]⟩
    · have h := hJu' (σ k)
      rw [h0, map_zero] at h
      exact b.orthonormal.ne_zero _ h.symm
  refine ⟨b.reindex σ.symm, fun k ↦ κ (σ k) - β, u ∘ σ,
    fun i j hij ↦ sub_le_sub_right (hσ hij) β, ?_, fun k ↦ ?_, fun k v ↦ heqQ (σ k) v, hiff⟩
  · simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right _ (-β) (tendsto_comp_atTop_of_finite_setOf_le hfin σ.injective)
  · rw [HilbertBasis.reindex_apply, Equiv.symm_symm, Function.comp_apply, hJu']

end TauCeti
