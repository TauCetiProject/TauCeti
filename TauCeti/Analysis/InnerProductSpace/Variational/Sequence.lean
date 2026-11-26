/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
import TauCeti.Order.Northcott.Enumeration

/-!
# The variational eigenvalues as a nondecreasing sequence

Let `B` be a symmetric coercive bounded bilinear form on a real Hilbert space `V`, and let
`J : V →L[ℝ] H` be a compact operator with dense range into an infinite-dimensional real Hilbert
space `H`. The variational eigenvalue problem

`B u v = κ ⟪J u, J v⟫` for every `v : V`, `u ≠ 0`,

then has a complete system of solutions listed by `ℕ` with multiplicity: there are a
nondecreasing sequence `0 < κ₀ ≤ κ₁ ≤ ⋯ → ∞` and eigenfunctions `uₖ` whose images `J uₖ` form an
orthonormal basis of `H`, and a real number is a variational eigenvalue exactly when it is some
`κₖ` (`IsCoercive.exists_hilbertBasis_nat_forall_apply_eq_smul_inner_monotone`).

This is the shape in which the eigenvalue problems of elliptic operators are used: `V` is a
Sobolev space encoding the boundary condition, `H = L²(Ω)`, `J` is the inclusion, compact by
Rellich–Kondrachov, and `B` is the energy form, shifted by a multiple of `⟪J ·, J ·⟫` when it is
only coercive up to such a term.

## The argument

The eigenbasis `IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner` is indexed by a set of
vectors of `H`. Since `J` is compact, only finitely many of its eigenvalues lie below any bound
(`IsCoercive.finite_setOf_le_of_orthonormal`), and since `H` is infinite-dimensional the basis is
infinite. A family with these two properties can be listed in nondecreasing order along a bijection
with `ℕ` (`TauCeti.exists_equiv_monotone_comp_of_finite_setOf_le`), and the listing tends to
infinity. An eigenvalue missing from the listing would have an eigenfunction `w` with `J w ≠ 0`
orthogonal to every basis vector, since eigenfunctions of a symmetric form for distinct eigenvalues
are orthogonal; so there is none.

The Dirichlet eigenvalue sequence
`TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_monotone` is an instance.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 6.11 and Theorem 9.31.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H}

/-- **The variational eigenvalues form a sequence `0 < κ₀ ≤ κ₁ ≤ ⋯ → ∞`.** Let `B` be symmetric
and coercive, and let `J` be compact with dense range in an infinite-dimensional Hilbert space
`H`. Then there are a nondecreasing sequence `κₖ` of positive reals tending to infinity and
`uₖ : V` such that the `J uₖ` form an orthonormal basis of `H` and `B uₖ v = κₖ ⟪J uₖ, J v⟫` for
every `v`. The sequence lists the variational eigenvalues with multiplicity: `κ` admits a nonzero
`w` with `B w v = κ ⟪J w, J v⟫` for every `v` exactly when `κ = κₖ` for some `k`. In this basis
the solution operator is diagonal, `S h = ∑ₖ κₖ⁻¹ ⟪eₖ, h⟫ eₖ`, where `S h = J u` for the solution
`u` of `B u v = ⟪h, J v⟫`. -/
theorem exists_hilbertBasis_nat_forall_apply_eq_smul_inner_monotone (hB : IsCoercive B)
    (hJ : IsCompactOperator J) (hJdense : DenseRange J) (hsymm : ∀ u v : V, B u v = B v u)
    (hH : ¬ FiniteDimensional ℝ H) :
    ∃ (basis : HilbertBasis ℕ ℝ H) (kappa : ℕ → ℝ) (u : ℕ → V),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧ (∀ k, 0 < kappa k) ∧
      (∀ k, J (u k) = basis k) ∧ (∀ (k : ℕ) (v : V), B (u k) v = kappa k * ⟪J (u k), J v⟫_ℝ) ∧
      (∀ kappa' : ℝ, (∃ w : V, w ≠ 0 ∧ ∀ v : V, B w v = kappa' * ⟪J w, J v⟫_ℝ) ↔
        ∃ k, kappa k = kappa') ∧
      ∀ h : H, HasSum (fun k ↦ (kappa k)⁻¹ • basis.repr h k • basis k)
        (hB.formSolutionOperator J h) := by
  obtain ⟨s, b, kappa, u, hb, hpos, hune, hJu, heq, hsum⟩ :=
    hB.exists_hilbertBasis_forall_apply_eq_smul_inner hJ hJdense hsymm
  have hJb (x : s) : J (u x) = b x := by rw [hb, hJu]
  have hfin (R : ℝ) : {x : s | kappa x ≤ R}.Finite :=
    hB.finite_setOf_le_of_orthonormal hJ b.orthonormal hpos hJb heq R
  -- The basis is infinite, since `H` is infinite-dimensional.
  have : Infinite s := by
    rw [← not_finite_iff_infinite]
    intro hs
    have := Fintype.ofFinite s
    exact hH (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  obtain ⟨e, he⟩ := exists_equiv_monotone_comp_of_finite_setOf_le kappa hfin
  -- Reindex the eigenbasis along the nondecreasing enumeration `e`.
  refine ⟨b.reindex e.symm, kappa ∘ e, u ∘ e, he,
    tendsto_comp_atTop_of_finite_setOf_le hfin e.injective, fun k ↦ hpos (e k),
    fun k ↦ by rw [b.reindex_apply, e.symm_symm]; exact hJb (e k), fun k v ↦ heq (e k) v,
    fun kappa' ↦ ⟨fun ⟨w, hw, hweq⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨u (e k), hune (e k), hk ▸ heq (e k)⟩⟩,
    fun h ↦ ?_⟩
  · -- An eigenvalue missing from the sequence would have an eigenfunction orthogonal to the whole
    -- eigenbasis.
    by_contra! hne
    refine hB.apply_ne_zero_of_forall_apply_eq_smul_inner J hw hweq
      (b.repr.map_eq_zero_iff.1 (lp.ext (funext fun x ↦ ?_)))
    have hx : kappa x ≠ kappa' := by simpa using hne (e.symm x)
    have h := hsymm w (u x)
    rw [hweq, heq, hJb, real_inner_comm] at h
    rw [HilbertBasis.repr_apply_apply, lp.coeFn_zero, Pi.zero_apply]
    exact (mul_eq_mul_right_iff.1 h.symm).resolve_left hx
  · convert (e.hasSum_iff).2 (hsum h) using 1
    funext k
    simp only [Function.comp_apply, HilbertBasis.repr_reindex_apply, HilbertBasis.reindex_apply,
      Equiv.symm_symm]

end IsCoercive
