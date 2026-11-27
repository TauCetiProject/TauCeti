/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.FieldDegree
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# Null Lagrangians of polynomial jets are total divergences

A Lagrangian `L` is a *null Lagrangian* when all its Euler expressions vanish,
`E_a(L) = 0` for every field component `a`. Every total divergence `∑ᵢ Dᵢ Θⁱ` is one
(`PolynomialJet.euler_totalDivergence`). This file proves the converse for polynomial jet
expressions whose coefficients form a `ℚ`-algebra, such as `ℝ` or `ℂ`: a null Lagrangian is a
total divergence up to its field-degree `0` component `L₀(x)`, a polynomial in the base coordinates
alone. When there is at least one base direction, the kernel of the Euler operator in top
horizontal degree is therefore the image of the horizontal differential; with no base directions
the kernel is the constants and the image is `0`.

The argument is the algebraic form of the vertical homotopy that scales the field values,
`u ↦ t u`. The scaling characteristic `Qᵃ = uᵃ` has the prolonged evolutionary derivation
`pr Q = ∑_(a,I) uᵃ_I ∂/∂uᵃ_I`, which multiplies an expression of field degree `m` by `m`
(`PolynomialJet.evolutionaryDeriv_X_eq_nsmul`). The first variation formula
`pr Q (L) = ∑ₐ Qᵃ E_a(L) + ∑ᵢ Dᵢ Θⁱ` then exhibits `m L` as a total divergence when `L` is a null
Lagrangian of field degree `m`. Dividing by `m` replaces the integral `∫₀¹ t^(m-1) dt = 1/m` of the
smooth homotopy formula. The component of field degree `0` is a polynomial `L₀(x)` in the base
coordinates alone; it is a total derivative as soon as there is a base direction, because every
polynomial has an antiderivative in each variable.

## Main results

* `PolynomialJet.sub_weightedHomogeneousComponent_zero_mem_range_totalDivergence`: if
  `E_a(L) = 0` for every `a`, then `L = L₀(x) + ∑ᵢ Dᵢ Θⁱ`, where `L₀` is the field-degree `0`
  component of `L`.
* `PolynomialJet.forall_euler_eq_zero_iff_mem_range_totalDivergence`: for a nonempty set of base
  directions, `L` is a null Lagrangian exactly when it is a total divergence.
* `PolynomialJet.forall_euler_eq_zero_iff_exists_eq_C`: with no base directions, `L` is a null
  Lagrangian exactly when it is a constant.

For example, the cubic density `u² Dᵢu`, whose Euler expressions vanish
(`PolynomialJet.euler_aeval_mul_totalDeriv`), is `Dᵢ(u³/3)`. Some condition on the coefficients
is needed: over `ZMod p` with a single base direction, `x^(p - 1)` is a null Lagrangian but not a
total derivative, since it has no antiderivative (`Polynomial.derivative_not_surjective_of_charP`).

These are identities of polynomial jet expressions: no smooth jet bundle, star-shaped domain or
integral is involved.

## References

* P. J. Olver, *Applications of Lie Groups to Differential Equations*, 2nd ed. (1993), §4.1,
  Theorem 4.7 (null Lagrangians are total divergences) and its homotopy proof.
* I. M. Anderson, *The Variational Bicomplex* (1989), §4A, Propositions 4.1–4.3.
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

variable {R ι α : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Over a `ℚ≥0`-algebra, a polynomial in the base coordinates alone is a total derivative in
every base direction `i`: it has an antiderivative in `xᵢ`. -/
theorem exists_totalDeriv_eq_of_mem_supported [Algebra ℚ≥0 R] (i : ι) {p : PolynomialJet R ι α}
    (hp : p ∈ supported R (Set.range Sum.inl)) : ∃ q, totalDeriv i q = p := by
  classical
  obtain ⟨p, rfl⟩ := exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective
    (mem_supported.1 hp)
  obtain ⟨q, rfl⟩ := pderiv_surjective i p
  refine ⟨rename Sum.inl q, ?_⟩
  simp only [rename_eq_aeval]
  exact (totalDeriv i).map_aeval_eq_aeval_pderiv (totalDeriv_X_base i) q

end CommSemiring

section CommRing

variable [CommRing R] [Fintype ι]

/-- **Euler's homogeneity identity for the field degree.** The prolonged evolutionary derivation
of the scaling characteristic `Qᵃ = uᵃ`, which is `∑_(a,I) uᵃ_I ∂/∂uᵃ_I`, multiplies an expression
of field degree `m` by `m`. -/
theorem evolutionaryDeriv_X_eq_nsmul {L : PolynomialJet R ι α} {m : ℕ}
    (hL : L.IsWeightedHomogeneous (fieldWeight ι α) m) :
    evolutionaryDeriv (fun a ↦ X (Sum.inr (a, 0))) L = m • L :=
  hL.derivation_eq_nsmul _ fun (v : ι ⊕ (α × (ι →₀ ℕ))) ↦ by
    rcases v with j | ⟨a, I⟩ <;> simp [iteratedTotalDeriv_X_field]

/-- If a null Lagrangian `L` has field degree `m`, then `m • L` is a total divergence. -/
theorem nsmul_mem_range_totalDivergence {L : PolynomialJet R ι α} {m : ℕ}
    (hL : L.IsWeightedHomogeneous (fieldWeight ι α) m) (hE : ∀ a, euler a L = 0) :
    m • L ∈ LinearMap.range (totalDivergence R ι α) := by
  obtain ⟨Θ, hΘ⟩ :=
    exists_evolutionaryDeriv_eq_finsum_mul_euler_add_totalDivergence (fun a ↦ X (Sum.inr (a, 0))) L
  rw [evolutionaryDeriv_X_eq_nsmul hL] at hΘ
  simp only [hE, mul_zero, finsum_zero, zero_add] at hΘ
  exact ⟨Θ, hΘ.symm⟩

section RatAlgebra

variable [Algebra ℚ R]

/-- Over a `ℚ`-algebra, a null Lagrangian of positive field degree is a total divergence. -/
theorem mem_range_totalDivergence_of_isWeightedHomogeneous {L : PolynomialJet R ι α} {m : ℕ}
    (hm : m ≠ 0) (hL : L.IsWeightedHomogeneous (fieldWeight ι α) m) (hE : ∀ a, euler a L = 0) :
    L ∈ LinearMap.range (totalDivergence R ι α) := by
  have h := Submodule.smul_of_tower_mem _ (m : ℚ)⁻¹ (nsmul_mem_range_totalDivergence hL hE)
  rwa [← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hm)] at h

/-- **Null Lagrangians are total divergences up to a base polynomial.** Over a `ℚ`-algebra, if
`E_a(L) = 0` for every field component `a`, then `L - L₀` is a total divergence, where `L₀` is the
component of `L` of field degree `0`, a polynomial in the base coordinates alone
(`PolynomialJet.isWeightedHomogeneous_fieldWeight_zero_iff`). -/
theorem sub_weightedHomogeneousComponent_zero_mem_range_totalDivergence {L : PolynomialJet R ι α}
    (hE : ∀ a, euler a L = 0) :
    L - weightedHomogeneousComponent (fieldWeight ι α) 0 L ∈
      LinearMap.range (totalDivergence R ι α) := by
  classical
  -- decompose `L` into its finitely many field-degree components, including degree `0`
  have hfin := weightedHomogeneousComponent_finsupp (w := fieldWeight ι α) L
  set s := insert 0 hfin.toFinset
  have hL : L = ∑ m ∈ s, weightedHomogeneousComponent (fieldWeight ι α) m L := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (fieldWeight ι α) L]
    exact finsum_eq_sum_of_support_subset _ fun m hm ↦ by simp [s, hfin.mem_toFinset.2 hm]
  have hsub : L - weightedHomogeneousComponent (fieldWeight ι α) 0 L =
      ∑ m ∈ s.erase 0, weightedHomogeneousComponent (fieldWeight ι α) m L := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_insert_self 0 _), ← hL]
  rw [hsub]
  refine Submodule.sum_mem _ fun m hm ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.ne_of_mem_erase hm)
  -- the Euler expressions of the field-degree `k + 1` component are the field-degree `k`
  -- components of `E_a(L) = 0`
  refine mem_range_totalDivergence_of_isWeightedHomogeneous k.succ_ne_zero
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _) fun a ↦ ?_
  rw [← weightedHomogeneousComponent_euler, hE, map_zero]

/-- **Null Lagrangians are total divergences.** Over a `ℚ`-algebra and with at least one base
direction, all Euler expressions of `L` vanish exactly when `L` is a total divergence. -/
theorem forall_euler_eq_zero_iff_mem_range_totalDivergence [Nonempty ι]
    {L : PolynomialJet R ι α} :
    (∀ a, euler a L = 0) ↔ L ∈ LinearMap.range (totalDivergence R ι α) := by
  refine ⟨fun hE ↦ ?_, fun ⟨Θ, hΘ⟩ a ↦ hΘ ▸ euler_totalDivergence a Θ⟩
  -- the antiderivative of the base component only needs to divide by positive integers
  let : Algebra ℚ≥0 R := Algebra.compHom R NNRat.coeHom
  obtain ⟨q, hq⟩ := exists_totalDeriv_eq_of_mem_supported (Classical.arbitrary ι)
    (isWeightedHomogeneous_fieldWeight_zero_iff.1
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := fieldWeight ι α) 0 L))
  have h := add_mem (sub_weightedHomogeneousComponent_zero_mem_range_totalDivergence hE)
    (hq ▸ totalDeriv_mem_range_totalDivergence _ q)
  rwa [sub_add_cancel] at h

/-- With no base directions there are no total derivatives: over a `ℚ`-algebra, all Euler
expressions `E_a(L) = ∂L/∂uᵃ` vanish exactly when `L` is a constant. -/
theorem forall_euler_eq_zero_iff_exists_eq_C [IsEmpty ι] {L : PolynomialJet R ι α} :
    (∀ a, euler a L = 0) ↔ ∃ c, L = C c := by
  refine ⟨fun hE ↦ ?_, fun ⟨c, hc⟩ a ↦ hc ▸ euler_C a c⟩
  obtain ⟨Θ, hΘ⟩ := sub_weightedHomogeneousComponent_zero_mem_range_totalDivergence hE
  have h₀ := isWeightedHomogeneous_fieldWeight_zero_iff.1
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := fieldWeight ι α) 0 L)
  rw [Set.range_eq_empty, supported_empty, Algebra.mem_bot] at h₀
  obtain ⟨c, hc⟩ := h₀
  refine ⟨c, ?_⟩
  rw [Subsingleton.elim Θ 0, map_zero, eq_comm, sub_eq_zero] at hΘ
  rw [hΘ, ← hc, algebraMap_eq]

end RatAlgebra

end CommRing

end PolynomialJet

end TauCeti
