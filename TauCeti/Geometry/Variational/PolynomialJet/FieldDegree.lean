/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.Geometry.Variational.PolynomialJet.Euler
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.Derivation
import TauCeti.Data.Finsupp.Multiset

/-!
# Field degree and the nonlinearity of Euler expressions

The **field degree** of a polynomial jet expression counts field-jet coordinates `uᵃ_I` only:
it is the weighted degree for the weight `PolynomialJet.fieldWeight`, which gives every field
coordinate weight `1` and every base coordinate `xⱼ` weight `0`. An expression is homogeneous of
field degree `0` exactly when it involves no field coordinates, that is, when it is a polynomial
in the base coordinates alone (`PolynomialJet.isWeightedHomogeneous_fieldWeight_zero_iff`).

Total derivatives preserve field degree, and partial derivatives in field coordinates lower it by
one, so the Euler operator `E_a(L) = ∑_I (-D)_I (∂L/∂uᵃ_I)` lowers it by one: the field-degree
`m` component of `E_a(L)` is the Euler expression of the field-degree `m + 1` component of `L`
(`PolynomialJet.weightedHomogeneousComponent_euler`), and `E_a` vanishes on expressions of field
degree `0`.

## Main results

* `PolynomialJet.euler_eq_add_of_weightedTotalDegree_le_two`: if `L` has field degree at most
  two, then `E_a(L) = E_a(L₁) + E_a(L₂)`, where `L₁` and `L₂` are the field-degree `1` and `2`
  components of `L`. The first term is a polynomial in the base coordinates (the linear source
  term) and the second is homogeneous linear in the field jets, so `E_a(L)` is affine-linear in
  the field jets.
* `PolynomialJet.isWeightedHomogeneous_euler_one_iff`: for such `L`, `E_a(L)` is homogeneous
  linear exactly when its linear source term `E_a(L₁)` vanishes.
* `PolynomialJet.euler_aeval_mul_totalDeriv`: for every one-variable polynomial `g`,
  `E(g(u) Dᵢu) = 0`. With `g = u²` the density `u² Dᵢu` has field degree three while its Euler
  expression vanishes, so a field degree above two does not by itself give a nonlinear Euler
  expression.

These are identities of polynomial jet expressions over an arbitrary commutative ring, in the
polynomial linear-field model.

## References

* P. J. Olver, *Applications of Lie Groups to Differential Equations*, 2nd ed. (1993), §4.1.
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α : Type*}

variable (ι α) in
/-- The field-degree weight on the variables of `PolynomialJet R ι α`: base coordinates have
weight `0` and field-jet coordinates have weight `1`. -/
def fieldWeight : ι ⊕ (α × (ι →₀ ℕ)) → ℕ :=
  Sum.elim 0 1

@[simp]
theorem fieldWeight_inl (j : ι) : fieldWeight ι α (Sum.inl j) = 0 :=
  (rfl)

@[simp]
theorem fieldWeight_inr (aI : α × (ι →₀ ℕ)) : fieldWeight ι α (Sum.inr aI) = 1 :=
  (rfl)

section CommSemiring

variable [CommSemiring R]

/-- An expression has field degree `0` exactly when it is a polynomial in the base coordinates. -/
theorem isWeightedHomogeneous_fieldWeight_zero_iff {p : PolynomialJet R ι α} :
    p.IsWeightedHomogeneous (fieldWeight ι α) 0 ↔ p ∈ supported R (Set.range Sum.inl) := by
  rw [mem_supported]
  constructor
  · intro h v hv
    obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
    rcases v with j | aI
    · exact ⟨j, rfl⟩
    · -- a field coordinate in the monomial `d` would give it positive field degree
      have hle := Finsupp.le_weight (fieldWeight ι α) (s := Sum.inr aI) (by simp) d
      rw [h (mem_support_iff.1 hd)] at hle
      exact absurd (Nat.le_zero.1 hle) (Finsupp.mem_support_iff.1 hvd)
  · intro h d hd
    rw [Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    obtain ⟨j, rfl⟩ := h ((mem_vars_iff_mem_support v).2 ⟨d, mem_support_iff.2 hd, hv⟩)
    simp

/-- Total derivatives preserve field degree. -/
theorem isWeightedHomogeneous_totalDeriv (i : ι) {p : PolynomialJet R ι α} {m : ℕ}
    (hp : p.IsWeightedHomogeneous (fieldWeight ι α) m) :
    (totalDeriv i p).IsWeightedHomogeneous (fieldWeight ι α) m := by
  classical
  refine hp.derivation 0 (totalDeriv i) fun v ↦ ?_
  rcases v with j | ⟨a, I⟩
  · rw [totalDeriv_X_base, fieldWeight_inl, add_zero]
    split
    · exact isWeightedHomogeneous_one R _
    · exact isWeightedHomogeneous_zero R _ 0
  · simpa using isWeightedHomogeneous_X R (fieldWeight ι α) (Sum.inr (a, I + Finsupp.single i 1))

end CommSemiring

section CommRing

variable [CommRing R] [Fintype ι]

/-- The Euler operator vanishes on expressions of field degree `0`. -/
theorem euler_eq_zero_of_isWeightedHomogeneous_zero (a : α)
    {L : PolynomialJet R ι α} (hL : L.IsWeightedHomogeneous (fieldWeight ι α) 0) :
    euler a L = 0 := by
  have hv := mem_supported.1 (isWeightedHomogeneous_fieldWeight_zero_iff.1 hL)
  rw [euler_eq_sum a L ∅ fun I _ ↦ pderiv_eq_zero_of_notMem_vars fun h ↦ by simpa using hv h]
  simp

/-- Iterated total derivatives preserve field degree. -/
theorem isWeightedHomogeneous_iteratedTotalDeriv (I : ι →₀ ℕ) {p : PolynomialJet R ι α}
    {m : ℕ} (hp : p.IsWeightedHomogeneous (fieldWeight ι α) m) :
    (iteratedTotalDeriv I p).IsWeightedHomogeneous (fieldWeight ι α) m := by
  induction I using Finsupp.induction_add_single_one with
  | zero => simpa using hp
  | add_single_one i I ih =>
    rw [iteratedTotalDeriv_add_single_one]
    exact isWeightedHomogeneous_totalDeriv i ih

/-- The Euler operator lowers field degree by one. -/
theorem isWeightedHomogeneous_euler (a : α) {L : PolynomialJet R ι α} {m : ℕ}
    (hL : L.IsWeightedHomogeneous (fieldWeight ι α) (m + 1)) :
    (euler a L).IsWeightedHomogeneous (fieldWeight ι α) m := by
  rw [← mem_weightedHomogeneousSubmodule, euler_apply]
  refine finsum_induction (· ∈ weightedHomogeneousSubmodule R (fieldWeight ι α) m) (zero_mem _)
    (fun _ _ ↦ add_mem) fun I ↦ Submodule.smul_mem _ _ ?_
  exact isWeightedHomogeneous_iteratedTotalDeriv I (hL.pderiv (by simp))

/-- The field-degree `m` component of the Euler expression `E_a(L)` is the Euler expression of
the field-degree `m + 1` component of `L`. -/
theorem weightedHomogeneousComponent_euler (a : α) (m : ℕ) (L : PolynomialJet R ι α) :
    weightedHomogeneousComponent (fieldWeight ι α) m (euler a L) =
      euler a (weightedHomogeneousComponent (fieldWeight ι α) (m + 1) L) := by
  induction L using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial d r =>
    obtain ⟨n, hn⟩ : ∃ n, Finsupp.weight (fieldWeight ι α) d = n := ⟨_, rfl⟩
    have hd := isWeightedHomogeneous_monomial (fieldWeight ι α) d r hn
    by_cases hnm : n = m + 1
    · subst hnm
      rw [hd.weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_euler a hd).weightedHomogeneousComponent_same]
    · rw [hd.weightedHomogeneousComponent_ne _ (Ne.symm hnm), map_zero]
      rcases n with _ | k
      · rw [euler_eq_zero_of_isWeightedHomogeneous_zero a hd, map_zero]
      · exact (isWeightedHomogeneous_euler a hd).weightedHomogeneousComponent_ne m (by omega)

/-- The field degree of the Euler expression `E_a(L)` is at most the field degree of `L` minus
one. -/
theorem weightedTotalDegree_euler_le (a : α) (L : PolynomialJet R ι α) :
    (euler a L).weightedTotalDegree (fieldWeight ι α) ≤
      L.weightedTotalDegree (fieldWeight ι α) - 1 := by
  classical
  refine Finset.sup_le fun d hd ↦ ?_
  -- the coefficient of `d` only sees the component of field degree `weight d + 1` of `L`
  have hc : (euler a L).coeff d = (euler a (weightedHomogeneousComponent (fieldWeight ι α)
      (Finsupp.weight (fieldWeight ι α) d + 1) L)).coeff d := by
    rw [← weightedHomogeneousComponent_euler, coeff_weightedHomogeneousComponent]
    simp
  by_contra hlt
  rw [weightedHomogeneousComponent_eq_zero _ _ (by omega), map_zero] at hc
  exact mem_support_iff.1 hd (by simpa using hc)

/-- **Field degree at most two gives an affine-linear Euler expression.** If `L` has field degree
at most two, then `E_a(L) = E_a(L₁) + E_a(L₂)` for its field-degree `1` and `2` components `L₁` and
`L₂`. The linear source term `E_a(L₁)` has field degree `0`, so it is a polynomial in the base
coordinates (`isWeightedHomogeneous_fieldWeight_zero_iff`), and `E_a(L₂)` has field degree `1`
(`isWeightedHomogeneous_euler`). -/
theorem euler_eq_add_of_weightedTotalDegree_le_two (a : α) {L : PolynomialJet R ι α}
    (hL : L.weightedTotalDegree (fieldWeight ι α) ≤ 2) :
    euler a L = euler a (weightedHomogeneousComponent (fieldWeight ι α) 1 L) +
      euler a (weightedHomogeneousComponent (fieldWeight ι α) 2 L) := by
  have hsum : L = ∑ m ∈ Finset.range 3, weightedHomogeneousComponent (fieldWeight ι α) m L := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (fieldWeight ι α) L]
    refine finsum_eq_sum_of_support_subset _ fun m hm ↦ ?_
    by_contra h
    exact hm (weightedHomogeneousComponent_eq_zero _ _ (by simp at h; omega))
  conv_lhs => rw [hsum]
  simp [Finset.sum_range_succ, euler_eq_zero_of_isWeightedHomogeneous_zero a
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]

/-- For `L` of field degree at most two, the Euler expression `E_a(L)` is homogeneous linear in
the field jets exactly when its linear source term `E_a(L₁)` vanishes, where `L₁` is the
field-degree `1` component of `L`. -/
theorem isWeightedHomogeneous_euler_one_iff (a : α) {L : PolynomialJet R ι α}
    (hL : L.weightedTotalDegree (fieldWeight ι α) ≤ 2) :
    (euler a L).IsWeightedHomogeneous (fieldWeight ι α) 1 ↔
      euler a (weightedHomogeneousComponent (fieldWeight ι α) 1 L) = 0 := by
  have h₀ := isWeightedHomogeneous_euler a (m := 0)
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := fieldWeight ι α) 1 L)
  have h₁ := isWeightedHomogeneous_euler a (m := 1)
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := fieldWeight ι α) 2 L)
  rw [euler_eq_add_of_weightedTotalDegree_le_two a hL]
  constructor
  · intro h
    have h0 := h.weightedHomogeneousComponent_ne 0 zero_ne_one
    rwa [map_add, h₀.weightedHomogeneousComponent_same,
      h₁.weightedHomogeneousComponent_ne 0 zero_ne_one, add_zero] at h0
  · intro h
    rw [h, zero_add]
    exact h₁

/-- **A nonlinear density with vanishing Euler expression.** For every one-variable polynomial
`g` and every jet coordinate `u = uᵃ_J`, the density `g(u) Dᵢu` has Euler expression zero for every
field component `b`. For `g = u²` and `J = 0` the density `u² Dᵢu = Dᵢ(u³/3)` has field degree
three. -/
theorem euler_aeval_mul_totalDeriv (a b : α) (J : ι →₀ ℕ) (i : ι) (g : Polynomial R) :
    euler b (Polynomial.aeval (X (Sum.inr (a, J)) : PolynomialJet R ι α) g *
      totalDeriv i (X (Sum.inr (a, J)))) = 0 := by
  classical
  by_cases hb : b = a
  · subst hb
    have hJ : J ≠ J + Finsupp.single i 1 := by simp
    rw [euler_eq_sum b _ {J, J + Finsupp.single i 1} fun I hI ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hI
      simp [Derivation.leibniz, Derivation.map_aeval, pderiv_X, Ne.symm hI.1, Ne.symm hI.2]]
    rw [Finset.sum_pair hJ]
    simp [Derivation.leibniz, Derivation.map_aeval, pderiv_X, hJ, Ne.symm hJ,
      iteratedTotalDeriv_add_single_one, totalDeriv_iteratedTotalDeriv_comm, pow_succ, mul_comm]
  · rw [euler_eq_sum b _ ∅ fun I _ ↦ by
      simp [Derivation.leibniz, Derivation.map_aeval, pderiv_X, hb]]
    simp

end CommRing

end

end PolynomialJet

end TauCeti
