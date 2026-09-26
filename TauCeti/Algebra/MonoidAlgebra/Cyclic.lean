/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.FiniteType

/-!
# The group algebra of a finite cyclic group: the powers of `σ - 1`

Let `C` be a finite cyclic group with generator `σ`, and let `R` be a commutative ring. The
powers `(σ - 1) ^ i` for `0 ≤ i < |C|` form an `R`-basis of the group algebra `R[C]`
(`TauCeti.MonoidAlgebra.basisSubOnePow`). In this basis, the coordinates of the value
`f(σ - 1) ∈ R[C]` of a polynomial `f` of degree `< |C|` are the coefficients of `f`
(`basisSubOnePow_repr_aeval`), so such an `f` is determined by `f(σ - 1)`; in particular, if
`f(σ - 1)` is a scalar multiple `r • y`, then `r` divides every coefficient of `f`
(`dvd_coeff_of_aeval_of_sub_one_eq_smul`).

These coefficient and divisibility formulas supply the finite-level linear algebra used for the
power-series coordinate `ℤ_p⟦X⟧ ≅ ℤ_p[[Γ]]` of an infinite procyclic profinite pro-`p` group `Γ`.

## Main declarations

* `TauCeti.MonoidAlgebra.basisSubOnePow`: the basis `(σ - 1) ^ i`, `i < |C|`, of `R[C]`.
* `TauCeti.MonoidAlgebra.basisSubOnePow_repr_aeval`: the coordinates of `f(σ - 1)` are the
  coefficients of `f`, for `deg f < |C|`.
* `TauCeti.MonoidAlgebra.dvd_coeff_of_aeval_of_sub_one_eq_smul`: if `f(σ - 1) = r • y` with
  `deg f < |C|`, then `r` divides every coefficient of `f`.
-/

public section

namespace TauCeti.MonoidAlgebra

open Module Polynomial

variable {R : Type*} [CommRing R] {C : Type*} [Group C] [Finite C] {σ : C}

/-- The powers `(σ - 1) ^ i` for `i < |C|` of a generator `σ` of a finite cyclic group `C` span
the group algebra `R[C]`. -/
theorem span_range_of_sub_one_pow_eq_top (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Submodule.span R (Set.range fun i : Fin (Nat.card C) ↦
      (MonoidAlgebra.of R C σ - 1) ^ (i : ℕ)) = ⊤ := by
  have := Fintype.ofFinite C
  suffices h : ∀ x : MonoidAlgebra R C, x ∈ Submodule.span R (Set.range fun i : Fin (Nat.card C) ↦
      (MonoidAlgebra.of R C σ - 1) ^ (i : ℕ)) from top_unique fun x _ ↦ h x
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    -- Every group element is `σ ^ j` with `j < |C|`, the order of `σ`.
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff m σ).mp (mem_powers_iff_mem_zpowers.mpr (hσ m))
    rw [← pow_mod_orderOf, orderOf_eq_card_of_forall_mem_zpowers hσ]
    have hj : j % Nat.card C < Nat.card C := Nat.mod_lt _ Nat.card_pos
    -- Expand `σ ^ j = ((σ - 1) + 1) ^ j` binomially.
    have hexp : MonoidAlgebra.of R C σ ^ (j % Nat.card C) =
        ((MonoidAlgebra.of R C σ - 1) + 1) ^ (j % Nat.card C) := by rw [sub_add_cancel]
    rw [map_pow, hexp, (Commute.one_right _).add_pow]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hi' : i < Nat.card C := (Finset.mem_range_succ_iff.mp hi).trans_lt hj
    rw [one_pow, mul_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul R]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩)
  | add x y hx hy => exact add_mem hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

/-- The powers `(σ - 1) ^ i` for `i < |C|` of a generator `σ` of a finite cyclic group `C` are
linearly independent in the group algebra `R[C]`. -/
theorem linearIndependent_of_sub_one_pow (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    LinearIndependent R fun i : Fin (Nat.card C) ↦ (MonoidAlgebra.of R C σ - 1) ^ (i : ℕ) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact linearIndependent_of_subsingleton
  · have := Fintype.ofFinite C
    refine linearIndependent_of_top_le_span_of_card_eq_finrank
      (span_range_of_sub_one_pow_eq_top hσ).ge ?_
    rw [Fintype.card_fin, finrank_eq_card_basis (MonoidAlgebra.basis C R), Nat.card_eq_fintype_card]

/-- **The basis of powers of `σ - 1`.** For a generator `σ` of a finite cyclic group `C`, the
powers `(σ - 1) ^ i` with `0 ≤ i < |C|` form an `R`-basis of the group algebra `R[C]`. -/
noncomputable def basisSubOnePow (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Basis (Fin (Nat.card C)) R (MonoidAlgebra R C) :=
  Basis.mk (linearIndependent_of_sub_one_pow hσ) (span_range_of_sub_one_pow_eq_top hσ).ge

@[simp]
theorem coe_basisSubOnePow (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ⇑(basisSubOnePow (R := R) hσ) = fun i : Fin (Nat.card C) ↦
      (MonoidAlgebra.of R C σ - 1) ^ (i : ℕ) :=
  Basis.coe_mk _ _

/-- The coordinates of `f(σ - 1)` in the basis of powers of `σ - 1` are the coefficients of the
polynomial `f`, when `f` has degree `< |C|`. -/
theorem basisSubOnePow_repr_aeval (hσ : ∀ x, x ∈ Subgroup.zpowers σ) {f : R[X]}
    (hf : f.degree < Nat.card C) (i : Fin (Nat.card C)) :
    (basisSubOnePow hσ).repr (aeval (MonoidAlgebra.of R C σ - 1) f) i = f.coeff i := by
  have hnat : f.natDegree < Nat.card C := by
    rcases eq_or_ne f 0 with rfl | h0
    · simp
    · exact (natDegree_lt_iff_degree_lt h0).mpr hf
  have : aeval (MonoidAlgebra.of R C σ - 1) f =
      ∑ j : Fin (Nat.card C), f.coeff j • basisSubOnePow (R := R) hσ j := by
    rw [aeval_eq_sum_range' hnat, Finset.sum_range]
    simp
  rw [this, Basis.repr_sum_self]

/-- If the value `f(σ - 1) ∈ R[C]` of a polynomial `f` of degree `< |C|` at `σ - 1` is a scalar
multiple `r • y`, then `r` divides every coefficient of `f`. -/
theorem dvd_coeff_of_aeval_of_sub_one_eq_smul (hσ : ∀ x, x ∈ Subgroup.zpowers σ) {f : R[X]}
    (hf : f.degree < Nat.card C) {r : R} {y : MonoidAlgebra R C}
    (h : aeval (MonoidAlgebra.of R C σ - 1) f = r • y) (i : ℕ) : r ∣ f.coeff i := by
  by_cases hi : i < Nat.card C
  · rw [← basisSubOnePow_repr_aeval hσ hf ⟨i, hi⟩, h, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  · rw [coeff_eq_zero_of_degree_lt (hf.trans_le (by exact_mod_cast not_lt.mp hi))]
    exact dvd_zero _

end TauCeti.MonoidAlgebra
