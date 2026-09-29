/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic
public import Mathlib.Algebra.Central.Basic
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Crossed products are central simple

For a field `L`, a commutative semiring `K` with `Algebra K L` and a `2`-cocycle `c` of
`Aut_K(L)` with values in `Lˣ`, this file proves that the crossed product `(L, Aut_K(L), c)` is a
simple ring, and that it is central over `K` when `L/K` is a Galois extension of fields.

Both proofs compare coefficients in the `L`-basis `u_σ`:

* **simplicity**: a nonzero element `a = ∑ a_σ u_σ` of a two-sided ideal with at least two
  coefficients `a_σ, a_ρ ≠ 0` gives the element `a · x - ρ(x) · a = ∑ a_τ (τ(x) - ρ(x)) u_τ` of
  the ideal, which for `σ(x) ≠ ρ(x)` is nonzero with a smaller support. An element of minimal
  support is therefore a single `y · u_σ`, which is a unit;
* **centrality**: a central element commutes with `L`, so all its coefficients off `u_1` vanish
  because distinct automorphisms differ somewhere, and it commutes with every `u_τ`, so its
  remaining coefficient is fixed by the Galois group and lies in `K`.

## Main results

* `TauCeti.CrossedProduct.instIsSimpleRing`: the crossed product is a simple ring.
* `TauCeti.CrossedProduct.instIsCentral`: for `L/K` Galois, the crossed product is central over
  `K`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

universe u v

namespace TauCeti

namespace CrossedProduct

section Simple

variable {K : Type u} [CommSemiring K] {L : Type v} [Field L] [Algebra K L]
  {c : TwoCocycle K L}

/-- A nonzero element of a two-sided ideal of the crossed product whose support has at most `n`
elements yields a nonzero single term `y · u_σ` of the ideal. -/
private theorem exists_smul_basis_mem (I : TwoSidedIdeal (CrossedProduct c)) (n : ℕ) :
    ∀ a ∈ I, a ≠ 0 → ((basis c).repr a).support.card ≤ n →
      ∃ (σ : L ≃ₐ[K] L) (y : L), y ≠ 0 ∧ y • basis c σ ∈ I := by
  induction n with
  | zero =>
    intro a _ ha hcard
    simp_all
  | succ n ih =>
    classical
    intro a haI ha hcard
    have hpos : 0 < ((basis c).repr a).support.card := by simp_all
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | h1
    · -- a single term
      obtain ⟨σ, y, hy, hσ⟩ := Finsupp.card_support_eq_one'.1 h1.symm
      refine ⟨σ, y, hy, ?_⟩
      rwa [← (basis c).repr_symm_single, ← hσ, LinearEquiv.symm_apply_apply]
    · -- two distinct automorphisms `σ ≠ ρ` in the support, separated by some `x`
      obtain ⟨σ, hσ, ρ, hρ, hne⟩ := Finset.one_lt_card.1 h1
      obtain ⟨x, hx⟩ : ∃ x, σ x ≠ ρ x := by
        by_contra! h
        exact hne (AlgEquiv.ext h)
      have hb : ∀ τ, (basis c).repr (a * inc c x - inc c (ρ x) * a) τ =
          (basis c).repr a τ * (τ x - ρ x) := fun τ => by
        rw [← smul_def, map_sub, Finsupp.sub_apply, repr_mul_inc, map_smul, Finsupp.smul_apply,
          smul_eq_mul]
        ring
      refine ih (a * inc c x - inc c (ρ x) * a)
        (I.sub_mem (I.mul_mem_right _ _ haI) (I.mul_mem_left _ _ haI)) ?_ ?_
      · intro h0
        have := hb σ
        rw [h0, map_zero, Finsupp.zero_apply] at this
        exact mul_ne_zero (Finsupp.mem_support_iff.1 hσ) (sub_ne_zero.2 hx) this.symm
      · have hsub : ((basis c).repr (a * inc c x - inc c (ρ x) * a)).support ⊆
            ((basis c).repr a).support.erase ρ := fun τ hτ => by
          rw [Finsupp.mem_support_iff, hb] at hτ
          refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hτ)⟩
          rintro rfl
          simp at hτ
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hρ] at this
        omega

/-- A two-sided ideal of the crossed product containing a nonzero single term `y · u_σ` contains
`1`: the term has the left inverse `(c(1, 1)⁻¹ · σ⁻¹(y)⁻¹ · c(σ⁻¹, σ)⁻¹) · u_{σ⁻¹}`. -/
private theorem one_mem_of_smul_basis_mem (I : TwoSidedIdeal (CrossedProduct c))
    {σ : L ≃ₐ[K] L} {y : L} (hy : y ≠ 0) (hI : y • basis c σ ∈ I) : (1 : CrossedProduct c) ∈ I := by
  have hσy : σ⁻¹ y ≠ 0 := (map_ne_zero _).2 hy
  convert I.mul_mem_left
    (((c.toFun (1, 1) : L)⁻¹ * (σ⁻¹ y)⁻¹ * (c.toFun (σ⁻¹, σ) : L)⁻¹) • basis c σ⁻¹) _ hI using 1
  rw [smul_basis_mul_smul_basis, inv_mul_cancel, one_def, Units.val_inv_eq_inv_val]
  congr 1
  field_simp

/-- **The crossed product is a simple ring.** -/
instance instIsSimpleRing : IsSimpleRing (CrossedProduct c) :=
  .of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.2 fun hI => by
    obtain ⟨a, haI, ha : a ≠ 0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hI)
    obtain ⟨σ, y, hy, hmem⟩ := exists_smul_basis_mem I _ a haI ha le_rfl
    exact I.one_mem_iff.1 (one_mem_of_smul_basis_mem I hy hmem)

end Simple

section Central

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (c : TwoCocycle K L)

/-- **The crossed product of a Galois extension is central.** -/
instance instIsCentral [IsGalois K L] : Algebra.IsCentral K (CrossedProduct c) where
  out a ha := by
    rw [Subalgebra.mem_center_iff] at ha
    -- commuting with `L` kills the coefficients off `u_1`
    have h1 : ∀ σ ≠ 1, (basis c).repr a σ = 0 := fun σ hσ => by
      obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra! h
        exact hσ (AlgEquiv.ext h)
      have h := congrArg (fun b => (basis c).repr b σ) (ha (inc c x))
      simp only [← smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, repr_mul_inc] at h
      exact (mul_eq_zero.1 (by linear_combination h)).resolve_right (sub_ne_zero.2 hx.symm)
    -- so `a = y · c(1, 1)⁻¹ · u_1 = inc c y` for `y = a_1 · c(1, 1)`
    set y := (basis c).repr a 1 * c.toFun (1, 1)
    have ha1 : a = inc c y := by
      apply (basis c).repr.injective
      ext σ
      rw [inc_apply, mul_assoc, Units.mul_inv, mul_one, map_smul, Module.Basis.repr_self,
        Finsupp.smul_apply, smul_eq_mul]
      by_cases hσ : σ = 1
      · simp [hσ]
      · simp [h1 σ hσ, Ne.symm hσ]
    -- commuting with `u_τ` makes `y` fixed by `τ`
    have hfix : ∀ τ : L ≃ₐ[K] L, τ y = y := fun τ => by
      have h := ha (basis c τ)
      rw [ha1, basis_mul_inc, ← smul_def, ← smul_def] at h
      simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_eq_same, mul_one] using congrArg (fun b => (basis c).repr b τ) h
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 hfix
    rw [ha1, ← hr, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ r

end Central

end CrossedProduct

end TauCeti
