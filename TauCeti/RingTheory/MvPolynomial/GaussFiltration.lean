/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Gauss filtrations of polynomial rings with real weights

For a ring element `w` the `w`-adic filtration of a commutative ring `R` is the family, indexed
by `t ∈ ℝ`, of the additive subgroups `{x | w ^ ⌈t⌉₊ ∣ x}`, where `⌈t⌉₊` is the ceiling truncated
at `0`. It is decreasing and multiplicative. Given such a filtration `F` of `R` and real weights
`c` of the variables, the *Gauss filtration* of `MvPolynomial σ R` at level `t` consists of the
polynomials whose coefficient at each monomial `X ^ α` lies in `F (t - c · α)`, where `c · α` is
the weight `Finsupp.weight c α`: each term has order plus weight at least `t`. For the `w`-adic
filtration this is the Gauss valuation with weights of the variables, read as a filtration.

## Main definitions

* `TauCeti.adicFiltration w t`: the elements divisible by `w ^ ⌈t⌉₊`.
* `TauCeti.gaussFiltration F c t`: the polynomials whose coefficient at `X ^ α` lies in
  `F (t - c · α)`.

## Main results

* `TauCeti.adicFiltration.gradedMonoid`, `TauCeti.gaussFiltration.gradedMonoid`: both filtrations
  are multiplicative, as `SetLike.GradedMonoid` instances; `TauCeti.antitone_adicFiltration` and
  `TauCeti.antitone_gaussFiltration` say that they decrease.
* `TauCeti.algHom_sub_mem_of_mem_gaussFiltration`: substitutions respect weights. If `χ` sends
  each variable `X i` to level `c i` of a multiplicative filtration `G` of an algebra, and
  `ψ X i - χ X i` lies a little higher, at level `c i + 1 / 20`, then `ψ` sends level `t` of the
  Gauss filtration to level `t` of `G`, and `ψ f - χ f` lies in level `t + 1 / 20`.

The definitions and results are adapted from `New.adicFiltration`, `New.gaussFiltration` and
`New.algHom_sub_mem_of_mem_gaussFiltration` in the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

@[expose] public section

namespace TauCeti

open MvPolynomial Finsupp SetLike Nat

section Filtration

variable {σ : Type*} {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- For a ring element `w` and real `t`, the additive subgroup of elements divisible by `w` to the
power `⌈t⌉₊ = max(⌈t⌉, 0)`. -/
def adicFiltration (w : R) (t : ℝ) : AddSubgroup R where
  carrier := {x : R | w ^ ⌈t⌉₊ ∣ x}
  add_mem' := Dvd.dvd.add
  zero_mem' := by simp
  neg_mem' := by simp

@[simp]
theorem mem_adicFiltration_iff {w : R} {t : ℝ} {x : R} :
    x ∈ adicFiltration w t ↔ w ^ ⌈t⌉₊ ∣ x :=
  Iff.rfl

/-- The `w`-adic filtration is multiplicative. -/
instance adicFiltration.gradedMonoid (w : R) : SetLike.GradedMonoid (adicFiltration w) where
  one_mem := by simp
  mul_mem s t x y hx hy :=
    calc w ^ ⌈s + t⌉₊ ∣ w ^ (⌈s⌉₊ + ⌈t⌉₊) := pow_dvd_pow w (ceil_add_le s t)
      _ ∣ x * y := by simpa [pow_add] using mul_dvd_mul hx hy

/-- The `w`-adic filtration is decreasing. -/
theorem antitone_adicFiltration (w : R) : Antitone (adicFiltration w) :=
  fun _ _ hst _ hx ↦ (pow_dvd_pow w (ceil_mono hst)).trans hx

/-- An element lies in the level `t ≤ 0` of the `w`-adic filtration; more generally, it suffices
that `t ≤ 0` when the element is non-zero. -/
theorem mem_adicFiltration_of_nonpos {w x : R} {t : ℝ} (h_nonpos : x ≠ 0 → t ≤ 0) :
    x ∈ adicFiltration w t := by
  by_cases hx : x = 0 <;> simp_all [ceil_eq_zero.2]

/-- The Gauss filtration: for additive subgroups `F t` of `R` and real weights `c` of the
variables, the additive group of polynomials whose coefficient at each `X ^ α` lies in
`F (t - c · α)`. -/
def gaussFiltration (F : ℝ → AddSubgroup R) (c : σ → ℝ) (t : ℝ) :
    AddSubgroup (MvPolynomial σ R) where
  carrier := {f : MvPolynomial σ R | ∀ α : σ →₀ ℕ, f.coeff α ∈ F (t - weight c α)}
  add_mem' hf hg α := by simpa using add_mem (hf α) (hg α)
  zero_mem' := by simp
  neg_mem' := by simp

variable {F : ℝ → AddSubgroup R} {c : σ → ℝ} {t : ℝ}

theorem mem_gaussFiltration_iff {f : MvPolynomial σ R} :
    f ∈ gaussFiltration F c t ↔ ∀ α : σ →₀ ℕ, f.coeff α ∈ F (t - weight c α) :=
  Iff.rfl

/-- The term `x X ^ α` lies in level `t` of the Gauss filtration if `x` lies in `F (t - c · α)`. -/
theorem monomial_mem_gaussFiltration {α : σ →₀ ℕ} {x : R} (hx : x ∈ F (t - weight c α)) :
    monomial α x ∈ gaussFiltration F c t := by
  classical
  intro β
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ hx
  · exact zero_mem _

theorem C_mem_gaussFiltration {x : R} (hx : x ∈ F t) :
    (C x : MvPolynomial σ R) ∈ gaussFiltration F c t :=
  monomial_mem_gaussFiltration (by simpa)

/-- The Gauss filtration of a multiplicative filtration is multiplicative. -/
instance gaussFiltration.gradedMonoid [SetLike.GradedMonoid F] :
    SetLike.GradedMonoid (gaussFiltration F c) where
  one_mem := monomial_mem_gaussFiltration (by simpa using one_mem_graded F)
  mul_mem s t f g hf hg α := by
    classical
    -- The coefficient at `α` is a sum of products of coefficients at `β`, `γ` with `β + γ = α`.
    rw [coeff_mul]
    refine sum_mem fun (β, γ) hβγ ↦ ?_
    obtain rfl : β + γ = α := by simpa using hβγ
    simpa [add_sub_add_comm] using mul_mem_graded (hf β) (hg γ)

/-- The Gauss filtration of a decreasing filtration is decreasing. -/
theorem antitone_gaussFiltration (hF : Antitone F) : Antitone (gaussFiltration F c) :=
  fun _ _ hst _ hf α ↦ hF (sub_le_sub_right hst _) (hf α)

/-- **Substitutions respect weights.** Let `G` be a decreasing multiplicative filtration of the
`R`-algebra `A` such that the algebra map sends `F s` into `G s`, and let `f` lie in level `t` of
the Gauss filtration for `F` and the weights `c` of the variables. Let `χ`, `ψ` be substitutions
with `χ X i` in `G (c i)` and `ψ X i - χ X i` in `G (c i + 1 / 20)`. Then `ψ f` lies in `G t` and
`ψ f - χ f` in `G (t + 1 / 20)`. -/
theorem algHom_sub_mem_of_mem_gaussFiltration (χ : MvPolynomial σ R →ₐ[R] A)
    (G : ℝ → AddSubgroup A) [SetLike.GradedMonoid G] (hG : Antitone G)
    {f : MvPolynomial σ R} (hf : f ∈ gaussFiltration F c t)
    (hχ : ∀ i : σ, χ (X i) ∈ G (c i)) (ψ : MvPolynomial σ R →ₐ[R] A)
    (hψ : ∀ i : σ, ψ (X i) - χ (X i) ∈ G (c i + 20⁻¹))
    (hF : ∀ {s : ℝ} {x : R}, x ∈ F s → algebraMap R A x ∈ G s) :
    ψ f ∈ G t ∧ ψ f - χ f ∈ G (t + 20⁻¹) := by
  classical
  -- Induction on `f`: degrees in the filtration add in products, so a gain of `1 / 20` on one
  -- factor is a gain of `1 / 20` on the product.
  induction f using induction_on'' generalizing t with
  | C x => simpa using hF (hf 0)
  | monomial_add α x f hα _ ih_f ih_monomial =>
    -- both summands lie in `gaussFiltration F c t`, since `α` is not in the support of `f`
    have h_monomial : monomial α x ∈ gaussFiltration F c t :=
      monomial_mem_gaussFiltration (by simpa [f.notMem_support_iff.1 hα] using hf α)
    have h_rest : f ∈ gaussFiltration F c t := (add_mem_cancel_left h_monomial).1 hf
    simpa [add_sub_add_comm, add_mem (ih_monomial h_monomial).1 (ih_f h_rest).1] using
      add_mem (ih_monomial h_monomial).2 (ih_f h_rest).2
  | mul_X p i ih =>
    have hp : p ∈ gaussFiltration F c (t - c i) := fun α ↦ by
      have h_level : t - c i - weight c α = t - weight c (α + .single i 1) := by
        simp [weight_single, sub_add_eq_sub_sub_swap]
      rw [h_level, ← coeff_mul_X α i p]
      exact hf _
    obtain ⟨hψp, h_diff⟩ : ψ p ∈ G (t - c i) ∧ ψ p - χ p ∈ G (t - c i + 20⁻¹) := ih hp
    have hψX : ψ (X i) ∈ G (c i) := by simpa using add_mem (hχ i) (hG (by simp) (hψ i))
    refine ⟨by simpa using mul_mem_graded hψp hψX, ?_⟩
    rw [show ψ (p * X i) - χ (p * X i) =
      (ψ p - χ p) * χ (X i) + ψ p * (ψ (X i) - χ (X i)) by simp [sub_mul, mul_sub]]
    exact add_mem (by simpa [add_right_comm] using mul_mem_graded h_diff (hχ i))
      (by simpa [← add_assoc] using mul_mem_graded hψp (hψ i))

end Filtration

end TauCeti
