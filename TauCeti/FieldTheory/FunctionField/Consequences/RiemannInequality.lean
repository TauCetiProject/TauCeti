/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Conorm

/-!
# Upper bounds for the genus, and Riemann's inequality

Let `F / k` be an algebraic function field with exact constant field `k`, and let `F₀ ⊆ F` be a
subfield containing `k` over which `F` is finite, of degree `n`.  If a basis `z₁, …, zₙ` of
`F / F₀` lies in the Riemann–Roch space `L(C)` of a divisor `C` of `F`, then

`g(F) ≤ 1 + n (g(F₀) - 1) + deg C`.

The proof counts sections.  For a divisor `A` of `F₀`, the products `u zᵢ` of a `k`-basis `u` of
`L(A)` with the `zᵢ` are `k`-linearly independent, because the `zᵢ` are linearly independent over
`F₀`; and they lie in `L(Con A + C)`.  Hence `n ℓ(A) ≤ ℓ(Con A + C)`.  The conorm multiplies
degrees by `n`, Riemann's theorem bounds `ℓ(A)` below by `deg A + 1 - g(F₀)`, and Riemann–Roch
evaluates `ℓ(Con A + C)` as `n deg A + deg C + 1 - g(F)` once `deg A` is large; comparing the two
gives the bound.  The section count is the case `k' = k` of
`TauCeti.Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add` in
`TauCeti.FieldTheory.FunctionField.RiemannRoch.Conorm`.

For `F₀ = k(x)` and `F = k(x, y)`, the powers `1, y, …, y^{m - 1}` with `m = [F : k(x)]` form a
basis of `F / k(x)` lying in `L((m - 1) (y)_∞)`, a divisor of degree `(m - 1) [F : k(y)]`.  Since
`k(x)` has genus zero, this is **Riemann's inequality**

`g(F) ≤ ([F : k(x)] - 1) ([F : k(y)] - 1)`.

Neither statement needs `k` to be perfect or the extensions to be separable: only the constant
field of `F` has to be exact, which is what makes Riemann–Roch an equality in large degree.  The
subfield `F₀` need not have exact constants, since only Riemann's lower bound `ℓ(A) ≥
deg A + 1 - g(F₀)` is used there.

## Main results

* `TauCeti.genus_le_one_add_finrank_mul_genus_sub_one_add_degree`:
  `g(F) ≤ 1 + [F : F₀] (g(F₀) - 1) + deg C` for a basis of `F / F₀` in `L(C)`.
* `TauCeti.genus_le_finrank_sub_one_mul_finrank_sub_one`: **Riemann's inequality**
  `g ≤ ([F : k(x)] - 1) ([F : k(y)] - 1)` for `F = k(x, y)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.11, Corollary 3.11.4.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F₀ F : Type*} [Field k] [Field F₀] [Field F]
variable [Algebra k F₀] [Algebra k F] [Algebra F₀ F] [IsScalarTower k F₀ F]
variable [FiniteDimensional F₀ F]

/-- **An upper bound for the genus from a subfield**: if `F / k` has exact constants, `F₀` is a
subfield over which `F` is finite, and a basis of `F / F₀` lies in `L(C)`, then
`g(F) ≤ 1 + [F : F₀] (g(F₀) - 1) + deg C`.

No hypothesis is placed on the constants of `F₀`: only Riemann's lower bound for `ℓ` on `F₀`
enters. -/
theorem genus_le_one_add_finrank_mul_genus_sub_one_add_degree (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ι : Type*} (b : Module.Basis ι F₀ F)
    {C : Divisor k F} (hb : ∀ i, b i ∈ riemannRochSpace C) :
    (genus k F : ℤ) ≤
      1 + Module.finrank F₀ F * ((genus k F₀ : ℤ) - 1) + Divisor.degree C := by
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι
  have : Algebra.IsAlgebraic F₀ F := Algebra.IsAlgebraic.of_finite F₀ F
  have hF₀ : IsFunctionField k F₀ := hF.of_isAlgebraic_top
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hF hex
  obtain ⟨P⟩ := Place.nonempty hF₀
  -- A divisor `A = N P` of `F₀` whose conorm, plus `C`, is in the range of Riemann–Roch.
  set A : Divisor k F₀ := Finsupp.single P ((c - Divisor.degree C).toNat : ℤ)
  have hP : (1 : ℤ) ≤ P.degree := by exact_mod_cast P.one_le_degree_of_isFunctionField hF₀
  have hn : (1 : ℤ) ≤ Module.finrank F₀ F := by exact_mod_cast Module.finrank_pos
  have hdegA : c - Divisor.degree C ≤ Divisor.degree A := by
    rw [Divisor.degree_single]
    nlinarith [Int.self_le_toNat (c - Divisor.degree C)]
  have hdegCon : Divisor.degree (Divisor.conorm k F A) =
      Module.finrank F₀ F * Divisor.degree A :=
    Divisor.degree_conorm_of_finrank_eq_one k F hF₀ (Module.finrank_self k) A
  have hA0 : 0 ≤ Divisor.degree A := by
    rw [Divisor.degree_single]
    positivity
  have hRR := hc (Divisor.conorm k F A + C) (by
    rw [Divisor.degree_add, hdegCon]
    nlinarith)
  have hcount : (Module.finrank F₀ F : ℤ) * Divisor.dim A ≤
      Divisor.dim (Divisor.conorm k F A + C) := by
    have h := Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add hF b.linearIndependent hb A
    rw [← Module.finrank_eq_card_basis b, Module.finrank_self, one_mul] at h
    exact_mod_cast h
  have hRiemann := Divisor.degree_add_one_sub_genus_le_dim hF₀ A
  rw [hRR, Divisor.degree_add, hdegCon] at hcount
  nlinarith

/-- **Riemann's inequality** (Stichtenoth, Corollary 3.11.4): if `F / k` has exact constants and
is generated by two transcendental elements `x` and `y`, then
`g ≤ ([F : k(x)] - 1) ([F : k(y)] - 1)`.

The powers `1, y, …, y^{m - 1}`, `m = [F : k(x)]`, are a basis of `F / k(x)` in
`L((m - 1) (y)_∞)`, so this is the case `F₀ = k(x)` of
`TauCeti.genus_le_one_add_finrank_mul_genus_sub_one_add_degree`. -/
theorem genus_le_finrank_sub_one_mul_finrank_sub_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x y : F} (hx : Transcendental k x)
    (hy : Transcendental k y) (hxy : k⟮x, y⟯ = ⊤) :
    genus k F ≤ (Module.finrank k⟮x⟯ F - 1) * (Module.finrank k⟮y⟯ F - 1) := by
  have := hF.finiteDimensional_adjoin hx
  have := hF.finiteDimensional_adjoin hy
  have hy0 : y ≠ 0 := by rintro rfl; exact hy isAlgebraic_zero
  -- `y` generates `F` over `k(x)`, so its powers below `m = [F : k(x)]` form a basis.
  have htop : k⟮x⟯⟮y⟯ = ⊤ := IntermediateField.restrictScalars_injective k <| by
    rw [IntermediateField.adjoin_simple_adjoin_simple, hxy, IntermediateField.restrictScalars_top]
  have hm : (minpoly k⟮x⟯ y).natDegree = Module.finrank k⟮x⟯ F := by
    rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite k⟮x⟯ y), htop,
      IntermediateField.finrank_top']
  set m := Module.finrank k⟮x⟯ F
  set n := Module.finrank k⟮y⟯ F
  have hm1 : 1 ≤ m := Module.finrank_pos
  have hn1 : 1 ≤ n := Module.finrank_pos
  let b : Module.Basis (Fin (minpoly k⟮x⟯ y).natDegree) k⟮x⟯ F :=
    basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_pow y)
      (by rw [Fintype.card_fin]; exact hm)
  set C : Divisor k F := ((m : ℤ) - 1) • Divisor.poles hF (Units.mk0 y hy0)
  have hb : ∀ i, b i ∈ riemannRochSpace C := fun i ↦ by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    exact pow_mem_riemannRochSpace_zsmul_poles_of_le hF (Units.mk0 y hy0)
      (by have := i.isLt; omega)
  have hdegC : Divisor.degree C = ((m : ℤ) - 1) * n := by
    rw [map_zsmul, Divisor.degree_poles hF (Units.mk0 y hy0) hy, smul_eq_mul, Units.val_mk0]
  have h := genus_le_one_add_finrank_mul_genus_sub_one_add_degree hF hex b hb
  rw [genus_adjoin_simple_eq_zero hx, hdegC, Nat.cast_zero] at h
  have h' : (genus k F : ℤ) ≤ ((m - 1 : ℕ) : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    push_cast [hm1, hn1]
    linarith
  exact_mod_cast h'

end TauCeti
