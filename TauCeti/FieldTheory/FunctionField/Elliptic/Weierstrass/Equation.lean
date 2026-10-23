/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Map

/-!
# The Weierstrass equation of an elliptic function field

Let `F / k` be an algebraic function field of genus one with exact constant field, and let `P` be
a place of degree one.  Riemann–Roch gives `ℓ(nP) = n` for `n ≥ 1`, and this dimension ladder
produces the classical Weierstrass coordinates at `P`: a function `x` with pole divisor `2P`, a
function `y` with pole divisor `3P`, and a relation

`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, `aᵢ ∈ k`,

because the seven functions `1, x, y, x², xy, x³, y²` lie in the six-dimensional space `L(6P)`,
and the coefficients of `y²` and `x³` in the resulting relation are nonzero since these two are
the only functions of the seven with a pole of order six.  Since `[F : k(x)] = 2` and
`[F : k(y)] = 3` are the degrees of the pole divisors, `x` and `y` generate `F` over `k`.  This is
the first half of Stichtenoth's Proposition 6.1.2; the normal forms in each characteristic are
coordinate changes of this equation.

The relation is recorded as the affine equation of a Weierstrass curve `W` over `k`, evaluated in
`F` along the base change `W.baseChange F`, so that Mathlib's Weierstrass-curve API (variable
changes, the discriminant) applies to it.

The Weierstrass place `P` is the unique pole of `x`. Away from characteristic two,
`2y + a₁x + a₃` has pole divisor `3P`; in the normal form with `a₁ = a₃ = 0`, its orders,
principal divisor and zero divisor agree with those of `y`.

## Main definitions

* `TauCeti.Place.IsWeierstrassCoordinates`: `x` and `y` have pole divisors `2P` and `3P` and
  satisfy the Weierstrass equation of `W`.

## Main results

* `TauCeti.Place.IsWeierstrassCoordinates.finrank_adjoin_x_eq_two`,
  `TauCeti.Place.IsWeierstrassCoordinates.finrank_adjoin_y_eq_three` and
  `TauCeti.Place.IsWeierstrassCoordinates.adjoin_eq_top`: `[F : k(x)] = 2`, `[F : k(y)] = 3` and
  `F = k(x, y)`.
* `TauCeti.Place.IsWeierstrassCoordinates.map`: Weierstrass coordinates are transported along
  isomorphisms of function fields.
* `TauCeti.Place.exists_isWeierstrassCoordinates_of_genus_eq_one`: **a genus-one function field
  with exact constants has Weierstrass coordinates at every place of degree one**
  (Stichtenoth, Proposition 6.1.2).
* `TauCeti.IsEllipticFunctionField.exists_isWeierstrassCoordinates`: the same for an elliptic
  function field, at some place of degree one.

* `TauCeti.Place.IsWeierstrassCoordinates.eq_of_isWeierstrassCoordinates`: the Weierstrass
  place is unique. The lemmas `ord_two_mul_add` and `poles_two_mul_add` give order `-3` at `P`
  and pole divisor `3P` away from characteristic two; `ord_two_mul_add_eq_ord_y`,
  `principal_two_mul_add_eq_principal_y` and `zeros_two_mul_add_eq_zeros_y` identify the
  corresponding data with those of `y` in normal form.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.1.2.
-/

public section

namespace TauCeti

open AlgebraicGeometry WeierstrassCurve

open scoped _root_.IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- **Weierstrass coordinates at a place** `P` for a Weierstrass curve `W` over `k`: functions
`x` and `y` with pole divisors `2P` and `3P` satisfying the affine Weierstrass equation of `W`
in `F`. -/
structure IsWeierstrassCoordinates (P : Place k F) (W : WeierstrassCurve k) (x y : F) : Prop where
  /-- `x` has a pole of order two at `P`. -/
  ord_x : P.ord x = -2
  /-- `x` is regular away from `P`. -/
  ord_x_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x
  /-- `y` has a pole of order three at `P`. -/
  ord_y : P.ord y = -3
  /-- `y` is regular away from `P`. -/
  ord_y_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y
  /-- `(x, y)` satisfies the Weierstrass equation of `W`, read in `F`. -/
  equation : (W.baseChange F).toAffine.Equation x y

namespace IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : P.IsWeierstrassCoordinates W x y)
include h

/-- Weierstrass coordinates are nonzero: `x` has a pole. -/
theorem x_ne_zero : x ≠ 0 := fun hx ↦ by simpa [hx] using h.ord_x

/-- Weierstrass coordinates are nonzero: `y` has a pole. -/
theorem y_ne_zero : y ≠ 0 := fun hy ↦ by simpa [hy] using h.ord_y

/-- `x` is transcendental over `k`, having a pole. -/
theorem transcendental_x : Transcendental k x :=
  P.transcendental_of_ord_ne_zero (by rw [h.ord_x]; decide)

/-- `y` is transcendental over `k`, having a pole. -/
theorem transcendental_y : Transcendental k y :=
  P.transcendental_of_ord_ne_zero (by rw [h.ord_y]; decide)

/-- The pole divisor of `x` is `2P`. -/
theorem poles_x (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 x h.x_ne_zero) = (2 : ℤ) • WeilDivisor.ofPoint P :=
  Divisor.poles_eq_natCast_zsmul_ofPoint_of_ord_eq_neg hF (n := 2) h.ord_x h.ord_x_nonneg

/-- The pole divisor of `y` is `3P`. -/
theorem poles_y (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 y h.y_ne_zero) = (3 : ℤ) • WeilDivisor.ofPoint P :=
  Divisor.poles_eq_natCast_zsmul_ofPoint_of_ord_eq_neg hF (n := 3) h.ord_y h.ord_y_nonneg

/-- `[F : k(x)] = 2` at a place of degree one: the degree of the pole divisor of `x`. -/
theorem finrank_adjoin_x_eq_two (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮x⟯ F = 2 := by
  rw [finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF (n := 2) two_ne_zero h.ord_x h.ord_x_nonneg,
    hP, mul_one]

/-- `[F : k(y)] = 3` at a place of degree one: the degree of the pole divisor of `y`. -/
theorem finrank_adjoin_y_eq_three (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮y⟯ F = 3 := by
  rw [finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF (n := 3) three_ne_zero h.ord_y
    h.ord_y_nonneg, hP, mul_one]

/-- **Weierstrass coordinates generate the function field**: `F = k(x, y)`, because
`[F : k(x, y)]` divides both `[F : k(x)] = 2` and `[F : k(y)] = 3`. -/
theorem adjoin_eq_top (hF : IsFunctionField k F) (hP : P.degree = 1) : k⟮x, y⟯ = ⊤ := by
  have _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin h.transcendental_x
  have _ : FiniteDimensional k⟮y⟯ F := hF.finiteDimensional_adjoin h.transcendental_y
  have hx : k⟮x⟯ ≤ k⟮x, y⟯ :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hy : k⟮y⟯ ≤ k⟮x, y⟯ :=
    IntermediateField.adjoin.mono _ _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
  have h2 := IntermediateField.finrank_dvd_of_le_left hx
  have h3 := IntermediateField.finrank_dvd_of_le_left hy
  rw [h.finrank_adjoin_x_eq_two hF hP] at h2
  rw [h.finrank_adjoin_y_eq_three hF hP] at h3
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp
    (Nat.eq_one_of_dvd_coprimes (by decide) h2 h3)

/-- **Weierstrass coordinates are transported along isomorphisms**: if `x` and `y` are
Weierstrass coordinates at `P`, then their images under `e : F ≃ₐ[k] F'` are Weierstrass
coordinates for the same curve at the transported place `P.map e`. -/
theorem map {F' : Type*} [Field F'] [Algebra k F'] (e : F ≃ₐ[k] F') :
    (P.map e).IsWeierstrassCoordinates W (e x) (e y) where
  ord_x := by rw [ord_map_apply, h.ord_x]
  ord_x_nonneg Q hQ := by
    obtain ⟨R, rfl⟩ := (mapEquiv e).surjective Q
    rw [mapEquiv_apply, ord_map_apply]
    exact h.ord_x_nonneg R fun hR ↦ hQ (by rw [mapEquiv_apply, hR])
  ord_y := by rw [ord_map_apply, h.ord_y]
  ord_y_nonneg Q hQ := by
    obtain ⟨R, rfl⟩ := (mapEquiv e).surjective Q
    rw [mapEquiv_apply, ord_map_apply]
    exact h.ord_y_nonneg R fun hR ↦ hQ (by rw [mapEquiv_apply, hR])
  equation := h.equation.baseChange e.toAlgHom

/-- **The place of Weierstrass coordinates is unique**: `P` is the only pole of `x`, so any two
places at which `x` is the first Weierstrass coordinate are equal. -/
theorem eq_of_isWeierstrassCoordinates {P' : Place k F} {W' : WeierstrassCurve k} {y' : F}
    (h' : P'.IsWeierstrassCoordinates W' x y') : P = P' := by
  by_contra hne
  have := h.ord_x_nonneg P' (Ne.symm hne)
  rw [h'.ord_x] at this
  omega

/-- `2y + a₁x + a₃` is regular away from `P`. -/
theorem ord_two_mul_add_nonneg {Q : Place k F} (hQ : Q ≠ P) :
    0 ≤ Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) := by
  rw [← Q.mem_integers_iff_ord_nonneg]
  have hx : x ∈ Q.integers := Q.mem_integers_iff_ord_nonneg.mpr (h.ord_x_nonneg Q hQ)
  have hy : y ∈ Q.integers := Q.mem_integers_iff_ord_nonneg.mpr (h.ord_y_nonneg Q hQ)
  have hc (c : k) : algebraMap k F c ∈ Q.integers := Q.algebraMap_mem_integers c
  refine add_mem (add_mem (mul_mem ?_ hy) (mul_mem (hc _) hx)) (hc _)
  simp

/-- **`2y + a₁x + a₃` has a pole of order three at `P`** away from characteristic two: `2y` has a
pole of order three and `a₁x + a₃` has order at least `-2`. -/
theorem ord_two_mul_add (h2 : (2 : k) ≠ 0) :
    P.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) = -3 := by
  have h2F : (2 : F) = algebraMap k F 2 := (map_ofNat (algebraMap k F) 2).symm
  have h2' : (2 : F) ≠ 0 := by rwa [h2F, map_ne_zero]
  have hord2y : P.ord (2 * y) = -3 := by
    rw [P.ord_mul h2' h.y_ne_zero, h2F, P.ord_algebraMap, h.ord_y, zero_add]
  rw [add_assoc]
  set g := algebraMap k F W.a₁ * x + algebraMap k F W.a₃
  rcases eq_or_ne g 0 with hg | hg
  · rw [hg, add_zero, hord2y]
  have hg_ge : -2 ≤ P.ord g := by
    refine le_trans ?_ (P.min_ord_le_ord_add hg)
    rw [P.ord_algebraMap, le_inf_iff]
    refine ⟨?_, by decide⟩
    rcases eq_or_ne W.a₁ 0 with ha₁ | ha₁
    · simp [ha₁]
    · rw [P.ord_mul ((map_ne_zero _).mpr ha₁) h.x_ne_zero, P.ord_algebraMap, h.ord_x, zero_add]
  rw [P.ord_add_eq_min_of_ord_ne (mul_ne_zero h2' h.y_ne_zero) hg (by omega)]
  omega

section TwoNeZero

variable (hF : IsFunctionField k F) (h2 : (2 : k) ≠ 0)
include h2

/-- Away from characteristic two, `2y + a₁x + a₃` is nonzero because it has a triple pole at `P`. -/
theorem two_mul_add_ne_zero_of_two_ne_zero :
    2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃ ≠ 0 := fun h0 ↦ by
  simpa [h0] using h.ord_two_mul_add h2

/-- **The pole divisor of `2y + a₁x + a₃` is `3P`** away from characteristic two. -/
theorem poles_two_mul_add :
    Divisor.poles hF
        (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
          (h.two_mul_add_ne_zero_of_two_ne_zero h2)) =
      (3 : ℤ) • WeilDivisor.ofPoint P :=
  Divisor.poles_eq_natCast_zsmul_ofPoint_of_ord_eq_neg hF (n := 3)
    (h.ord_two_mul_add h2) (fun _ ↦ h.ord_two_mul_add_nonneg)

section CharNeTwoNF

variable [W.IsCharNeTwoNF]

/-- In the characteristic-not-two normal form `y² = x³ + a₂x² + a₄x + a₆`, the partial derivative
`2y + a₁x + a₃` has the same order as `y` at every place. -/
theorem ord_two_mul_add_eq_ord_y (Q : Place k F) :
    Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) = Q.ord y := by
  have h2F : (2 : F) = algebraMap k F 2 := (map_ofNat (algebraMap k F) 2).symm
  have h2' : (2 : F) ≠ 0 := by rwa [h2F, map_ne_zero]
  rw [W.a₁_of_isCharNeTwoNF, W.a₃_of_isCharNeTwoNF, map_zero, zero_mul, add_zero, add_zero,
    Q.ord_mul h2' h.y_ne_zero, h2F, Q.ord_algebraMap, zero_add]

/-- In the characteristic-not-two normal form, `2y + a₁x + a₃` and `y` have the same principal
divisor. -/
theorem principal_two_mul_add_eq_principal_y :
    Divisor.principal hF
        (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
          (h.two_mul_add_ne_zero_of_two_ne_zero h2)) =
      Divisor.principal hF (Units.mk0 y h.y_ne_zero) := by
  ext Q
  rw [Divisor.coeff_principal, Divisor.coeff_principal, Units.val_mk0, Units.val_mk0,
    h.ord_two_mul_add_eq_ord_y h2 Q]

/-- In the characteristic-not-two normal form, `2y + a₁x + a₃` and `y` have the same zero
divisor. -/
theorem zeros_two_mul_add_eq_zeros_y :
    Divisor.zeros hF
        (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
          (h.two_mul_add_ne_zero_of_two_ne_zero h2)) =
      Divisor.zeros hF (Units.mk0 y h.y_ne_zero) := by
  ext Q
  rw [Divisor.coeff_zeros, Divisor.coeff_zeros, Units.val_mk0, Units.val_mk0,
    h.ord_two_mul_add_eq_ord_y h2 Q]

end CharNeTwoNF

end TwoNeZero

end IsWeierstrassCoordinates

/-- **The relation in `L(6P)`**: for `x` and `y` with pole divisors `2P` and `3P` at a place `P` of
degree one on a genus-one function field, `y²` is a `k`-linear combination of the six monomials
`1, x, y, x², xy, x³`, and the coefficient of `x³` is nonzero. -/
private theorem exists_sq_eq_sum_smul_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1)
    {x y : F} (hx0 : x ≠ 0) (hxP : P.ord x = -2) (hxQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x)
    (hy0 : y ≠ 0) (hyP : P.ord y = -3) (hyQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y) :
    ∃ c : Fin 6 → k, c 5 ≠ 0 ∧ ∑ i, c i • ![1, x, y, x ^ 2, x * y, x ^ 3] i = y ^ 2 := by
  classical
  -- The six monomials lie in `L(6P)`, the first five in `L(5P)`, with distinct orders at `P`.
  set v : Fin 6 → F := ![1, x, y, x ^ 2, x * y, x ^ 3] with hv
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hv, hx0, hy0]
  have hvP : ∀ i, P.ord (v i) = ![0, -2, -3, -4, -5, -6] i := by
    intro i
    fin_cases i <;> simp [hv, P.ord_mul hx0 hy0, P.ord_pow, hxP, hyP]
  have hvQ : ∀ Q : Place k F, Q ≠ P → ∀ i, 0 ≤ Q.ord (v i) := by
    intro Q hQ i
    have hx := hxQ Q hQ
    have hy := hyQ Q hQ
    fin_cases i <;> simp [hv, Q.ord_mul hx0 hy0, Q.ord_pow] <;> omega
  have hmem : ∀ i, v i ∈ riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) := fun i ↦
    (mem_riemannRochSpace_zsmul_ofPoint_iff (hv0 i)).mpr
      ⟨by rw [hvP i]; fin_cases i <;> simp, fun Q hQ ↦ hvQ Q hQ i⟩
  have hmem5 : ∀ i, i ≠ 5 → v i ∈ riemannRochSpace ((5 : ℤ) • WeilDivisor.ofPoint P) :=
    fun i hi ↦ (mem_riemannRochSpace_zsmul_ofPoint_iff (hv0 i)).mpr
      ⟨by rw [hvP i]; fin_cases i <;> simp_all, fun Q hQ ↦ hvQ Q hQ i⟩
  -- Being linearly independent in the six-dimensional `L(6P)`, the monomials span it.
  have hdim : Module.finrank k (riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P)) = 6 := by
    have := Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one hF hex hg (P := P) (n := 6)
      (by norm_num)
    rw [hP, mul_one] at this
    simpa [Divisor.dim_def] using this
  have hli : LinearIndependent k v :=
    P.linearIndependent_of_injective_ord hv0 (by rw [funext hvP]; decide)
  set v' : Fin 6 → riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) := fun i ↦ ⟨v i, hmem i⟩
    with hv'
  have hli' : LinearIndependent k v' :=
    LinearIndependent.of_comp (riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P)).subtype hli
  have _ := finiteDimensional_riemannRochSpace hF ((6 : ℤ) • WeilDivisor.ofPoint P)
  have hspan : Submodule.span k (Set.range v') = ⊤ :=
    hli'.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  -- Hence `y²`, which also lies in `L(6P)`, is a linear combination of the six monomials.
  have hy2 : y ^ 2 ∈ riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) :=
    (mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero 2 hy0)).mpr
      ⟨by rw [P.ord_pow, hyP]; norm_num, fun Q hQ ↦ by
        rw [Q.ord_pow]
        have := hyQ Q hQ
        omega⟩
  have hy2' : (⟨y ^ 2, hy2⟩ : riemannRochSpace _) ∈ Submodule.span k (Set.range v') :=
    hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy2'
  have hrel : ∑ i, c i • v i = y ^ 2 := by
    have := congrArg Subtype.val hc
    simpa [hv'] using this
  -- The coefficient of `x³` is nonzero: otherwise `y²` would lie in `L(5P)`.
  refine ⟨c, fun h5 ↦ ?_, hrel⟩
  have hmem' : y ^ 2 ∈ riemannRochSpace ((5 : ℤ) • WeilDivisor.ofPoint P) := by
    rw [← hrel, ← Finset.sum_erase Finset.univ (a := 5) (by simp [h5])]
    exact Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (hmem5 i (Finset.ne_of_mem_erase hi))
  have := ((mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero 2 hy0)).mp hmem').1
  rw [P.ord_pow, hyP] at this
  norm_num at this

/-- **The Weierstrass equation of a genus-one function field** (Stichtenoth, Proposition 6.1.2):
over an exact constant field, at every place `P` of degree one there are functions `x` and `y`
with pole divisors `2P` and `3P` satisfying the affine equation of a Weierstrass curve over `k`.
By `TauCeti.Place.IsWeierstrassCoordinates.adjoin_eq_top`, they generate `F` over `k`. -/
theorem exists_isWeierstrassCoordinates_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), P.IsWeierstrassCoordinates W x y := by
  -- Functions with pole divisors `2P` and `3P`, from `ℓ(nP) = n`.
  obtain ⟨x, hx0, hxP, hxQ⟩ :=
    P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex (n := 2) (by omega)
  obtain ⟨y, hy0, hyP, hyQ⟩ :=
    P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex (n := 3) (by omega)
  have hxP' : P.ord x = -2 := by simpa using hxP
  have hyP' : P.ord y = -3 := by simpa using hyP
  -- The relation `y² = c₀ + c₁x + c₂y + c₃x² + c₄xy + c₅x³` in `L(6P)`, with `c₅ ≠ 0`.
  obtain ⟨c, hc5, hrel⟩ :=
    exists_sq_eq_sum_smul_of_genus_eq_one hF hex hg hP hx0 hxP' hxQ hy0 hyP' hyQ
  simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Algebra.smul_def, mul_one] at hrel
  -- Rescale `x` and `y` by `c₅` to make `y²` and `x³` monic.
  have hc5' : algebraMap k F (c 5) ≠ 0 := (map_ne_zero _).mpr hc5
  refine ⟨⟨-c 4, c 3, -(c 5 * c 2), c 5 * c 1, c 5 ^ 2 * c 0⟩, algebraMap k F (c 5) * x,
    algebraMap k F (c 5) * y, ?_, fun Q hQ ↦ ?_, ?_, fun Q hQ ↦ ?_, ?_⟩
  · rw [P.ord_mul hc5' hx0, P.ord_algebraMap, hxP', zero_add]
  · rw [Q.ord_mul hc5' hx0, Q.ord_algebraMap, zero_add]
    exact hxQ Q hQ
  · rw [P.ord_mul hc5' hy0, P.ord_algebraMap, hyP', zero_add]
  · rw [Q.ord_mul hc5' hy0, Q.ord_algebraMap, zero_add]
    exact hyQ Q hQ
  · rw [Affine.equation_iff]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_neg, map_mul, map_pow]
    linear_combination -(algebraMap k F (c 5)) ^ 2 * hrel

end Place

/-- **The Weierstrass equation of an elliptic function field** (Stichtenoth,
Proposition 6.1.2): over an exact constant field, an elliptic function field has a place `P` of
degree one and Weierstrass coordinates at `P`. -/
theorem IsEllipticFunctionField.exists_isWeierstrassCoordinates (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F) :
    ∃ (P : Place k F) (W : WeierstrassCurve k) (x y : F),
      P.degree = 1 ∧ P.IsWeierstrassCoordinates W x y := by
  obtain ⟨P, hP⟩ := he.exists_place_degree_eq_one hF hex
  obtain ⟨W, x, y, h⟩ :=
    P.exists_isWeierstrassCoordinates_of_genus_eq_one hF hex he.genus_eq_one hP
  exact ⟨P, W, x, y, hP, h⟩

end TauCeti

end
