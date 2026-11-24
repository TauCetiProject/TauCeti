/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# The gonality of an algebraic function field

The *gonality* of a field extension `F / k` is the least degree `[F : k(x)]` of `F` over a
rational subfield `k(x)`, for `x ∈ F` transcendental over `k`. For an algebraic function field
of one variable it is the least degree of a nonconstant map from the curve to the projective
line, and it is the first invariant after the genus that a curve's arithmetic is read from.

The definition `TauCeti.gonality` is a plain infimum of field degrees and makes sense for every
extension. For a function field the infimum is attained by some transcendental `x` and is
positive.

Over an exact constant field the gonality has an intrinsic description by divisors, the *pencil
description*: it is the least degree of a divisor `D` with `ℓ(D) ≥ 2`. One inequality is the pole
divisor `(x)_∞`, of degree `[F : k(x)]`, whose Riemann–Roch space contains `1` and `x`. For the
other, move `D` inside its linear equivalence class to an effective divisor and take a
transcendental `x ∈ L(D)`; the poles of `x` are bounded by `D`, so `[F : k(x)] = deg (x)_∞ ≤ deg D`.
A divisor of least degree in the pencil description has no base points: `ℓ(D - P) < ℓ(D)` for
every place `P`.

The pencil description turns Riemann–Roch into upper bounds. A divisor of degree one bounds the
gonality by `g + 1`, a canonical divisor bounds it by `2g - 2` in genus at least two, and a field
of genus two has gonality exactly two. Gonality one characterizes rational function fields.

## Main definitions

* `TauCeti.gonality`: the least degree of `F` over a rational subfield.

## Main results

* `TauCeti.gonality_le_finrank_adjoin`, `TauCeti.exists_finrank_adjoin_eq_gonality`,
  `TauCeti.gonality_pos`: every transcendental element bounds the gonality, and for a function
  field some transcendental element attains it, which is then positive.
* `AlgEquiv.gonality_eq`: isomorphic extensions have the same gonality.
* `TauCeti.gonality_eq_sInf_degree`: **the pencil description** of the gonality.
* `TauCeti.Divisor.dim_sub_ofPoint_lt_of_degree_eq_gonality`: a divisor of least degree with
  `ℓ ≥ 2` is base-point-free.
* `TauCeti.gonality_le_mul_degree_of_isPoleNumber`: a pole number `n ≠ 0` at a place `P`
  bounds the gonality by `n · deg P`.
* `TauCeti.gonality_eq_one_iff`: gonality one means `F ≃ₐ[k] k(t)`.
* `TauCeti.gonality_eq_two_iff`: for a non-rational field, gonality two means a rational subfield
  of index two.
* `TauCeti.gonality_le_genus_add_one`, `TauCeti.gonality_le_two_mul_genus_sub_two`,
  `TauCeti.gonality_of_genus_eq_two`: the elementary bounds from Riemann–Roch.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.4.11 and Lemma 6.2.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The **gonality** of `F / k`: the least degree `[F : k(x)]` of `F` over a rational subfield
`k(x)`, for `x` transcendental over `k`.

For an algebraic function field this is the least degree of a nonconstant map from the curve to
the projective line over `k`; it is attained and positive (`TauCeti.gonality_pos`). Outside that
setting it can be zero: when no element is transcendental the infimum is over the empty set, and
when `F` has transcendence degree two every degree `[F : k(x)]` is the junk value zero. -/
noncomputable def gonality (k F : Type*) [Field k] [Field F] [Algebra k F] : ℕ :=
  sInf {n : ℕ | ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = n}

/-! ### The infimum and its attainment -/

/-- Every transcendental element bounds the gonality by its index `[F : k(x)]`. -/
theorem gonality_le_finrank_adjoin {x : F} (hx : Transcendental k x) :
    gonality k F ≤ Module.finrank k⟮x⟯ F :=
  Nat.sInf_le ⟨x, hx, rfl⟩

/-- **The gonality of a function field is attained**: some transcendental `x` has
`[F : k(x)] = gonality k F`. -/
theorem exists_finrank_adjoin_eq_gonality (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = gonality k F := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  exact Nat.sInf_mem (s := {n : ℕ | ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = n})
    ⟨_, x, hx, rfl⟩

/-- The gonality of a function field is a lower bound for every index `[F : k(x)]`, and it is the
largest one. -/
theorem le_gonality_iff (hF : IsFunctionField k F) {n : ℕ} :
    n ≤ gonality k F ↔ ∀ x : F, Transcendental k x → n ≤ Module.finrank k⟮x⟯ F := by
  refine ⟨fun h x hx ↦ h.trans (gonality_le_finrank_adjoin hx), fun h ↦ ?_⟩
  obtain ⟨x, hx, hrank⟩ := exists_finrank_adjoin_eq_gonality hF
  exact hrank ▸ h x hx

/-- **The gonality of a function field is positive.** -/
theorem gonality_pos (hF : IsFunctionField k F) : 0 < gonality k F := by
  obtain ⟨x, hx, hrank⟩ := exists_finrank_adjoin_eq_gonality hF
  have := hF.finiteDimensional_adjoin hx
  exact hrank ▸ Module.finrank_pos

/-- An isomorphism over `k` carries rational subfields to rational subfields of the same index,
so **isomorphic extensions have the same gonality**. -/
theorem _root_.AlgEquiv.gonality_eq {F' : Type*} [Field F'] [Algebra k F'] (e : F ≃ₐ[k] F') :
    gonality k F = gonality k F' := by
  have htr (x : F) : Transcendental k (e x) ↔ Transcendental k x :=
    not_congr (isAlgebraic_algHom_iff e.toAlgHom e.injective)
  have hrank := e.finrank_adjoin_apply
  have hset : {n : ℕ | ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = n} =
      {n : ℕ | ∃ y : F', Transcendental k y ∧ Module.finrank k⟮y⟯ F' = n} := by
    ext n
    refine ⟨fun ⟨x, hx, hn⟩ ↦ ⟨e x, (htr x).mpr hx, (hrank x).trans hn⟩, fun ⟨y, hy, hn⟩ ↦ ?_⟩
    refine ⟨e.symm y, (htr _).mp (by rwa [e.apply_symm_apply]), (hrank _).symm.trans ?_⟩
    rwa [e.apply_symm_apply]
  rw [gonality, gonality, hset]

/-! ### The pencil description -/

/-- Over an exact constant field, **the gonality is at most the degree of every divisor with
`ℓ(D) ≥ 2`**. -/
theorem gonality_le_degree (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hdim : 2 ≤ Divisor.dim D) : (gonality k F : ℤ) ≤ Divisor.degree D := by
  obtain ⟨x, hx, hle⟩ := exists_transcendental_finrank_adjoin_le_degree_of_two_le_dim hF hex hdim
  exact (Int.ofNat_le.mpr (gonality_le_finrank_adjoin hx)).trans hle

/-- **The gonality is the degree of an effective divisor with `ℓ ≥ 2`**: the pole divisor of an
element attaining the gonality. No exactness of the constant field is needed. -/
theorem exists_nonneg_and_degree_eq_gonality_and_two_le_dim (hF : IsFunctionField k F) :
    ∃ D : Divisor k F, 0 ≤ D ∧ Divisor.degree D = gonality k F ∧ 2 ≤ Divisor.dim D := by
  obtain ⟨x, hx, hrank⟩ := exists_finrank_adjoin_eq_gonality hF
  exact hrank ▸ exists_nonneg_and_degree_eq_finrank_and_two_le_dim hF hx

/-- **The pencil description of the gonality** (Poonen, Appendix A): over an exact constant
field, the gonality is the least degree of a divisor whose Riemann–Roch space has dimension at
least two. -/
theorem gonality_eq_sInf_degree (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    gonality k F =
      sInf {n : ℕ | ∃ D : Divisor k F, Divisor.degree D = n ∧ 2 ≤ Divisor.dim D} := by
  obtain ⟨D, -, hD, hdim⟩ := exists_nonneg_and_degree_eq_gonality_and_two_le_dim hF
  refine le_antisymm (le_csInf ⟨_, D, hD, hdim⟩ ?_) (Nat.sInf_le ⟨D, hD, hdim⟩)
  rintro n ⟨E, hE, hEdim⟩
  exact_mod_cast hE ▸ gonality_le_degree hF hex hEdim

/-- Over an exact constant field, a divisor of degree less than the gonality has `ℓ ≤ 1`. -/
theorem Divisor.dim_le_one_of_degree_lt_gonality (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {D : Divisor k F}
    (hD : Divisor.degree D < gonality k F) : Divisor.dim D ≤ 1 := by
  by_contra! h
  have := gonality_le_degree hF hex h
  omega

/-- **A divisor of least degree with `ℓ ≥ 2` is base-point-free**: over an exact constant field,
if `deg D` is the gonality and `ℓ(D) ≥ 2`, then `ℓ(D - P) < ℓ(D)` for every place `P`. -/
theorem Divisor.dim_sub_ofPoint_lt_of_degree_eq_gonality (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {D : Divisor k F} (hD : Divisor.degree D = gonality k F)
    (hdim : 2 ≤ Divisor.dim D) (P : Place k F) :
    Divisor.dim (D - WeilDivisor.ofPoint P) < Divisor.dim D := by
  have hP := P.one_le_degree_of_isFunctionField hF
  have := Divisor.dim_le_one_of_degree_lt_gonality hF hex (D := D - WeilDivisor.ofPoint P)
    (by simp only [Divisor.degree_sub, Divisor.degree_ofPoint]; omega)
  omega

/-- **A positive pole number bounds the gonality**: if some function has a pole of order `n ≠ 0`
at `P` and no other pole, then the gonality is at most `n · deg P`. At a rational place the
bound is `n` itself. No exactness of the constant field is needed. -/
theorem gonality_le_mul_degree_of_isPoleNumber (hF : IsFunctionField k F) {P : Place k F}
    {n : ℕ} (hn : n ≠ 0) (h : P.IsPoleNumber n) : gonality k F ≤ n * P.degree := by
  obtain ⟨x, -, hxP, hxQ⟩ := (P.isPoleNumber_iff n).mp h
  exact (gonality_le_finrank_adjoin (P.transcendental_of_ord_ne_zero (by omega))).trans
    (P.finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF hxP hxQ).le

/-! ### Rational function fields -/

/-- The rational function field `k(t)` has gonality one, attained by `t`. -/
@[simp]
theorem gonality_ratFunc : gonality k (RatFunc k) = 1 := by
  refine le_antisymm ?_ (gonality_pos (IsFunctionField.ratFunc k))
  have h := gonality_le_finrank_adjoin (RatFunc.transcendental_X (K := k))
  rwa [RatFunc.adjoin_X, IntermediateField.finrank_top] at h

/-- **Gonality one characterizes the rational function field**: `F / k` has gonality one exactly
when `F` is `k`-isomorphic to `k(t)`. No hypothesis on `F` is needed: an index-one rational
subfield `k(x)` is all of `F`. -/
theorem gonality_eq_one_iff : gonality k F = 1 ↔ Nonempty (F ≃ₐ[k] RatFunc k) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.gonality_eq.trans gonality_ratFunc⟩
  obtain ⟨x, hx, hrank⟩ := Nat.sInf_mem (Nat.nonempty_of_pos_sInf (h ▸ Nat.one_pos))
  have htop : k⟮x⟯ = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp (hrank.trans h)
  have : Algebra.Transcendental k F := ⟨x, hx⟩
  exact ⟨(RatFunc.algEquivOfAdjoinEqTop htop).symm⟩

/-- A function field of positive genus is not rational, so its gonality is at least two. -/
theorem two_le_gonality_of_genus_ne_zero (hF : IsFunctionField k F) (hg : genus k F ≠ 0) :
    2 ≤ gonality k F := by
  have := gonality_pos hF
  by_contra! h
  obtain ⟨e⟩ := (gonality_eq_one_iff (k := k) (F := F)).mp (by omega)
  exact (isEmpty_algEquiv_ratFunc_of_genus_ne_zero hg).false e

/-- **Gonality two means a rational subfield of index two**, for a function field that is not
rational. Rationality has to be excluded: `k(t)` has gonality one but `k(t ^ 2)` has index two. -/
theorem gonality_eq_two_iff (hF : IsFunctionField k F) (hrat : IsEmpty (F ≃ₐ[k] RatFunc k)) :
    gonality k F = 2 ↔ ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = 2 := by
  refine ⟨fun h ↦ h ▸ exists_finrank_adjoin_eq_gonality hF, fun ⟨x, hx, hrank⟩ ↦ ?_⟩
  have h1 : gonality k F ≠ 1 := fun h ↦ (gonality_eq_one_iff.mp h).elim hrat.false
  have := gonality_le_finrank_adjoin hx
  have := gonality_pos hF
  omega

/-! ### Bounds from Riemann–Roch -/

/-- **A divisor of degree one bounds the gonality by `g + 1`**: by Riemann's inequality the
multiple `(g + 1) D` has `ℓ ≥ 2`. -/
theorem gonality_le_genus_add_one (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hD : Divisor.degree D = 1) : gonality k F ≤ genus k F + 1 := by
  have hdeg : Divisor.degree (((genus k F : ℤ) + 1) • D) = genus k F + 1 := by simp [hD]
  have hdim := Divisor.degree_add_one_sub_genus_le_dim hF (((genus k F : ℤ) + 1) • D)
  rw [hdeg] at hdim
  have := gonality_le_degree hF hex (D := ((genus k F : ℤ) + 1) • D) (by omega)
  rw [hdeg] at this
  omega

/-- **A canonical divisor bounds the gonality by `2g - 2`** in genus at least two: it has degree
`2g - 2` and `ℓ = g ≥ 2`. -/
theorem gonality_le_two_mul_genus_sub_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F) :
    gonality k F ≤ 2 * genus k F - 2 := by
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  have := gonality_le_degree hF hex (D := W) (by rw [hW.dim_eq hF hex]; exact hg)
  rw [hW.degree_eq hF hex] at this
  omega

/-- **A function field of genus two has gonality two**, over every exact constant field: the
canonical divisor bounds it by two, and a field of positive genus is not rational. -/
theorem gonality_of_genus_eq_two (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 2) : gonality k F = 2 := by
  have := gonality_le_two_mul_genus_sub_two hF hex hg.ge
  have := two_le_gonality_of_genus_ne_zero hF (by omega)
  omega

end TauCeti
