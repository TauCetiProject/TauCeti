/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.Separable.Quadratic

/-!
# Hyperelliptic function fields

An algebraic function field `F / k` is *hyperelliptic* when it has genus at least two and
contains a rational subfield `k(x)` of index two over which it is separable.  Separability is
part of the definition rather than a consequence of it: over a constant field of characteristic
two an index-two subfield can be inseparable, and no standing hypothesis of this development
rules that out.  Away from characteristic two it is automatic, by
`TauCeti.Algebra.isSeparable_of_finrank_eq_two`.

The content of this file is the *intrinsic* description of that subfield, which mentions no
element of `F` at all: `F` is hyperelliptic exactly when its genus is at least two and some
divisor of degree two has `ℓ(A) ≥ 2`.  One direction is the pole divisor `(x)_∞` of the
index-two generator, whose Riemann--Roch space contains `1` and `x`.  The other moves `A` inside
its class to an effective divisor `B`, picks a function `x ∈ L(B)` outside the constants — which
positivity of `ℓ(B)` over the line of constants provides — and reads `[F : k(x)] = deg (x)_∞`
off the product formula: the pole divisor of `x` is dominated by `B`, so the degree is at most
two, and it is not one because a rational function field has genus zero.

In genus two the canonical divisor is such an `A`, since `deg W = 2g - 2 = 2` and `ℓ(W) = g = 2`;
so every function field of genus two has an index-two rational subfield, and away from
characteristic two every function field of genus two is hyperelliptic.

## Main definitions

* `TauCeti.IsHyperellipticFunctionField`: genus at least two together with a separable rational
  subfield of index two.

## Main results

* `TauCeti.exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two`: a divisor of degree two
  with `ℓ ≥ 2` produces a rational subfield of index two; no hypothesis on the characteristic.
* `TauCeti.isHyperellipticFunctionField_iff_exists_degree_eq_two_and_two_le_dim`: the intrinsic
  characterization, away from characteristic two.
* `TauCeti.exists_transcendental_finrank_adjoin_eq_two_of_genus_eq_two` and
  `TauCeti.isHyperellipticFunctionField_of_genus_eq_two`: genus two gives an index-two rational
  subfield, and away from characteristic two makes `F` hyperelliptic.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section VI.2: Definition 6.2.1 and Lemma 6.2.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A **hyperelliptic function field** (Stichtenoth, Definition 6.2.1, with separability of the
index-two subextension made part of the definition): genus at least two together with an element
`x` transcendental over `k` such that `F / k(x)` is separable of degree two.

Being an algebraic function field is *not* part of the predicate: the hypothesis
`TauCeti.IsFunctionField`, like the exactness of the constant field, is kept as a separate
hypothesis on the statements that need it, as everywhere in this development.

In characteristic two an index-two subextension can be purely inseparable, and such an `F` is
deliberately outside this model class; away from characteristic two the separability clause is
automatic, so there the predicate agrees with Stichtenoth's index-two definition. -/
structure IsHyperellipticFunctionField (k F : Type*) [Field k] [Field F] [Algebra k F] :
    Prop where
  /-- A hyperelliptic function field has genus at least two. -/
  two_le_genus : 2 ≤ genus k F
  /-- A hyperelliptic function field has a separable rational subfield of index two. -/
  exists_separable_finrank_adjoin_eq_two : ∃ x : F, Transcendental k x ∧
    Module.finrank k⟮x⟯ F = 2 ∧ Algebra.IsSeparable k⟮x⟯ F

/-! ### From the index-two subfield to a divisor of degree two -/

/-- **The pole divisor of an index-two generator has degree two and `ℓ ≥ 2`**: its degree is
`[F : k(x)]` by the product formula, and its Riemann--Roch space contains the two independent
functions `1` and `x`. -/
theorem IsHyperellipticFunctionField.exists_degree_eq_two_and_two_le_dim
    (hF : IsFunctionField k F) (hhyp : IsHyperellipticFunctionField k F) :
    ∃ A : Divisor k F, Divisor.degree A = 2 ∧ 2 ≤ Divisor.dim A := by
  obtain ⟨x, hx, hrank, -⟩ := hhyp.exists_separable_finrank_adjoin_eq_two
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  refine ⟨Divisor.poles hF (Units.mk0 x hx0), ?_, ?_⟩
  · rw [Divisor.degree_poles hF (Units.mk0 x hx0) hx, Units.val_mk0, hrank]
    norm_num
  · simpa using Divisor.succ_le_dim_nsmul_poles hF (Units.mk0 x hx0) hx 1

/-! ### From a divisor of degree two to the index-two subfield -/

/-- **A divisor of degree two whose Riemann--Roch space has dimension at least two produces a
rational subfield of index two**, as soon as the genus is positive.

No hypothesis on the characteristic is made, and no separability is claimed: this is the part of
Stichtenoth's Section VI.2 dictionary that holds over an arbitrary constant field.  Positivity of
the genus is what rules out `F = k(x)`, which would make the degree one instead of two. -/
theorem exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : genus k F ≠ 0)
    {A : Divisor k F} (hA : Divisor.degree A = 2) (hdim : 2 ≤ Divisor.dim A) :
    ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = 2 := by
  -- Move `A` inside its class to an effective divisor `B`, which has the same degree and `ℓ`.
  obtain ⟨z, hzA, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF A).mp (by omega))
  set B : Divisor k F := Divisor.principal hF (Units.mk0 z hz0) + A with hB
  have hBrw : B = A - Divisor.principal hF (Units.mk0 z hz0)⁻¹ := by
    rw [hB, Divisor.principal_inv]; abel
  have hBeff : 0 ≤ B := (mem_riemannRochSpace_units_iff hF).mp hzA
  have hBdeg : Divisor.degree B = 2 := by rw [hB]; simp [hA]
  have hBdim : 2 ≤ Divisor.dim B := by rwa [hBrw, Divisor.dim_sub_principal]
  -- The constants form a line inside `L(B)`, which has dimension at least two, so `L(B)` holds a
  -- function `x` outside the constants.
  have hlt : (k ∙ (1 : F)) < riemannRochSpace B := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (one_mem_riemannRochSpace_iff.mpr hBeff)) fun hEq ↦ ?_
    rw [Divisor.dim_def, ← hEq, finrank_span_singleton (one_ne_zero : (1 : F) ≠ 0)] at hBdim
    omega
  obtain ⟨x, hxB, hxspan⟩ := SetLike.exists_of_lt hlt
  have hxconst : ∀ c : k, algebraMap k F c ≠ x := fun c hc ↦
    hxspan (hc ▸ Submodule.mem_span_singleton.mpr ⟨c, by simp [Algebra.smul_def]⟩)
  have hx : Transcendental k x := fun halg ↦
    let ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex x halg
    hxconst c hc
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  -- The poles of `x` are bounded by `B`, so `[F : k(x)] = deg (x)_∞ ≤ deg B = 2`.
  have hle : Divisor.poles hF (Units.mk0 x hx0) ≤ B := by
    rw [WeilDivisor.le_iff]
    intro P
    have hBP : (0 : ℤ) ≤ B.coeff P := by simpa using WeilDivisor.le_iff.mp hBeff P
    have hord := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp hxB P
    rw [Divisor.coeff_poles, Units.val_mk0, sup_le_iff]
    exact ⟨by omega, hBP⟩
  have hdegle : Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) ≤ 2 := by
    rw [← hBdeg]
    exact Divisor.degree_le_of_le hle
  have _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  have hrank : (Module.finrank k⟮x⟯ F : ℤ) =
      Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) :=
    (Divisor.degree_poles hF (Units.mk0 x hx0) hx).symm
  have hpos : 0 < Module.finrank k⟮x⟯ F := Module.finrank_pos
  have hne : Module.finrank k⟮x⟯ F ≠ 1 := fun h1 ↦ hg (genus_eq_zero_of_adjoin_eq_top hF hex hx
    (IntermediateField.finrank_eq_one_iff_eq_top.mp h1))
  exact ⟨x, hx, by omega⟩

/-- **The intrinsic characterization of hyperelliptic function fields** away from characteristic
two (Stichtenoth, Section VI.2): `F` is hyperelliptic exactly when its genus is at least two and
some divisor of degree two has a Riemann--Roch space of dimension at least two.

The characteristic hypothesis is used only to make the index-two subextension separable, so the
forward implication `TauCeti.IsHyperellipticFunctionField.exists_degree_eq_two_and_two_le_dim`
and the subfield half of the converse hold without it. -/
theorem isHyperellipticFunctionField_iff_exists_degree_eq_two_and_two_le_dim
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (h2 : (2 : k) ≠ 0) :
    IsHyperellipticFunctionField k F ↔
      2 ≤ genus k F ∧ ∃ A : Divisor k F, Divisor.degree A = 2 ∧ 2 ≤ Divisor.dim A := by
  refine ⟨fun hhyp ↦ ⟨hhyp.two_le_genus, hhyp.exists_degree_eq_two_and_two_le_dim hF⟩, ?_⟩
  rintro ⟨hgen, A, hA, hdim⟩
  obtain ⟨x, hx, hrank⟩ :=
    exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two hF hex (by omega) hA hdim
  have h2' : (2 : k⟮x⟯) ≠ 0 := by
    intro h
    have hmap : algebraMap k k⟮x⟯ (2 : k) = 0 := by rw [map_ofNat]; exact h
    exact h2 (by simpa using hmap)
  exact ⟨hgen, x, hx, hrank, Algebra.isSeparable_of_finrank_eq_two h2' hrank⟩

/-! ### Genus two -/

/-- **In genus two the canonical divisor has degree two and `ℓ = 2`**: `deg W = 2g - 2` and
`ℓ(W) = g` for a Riemann--Roch divisor `W`. -/
theorem exists_degree_eq_two_and_two_le_dim_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 2) :
    ∃ A : Divisor k F, Divisor.degree A = 2 ∧ 2 ≤ Divisor.dim A := by
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  refine ⟨W, ?_, ?_⟩
  · rw [hW.degree_eq hF hex, hg]; norm_num
  · rw [hW.dim_eq hF hex, hg]

/-- **Every function field of genus two has a rational subfield of index two** (Stichtenoth,
Lemma 6.2.2), over an arbitrary constant field: the canonical pencil is a divisor of degree two
with `ℓ = 2`.  Separability of that subextension is *not* claimed here; see
`TauCeti.isHyperellipticFunctionField_of_genus_eq_two`. -/
theorem exists_transcendental_finrank_adjoin_eq_two_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 2) :
    ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = 2 := by
  obtain ⟨A, hA, hdim⟩ := exists_degree_eq_two_and_two_le_dim_of_genus_eq_two hF hex hg
  exact exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two hF hex (by omega) hA hdim

/-- **Every function field of genus two away from characteristic two is hyperelliptic**
(Stichtenoth, Lemma 6.2.2). -/
theorem isHyperellipticFunctionField_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h2 : (2 : k) ≠ 0) (hg : genus k F = 2) :
    IsHyperellipticFunctionField k F :=
  (isHyperellipticFunctionField_iff_exists_degree_eq_two_and_two_le_dim hF hex h2).mpr
    ⟨by omega, exists_degree_eq_two_and_two_le_dim_of_genus_eq_two hF hex hg⟩

end TauCeti
