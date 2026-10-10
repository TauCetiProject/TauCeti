/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Residue
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Derivative
import TauCeti.FieldTheory.FunctionField.Differential.LocalNonvanishing
import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# The Weil differential `dx` does not depend on the separating element

Let `F / k` be an algebraic function field with exact constants, and let `x` and `y` be separating
elements. The Weil differentials `dx` and `dy` (`TauCeti.weilDifferentialOfSeparating`) are the
cotraces of the canonical differential of the rational function field along `X ↦ x` and `X ↦ y`.
They satisfy the chain rule

`dy = (dy/dx) · dx`,

where `dy/dx` is the derivative of Kähler differentials (`TauCeti.derivativeOfSeparating`). This
is Stichtenoth's Theorem 4.3.2(a), `δ(y) = (dy/dx) · δ(x)`.

The proof compares one local component. At a rational place `P` where `x - a` and `y - b` are both
prime elements, the local components are residues
(`TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`):
`(dy)_P (u) = res_{P,y-b} (u)` and `(dx)_P (u) = res_{P,x-a} (u)`. The transformation formula
(`TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`) rewrites the first as
`res_{P,x-a} (u · dy/dx)`, which is the local component of `(dy/dx) · dx`. Over an exact constant
field one local component determines a Weil differential
(`TauCeti.repartitionDualComponent_inj`). Such a place exists as soon as `F` has infinitely many
rational places, for instance over an algebraically closed field: at all but finitely many
rational places `P`, the function `x - x(P)` is a prime element, since only finitely many places
ramify over `k(x)`.

Consequently the Kähler–Weil comparison
`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating` does not depend on the separating
element used to build it, and the local components of the Weil differential attached to a Kähler
differential `ω` are its residues: `ω_P (u) = res_P (u ω)` at every rational place with a
separating prime element (Stichtenoth, Theorem 4.3.2(d)).

## Main results

* `TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`: at all but finitely many rational
  places that are not poles of a separating `x`, some `x - a` is a prime element.
* `TauCeti.Place.infinite_setOf_degree_eq_one`: over an algebraically closed field there are
  infinitely many rational places.
* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one`:
  `dy = (dy/dx) · dx`, given a rational place at which `x - a` and `y - b` are prime elements.
* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`: **the chain rule
  `dy = (dy/dx) · dx`** when `F` has infinitely many rational places.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq`:
  the Kähler–Weil comparison is independent of the separating element.
* `TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`:
  **local components are residues**, `ω_P (u) = res_P (u ω)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2.
-/

public section

open scoped IntermediateField

open KaehlerDifferential

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- **Almost every rational place has a translate of `x` as a prime element**: for a separating
element `x`, only finitely many rational places `P` with `ord_P x ≥ 0` admit no constant `a` with
`ord_P (x - a) = 1`. -/
theorem finite_setOf_forall_ord_sub_algebraMap_ne_one (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | P.degree = 1 ∧ 0 ≤ P.ord x ∧
      ∀ a : k, P.ord (x - algebraMap k F a) ≠ 1}.Finite := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  refine (finite_setOf_differentExponent_ne_zero (k' := k) (F' := F) k (RatFunc k)
    (IsFunctionField.ratFunc k)).subset fun P ⟨hP, hx0, hne⟩ ↦ ?_
  refine (differentExponent_pos_of_one_lt_ramificationIdx k (RatFunc k) P ?_).ne'
  refine lt_of_le_of_ne (ramificationIdx_pos (RatFunc k) P) fun he ↦ ?_
  rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C (Nat.eq_one_of_mul_eq_one_right
    (hP ▸ degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P).symm) with h | ⟨a, h⟩
  · -- `x` would have a pole at `P`, lying over the pole of `X`.
    rw [← hX, ord_algebraMap_restrict k (RatFunc k) P, h, ord_infty, RatFunc.intDegree_X,
      ← he] at hx0
    omega
  · -- `x - a` is a prime element at `P`, lying unramified over the zero of `X - a`.
    refine hne a ?_
    rw [← hX, IsScalarTower.algebraMap_apply k (RatFunc k) F, RatFunc.algebraMap_eq_C, ← map_sub,
      ord_algebraMap_restrict k (RatFunc k) P, h, ord_adicOfIrreducible_X_sub_C_self, ← he,
      Nat.cast_one, mul_one]

/-- Over an algebraically closed constant field, an algebraic function field has infinitely many
rational places. -/
theorem infinite_setOf_degree_eq_one [IsAlgClosed k] (hF : IsFunctionField k F) :
    {P : Place k F | P.degree = 1}.Infinite := by
  have := infinite hF
  simpa [degree_eq_one_of_isAlgClosed_of_isFunctionField _ hF] using
    Set.infinite_univ (α := Place k F)

end Place

/-- **The chain rule for Weil differentials, at a common rational place** (Stichtenoth,
Theorem 4.3.2(a)): over an exact constant field, if `x - a` and `y - b` are prime elements at the
same rational place, then the Weil differentials of the separating elements `x` and `y` satisfy
`dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] {P : Place k F} (hP : P.degree = 1)
    {a b : k} (hxa : P.ord (x - algebraMap k F a) = 1) (hyb : P.ord (y - algebraMap k F b) = 1) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  -- The translate `x - a` is separating, with the same derivative as `x`.
  have hxa' : Transcendental k (x - algebraMap k F a) := fun h ↦ hx <| by
    simpa using (h.isIntegral.add (isIntegral_algebraMap (x := a))).isAlgebraic
  have : Algebra.IsSeparable k⟮x - algebraMap k F a⟯ F := by
    rw [sub_eq_add_neg, ← map_neg, IntermediateField.adjoin_simple_add_algebraMap]
    infer_instance
  -- One local component determines a Weil differential; compare them at `P`.
  refine Subtype.ext ((repartitionDualComponent_inj hF hex (Submodule.coe_mem _)
    (Submodule.coe_mem _) P).mp (LinearMap.ext fun u ↦ ?_))
  rw [coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating hF hy hP hyb,
    repartitionDualComponent_weilDifferentialOfSeparating hF hx hP hxa,
    P.residue_eq_residue_mul_derivativeOfSeparating hP hxa hxa' hyb,
    derivativeOfSeparating_sub_algebraMap hx hxa', map_sub, Derivation.map_algebraMap, sub_zero,
    mul_comm]

/-- **The chain rule for Weil differentials** (Stichtenoth, Theorem 4.3.2(a)): over an exact
constant field, if `F` has infinitely many rational places (for instance if `k` is algebraically
closed, `TauCeti.Place.infinite_setOf_degree_eq_one`), then the Weil differentials of any two
separating elements `x` and `y` satisfy `dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hinf : {P : Place k F | P.degree = 1}.Infinite) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  -- Avoid the poles and zeros of `x` and `y` and the finitely many bad places of each.
  obtain ⟨P, hP, hPgood⟩ := (hinf.sdiff (((((Place.finite_setOf_ord_ne_zero hF x).union
    (Place.finite_setOf_ord_ne_zero hF y)).union
      (Place.finite_setOf_forall_ord_sub_algebraMap_ne_one hF hx)).union
        (Place.finite_setOf_forall_ord_sub_algebraMap_ne_one hF hy)))).nonempty
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_forall, not_not] at hPgood
  obtain ⟨⟨⟨hx0, hy0⟩, hxP⟩, hyP⟩ := hPgood
  obtain ⟨a, hxa⟩ := hxP hP hx0.ge
  obtain ⟨b, hyb⟩ := hyP hP hy0.ge
  exact weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one hF hex hx hy hP
    hxa hyb

/-- **The Kähler–Weil comparison does not depend on the separating element** (Stichtenoth,
Theorem 4.3.2): over an exact constant field, if `F` has infinitely many rational places, then the
comparisons built from any two separating elements are equal. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx =
      kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hy := by
  let := weilDifferentialSpaceModule hF
  -- Both are `F`-linear, so compare them on the basis `dx`.
  refine LinearEquiv.toLinearMap_injective ((kaehlerBasisOfSeparating hx).ext fun _ ↦ ?_)
  rw [kaehlerBasisOfSeparating_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D,
    weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hex hinf hy hx]

/-- **Local components are residues** (Stichtenoth, Theorem 4.3.2(d)): over an exact constant
field with infinitely many rational places, let `ω` be a Kähler differential and `P` a rational
place with a separating prime element `t`. The local component at `P` of the Weil differential
attached to `ω` by the Kähler–Weil comparison is `u ↦ res_P (u ω)`. -/
theorem repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    {t : F} (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : Ω[F⁄k]) (u : F) :
    repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.kaehlerResidue hP ht htr (u • ω) := by
  let := weilDifferentialSpaceModule hF
  -- Write `ω = z dt` and compute with the comparison built from `t`.
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F t = ω :=
    ⟨(kaehlerBasisOfSeparating htr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating htr).sum_repr ω⟩
  -- The residue only depends on the uniformizer, not on the proof that it is one.
  have hres {s : F} (hs : s = t) (hs₁ : P.ord s = 1) : P.residue hP hs₁ = P.residue hP ht := by
    subst hs
    rfl
  have ht₀ : P.ord (t - algebraMap k F 0) = 1 := by simpa using ht
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hinf hx htr, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating hF htr hP ht₀,
    hres (by simp) ht₀, smul_smul, Place.kaehlerResidue_smul_D, mul_comm]

end TauCeti
