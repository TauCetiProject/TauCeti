/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Algebra.Polynomial.Roots

/-!
# Automorphisms of an elliptic curve

Let `E` be an elliptic curve over a field `K`. Over a field, isomorphisms of Weierstrass curves
are exactly the admissible changes of variables `WeierstrassCurve.VariableChange K`, acting via
`•`; the automorphisms of `E` are therefore the `C : VariableChange K` with `C • E = E`. This file
proves the classical fact (Silverman, *The Arithmetic of Elliptic Curves*, III.10) that if
`j(E) ∉ {0, 1728}` then the only automorphisms of `E` are `±1`, uniformly in the characteristic,
and that in general the automorphism group is finite, over any integral domain.

## Main definitions and statements

* `WeierstrassCurve.eq_one_or_eq_negVariableChange_of_smul_eq`: if `j(E) ∉ {0, 1728}` then any
  `C : VariableChange K` with `C • E = E` equals `1` or `negVariableChange E`.
* `WeierstrassCurve.eq_one_or_eq_negVariableChange_map`: the same dichotomy for the image of `E`
  under any injective ring map, with the `j`-hypotheses still read on `E` itself.
* `WeierstrassCurve.autGroup E`: the automorphism group of `E`, as the stabiliser of `E` under
  the action of `VariableChange K`. It is an `abbrev`, so Mathlib's `MulAction.stabilizer` API
  applies to it unchanged.
* `WeierstrassCurve.autGroupMulEquiv`: for `j(E) ∉ {0, 1728}`, the isomorphism
  `autGroup E ≃* Multiplicative (ZMod 2)`, obtained from Mathlib's `zmodMulEquivOfGenerator`
  with `negVariableChange E` as the generator.
* `WeierstrassCurve.finite_autGroup`: the automorphism group of an elliptic curve over an integral
  domain is finite, in every characteristic.

## Implementation notes

The proof is broken into pieces. `j ∉ {0, 1728}` is equivalent to `c₄ ≠ 0` and `c₆ ≠ 0`
(`j_eq_zero_iff` and `j_eq_1728_iff`). From the transformation laws of `c₄` and `c₆`
one gets `u² = 1` (`u_eq_one_or_eq_neg_one`), which reduces everything to the case `u = 1`. There
`r = 0` follows from the transformation laws of `b₄`, `b₆`, `b₈` (`r_eq_zero_of_u_eq_one`), and
then `s`, `t` are read off from those of `a₁`, `a₂`, `a₃`, `a₄`
(`eq_one_or_eq_negVariableChange_of_u_eq_one`, where the `negVariableChange` value can occur only
in characteristic `2`).

Finiteness in general does not classify the automorphisms. The discriminant forces `u¹² = 1`. The
transformation laws of `b₈` and `b₆` are a quartic and a cubic equation for `r`, with leading
coefficients `3` and `4`, which do not both vanish; those of `a₂` and `a₆` are monic quadratic
equations for `s` and `t`. So each coordinate of `C` ranges over a finite set.

This is the `Aut (E, O)` milestone of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1 (in its
equation-level form over the ground field), which §Layer 5's twist classification quantifies
over: for `j ∉ {0, 1728}` the pointed twists are exactly the quadratic twists because this group
is `{±1}`.

The `j ∉ {0, 1728}` classification is adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Aut.lean` at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0). That file's own header reads `Authors: Michael Stoll, Claude`, and it
has not been touched in FLT since `bc2fe8ff7396`, so the pin and the working clone
(`d18b563029f3`, a later Mathlib bump) agree on it verbatim. Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-! ### `Aut(E) = {±1}` for `j ∉ {0, 1728}`

Throughout, `C • E = E` is an automorphism of `E`; the nonvanishing of `c₄` and `c₆` encodes
`j ∉ {0, 1728}`. -/

/-- An automorphism `C` of `E` with `C.u = 1` has no `x`-translation: `C.r = 0`. This follows
from the transformation laws of `b₄`, `b₆`, `b₈` together with `c₆ ≠ 0`. -/
private lemma r_eq_zero_of_u_eq_one (hc6 : E.c₆ ≠ 0) {C : VariableChange K} (hu : C.u = 1)
    (hCE : C • E = E) : C.r = 0 := by
  rw [c₆] at hc6
  have eb4 := congrArg b₄ hCE
  have eb6 := congrArg b₆ hCE
  have eb8 := congrArg b₈ hCE
  simp only [variableChange_b₄, hu, inv_one, Units.val_one, one_pow, one_mul,
    variableChange_b₆, variableChange_b₈] at eb4 eb6 eb8
  grobner

/-- An automorphism `C` of `E` with `C.u = 1` is either the identity or `negVariableChange E`.
After `r_eq_zero_of_u_eq_one`, the `a₁` and `a₃` laws give `2s = 2t = 0`; in characteristic `≠ 2`
this forces `s = t = 0`, and in characteristic `2` the `a₂`, `a₄` laws pin `(s, t)` down to either
`(0, 0)` or `(-a₁, -a₃)`. -/
private lemma eq_one_or_eq_negVariableChange_of_u_eq_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hu : C.u = 1) (hCE : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  have hr : C.r = 0 := E.r_eq_zero_of_u_eq_one hc6 hu hCE
  obtain ⟨e1, e2, e3, e4, -⟩ := WeierstrassCurve.ext_iff.mp hCE
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, hu,
    inv_one, Units.val_one, one_pow, one_mul] at e1 e2 e3 e4
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- characteristic `2`: `a₁ ≠ 0` (else `c₄ = a₁⁴ = 0`); the `a₂`, `a₄` laws force `(s, t)` to
    -- be `(0, 0)` or `(-a₁, -a₃)`, the latter being `negVariableChange` since `-1 = 1`.
    have ha1 : E.a₁ ≠ 0 := by rw [c₄, b₂, b₄] at hc4; grobner
    have hq2 : C.s * (E.a₁ + C.s) = 0 := by linear_combination -e2 + 3 * hr
    have hq4 : C.s * E.a₃ + C.t * E.a₁ = 0 := by
      linear_combination -e4 + (2 * E.a₂ - C.s * E.a₁ + 3 * C.r) * hr - C.s * C.t * h2
    rcases (mul_eq_zero.mp hq2).imp id eq_neg_of_add_eq_zero_right with hs | hs
    · have ht : C.t = 0 := by grobner
      exact .inl (VariableChange.ext hu hr hs ht)
    · have ht : C.t = -E.a₃ := by grobner
      have hu1neg : (1 : Kˣ) = -1 := by ext; push_cast; linear_combination h2
      exact .inr (VariableChange.ext (by simpa using hu.trans hu1neg) (by simpa using hr)
        (by simpa using hs) (by simpa using ht))
  · -- characteristic `≠ 2`: `2s = 2t = 0`, so `s = t = 0` and `C = 1`.
    have hs : C.s = 0 := by grobner
    have ht : C.t = 0 := by grobner
    exact .inl (VariableChange.ext hu hr hs ht)

/-- The `u`-coefficient of an automorphism `C` of `E` (with `c₄, c₆ ≠ 0`) satisfies `u² = 1`:
the `c₄` and `c₆` laws give `u⁴ = u⁶ = 1`. -/
private lemma u_eq_one_or_eq_neg_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hCE : C • E = E) : C.u = 1 ∨ C.u = -1 := by
  have hu4 : (C.u : K) ^ 4 = 1 := by
    have h := congrArg c₄ hCE
    rwa [variableChange_c₄, Units.val_inv_eq_inv_val, mul_eq_right₀ hc4, inv_pow, inv_eq_one] at h
  have hu6 : (C.u : K) ^ 6 = 1 := by
    have h := congrArg c₆ hCE
    rwa [variableChange_c₆, Units.val_inv_eq_inv_val, mul_eq_right₀ hc6, inv_pow, inv_eq_one] at h
  have hu2 : (C.u : K) * (C.u : K) = 1 := by linear_combination hu6 - (C.u : K) ^ 2 * hu4
  exact (mul_self_eq_one_iff.mp hu2).imp Units.val_eq_one.mp Units.val_eq_neg_one.mp

/-- If `c₄ ≠ 0` and `c₆ ≠ 0` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`. This is the form of `Aut(E) = {±1}` phrased via `c₄, c₆` (equivalent to
`j ∉ {0, 1728}` for an elliptic curve, see `eq_one_or_eq_negVariableChange_of_smul_eq`). -/
private theorem eq_one_or_eq_negVariableChange_of_c₄_ne_zero_of_c₆_ne_zero_of_smul_eq_field
    (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange K} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  rcases E.u_eq_one_or_eq_neg_one hc4 hc6 hC with hu | hu
  · exact E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hu hC
  · -- Reduce `u = -1` to `u = 1` by composing with the involution `negVariableChange E`.
    have hDu : (E.negVariableChange * C).u = 1 := by
      simp [VariableChange.mul_def, hu]
    have hDE : (E.negVariableChange * C) • E = E := by
      rw [mul_smul, hC, negVariableChange_smul_self]
    have hCeq : C = E.negVariableChange * (E.negVariableChange * C) := by
      rw [← mul_assoc, negVariableChange_mul_self, one_mul]
    rcases E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hDu hDE with h | h
    · right; rw [hCeq, h, mul_one]
    · left; rw [hCeq, h, negVariableChange_mul_self]

end Field

section Domain

variable {A : Type*} [CommRing A] [IsDomain A] (E : WeierstrassCurve A)

/-- If `c₄ ≠ 0` and `c₆ ≠ 0` then the only admissible changes of variables fixing `E` are `1`
and `negVariableChange E`.

The classification is a statement about an integral domain, not a field: the argument is
cancellation and zero-product reasoning throughout. It is obtained here from the field case by
base change to the fraction field, where every hypothesis and conclusion transfers along the
injection — `c₄`, `c₆` by `map_c₄`/`map_c₆`, the fixing equation by
`VariableChange.map_variableChange`, and the conclusion back down by
`VariableChange.map_injective`. -/
theorem eq_one_or_eq_negVariableChange_of_c₄_ne_zero_of_c₆_ne_zero_of_smul_eq
    (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange A} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  set φ := algebraMap A (FractionRing A)
  have hinj : Function.Injective φ := IsFractionRing.injective A (FractionRing A)
  have hC' : (C.map φ) • (E.map φ) = E.map φ := by
    rw [map_variableChange, hC]
  have h4 : (E.map φ).c₄ ≠ 0 := by rw [map_c₄]; exact fun h ↦ hc4 (hinj (by simpa using h))
  have h6 : (E.map φ).c₆ ≠ 0 := by rw [map_c₆]; exact fun h ↦ hc6 (hinj (by simpa using h))
  rcases (E.map φ).eq_one_or_eq_negVariableChange_of_c₄_ne_zero_of_c₆_ne_zero_of_smul_eq_field
    h4 h6 hC' with h | h
  · -- `VariableChange.mapHom` is a monoid hom, so it carries `1` to `1`.
    have hone : (1 : VariableChange A).map φ = 1 := map_one (VariableChange.mapHom φ)
    exact .inl (VariableChange.map_injective hinj (by simpa only [hone] using h))
  · refine .inr (VariableChange.map_injective hinj ?_)
    rwa [negVariableChange_map] at h

/-- If `j(E) ∉ {0, 1728}` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`; that is, `Aut(E) = {±1}`. -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq [E.IsElliptic] (hj₀ : E.j ≠ 0)
    (hj₁₇₂₈ : E.j ≠ 1728) {C : VariableChange A} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange :=
  E.eq_one_or_eq_negVariableChange_of_c₄_ne_zero_of_c₆_ne_zero_of_smul_eq
    (E.j_eq_zero_iff.not.mp hj₀) (E.j_eq_1728_iff.not.mp hj₁₇₂₈) hC

omit [IsDomain A] in
variable {B : Type*} [CommRing B] [IsDomain B] in
/-- **`Aut(E.map f) = {±1}` when `j(E) ∉ {0, 1728}`**: the dichotomy survives any injective change
of base ring. The hypotheses stay on `E` over the source ring, since `j` of the image is the image
of `j` (`map_j`), so an injective `f` carries both away from `0` and from `1728`. Only the target
has to be a domain; the source needs no more than a commutative ring. Applies to a base change
through `E.baseChange B = E.map (algebraMap A B)`. -/
theorem eq_one_or_eq_negVariableChange_map [E.IsElliptic] {f : A →+* B}
    (hf : Function.Injective f) (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728)
    {D : VariableChange B} (hD : D • E.map f = E.map f) :
    D = 1 ∨ D = (E.map f).negVariableChange := by
  have hj : (E.map f).j = f E.j := E.map_j f
  refine (E.map f).eq_one_or_eq_negVariableChange_of_smul_eq ?_ ?_ hD
  · rw [hj]; exact fun h ↦ hj₀ (hf (by rw [h, map_zero]))
  · rw [hj]; exact fun h ↦ hj₁₇₂₈ (hf (by rw [h, map_ofNat]))

/-! ### The automorphism group -/

section AutGroup

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open MulAction in
/-- The automorphism group of a Weierstrass curve `W`: the admissible changes of variables
fixing `W`, i.e. the stabiliser of `W` under the action of `VariableChange R`. This is an
`abbrev` rather than a `def` so that Mathlib's `MulAction.stabilizer` API applies to it
unchanged — in particular the `simp` lemma `MulAction.mem_stabilizer_iff`, which is the
membership normal form `C ∈ W.autGroup ↔ C • W = W`. -/
abbrev autGroup : Subgroup (VariableChange R) := stabilizer (VariableChange R) W

end AutGroup

/-! ### Finiteness of the automorphism group -/

open Polynomial in
/-- The values of `r` in a change of variables fixing a curve with invariants `b₂`, `b₄`, `b₆`,
`b₈` lie in a finite set: they solve both the `b₈`-equation, a quartic with leading coefficient
`3`, and the `b₆`-equation, a cubic with leading coefficient `4`, and `3` and `4` cannot both
vanish. -/
private theorem finite_setOf_r (b₂ b₄ b₆ c d : A) :
    {r : A | 3 * r ^ 4 + b₂ * r ^ 3 + 3 * b₄ * r ^ 2 + 3 * b₆ * r + c = 0 ∧
      4 * r ^ 3 + b₂ * r ^ 2 + 2 * b₄ * r + d = 0}.Finite := by
  by_cases h3 : (3 : A) = 0
  · have h4 : (4 : A) ≠ 0 := fun h4 ↦ one_ne_zero (α := A) (by linear_combination h4 - h3)
    have hp : (C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 1 + C d : A[X]) ≠ 0 := fun h ↦
      h4 (by simpa [coeff_C_mul_X_pow, coeff_C, -map_mul] using congrArg (coeff · 3) h)
    exact (finite_setOfPred_isRoot hp).subset fun r hr ↦ by simpa using hr.2
  · have hp : (C 3 * X ^ 4 + C b₂ * X ^ 3 + C (3 * b₄) * X ^ 2 + C (3 * b₆) * X ^ 1 + C c :
        A[X]) ≠ 0 := fun h ↦
      h3 (by simpa [coeff_C_mul_X_pow, coeff_C, -map_mul] using congrArg (coeff · 4) h)
    exact (finite_setOfPred_isRoot hp).subset fun r hr ↦ by simpa using hr.1

/-- **The automorphism group of an elliptic curve is finite**, over any integral domain and in
every characteristic. -/
instance finite_autGroup [E.IsElliptic] : Finite E.autGroup := by
  set V : Set A := {v | v ^ 12 = 1}
  set R : Set A := ⋃ v ∈ V, {r | 3 * r ^ 4 + E.b₂ * r ^ 3 + 3 * E.b₄ * r ^ 2 + 3 * E.b₆ * r +
    (E.b₈ - v ^ 4 * E.b₈) = 0 ∧ 4 * r ^ 3 + E.b₂ * r ^ 2 + 2 * E.b₄ * r + (E.b₆ - v ^ 6 * E.b₆) = 0}
  set S : Set A := ⋃ v ∈ V, ⋃ r ∈ R, {s | s ^ 2 + E.a₁ * s + (v ^ 10 * E.a₂ - E.a₂ - 3 * r) = 0}
  set T : Set A := ⋃ v ∈ V, ⋃ r ∈ R, {t | t ^ 2 + (E.a₃ + r * E.a₁) * t +
    (v ^ 6 * E.a₆ - E.a₆ - r * E.a₄ - r ^ 2 * E.a₂ - r ^ 3) = 0}
  -- a monic quadratic has finitely many roots
  have quad (a b : A) : {x : A | x ^ 2 + a * x + b = 0}.Finite := by
    have hp : (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial A) ≠ 0 := fun h ↦ by simpa using congrArg (Polynomial.coeff · 2) h
    exact (Polynomial.finite_setOfPred_isRoot hp).subset fun x hx ↦ by simpa using hx
  have hV : V.Finite := (Polynomial.finite_setOfPred_isRoot
    (Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 12) (1 : A))).subset
      fun v (hv : v ^ 12 = 1) ↦ by simpa [sub_eq_zero] using hv
  have hR : R.Finite := hV.biUnion fun v _ ↦ finite_setOf_r _ _ _ _ _
  have hS : S.Finite := hV.biUnion fun v _ ↦ hR.biUnion fun r _ ↦ quad _ _
  have hT : T.Finite := hV.biUnion fun v _ ↦ hR.biUnion fun r _ ↦ quad _ _
  let f : E.autGroup → A × A × A × A := fun C ↦ ((C.1.u⁻¹ : Aˣ), C.1.r, C.1.s, C.1.t)
  have hf : Function.Injective f := fun C D h ↦ by
    simp only [f, Prod.mk.injEq] at h
    exact Subtype.ext (VariableChange.ext (inv_injective (Units.ext h.1)) h.2.1 h.2.2.1 h.2.2.2)
  suffices hrange : Set.range f ⊆ V ×ˢ R ×ˢ S ×ˢ T by
    have := ((hV.prod (hR.prod (hS.prod hT))).subset hrange).to_subtype
    exact Finite.of_injective_finite_range hf
  -- read the coordinates of `C • E = E` off the transformation laws
  rintro _ ⟨⟨C, hC⟩, rfl⟩
  rw [MulAction.mem_stabilizer_iff] at hC
  set v : A := ((C.u⁻¹ : Aˣ) : A)
  have hΔ := congrArg WeierstrassCurve.Δ hC
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  have hb₆ := congrArg WeierstrassCurve.b₆ hC
  have hb₈ := congrArg WeierstrassCurve.b₈ hC
  simp only [variableChange_Δ, variableChange_a₂, variableChange_a₆, variableChange_b₆,
    variableChange_b₈] at hΔ h₂ h₆ hb₆ hb₈
  have hv : v ^ 12 = 1 :=
    (mul_left_eq_self₀.mp hΔ).resolve_right E.isUnit_Δ.ne_zero
  have hr : C.r ∈ R := Set.mem_biUnion hv
    ⟨by linear_combination v ^ 4 * hb₈ - (E.b₈ + 3 * C.r * E.b₆ + 3 * C.r ^ 2 * E.b₄ +
        C.r ^ 3 * E.b₂ + 3 * C.r ^ 4) * hv,
      by linear_combination v ^ 6 * hb₆ - (E.b₆ + 2 * C.r * E.b₄ + C.r ^ 2 * E.b₂ +
        4 * C.r ^ 3) * hv⟩
  have hs : C.s ^ 2 + E.a₁ * C.s + (v ^ 10 * E.a₂ - E.a₂ - 3 * C.r) = 0 := by
    linear_combination (-v ^ 10) * h₂ + (E.a₂ - C.s * E.a₁ + 3 * C.r - C.s ^ 2) * hv
  have ht : C.t ^ 2 + (E.a₃ + C.r * E.a₁) * C.t +
      (v ^ 6 * E.a₆ - E.a₆ - C.r * E.a₄ - C.r ^ 2 * E.a₂ - C.r ^ 3) = 0 := by
    linear_combination (-v ^ 6) * h₆ + (E.a₆ + C.r * E.a₄ + C.r ^ 2 * E.a₂ + C.r ^ 3 - C.t * E.a₃ -
      C.t ^ 2 - C.r * C.t * E.a₁) * hv
  exact ⟨hv, hr, Set.mem_biUnion hv (Set.mem_biUnion hr hs),
    Set.mem_biUnion hv (Set.mem_biUnion hr ht)⟩

/-- **`Aut(E) ≅ ℤ/2` for `j(E) ∉ {0, 1728}`.** The automorphism group of `E` is `{±1}`, so it is
isomorphic to `Multiplicative (ZMod 2)`: it has exactly two elements — `1` and
`negVariableChange E` (`eq_one_or_eq_negVariableChange_of_smul_eq`), distinct by
`negVariableChange_ne_one`. The isomorphism sends `negVariableChange E` to
`Multiplicative.ofAdd 1` (`autGroupMulEquiv_apply_negVariableChange`), its inverse sending
`Multiplicative.ofAdd 1` back (`autGroupMulEquiv_symm_apply_ofAdd_one`). -/
noncomputable def autGroupMulEquiv [E.IsElliptic] (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    E.autGroup ≃* Multiplicative (ZMod 2) :=
  let g : E.autGroup := ⟨E.negVariableChange, E.negVariableChange_smul_self⟩
  have hg : g ≠ 1 := fun h ↦ E.negVariableChange_ne_one (congrArg Subtype.val h)
  have key : ∀ C : E.autGroup, C = 1 ∨ C = g := fun C ↦
    (E.eq_one_or_eq_negVariableChange_of_smul_eq hj₀ hj₁₇₂₈ C.2).imp Subtype.ext Subtype.ext
  (zmodMulEquivOfGenerator (g := g) (fun x ↦ by rcases key x with h | h <;> subst h <;> simp)
    ((Nat.card_eq_two_iff' 1).mpr ⟨g, hg, fun y hy ↦ (key y).resolve_left hy⟩)).symm

variable [E.IsElliptic] (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728)

/-- The inverse of `autGroupMulEquiv` sends `Multiplicative.ofAdd 1` to the negation
automorphism: it is `zmodMulEquivOfGenerator` for that generator. -/
@[simp] lemma autGroupMulEquiv_symm_apply_ofAdd_one :
    (E.autGroupMulEquiv hj₀ hj₁₇₂₈).symm (Multiplicative.ofAdd 1)
      = ⟨E.negVariableChange, E.negVariableChange_smul_self⟩ := by
  simp only [autGroupMulEquiv, MulEquiv.symm_symm, zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- `autGroupMulEquiv` sends the negation automorphism to `Multiplicative.ofAdd 1`. -/
@[simp] lemma autGroupMulEquiv_apply_negVariableChange :
    E.autGroupMulEquiv hj₀ hj₁₇₂₈ ⟨E.negVariableChange, E.negVariableChange_smul_self⟩
      = Multiplicative.ofAdd 1 := by
  rw [← autGroupMulEquiv_symm_apply_ofAdd_one E hj₀ hj₁₇₂₈, MulEquiv.apply_symm_apply]

end Domain

end WeierstrassCurve

end
