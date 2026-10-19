/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

-- Non-public: the nonvanishing of the numerals `12`, `48`, `864` and `1728` is used only in the
-- proofs below.
import TauCeti.Algebra.Ring.TwoPowMulThreePow

/-!
# The short Weierstrass curve `y² = x³ + Ax + B`

Mathlib carries short Weierstrass form as a *predicate*, `WeierstrassCurve.IsShortNF`, asserting
`a₁ = a₂ = a₃ = 0` of a curve one already has, together with the invariants that follow from it
(`Δ_of_isShortNF`, `j_of_isShortNF`, and the `b`- and `c`-families). What it does not carry is the
*constructor*: the curve built from a chosen pair of coefficients. Statements phrased over an
explicit `y² = x³ + Ax + B` — the classical form of the Nagell–Lutz theorem among them — need that
constructor, so it is supplied here, with the `IsShortNF` instance that connects it to everything
Mathlib already proves.

All five coefficients are stated as `@[simp]` lemmas, in the `Zero` section. They are not
redundant with Mathlib's `a₁_of_isShortNF` family: that family needs the `IsShortNF` instance,
which needs `CommRing`, so at `Zero R` generality it is unavailable and `simp` cannot otherwise
reduce a projection of the opaque constructor. Every other fact about `shortCurve` — the `b`- and
`c`-invariants, `Δ` and `j` — is inherited through the instance rather than restated.

A second construction sits on top of it over a field in which `2` and `3` are invertible: the
short equation `WeierstrassCurve.ofCInvariants c₄ c₆` with prescribed `c`-invariants. A pair
`(c₄, c₆)` and a Weierstrass equation carrying it determine each other up to a change of variables
with `u = 1`, and this is the canonical representative of the pair.

## Main definitions

* `WeierstrassCurve.shortCurve`: the curve `y² = x³ + Ax + B`, over any `Zero`.
* `WeierstrassCurve.ofCInvariants`: the curve `y² = x³ - (c₄/48)x - c₆/864`, whose `c`-invariants
  are `c₄` and `c₆`.

## Main results

* `WeierstrassCurve.instIsShortNFShortCurve`: it is in short normal form, which is what
  makes Mathlib's `*_of_isShortNF` family apply to it.
* `WeierstrassCurve.map_shortCurve`: short form is preserved by a ring hom, and the
  coefficients transport. Mathlib has no `IsShortNF`-under-`map` instance, so this is what lets a
  curve over `ℤ` be base changed to `ℚ` and stay recognisably short.
* `WeierstrassCurve.baseChange_shortCurve`: the same for a base change, which is the spelling
  consumers actually hold. It follows definitionally from `map_shortCurve`, but `simp` does not
  automatically unfold `baseChange`, so that lemma never fires on this spelling by itself.
* `WeierstrassCurve.shortCurve_equation_iff`: a point lies on it exactly when
  `y² = x³ + Ax + B`.
* `WeierstrassCurve.shortCurve_a₄_a₆`: a curve in short normal form is `shortCurve` of its own
  `a₄` and `a₆`. This is how a statement about an arbitrary `[W.IsShortNF]` reaches the explicit
  `y² = x³ + Ax + B` shape and the `shortCurve` API.
* `WeierstrassCurve.smul_shortCurve`: the scaling `(x, y) ↦ (u²x, u³y)` carries `shortCurve A B`
  to `shortCurve (u⁻⁴A) (u⁻⁶B)`. Over a field of characteristic other than `2` and `3` these
  scalings are the only changes of variables between short equations
  (`WeierstrassCurve.variableChange_a₄_of_isShortNF`), so this is the whole coefficient freedom
  of a short equation.
* `WeierstrassCurve.ofCInvariants_c₄`, `WeierstrassCurve.ofCInvariants_c₆` and
  `WeierstrassCurve.ofCInvariants_Δ`: its invariants are `c₄`, `c₆` and `(c₄³ - c₆²)/1728`.
* `WeierstrassCurve.smul_ofCInvariants`: every Weierstrass equation is the
  `(b₂/12, a₁/2, a₃/2)`-transform, with scaling factor `1`, of the canonical equation with its own
  `c`-invariants. So the equations carrying a given pair of `c`-invariants form a single orbit
  under the changes of variables with `u = 1`.
* `WeierstrassCurve.map_ofCInvariants`, `WeierstrassCurve.baseChange_ofCInvariants` and
  `WeierstrassCurve.ofCInvariants_equation_iff`: the same transport and equation API that
  `shortCurve` carries, phrased on the canonical equation.

The classical discriminant `-16(4A³ + 27B²)` is *not* restated: it is Mathlib's `Δ_of_isShortNF`,
which the instance below makes applicable and the coefficient lemmas reduce.

This is a prerequisite of the Nagell–Lutz milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose classical statement is about this curve and its discriminant.

## Provenance

Adapted from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
`LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`: `shortCurveZ` (`:30`), `shortCurveQ` (`:34`),
`shortCurveQ_equation_iff` (`:58`) and `shortCurveZ_delta` (`:63`, not ported — see above).

Three departures. The source fixes `ℤ` and `ℚ`; here the construction needs only `Zero R`
(`WeierstrassCurve` is a bare structure), and `map_shortCurve` relates the two — so the `ℤ → ℚ`
pair of the classical statement is one definition plus a base change, not two definitions.
The source's ten
`@[simp]` coefficient lemmas — `shortCurve{Z,Q}_a₁` through `_a₆` — collapse to five, one per
coefficient, because the ℤ and ℚ copies become one general statement that `map_shortCurve`
transports to any base change. And `shortCurveZ_delta` is not ported at all: it is exactly
Mathlib's `Δ_of_isShortNF`, `W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`, which the coefficient
lemmas above already reduce at `shortCurve A B`.
-/

public section

namespace WeierstrassCurve

section Zero

variable {R : Type*} [Zero R] (A B : R)

/-- The short Weierstrass curve `y² = x³ + Ax + B`. Only `Zero R` is needed to write it down;
`WeierstrassCurve` is a bare structure and the three vanishing coefficients are the only
requirement. -/
def shortCurve : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

@[simp] lemma shortCurve_a₁ : (shortCurve A B).a₁ = 0 := (rfl)

@[simp] lemma shortCurve_a₂ : (shortCurve A B).a₂ = 0 := (rfl)

@[simp] lemma shortCurve_a₃ : (shortCurve A B).a₃ = 0 := (rfl)

@[simp] lemma shortCurve_a₄ : (shortCurve A B).a₄ = A := (rfl)

@[simp] lemma shortCurve_a₆ : (shortCurve A B).a₆ = B := (rfl)

end Zero

variable {R S : Type*} [CommRing R] [CommRing S] (A B : R)

/-- `shortCurve A B` is in short normal form. This instance is the point of the definition: it
hands the curve to Mathlib's whole `*_of_isShortNF` family, so every invariant — the `b`- and
`c`-families, `Δ` and `j` — comes for free rather than being restated here. -/
instance instIsShortNFShortCurve : (shortCurve A B).IsShortNF := ⟨(rfl), (rfl), (rfl)⟩

/-- A ring hom carries `shortCurve` to `shortCurve` on the images of the coefficients. Mathlib has
no instance propagating `IsShortNF` along `map`, so this is what keeps a base change — `ℤ → ℚ` in
the classical Nagell–Lutz statement — recognisably in short form. -/
@[simp] lemma map_shortCurve (f : R →+* S) : (shortCurve A B).map f = shortCurve (f A) (f B) := by
  ext <;> simp [WeierstrassCurve.map]

/-- The same statement for a base change, which is the spelling consumers actually meet.
`baseChange` *is* `map (algebraMap R S)` by definition, which is why the proof below is just
`map_shortCurve` at that hom.

It is nonetheless worth stating and tagging `@[simp]`: `simp` does not automatically unfold
`baseChange`, which carries no simp lemma of its own, so `map_shortCurve` never fires on a
`baseChange` spelling. This lemma is that missing normalisation step, not a wrapper to name by
hand. -/
@[simp] lemma baseChange_shortCurve [Algebra R S] :
    (shortCurve A B).baseChange S = shortCurve (algebraMap R S A) (algebraMap R S B) :=
  map_shortCurve A B _

/-- A point lies on `y² = x³ + Ax + B` exactly when it satisfies that equation. -/
@[simp] lemma shortCurve_equation_iff (x y : R) :
    (shortCurve A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  rw [Affine.equation_iff]
  simp [shortCurve]

/-- A curve in short normal form is `shortCurve` of its own `a₄` and `a₆`. This is how a statement
about an arbitrary `[W.IsShortNF]` reaches the explicit `y² = x³ + Ax + B` shape and the
`shortCurve` API. -/
@[simp] lemma shortCurve_a₄_a₆ (W : WeierstrassCurve R) [W.IsShortNF] :
    shortCurve W.a₄ W.a₆ = W := by
  ext <;> simp

/-- The scaling `(x, y) ↦ (u²x, u³y)`, the change of variables `⟨u, 0, 0, 0⟩`, carries
`y² = x³ + Ax + B` to `y² = x³ + u⁻⁴Ax + u⁻⁶B`. -/
@[simp] lemma smul_shortCurve (u : Rˣ) :
    (⟨u, 0, 0, 0⟩ : VariableChange R) • shortCurve A B =
      shortCurve (u⁻¹ ^ 4 * A) (u⁻¹ ^ 6 * B) := by
  ext <;> simp [variableChange_def]

section CInvariants

variable {K : Type*} [Field K]

/-- **The Weierstrass equation with prescribed `c`-invariants**, `y² = x³ - (c₄/48)x - c₆/864`.
Over a field in which `2` and `3` are invertible its `c`-invariants are exactly `c₄` and `c₆`
(`ofCInvariants_c₄` and `ofCInvariants_c₆`), and every equation with those invariants is obtained
from it by a change of variables with `u = 1` (`smul_ofCInvariants`). It is therefore the
canonical representative of a pair of invariants: the equation one starts from when asking
whether the pair is realised over a subring, and whose transforms are the equations to test for
integrality there. -/
def ofCInvariants (c₄ c₆ : K) : WeierstrassCurve K :=
  shortCurve (-c₄ / 48) (-c₆ / 864)

/-- The canonical equation of a pair of `c`-invariants, unfolded to its `shortCurve` spelling.
This is the bridge to the `shortCurve` API and, through it, to the `IsShortNF` instance: no such
instance is registered for `ofCInvariants` itself, because it would put Mathlib's `@[simp]` lemma
`c₄_of_isCharNeTwoNF` in competition with `ofCInvariants_c₄` below, and `simp` would expand
`(ofCInvariants c₄ c₆).c₄` back into coefficients instead of returning `c₄`. Rewriting with this
lemma hands the instance over on demand. -/
lemma ofCInvariants_eq_shortCurve (c₄ c₆ : K) :
    ofCInvariants c₄ c₆ = shortCurve (-c₄ / 48) (-c₆ / 864) := (rfl)

@[simp] lemma ofCInvariants_a₁ (c₄ c₆ : K) : (ofCInvariants c₄ c₆).a₁ = 0 := (rfl)

@[simp] lemma ofCInvariants_a₂ (c₄ c₆ : K) : (ofCInvariants c₄ c₆).a₂ = 0 := (rfl)

@[simp] lemma ofCInvariants_a₃ (c₄ c₆ : K) : (ofCInvariants c₄ c₆).a₃ = 0 := (rfl)

@[simp] lemma ofCInvariants_a₄ (c₄ c₆ : K) : (ofCInvariants c₄ c₆).a₄ = -c₄ / 48 := (rfl)

@[simp] lemma ofCInvariants_a₆ (c₄ c₆ : K) : (ofCInvariants c₄ c₆).a₆ = -c₆ / 864 := (rfl)

/-- A field hom carries the canonical equation of a pair to the canonical equation of the image
pair: the denominators `48` and `864` transport. -/
@[simp] lemma map_ofCInvariants {L : Type*} [Field L] (f : K →+* L) (c₄ c₆ : K) :
    (ofCInvariants c₄ c₆).map f = ofCInvariants (f c₄) (f c₆) := by
  simp [ofCInvariants_eq_shortCurve, map_div₀, map_ofNat]

/-- The same statement for a base change, which is the spelling consumers actually meet; `simp`
does not unfold `baseChange`, so `map_ofCInvariants` never fires on it by itself. -/
@[simp] lemma baseChange_ofCInvariants {L : Type*} [Field L] [Algebra K L] (c₄ c₆ : K) :
    (ofCInvariants c₄ c₆).baseChange L =
      ofCInvariants (algebraMap K L c₄) (algebraMap K L c₆) :=
  map_ofCInvariants _ c₄ c₆

/-- A point lies on the canonical equation of `(c₄, c₆)` exactly when it satisfies
`y² = x³ - (c₄/48)x - c₆/864`. -/
@[simp] lemma ofCInvariants_equation_iff (c₄ c₆ x y : K) :
    (ofCInvariants c₄ c₆).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - c₄ / 48 * x - c₆ / 864 := by
  rw [ofCInvariants_eq_shortCurve, shortCurve_equation_iff, neg_div, neg_div]
  ring_nf

variable [Invertible (2 : K)] [Invertible (3 : K)]

variable (c₄ c₆ : K)

/-- The `c₄` of the canonical equation with prescribed `c`-invariants is the prescribed one. -/
@[simp] lemma ofCInvariants_c₄ : (ofCInvariants c₄ c₆).c₄ = c₄ := by
  have h48 : (48 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 4) (n := 1) (by norm_num)
  rw [ofCInvariants_eq_shortCurve, c₄_of_isShortNF, shortCurve_a₄]
  field_simp

/-- The `c₆` of the canonical equation with prescribed `c`-invariants is the prescribed one. -/
@[simp] lemma ofCInvariants_c₆ : (ofCInvariants c₄ c₆).c₆ = c₆ := by
  have h864 : (864 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 5) (n := 3) (by norm_num)
  rw [ofCInvariants_eq_shortCurve, c₆_of_isShortNF, shortCurve_a₆]
  field_simp

/-- **Every Weierstrass equation is a translate of the canonical equation with its own
`c`-invariants.** The change of variables exhibited here takes the scaling factor to be `u = 1`;
sharing `c₄` and `c₆` does not by itself force that choice, since `u = -1` scales `c₄` by `u⁻⁴ = 1`
and `c₆` by `u⁻⁶ = 1` as well. Once `u = 1` is fixed, `(r, s, t) = (b₂/12, a₁/2, a₃/2)` is the only
triple returning the coefficients `a₁`, `a₂`, `a₃` of `W` from the vanishing ones of
`ofCInvariants`.

Mathlib's `WeierstrassCurve.toShortNF` makes the opposite move, carrying `W` to *a* short
equation, also with scaling factor `1`. This lemma is that move inverted and written out, which
is what a statement phrased on the pair `(c₄, c₆)` rather than on a curve in hand needs. -/
@[simp] lemma smul_ofCInvariants (W : WeierstrassCurve K) :
    (⟨1, W.b₂ / 12, W.a₁ / 2, W.a₃ / 2⟩ : VariableChange K) • ofCInvariants W.c₄ W.c₆ = W := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have h12 : (12 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 2) (n := 1) (by norm_num)
  have h48 : (48 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 4) (n := 1) (by norm_num)
  have h864 : (864 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 5) (n := 3) (by norm_num)
  ext <;>
    simp only [variableChange_def, ofCInvariants_eq_shortCurve, shortCurve_a₁, shortCurve_a₂,
      shortCurve_a₃, shortCurve_a₄, shortCurve_a₆, c₄, c₆, b₂, b₄, b₆, inv_one, Units.val_one,
      one_pow, one_mul] <;>
    field_simp <;>
    ring

/-- The discriminant attached to a pair of `c`-invariants, `(c₄³ - c₆²)/1728`. -/
@[simp] lemma ofCInvariants_Δ : (ofCInvariants c₄ c₆).Δ = (c₄ ^ 3 - c₆ ^ 2) / 1728 := by
  have h1728 : (1728 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 6) (n := 3) (by norm_num)
  rw [eq_div_iff h1728, mul_comm, c_relation, ofCInvariants_c₄, ofCInvariants_c₆]

end CInvariants

end WeierstrassCurve
