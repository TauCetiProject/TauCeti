/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Data.EReal.Operations

/-!
# The Legendre–Fenchel conjugate on a real dual pair

Let `E` and `F` be real vector spaces paired by a bilinear form `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, written
`⟪x, y⟫ = B x y`. The *Legendre–Fenchel conjugate* of an extended-real function `f : E → EReal` is
the function

`f⋆ y = ⨆ x, (⟪x, y⟫ - f x)`

on `F`. It is the basic operation of convex analysis: it turns a function into the supremum of
the affine functions `y ↦ ⟪x, y⟫ - f x` indexed by the points of `E`, so whatever `f` is, it is
convex, and it is lower semicontinuous for any topology on `F` making every functional `B x`
continuous. When the pairing is separating and `E` carries a locally convex topology compatible
with it (for instance the weak topology `σ(E, F)`), the Fenchel–Moreau theorem describes the
biconjugate `f⋆⋆`. If `f` lies above some affine function `x ↦ ⟪x, y⟫ + c` (so in particular `f`
never takes the value `⊥`), then `f⋆⋆` is the largest lower-semicontinuous convex minorant of
`f`; in particular `f⋆⋆ = f` when `f` is proper, convex and lower semicontinuous. If `f` has no
such affine minorant, for instance when `f x = ⊥` at some point
(`TauCeti.fenchelConjugate_eq_top_of_eq_bot`), then `f⋆ ≡ ⊤` and `f⋆⋆ ≡ ⊥`, even though the
lower-semicontinuous convex minorants of `f` need not all be `⊥`. The theorem needs a separation
theorem and is not proved here. For a bare bilinear pairing only the inequality `f⋆⋆ ≤ f` holds
(for the zero pairing, `f⋆⋆` is the constant `⨅ x, f x`). This file contains the algebraic part
of the theory, valid on a bare dual pair:
the conjugate itself, the Fenchel–Young inequality, the antitone Galois connection between the
functions on `E` and on `F` that the conjugate and its transpose `B.flip` form, the
biconjugate inequality `f⋆⋆ ≤ f`, the triple-conjugate identity `f⋆⋆⋆ = f⋆`, the normalisation
rule for an additive constant, the convexity of every conjugate, and its lower semicontinuity
for any topology on `F` making every functional `B x` continuous.

The codomain is `EReal` throughout: the supremum defining `f⋆` can be `+∞` even for a finite `f`,
and it is `-∞` exactly when `f ≡ +∞`. The only subtraction that occurs is `⟪x, y⟫ - f x`, a real
number minus an extended real, which is always defined and never of the form `∞ - ∞`; the value
`f x = -∞` gives the term `+∞`, and `f x = +∞` gives the term `-∞`, which contributes nothing to
the supremum. Consequently every statement that adds `f x` to `f⋆ y` carries the hypotheses that
keep `⊥ + ⊤` from arising, and those hypotheses are recorded exactly rather than replaced by a
blanket properness assumption.

For a self-paired real inner product space, `B` is `innerₗ E`, whose transpose is itself, so the
two Galois-connection maps coincide.

## Main definitions

* `TauCeti.fenchelConjugate B f` — the Legendre–Fenchel conjugate `y ↦ ⨆ x, (B x y - f x)`.

## Main statements

* `TauCeti.sub_le_fenchelConjugate` and `TauCeti.le_add_fenchelConjugate` — the **Fenchel–Young
  inequality** `⟪x, y⟫ ≤ f x + f⋆ y`, in the subtraction form that needs no hypothesis and in the
  additive form that needs neither summand to be `-∞`;
* `TauCeti.fenchelConjugate_le_iff_fenchelConjugate_flip_le` and
  `TauCeti.fenchelConjugate_galoisConnection` — `f⋆ ≤ g` and `g⋆ ≤ f` both say that the pair
  `(f, g)` satisfies the Fenchel–Young inequality; the conjugate for `B` and the conjugate for
  the transposed pairing `B.flip` form an antitone Galois connection;
* `TauCeti.fenchelConjugate_flip_fenchelConjugate_le` — the biconjugate inequality `f⋆⋆ ≤ f`,
  and `TauCeti.fenchelConjugate_fenchelConjugate_flip_fenchelConjugate` — `f⋆⋆⋆ = f⋆`;
* `TauCeti.fenchelConjugate_eq_bot_iff` — `f⋆ y = -∞` exactly when `f ≡ +∞`, and
  `TauCeti.fenchelConjugate_eq_top_of_eq_bot` — `f⋆ ≡ +∞` as soon as `f` takes the value `-∞`;
* `TauCeti.fenchelConjugate_add_const` — adding a real constant to `f` subtracts it from `f⋆`;
* `TauCeti.convex_epigraph_fenchelConjugate` — the real epigraph of a conjugate is convex, and
  `TauCeti.lowerSemicontinuous_fenchelConjugate` — a conjugate is lower semicontinuous for any
  topology on `F` making every functional `B x` continuous, such as the weak topology of the
  pairing.

## Implementation notes

The conjugate is a supremum, so `f x = +∞` is harmless and `f x = -∞` is the degenerate value,
whereas for the infimal `c`-transform of optimal transport the roles of the two infinities are
exchanged. Up to the sign change `c (x, y) = -B x y` and the negation of both potentials the two
transforms agree, but the sup-based normal form is the one used throughout convex analysis and
by the differentiability theory of convex functions, so it is developed on its own terms here.
The bridge between the two is a statement about the quadratic transport cost `‖x - y‖ ^ 2 / 2`,
whose `c`-concave potentials are exactly `‖x‖ ^ 2 / 2 - u x` for `u` a conjugate
(`TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic`).

Convexity of a conjugate is stated as convexity of the real epigraph
`{p : F × ℝ | f⋆ p.1 ≤ p.2}` rather than through `ConvexOn`, whose scalar action would have to
be defined on `EReal`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §12.
* I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, Classics in Applied
  Mathematics 28, SIAM 1999, Chapter I, §4.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1, for the Legendre transform in the setting of optimal transport.
-/

public section

noncomputable section

namespace TauCeti

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- The Legendre–Fenchel conjugate of `f : E → EReal` with respect to the pairing `B`, the function
`y ↦ ⨆ x, (B x y - f x)` on `F`. The subtraction is of an extended real from a real, so it is
always defined; the supremum is `⊥` exactly when `f ≡ ⊤`, and it is `⊤` as soon as `f` takes the
value `⊥`. -/
def fenchelConjugate (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) : EReal :=
  ⨆ x, ((B x y : EReal) - f x)

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {g : F → EReal} {x : E} {y : F} {a : EReal}

/-- The defining formula for the Legendre–Fenchel conjugate. -/
theorem fenchelConjugate_apply (f : E → EReal) (y : F) :
    fenchelConjugate B f y = ⨆ x, ((B x y : EReal) - f x) := (rfl)

/-! ### The Fenchel–Young inequality -/

/-- **The Fenchel–Young inequality**, in the form that holds with no hypothesis: every point of `E`
bounds the conjugate from below. -/
theorem sub_le_fenchelConjugate (f : E → EReal) (x : E) (y : F) :
    (B x y : EReal) - f x ≤ fenchelConjugate B f y :=
  le_iSup (fun x => (B x y : EReal) - f x) x

/-- An upper bound for the conjugate at a point is an upper bound for every term of the
supremum. -/
theorem fenchelConjugate_le_iff :
    fenchelConjugate B f y ≤ a ↔ ∀ x, (B x y : EReal) - f x ≤ a :=
  iSup_le_iff

/-- A bound valid for every term of the supremum bounds the conjugate. -/
theorem fenchelConjugate_le (h : ∀ x, (B x y : EReal) - f x ≤ a) : fenchelConjugate B f y ≤ a :=
  iSup_le h

/-- The conjugate is `⊤` everywhere as soon as `f` takes the value `⊥` somewhere. -/
theorem fenchelConjugate_eq_top_of_eq_bot (hx : f x = ⊥) (y : F) :
    fenchelConjugate B f y = ⊤ :=
  top_le_iff.1 <| by
    have h := sub_le_fenchelConjugate B f x y
    rwa [hx, EReal.coe_sub_bot] at h

/-- The conjugate takes the value `⊥` exactly when `f` is identically `⊤`. -/
@[simp]
theorem fenchelConjugate_eq_bot_iff : fenchelConjugate B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  simp only [fenchelConjugate_apply, iSup_eq_bot, sub_eq_add_neg, EReal.add_eq_bot_iff,
    EReal.coe_ne_bot, false_or, EReal.neg_eq_bot_iff]

/-- The conjugate is not `⊥` as soon as `f` is finite or `⊥` somewhere. -/
theorem fenchelConjugate_ne_bot (hx : f x ≠ ⊤) (y : F) : fenchelConjugate B f y ≠ ⊥ :=
  fun h => hx ((fenchelConjugate_eq_bot_iff B).1 h x)

/-- **The Fenchel–Young inequality** in additive form, `⟪x, y⟫ ≤ f x + f⋆ y`, valid whenever
neither summand is `⊥`; the second summand is `⊥` only when `f ≡ ⊤`. -/
theorem le_add_fenchelConjugate (hx : f x ≠ ⊥) (hy : fenchelConjugate B f y ≠ ⊥) :
    (B x y : EReal) ≤ f x + fenchelConjugate B f y := by
  rcases eq_or_ne (f x) ⊤ with hx' | hx'
  · rw [hx', EReal.top_add_of_ne_bot hy]
    exact le_top
  · rw [add_comm]
    exact (EReal.sub_le_iff_le_add (.inl hx) (.inl hx')).1 (sub_le_fenchelConjugate B f x y)

/-- The conjugate of the constant `⊤` is the constant `⊥`. -/
@[simp]
theorem fenchelConjugate_top (y : F) : fenchelConjugate B (⊤ : E → EReal) y = ⊥ :=
  (fenchelConjugate_eq_bot_iff B).2 fun _ => rfl

/-- The conjugate of the constant `⊥` is the constant `⊤`. -/
@[simp]
theorem fenchelConjugate_bot (y : F) : fenchelConjugate B (⊥ : E → EReal) y = ⊤ :=
  fenchelConjugate_eq_top_of_eq_bot B (x := 0) rfl y

/-! ### The Galois connection and the biconjugate -/

/-- `f⋆ ≤ g` and `g⋆ ≤ f`, the latter for the transposed pairing, both express the Fenchel–Young
inequality for the pair `(f, g)`, so they are equivalent, with no finiteness hypothesis. -/
theorem fenchelConjugate_le_iff_fenchelConjugate_flip_le :
    fenchelConjugate B f ≤ g ↔ fenchelConjugate B.flip g ≤ f := by
  constructor
  · intro h x
    refine fenchelConjugate_le B.flip fun y => ?_
    rw [LinearMap.flip_apply]
    exact EReal.coe_sub_le_comm.1 ((sub_le_fenchelConjugate B f x y).trans (h y))
  · intro h y
    refine fenchelConjugate_le B fun x => ?_
    have hxy := (sub_le_fenchelConjugate B.flip g y x).trans (h x)
    rw [LinearMap.flip_apply] at hxy
    exact EReal.coe_sub_le_comm.1 hxy

/-- The conjugate for `B` and the conjugate for the transposed pairing `B.flip` form an antitone
Galois connection between the functions on `E` and the functions on `F`. Order reversal, the
biconjugate inequality and the triple-conjugate identity are its standard consequences. -/
theorem fenchelConjugate_galoisConnection :
    GaloisConnection (fun g : (F → EReal)ᵒᵈ => fenchelConjugate B.flip (OrderDual.ofDual g))
      (fun f : E → EReal => OrderDual.toDual (fenchelConjugate B f)) := fun _ _ =>
  (fenchelConjugate_le_iff_fenchelConjugate_flip_le B).symm

/-- The conjugate reverses the pointwise order. -/
theorem fenchelConjugate_antitone : Antitone (fenchelConjugate B) := fun _ _ h y =>
  (fenchelConjugate_galoisConnection B).monotone_u h y

/-- **The biconjugate inequality**: `f⋆⋆ ≤ f`, where the second conjugate is taken for the
transposed pairing. -/
theorem fenchelConjugate_flip_fenchelConjugate_le (f : E → EReal) :
    fenchelConjugate B.flip (fenchelConjugate B f) ≤ f :=
  (fenchelConjugate_galoisConnection B).l_u_le f

/-- The triple conjugate is the conjugate: `f⋆⋆⋆ = f⋆`. -/
theorem fenchelConjugate_fenchelConjugate_flip_fenchelConjugate (f : E → EReal) :
    fenchelConjugate B (fenchelConjugate B.flip (fenchelConjugate B f)) =
      fenchelConjugate B f :=
  OrderDual.toDual.injective ((fenchelConjugate_galoisConnection B).u_l_u_eq_u f)

/-- Adding a real constant to a function subtracts it from the conjugate. -/
@[simp]
theorem fenchelConjugate_add_const (f : E → EReal) (r : ℝ) (y : F) :
    fenchelConjugate B (fun x => f x + (r : EReal)) y = fenchelConjugate B f y - (r : EReal) := by
  simp only [fenchelConjugate_apply]
  rw [← EReal.iSup_sub_coe]
  exact iSup_congr fun x => EReal.coe_sub_add_coe (f x) (B x y) r

/-! ### Convexity and lower semicontinuity -/

/-- The real epigraph `{(y, r) | f⋆ y ≤ r}` of a conjugate is convex: it is the intersection over
`x` of the half-spaces `{(y, r) | B x y - r ≤ f x}`, each of which is the whole space when
`f x = ⊤` and empty when `f x = ⊥`. -/
theorem convex_epigraph_fenchelConjugate (f : E → EReal) :
    Convex ℝ {p : F × ℝ | fenchelConjugate B f p.1 ≤ (p.2 : EReal)} := by
  have hset : {p : F × ℝ | fenchelConjugate B f p.1 ≤ (p.2 : EReal)} =
      ⋂ x, {p : F × ℝ | ((B x p.1 - p.2 : ℝ) : EReal) ≤ f x} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, fenchelConjugate_le_iff, EReal.coe_sub,
      EReal.coe_sub_le_comm]
  rw [hset]
  refine convex_iInter fun x => ?_
  generalize f x = z
  induction z with
  | bot =>
    simp only [le_bot_iff, EReal.coe_ne_bot, Set.ofPred_false]
    exact convex_empty
  | coe s =>
    simp only [EReal.coe_le_coe_iff]
    exact convex_halfSpace_le ((B x).comp (LinearMap.fst ℝ F ℝ) - LinearMap.snd ℝ F ℝ).isLinear s
  | top =>
    simp only [le_top, Set.ofPred_true]
    exact convex_univ

/-- A conjugate is lower semicontinuous for every topology on `F` in which each functional `B x`
is continuous, since it is a supremum of continuous or constant extended-real functions. -/
theorem lowerSemicontinuous_fenchelConjugate [TopologicalSpace F] (hB : ∀ x, Continuous (B x))
    (f : E → EReal) : LowerSemicontinuous (fenchelConjugate B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  generalize f x = z
  induction z with
  | bot =>
    simp only [EReal.coe_sub_bot]
    exact lowerSemicontinuous_const
  | coe s =>
    have hfun : (fun y => (B x y : EReal) - (s : EReal)) = fun y => ((B x y - s : ℝ) : EReal) :=
      funext fun y => (EReal.coe_sub _ _).symm
    rw [hfun]
    exact (continuous_coe_real_ereal.comp ((hB x).sub continuous_const)).lowerSemicontinuous
  | top =>
    simp only [EReal.sub_top]
    exact lowerSemicontinuous_const

end TauCeti

end

end
