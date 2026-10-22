/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

-- Proof-only: membership in the ideal of a point, as a span of two polynomials.
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Ideals of points of a Weierstrass curve

For a point `(x, y)` on an affine Weierstrass curve `W` over a field, Mathlib's
`CoordinateRing.XYIdeal W x (C y)` is the ideal `⟨X - x, Y - y⟩` of the coordinate ring, and
`CoordinateRing.quotientXYIdealEquiv` identifies the quotient by it with the base field. This file
records the consequences: that ideal is maximal, it is nonzero, and it determines the coordinates
it was built from. Conversely, every ideal whose quotient has rank one over the base field is the
ideal of a point.

Evaluation kernels identify point ideals over any commutative base ring, and equality of point
ideals determines their coordinates over any such ring. Maximality and the classification by
residue degree below require a field.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot`: `XYIdeal W x y` is nonzero, over
  any nontrivial commutative base.
* `WeierstrassCurve.Affine.CoordinateRing.mk_mem_XYIdeal_iff`: a class lies in `XYIdeal W x y`
  exactly when its representative vanishes at `(x, y.eval x)`, over any commutative base ring.
* `WeierstrassCurve.Affine.CoordinateRing.mk_mem_XYIdeal_iff_of_ne_top`: over a field,
  properness of the ideal suffices for the same membership test.
* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal`: `XYIdeal W x y` is maximal
  for any `y : F[X]` solving the Weierstrass equation at `x`, matching the generality of
  `XYIdeal` and `quotientXYIdealEquiv` themselves.
* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`: the point case,
  `XYIdeal W x (C y)` for `(x, y)` on `W`.
* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff_of_ne_top`: two such ideals are
  equal exactly when `x₁ = x₂` and the two `Y`-polynomials agree at the point,
  `y₁.eval x₁ = y₂.eval x₂`, as soon as the first is proper.
* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff`: equality of polynomial point ideals
  determines `x` and `y.eval x`, over any commutative base ring, given the first curve equation.
* `WeierstrassCurve.Affine.CoordinateRing.finrank_quotient_eq_one_iff`: an ideal has a
  rank-one quotient exactly when it is `XYIdeal W x (C y)` for a solution `(x, y)` of the
  Weierstrass equation.
* `WeierstrassCurve.Affine.CoordinateRing.ker_evalAlgHom_eq_XYIdeal`: the kernel of evaluation
  at a point is the ideal of that point.
* `WeierstrassCurve.Affine.CoordinateRing.mem_XYIdeal_iff_evalAlgHom_eq_zero`: its elementwise
  form, a function lying in the ideal exactly when it vanishes at the point.

Mathlib has the quotient isomorphism but records nothing about the ideal itself; the many `XYIdeal`
lemmas it does state (`XYIdeal_eq₁`, `XYIdeal_eq₂`, `XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul`) are
all about products and rewriting, not about the ideal's place in the spectrum. It does record that
the two generators are nonzero (`XClass_ne_zero`, `YClass_ne_zero`), which is what `XYIdeal_ne_bot`
rests on.

Only the curve equation is needed, not nonsingularity: the quotient is the base field either way.

Evaluation at a point of the curve is an `F`-algebra map out of the coordinate ring whose kernel
is that point's ideal, so a function lies in the ideal exactly when it vanishes at the point. The
membership test detects that vanishing and nothing finer — the order of vanishing is a fact about
the valuation, not about the ideal — and it is what identifies the residue-degree-one ideals with
points below.

For an elliptic curve over a field, the affine places are the maximal ideals of its coordinate
ring. Maximality of `XYIdeal` sends a point to a place, `XYIdeal_eq_iff` says that map is
injective, and `finrank_quotient_eq_one_iff` classifies the ideals with residue degree one.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/Basic.lean`, declaration
`maximalIdealAt_isMaximal`. The two `XYIdeal_eq_iff` lemmas are not in the source.

Changes from the source. There the ideal is reached through a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine` and a `SmoothPoint` structure bundling the coordinates with their
nonsingularity proof; the surrounding wrappers are not ported, and the statement is made directly
about Mathlib's `XYIdeal`. The hypothesis is correspondingly weakened from nonsingularity to the
curve equation, which is all the quotient isomorphism consumes.

The classification has a counterpart in the same project, in
`projects/HasseWeil/HasseWeil/Foundation/Curves/Valuation/NormValuation.lean` at
`github.com/CBirkbeck/AINTLIB @ 1c1c74664e40` (Apache-2.0 per that file's header;
Authors: Chris Birkbeck): `exists_coordinates_of_isMaximal_of_surjective`,
`equation_of_coordinates_of_field` and `exists_smoothPoint_of_isMaximal_of_surjective`, packaged
in `Valuation/SmoothPointPrime.lean` as `smoothPointEquivHeightOneSpectrum`. That statement is
about a *maximal* ideal of the coordinate ring of a `SmoothPlaneCurve`, hypothesises surjectivity
of `algebraMap F (F[C] ⧸ M)`, and assumes ellipticity throughout. The classification below is
written directly against Mathlib's `XYIdeal`: its hypothesis is the residue degree and it uses no
ellipticity or Dedekind assumption.

-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace TauCeti

section

section CommRing

variable {R : Type*} [CommRing R] {W : _root_.WeierstrassCurve.Affine R}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is nonzero** over a nontrivial base. -/
@[simp]
lemma _root_.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot [Nontrivial R]
    (x : R) (y : R[X]) : CoordinateRing.XYIdeal W x y ≠ ⊥ := fun hbot => by
  have hmem : CoordinateRing.XClass W x ∈ CoordinateRing.XYIdeal W x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact CoordinateRing.XClass_ne_zero x hmem

/-- **A class lies in the ideal of a point exactly when its representative vanishes there.**
The polynomial generator `Y - y(X)` evaluates at `x` to the coordinate `y.eval x`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.mk_mem_XYIdeal_iff
    {x : R} {y : R[X]} (h : (W.polynomial.eval y).eval x = 0) (p : R[X][Y]) :
    CoordinateRing.mk W p ∈ CoordinateRing.XYIdeal W x y ↔ (p.eval y).eval x = 0 := by
  -- The curve relation lies in the polynomial point ideal, so quotienting preserves membership.
  have hle : Ideal.span {W.polynomial} ≤ Ideal.span {C (X - C x), Y - C y} :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h)
  rw [CoordinateRing.XYIdeal, CoordinateRing.XClass, CoordinateRing.YClass,
    ← Set.image_pair, ← Ideal.map_span]
  exact (Ideal.mem_quotient_iff_mem hle).trans
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero

section EvalKernel

variable {R : Type*} [CommRing R] {W : _root_.WeierstrassCurve.Affine R} {x : R}

/-- **The kernel of evaluation at a point is the ideal of that point.** The evaluation map
`W.CoordinateRing →ₐ[R] R` at a solution `(x, y)` of the Weierstrass equation has kernel
`⟨X - x, Y - y⟩`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.ker_evalAlgHom_eq_XYIdeal {y : R}
    (h : (W⁄R).toAffine.Equation x y) :
    RingHom.ker (CoordinateRing.evalAlgHom h : W.CoordinateRing →+* R) =
      CoordinateRing.XYIdeal W x (C y) := by
  have hself : (W⁄R) = W := WeierstrassCurve.map_id W
  have h' : W.Equation x y := by rw [← hself]; exact h
  ext f
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective f
  rw [RingHom.mem_ker, RingHom.coe_coe, CoordinateRing.evalAlgHom_mk,
    CoordinateRing.mk_mem_XYIdeal_iff h']
  simp only [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

/-- **A function lies in the ideal of a point exactly when it vanishes there**, the elementwise
form of `ker_evalAlgHom_eq_XYIdeal`.

Not `@[simp]`: `AlgHom.toRingHom_eq_coe` rewrites the left-hand side of the kernel equality this
rests on, and `simpNF` rejects the pair. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.mem_XYIdeal_iff_evalAlgHom_eq_zero {y : R}
    (h : (W⁄R).toAffine.Equation x y) {f : W.CoordinateRing} :
    f ∈ CoordinateRing.XYIdeal W x (C y) ↔ CoordinateRing.evalAlgHom h f = 0 := by
  rw [← CoordinateRing.ker_evalAlgHom_eq_XYIdeal h, RingHom.mem_ker, RingHom.coe_coe]

end EvalKernel

/-- **The ideal of a point determines its coordinates** over any commutative base ring.
For polynomial generators, the second coordinate is `y.eval x`; the first pair must satisfy the
curve equation. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff
    {x₁ x₂ : R} {y₁ y₂ : R[X]} (h₁ : (W.polynomial.eval y₁).eval x₁ = 0) :
    CoordinateRing.XYIdeal W x₁ y₁ = CoordinateRing.XYIdeal W x₂ y₂ ↔
      x₁ = x₂ ∧ y₁.eval x₁ = y₂.eval x₂ := by
  constructor
  · intro h
    have hx : CoordinateRing.XClass W x₂ ∈ CoordinateRing.XYIdeal W x₁ y₁ :=
      h ▸ Ideal.subset_span (Set.mem_insert _ _)
    have hy : CoordinateRing.YClass W y₂ ∈ CoordinateRing.XYIdeal W x₁ y₁ :=
      h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    rw [CoordinateRing.XClass, CoordinateRing.mk_mem_XYIdeal_iff h₁] at hx
    rw [CoordinateRing.YClass, CoordinateRing.mk_mem_XYIdeal_iff h₁] at hy
    simp only [eval_C, eval_sub, eval_X, sub_eq_zero] at hx hy
    exact ⟨hx, by rw [← hx]; exact hy⟩
  · rintro ⟨rfl, hy⟩
    simp only [CoordinateRing.XYIdeal, CoordinateRing.XClass, CoordinateRing.YClass,
      ← Set.image_pair, ← Ideal.map_span]
    congr 1
    ext p
    simp only [mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero]
    have heval (y : R[X]) : (p.eval y).eval x₁ = p.eval₂ (evalRingHom x₁) (y.eval x₁) :=
      (eval₂_at_apply (evalRingHom x₁) y).symm
    rw [heval, heval, hy]

end CommRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is maximal** whenever `y` is a
polynomial solving the Weierstrass equation at `x`. Equivalently, the quotient by it is the base
field. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal
    {y : F[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (CoordinateRing.XYIdeal W x y).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((CoordinateRing.quotientXYIdealEquiv h).toRingEquiv.isField (Field.toIsField F))

/-- **The ideal of a point of a Weierstrass curve is maximal**, the constant-polynomial case of
`XYIdeal_isMaximal`. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
    {y : F} (h : W.Equation x y) :
    (CoordinateRing.XYIdeal W x (C y)).IsMaximal :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal h

/-- **A class lies in a proper polynomial point ideal exactly when its representative vanishes
there.** Over a field, properness already forces the coordinates to satisfy the curve equation. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.mk_mem_XYIdeal_iff_of_ne_top
    {y : F[X]} (hI : CoordinateRing.XYIdeal W x y ≠ ⊤) (p : F[X][Y]) :
    CoordinateRing.mk W p ∈ CoordinateRing.XYIdeal W x y ↔ (p.eval y).eval x = 0 := by
  let J : Ideal F[X][Y] := Ideal.span {C (X - C x), Y - C y}
  have hmap : J.map (CoordinateRing.mk W) = CoordinateRing.XYIdeal W x y := by
    rw [Ideal.map_span, Set.image_pair]
    rfl
  have : J.IsMaximal := Ideal.Quotient.maximal_of_isField _
    ((quotientSpanCXSubCXSubCAlgEquiv (x := x) (y := y)).toRingEquiv.isField (Field.toIsField F))
  -- A maximal ideal remains unchanged under extension and contraction when its image is proper.
  have hcomap := Ideal.comap_map_eq_self_of_isMaximal (CoordinateRing.mk W) (hmap ▸ hI)
  rw [← hmap, ← Ideal.mem_comap, hcomap]
  exact mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero

/-- **Two such ideals are equal exactly when their data agree at the point**, given only that the
first is proper: the `X`-coordinates must coincide, and the two `Y`-polynomials must take the same
value there. Stated for polynomial `y`, matching `XYIdeal` and `XYIdeal_isMaximal`; no curve
equation is needed. Use `XYIdeal_eq_iff` when the curve equation is available instead. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff_of_ne_top
    {x₁ x₂ : F} {y₁ y₂ : F[X]}
    (hI : CoordinateRing.XYIdeal W x₁ y₁ ≠ ⊤) :
    CoordinateRing.XYIdeal W x₁ y₁ = CoordinateRing.XYIdeal W x₂ y₂ ↔
      x₁ = x₂ ∧ y₁.eval x₁ = y₂.eval x₂ := by
  apply CoordinateRing.XYIdeal_eq_iff
  exact (CoordinateRing.mk_mem_XYIdeal_iff_of_ne_top hI W.polynomial).mp (by
    rw [AdjoinRoot.mk_self]
    exact Ideal.zero_mem _)

/-- **The ideals of residue degree one are exactly the ideals of points.** An ideal `I` has a
rank-one quotient over `F` if and only if it is `XYIdeal W x (C y)` for some solution `(x, y)` of
the Weierstrass equation. No ellipticity or Dedekind hypothesis is involved. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.finrank_quotient_eq_one_iff
    {I : Ideal W.CoordinateRing} :
    Module.finrank F (W.CoordinateRing ⧸ I) = 1 ↔
      ∃ x y : F, W.Equation x y ∧ I = CoordinateRing.XYIdeal W x (C y) := by
  constructor
  · intro hdeg
    have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ I)) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg
    let e : (W.CoordinateRing ⧸ I) ≃ₐ[F] F :=
      (AlgEquiv.ofBijective (Algebra.ofId F _) hbij).symm
    let ρ : W.CoordinateRing →ₐ[F] F := e.toAlgHom.comp (Ideal.Quotient.mkₐ F I)
    have hρmem : ∀ a, ρ a = 0 ↔ a ∈ I := fun a ↦ by
      simp only [ρ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk]
      rw [map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
    -- `ρ` is evaluation at the images of the two coordinate functions, so its kernel is the
    -- ideal of that point; and its kernel is `I`.
    have hker := WeierstrassCurve.Affine.CoordinateRing.ker_evalAlgHom_eq_XYIdeal
      (_root_.WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom ρ)
    rw [_root_.WeierstrassCurve.Affine.CoordinateRing.evalAlgHom_equation_ofAlgHom] at hker
    have hIker : I = RingHom.ker (ρ : W.CoordinateRing →+* F) :=
      Ideal.ext fun a ↦ by simpa only [RingHom.mem_ker, RingHom.coe_coe] using (hρmem a).symm
    have heq : W.Equation (ρ (AdjoinRoot.of W.polynomial X))
        (ρ (AdjoinRoot.root W.polynomial)) := by
      simpa only [Algebra.algebraMap_self, _root_.WeierstrassCurve.baseChange,
        _root_.WeierstrassCurve.map_id] using
        _root_.WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom ρ
    exact ⟨_, _, heq, hIker.trans hker⟩
  · rintro ⟨x, y, h, rfl⟩
    rw [(CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

end

end TauCeti

end
