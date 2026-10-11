/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.DegreeOne
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Relative effective Cartier divisors of degree zero and one are representable

Let `f : X ⟶ S` be a proper family of curves. The symmetric power `Symᵈ X` should represent the
functor `Div^d_{X/S}` of relative effective Cartier divisors of degree `d`. This file proves the
two cases `d = 0` and `d = 1`, where `Sym⁰ X = S` and `Sym¹ X = X`.

* **Degree zero.** A relative effective Cartier divisor `D` on `X_T` over `T` is finite flat over
  `T`, and its rank vanishes exactly off its image. So `D` has degree zero exactly when it is
  empty, and `Div⁰_{X/S}` is the one-point functor, represented by `S`.
* **Degree one.** When `f` is moreover smooth of relative dimension one, sending a `T`-point `x`
  of `X` over `S` to its graph `Γₓ ⊆ X_T` is a natural transformation `graphDivisor` from the
  functor of points of `X` to `Div_{X/S}`. It is injective, and its image is exactly `Div¹_{X/S}`
  (a degree-one divisor is the image of a unique section of `X_T ⟶ T`). So it corestricts to a
  natural isomorphism `Hom_S(-, X) ≅ Div¹_{X/S}`, and `X` represents `Div¹_{X/S}`.

## Main declarations

* `TauCeti.AlgebraicGeometry.mem_relativeEffectiveCartierDegreeSubfunctor_zero_obj_iff`: the
  divisors of degree zero are the empty divisor;
* the instances `Unique` on the values of `Div⁰_{X/S}` and
  `(relativeEffectiveCartierDegreeSubfunctor f 0).toFunctor.IsRepresentable`;
* `TauCeti.AlgebraicGeometry.range_graphDivisor`: the image of the graph divisor is
  `Div¹_{X/S}`;
* `TauCeti.AlgebraicGeometry.graphDivisorDegreeOne`: the graph divisor as a natural
  transformation `Hom_S(-, X) ⟶ Div¹_{X/S}`, which is an isomorphism;
* `TauCeti.AlgebraicGeometry.graphDivisorDegreeOne_app_basePoint`: under it, the base point
  given by a section `x₀` corresponds to the degree-one divisor `x₀_T` on every base change;
* the instance `(relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor.IsRepresentable`.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3.
* The Stacks Project, *Picard Schemes of Curves*, section *Moduli of divisors on smooth curves*.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [RelativeDimensionLE 1 f]

section DegreeZero

/-- **The only divisor of degree zero is the empty divisor.** For a proper `f : X ⟶ S` with
fibres of dimension at most one, a relative effective Cartier divisor on `X_T` over `T` has
degree zero exactly when it is the empty divisor `⊤`. -/
lemma mem_relativeEffectiveCartierDegreeSubfunctor_zero_obj_iff {T : (Over S)ᵒᵖ}
    {D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T} :
    D ∈ (relativeEffectiveCartierDegreeSubfunctor f 0).obj T ↔
      D.1 = (⊤ : (pullback T.unop.hom f).IdealSheafData) := by
  have hD := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.2
  have : Flat (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hD.flat
  have : IsFinite (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hD.isFinite
  -- Both sides say that the closed subscheme of `D` is empty.
  have h (I : (pullback T.unop.hom f).IdealSheafData) : I = ⊤ ↔ IsEmpty I.subscheme := by
    rw [← I.subschemeι.ker_eq_top_iff_isEmpty, I.ker_subschemeι]
  refine Iff.trans ?_ (h D.1).symm
  simp only [mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff, funext_iff,
    Scheme.Hom.finrank_eq_zero_iff_notMem_range, Set.mem_range, not_exists]
  exact ⟨fun H ↦ ⟨fun x ↦ H _ x rfl⟩, fun H _ x ↦ H.elim x⟩

/-- On every base change, the empty divisor is the unique divisor of degree zero. -/
instance (T : (Over S)ᵒᵖ) :
    Unique ((relativeEffectiveCartierDegreeSubfunctor f 0).toFunctor.obj T) where
  default := ⟨⟨(⊤ : (pullback T.unop.hom f).IdealSheafData),
      top_mem_relativeEffectiveCartierSubfunctor_obj f T⟩,
    (mem_relativeEffectiveCartierDegreeSubfunctor_zero_obj_iff f).mpr rfl⟩
  uniq D := Subtype.ext <| Subtype.ext <|
    (mem_relativeEffectiveCartierDegreeSubfunctor_zero_obj_iff f).mp D.2

/-- **`S` represents `Div⁰_{X/S}`**: the functor of divisors of degree zero is represented by the
terminal object `S` of the category of `S`-schemes. -/
instance : (relativeEffectiveCartierDegreeSubfunctor f 0).toFunctor.IsRepresentable :=
  Functor.RepresentableBy.isRepresentable (Y := Over.mk (𝟙 S))
    { homEquiv := Equiv.ofBijective (fun _ ↦ default)
        ⟨fun _ _ _ ↦ Over.mkIdTerminal.hom_ext _ _,
          fun _ ↦ ⟨Over.mkIdTerminal.from _, Subsingleton.elim _ _⟩⟩
      homEquiv_comp _ _ := Subsingleton.elim _ _ }

end DegreeZero

section DegreeOne

variable [SmoothOfRelativeDimension 1 f]

/-- **The graphs of points are exactly the divisors of degree one**: for a smooth proper `f` of
relative dimension one, the image of the graph divisor `Hom_S(-, X) ⟶ Div_{X/S}` is the
subfunctor `Div¹_{X/S}` of relative effective Cartier divisors of degree one. -/
theorem range_graphDivisor :
    Subfunctor.range (graphDivisor f) = relativeEffectiveCartierDegreeSubfunctor f 1 := by
  have := SmoothOfRelativeDimension.smooth 1 f
  ext T D
  have hD := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.2
  simp only [Subfunctor.range_obj, Set.mem_range,
    mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff]
  rw [← Pi.one_def, ← exists_ker_graphSection_eq_iff_finrank_eq_one hD]
  refine exists_congr fun x ↦ ?_
  rw [Subtype.ext_iff, graphDivisor_app_apply_val]
  -- The two sides differ only in how the type of ideal sheaves on `X_T` is written:
  -- `(baseChangeIdealSheafFunctor f).obj T` against `(pullback T.unop.hom f).IdealSheafData`,
  -- which agree by `baseChangeIdealSheafFunctor_obj`.
  exact Iff.rfl

/-- The **graph divisor of degree one**: for a smooth proper `f : X ⟶ S` of relative dimension
one, the natural transformation from the functor of points `T ↦ Hom_S(T, X)` of `X` to the
functor `Div¹_{X/S}` of relative effective Cartier divisors of degree one, sending a `T`-point to
its graph. It is an isomorphism, so `X` represents `Div¹_{X/S}`. -/
def graphDivisorDegreeOne :
    yoneda.obj (Over.mk f) ⟶ (relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor :=
  Subfunctor.lift (graphDivisor f) (range_graphDivisor f).le

/-- Composing the graph divisor of degree one with the inclusion `Div¹_{X/S} ⟶ Div_{X/S}` gives
the graph divisor. -/
@[reassoc (attr := simp)]
lemma graphDivisorDegreeOne_ι :
    graphDivisorDegreeOne f ≫ (relativeEffectiveCartierDegreeSubfunctor f 1).ι = graphDivisor f :=
  Subfunctor.lift_ι _ _

-- As for `graphDivisor_app_apply_val`, the source and target are spelled out in their
-- simp-normal form, so that the left-hand side passes the `simpNF` linter.
/-- The divisor underlying the graph divisor of degree one of `x` is the graph divisor of `x`. -/
@[simp]
lemma graphDivisorDegreeOne_app_apply_val {T : (Over S)ᵒᵖ} (x : T.unop ⟶ Over.mk f) :
    (ConcreteCategory.hom (C := Type u) (X := T.unop ⟶ Over.mk f)
      (Y := (relativeEffectiveCartierDegreeSubfunctor f 1).obj T)
      ((graphDivisorDegreeOne f).app T) x).1 = (graphDivisor f).app T x :=
  (rfl)

/-- **`X` represents `Div¹_{X/S}`**: the graph divisor of degree one is an isomorphism. -/
instance : IsIso (graphDivisorDegreeOne f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨fun x y h ↦ graphDivisor_app_injective T (congrArg Subtype.val h), fun D ↦ ?_⟩
  obtain ⟨x, hx⟩ := (range_graphDivisor f).ge T D.2
  exact ⟨x, Subtype.ext hx⟩

/-- **`X` represents `Div¹_{X/S}`**, through the graph divisor of degree one. -/
instance : (relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor.IsRepresentable :=
  .mk' (asIso (graphDivisorDegreeOne f))

/-- Under the isomorphism `Hom_S(-, X) ≅ Div¹_{X/S}`, the base point `T ⟶ S ⟶ X` given by a
section `x₀` of `f` corresponds to the degree-one divisor of the base-changed section
`x₀_T : T ⟶ X_T`. -/
lemma graphDivisorDegreeOne_app_basePoint {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S) (T : Over S) :
    (graphDivisorDegreeOne f).app (op T) (basePoint hx₀ T) =
      relativeEffectiveCartierDegreeOneSection f x₀ hx₀ (op T) :=
  Subtype.ext <| Subtype.ext <| by
    rw [graphDivisorDegreeOne_app_apply_val, graphDivisor_app_apply_val, graphSection_basePoint,
      relativeEffectiveCartierDegreeOneSection_val]

end DegreeOne

end

end TauCeti.AlgebraicGeometry
