/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section

/-!
# Relative effective Cartier divisors of fixed degree

Let `f : X ⟶ S` be a proper family of curves. A relative effective Cartier divisor `D` on
`X_T = T ×_S X` is finite flat over `T`, so its degree at `t : T` is the rank of its closed
subscheme over `t`. The degree is preserved by arbitrary base change. Consequently, the divisors
whose degree is everywhere a fixed natural number `d` form a subfunctor `Div^d_{X/S}` of the
functor of relative effective Cartier divisors.

This fixed-degree functor is the functor represented by the symmetric power `Symᵈ X` when `f` is
a smooth proper curve. This file constructs the functor; it does not prove representability.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeEffectiveCartierDegreeSubfunctor`: the subfunctor
  `Div^d_{X/S}` of relative effective Cartier divisors of degree `d`;
* `TauCeti.AlgebraicGeometry.relativeEffectiveCartierDegreeOneSection`: the degree-one divisor
  supplied by a section of a smooth proper relative curve.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3.
* The Stacks Project, *Picard Schemes of Curves*, section *Moduli of divisors on smooth curves*.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [RelativeDimensionLE 1 f]

/-- The subfunctor `Div^d_{X/S}` of relative effective Cartier divisors of degree `d`.

At an `S`-scheme `T`, its elements are relative effective Cartier divisors on
`X_T = T ×_S X` whose finite flat closed subscheme has rank `d` at every point of `T`.
Arbitrary base change preserves this condition. -/
def relativeEffectiveCartierDegreeSubfunctor (d : ℕ) :
    Subfunctor (relativeEffectiveCartierSubfunctor f).toFunctor where
  obj T := {D | (D.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank = fun _ ↦ d}
  map {T T'} φ D hD := by
    have hrel : D.1.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f) :=
      (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mp D.2
    have : Flat (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hrel.flat
    have : IsFinite (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hrel.isFinite
    ext t
    exact (D.1.finrank_comap_of_isPullback _ _ _ _
      (isPullback_over_pullback_map_left f φ.unop) t).trans
      (congrFun hD (φ.unop.left t))

/-- A relative effective Cartier divisor belongs to `Div^d_{X/S}` exactly when the rank of its
closed subscheme over the base is constantly `d`. -/
@[simp]
lemma mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff
    {d : ℕ} {T : (Over S)ᵒᵖ} {D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T} :
    D ∈ (relativeEffectiveCartierDegreeSubfunctor f d).obj T ↔
      (D.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank = fun _ ↦ d :=
  Iff.rfl

variable [SmoothOfRelativeDimension 1 f]

/-- The degree-one relative effective Cartier divisor obtained by pulling a fixed section `x₀`
back to `X_T` for every `S`-scheme `T`. -/
@[expose]
def relativeEffectiveCartierDegreeOneSection (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)
    (T : (Over S)ᵒᵖ) :
    (relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor.obj T :=
  ⟨⟨(baseChangeSection f x₀ hx₀ T.unop).ker,
      (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mpr
        (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension _
          (baseChangeSection_fst f x₀ hx₀ T.unop))⟩,
    (mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff (f := f)).mpr (by
      have := Scheme.Hom.isClosedImmersion_of_comp_eq_id
        (baseChangeSection f x₀ hx₀ T.unop) (baseChangeSection_fst f x₀ hx₀ T.unop)
      ext t
      simpa using congrFun (Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id
        (baseChangeSection f x₀ hx₀ T.unop) (baseChangeSection_fst f x₀ hx₀ T.unop)) t)⟩

/-- The ideal sheaf underlying the degree-one divisor supplied by a section is the kernel of the
base-changed section. -/
@[simp]
lemma relativeEffectiveCartierDegreeOneSection_val (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)
    (T : (Over S)ᵒᵖ) :
    (relativeEffectiveCartierDegreeOneSection f x₀ hx₀ T).1.1 =
      (baseChangeSection f x₀ hx₀ T.unop).ker :=
  rfl

/-- Pulling back the degree-one divisor supplied by `x₀` gives the divisor supplied by the
base-changed section. -/
lemma relativeEffectiveCartierDegreeOneSection_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S) :
    (relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor.map φ
        (relativeEffectiveCartierDegreeOneSection f x₀ hx₀ T) =
      relativeEffectiveCartierDegreeOneSection f x₀ hx₀ T' := by
  apply Subtype.ext
  apply Subtype.ext
  have := Scheme.Hom.isClosedImmersion_of_comp_eq_id
    (baseChangeSection f x₀ hx₀ T.unop) (baseChangeSection_fst f x₀ hx₀ T.unop)
  exact (Scheme.IdealSheafData.ker_eq_comap_of_isPullback
    (baseChangeSection f x₀ hx₀ T.unop)
    (isPullback_baseChangeSection f x₀ hx₀ φ.unop)).symm

end

end TauCeti.AlgebraicGeometry
