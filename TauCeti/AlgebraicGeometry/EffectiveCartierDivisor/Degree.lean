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

* `AlgebraicGeometry.Scheme.IdealSheafData.finrank_comap_of_isPullback`: the degree of a flat
  finite closed subscheme is preserved when its ideal sheaf is pulled back around a pullback
  square;
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

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' S S' : Scheme.{u}}

/-- The degree of a finite flat closed subscheme is preserved by base change. More precisely, if
`X' ⟶ X` is the base change of `X ⟶ S` along `S' ⟶ S`, then the closed subscheme cut out by
the inverse-image ideal sheaf has rank at `s'` equal to the original closed subscheme's rank at
its image in `S`.

The hypothesis that the original closed subscheme is finite and flat is exactly what is needed
for the two rank functions. -/
theorem finrank_comap_of_isPullback (I : X.IdealSheafData) (f : X ⟶ S)
    (g : X' ⟶ X) (f' : X' ⟶ S') (h : S' ⟶ S)
    (H : IsPullback g f' f h) [Flat (I.subschemeι ≫ f)] [IsFinite (I.subschemeι ≫ f)]
    (s : S') :
    ((I.comap g).subschemeι ≫ f').finrank s = (I.subschemeι ≫ f).finrank (h s) := by
  let α := subschemeMap (I.comap g) I g (I.le_map_comap g)
  have hI : IsPullback (I.comap g).subschemeι α g I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [α]) (by simp)
  have h' : IsPullback α ((I.comap g).subschemeι ≫ f') (I.subschemeι ≫ f) h := by
    simpa [Category.assoc] using (hI.paste_horiz H.flip).flip
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ h' s

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (s : S ⟶ X) {f : X ⟶ S}

/-- The closed subscheme defined by the ideal sheaf of a closed section has degree one over the
base. -/
theorem finrank_ker_comp_eq_one_of_comp_eq_id (hs : s ≫ f = 𝟙 S) [IsClosedImmersion s] :
    (s.ker.subschemeι ≫ f).finrank = 1 := by
  have h : s.ker.subschemeι ≫ f = inv s.toImage :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs])
  rw [h]
  exact Scheme.Hom.finrank_eq_one_of_isIso _

end AlgebraicGeometry.Scheme.Hom

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
    have H : IsPullback ((Over.pullback f).map φ.unop).left
        (pullback.fst T'.unop.hom f)
        (pullback.fst T.unop.hom f) φ.unop.left := by
      refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback T.unop.hom f).flip
      simpa using (IsPullback.of_hasPullback T'.unop.hom f).flip
    have hrel : D.1.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f) :=
      (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mp D.2
    let _ : Flat (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hrel.flat
    let _ : IsFinite (D.1.subschemeι ≫ pullback.fst T.unop.hom f) := hrel.isFinite
    ext t
    exact (D.1.finrank_comap_of_isPullback _ _ _ _ H t).trans
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

/-- A section of a smooth proper relative curve gives a degree-one relative effective Cartier
divisor after every base change. This is the functor-of-points precursor of the canonical map
`X → Sym¹ X`. -/
def relativeEffectiveCartierDegreeOneSection (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)
    (T : (Over S)ᵒᵖ) :
    (relativeEffectiveCartierDegreeSubfunctor f 1).toFunctor.obj T := by
  let s := baseChangeSection f x₀ hx₀ T.unop
  have hs : s ≫ pullback.fst T.unop.hom f = 𝟙 T.unop.left :=
    baseChangeSection_fst f x₀ hx₀ T.unop
  have hclosed : IsClosedImmersion s := by
    have : IsClosedImmersion (s ≫ pullback.fst T.unop.hom f) := hs ▸ inferInstance
    exact IsClosedImmersion.of_comp s (pullback.fst T.unop.hom f)
  let _ : IsClosedImmersion s := hclosed
  have hrel : s.ker.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f) :=
    Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs
  refine ⟨⟨s.ker, (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mpr hrel⟩, ?_⟩
  apply (mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff (f := f)).mpr
  ext t
  simpa using congrFun (Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id s hs) t

/-- The ideal sheaf underlying the degree-one divisor supplied by a section is the kernel of the
base-changed section. -/
@[simp]
lemma relativeEffectiveCartierDegreeOneSection_val (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)
    (T : (Over S)ᵒᵖ) :
    (relativeEffectiveCartierDegreeOneSection f x₀ hx₀ T).1.1 =
      (baseChangeSection f x₀ hx₀ T.unop).ker :=
  by
    unfold relativeEffectiveCartierDegreeOneSection
    rfl

end

end TauCeti.AlgebraicGeometry
