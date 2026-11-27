/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative.ZeroLocus
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
import TauCeti.AlgebraicGeometry.Curves.Cohomology.Disconnected
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image

/-!
# Fixed-degree divisors from fibrewise injective functionals

On a smooth proper family of curves, a functional on a line bundle which is injective on every
residue-field fibre cuts out a finite flat relative effective Cartier divisor. Its rank at a point
is the negative of the degree of that line bundle on the fibre. Consequently, a fibrewise
injective functional whose source has constant degree `-d` supplies an element of `Divᵈ`.
The fibres may be disconnected or empty.

The construction uses the actual image ideal of the functional. The native divisor functor's
base-change map therefore gives the image ideal of the pulled-back functional.

## References

* The Stacks Project, *Divisors*, Sections 31.14 and 31.18.
* The Stacks Project, *Picard Schemes of Curves*, Section 44.3.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

noncomputable section

variable {S X : Scheme.{u}} (L : InvertibleSheaf X) (f : X ⟶ S) [IsProper f]
  [SmoothOfRelativeDimension 1 f] (φ : L.obj ⟶ 𝟙_ X.Modules)

/-- The rank of the relative zero divisor of a fibrewise injective functional is the negative
of the degree of its source line bundle on the residue-field fibre. No connectedness assumption
on the fibres is needed. -/
theorem eulerDegree_fiber_eq_neg_finrank_imageIdealSheaf
    (hφ : ∀ s : S, Mono ((Scheme.Modules.pullback (f.fiberι s)).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso (f.fiberι s)).hom)) (s : S) :
    letI := f.fiberOverSpecResidueField s
    ((pullback (f.fiberι s)).obj L).eulerDegree (S.residueField s) =
      -((φ.imageIdealSheaf.subschemeι ≫ f).finrank s : ℤ) := by
  let _ := f.fiberOverSpecResidueField s
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (f.fiber s ↘ Spec (S.residueField s)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (S.fromSpecResidueField s)))
  have : SmoothOfRelativeDimension 1 (f.fiber s ↘ Spec (S.residueField s)) :=
    inferInstanceAs
      (SmoothOfRelativeDimension 1 (Limits.pullback.snd f (S.fromSpecResidueField s)))
  let Ls : InvertibleSheaf (f.fiber s) :=
    ⟨(Scheme.Modules.pullback (f.fiberι s)).obj L.obj, inferInstance⟩
  let ψ : Ls.obj ⟶ 𝟙_ (f.fiber s).Modules :=
    (Scheme.Modules.pullback (f.fiberι s)).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso (f.fiberι s)).hom
  have : Mono ψ := hφ s
  have hJ := Ls.isEffectiveCartier_imageIdealSheaf ψ
  have : IsFinite (ψ.imageIdealSheaf.subschemeι ≫ f.fiber s ↘ Spec (S.residueField s)) :=
    hJ.isFinite_subschemeι_comp
  have (i : ℕ) : FiniteDimensional (S.residueField s)
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (f.fiber s)).obj i) :=
    Scheme.Modules.finiteDimensional_cohomology_of_smooth _ i
  have hd := hJ.eulerDegree_toInvertibleSheaf (S.residueField s) ψ.imageIdealSheaf default
  rw [← LineBundleClass.eulerDegree_mk, Ls.mk_toInvertibleSheaf_imageIdealSheaf ψ,
    LineBundleClass.eulerDegree_mk] at hd
  have hrel := L.isRelativeEffectiveCartier_imageIdealSheaf_of_fiber_mono f φ hφ
  have := hrel.flat
  have := hrel.isFinite
  have hrank := φ.imageIdealSheaf.finrank_comap_of_isPullback f (f.fiberι s)
    (f.fiberToSpecResidueField s) (S.fromSpecResidueField s)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) default
  rw [S.fromSpecResidueField_apply] at hrank
  dsimp only [ψ] at hd
  rw [Scheme.Modules.Hom.imageIdealSheaf_pullback] at hd
  -- `hd` uses the structure morphism `(f.fiber s) ↘ Spec (.of (S.residueField s))`;
  -- `hrank` uses `f.fiberToSpecResidueField s`, which induces that `Over` instance.
  erw [hrank] at hd
  -- The bundled pullback and the explicit underlying module use the same invertible sheaf.
  change Ls.eulerDegree (S.residueField s) = _
  exact hd

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace TauCeti.AlgebraicGeometry

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  {T : (Over S)ᵒᵖ} (L : InvertibleSheaf (Limits.pullback T.unop.hom f))
  (φ : L.obj ⟶ 𝟙_ (Limits.pullback T.unop.hom f).Modules)

variable (d : ℕ)
    (hφ : ∀ t : T.unop.left,
      Mono ((Scheme.Modules.pullback ((Limits.pullback.fst T.unop.hom f).fiberι t)).map φ ≫
        (Scheme.Modules.pullbackObjUnitIso
          ((Limits.pullback.fst T.unop.hom f).fiberι t)).hom))
    (hdeg : ∀ t : T.unop.left,
      letI := (Limits.pullback.fst T.unop.hom f).fiberOverSpecResidueField t
      InvertibleSheaf.eulerDegree (T.unop.left.residueField t)
        ((InvertibleSheaf.pullback
          ((Limits.pullback.fst T.unop.hom f).fiberι t)).obj L) = -(d : ℤ))

/-- A fibrewise injective line-bundle functional of source fibre degree `-d` determines a
degree-`d` relative effective Cartier divisor on the native base-changed family. -/
def relativeEffectiveCartierDegreeOfFunctional :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hrel := L.isRelativeEffectiveCartier_imageIdealSheaf_of_fiber_mono
    (Limits.pullback.fst T.unop.hom f) φ hφ
  refine ⟨⟨φ.imageIdealSheaf,
    (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mpr hrel⟩, ?_⟩
  apply (mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff (f := f)).mpr
  funext t
  have hrank := L.eulerDegree_fiber_eq_neg_finrank_imageIdealSheaf
    (Limits.pullback.fst T.unop.hom f) φ hφ t
  rw [hdeg t] at hrank
  exact_mod_cast neg_injective hrank.symm

/-- The divisor cut out by the functional is defined by its actual image ideal sheaf. -/
@[simp]
lemma relativeEffectiveCartierDegreeOfFunctional_val :
    (relativeEffectiveCartierDegreeOfFunctional f L φ d hφ hdeg).val.val =
      φ.imageIdealSheaf := by
  simp [relativeEffectiveCartierDegreeOfFunctional]

/-- Base change in the fixed-degree divisor functor gives the image ideal of the pulled-back
functional, for an arbitrary morphism of test schemes. -/
lemma relativeEffectiveCartierDegreeOfFunctional_map_val
    {T' : (Over S)ᵒᵖ} (τ : T ⟶ T') :
    ((relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.map τ
      (relativeEffectiveCartierDegreeOfFunctional f L φ d hφ hdeg)).val.val =
        ((Scheme.Modules.pullback ((Over.pullback f).map τ.unop).left).map φ ≫
          (Scheme.Modules.pullbackObjUnitIso
            ((Over.pullback f).map τ.unop).left).hom).imageIdealSheaf := by
  simp only [Subfunctor.toFunctor_map, baseChangeIdealSheafFunctor_map_apply]
  exact (Scheme.Modules.Hom.imageIdealSheaf_pullback φ _).symm

end

end TauCeti.AlgebraicGeometry
