/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FullSetOfSections.Basic
public import TauCeti.AlgebraicGeometry.SectionTupleScheme

/-!
# The scheme of full sets of sections

Let `g : Z ⟶ S` be finite locally free and `ι` a finite type. The `ι`-fold fibre power
`Z ×_S ⋯ ×_S Z` (`sectionTupleScheme g ι`) is the ambient scheme of `ι`-tuples of sections: its
`T`-points over `S` are the families `x : ι → (T ⟶ Z)` of `T`-points of `Z` over `S`, that is,
the families of sections of `Z_T ⟶ T`. Over it lives the universal family of sections
(`universalSection`) of the base change of `Z`, and the full-set locus of that family
(`fullSetTupleLocus g ι`) is a closed subscheme of the ambient scheme, cut out by the norm
identities.

By the universal property of the full-set locus, a `T`-point `x` of the ambient scheme factors
through this closed subscheme exactly when the sections of `Z_T ⟶ T` given by `x` are a full set
of sections (`fullSetTupleLocus_le_ker_lift_iff`, Katz–Mazur 1.9.1): the closed subscheme
represents the functor of `ι`-indexed full sets of sections of `Z`.

## Main definitions

* `TauCeti.AlgebraicGeometry.fullSetTupleLocus g ι`: the ideal sheaf of the full-set locus of the
  universal family of sections.

## Main results

* `TauCeti.AlgebraicGeometry.fullSetTupleLocus_def`: it is the full-set locus of the universal
  family of sections.
* `TauCeti.AlgebraicGeometry.fullSetTupleLocus_le_ker_lift_iff`: the universal property of the
  scheme of full sets of sections.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_fullSetTupleLocus`: over the closed subscheme,
  the universal family of sections is a full set of sections.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§1.8–1.9.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.IdealSheafData

variable {Z S : Scheme.{u}} (g : Z ⟶ S) (ι : Type) [Fintype ι]

variable [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]

/-- The ideal sheaf of the **scheme of full sets of sections** of `g` indexed by `ι`
(Katz–Mazur 1.9.1): the full-set locus of the universal family of sections over the scheme of
tuples of sections. Its closed subscheme represents the `ι`-indexed full sets of sections
(`fullSetTupleLocus_le_ker_lift_iff`). -/
noncomputable def fullSetTupleLocus : (sectionTupleScheme g ι).IdealSheafData :=
  fullSetLocus (pullback.fst _ g) (universalSection g ι) (universalSection_fst g ι)

/-- The scheme of full sets of sections is the full-set locus of the universal family of
sections, so `fullSetLocus_ideal` and `fullSetLocus_pullback` apply to it. -/
theorem fullSetTupleLocus_def : fullSetTupleLocus g ι =
    fullSetLocus (pullback.fst _ g) (universalSection g ι) (universalSection_fst g ι) :=
  (rfl)

/-- **The universal property of the scheme of full sets of sections** (Katz–Mazur 1.9.1). A
family `x : ι → (T ⟶ Z)` of `T`-points of `Z` over `t : T ⟶ S` factors through the closed
subscheme of `fullSetTupleLocus g ι` exactly when the corresponding sections of
`T ×_S Z ⟶ T` are a full set of sections. -/
theorem fullSetTupleLocus_le_ker_lift_iff {T : Scheme.{u}} (t : T ⟶ S) (x : ι → (T ⟶ Z))
    (hx : ∀ i, x i ≫ g = t) :
    fullSetTupleLocus g ι ≤ (WidePullback.lift t x hx).ker ↔
      IsFullSetOfSections (pullback.fst t g)
        (fun i ↦ graphSection (T := Over.mk t) (Over.homMk (x i) (hx i)))
        fun _ ↦ graphSection_fst (T := Over.mk t) _ := by
  -- the base change of `Z` to `T` through the scheme of tuples
  let φ := WidePullback.lift t x hx
  let gZ : pullback t g ⟶ pullback (WidePullback.base fun _ : ι ↦ g) g :=
    pullback.lift (pullback.fst t g ≫ φ) (pullback.snd t g) (by simp [φ, pullback.condition])
  have H : IsPullback gZ (pullback.fst t g) (pullback.fst _ g) φ := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (WidePullback.base fun _ : ι ↦ g) g).flip
    rw [pullback.lift_snd, WidePullback.lift_base]
    exact (IsPullback.of_hasPullback t g).flip
  refine fullSetLocus_le_ker_iff_of_isPullback _ _ _ H _ fun i ↦ ?_
  ext : 1
  · simpa [gZ, φ] using graphSection_fst_assoc (T := Over.mk t) (Over.homMk (x i) (hx i)) φ
  · simpa [gZ, φ] using graphSection_snd (T := Over.mk t) (Over.homMk (x i) (hx i))

/-- Over the scheme of full sets of sections, the universal family of sections is a full set of
sections. -/
theorem isFullSetOfSections_fullSetTupleLocus :
    IsFullSetOfSections (pullback.fst (fullSetTupleLocus g ι).subschemeι (pullback.fst _ g))
      (fun i ↦ baseChangeSection _ _ (universalSection_fst g ι i)
        (Over.mk (fullSetTupleLocus g ι).subschemeι))
      (fun i ↦ baseChangeSection_fst (pullback.fst _ g) _ (universalSection_fst g ι i)
        (Over.mk (fullSetTupleLocus g ι).subschemeι)) :=
  isFullSetOfSections_pullback_subschemeι_fullSetLocus _ _ _

end TauCeti.AlgebraicGeometry
