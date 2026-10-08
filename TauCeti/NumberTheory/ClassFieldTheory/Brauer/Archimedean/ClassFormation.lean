/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.InfinitePlace
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.TrivialLayer

/-!
# The class formation at a complex place

The completion of a number field at a complex place is algebraically closed. Its absolute Galois
group is therefore trivial, so every finite normal layer of its units formation is trivial. This
gives the complex-place half of the archimedean class formation directly: all positive-degree
layer cohomology vanishes and every invariant map is zero.

The resulting invariant agrees with `infiniteInvMap` after inflation into the Brauer group. Thus
the construction has the normalization required by the global sum of local invariants, rather than
merely providing an abstract class formation on the same coefficient module.

## Main definitions

* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex`: the units class formation at a
  complex infinite place.

## Main results

* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex_inv`: its invariant agrees with the
  archimedean Brauer invariant after inflation.
* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex_artinMap`: every finite-layer Artin
  map at a complex place is zero.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–4.
* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K]

/-- The absolute Galois group of a complex infinite completion is trivial. -/
theorem subsingleton_absoluteGaloisGroup_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    Subsingleton (AbsoluteGaloisGroup w.Completion) := by
  let _ : IsAlgClosed w.Completion :=
    IsAlgClosed.of_ringEquiv ℂ w.Completion
      (Completion.ringEquivComplexOfIsComplex hw).symm
  infer_instance

/-- **The class formation at a complex place.** The absolute Galois group of the completion is
trivial, so the units formation carries the canonical class formation with zero invariant maps. -/
def infiniteClassFormationOfIsComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    ClassFormation (unitsFormation w.Completion) := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact ClassFormation.ofSubsingleton (unitsFormation w.Completion)

/-- The invariant of the complex-place class formation is zero on every layer. -/
@[simp]
theorem infiniteClassFormationOfIsComplex_inv_apply (w : InfinitePlace K) (hw : w.IsComplex)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion))
    (x : L.H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsComplex w hw).inv L x = 0 := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact ClassFormation.ofSubsingleton_inv_apply (unitsFormation w.Completion) L x

/-- The invariant of the complex-place class formation is the archimedean Brauer invariant of the
inflated class. This is the complex-place specialization of the normalization required of
`infiniteClassFormation`. -/
theorem infiniteClassFormationOfIsComplex_inv (w : InfinitePlace K) (hw : w.IsComplex)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsComplex w hw).inv (NormalLayer.ofOpenNormal V) x =
      infiniteInvMap w (brInfl V x) := by
  rw [infiniteClassFormationOfIsComplex_inv_apply,
    infiniteInvMap_eq_zero_of_isComplex w hw]

/-- Every finite-layer Artin map of the complex-place class formation is zero. -/
@[simp]
theorem infiniteClassFormationOfIsComplex_artinMap (w : InfinitePlace K) (hw : w.IsComplex)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    (infiniteClassFormationOfIsComplex w hw).artinMap L = 0 := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact (infiniteClassFormationOfIsComplex w hw).artinMap_trivialLayer L
    L.top_eq_ground_of_subsingleton

end TauCeti.ClassFieldTheory
