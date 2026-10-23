/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Acyclic
public import TauCeti.CategoryTheory.Triangulated.VerdierQuotient

/-!
# Derived categories of the second kind

Let `A` be a right-convention curved DG algebra. Curved right `A`-modules have no homology, so
their derived categories are not defined by inverting quasi-isomorphisms. Instead, the curved
homotopy category is divided by one of the three acyclic classes of the second kind generated
by the totalizations of short exact sequences. This file constructs the three Verdier quotients

* the **absolute derived category** `D_abs`, by the absolutely acyclic objects;
* the **coderived category** `D_co`, by the coacyclic objects;
* the **contraderived category** `D_ctr`, by the contraacyclic objects.

Each is Mathlib's localization `P.trW.Localization` of the curved homotopy category at the
morphisms whose cone lies in the acyclic class `P`, and is therefore a triangulated category
whose localization functor from the curved homotopy category is a triangle functor.

The objects killed by each localization are identified: the absolutely acyclic class is thick,
so a curved module becomes zero in `D_abs` exactly when it is absolutely acyclic; it becomes zero
in `D_co` or `D_ctr` exactly when it is a retract of a coacyclic or contraacyclic module. In
particular the totalization of every short exact sequence of curved modules vanishes in all
three. The absolute derived category has a universal property in terms of its generators: a
triangle functor out of the curved homotopy category inverts the absolute weak equivalences if
and only if it kills the totalization of every short exact sequence, and it then descends to
`D_abs` through `CategoryTheory.ObjectProperty.trWLift`.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory`,
  `TauCeti.CurvedDGRightModuleCat.CoderivedCategory`,
  `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory`: the three derived categories of the
  second kind.
* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory.Qh`,
  `TauCeti.CurvedDGRightModuleCat.CoderivedCategory.Qh`,
  `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.Qh`: their localization functors from
  the curved homotopy category.

## Main results

* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory.isZero_Qh_obj_iff`: a curved module is
  zero in `D_abs` if and only if it is absolutely acyclic; the analogous statements for `D_co` and
  `D_ctr` involve retracts.
* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory.trW_isInvertedBy_iff`: the universal
  property of `D_abs` among triangle functors.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6 and Definitions 7.4–7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-! ### The three derived categories of the second kind -/

variable (R h) in
/-- The **absolute derived category** of curved right modules: the Verdier quotient of the
curved homotopy category by the absolutely acyclic objects. -/
abbrev AbsoluteDerivedCategory := (absolutelyAcyclic R h).trW.Localization

variable (R h) in
/-- The **coderived category** of curved right modules: the Verdier quotient of the curved
homotopy category by the coacyclic objects. -/
abbrev CoderivedCategory := (coacyclic R h).trW.Localization

variable (R h) in
/-- The **contraderived category** of curved right modules: the Verdier quotient of the curved
homotopy category by the contraacyclic objects. -/
abbrev ContraderivedCategory := (contraacyclic R h).trW.Localization

namespace AbsoluteDerivedCategory

variable (R h) in
/-- The localization functor from the curved homotopy category to the absolute derived
category. -/
noncomputable abbrev Qh :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ AbsoluteDerivedCategory R h :=
  (absolutelyAcyclic R h).trW.Q

/-- A curved module becomes zero in the absolute derived category if and only if it is
absolutely acyclic. -/
theorem isZero_Qh_obj_iff (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((Qh R h).obj X) ↔ absolutelyAcyclic R h X :=
  (absolutelyAcyclic R h).isZero_obj_iff _ X

/-- The totalization of a short exact sequence of curved modules is zero in the absolute derived
category. -/
theorem isZero_Qh_obj_totalization
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) : IsZero ((Qh R h).obj (DGHomotopyCategory.of R (totalization S))) :=
  (isZero_Qh_obj_iff _).2 (totalizations_le_absolutelyAcyclic R h _
    (totalizations_totalization hS))

/-- **The universal property of the absolute derived category.** A triangle functor out of the
curved homotopy category inverts the morphisms whose cone is absolutely acyclic if and only if it
kills the totalization of every short exact sequence of curved modules. -/
theorem trW_isInvertedBy_iff {E : Type*} [Category* E] [HasZeroObject E] [Preadditive E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (F : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] :
    (absolutelyAcyclic R h).trW.IsInvertedBy F ↔
      ∀ S : ShortComplex
        (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)),
        S.ShortExact → IsZero (F.obj (DGHomotopyCategory.of R (totalization S))) := by
  simp only [ObjectProperty.trW_isInvertedBy_iff, absolutelyAcyclic_le_iff, totalizations_le_iff,
    ObjectProperty.prop_inverseImage_iff]

end AbsoluteDerivedCategory

namespace CoderivedCategory

variable (R h) in
/-- The localization functor from the curved homotopy category to the coderived category. -/
noncomputable abbrev Qh :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ CoderivedCategory R h :=
  (coacyclic R h).trW.Q

/-- A curved module becomes zero in the coderived category if and only if it is a retract of a
coacyclic curved module. -/
theorem isZero_Qh_obj_iff (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((Qh R h).obj X) ↔ (coacyclic R h).retractClosure X :=
  (coacyclic R h).isZero_obj_iff_retractClosure _ X

/-- The totalization of a short exact sequence of curved modules is zero in the coderived
category. -/
theorem isZero_Qh_obj_totalization
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) : IsZero ((Qh R h).obj (DGHomotopyCategory.of R (totalization S))) :=
  (isZero_Qh_obj_iff _).2 ((coacyclic R h).le_retractClosure _
    (totalizations_le_coacyclic R h _ (totalizations_totalization hS)))

end CoderivedCategory

namespace ContraderivedCategory

variable (R h) in
/-- The localization functor from the curved homotopy category to the contraderived
category. -/
noncomputable abbrev Qh :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ ContraderivedCategory R h :=
  (contraacyclic R h).trW.Q

/-- A curved module becomes zero in the contraderived category if and only if it is a retract
of a contraacyclic curved module. -/
theorem isZero_Qh_obj_iff (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((Qh R h).obj X) ↔ (contraacyclic R h).retractClosure X :=
  (contraacyclic R h).isZero_obj_iff_retractClosure _ X

/-- The totalization of a short exact sequence of curved modules is zero in the contraderived
category. -/
theorem isZero_Qh_obj_totalization
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) : IsZero ((Qh R h).obj (DGHomotopyCategory.of R (totalization S))) :=
  (isZero_Qh_obj_iff _).2 ((contraacyclic R h).le_retractClosure _
    (totalizations_le_contraacyclic R h _ (totalizations_totalization hS)))

end ContraderivedCategory

end TauCeti.CurvedDGRightModuleCat
