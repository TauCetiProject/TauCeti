/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Acyclic
public import TauCeti.CategoryTheory.Triangulated.VerdierLocalization

/-!
# Derived categories of the second kind of curved modules

Let `A` be a right-convention curved DG algebra. Curved right `A`-modules have no homology, so
their derived categories are not formed by inverting quasi-isomorphisms. Instead, the curved
homotopy category is localized at one of the three acyclic classes of the second kind generated
by totalizations of short exact sequences:

* the **absolute derived category** `D_abs`, the Verdier quotient by the absolutely acyclic
  objects;
* the **coderived category** `D_co`, the Verdier quotient by the coacyclic objects;
* the **contraderived category** `D_ctr`, the Verdier quotient by the contraacyclic objects.

Each is Mathlib's localization of the curved homotopy category at the morphisms whose cone lies
in the corresponding class, and so carries the localization universal property, a preadditive
structure, an integral shift, and a triangulated structure for which the localization functor
is a triangle functor.

Since the absolutely acyclic objects form a thick triangulated subcategory, they are exactly the
curved modules that become zero in `D_abs`. A triangle functor out of the curved homotopy
category factors through `D_abs` exactly when it kills the totalization of every short exact
sequence of curved modules.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory`,
  `TauCeti.CurvedDGRightModuleCat.CoderivedCategory`,
  `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory`: the three derived categories of the
  second kind.
* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory.Q`,
  `TauCeti.CurvedDGRightModuleCat.CoderivedCategory.Q`,
  `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.Q`: their localization functors.

## Main results

* `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory.isZero_Q_obj_iff`: a curved module is
  zero in the absolute derived category if and only if it is absolutely acyclic.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_trW_isInvertedBy_iff`: a triangle functor
  out of the curved homotopy category inverts the absolutely acyclic weak equivalences if and
  only if it kills every totalization of a short exact sequence.

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
noncomputable abbrev Q :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ AbsoluteDerivedCategory R h :=
  (absolutelyAcyclic R h).trW.Q

/-- A curved module becomes zero in the absolute derived category if and only if it is
absolutely acyclic. -/
theorem isZero_Q_obj_iff (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((Q R h).obj X) ↔ absolutelyAcyclic R h X :=
  ObjectProperty.TrWLocalization.isZero_obj_iff _ _ X

end AbsoluteDerivedCategory

namespace CoderivedCategory

variable (R h) in
/-- The localization functor from the curved homotopy category to the coderived category. -/
noncomputable abbrev Q :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ CoderivedCategory R h :=
  (coacyclic R h).trW.Q

/-- A coacyclic curved module becomes zero in the coderived category. -/
theorem isZero_Q_obj {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    (hX : coacyclic R h X) : IsZero ((Q R h).obj X) :=
  ObjectProperty.TrWLocalization.isZero_obj _ _ hX

end CoderivedCategory

namespace ContraderivedCategory

variable (R h) in
/-- The localization functor from the curved homotopy category to the contraderived category. -/
noncomputable abbrev Q :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ ContraderivedCategory R h :=
  (contraacyclic R h).trW.Q

/-- A contraacyclic curved module becomes zero in the contraderived category. -/
theorem isZero_Q_obj {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    (hX : contraacyclic R h X) : IsZero ((Q R h).obj X) :=
  ObjectProperty.TrWLocalization.isZero_obj _ _ hX

end ContraderivedCategory

/-- **The universal property of the absolute derived category.** A triangle functor out of the
curved homotopy category inverts the morphisms with absolutely acyclic cone, and hence factors
through the absolute derived category, if and only if it sends the totalization of every short
exact sequence of curved modules to a zero object. -/
theorem absolutelyAcyclic_trW_isInvertedBy_iff {E : Type*} [Category* E] [HasZeroObject E]
    [Preadditive E] [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (F : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] :
    (absolutelyAcyclic R h).trW.IsInvertedBy F ↔
      ∀ S : ShortComplex
        (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)),
        S.ShortExact → IsZero (F.obj (DGHomotopyCategory.of R (totalization S))) := by
  rw [ObjectProperty.trW_isInvertedBy_iff]
  refine ⟨fun hF S hS ↦ hF _ (totalizations_le_absolutelyAcyclic R h _
    (totalizations_totalization hS)), fun hF ↦ ?_⟩
  -- The objects killed by `F` form a thick triangulated subcategory containing every
  -- totalization, so they contain the absolutely acyclic objects.
  exact absolutelyAcyclic_le_iff (Q := ObjectProperty.inverseImage (IsZero (C := E)) F) |>.2
    ((totalizations_le_iff _).2 hF)

end TauCeti.CurvedDGRightModuleCat
