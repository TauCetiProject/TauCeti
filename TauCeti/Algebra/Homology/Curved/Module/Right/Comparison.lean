/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.SecondKind

/-!
# Comparisons between curved derived categories of the second kind

The absolutely acyclic curved right modules are both coacyclic and contraacyclic. Consequently,
the coderived and contraderived localization functors descend through the absolute derived
category. This file constructs the resulting triangle functors
`D_abs → D_co` and `D_abs → D_ctr`, with natural isomorphisms identifying their composites with
the absolute localization with the original localization functors.

These are not identifications of the three derived categories. On objects represented by curved
modules, the kernels of the comparisons are precisely the coacyclic and contraacyclic classes,
respectively. No comparison between the coderived and contraderived categories is asserted.

The construction instantiates `ObjectProperty.trWLocalizerMorphismOfLE` and Mathlib's
`LocalizerMorphism.localizedFunctor`; compatibility with localization is a natural isomorphism,
not an equality of functors.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Definitions 7.4–7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

namespace AbsoluteDerivedCategory

variable (R h)

/-- The comparison from the absolute derived category to the coderived category, induced by the
inclusion of the absolutely acyclic objects into the coacyclic objects. -/
noncomputable def toCoderived : AbsoluteDerivedCategory R h ⥤ CoderivedCategory R h :=
  (ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_coacyclic R h)).localizedFunctor
    (Q R h) (CoderivedCategory.Q R h)

/-- The comparison from the absolute derived category to the contraderived category, induced by
the inclusion of the absolutely acyclic objects into the contraacyclic objects. -/
noncomputable def toContraderived : AbsoluteDerivedCategory R h ⥤ ContraderivedCategory R h :=
  (ObjectProperty.trWLocalizerMorphismOfLE
    (absolutelyAcyclic_le_contraacyclic R h)).localizedFunctor (Q R h) (ContraderivedCategory.Q R h)

/-- The comparison to the coderived category commutes coherently with all integral shifts. -/
noncomputable instance : (toCoderived R h).CommShift ℤ :=
  inferInstanceAs (((ObjectProperty.trWLocalizerMorphismOfLE
    (absolutelyAcyclic_le_coacyclic R h)).localizedFunctor (Q R h)
      (CoderivedCategory.Q R h)).CommShift ℤ)

/-- The comparison to the contraderived category commutes coherently with all integral shifts. -/
noncomputable instance : (toContraderived R h).CommShift ℤ :=
  inferInstanceAs (((ObjectProperty.trWLocalizerMorphismOfLE
    (absolutelyAcyclic_le_contraacyclic R h)).localizedFunctor (Q R h)
      (ContraderivedCategory.Q R h)).CommShift ℤ)

/-- The comparison to the coderived category preserves distinguished triangles. -/
instance : (toCoderived R h).IsTriangulated :=
  LocalizerMorphism.isTriangulated_localizedFunctor _ (Q R h) (CoderivedCategory.Q R h)

/-- The comparison to the contraderived category preserves distinguished triangles. -/
instance : (toContraderived R h).IsTriangulated :=
  LocalizerMorphism.isTriangulated_localizedFunctor _ (Q R h) (ContraderivedCategory.Q R h)

/-- Localizing absolutely and then comparing with the coderived category agrees naturally with
localizing directly at the coacyclic objects. -/
noncomputable def toCoderivedFactors : Q R h ⋙ toCoderived R h ≅ CoderivedCategory.Q R h :=
  Localization.fac _
    ((ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_coacyclic R h)).inverts
      (CoderivedCategory.Q R h)) (Q R h) ≪≫
    Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
    Functor.leftUnitor _

/-- Localizing absolutely and then comparing with the contraderived category agrees naturally
with localizing directly at the contraacyclic objects. -/
noncomputable def toContraderivedFactors :
    Q R h ⋙ toContraderived R h ≅ ContraderivedCategory.Q R h :=
  Localization.fac _
    ((ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_contraacyclic R h)).inverts
      (ContraderivedCategory.Q R h)) (Q R h) ≪≫
    Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
    Functor.leftUnitor _

variable {R h}

/-- On objects represented in the curved homotopy category, the kernel of the comparison to the
coderived category consists exactly of the coacyclic objects. -/
@[simp] theorem isZero_toCoderived_obj_Q_obj_iff
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((toCoderived R h).obj ((Q R h).obj X)) ↔ coacyclic R h X := by
  have e := (toCoderivedFactors R h).app X
  exact ⟨fun hX ↦ (ObjectProperty.TrWLocalization.isZero_obj_iff _ _ X).1
    (hX.of_iso e.symm), fun hX ↦
      (ObjectProperty.TrWLocalization.isZero_obj_iff _ _ X).2 hX |>.of_iso e⟩

/-- On objects represented in the curved homotopy category, the kernel of the comparison to the
contraderived category consists exactly of the contraacyclic objects. -/
@[simp] theorem isZero_toContraderived_obj_Q_obj_iff
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    IsZero ((toContraderived R h).obj ((Q R h).obj X)) ↔ contraacyclic R h X := by
  have e := (toContraderivedFactors R h).app X
  exact ⟨fun hX ↦ (ObjectProperty.TrWLocalization.isZero_obj_iff _ _ X).1
    (hX.of_iso e.symm), fun hX ↦
      (ObjectProperty.TrWLocalization.isZero_obj_iff _ _ X).2 hX |>.of_iso e⟩

end AbsoluteDerivedCategory

end TauCeti.CurvedDGRightModuleCat
