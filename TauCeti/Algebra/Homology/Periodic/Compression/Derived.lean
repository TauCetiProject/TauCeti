/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Localization
public import TauCeti.Algebra.Homology.Periodic.Compression.Acyclic
public import TauCeti.Algebra.Homology.Periodic.Compression.Triangulated
public import TauCeti.Algebra.Homology.Periodic.Derived

/-!
# Compression on derived categories

Let `C` be an abelian category. The `n`-periodic compression `K^b(C) ⥤ K_n(C)` from the bounded
homotopy category to the `n`-periodic homotopy category preserves and reflects
quasi-isomorphisms (`TauCeti.PeriodicComplex.quasiIso_iff_trW_homotopyCompressionFunctor_map`):
it is a triangle functor, and a bounded complex is acyclic exactly when its compression is.
Since `K^b(C) ⥤ D^b(C)` is a localization at the quasi-isomorphisms, compression descends to a
triangle functor `TauCeti.PeriodicComplex.derivedCompressionFunctor : D^b(C) ⥤ D_n(C)` from the
bounded derived category to the `n`-periodic derived category, compatible with the localization
functors up to the natural isomorphism
`TauCeti.PeriodicComplex.derivedCompressionFunctorFactors`.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (n : ℕ)

/-- An object of the bounded homotopy category is acyclic exactly when its compression is
acyclic. -/
theorem homotopyCompressionFunctor_obj_mem_subcategoryAcyclic_iff
    (K : HomotopyCategory.Bounded C) :
    subcategoryAcyclic C n ((homotopyCompressionFunctor n).obj K) ↔
      HomotopyCategory.Bounded.subcategoryAcyclic C K := by
  obtain ⟨a, b, _, _⟩ :=
    (CochainComplex.bounded_iff C _).mp (HomotopyCategory.Bounded.bounded_rep K)
  rw [homotopyCompressionFunctor_obj, quotient_obj_mem_subcategoryAcyclic_iff,
    compression_acyclic_iff n _ a b, HomotopyCategory.Bounded.mem_subcategoryAcyclic_iff,
    ← HomotopyCategory.Bounded.quotient_obj_rep K,
    _root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]

/-- The acyclic objects of the bounded homotopy category are the inverse image of the acyclic
objects of the `n`-periodic homotopy category under compression. -/
theorem subcategoryAcyclic_inverseImage_homotopyCompressionFunctor :
    (subcategoryAcyclic C n).inverseImage (homotopyCompressionFunctor n) =
      HomotopyCategory.Bounded.subcategoryAcyclic C :=
  funext fun K ↦ propext (homotopyCompressionFunctor_obj_mem_subcategoryAcyclic_iff n K)

/-- A morphism of the bounded homotopy category is a quasi-isomorphism exactly when its
compression has an acyclic cone, and hence becomes an isomorphism in the periodic derived
category. -/
theorem quasiIso_iff_trW_homotopyCompressionFunctor_map
    {K L : HomotopyCategory.Bounded C} (f : K ⟶ L) :
    HomotopyCategory.Bounded.quasiIso C f ↔
      (subcategoryAcyclic C n).trW ((homotopyCompressionFunctor n).map f) := by
  rw [HomotopyCategory.Bounded.quasiIso_eq_subcategoryAcyclic_trW,
    ← subcategoryAcyclic_inverseImage_homotopyCompressionFunctor]
  exact ObjectProperty.inverseImage_trW_iff _ _ f

/-- Compression followed by the localization to the periodic derived category inverts the
quasi-isomorphisms of bounded complexes. -/
lemma homotopyCompressionFunctor_comp_Qh_inverts_quasiIso :
    (HomotopyCategory.Bounded.quasiIso C).IsInvertedBy
      (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n) := by
  rw [HomotopyCategory.Bounded.quasiIso_eq_subcategoryAcyclic_trW,
    ← subcategoryAcyclic_inverseImage_homotopyCompressionFunctor]
  exact ObjectProperty.inverseImage_trW_isInverted _ _ _

variable [HasDerivedCategory.{w} C]

/-- The `n`-periodic compression `D^b(C) ⥤ D_n(C)` from the bounded derived category to the
`n`-periodic derived category, induced by the compression of bounded complexes. -/
noncomputable def derivedCompressionFunctor :
    _root_.DerivedCategory.Bounded C ⥤ DerivedCategory C n :=
  Localization.lift _ (homotopyCompressionFunctor_comp_Qh_inverts_quasiIso n)
    (TauCeti.DerivedCategory.Bounded.Qh C)

/-- The compression `D^b(C) ⥤ D_n(C)` is induced by the compression `K^b(C) ⥤ K_n(C)`. -/
noncomputable def derivedCompressionFunctorFactors :
    TauCeti.DerivedCategory.Bounded.Qh C ⋙ derivedCompressionFunctor (C := C) n ≅
      homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n :=
  Localization.fac _ _ _

noncomputable instance :
    Localization.Lifting (TauCeti.DerivedCategory.Bounded.Qh C)
      (HomotopyCategory.Bounded.quasiIso C)
      (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n) (derivedCompressionFunctor n) :=
  ⟨derivedCompressionFunctorFactors n⟩

noncomputable instance : (derivedCompressionFunctor (C := C) n).CommShift ℤ :=
  Functor.commShiftOfLocalization (TauCeti.DerivedCategory.Bounded.Qh C)
    (HomotopyCategory.Bounded.quasiIso C) ℤ
    (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n) (derivedCompressionFunctor n)

instance : NatTrans.CommShift (derivedCompressionFunctorFactors (C := C) n).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
    (TauCeti.DerivedCategory.Bounded.Qh C) (HomotopyCategory.Bounded.quasiIso C)
    (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n)
    (derivedCompressionFunctor n)).hom ℤ)

/-- **Compression is a triangle functor on derived categories.** -/
instance : (derivedCompressionFunctor (C := C) n).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (derivedCompressionFunctorFactors n)

end TauCeti.PeriodicComplex
