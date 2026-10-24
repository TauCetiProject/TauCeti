/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Localization
public import TauCeti.Algebra.Homology.Periodic.Compression.Acyclic
public import TauCeti.Algebra.Homology.Periodic.Compression.Periodicity
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

Compression on derived categories is invariant under the shift by any multiple `k` of `n`
(`TauCeti.PeriodicComplex.derivedCompressionFunctorPeriodicityIso`): the periodicity isomorphism
of `K^b(C) ⥤ K_n(C)` descends along `K^b(C) ⥤ D^b(C)`. Taking `k = n`, Keller's universal
property of the orbit category descends compression to the orbit functor
`D^b(C)/[n] ⥤ D_n(C)` (`TauCeti.PeriodicComplex.orbitDerivedCompressionFunctor`), which
restricts to compression along the projection `D^b(C) ⥤ D^b(C)/[n]`. It is induced by the orbit
functor `K^b(C)/[n] ⥤ K_n(C)`: the induced functor `K^b(C)/[n] ⥤ D^b(C)/[n]` followed by the
derived orbit functor is the homotopy orbit functor followed by `K_n(C) ⥤ D_n(C)`
(`TauCeti.PeriodicComplex.orbitDerivedCompressionFunctorFactors`). No hypothesis on `C` beyond
abelianity is needed for these constructions. Stai proves that the derived orbit functor is fully
faithful when `C` is the category of finitely generated modules over a finite-dimensional algebra
of finite global dimension.

## References

* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
* `derivedCompressionFunctorPeriodicityIso` is descended along the localization functor like
  `TauCeti.PeriodicComplex.homotopyCompressionFunctorPeriodicityIso`
  (`TauCeti.Algebra.Homology.Periodic.Compression.Periodicity`).
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

section Periodicity

variable (k : ℤ) (hk : (k : ZMod n) = 0)

open TauCeti.DerivedCategory.Bounded in
/-- The compression functor `D^b(C) ⥤ D_n(C)` is invariant under the shift by a multiple `k` of
`n`. It is induced, along the localization functor `K^b(C) ⥤ D^b(C)`, by the periodicity
isomorphism of the compression functor `K^b(C) ⥤ K_n(C)`. -/
noncomputable def derivedCompressionFunctorPeriodicityIso :
    CategoryTheory.shiftFunctor (_root_.DerivedCategory.Bounded C) k ⋙ derivedCompressionFunctor n ≅
      derivedCompressionFunctor n :=
  Localization.liftNatIso (Qh C) (HomotopyCategory.Bounded.quasiIso C)
    (Qh C ⋙ CategoryTheory.shiftFunctor _ k ⋙ derivedCompressionFunctor n)
    (Qh C ⋙ derivedCompressionFunctor n) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Qh C).commShiftIso k).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedCompressionFunctorFactors n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homotopyCompressionFunctorPeriodicityIso n k hk) _ ≪≫
      (derivedCompressionFunctorFactors n).symm)

open TauCeti.DerivedCategory.Bounded in
/-- On the image of a bounded homotopy class, the periodicity isomorphism of `D^b(C) ⥤ D_n(C)`
is the image of the periodicity isomorphism of `K^b(C) ⥤ K_n(C)`, conjugated by the
identifications `derivedCompressionFunctorFactors` of the two compressions. -/
@[simp]
lemma derivedCompressionFunctorPeriodicityIso_hom_app_Qh_obj (K : HomotopyCategory.Bounded C) :
    (derivedCompressionFunctorPeriodicityIso n k hk).hom.app ((Qh C).obj K) =
      (derivedCompressionFunctor n).map (((Qh C).commShiftIso k).inv.app K) ≫
        (derivedCompressionFunctorFactors n).hom.app (K⟦k⟧) ≫
          (DerivedCategory.Qh C n).map
            ((homotopyCompressionFunctorPeriodicityIso n k hk).hom.app K) ≫
            (derivedCompressionFunctorFactors n).inv.app K := by
  simp [derivedCompressionFunctorPeriodicityIso]

open TauCeti.DerivedCategory.Bounded in
/-- On the image of a bounded homotopy class, the inverse of the periodicity isomorphism of
`D^b(C) ⥤ D_n(C)` is the image of the inverse periodicity isomorphism of `K^b(C) ⥤ K_n(C)`,
conjugated by the identifications `derivedCompressionFunctorFactors` of the two compressions. -/
@[simp]
lemma derivedCompressionFunctorPeriodicityIso_inv_app_Qh_obj (K : HomotopyCategory.Bounded C) :
    (derivedCompressionFunctorPeriodicityIso n k hk).inv.app ((Qh C).obj K) =
      (derivedCompressionFunctorFactors n).hom.app K ≫
        (DerivedCategory.Qh C n).map
          ((homotopyCompressionFunctorPeriodicityIso n k hk).inv.app K) ≫
          (derivedCompressionFunctorFactors n).inv.app (K⟦k⟧) ≫
            (derivedCompressionFunctor n).map (((Qh C).commShiftIso k).hom.app K) := by
  simp [derivedCompressionFunctorPeriodicityIso]

/-- The orbit functor `D^b(C)/[n] ⥤ D_n(C)`: the descent of the compression functor
`D^b(C) ⥤ D_n(C)` to the orbit category, along its periodicity isomorphism for the shift by `n`.
It restricts to compression along the projection `D^b(C) ⥤ D^b(C)/[n]`
(`TauCeti.OrbitCategory.projectionCompLift`). -/
noncomputable abbrev orbitDerivedCompressionFunctor :
    OrbitCategory (_root_.DerivedCategory.Bounded C) n ⥤ DerivedCategory C n :=
  OrbitCategory.lift (derivedCompressionFunctor n)
    (derivedCompressionFunctorPeriodicityIso n n (by simp))

open TauCeti.DerivedCategory.Bounded in
/-- The orbit functor `D^b(C)/[n] ⥤ D_n(C)` is induced by the orbit functor
`K^b(C)/[n] ⥤ K_n(C)`: the functor `K^b(C)/[n] ⥤ D^b(C)/[n]` induced by the localization
`K^b(C) ⥤ D^b(C)`, followed by the derived orbit functor, is the homotopy orbit functor followed
by the localization `K_n(C) ⥤ D_n(C)`. On components it is `derivedCompressionFunctorFactors`. -/
noncomputable def orbitDerivedCompressionFunctorFactors :
    OrbitCategory.map (Qh C) ⋙ orbitDerivedCompressionFunctor (C := C) n ≅
      orbitCompressionFunctor n ⋙ DerivedCategory.Qh C n :=
  OrbitCategory.mapCompLiftIso (Qh C) (derivedCompressionFunctorFactors n) (fun K ↦ by
    simp [← Functor.map_comp_assoc]) ≪≫
    (OrbitCategory.liftCompIso _ _ _).symm

/-- The component of `orbitDerivedCompressionFunctorFactors` at a bounded homotopy class is the
component of `derivedCompressionFunctorFactors`. -/
@[simp]
lemma orbitDerivedCompressionFunctorFactors_hom_app (K : HomotopyCategory.Bounded C) :
    (orbitDerivedCompressionFunctorFactors (C := C) n).hom.app ⟨K⟩ =
      (derivedCompressionFunctorFactors n).hom.app K := by
  simp only [orbitDerivedCompressionFunctorFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    OrbitCategory.mapCompLiftIso_hom_app, OrbitCategory.liftCompIso_inv_app]
  -- The identity component is typed at the objects of the descents along `map (Qh C)`, which are
  -- those of `Qh C` only after unfolding `map` and `lift`, so `simp` cannot cancel it.
  exact Category.comp_id _

/-- The inverse component of `orbitDerivedCompressionFunctorFactors` at a bounded homotopy class
is the inverse component of `derivedCompressionFunctorFactors`. -/
@[simp]
lemma orbitDerivedCompressionFunctorFactors_inv_app (K : HomotopyCategory.Bounded C) :
    (orbitDerivedCompressionFunctorFactors (C := C) n).inv.app ⟨K⟩ =
      (derivedCompressionFunctorFactors n).inv.app K := by
  simp only [orbitDerivedCompressionFunctorFactors, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    OrbitCategory.mapCompLiftIso_inv_app, OrbitCategory.liftCompIso_hom_app]
  -- The identity component is typed at the objects of the descents along `map (Qh C)`, which are
  -- those of `Qh C` only after unfolding `map` and `lift`, so `simp` cannot cancel it.
  exact Category.id_comp _

end Periodicity

end TauCeti.PeriodicComplex
