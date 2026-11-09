/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import TauCeti.Algebra.Category.Ring.PolynomialQuotient
public import TauCeti.RingTheory.MvPolynomial.FilteredColimit

/-!
# Descent of finitely presented algebras

A finitely presented algebra over a filtered colimit of commutative rings is a pushout
of a finitely presented algebra over one stage. Lift the finite polynomial presentation
to a common stage and verify its universal property. This is the affine object-descent
step for finitely presented schemes, used in representability of the Picard functor.
-/

public section

universe categoryHom categoryObj ringUniverse

open CategoryTheory Limits

namespace CommRingCat

variable {Index : Type categoryObj} [Category.{categoryHom} Index] [IsFiltered Index]
  (diagram : Index ⥤ CommRingCat.{ringUniverse}) (cocone : Cocone diagram)
  [PreservesColimit diagram (forget CommRingCat)] {indeterminates : Type*}

variable (colimit : IsColimit cocone)

include colimit in
/-- A finitely presented algebra over a filtered colimit is the pushout of a finitely presented
algebra over one stage. -/
theorem exists_isPushout_of_finitePresentation {T : CommRingCat.{ringUniverse}}
    (f : cocone.pt ⟶ T) (hfp : f.hom.FinitePresentation) :
    ∃ (stage : Index) (B : CommRingCat.{ringUniverse})
      (fᵢ : diagram.obj stage ⟶ B) (_ : fᵢ.hom.FinitePresentation)
      (g : B ⟶ T),
      IsPushout (cocone.ι.app stage) fᵢ f g := by
  classical
  let : Algebra cocone.pt T := f.hom.toAlgebra
  obtain ⟨n, hpres⟩ := hfp
  obtain ⟨π, rfl, hπ, rels, hspan⟩ :
      ∃ π : of (MvPolynomial (Fin n) cocone.pt) ⟶ T,
        ofHom MvPolynomial.C ≫ π = f ∧
          Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, hπ, kernel_finite⟩ := hpres
    exact ⟨ofHom π, by ext1; exact π.comp_algebraMap,
      hπ, kernel_finite⟩
  obtain ⟨stage, hlift⟩ :=
    TauCeti.CommRingCat.exists_forall_mem_range_map_ι_app diagram cocone colimit rels
  choose r hr using fun p : rels ↦
    hlift p p.2
  have hrange : (↑rels : Set (MvPolynomial (Fin n) cocone.pt)) =
      Set.range fun i ↦ MvPolynomial.map (cocone.ι.app stage).hom (r i) := by
    refine Set.ext fun p ↦ ⟨fun membership ↦
      ⟨⟨p, membership⟩, hr ⟨p, membership⟩⟩, ?_⟩
    rintro ⟨i, hp⟩
    exact Set.mem_of_eq_of_mem (hp.symm.trans (hr i))
      (Finset.mem_coe.mpr i.2)
  obtain ⟨g, pushout⟩ := exists_isPushout_quotient_span (S := cocone.pt)
    (cocone.ι.app stage) r π hπ
      (by rw [← hspan, hrange])
  refine ⟨stage, _, _, ?_, g, pushout⟩
  -- FinitePresentation of the categorical composite is that of the underlying quotient ring map.
  change ((Ideal.Quotient.mk (Ideal.span (Set.range r))).comp
    MvPolynomial.C).FinitePresentation
  refine RingHom.FinitePresentation.comp
    (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_) ?_
  · rw [Ideal.mk_ker]
    exact ⟨Finset.univ.image r, by simp⟩
  · have hpoly := RingHom.finitePresentation_algebraMap
      (A := (diagram.obj stage : Type ringUniverse))
      (B := MvPolynomial (Fin n) (diagram.obj stage))
    rw [MvPolynomial.algebraMap_eq] at hpoly
    exact hpoly.mpr inferInstance

end CommRingCat
