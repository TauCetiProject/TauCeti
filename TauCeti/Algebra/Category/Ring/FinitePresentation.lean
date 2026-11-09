/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

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

/-- Relations defined over the source ring give a pushout presentation of the quotient after
extending coefficients. -/
private lemma exists_isPushout_quotient_span
    {R S T : CommRingCat.{ringUniverse}}
    (f : R ⟶ S) {n : ℕ}
    {ι : Type*} (r : ι → MvPolynomial (Fin n) R)
    (π : of (MvPolynomial (Fin n) S) ⟶ T)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker π.hom = Ideal.span
      (Set.range fun i ↦ MvPolynomial.map f.hom (r i))) :
    ∃ g : of (MvPolynomial (Fin n) R ⧸
        Ideal.span (Set.range r)) ⟶ T,
      IsPushout f
        (ofHom MvPolynomial.C ≫ ofHom (Ideal.Quotient.mk (Ideal.span (Set.range r))))
        (ofHom MvPolynomial.C ≫ π) g := by
  set I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range r) with hI
  set q : of (MvPolynomial (Fin n) R) ⟶
      of (MvPolynomial (Fin n) R ⧸ I) :=
    ofHom (Ideal.Quotient.mk I) with hq
  set φ : of (MvPolynomial (Fin n) R) ⟶
      of (MvPolynomial (Fin n) S) :=
    ofHom (MvPolynomial.map f.hom) with hφ
  have relations_mem_kernel : I ≤ RingHom.ker (φ ≫ π).hom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.map f.hom (r i) ∈ RingHom.ker π.hom
    rw [hker]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨ofHom (Ideal.Quotient.lift I (φ ≫ π).hom
    fun p membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership)), ?_⟩
  set g : of (MvPolynomial (Fin n) R ⧸ I) ⟶ T :=
    ofHom (Ideal.Quotient.lift I (φ ≫ π).hom
      fun p membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership))
    with hg
  have hgq : ∀ p : MvPolynomial (Fin n) R,
      g.hom (q.hom p) =
        π.hom (MvPolynomial.map f.hom p) := by
    intro p
    rw [hg, hq]
    simp [hφ]
  have hqr : ∀ i, q.hom (r i) = 0 := by
    intro i
    rw [hq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hI ▸ Ideal.subset_span ⟨i, rfl⟩)
  have eval_map : ∀ (D : CommRingCat.{ringUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial (Fin n) R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      ∀ p : MvPolynomial (Fin n) R,
        MvPolynomial.eval₂ u.hom
          (fun i ↦ v.hom (q.hom (MvPolynomial.X i)))
          (MvPolynomial.map f.hom p) =
            v.hom (q.hom p) := by
    intro D u v huv p
    rw [MvPolynomial.eval₂_map]
    have hcoeff : u.hom.comp f.hom =
        v.hom.comp (q.hom.comp MvPolynomial.C) := by
      have equality := congrArg CommRingCat.Hom.hom huv
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] using equality
    have hevalq : MvPolynomial.eval₂Hom (q.hom.comp MvPolynomial.C)
        (fun i ↦ q.hom (MvPolynomial.X i)) = q.hom :=
      MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun i ↦ by simp)
    have hevalv : MvPolynomial.eval₂Hom
        (v.hom.comp (q.hom.comp MvPolynomial.C))
        (fun i ↦ v.hom (q.hom (MvPolynomial.X i))) =
          v.hom.comp q.hom := by
      rw [← MvPolynomial.comp_eval₂Hom, hevalq]
    rw [hcoeff]
    simpa using DFunLike.congr_fun hevalv p
  have hevalker : ∀ (D : CommRingCat.{ringUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial (Fin n) R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      RingHom.ker π.hom ≤ RingHom.ker
        (MvPolynomial.eval₂Hom u.hom
          fun i ↦ v.hom (q.hom (MvPolynomial.X i))) := by
    intro D u v huv
    rw [hker, Ideal.span_le, Set.range_subset_iff]
    intro i
    change MvPolynomial.eval₂ u.hom
      (fun j ↦ v.hom (q.hom (MvPolynomial.X j)))
      (MvPolynomial.map f.hom (r i)) = 0
    rw [eval_map _ u v huv, hqr, map_zero]
  set desc : ∀ (D : CommRingCat.{ringUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial (Fin n) R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      (T ⟶ D) :=
    fun D u v huv ↦ ofHom
      (RingHom.liftOfSurjective π.hom hπ
        ⟨_, hevalker D u v huv⟩) with hdesc
  have hdescπ : ∀ (D : CommRingCat.{ringUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial (Fin n) R ⧸ I) ⟶ D)
      (huv : f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v)
      (p : MvPolynomial (Fin n) S),
      (desc D u v huv).hom (π.hom p) =
        MvPolynomial.eval₂ u.hom
          (fun i ↦ v.hom (q.hom (MvPolynomial.X i))) p := by
    intro D u v huv p
    rw [hdesc]
    exact RingHom.liftOfSurjective_comp_apply π.hom hπ
      ⟨_, hevalker D u v huv⟩ p
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun cocone ↦ desc _ cocone.inl cocone.inr cocone.condition) ?_ ?_ ?_⟩⟩
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change π.hom (MvPolynomial.C (f.hom a)) =
      g.hom (q.hom (MvPolynomial.C a))
    rw [hgq, MvPolynomial.map_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change (desc _ cocone.inl cocone.inr cocone.condition).hom
      (π.hom (MvPolynomial.C a)) = cocone.inl.hom a
    rw [hdescπ _ cocone.inl cocone.inr cocone.condition, MvPolynomial.eval₂_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (desc _ cocone.inl cocone.inr cocone.condition).hom
      (g.hom (q.hom p)) = cocone.inr.hom (q.hom p)
    rw [hgq, hdescπ _ cocone.inl cocone.inr cocone.condition]
    exact eval_map _ cocone.inl cocone.inr cocone.condition p
  · intro cocone candidate left_eq right_eq
    have hcomp : candidate.hom.comp π.hom =
        MvPolynomial.eval₂Hom cocone.inl.hom
          (fun i ↦ cocone.inr.hom (q.hom (MvPolynomial.X i))) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · rw [MvPolynomial.eval₂Hom_C]
        exact congrArg (fun ringMorphism ↦ CommRingCat.Hom.hom ringMorphism a) left_eq
      · rw [MvPolynomial.eval₂Hom_X']
        change candidate.hom (π.hom (MvPolynomial.X i)) =
          cocone.inr.hom (q.hom (MvPolynomial.X i))
        rw [show π.hom (MvPolynomial.X i) =
            g.hom (q.hom (MvPolynomial.X i)) by
          rw [hgq, MvPolynomial.map_X]]
        exact congrArg (fun ringMorphism ↦
          CommRingCat.Hom.hom ringMorphism (q.hom (MvPolynomial.X i))) right_eq
    refine CommRingCat.hom_ext (RingHom.ext fun t ↦ ?_)
    obtain ⟨p, rfl⟩ := hπ t
    change candidate.hom (π.hom p) =
      (desc _ cocone.inl cocone.inr cocone.condition).hom (π.hom p)
    rw [hdescπ _ cocone.inl cocone.inr cocone.condition]
    exact DFunLike.congr_fun hcomp p

variable {Index : Type categoryObj} [Category.{categoryHom} Index] [IsFiltered Index]
  (diagram : Index ⥤ CommRingCat.{ringUniverse}) (cocone : Cocone diagram)
  [PreservesColimit diagram (forget CommRingCat)] {indeterminates : Type*}

omit [IsFiltered Index] [PreservesColimit diagram (forget CommRingCat)] in
private lemma range_map_ι_app_subset {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) :
    Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app sourceIndex).hom) ⊆
      Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app targetIndex).hom) := by
  have maps_comp : (cocone.ι.app targetIndex).hom.comp (diagram.map transition).hom =
      (cocone.ι.app sourceIndex).hom :=
    congrArg CommRingCat.Hom.hom (cocone.w transition)
  rintro _ ⟨p, rfl⟩
  exact ⟨MvPolynomial.map (diagram.map transition).hom p, by
    rw [MvPolynomial.map_map, maps_comp]⟩

variable (colimit : IsColimit cocone)

include colimit in
/-- Every p over a filtered colimit of rings lifts to one stage. -/
private lemma exists_mem_range_map_ι_app (p : MvPolynomial indeterminates cocone.pt) :
    ∃ stage, p ∈ Set.range (MvPolynomial.map (σ := indeterminates)
      (cocone.ι.app stage).hom) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨stage, a, ha⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) colimit)
        (show ((forget CommRingCat).mapCocone cocone).pt from a)
    exact ⟨stage, MvPolynomial.C a, by
      rw [MvPolynomial.map_C]
      exact congrArg MvPolynomial.C ha⟩
  | add p q hp hq =>
    obtain ⟨i, p, rfl⟩ := hp
    obtain ⟨j, q, rfl⟩ := hq
    obtain ⟨pᵢ, hpᵢ⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.leftToMax i j) ⟨p, rfl⟩
    obtain ⟨qⱼ, hqⱼ⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.rightToMax i j) ⟨q, rfl⟩
    exact ⟨IsFiltered.max i j, pᵢ + qⱼ, by
      rw [map_add]
      exact congrArg₂ (· + ·) hpᵢ hqⱼ⟩
  | mul_X p j polynomialLift =>
    obtain ⟨stage, p, rfl⟩ := polynomialLift
    exact ⟨stage, p * MvPolynomial.X j, by
      rw [map_mul]
      exact congrArg (MvPolynomial.map (cocone.ι.app stage).hom p * ·)
        (MvPolynomial.map_X _ _)⟩

include colimit in
/-- A finite set of polynomials over a filtered colimit lifts to a common stage. -/
private lemma exists_forall_mem_range_map_ι_app
    (polynomials : Finset (MvPolynomial indeterminates cocone.pt)) :
    ∃ stage, ∀ p ∈ polynomials,
      p ∈ Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app stage).hom) := by
  classical
  choose j hlift using fun p : polynomials ↦
    exists_mem_range_map_ι_app diagram cocone colimit
      (p : MvPolynomial indeterminates cocone.pt)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨k, fun p membership ↦ ?_⟩
  obtain ⟨transition⟩ := hk
    (Finset.mem_image_of_mem j (Finset.mem_univ (⟨p, membership⟩ : polynomials)))
  exact range_map_ι_app_subset diagram cocone transition (hlift ⟨p, membership⟩)

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
  obtain ⟨stage, hlift⟩ := exists_forall_mem_range_map_ι_app diagram cocone colimit rels
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
