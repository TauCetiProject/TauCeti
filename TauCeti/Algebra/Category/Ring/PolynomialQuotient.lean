/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Polynomial quotient pushouts

Extension of coefficients carries a quotient by relations to the corresponding pushout.
-/

public section

universe ringUniverse variableUniverse

open CategoryTheory Limits

namespace CommRingCat

/-- Relations defined over the source ring give a pushout presentation of the quotient after
extending coefficients. -/
lemma exists_isPushout_quotient_span
    {R S T : CommRingCat.{max ringUniverse variableUniverse}}
    (f : R ⟶ S) {σ : Type variableUniverse}
    {ι : Type*} (r : ι → MvPolynomial σ R)
    (π : of (MvPolynomial σ S) ⟶ T)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker π.hom = Ideal.span
      (Set.range fun i ↦ MvPolynomial.map f.hom (r i))) :
    ∃ g : of (MvPolynomial σ R ⧸
        Ideal.span (Set.range r)) ⟶ T,
      IsPushout f
        (ofHom MvPolynomial.C ≫ ofHom (Ideal.Quotient.mk (Ideal.span (Set.range r))))
        (ofHom MvPolynomial.C ≫ π) g := by
  set I : Ideal (MvPolynomial σ R) :=
    Ideal.span (Set.range r) with hI
  set q : of (MvPolynomial σ R) ⟶
      of (MvPolynomial σ R ⧸ I) :=
    ofHom (Ideal.Quotient.mk I) with hq
  set φ : of (MvPolynomial σ R) ⟶
      of (MvPolynomial σ S) :=
    ofHom (MvPolynomial.map f.hom) with hφ
  have relations_mem_kernel : I ≤ RingHom.ker (φ ≫ π).hom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    -- Composition of CommRingCat morphisms evaluates as composition of their ring homomorphisms.
    change MvPolynomial.map f.hom (r i) ∈ RingHom.ker π.hom
    rw [hker]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨ofHom (Ideal.Quotient.lift I (φ ≫ π).hom
    fun p membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership)), ?_⟩
  set g : of (MvPolynomial σ R ⧸ I) ⟶ T :=
    ofHom (Ideal.Quotient.lift I (φ ≫ π).hom
      fun p membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership))
    with hg
  have hgq : ∀ p : MvPolynomial σ R,
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
  have eval_map : ∀ (D : CommRingCat.{max ringUniverse variableUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial σ R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      ∀ p : MvPolynomial σ R,
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
  have hevalker : ∀ (D : CommRingCat.{max ringUniverse variableUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial σ R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      RingHom.ker π.hom ≤ RingHom.ker
        (MvPolynomial.eval₂Hom u.hom
          fun i ↦ v.hom (q.hom (MvPolynomial.X i))) := by
    intro D u v huv
    rw [hker, Ideal.span_le, Set.range_subset_iff]
    intro i
    -- Kernel membership is vanishing under the evaluation homomorphism used to define desc.
    change MvPolynomial.eval₂ u.hom
      (fun j ↦ v.hom (q.hom (MvPolynomial.X j)))
      (MvPolynomial.map f.hom (r i)) = 0
    rw [eval_map _ u v huv, hqr, map_zero]
  set desc : ∀ (D : CommRingCat.{max ringUniverse variableUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial σ R ⧸ I) ⟶ D),
      f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v →
      (T ⟶ D) :=
    fun D u v huv ↦ ofHom
      (RingHom.liftOfSurjective π.hom hπ
        ⟨_, hevalker D u v huv⟩) with hdesc
  have hdescπ : ∀ (D : CommRingCat.{max ringUniverse variableUniverse})
      (u : S ⟶ D)
      (v : of (MvPolynomial σ R ⧸ I) ⟶ D)
      (huv : f ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v)
      (p : MvPolynomial σ S),
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
    -- Evaluate the categorical square on coefficient constants through ofHom.
    change π.hom (MvPolynomial.C (f.hom a)) =
      g.hom (q.hom (MvPolynomial.C a))
    rw [hgq, MvPolynomial.map_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    -- Evaluate the categorical cocone identity through the underlying ring homomorphisms.
    change (desc _ cocone.inl cocone.inr cocone.condition).hom
      (π.hom (MvPolynomial.C a)) = cocone.inl.hom a
    rw [hdescπ _ cocone.inl cocone.inr cocone.condition, MvPolynomial.eval₂_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    -- Evaluate the categorical cocone identity through the underlying ring homomorphisms.
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
        -- Evaluate the candidate morphism on the image of a polynomial variable.
        change candidate.hom (π.hom (MvPolynomial.X i)) =
          cocone.inr.hom (q.hom (MvPolynomial.X i))
        have hX : π.hom (MvPolynomial.X i) = g.hom (q.hom (MvPolynomial.X i)) := by
          rw [hgq, MvPolynomial.map_X]
        rw [hX]
        exact congrArg (fun ringMorphism ↦
          CommRingCat.Hom.hom ringMorphism (q.hom (MvPolynomial.X i))) right_eq
    refine CommRingCat.hom_ext (RingHom.ext fun t ↦ ?_)
    obtain ⟨p, rfl⟩ := hπ t
    -- Evaluate the morphism equality on the chosen representative supplied by surjectivity.
    change candidate.hom (π.hom p) =
      (desc _ cocone.inl cocone.inr cocone.condition).hom (π.hom p)
    rw [hdescπ _ cocone.inl cocone.inr cocone.condition]
    exact DFunLike.congr_fun hcomp p

end CommRingCat
