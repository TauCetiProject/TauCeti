/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.Ideal.AssociatedGraded
public import TauCeti.RingTheory.ReesAlgebra.Grading

/-!
# The ordinary Rees quotient and the associated graded ring

The quotient of `R[It]` by the extended coefficient ideal `I R[It]` is the associated
graded ring `⨁ n, I^n / I^(n+1)`. The comparison sends a Rees monomial to its homogeneous
class, not to its value at zero. Its inverse therefore recovers the quotient class of
an actual polynomial, and each coordinate is the class of its actual coefficient.

We use Mathlib's `mem_map_algebraMap_reesAlgebra_iff` for the coefficient ideal and the
existing Rees grading. In particular this is the ordinary ideal-power construction,
not specialization of an increasing filtration at a parameter belonging to the Rees algebra.
The direct-sum algebra construction follows the symbol-map pattern in
`TauCeti.Algebra.wordFiltration.reesSymbol`.

## References

* Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
* The Stacks Project, Section 10.58 (associated graded rings).
-/

public section

open Polynomial DirectSum

namespace Ideal.AssociatedGraded

variable {R : Type*} [CommRing R] (I : Ideal R)

private noncomputable def reesComponent (n : ℕ) :
    reesAlgebra.grade I n →ₗ[R] I.AssociatedGraded :=
  mk I n ∘ₗ LinearMap.codRestrict (I ^ n)
    ((Polynomial.lcoeff R n).comp
      ((reesAlgebra I).val.toLinearMap.comp (reesAlgebra.grade I n).subtype))
    (fun f => (mem_reesAlgebra_iff I _).mp (f : reesAlgebra I).2 n)

private theorem reesComponent_apply (n : ℕ) (f : reesAlgebra.grade I n) :
    reesComponent I n f = mk I n
      ⟨((f : reesAlgebra I) : R[X]).coeff n,
        (mem_reesAlgebra_iff I _).mp (f : reesAlgebra I).2 n⟩ := rfl

/-- The symbol map of the ordinary Rees algebra, taking each coefficient to its
homogeneous quotient class. -/
noncomputable def ofRees : reesAlgebra I →ₐ[R] I.AssociatedGraded := by
  have h1 : reesComponent I 0 (GradedMonoid.GOne.one
      (A := fun n => reesAlgebra.grade I n)) = 1 := by
    rw [reesComponent_apply, mk_zero]
    simp
  have hm {i j} (a : reesAlgebra.grade I i) (b : reesAlgebra.grade I j) :
      reesComponent I (i + j) (GradedMonoid.GMul.mul
        (A := fun n => reesAlgebra.grade I n) a b) =
        reesComponent I i a * reesComponent I j b := by
    simp only [reesComponent_apply, mk_mul_mk]
    congr 1
    apply Subtype.ext
    simp only [SetLike.coe_gMul, Subalgebra.coe_mul]
    rw [← reesAlgebra.mem_grade_iff_monomial_coeff.mp a.2,
      ← reesAlgebra.mem_grade_iff_monomial_coeff.mp b.2]
    simp [monomial_mul_monomial]
  exact (DirectSum.toAlgebra R _ (reesComponent I) h1 @hm).comp
    (DirectSum.decomposeAlgEquiv (reesAlgebra.grade I)).toAlgHom

/-- The symbol of a homogeneous Rees monomial is its homogeneous class. -/
@[simp]
theorem ofRees_monomial (n : ℕ) (x : R) (hx : x ∈ I ^ n) :
    ofRees I ⟨monomial n x, reesAlgebra.monomial_mem.mpr hx⟩ = mk I n ⟨x, hx⟩ := by
  simp only [ofRees, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    DirectSum.decomposeAlgEquiv_apply]
  rw [DirectSum.decompose_of_mem _ (reesAlgebra.monomial_mem_grade hx)]
  rw [DirectSum.toAlgebra_apply]
  -- The algebra constructor uses the underlying additive homomorphisms.
  erw [DirectSum.toSemiring_of]
  simp [reesComponent_apply]

/-- Every associated-graded element has a polynomial lift in the ordinary Rees algebra. -/
theorem ofRees_surjective : Function.Surjective (ofRees I) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n x =>
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      refine ⟨⟨monomial n x, reesAlgebra.monomial_mem.mpr x.2⟩, ?_⟩
      simpa only [mk_apply] using ofRees_monomial I n x x.2
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ p q⟩

/-- The degree-`n` coordinate of the symbol is the class of the `n`-th coefficient. -/
@[simp]
theorem ofRees_apply (f : reesAlgebra I) (n : ℕ) :
    ofRees I f n = Submodule.Quotient.mk
      (⟨(f : R[X]).coeff n, (mem_reesAlgebra_iff I _).mp f.2 n⟩ : ↥(I ^ n)) := by
  classical
  conv_lhs => rw [reesAlgebra.as_sum_support f, map_sum]
  have hm (j : ℕ) :
      ofRees I ⟨monomial j ((f : R[X]).coeff j), reesAlgebra.monomial_coeff_mem f j⟩ =
        mk I j ⟨(f : R[X]).coeff j, (mem_reesAlgebra_iff I _).mp f.2 j⟩ :=
    ofRees_monomial I j _ _
  simp only [DirectSum.sum_apply]
  simp_rw [hm, mk_apply]
  by_cases hn : n ∈ (f : R[X]).support
  · simp [DirectSum.of_apply, hn]
  · have hc := Polynomial.notMem_support_iff.mp hn
    simp only [DirectSum.of_apply, Finset.sum_dite_eq', hn, ↓reduceIte, hc]
    exact (Submodule.Quotient.mk_zero _).symm

/-- The symbol kernel is precisely the extended coefficient ideal. -/
theorem ker_ofRees :
    RingHom.ker (ofRees I) = I.map (algebraMap R (reesAlgebra I)) := by
  ext f
  rw [RingHom.mem_ker, mem_map_algebraMap_reesAlgebra_iff, DirectSum.ext_iff]
  simp only [ofRees_apply, DirectSum.zero_apply, gradedPiece_mk_eq_zero_iff]

/-- The extended coefficient ideal is homogeneous for the ordinary Rees grading. -/
theorem isHomogeneous_map_algebraMap :
    (I.map (algebraMap R (reesAlgebra I))).IsHomogeneous (reesAlgebra.grade I) := by
  intro n f hf
  rw [mem_map_algebraMap_reesAlgebra_iff] at hf ⊢
  intro m
  rw [reesAlgebra.coe_decompose_apply, coeff_monomial, Finsupp.single_apply]
  split_ifs with h
  · subst m
    exact hf n
  · exact zero_mem _

/-- The residue coefficient algebra structure on the ordinary Rees quotient. -/
noncomputable instance instAlgebraReesQuotient :
    Algebra (R ⧸ I) (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

/-- The residue scalar map is induced by the constant Rees polynomials. -/
@[simp]
theorem algebraMap_reesQuotient_mk (r : R) :
    algebraMap (R ⧸ I) (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
      (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk _ (algebraMap R (reesAlgebra I) r) := (rfl)

/-- The residue coefficient structure extends the original coefficient structure. -/
instance : IsScalarTower R (R ⧸ I)
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The ordinary Rees quotient is the associated graded algebra, over `R / I`. -/
noncomputable def reesQuotientEquiv :
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) ≃ₐ[R ⧸ I]
      I.AssociatedGraded := by
  let e := (Ideal.quotientEquivAlgOfEq R (ker_ofRees I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (ofRees_surjective I))
  refine AlgEquiv.ofRingEquiv (f := e.toRingEquiv) ?_
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [algebraMap_reesQuotient_mk, Ideal.Quotient.mk_algebraMap,
    algebraMap_quotient_mk]
  exact e.commutes r

/-- The quotient comparison sends a polynomial class to its symbol. -/
@[simp]
theorem reesQuotientEquiv_mk (f : reesAlgebra I) :
    reesQuotientEquiv I (Ideal.Quotient.mk _ f) = ofRees I f := by
  rw [reesQuotientEquiv, AlgEquiv.ofRingEquiv_apply]
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective (ofRees_surjective I))
    (Ideal.quotientEquivAlgOfEq_mk R (ker_ofRees I).symm f)).trans
      (Ideal.quotientKerAlgEquivOfSurjective_mk (ofRees_surjective I) f)

/-- On each homogeneous class, the inverse comparison is the actual Rees monomial class. -/
@[simp]
theorem reesQuotientEquiv_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    (reesQuotientEquiv I).symm (mk I n x) =
      Ideal.Quotient.mk _ ⟨monomial n x, reesAlgebra.monomial_mem.mpr x.2⟩ := by
  apply (reesQuotientEquiv I).injective
  simp

/-- The quotient carries the grading descended from the ordinary Rees grading. -/
noncomputable instance instGradedAlgebraReesQuotient :
    GradedAlgebra (TauCeti.GradedAlgebra.quotientPiece (reesAlgebra.grade I)
      (I.map (algebraMap R (reesAlgebra I)))) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece _ _
    (isHomogeneous_map_algebraMap I)

/-- The degree-`n` quotient coefficient, linear over the original coefficient ring. -/
noncomputable def reesCoeff (n : ℕ) :
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) →ₗ[R] I.GradedPiece n :=
  DirectSum.component R ℕ I.GradedPiece n ∘ₗ
    (reesQuotientEquiv I).toLinearMap.restrictScalars R

/-- Quotient coefficients are represented by actual polynomial coefficients. -/
@[simp]
theorem reesCoeff_mk (n : ℕ) (f : reesAlgebra I) :
    reesCoeff I n (Ideal.Quotient.mk _ f) = Submodule.Quotient.mk
      (⟨(f : R[X]).coeff n, (mem_reesAlgebra_iff I _).mp f.2 n⟩ : ↥(I ^ n)) := by
  simp [reesCoeff, ← DirectSum.apply_eq_component]

/-- Inclusion of a homogeneous quotient piece as a Rees quotient class. -/
noncomputable def reesIncl (n : ℕ) :
    I.GradedPiece n →ₗ[R] (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  (reesQuotientEquiv I).symm.toLinearMap.restrictScalars R ∘ₗ
    DirectSum.lof R ℕ I.GradedPiece n

/-- A homogeneous inclusion is represented by the corresponding Rees monomial. -/
@[simp]
theorem reesIncl_mk (n : ℕ) (x : ↥(I ^ n)) :
    reesIncl I n (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk _ ⟨monomial n x, reesAlgebra.monomial_mem.mpr x.2⟩ := by
  simpa only [mk_apply, reesIncl, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, DirectSum.lof_eq_of] using
    reesQuotientEquiv_symm_mk I n x

/-- The quotient coefficient retracts the homogeneous inclusion in the same degree. -/
@[simp]
theorem reesCoeff_reesIncl (n : ℕ) (x : I.GradedPiece n) :
    reesCoeff I n (reesIncl I n x) = x := by
  simp [reesCoeff, reesIncl]

/-- Quotient coefficients kill homogeneous inclusions in every other degree. -/
@[simp]
theorem reesCoeff_reesIncl_of_ne {m n : ℕ} (h : m ≠ n) (x : I.GradedPiece n) :
    reesCoeff I m (reesIncl I n x) = 0 := by
  simp [reesCoeff, reesIncl, DirectSum.component.of, h.symm]

/-- Equality of every quotient coefficient detects equality in the ordinary Rees quotient. -/
@[ext]
theorem reesQuotient_ext
    {x y : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))}
    (h : ∀ n, reesCoeff I n x = reesCoeff I n y) : x = y := by
  apply (reesQuotientEquiv I).injective
  exact DirectSum.ext h

/-- Finitely many homogeneous quotient coefficients reconstruct a polynomial class. -/
theorem sum_reesIncl_reesCoeff (f : reesAlgebra I) :
    ∑ n ∈ (f : R[X]).support,
      reesIncl I n (reesCoeff I n (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  simp only [reesCoeff_mk, reesIncl_mk]
  simpa only [map_sum] using congrArg (Ideal.Quotient.mk
    (I.map (algebraMap R (reesAlgebra I)))) (reesAlgebra.as_sum_support f).symm

/-- The image of the homogeneous inclusion is precisely the descended Rees component. -/
theorem range_reesIncl (n : ℕ) :
    LinearMap.range (reesIncl I n) =
      TauCeti.GradedAlgebra.quotientPiece (reesAlgebra.grade I)
        (I.map (algebraMap R (reesAlgebra I))) n := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | _ a =>
      rw [reesIncl_mk]
      exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
        (reesAlgebra.monomial_mem_grade a.2)
  · intro hx
    obtain ⟨f, hf, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp hx
    obtain ⟨r, hr, heq⟩ := reesAlgebra.mem_grade_iff.mp hf
    refine ⟨Submodule.Quotient.mk (⟨r, hr⟩ : ↥(I ^ n)), ?_⟩
    rw [reesIncl_mk]
    exact congrArg (Ideal.Quotient.mk _) (Subtype.ext heq)

end Ideal.AssociatedGraded
