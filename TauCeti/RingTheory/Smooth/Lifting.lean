/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import TauCeti.RingTheory.Smooth.Jacobian

/-!
# Lifting standard smooth and étale algebras along surjections

Every standard smooth `R₀`-algebra `B₀` of relative dimension `d` lifts along a surjective
`R`-algebra map `R → R₀` to a standard smooth `R`-algebra `A` of relative dimension `d` with
`R₀ ⊗[R] A ≃ₐ[R₀] B₀`. Taking `d = 0`, where standard smoothness of relative dimension zero
coincides with étaleness (`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`), every
étale `R₀`-algebra lifts along a surjective ring map to an étale `R`-algebra in the universe of
`R`. Note that finiteness over `R₀` is not preserved in general before localizing or passing to a
clopen summand over a Henselian pair.

## Main results

* `Algebra.SubmersivePresentation.exists_tensorProduct_algEquiv_of_surjective`: the algebra
  defined by lifting the relations of a submersive presentation along `R → R₀` and inverting its
  selected Jacobian minor is standard smooth over `R` of the same dimension and base-changes to the
  given `R₀`-algebra.
* `Algebra.IsStandardSmoothOfRelativeDimension.exists_tensorProduct_algEquiv_of_surjective`:
  standard smooth algebras of relative dimension `d` lift along surjective algebra maps.
* `Algebra.IsStandardSmooth.exists_tensorProduct_algEquiv_of_surjective`: standard smooth algebras
  lift along surjective algebra maps.
* `Algebra.Etale.exists_tensorProduct_algEquiv_of_surjective`: étale algebras lift along
  surjective algebra maps.

## References

* [Stacks Project, Lemma 10.137.17](https://stacks.math.columbia.edu/tag/00TL) (lifting standard
  smooth algebras along surjections; see also Lemma 15.13.1 (0D4A) for the étale case).
-/

public section

open MvPolynomial TensorProduct

universe u

namespace Algebra

section SubmersivePresentation

variable {R : Type u} {R₀ B₀ : Type*} {ι σ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]
  [CommRing B₀] [Algebra R₀ B₀] [Finite σ]

/-- Quotient map from `MvPolynomial ι R ⧸ Ideal.span (Set.range v)` to `B₀` induced by evaluating
at `P₀.val`, when `v` lifts the relations of `P₀` along `R → R₀`. -/
private noncomputable def liftedQuotientHom [Algebra R B₀] [IsScalarTower R R₀ B₀]
    (P₀ : SubmersivePresentation R₀ B₀ ι σ) (v : σ → MvPolynomial ι R)
    (hv : ∀ j, MvPolynomial.map (algebraMap R R₀) (v j) = P₀.relation j) :
    MvPolynomial ι R ⧸ Ideal.span (Set.range v) →ₐ[R] B₀ :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range v)) (MvPolynomial.aeval (R := R) P₀.val) fun p hp ↦ by
    have hker : Ideal.span (Set.range v) ≤ RingHom.ker (MvPolynomial.aeval (R := R) P₀.val) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      rw [← MvPolynomial.aeval_map_algebraMap R₀ P₀.val, hv, P₀.aeval_val_relation]
    exact hker hp

/-- `liftedQuotientHom` sends the naive Jacobian determinant of the lifted relations `v` to
`P₀.jacobian`. -/
private theorem liftedQuotientHom_jacobian [Algebra R B₀] [IsScalarTower R R₀ B₀]
    (P₀ : SubmersivePresentation R₀ B₀ ι σ) (v : σ → MvPolynomial ι R)
    (hv : ∀ j, MvPolynomial.map (algebraMap R R₀) (v j) = P₀.relation j) :
    liftedQuotientHom P₀ v hv
        (PreSubmersivePresentation.naive (v := v) P₀.map P₀.map_inj).jacobian =
      P₀.jacobian := by
  classical
  cases nonempty_fintype σ
  let P := PreSubmersivePresentation.naive (v := v) P₀.map P₀.map_inj
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, P₀.jacobian_eq_jacobiMatrix_det]
  have hmat : P₀.jacobiMatrix =
      (MvPolynomial.map (algebraMap R R₀)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, PreSubmersivePresentation.jacobiMatrix_apply,
      PreSubmersivePresentation.jacobiMatrix_apply]
    have hrel : P.relation j = v j := rfl
    have hmap : P.map i = P₀.map i := rfl
    rw [hrel, hmap, ← hv j, MvPolynomial.pderiv_map]
  have hdet : MvPolynomial.map (algebraMap R R₀) P.jacobiMatrix.det = P₀.jacobiMatrix.det := by
    rw [hmat, RingHom.map_det]
  calc liftedQuotientHom P₀ v hv (algebraMap P.Ring _ P.jacobiMatrix.det)
      = MvPolynomial.aeval (R := R) P₀.val P.jacobiMatrix.det := rfl
    _ = MvPolynomial.aeval (R := R₀) P₀.val
          (MvPolynomial.map (algebraMap R R₀) P.jacobiMatrix.det) :=
        (MvPolynomial.aeval_map_algebraMap R₀ P₀.val P.jacobiMatrix.det).symm
    _ = algebraMap P₀.Ring B₀ P₀.jacobiMatrix.det := by
        rw [hdet, Generators.algebraMap_apply]

/-- Inverse `R₀`-algebra homomorphism `B₀ →ₐ[R₀] R₀ ⊗[R] A` sending `P₀.val i` to the canonical
generator `1 ⊗ₜ X i` in `R₀ ⊗[R] A`. -/
private noncomputable def liftedBaseChangeInv (P₀ : SubmersivePresentation R₀ B₀ ι σ)
    (v : σ → MvPolynomial ι R)
    (hv : ∀ j, MvPolynomial.map (algebraMap R R₀) (v j) = P₀.relation j)
    {A : Type u} [CommRing A] [Algebra R A]
    [Algebra (MvPolynomial ι R ⧸ Ideal.span (Set.range v)) A]
    [IsScalarTower R (MvPolynomial ι R ⧸ Ideal.span (Set.range v)) A] :
    B₀ →ₐ[R₀] R₀ ⊗[R] A := by
  let C := MvPolynomial ι R ⧸ Ideal.span (Set.range v)
  let xA : ι → R₀ ⊗[R] A := fun i ↦
    1 ⊗ₜ[R] algebraMap C A (Ideal.Quotient.mk (Ideal.span (Set.range v)) (MvPolynomial.X i))
  let g₀ : MvPolynomial ι R₀ →ₐ[R₀] R₀ ⊗[R] A := MvPolynomial.aeval xA
  have hg₀_map (p : MvPolynomial ι R) :
      g₀ (MvPolynomial.map (algebraMap R R₀) p) =
        1 ⊗ₜ[R] algebraMap C A (Ideal.Quotient.mk (Ideal.span (Set.range v)) p) := by
    have hcomp : (g₀.restrictScalars R).comp (MvPolynomial.mapAlgHom (Algebra.ofId R R₀)) =
        Algebra.TensorProduct.includeRight.comp
          ((IsScalarTower.toAlgHom R C A).comp (Ideal.Quotient.mkₐ R _)) := by
      ext i
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', MvPolynomial.mapAlgHom_apply,
        MvPolynomial.map_X, g₀, MvPolynomial.aeval_X]
      rfl
    exact DFunLike.congr_fun hcomp p
  have hkerB₀ : P₀.ker ≤ RingHom.ker g₀ := by
    rw [← P₀.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    rw [← hv j, hg₀_map,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)),
      map_zero, TensorProduct.tmul_zero]
  exact (Ideal.Quotient.liftₐ P₀.ker g₀ (fun p hp ↦ hkerB₀ hp)).comp
    (P₀.quotientEquiv.restrictScalars R₀).symm.toAlgHom

private theorem liftedBaseChangeInv_val (P₀ : SubmersivePresentation R₀ B₀ ι σ)
    (v : σ → MvPolynomial ι R)
    (hv : ∀ j, MvPolynomial.map (algebraMap R R₀) (v j) = P₀.relation j)
    {A : Type u} [CommRing A] [Algebra R A]
    [Algebra (MvPolynomial ι R ⧸ Ideal.span (Set.range v)) A]
    [IsScalarTower R (MvPolynomial ι R ⧸ Ideal.span (Set.range v)) A] (i : ι) :
    liftedBaseChangeInv P₀ v hv (A := A) (P₀.val i) =
      1 ⊗ₜ[R] algebraMap (MvPolynomial ι R ⧸ Ideal.span (Set.range v)) A
        (Ideal.Quotient.mk (Ideal.span (Set.range v)) (MvPolynomial.X i)) := by
  have hsymm : P₀.quotientEquiv.symm (P₀.val i) = Ideal.Quotient.mk P₀.ker (MvPolynomial.X i) :=
    P₀.quotientEquiv.symm_apply_eq.mpr (by simp [Generators.algebraMap_apply])
  simp only [liftedBaseChangeInv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_restrictScalars, AlgEquiv.coe_restrictScalars, hsymm]
  exact MvPolynomial.aeval_X _ i

/-- Lift the target of a submersive presentation over `R₀` along a surjective algebra map
`R → R₀` by lifting its relations to `MvPolynomial ι R` and localizing away from the resulting
Jacobian minor. -/
theorem SubmersivePresentation.exists_tensorProduct_algEquiv_of_surjective [Finite ι]
    (P₀ : SubmersivePresentation R₀ B₀ ι σ) (hsurj : Function.Surjective (algebraMap R R₀)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      IsStandardSmoothOfRelativeDimension P₀.dimension R A ∧ Nonempty (R₀ ⊗[R] A ≃ₐ[R₀] B₀) := by
  let : Algebra R B₀ := ((algebraMap R₀ B₀).comp (algebraMap R R₀)).toAlgebra
  have : IsScalarTower R R₀ B₀ := .of_algebraMap_eq' rfl
  choose v hv using fun j ↦ MvPolynomial.map_surjective (algebraMap R R₀) hsurj (P₀.relation j)
  let C := MvPolynomial ι R ⧸ Ideal.span (Set.range v)
  let P : PreSubmersivePresentation R C ι σ :=
    PreSubmersivePresentation.naive (v := v) P₀.map P₀.map_inj
  let A := Localization.Away P.jacobian
  have hdim : P.dimension = P₀.dimension := rfl
  have hsmooth : IsStandardSmoothOfRelativeDimension P₀.dimension R A :=
    hdim ▸ P.isStandardSmoothOfRelativeDimension_localizationAway A
  let φA : A →ₐ[R] B₀ := IsLocalization.Away.liftAlgHom P.jacobian (f := liftedQuotientHom P₀ v hv)
    (by dsimp only [P]; rw [liftedQuotientHom_jacobian P₀ v hv]; exact P₀.jacobian_isUnit)
  let fwd : R₀ ⊗[R] A →ₐ[R₀] B₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ B₀) φA fun _ _ ↦ mul_comm _ _
  let bwd : B₀ →ₐ[R₀] R₀ ⊗[R] A := liftedBaseChangeInv P₀ v hv
  have hfwd_X (i : ι) :
      fwd (1 ⊗ₜ[R] algebraMap C A (Ideal.Quotient.mk (Ideal.span (Set.range v))
        (MvPolynomial.X i))) = P₀.val i := by
    have htmul : fwd (1 ⊗ₜ[R] algebraMap C A
        (Ideal.Quotient.mk (Ideal.span (Set.range v)) (MvPolynomial.X i))) =
        Algebra.ofId R₀ B₀ 1 * φA (algebraMap C A
          (Ideal.Quotient.mk (Ideal.span (Set.range v)) (MvPolynomial.X i))) := rfl
    rw [htmul, map_one, one_mul]
    dsimp only [φA]
    rw [IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    exact MvPolynomial.aeval_X (R := R) P₀.val i
  refine ⟨A, inferInstance, inferInstance, hsmooth, ⟨AlgEquiv.ofAlgHom fwd bwd ?_ ?_⟩⟩
  · have hq : (fwd.comp bwd).comp (P₀.quotientEquiv.restrictScalars R₀).toAlgHom =
        (P₀.quotientEquiv.restrictScalars R₀).toAlgHom := by
      refine Ideal.Quotient.algHom_ext R₀ (MvPolynomial.algHom_ext fun i ↦ ?_)
      have hval : P₀.quotientEquiv (Ideal.Quotient.mk P₀.ker (MvPolynomial.X i)) = P₀.val i := by
        simp [Generators.algebraMap_apply]
      simp [bwd, C, AlgHom.comp_apply, hval, liftedBaseChangeInv_val, hfwd_X]
    ext x
    obtain ⟨q, rfl⟩ := (P₀.quotientEquiv.restrictScalars R₀).surjective x
    exact DFunLike.congr_fun hq q
  · refine Algebra.TensorProduct.ext (by ext) ?_
    apply IsLocalization.algHom_ext (.powers P.jacobian)
    refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i ↦ ?_)
    have halg (c : C) : Algebra.algHom R C A c = algebraMap C A c := rfl
    simp [bwd, C, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, halg, hfwd_X,
      liftedBaseChangeInv_val]

end SubmersivePresentation

/-- **Standard smooth algebras of given relative dimension lift along surjections.** Let
`R → R₀` be a surjective algebra map and let `B₀` be standard smooth of relative dimension `d`
over `R₀`. Then there is a standard smooth `R`-algebra `A` of relative dimension `d`, in the
universe of `R`, whose base change to `R₀` is `R₀`-isomorphic to `B₀`. -/
theorem IsStandardSmoothOfRelativeDimension.exists_tensorProduct_algEquiv_of_surjective
    (d : ℕ) (R : Type u) (R₀ B₀ : Type*) [CommRing R] [CommRing R₀] [Algebra R R₀]
    [CommRing B₀] [Algebra R₀ B₀] [IsStandardSmoothOfRelativeDimension d R₀ B₀]
    (hsurj : Function.Surjective (algebraMap R R₀)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      IsStandardSmoothOfRelativeDimension d R A ∧ Nonempty (R₀ ⊗[R] A ≃ₐ[R₀] B₀) := by
  obtain ⟨ι, σ, _, _, P₀, rfl⟩ := IsStandardSmoothOfRelativeDimension.out (n := d) (R := R₀)
    (S := B₀)
  exact P₀.exists_tensorProduct_algEquiv_of_surjective hsurj

/-- **Standard smooth algebras lift along surjections.** -/
theorem IsStandardSmooth.exists_tensorProduct_algEquiv_of_surjective
    (R : Type u) (R₀ B₀ : Type*) [CommRing R] [CommRing R₀] [Algebra R R₀]
    [CommRing B₀] [Algebra R₀ B₀] [IsStandardSmooth R₀ B₀]
    (hsurj : Function.Surjective (algebraMap R R₀)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      IsStandardSmooth R A ∧ Nonempty (R₀ ⊗[R] A ≃ₐ[R₀] B₀) := by
  obtain ⟨ι, σ, _, _, ⟨P₀⟩⟩ := IsStandardSmooth.out (R := R₀) (S := B₀)
  obtain ⟨A, _, _, hA, he⟩ := P₀.exists_tensorProduct_algEquiv_of_surjective hsurj
  exact ⟨A, inferInstance, inferInstance, hA.isStandardSmooth, he⟩

/-- **Étale algebras lift along surjections.** Let `R → R₀` be a surjective algebra map and let
`B₀` be an étale `R₀`-algebra. Then there is an étale `R`-algebra `A`, in the universe of `R`,
whose base change to `R₀` is `R₀`-isomorphic to `B₀`. -/
theorem Etale.exists_tensorProduct_algEquiv_of_surjective
    (R : Type u) (R₀ B₀ : Type*) [CommRing R] [CommRing R₀] [Algebra R R₀]
    [CommRing B₀] [Algebra R₀ B₀] [Etale R₀ B₀]
    (hsurj : Function.Surjective (algebraMap R R₀)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Etale R A ∧ Nonempty (R₀ ⊗[R] A ≃ₐ[R₀] B₀) := by
  have : IsStandardSmoothOfRelativeDimension 0 R₀ B₀ :=
    Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›
  obtain ⟨A, _, _, hA, he⟩ :=
    IsStandardSmoothOfRelativeDimension.exists_tensorProduct_algEquiv_of_surjective 0 R R₀ B₀ hsurj
  exact ⟨A, inferInstance, inferInstance,
    Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr hA, he⟩

end Algebra
