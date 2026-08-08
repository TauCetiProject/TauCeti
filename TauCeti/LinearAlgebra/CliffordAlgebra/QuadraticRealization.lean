/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalAction
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The quadratic realization of a skew-adjoint Lie algebra

For a nondegenerate quadratic form on a finite-dimensional vector space, quadratic Clifford
elements are exactly the skew-adjoint endomorphisms of its polar form. This module constructs the
inverse to `quadraticLieAction` and packages the resulting Lie equivalence.

The basis used in the surjectivity proof is not part of the public construction. The equivalence is
pinned instead by its action on the Clifford generators.

## Main results

* `TauCeti.CliffordAlgebra.soEquivQuadratic`: the quadratic realization Lie equivalence.
* `TauCeti.CliffordAlgebra.soEquivQuadratic_lie_ι`: its defining generator-action equation.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, "The abstract quadratic realization".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

private noncomputable instance : DecidableEq (Module.Basis.ofVectorSpaceIndex K V) :=
  Classical.decEq _

private noncomputable def bivectorLeftLinear (Q : QuadraticForm K V) (b : V) :
    V →ₗ[K] CliffordAlgebra Q :=
  (cliffordBivectorAlternating Q).toMultilinearMap.toLinearMap ![0, b] 0

omit [FiniteDimensional K V] in
private theorem bivectorLeftLinear_apply (Q : QuadraticForm K V) (a b : V) :
    bivectorLeftLinear Q b a = cliffordBivector Q a b := by
  -- Expose the vector updated by the first-variable partial map.
  change cliffordBivectorAlternating Q (Function.update ![0, b] 0 a) = _
  rw [show Function.update ![0, b] 0 a = ![a, b] by
    ext i
    fin_cases i <;> simp]
  exact cliffordBivectorAlternating_apply Q a b

private noncomputable def bivectorRightLinear (Q : QuadraticForm K V) (a : V) :
    V →ₗ[K] CliffordAlgebra Q :=
  (cliffordBivectorAlternating Q).toMultilinearMap.toLinearMap ![a, 0] 1

omit [FiniteDimensional K V] in
private theorem bivectorRightLinear_apply (Q : QuadraticForm K V) (a b : V) :
    bivectorRightLinear Q a b = cliffordBivector Q a b := by
  -- Expose the vector updated by the second-variable partial map.
  change cliffordBivectorAlternating Q (Function.update ![a, 0] 1 b) = _
  rw [show Function.update ![a, 0] 1 b = ![a, b] by
    ext i
    fin_cases i <;> simp]
  exact cliffordBivectorAlternating_apply Q a b

omit [FiniteDimensional K V] in
private theorem bivector_sum_right (Q : QuadraticForm K V)
    {ι : Type*} [Fintype ι] (c : ι → K) (a : V) (b : ι → V) :
    (∑ i, c i • cliffordBivector Q a (b i)) =
      cliffordBivector Q a (∑ i, c i • b i) := by
  simp_rw [← bivectorRightLinear_apply Q]
  rw [map_sum]
  simp_rw [map_smul]

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private theorem bilin_apply_dualBasis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    {ι : Type*} [DecidableEq ι] [Finite ι] (b : Module.Basis ι K V) (i : ι) (x : V) :
    B (LinearMap.BilinForm.dualBasis B hB b i) x = b.repr x i := by
  let _ := b.finiteDimensional_of_finite
  simp [LinearMap.BilinForm.dualBasis]

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private theorem sum_dualBasis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hBsymm : B.IsSymm) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K V) (x : V) :
    ∑ i, B (b i) x • LinearMap.BilinForm.dualBasis B hB b i = x := by
  let d := LinearMap.BilinForm.dualBasis B hB b
  simpa only [d, LinearMap.BilinForm.dualBasis_repr_apply, ← hBsymm.eq] using d.sum_repr x

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private theorem sum_basis_dual (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hBsymm : B.IsSymm) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K V) (x : V) :
    ∑ i, B x (LinearMap.BilinForm.dualBasis B hB b i) • b i = x := by
  calc
    _ = ∑ i, b.repr x i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hBsymm.eq, bilin_apply_dualBasis]
    _ = x := b.sum_repr x

private noncomputable def quadraticLieActionLiftSummand (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (i : Module.Basis.ofVectorSpaceIndex K V) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) →ₗ[K] quadraticLieSubalgebra Q := by
  classical
  exact ((bivectorLeftLinear Q (Module.Basis.ofVectorSpace K V i)).comp
      ((LinearMap.applyₗ (R := K) (M₂ := V)
        (LinearMap.BilinForm.dualBasis (QuadraticMap.polarBilin Q)
          (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
          (Module.Basis.ofVectorSpace K V) i)).comp
        (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)).toSubmodule.subtype)).codRestrict
    (quadraticLieSubalgebra Q) (by
      intro f
      simp only [LinearMap.comp_apply]
      rw [bivectorLeftLinear_apply]
      exact cliffordBivector_mem_quadraticLieSubalgebra Q _ _)

private noncomputable def quadraticLieActionLift (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) →ₗ[K] quadraticLieSubalgebra Q := by
  classical
  exact ∑ i, ⅟(2 : K) • quadraticLieActionLiftSummand Q hQ i

private theorem quadraticLieActionLift_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    quadraticLieActionLift Q hQ f = ∑ i, ⅟(2 : K) •
      (⟨cliffordBivector Q
          ((f : Module.End K V) (LinearMap.BilinForm.dualBasis (QuadraticMap.polarBilin Q)
            (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
            (Module.Basis.ofVectorSpace K V) i))
          (Module.Basis.ofVectorSpace K V i),
        cliffordBivector_mem_quadraticLieSubalgebra Q _ _⟩ : quadraticLieSubalgebra Q) := by
  classical
  apply Submodule.subtype_injective (quadraticLieSubalgebra Q).toSubmodule
  simp [quadraticLieActionLift, quadraticLieActionLiftSummand, bivectorLeftLinear_apply]
  rfl

private theorem quadraticLieAction_quadraticLieActionLift
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    quadraticLieAction Q (quadraticLieActionLift Q hQ f) = f := by
  classical
  rw [quadraticLieActionLift_apply]
  rw [map_sum]
  simp_rw [map_smul]
  apply Submodule.subtype_injective
    (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)).toSubmodule
  simp only [map_sum, map_smul, Submodule.subtype_apply]
  apply LinearMap.ext
  intro m
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  -- Expose the underlying endomorphism action before using the bivector action equation.
  change (∑ i : Module.Basis.ofVectorSpaceIndex K V,
    ⅟(2 : K) •
      (((quadraticLieAction Q
        ⟨cliffordBivector Q
            ((f : Module.End K V) (LinearMap.BilinForm.dualBasis
              (QuadraticMap.polarBilin Q) (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
              (Module.Basis.ofVectorSpace K V) i))
            (Module.Basis.ofVectorSpace K V i),
          cliffordBivector_mem_quadraticLieSubalgebra Q _ _⟩ :
          skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End K V) m)) =
    (f : Module.End K V) m
  simp_rw [quadraticLieAction_cliffordBivector_apply]
  let B := QuadraticMap.polarBilin Q
  let b := Module.Basis.ofVectorSpace K V
  let d := LinearMap.BilinForm.dualBasis B
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) b
  -- Rewrite the indexed construction using the local names for the polar form and dual basis.
  change (∑ i, ⅟(2 : K) •
    (B (b i) m • (f : Module.End K V) (d i) - B ((f : Module.End K V) (d i)) m • b i)) =
    (f : Module.End K V) m
  have hsum₁ : ∑ i, B (b i) m • (f : Module.End K V) (d i) = (f : Module.End K V) m := by
    have hvec : ∑ i, B (b i) m • d i = m :=
      sum_dualBasis B (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
        ⟨fun x y => QuadraticMap.polar_comm Q x y⟩ b m
    calc
      _ = (f : Module.End K V) (∑ i, B (b i) m • d i) := by
        rw [map_sum]
        simp
      _ = (f : Module.End K V) m := congrArg (f : Module.End K V) hvec
  have hskew := (LinearMap.mem_skewAdjointSubmodule ((f : Module.End K V))).mp f.property
  have hsum₂ : ∑ i, B ((f : Module.End K V) (d i)) m • b i = -(f : Module.End K V) m := by
    calc
      _ = ∑ i, -(b.repr ((f : Module.End K V) m) i • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hskew]
        simp only [Pi.neg_apply]
        rw [map_neg, bilin_apply_dualBasis, neg_smul]
      _ = -(∑ i, b.repr ((f : Module.End K V) m) i • b i) := by
        rw [Finset.sum_neg_distrib]
      _ = -(f : Module.End K V) m := by rw [b.sum_repr]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, hsum₁, hsum₂, sub_neg_eq_add]
  rw [← two_smul K, smul_smul, invOf_mul_self, one_smul]

private theorem quadraticLieActionLift_quadraticLieAction_cliffordBivector
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a b : V) :
    quadraticLieActionLift Q hQ
      (quadraticLieAction Q
        ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩) =
      ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩ := by
  classical
  rw [quadraticLieActionLift_apply]
  apply Submodule.subtype_injective (quadraticLieSubalgebra Q).toSubmodule
  -- Expose the ambient Clifford values of the summed quadratic elements.
  change ↑(∑ i : Module.Basis.ofVectorSpaceIndex K V, ⅟(2 : K) •
    (⟨cliffordBivector Q
        ((((quadraticLieAction Q
          ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩) :
          skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End K V)
          (LinearMap.BilinForm.dualBasis (QuadraticMap.polarBilin Q)
            (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (Module.Basis.ofVectorSpace K V) i))
        (Module.Basis.ofVectorSpace K V i),
      cliffordBivector_mem_quadraticLieSubalgebra Q _ _⟩ : quadraticLieSubalgebra Q)) =
    cliffordBivector Q a b
  simp_rw [quadraticLieAction_cliffordBivector_apply]
  -- Reduce equality in the quadratic subalgebra to equality of ambient Clifford values.
  change (quadraticLieSubalgebra Q).toSubmodule.subtype _ = _
  rw [map_sum]
  simp_rw [map_smul, Submodule.subtype_apply]
  let B := QuadraticMap.polarBilin Q
  let basis := Module.Basis.ofVectorSpace K V
  let dualBasis := LinearMap.BilinForm.dualBasis B
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) basis
  -- Rewrite the indexed construction using the local polar form and dual basis.
  change (∑ i, ⅟(2 : K) • cliffordBivector Q
    (B b (dualBasis i) • a - B a (dualBasis i) • b) (basis i)) =
    cliffordBivector Q a b
  have hsum (x : V) : ∑ i, B x (dualBasis i) • basis i = x :=
    sum_basis_dual B (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
      ⟨fun x y => QuadraticMap.polar_comm Q x y⟩ basis x
  -- Expose linearity in the first bivector argument through the bundled partial map.
  simp_rw [← bivectorLeftLinear_apply Q]
  simp_rw [map_sub, map_smul, bivectorLeftLinear_apply, smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib]
  have hsumBivector (x y : V) :
      (∑ i, (⅟(2 : K) * B x (dualBasis i)) • cliffordBivector Q y (basis i)) =
        ⅟(2 : K) • cliffordBivector Q y x := by
    calc
      _ = ⅟(2 : K) • ∑ i, B x (dualBasis i) • cliffordBivector Q y (basis i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
      _ = ⅟(2 : K) • cliffordBivector Q y (∑ i, B x (dualBasis i) • basis i) := by
        rw [bivector_sum_right]
      _ = ⅟(2 : K) • cliffordBivector Q y x := by rw [hsum]
  rw [hsumBivector b a, hsumBivector a b, cliffordBivector_swap Q a b, smul_neg,
    sub_neg_eq_add, ← two_smul K, smul_smul, mul_invOf_self, one_smul]

private theorem quadraticLieActionLift_quadraticLieAction
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (x : quadraticLieSubalgebra Q) :
    quadraticLieActionLift Q hQ (quadraticLieAction Q x) = x := by
  let F : quadraticLieSubalgebra Q →ₗ[K] quadraticLieSubalgebra Q :=
    (quadraticLieActionLift Q hQ).comp (quadraticLieAction Q).toLinearMap - LinearMap.id
  let P : Submodule K (CliffordAlgebra Q) := F.ker.map (quadraticLieSubalgebra Q).subtype
  have hP : (quadraticLieSubalgebra Q).toSubmodule ≤ P :=
    quadraticLieSubalgebra_toSubmodule_le_of_cliffordBivector_mem Q fun a b => by
      refine ⟨⟨cliffordBivector Q a b,
        cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩, ?_, rfl⟩
      -- Expose membership in the kernel of the difference of the two linear maps.
      change quadraticLieActionLift Q hQ
        (quadraticLieAction Q
          ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩) -
        ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩ = 0
      rw [quadraticLieActionLift_quadraticLieAction_cliffordBivector, sub_self]
  obtain ⟨y, hy, hxy⟩ := hP x.property
  have hyx : y = x := Subtype.ext hxy
  subst y
  exact sub_eq_zero.mp hy

/-- The skew-adjoint endomorphisms of a nondegenerate finite-dimensional quadratic module are
the quadratic elements of its Clifford algebra. -/
noncomputable def soEquivQuadratic (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  (LieEquiv.ofBijective (quadraticLieAction Q) ⟨
    Function.LeftInverse.injective (quadraticLieActionLift_quadraticLieAction Q hQ),
    Function.RightInverse.surjective (quadraticLieAction_quadraticLieActionLift Q hQ)⟩).symm

/-- The inverse quadratic realization is the canonical action. -/
@[simp]
theorem soEquivQuadratic_symm_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : quadraticLieSubalgebra Q) :
    (soEquivQuadratic Q hQ).symm x = quadraticLieAction Q x := by
  rfl

/-- The quadratic element realizing a skew-adjoint endomorphism acts by that endomorphism on the
Clifford generators. -/
theorem soEquivQuadratic_lie_ι (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : V) :
    ⁅(soEquivQuadratic Q hQ f : CliffordAlgebra Q), ι Q x⁆ =
      ι Q ((f : Module.End K V) x) := by
  rw [← ι_quadraticLieAction_apply Q (soEquivQuadratic Q hQ f) x,
    ← soEquivQuadratic_symm_apply Q hQ, LieEquiv.symm_apply_apply]

end TauCeti.CliffordAlgebra
