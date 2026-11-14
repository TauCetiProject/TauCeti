/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Connected
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix

/-!
# The Betti Poincaré matrix of the graded vertex simples of a path algebra

Let `kQ` carry its integer-extended path-length grading. For a vertex `i` with finitely many
outgoing arrows, the short exact first-arrow sequence
`0 ⟶ ⨁_{a : i ⟶ j} (kQ eⱼ){1} ⟶ kQ eᵢ ⟶ Sᵢ ⟶ 0` from
`TauCeti.PathAlgebra.gradedVertexSimpleResolution` packages via
`TauCeti.GradedProjectiveResolution.ofShortExact` into a concrete two-term graded projective
resolution of the graded vertex simple `Sᵢ`. Because `kQ eᵢ` is generated in degree zero by `eᵢ`
and each summand `(kQ eⱼ){1}` is generated in degree one by `eⱼ`, this resolution is linear and
therefore minimal.

When `k` is a field and `kQ` is finite-dimensional (equivalently, `Q` is finite and acyclic),
expanding `[kQ eⱼ]` and `[⨁_{a : j ⟶ l} (kQ eₗ){1}]` in
`TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis` computes the matrix-valued Betti Poincaré
series of the graded vertex simples:

```text
B(q, t) = I + q t Aᵀ,
```

where the `(i, j)` entry of `Aᵀ` is `Nat.card (j ⟶ i)`, the number of arrows from `j` to `i`. Every
nonzero graded Betti number lies on the Koszul diagonal `d = n` (`(0, 0)` and `(1, 1)`).

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`: the two-term first-arrow graded
  projective resolution of `Sᵢ`.

## Main results

* `TauCeti.PathAlgebra.isLinear_gradedVertexSimpleProjectiveResolution` and
  `TauCeti.PathAlgebra.isMinimal_gradedVertexSimpleProjectiveResolution`: the first-arrow
  resolution is linear and minimal.
* `TauCeti.PathAlgebra.bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution`: the
  `(i, j)` Betti Poincaré power series is `δ_{i,j} + |j ⟶ i| q t`.
* `TauCeti.PathAlgebra.bettiPoincarePowerSeriesMatrix_gradedVertexSimple`: matrix form
  `1 + (q t) • Aᵀ` in the vertex-projective basis.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the projective resolution of a vertex simple.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 2.11, for linear resolutions of path-algebra simples.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped _root_.DirectSum

universe u v w

section Resolution

variable (k : Type w) (Q : Type u) [Quiver.{v} Q] [CommRing k] [Finite Q]

instance moduleFinite_gradedVertexProjective (i : Q) :
    Module.Finite (pathAlgebra k Q) (gradedVertexProjective k Q i) :=
  (gradedFiniteProjectiveModules_iff.1
    (gradedFiniteProjectiveModules_gradedVertexProjective k Q i)).1

/-- The direct sum `⨁_{a : i ⟶ j} (kQ eⱼ){1}` of shifted vertex projectives is a finite graded
projective module. -/
theorem gradedFiniteProjectiveModules_gradedArrowSum (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    gradedFiniteProjectiveModules (integerGrade k Q) (gradedArrowSum k Q i) :=
  let _ := integerGradedAlgebra k Q
  gradedFiniteProjectiveModules_directSumObj.{w, max u v w, max u v}
    fun a : (j : Q) × (i ⟶ j) ↦
      ⟨(gradedVertexProjective k Q a.1).shiftObj 1,
        gradedFiniteProjectiveModules_shiftObj
          (gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1) 1⟩

instance moduleFinite_gradedArrowSum (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    Module.Finite (pathAlgebra k Q) (gradedArrowSum k Q i) :=
  (gradedFiniteProjectiveModules_iff.1 (gradedFiniteProjectiveModules_gradedArrowSum k Q i)).1

instance moduleProjective_gradedArrowSum (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    Module.Projective (pathAlgebra k Q) (gradedArrowSum k Q i) :=
  (gradedFiniteProjectiveModules_iff.1 (gradedFiniteProjectiveModules_gradedArrowSum k Q i)).2

private theorem shortExact_firstArrowMk (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    (ShortComplex.mk (gradedArrowSumToVertexProjective k Q i)
      (gradedVertexProjectiveToSimple k Q i)
      (gradedArrowSumToVertexProjective_comp_gradedVertexProjectiveToSimple k Q i)).ShortExact :=
  gradedVertexSimpleResolution_def k Q i ▸ shortExact_gradedVertexSimpleResolution k Q i

/-- **The first-arrow graded projective resolution**
`0 ⟶ ⨁_{a : i ⟶ j} (kQ eⱼ){1} ⟶ kQ eᵢ ⟶ Sᵢ ⟶ 0` of the graded vertex simple `Sᵢ`, packaged as a
`TauCeti.GradedProjectiveResolution`. -/
def gradedVertexSimpleProjectiveResolution (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    GradedProjectiveResolution.{w, max u v w, max u v w, max u v w} (integerGrade k Q)
      (gradedVertexSimple k Q i).grading :=
  GradedProjectiveResolution.ofShortExact (shortExact_firstArrowMk k Q i)

instance moduleFinite_gradedVertexSimpleProjectiveResolution_X (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] (n : ℕ) :
    Module.Finite (pathAlgebra k Q) ((gradedVertexSimpleProjectiveResolution k Q i).X n) := by
  unfold gradedVertexSimpleProjectiveResolution
  exact inferInstance

/-- The graded vertex projective `kQ eᵢ` is generated in degree zero by the vertex idempotent
`eᵢ`. -/
theorem isGeneratedInDegree_zero_gradedVertexProjective (i : Q) :
    (gradedVertexProjective k Q i).grading.IsGeneratedInDegree (pathAlgebra k Q) 0 := by
  refine ((gradedVertexProjective k Q i).grading.isGeneratedInDegree_iff 0).2 fun x ↦ ?_
  let gen : gradedVertexProjective k Q i :=
    (gradedVertexProjectiveEquiv k Q i).symm ⟨vertexIdempotent k i, Ideal.subset_span rfl⟩
  have hgen : gen ∈ (gradedVertexProjective k Q i).grading.piece 0 := by
    rw [mem_gradedVertexProjective_piece_iff, ← coe_gradedVertexProjectiveEquiv_apply]
    simpa [gen] using vertexIdempotent_mem_integerGrade_zero k Q i
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (gradedVertexProjectiveEquiv k Q i x).2
  have hx : x = r • gen := by
    refine gradedVertexProjectiveSubtype_injective k Q i ?_
    rw [map_smul, ← coe_gradedVertexProjectiveEquiv_apply, ← coe_gradedVertexProjectiveEquiv_apply]
    simpa [gen, smul_eq_mul] using hr.symm
  rw [hx]
  exact Submodule.smul_mem _ r (Submodule.subset_span (SetLike.mem_coe.2 hgen))

/-- **The first-arrow graded projective resolution of `Sᵢ` is linear**: `kQ eᵢ` is generated in
degree `0` and `⨁_{a : i ⟶ j} (kQ eⱼ){1}` is generated in degree `1`. -/
theorem isLinear_gradedVertexSimpleProjectiveResolution (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).IsLinear := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite ((j : Q) × (i ⟶ j))
  unfold gradedVertexSimpleProjectiveResolution
  rw [GradedProjectiveResolution.isLinear_ofShortExact_iff]
  refine ⟨isGeneratedInDegree_zero_gradedVertexProjective k Q i, ?_⟩
  change (gradedArrowSum k Q i).grading.IsGeneratedInDegree (pathAlgebra k Q) 1
  refine ((gradedArrowSum k Q i).grading.isGeneratedInDegree_iff 1).2 fun y ↦ ?_
  classical
  rw [← DirectSum.sum_univ_of y]
  refine Submodule.sum_mem _ fun a _ ↦ ?_
  let gen : (gradedVertexProjective k Q a.1).shiftObj 1 :=
    (gradedVertexProjectiveEquiv k Q a.1).symm ⟨vertexIdempotent k a.1, Ideal.subset_span rfl⟩
  have hgen : DirectSum.lof (pathAlgebra k Q) ((j : Q) × (i ⟶ j))
      (fun b ↦ (gradedVertexProjective k Q b.1).shiftObj 1) a gen ∈
      (gradedArrowSum k Q i).grading.piece 1 := by
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff]
    intro b
    rw [DirectSum.lof_eq_of]
    by_cases hab : a = b
    · subst hab
      rw [DirectSum.of_eq_same, GradedModuleCat.mem_shiftObj_piece_iff, sub_self,
        mem_gradedVertexProjective_piece_iff, ← coe_gradedVertexProjectiveEquiv_apply]
      simpa [gen] using vertexIdempotent_mem_integerGrade_zero k Q a.1
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hab)]
      exact zero_mem _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (gradedVertexProjectiveEquiv k Q a.1 (y a)).2
  have hya : y a = r • gen := by
    refine gradedVertexProjectiveSubtype_injective k Q a.1 ?_
    rw [map_smul, ← coe_gradedVertexProjectiveEquiv_apply, ← coe_gradedVertexProjectiveEquiv_apply]
    simpa [gen, smul_eq_mul] using hr.symm
  rw [← DirectSum.lof_eq_of (pathAlgebra k Q), hya, map_smul]
  exact Submodule.smul_mem _ r (Submodule.subset_span (SetLike.mem_coe.2 hgen))

/-- **The first-arrow graded projective resolution of `Sᵢ` is minimal.** -/
theorem isMinimal_gradedVertexSimpleProjectiveResolution (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).IsMinimal := by
  let _ := integerGradedAlgebra k Q
  exact (isLinear_gradedVertexSimpleProjectiveResolution k Q i).isMinimal
    (fun _ ↦ integerGrade_eq_bot_of_neg k Q)

/-- In `K₀^gr(proj kQ)`, the arrow kernel `⨁_{a : j ⟶ l} (kQ eₗ){1}` has class
`∑_{a : j ⟶ l} q [kQ eₗ]`. -/
theorem laurentK0_projective_gradedArrowSum (j : Q) [Fintype ((l : Q) × (j ⟶ l))] :
    LaurentK0.of.{max u v w} (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ =
      ∑ a : (l : Q) × (j ⟶ l),
        (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClass k Q a.1 := by
  let _ := integerGradedAlgebra k Q
  have h := laurentK0_projective_of_directSumObj.{w, max u v w, max u v}
    (𝒜 := integerGrade k Q) fun a : (l : Q) × (j ⟶ l) ↦
      ⟨(gradedVertexProjective k Q a.1).shiftObj 1,
        gradedFiniteProjectiveModules_shiftObj
          (gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1) 1⟩
  refine h.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
  rw [laurentK0_projective_of_shiftObj
    ⟨gradedVertexProjective k Q a.1,
      gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1⟩ 1,
    gradedVertexProjectiveClass_eq]

end Resolution

/-! ### Expansion in the vertex-projective basis -/

section FiniteDimensional

variable (k : Type w) (Q : Type u) [Quiver.{v} Q] [Field k] [Finite Q]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- The `i`th coordinate of `[⨁_{a : j ⟶ l} (kQ eₗ){1}]` in `gradedVertexProjectiveClassBasis` is
`|j ⟶ i| q`. -/
@[simp]
theorem gradedVertexProjectiveClassBasis_repr_gradedArrowSum (i j : Q)
    [Finite ((l : Q) × (j ⟶ l))] :
    (gradedVertexProjectiveClassBasis k Q).repr
        (LaurentK0.of.{max u v w} (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
          ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩) i =
      (Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1 := by
  classical
  let _ := Fintype.ofFinite Q
  let (a b : Q) : Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance a b
  let (a b : Q) : Fintype (a ⟶ b) := Fintype.ofFinite (a ⟶ b)
  rw [laurentK0_projective_gradedArrowSum k Q j, map_sum, Finsupp.finsetSum_apply]
  simp_rw [LinearEquiv.map_smul, Finsupp.smul_apply, ← gradedVertexProjectiveClassBasis_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
  · intro l _ hli
    simp only [hli, ↓reduceIte, Finset.sum_const_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Betti Poincaré series of a graded vertex simple.** In the vertex-projective basis, the `i`th
coordinate of the Betti Poincaré series of `Sⱼ` is `δ_{j,i} + |j ⟶ i| q t`. -/
theorem bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution [DecidableEq Q]
    (i j : Q) [Finite ((l : Q) × (j ⟶ l))] :
    (gradedVertexSimpleProjectiveResolution k Q j).bettiPoincarePowerSeries
        (gradedVertexProjectiveClassBasis k Q) i =
      (if i = j then 1 else 0) +
        PowerSeries.C ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) * PowerSeries.X := by
  unfold gradedVertexSimpleProjectiveResolution
  rw [GradedProjectiveResolution.bettiPoincarePowerSeries_ofShortExact]
  have hX₂ : (⟨gradedVertexProjective k Q j,
      gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :
        (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory) =
      ⟨gradedVertexProjective k Q j, gradedFiniteProjectiveModules_gradedVertexProjective k Q j⟩ :=
    rfl
  have hX₁ : (⟨gradedArrowSum k Q j,
      gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :
        (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory) =
      ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ :=
    rfl
  rw [hX₂, hX₁, ← gradedVertexProjectiveClass_eq, ← gradedVertexProjectiveClassBasis_apply,
    Module.Basis.repr_self, Finsupp.single_apply,
    gradedVertexProjectiveClassBasis_repr_gradedArrowSum]
  rcases eq_or_ne i j with rfl | hij
  · simp only [↓reduceIte, map_one]
  · simp only [hij, hij.symm, ↓reduceIte, map_zero]

/-- **The Betti Poincaré matrix of the graded vertex simples of a finite acyclic quiver** is
`1 + (q t) • Aᵀ`, where the `(i, j)` entry counts arrows `j ⟶ i`. -/
theorem bettiPoincarePowerSeriesMatrix_gradedVertexSimple [DecidableEq Q]
    [∀ a b : Q, Finite (a ⟶ b)] :
    bettiPoincarePowerSeriesMatrix (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimple k Q) (fun j ↦ gradedVertexSimpleProjectiveResolution k Q j) =
      1 + Matrix.of fun i j : Q ↦
        PowerSeries.C ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) * PowerSeries.X := by
  refine Matrix.ext fun i j ↦ ?_
  rw [bettiPoincarePowerSeriesMatrix_apply,
    bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution, Matrix.add_apply,
    Matrix.one_apply, Matrix.of_apply]

end FiniteDimensional

end TauCeti.PathAlgebra
