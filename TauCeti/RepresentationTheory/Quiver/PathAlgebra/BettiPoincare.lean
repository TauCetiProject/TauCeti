/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Linearity
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix

/-!
# The Betti Poincaré matrix of a finite acyclic path algebra

Let `Q` be a finite quiver whose path algebra `kQ` over a field `k` is finite-dimensional, equipped
with its path-length grading `TauCeti.PathAlgebra.integerGrade k Q`. Each graded vertex simple
`Sⱼ = kQ eⱼ / A₊ eⱼ` has the short exact first-arrow resolution
`0 ⟶ ⨁_{a : j ⟶ l} (kQ eₗ){1} ⟶ kQ eⱼ ⟶ Sⱼ ⟶ 0`
(`TauCeti.PathAlgebra.shortExact_gradedVertexSimpleResolution`). Packaging these short exact
sequences into concrete graded projective resolutions gives the Betti Poincaré matrix of the vertex
simples in the vertex-projective basis `[kQ eᵢ]`:

`B(q, t) = 1 + q t · Aᵀ`,

where `A_{i, j} = #(i ⟶ j)` is the arrow-counting adjacency matrix of `Q` (so `Aᵀ_{i, j}` counts
arrows `j ⟶ i`). Because every entry is supported on `p = n` (`n ∈ {0, 1}`), the diagonal-support
criterion `TauCeti.forall_isLinear_iff_diagonal_bettiPoincareMatrix` shows immediately that the
first-arrow resolutions are linear and hence minimal.

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`: the first-arrow resolution of `Sⱼ`
  as a `GradedProjectiveResolution`.

## Main results

* `TauCeti.PathAlgebra.bettiPoincareMatrix_gradedVertexSimpleProjectiveResolution`: in the basis
  `[kQ eᵢ]`, `bettiPoincareMatrix` equals `1 + (C (T 1) * X) • Aᵀ`.
* `TauCeti.PathAlgebra.isLinear_gradedVertexSimpleProjectiveResolution` and
  `TauCeti.PathAlgebra.isMinimal_gradedVertexSimpleProjectiveResolution`: every first-arrow
  resolution is linear and minimal.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2–3.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *J. Amer. Math. Soc.* **9** (1996), Sections 1.2 and 2.11.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v w

variable (k : Type w) (Q : Type u) [Quiver.{v} Q] [Field k]

section Finite

variable [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- `gradedArrowSum k Q j` is a finitely generated projective graded `kQ`-module. -/
theorem gradedFiniteProjectiveModules_gradedArrowSum (j : Q) :
    let _ := integerGradedAlgebra k Q
    let _ : ∀ a b : Q, Finite (a ⟶ b) :=
      finite_hom_of_module_finite_pathAlgebra k Q inferInstance
    gradedFiniteProjectiveModules (integerGrade k Q) (gradedArrowSum k Q j) := by
  let _ := integerGradedAlgebra k Q
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  exact gradedFiniteProjectiveModules_iff.mpr
    ⟨gradedFiniteModules_iff.mp (gradedFiniteModules_gradedArrowSum k Q j), inferInstance⟩

/-- The first-arrow short complex with transparent `X₁`, `X₂`, and `X₃` projections. -/
abbrev gradedVertexSimpleShortComplex (j : Q) :
    ShortComplex (GradedModuleCat.{max u v w} (integerGrade k Q)) :=
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  ShortComplex.mk (gradedArrowSumToVertexProjective k Q j)
    (gradedVertexProjectiveToSimple k Q j)
    (gradedArrowSumToVertexProjective_comp_gradedVertexProjectiveToSimple k Q j)

/-- `gradedVertexSimpleShortComplex k Q j` is short exact. -/
theorem shortExact_gradedVertexSimpleShortComplex (j : Q) :
    (gradedVertexSimpleShortComplex k Q j).ShortExact := by
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  have heq : gradedVertexSimpleShortComplex k Q j = gradedVertexSimpleResolution k Q j :=
    (gradedVertexSimpleResolution_def k Q j).symm
  exact heq ▸ shortExact_gradedVertexSimpleResolution k Q j

/-- **The first-arrow graded projective resolution of a vertex simple `Sⱼ`.** -/
def gradedVertexSimpleProjectiveResolution (j : Q) :
    let _ := integerGradedAlgebra k Q
    GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q j).grading :=
  let _ := integerGradedAlgebra k Q
  let _ : Module.Projective (pathAlgebra k Q) (gradedArrowSum k Q j) := inferInstance
  GradedProjectiveResolution.ofShortExact (shortExact_gradedVertexSimpleShortComplex k Q j)

instance moduleFinite_gradedVertexSimpleProjectiveResolution (j : Q) (n : ℕ) :
    Module.Finite (pathAlgebra k Q)
      ((gradedVertexSimpleProjectiveResolution k Q j).X n) := by
  let _ := integerGradedAlgebra k Q
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  let _ : Module.Projective (pathAlgebra k Q) (gradedArrowSum k Q j) := inferInstance
  have : Module.Finite (pathAlgebra k Q) (gradedArrowSum k Q j) :=
    gradedFiniteModules_iff.mp (gradedFiniteModules_gradedArrowSum k Q j)
  have : Module.Finite (pathAlgebra k Q) (gradedVertexProjective k Q j) :=
    (gradedFiniteProjectiveModules_iff.mp
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q j)).1
  exact GradedProjectiveResolution.moduleFinite_ofShortExact
    (shortExact_gradedVertexSimpleShortComplex k Q j) n

/-- The Grothendieck class `[⨁_{a : j ⟶ l} (kQ eₗ){1}]` in `K₀^gr(proj kQ)` decomposes as
`∑_{l, a : j ⟶ l} q • [kQ eₗ]`. -/
theorem laurentK0_gradedArrowSum [Fintype Q] (j : Q)
    [∀ l : Q, Fintype (j ⟶ l)] :
    let _ := integerGradedAlgebra k Q
    LaurentK0.of.{max u v w} (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
      ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ =
      ∑ a : (l : Q) × (j ⟶ l),
        (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClassBasis k Q a.1 := by
  classical
  dsimp only
  let _ := integerGradedAlgebra k Q
  let J := (l : Q) × (j ⟶ l)
  let M : J → Type (max u v w) := fun b => ((gradedVertexProjective k Q b.1).shiftObj 1).carrier
  let Q₀ : J → (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory :=
    fun a => ⟨gradedVertexProjective k Q a.1,
      gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1⟩
  let P : J → (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory :=
    fun a => ⟨(Q₀ a).obj.shiftObj 1, gradedFiniteProjectiveModules_shiftObj (Q₀ a).property 1⟩
  let ι : ∀ a : J, (P a).obj ⟶ gradedArrowSum k Q j := fun a =>
    GradedModuleCat.ofHom (DirectSum.lof (pathAlgebra k Q) J M a) <|
      LinearMap.isHomogeneous_def.2 fun p x hx => by
        dsimp only [P, Q₀] at hx
        rw [add_zero, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff]
        intro b
        by_cases hab : a = b
        · subst hab; rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]; exact hx
        · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hab)]
          exact Submodule.zero_mem _
  let π : ∀ a : J, gradedArrowSum k Q j ⟶ (P a).obj := fun a =>
    GradedModuleCat.ofHom (DirectSum.component (pathAlgebra k Q) J M a) <|
      LinearMap.isHomogeneous_def.2 fun p x hx => by
        rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx
        rw [add_zero]; exact hx a
  have hhom_sum : ∀ (S : Finset J) (g : J → (gradedArrowSum k Q j ⟶ gradedArrowSum k Q j)),
      (∑ a ∈ S, g a).hom = ∑ a ∈ S, (g a).hom :=
    fun S g => Finset.induction_on S rfl fun a s ha ih => by
      rw [Finset.sum_insert ha, Finset.sum_insert ha, GradedModuleCat.hom_add, ih]
  rw [laurentK0_projective_of_retract_sum _ P ι π
    (fun a => GradedModuleCat.hom_ext <| LinearMap.ext fun x => by simp [ι, π])
    (fun a b hab => GradedModuleCat.hom_ext <| LinearMap.ext fun x => by
      dsimp only [ι, π]
      rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.hom_ofHom,
        GradedModuleCat.hom_ofHom, DirectSum.component.of]
      simp [hab])
    (GradedModuleCat.hom_ext <| LinearMap.ext fun x => by
      rw [hhom_sum, LinearMap.sum_apply]
      refine (Finset.sum_congr rfl fun d _ => ?_).trans (DirectSum.sum_univ_of x)
      dsimp only [ι, π, M]
      rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.hom_ofHom,
        GradedModuleCat.hom_ofHom, DirectSum.lof_eq_of]
      rfl)]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only [P]
  rw [laurentK0_projective_of_shiftObj (Q₀ a) 1,
    gradedVertexProjectiveClassBasis_apply, gradedVertexProjectiveClass_eq]

/-- The Grothendieck class `[⨁_{a : j ⟶ l} (kQ eₗ){1}]` in `K₀^gr(proj kQ)` has `i`th coordinate
`#(j ⟶ i) · q` in the vertex-projective basis `[kQ eᵢ]`. -/
theorem repr_gradedVertexProjectiveClassBasis_gradedArrowSum (i j : Q) :
    let _ := integerGradedAlgebra k Q
    (gradedVertexProjectiveClassBasis k Q).repr
      (LaurentK0.of.{max u v w} (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩) i =
      (Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1 := by
  classical
  dsimp only
  let _ := integerGradedAlgebra k Q
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  let _ (l : Q) : Fintype (j ⟶ l) := Fintype.ofFinite (j ⟶ l)
  rw [laurentK0_gradedArrowSum k Q j, map_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
  have hterm : ∀ l : Q,
      (∑ _ : (j ⟶ l), ((gradedVertexProjectiveClassBasis k Q).repr
        ((T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClassBasis k Q l)) i) =
        if l = i then (Nat.card (j ⟶ l) : LaurentPolynomial ℤ) * T 1 else 0 := fun l => by
    rw [(gradedVertexProjectiveClassBasis k Q).repr.map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hli : l = i
    · subst hli; simp [Nat.card_eq_fintype_card]
    · simp [hli]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  simp

/-- **Betti Poincaré series of a graded vertex simple `Sⱼ`.** Its `i`th coordinate in `[kQ eᵢ]` is
`(if j = i then 1 else 0) + C (#(j ⟶ i) · q) * X`. -/
theorem bettiPoincareSeries_gradedVertexSimpleProjectiveResolution [DecidableEq Q] (i j : Q) :
    bettiPoincareSeries (gradedVertexProjectiveClassBasis k Q)
      (gradedVertexSimpleProjectiveResolution k Q j) i =
      (if j = i then (1 : PowerSeries (LaurentPolynomial ℤ)) else 0) +
        PowerSeries.C ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) * PowerSeries.X := by
  let _ := integerGradedAlgebra k Q
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  let _ : Module.Projective (pathAlgebra k Q) (gradedArrowSum k Q j) := inferInstance
  have : Module.Finite (pathAlgebra k Q) (gradedArrowSum k Q j) :=
    gradedFiniteModules_iff.mp (gradedFiniteModules_gradedArrowSum k Q j)
  have : Module.Finite (pathAlgebra k Q) (gradedVertexProjective k Q j) :=
    (gradedFiniteProjectiveModules_iff.mp
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q j)).1
  unfold gradedVertexSimpleProjectiveResolution
  rw [GradedProjectiveResolution.bettiPoincareSeries_ofShortExact
      (gradedVertexProjectiveClassBasis k Q)
      (shortExact_gradedVertexSimpleShortComplex k Q j)
      (gradedFiniteProjectiveModules_gradedArrowSum k Q j)
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q j) i,
    repr_gradedVertexProjectiveClassBasis_gradedArrowSum k Q i j]
  have h0 : LaurentK0.of.{max u v w}
      (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
      ⟨gradedVertexProjective k Q j, gradedFiniteProjectiveModules_gradedVertexProjective k Q j⟩ =
      gradedVertexProjectiveClassBasis k Q j := by
    rw [gradedVertexProjectiveClassBasis_apply, gradedVertexProjectiveClass_eq]
  rw [h0, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hji : j = i <;> simp [hji]

/-- **Every first-arrow resolution of a graded vertex simple is linear.** -/
theorem isLinear_gradedVertexSimpleProjectiveResolution (j : Q) :
    let _ := integerGradedAlgebra k Q
    (gradedVertexSimpleProjectiveResolution k Q j).IsLinear := by
  classical
  dsimp only
  let _ := integerGradedAlgebra k Q
  let _ : Fintype Q := Fintype.ofFinite Q
  refine (forall_isLinear_iff_diagonal_bettiPoincareMatrix
    (completeOrthogonalIdempotents_vertexIdempotent k Q) (isHomogeneous_span_vertexIdempotent k Q)
    (fun _ => integerGrade_eq_bot_of_neg k Q)
    (integerGrade_zero_eq_span_range_vertexIdempotent k Q).le vertexIdempotent_ne_zero
    (gradedVertexProjectiveClassBasis k Q)
    (fun i => by
      rw [gradedVertexProjectiveClassBasis_apply, gradedVertexProjectiveClass_eq]
      congr 2; exact gradedVertexProjective_def k Q i)
    (gradedVertexSimpleProjectiveResolution k Q)).mpr (fun i l n p hpn => ?_) j
  rw [bettiPoincareMatrix_apply, bettiPoincareSeries_gradedVertexSimpleProjectiveResolution]
  cases n with
  | zero =>
      by_cases hli : l = i
      · simp only [hli, ↓reduceIte, map_add, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero, add_zero]
        have hp0 : (0 : ℤ) ≠ p := fun h => hpn (by omega)
        rw [← T_zero, T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]; simp [hp0]
      · simp [hli]
  | succ m =>
      have h0 : PowerSeries.coeff (m + 1)
          (if l = i then (1 : PowerSeries (LaurentPolynomial ℤ)) else 0) = 0 := by
        by_cases hli : l = i
        · rw [ite_eq_left hli, PowerSeries.coeff_one]; simp
        · simp [hli]
      rw [map_add, h0, zero_add, PowerSeries.coeff_C_mul]
      cases m with
      | zero =>
          have hp1 : (1 : ℤ) ≠ p := fun hp => hpn (by omega)
          simp only [Nat.zero_add, PowerSeries.coeff_X, ↓reduceIte, mul_one]
          rw [coeff_natCast_mul, T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
          simp [hp1]
      | succ r =>
          rw [PowerSeries.coeff_X]; simp

/-- **Every first-arrow resolution of a graded vertex simple is minimal.** -/
theorem isMinimal_gradedVertexSimpleProjectiveResolution (j : Q) :
    let _ := integerGradedAlgebra k Q
    (gradedVertexSimpleProjectiveResolution k Q j).IsMinimal := by
  let _ := integerGradedAlgebra k Q
  exact (isLinear_gradedVertexSimpleProjectiveResolution k Q j).isMinimal
    (fun _ => integerGrade_eq_bot_of_neg k Q)

/-- **Betti Poincaré matrix of a finite acyclic path algebra**: in the vertex-projective basis,
`B(q, t) = 1 + (q t) Aᵀ`, where `A_{i, j} = #(i ⟶ j)`. -/
theorem bettiPoincareMatrix_gradedVertexSimpleProjectiveResolution [DecidableEq Q] :
    bettiPoincareMatrix (gradedVertexProjectiveClassBasis k Q)
      (gradedVertexSimpleProjectiveResolution k Q) =
      1 + (PowerSeries.C (T 1) * PowerSeries.X : PowerSeries (LaurentPolynomial ℤ)) •
        (Matrix.of fun i j : Q =>
          (Nat.card (i ⟶ j) : PowerSeries (LaurentPolynomial ℤ)))ᵀ := by
  refine Matrix.ext fun i j => ?_
  rw [bettiPoincareMatrix_apply, bettiPoincareSeries_gradedVertexSimpleProjectiveResolution,
    Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
    smul_eq_mul]
  let CMap : LaurentPolynomial ℤ →+* PowerSeries (LaurentPolynomial ℤ) := PowerSeries.C
  have hcast : (Nat.card (j ⟶ i) : PowerSeries (LaurentPolynomial ℤ)) =
      CMap (Nat.card (j ⟶ i) : LaurentPolynomial ℤ) := (map_natCast CMap _).symm
  rw [hcast]
  dsimp only [CMap]
  rw [map_mul]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte]
    ring

end Finite

end TauCeti.PathAlgebra
