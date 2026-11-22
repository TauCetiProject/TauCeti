/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix

/-!
# Linear resolutions and Betti Poincaré matrix of a path algebra

For a quiver `Q` with finitely many vertices and a vertex `i` with finitely many outgoing arrows,
the graded first-arrow short exact sequence

```text
0 ⟶ ⨁_{a : i ⟶ j} (kQ eⱼ){1} ⟶ kQ eᵢ ⟶ Sᵢ ⟶ 0
```

packages into a length-one `TauCeti.GradedProjectiveResolution` of the graded vertex simple `Sᵢ`.
Its degree-zero term `kQ eᵢ` is generated in internal degree `0`, its degree-one term
`⨁_{a : i ⟶ j} (kQ eⱼ){1}` is generated in internal degree `1`, and all higher terms vanish.
Hence the resolution is linear (and in particular minimal).

For a finite acyclic quiver over a field `k`, the Betti Poincaré matrix of these minimal
resolutions in the graded vertex-projective basis `[kQ eᵢ]` is `B(q, t) = I + q t Aᵀ`, where the
`(i, j)` entry of `A` counts arrows `i ⟶ j`. Setting `t = -1` recovers `I - q Aᵀ`, the inverse of
the graded Cartan matrix `C(q) = (I - q Aᵀ)⁻¹`.

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`: the length-one graded projective
  resolution of the graded vertex simple `Sᵢ`.

## Main results

* `TauCeti.PathAlgebra.isGeneratedInDegree_zero_gradedVertexProjective`: `kQ eᵢ` is generated in
  internal degree `0`.
* `TauCeti.PathAlgebra.gradedFiniteProjectiveModules_gradedArrowSum`: the arrow kernel
  `⨁_{a : i ⟶ j} (kQ eⱼ){1}` is a finite graded projective `kQ`-module.
* `TauCeti.PathAlgebra.isLinear_gradedVertexSimpleProjectiveResolution` and
  `TauCeti.PathAlgebra.isMinimal_gradedVertexSimpleProjectiveResolution`: the first-arrow resolution
  of `Sᵢ` is linear and minimal.
* `TauCeti.PathAlgebra.laurentK0_gradedArrowSum_eq_sum`: the class of `⨁_{a : j ⟶ i} (kQ eᵢ){1}`
  in `K₀^gr(proj kQ)` is `∑ i, |j ⟶ i| q [kQ eᵢ]`.
* `TauCeti.PathAlgebra.bettiPoincareMatrix_gradedVertexSimple`: the Betti Poincaré matrix of any
  minimal resolutions of the graded vertex simples of a finite acyclic path algebra is
  `I + q t Aᵀ`.
* `TauCeti.PathAlgebra.eval_neg_one_trunc_two_bettiPoincareMatrix`: evaluating the truncated Betti
  Poincaré matrix at `t = -1` gives `1 - q Aᵀ`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the first-arrow resolution of vertex simples.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Section 1.2, for linear resolutions and Koszulity of path
  algebras.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Limits LaurentPolynomial
open scoped Matrix

universe u v w

variable {k : Type w} {Q : Type u} [Quiver.{v} Q]

section Resolution

variable (k Q) [CommRing k] [Finite Q]

/-- The graded vertex projective `kQ eᵢ` is generated as a `kQ`-module in internal degree `0`. -/
theorem isGeneratedInDegree_zero_gradedVertexProjective (i : Q) :
    (gradedVertexProjective k Q i).grading.IsGeneratedInDegree (pathAlgebra k Q) 0 := by
  let _ := integerGradedAlgebra k Q
  rw [InternalGrading.isGeneratedInDegree_iff]
  intro x
  let e' : gradedVertexProjective k Q i :=
    (gradedVertexProjectiveEquiv k Q i).symm
      ⟨vertexIdempotent k i, Ideal.subset_span rfl⟩
  have he' : e' ∈ (gradedVertexProjective k Q i).grading.piece 0 := by
    rw [mem_gradedVertexProjective_piece_iff, ← coe_gradedVertexProjectiveEquiv_apply]
    simpa [e'] using vertexIdempotent_mem_integerGrade_zero k Q i
  have hx : gradedVertexProjectiveSubtype k Q i x • e' = x := by
    apply gradedVertexProjectiveSubtype_injective k Q i
    rw [map_smul, smul_eq_mul, ← coe_gradedVertexProjectiveEquiv_apply,
      ← coe_gradedVertexProjectiveEquiv_apply]
    simp only [e', LinearEquiv.apply_symm_apply]
    exact (mem_span_singleton_iff_mul_eq_self (vertexIdempotent_mul_self i)).mp
      (gradedVertexProjectiveEquiv k Q i x).2
  rw [← hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span he')

/-- The arrow kernel `⨁_{a : i ⟶ j} (kQ eⱼ){1}` is generated as a `kQ`-module in internal
degree `1`. -/
theorem isGeneratedInDegree_one_gradedArrowSum (i : Q) :
    (gradedArrowSum k Q i).grading.IsGeneratedInDegree (pathAlgebra k Q) 1 := by
  rw [InternalGrading.isGeneratedInDegree_directSum_iff]
  intro a
  dsimp only [GradedModuleCat.shiftObj]
  rw [InternalGrading.isGeneratedInDegree_shift_iff, add_neg_cancel]
  exact isGeneratedInDegree_zero_gradedVertexProjective k Q a.1

/-- The arrow kernel `⨁_{a : i ⟶ j} (kQ eⱼ){1}` is a finite graded projective `kQ`-module. -/
theorem gradedFiniteProjectiveModules_gradedArrowSum (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    gradedFiniteProjectiveModules (integerGrade k Q) (gradedArrowSum k Q i) := by
  refine gradedFiniteProjectiveModules_iff.mpr
    ⟨gradedFiniteModules_iff.mp (gradedFiniteModules_gradedArrowSum k Q i), ?_⟩
  let _ : ∀ a : (j : Q) × (i ⟶ j),
      Module.Projective (pathAlgebra k Q) ((gradedVertexProjective k Q a.1).shiftObj 1) :=
    fun a => moduleProjective_gradedVertexProjective k Q a.1
  infer_instance

private abbrev resolutionTerm (i : Q) : ℕ → GradedModuleCat.{max u v w} (integerGrade k Q)
  | 0 => gradedVertexProjective k Q i
  | 1 => gradedArrowSum k Q i
  | _ + 2 => GradedModuleCat.zeroObj

/-- **The length-one graded projective resolution of a graded vertex simple `Sᵢ`**:
`⋯ ⟶ 0 ⟶ ⨁_{a : i ⟶ j} (kQ eⱼ){1} ⟶ kQ eᵢ ⟶ Sᵢ ⟶ 0`. -/
def gradedVertexSimpleProjectiveResolution (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q i).grading where
  X n := resolutionTerm k Q i n
  grading n := (resolutionTerm k Q i n).grading
  projective
    | 0 => moduleProjective_gradedVertexProjective k Q i
    | 1 => (gradedFiniteProjectiveModules_iff.mp
        (gradedFiniteProjectiveModules_gradedArrowSum k Q i)).2
    | _ + 2 => inferInstance
  d
    | 0 => (gradedArrowSumToVertexProjective k Q i).hom
    | 1 => 0
    | _ + 2 => 0
  «π» := (gradedVertexProjectiveToSimple k Q i).hom
  isHomogeneous_d
    | 0 => (gradedArrowSumToVertexProjective k Q i).isHomogeneous
    | 1 => LinearMap.isHomogeneous_zero _ _ _
    | _ + 2 => LinearMap.isHomogeneous_zero _ _ _
  isHomogeneous_π := (gradedVertexProjectiveToSimple k Q i).isHomogeneous
  surjective_π := (GradedModuleCat.epi_iff_surjective _).mp
    (epi_gradedVertexProjectiveToSimple k Q i)
  exact_d_π := by
    have hex := GradedModuleCat.exact_iff.mp (shortExact_gradedVertexSimpleResolution k Q i).exact
    rw [gradedVertexSimpleResolution_def] at hex
    exact hex
  exact_d_d
    | 0 => (LinearMap.exact_zero_iff_injective _ _).mpr <|
      (GradedModuleCat.mono_iff_injective _).mp (mono_gradedArrowSumToVertexProjective k Q i)
    | 1 => by
      dsimp [resolutionTerm]
      exact (LinearMap.exact_zero_iff_injective _ _).mpr (Function.injective_of_subsingleton _)
    | _ + 2 => by
      dsimp [resolutionTerm]
      exact (LinearMap.exact_zero_iff_injective _ _).mpr (Function.injective_of_subsingleton _)

/-- The degree-zero term of the first-arrow resolution of `Sᵢ` is `kQ eᵢ`. -/
@[simp]
theorem gradedVertexSimpleProjectiveResolution_termObj_zero (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).termObj 0 =
      gradedVertexProjective k Q i := by
  unfold gradedVertexSimpleProjectiveResolution
  rfl

/-- The degree-one term of the first-arrow resolution of `Sᵢ` is `⨁_{a : i ⟶ j} (kQ eⱼ){1}`. -/
@[simp]
theorem gradedVertexSimpleProjectiveResolution_termObj_one (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).termObj 1 =
      gradedArrowSum k Q i := by
  unfold gradedVertexSimpleProjectiveResolution
  rfl

/-- All terms of the first-arrow resolution of `Sᵢ` in homological degrees `n ≥ 2` vanish. -/
theorem subsingleton_gradedVertexSimpleProjectiveResolution_of_two_le (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton ((gradedVertexSimpleProjectiveResolution k Q i).X n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  dsimp only [gradedVertexSimpleProjectiveResolution]
  exact inferInstanceAs (Subsingleton PUnit.{max u v w + 1})

/-- Every term of the first-arrow resolution of `Sᵢ` is finitely generated over `kQ`. -/
instance moduleFinite_gradedVertexSimpleProjectiveResolution (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] (n : ℕ) :
    Module.Finite (pathAlgebra k Q)
      ((gradedVertexSimpleProjectiveResolution k Q i).X n) := by
  unfold gradedVertexSimpleProjectiveResolution
  match n with
  | 0 =>
    exact (gradedFiniteProjectiveModules_iff.mp
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q i)).1
  | 1 =>
    exact gradedFiniteModules_iff.mp (gradedFiniteModules_gradedArrowSum k Q i)
  | _ + 2 =>
    exact inferInstanceAs (Module.Finite (pathAlgebra k Q) PUnit.{max u v w + 1})

/-- **The first-arrow resolution of a graded vertex simple is linear.** -/
theorem isLinear_gradedVertexSimpleProjectiveResolution (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).IsLinear := by
  rw [GradedProjectiveResolution.isLinear_iff]
  intro n
  unfold gradedVertexSimpleProjectiveResolution
  match n with
  | 0 =>
    rw [Nat.cast_zero]
    exact isGeneratedInDegree_zero_gradedVertexProjective k Q i
  | 1 =>
    rw [Nat.cast_one]
    exact isGeneratedInDegree_one_gradedArrowSum k Q i
  | _ + 2 =>
    rw [InternalGrading.isGeneratedInDegree_iff]
    intro x
    simpa only [Subsingleton.elim x (0 : PUnit.{max u v w + 1})] using (Submodule.zero_mem _)

/-- **The first-arrow resolution of a graded vertex simple is minimal.** -/
theorem isMinimal_gradedVertexSimpleProjectiveResolution (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (gradedVertexSimpleProjectiveResolution k Q i).IsMinimal := by
  let _ := integerGradedAlgebra k Q
  exact (isLinear_gradedVertexSimpleProjectiveResolution k Q i).isMinimal
    (fun _ hp => integerGrade_eq_bot_of_neg k Q hp)

end Resolution

section ArrowSumClass

variable (k Q) [CommRing k] [Fintype Q]

/-- The class of the arrow kernel `⨁_{a : j ⟶ i} (kQ eᵢ){1}` in `K₀^gr(proj kQ)` is
`∑ i, |j ⟶ i| q [kQ eᵢ]`. -/
theorem laurentK0_gradedArrowSum_eq_sum (j : Q) [Finite ((i : Q) × (j ⟶ i))] :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ =
      ∑ i : Q, ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) •
        gradedVertexProjectiveClass k Q i := by
  classical
  let _ (i : Q) : Finite (j ⟶ i) :=
    Finite.of_injective (fun f : j ⟶ i => (⟨i, f⟩ : (i : Q) × (j ⟶ i)))
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  let _ (i : Q) : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  let e : Fin (Fintype.card ((i : Q) × (j ⟶ i))) ≃ ((i : Q) × (j ⟶ i)) :=
    (Fintype.equivFin _).symm
  let P := gradedFiniteProjectiveModules (integerGrade k Q)
  let G : ((i : Q) × (j ⟶ i)) → GradedModuleCat.{max u v w} (integerGrade k Q) :=
    fun a => (gradedVertexProjective k Q a.1).shiftObj 1
  let F : Fin (Fintype.card ((i : Q) × (j ⟶ i))) → P.FullSubcategory := fun m =>
    ⟨G (e m), gradedFiniteProjectiveModules_shiftObj
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q (e m).1) 1⟩
  have _ : HasFiniteBiproducts P.FullSubcategory := hasFiniteBiproducts_of_hasBinaryBiproducts
  have _ : HasBiproduct (fun m => G (e m)) := HasBiproduct.of_hasCoproduct _
  have _ : HasBiproduct G := HasBiproduct.of_hasCoproduct _
  let e₁ : P.ι.obj (⨁ F) ≅ ⨁ (fun m => G (e m)) := P.ι.mapBiproduct F
  let e₂ : ⨁ (fun m => G (e m)) ≅ ⨁ G := biproduct.whiskerEquiv e (fun _ => Iso.refl _)
  let e₃ : ⨁ G ≅ GradedModuleCat.directSumObj G :=
    (biproduct.isColimit G).coconePointUniqueUpToIso (GradedModuleCat.coproductCofanIsColimit G)
  let iso : (⨁ F) ≅
      (⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ :
        P.FullSubcategory) :=
    ObjectProperty.isoMk P (e₁ ≪≫ e₂ ≪≫ e₃)
  rw [← LaurentK0.of_congr.{max u v w} _ iso,
    ← LaurentK0.ofExactK0_exactK0_of.{max u v w},
    ← ExactK0.fromSplit_of.{max u v w},
    SplitK0.of_biproduct, map_sum, map_sum]
  have hterm : ∀ m,
      LaurentK0.ofExactK0.{max u v w}
          (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
          (ExactK0.fromSplit.{max u v w} _ (SplitK0.of.{max u v w} (F m))) =
        (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClass k Q (e m).1 := fun m => by
    rw [ExactK0.fromSplit_of.{max u v w}, LaurentK0.ofExactK0_exactK0_of.{max u v w},
      gradedVertexProjectiveClass_eq]
    exact laurentK0_projective_of_shiftObj
      ⟨gradedVertexProjective k Q (e m).1,
        gradedFiniteProjectiveModules_gradedVertexProjective k Q (e m).1⟩ 1
  simp_rw [hterm]
  rw [e.sum_comp fun a : (i : Q) × (j ⟶ i) =>
    (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClass k Q a.1,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul
    (LaurentPolynomial ℤ), smul_smul]

end ArrowSumClass

/-! ### Betti Poincaré matrix of a finite acyclic path algebra -/

section BettiMatrix

variable (k Q) [Field k] [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- **The Betti Poincaré matrix of a finite acyclic path algebra is `I + q t Aᵀ`.** In the graded
vertex-projective basis `[kQ eᵢ]`, the `(i, j)` entry of the Betti Poincaré matrix of any minimal
graded projective resolutions `r` of the graded vertex simples `Sⱼ` is `δᵢⱼ + |j ⟶ i| q t`. -/
theorem bettiPoincareMatrix_gradedVertexSimple [DecidableEq Q]
    (r : ∀ l, GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q l).grading)
    [∀ l n, Module.Finite (pathAlgebra k Q) ((r l).X n)]
    (hr : ∀ l, (r l).IsMinimal) (i j : Q) :
    bettiPoincareMatrix (gradedVertexProjectiveClassBasis k Q) r i j =
      (if i = j then 1 else 0) +
        PowerSeries.C ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) * PowerSeries.X := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  let _ (a b : Q) : Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance a b
  have heq :
      bettiPoincareMatrix (gradedVertexProjectiveClassBasis k Q) r =
        bettiPoincareMatrix (gradedVertexProjectiveClassBasis k Q)
          (fun l => gradedVertexSimpleProjectiveResolution k Q l) :=
    bettiPoincareMatrix_eq_of_isMinimal (gradedVertexProjectiveClassBasis k Q) hr
      (fun l => isMinimal_gradedVertexSimpleProjectiveResolution k Q l)
      (fun _ hp => integerGrade_eq_bot_of_neg k Q hp)
  rw [heq, bettiPoincareMatrix_apply]
  let r₀ := gradedVertexSimpleProjectiveResolution k Q j
  have h0 :
      PowerSeries.coeff 0 (r₀.bettiPoincareSeries (gradedVertexProjectiveClassBasis k Q) i) =
        if i = j then 1 else 0 := by
    rw [GradedProjectiveResolution.coeff_bettiPoincareSeries]
    have hterm :
        LaurentK0.of.{max u v w}
            (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
            (r₀.finiteProjectiveTerm 0) =
          gradedVertexProjectiveClassBasis k Q j := by
      rw [gradedVertexProjectiveClassBasis_apply, gradedVertexProjectiveClass_eq]
      congr 1
      refine ObjectProperty.FullSubcategory.ext ?_
      rw [r₀.finiteProjectiveTerm_obj 0, gradedVertexSimpleProjectiveResolution_termObj_zero]
    rw [hterm, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  have h1 :
      PowerSeries.coeff 1 (r₀.bettiPoincareSeries (gradedVertexProjectiveClassBasis k Q) i) =
        (Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1 := by
    rw [GradedProjectiveResolution.coeff_bettiPoincareSeries]
    have hterm :
        r₀.finiteProjectiveTerm 1 =
          ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ :=
      ObjectProperty.FullSubcategory.ext <| by
        rw [r₀.finiteProjectiveTerm_obj 1, gradedVertexSimpleProjectiveResolution_termObj_one]
    rw [hterm, laurentK0_gradedArrowSum_eq_sum k Q j, map_sum, Finsupp.finsetSum_apply]
    have hcoord (l : Q) :
        ((gradedVertexProjectiveClassBasis k Q).repr
            (((Nat.card (j ⟶ l) : LaurentPolynomial ℤ) * T 1) •
              gradedVertexProjectiveClass k Q l)) i =
          if l = i then (Nat.card (j ⟶ l) : LaurentPolynomial ℤ) * T 1 else 0 := by
      rw [← gradedVertexProjectiveClassBasis_apply k Q l, map_smul, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp_rw [hcoord]
    simp
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero =>
    rw [h0, map_add, PowerSeries.coeff_zero_mul_X, add_zero]
    split_ifs <;> simp [PowerSeries.coeff_one]
  | succ n =>
    cases n with
    | zero =>
      rw [h1, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_C]
      split_ifs <;> simp [PowerSeries.coeff_one]
    | succ m =>
      have hsub := subsingleton_gradedVertexSimpleProjectiveResolution_of_two_le k Q j
        (n := m + 2) (by omega)
      have hzero :=
        r₀.coeff_bettiPoincareSeries_eq_zero_of_subsingleton
          (gradedVertexProjectiveClassBasis k Q) i hsub
      rw [hzero, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
        ite_eq_right (Nat.succ_ne_zero m), add_zero]
      split_ifs <;> simp [PowerSeries.coeff_one]

/-- **Evaluation of the Betti Poincaré matrix of a finite acyclic path algebra at `t = -1`**
gives `1 - q Aᵀ`, the left and right inverse of the graded Cartan matrix `C(q)`. -/
theorem eval_neg_one_trunc_two_bettiPoincareMatrix [DecidableEq Q]
    (r : ∀ l, GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q l).grading)
    [∀ l n, Module.Finite (pathAlgebra k Q) ((r l).X n)]
    (hr : ∀ l, (r l).IsMinimal) :
    (bettiPoincareMatrix (gradedVertexProjectiveClassBasis k Q) r).map
        (fun P => (PowerSeries.trunc 2 P).eval (-1)) =
      1 - (T 1 : LaurentPolynomial ℤ) •
        (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ))ᵀ := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, bettiPoincareMatrix_gradedVertexSimple k Q r hr i j, map_add]
  by_cases hij : i = j <;>
    simp [hij, PowerSeries.trunc_one, PowerSeries.trunc_C_mul, PowerSeries.trunc_X,
      Polynomial.eval_X, sub_eq_add_neg, -map_mul, -map_natCast]

end BettiMatrix

end TauCeti.PathAlgebra
