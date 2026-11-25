/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
import TauCeti.MeasureTheory.Integral.FullSimplex
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The period of a closed two-form on the class of a torus is its integral

For positive periods `p` and `q`, the class of the parameter torus
`[T] = [ℝ / pℤ] × [ℝ / qℤ] ∈ H₂(ℝ / pℤ × ℝ / qℤ; ℤ)` (`TauCeti.addCircleProdFundamentalClass`)
is the cross product of the circuit classes of the two circles. This file proves that pairing a
closed two-form `φ` with it computes the integral of `φ` over the torus, oriented as the product of
the positive orientations of the two circles:

`⟨[φ], [T]⟩ = ∫_T φ`

(`TauCeti.closedFormHomologyPeriod_addCircleProdFundamentalClass`). This is the comparison of the
integration of top forms with the de Rham pairing against fundamental classes, for the
two-dimensional torus. Combined with naturality of the periods, it computes the periods of closed
two-forms on the class of every smooth parametrized torus, such as the torus `(ℝ / ℤ) × γ` over a
closed orbit `γ` of a suspension flow, as integrals over the parameter torus.

The proof represents `[T]` by an explicit smooth cycle. The cross product of the classes of the
circuits `s ↦ [s p]` and `t ↦ [t q]` is the class of their shuffle product
(`TauCeti.addCircleProdFundamentalClass_eq_homologyπ`), the difference of the two singular
`2`-simplices `y ↦ ([(y₀ + y₁) p], [y₁ q])` and `y ↦ ([y₁ p], [(y₀ + y₁) q])` of the torus, read on
the full-dimensional simplex `Δ² ⊆ ℝ²`. Both are smooth: they are the quotient map
`ℝ × ℝ → ℝ / pℤ × ℝ / qℤ` composed with linear maps of determinants `p q` and `-p q`. So the period
of `φ` is the difference of the integrals of `φ` over the two simplices. On `Δ²` an alternating
form of degree two is its value on the standard basis times the determinant, so this difference is
`p q` times the sum of the integrals of `f(s, t) = φ_([s p], [t q])((1, 0), (0, 1))` over the two
halves of the unit square, which is the integral of `f` over the square. Rescaling the square to
the fundamental rectangle `[0, p] × [0, q]` gives the integral of `φ` over the torus
(`AddCircle.integralTopForm_prod_eq_setIntegral`).

## Main results

* `TauCeti.closedFormHomologyPeriod_addCircleProdFundamentalClass`: the period of a closed
  two-form on the class of the torus is its integral over the torus.
* `TauCeti.closedFormHomologyPeriod_singularHomologyMap_addCircleProdFundamentalClass`: the
  period of a closed two-form on the image of the class of the torus under a smooth map is the
  integral of its pullback over the torus.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (integration over smooth
  singular chains and the de Rham homomorphism).
* A. Hatcher, *Algebraic Topology*, Section 3.B (the cross product, computed on cycles by the
  shuffle product).
-/

public section

noncomputable section

open Set MeasureTheory CategoryTheory MonoidalCategory Convexity
open scoped Manifold ContDiff Simplicial

namespace TauCeti

/-! ### The two simplices of the torus cycle -/

section Simplex

variable (p q : ℝ)

/-- The linear map `y ↦ ((y₀ + y₁) p, y₁ q)`, which parametrizes the first simplex of the torus
cycle in the real coordinates of the two circles. -/
private def lowerMap : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (p • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) + EuclideanSpace.proj 1)).prod
    (q • EuclideanSpace.proj 1)

/-- The linear map `y ↦ (y₁ p, (y₀ + y₁) q)`, which parametrizes the second simplex of the torus
cycle in the real coordinates of the two circles. -/
private def upperMap : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (p • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).prod
    (q • (EuclideanSpace.proj 0 + EuclideanSpace.proj 1))

private theorem lowerMap_apply (y : EuclideanSpace ℝ (Fin 2)) :
    lowerMap p q y = (p * (y 0 + y 1), q * y 1) :=
  (rfl)

private theorem upperMap_apply (y : EuclideanSpace ℝ (Fin 2)) :
    upperMap p q y = (p * y 1, q * (y 0 + y 1)) :=
  (rfl)

/-- The degeneracy `s₁ c_p` of the circuit simplex of `ℝ / pℤ`, read on `Δ²`, is
`y ↦ [(y₀ + y₁) p]`. -/
private theorem toSSetObjEquiv_σ_one_circuitSimplex (y : fullSimplex 2) :
    (TopCat.of (AddCircle p)).toSSetObjEquiv _
        ((TopCat.toSSet.obj _).σ 1 (AddCircle.circuitSimplex p)) (fullSimplexEquivStdSimplex 2 y) =
      ((p * (y.val 0 + y.val 1) : ℝ) : AddCircle p) := by
  rw [TopCat.toSSetObjEquiv_σ_apply, AddCircle.toSSetObjEquiv_circuitSimplex_apply]
  -- The vertex map of `s₁` is `Fin.predAbove 1` on `Fin (1 + 1 + 1)`, the `Fin 3` of the lemma.
  exact congrArg (fun t : ℝ ↦ ((p * t : ℝ) : AddCircle p))
    (homeomorphI_map_predAbove_one_fullSimplexEquivStdSimplex_coe y)

/-- The degeneracy `s₀ c_p` of the circuit simplex of `ℝ / pℤ`, read on `Δ²`, is `y ↦ [y₁ p]`. -/
private theorem toSSetObjEquiv_σ_zero_circuitSimplex (y : fullSimplex 2) :
    (TopCat.of (AddCircle p)).toSSetObjEquiv _
        ((TopCat.toSSet.obj _).σ 0 (AddCircle.circuitSimplex p)) (fullSimplexEquivStdSimplex 2 y) =
      ((p * y.val 1 : ℝ) : AddCircle p) := by
  rw [TopCat.toSSetObjEquiv_σ_apply, AddCircle.toSSetObjEquiv_circuitSimplex_apply]
  -- As above, for `Fin.predAbove 0`.
  exact congrArg (fun t : ℝ ↦ ((p * t : ℝ) : AddCircle p))
    (homeomorphI_map_predAbove_zero_fullSimplexEquivStdSimplex_coe y)

/-- The first simplex `(s₁ c_p, s₀ c_q)` of the shuffle product of the circuit simplices, read on
`Δ²`, is `y ↦ ([(y₀ + y₁) p], [y₁ q])`. -/
private theorem toSSetObjEquiv_lower (y : fullSimplex 2) :
    (TopCat.of (AddCircle p × AddCircle q)).toSSetObjEquiv _
        ((Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (AddCircle p))
          (TopCat.of (AddCircle q))).app _
          (((TopCat.toSSet.obj _).σ 1 (AddCircle.circuitSimplex p),
            (TopCat.toSSet.obj _).σ 0 (AddCircle.circuitSimplex q)) :
            (TopCat.toSSet.obj (TopCat.of (AddCircle p)) ⊗
              TopCat.toSSet.obj (TopCat.of (AddCircle q))) _⦋2⦌))
        (fullSimplexEquivStdSimplex 2 y) =
      Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) (lowerMap p q y) :=
  (TopCat.toSSetObjEquiv_μ_apply (X := TopCat.of (AddCircle p)) (Y := TopCat.of (AddCircle q)) _ _
    (fullSimplexEquivStdSimplex 2 y)).trans
    (Prod.ext (toSSetObjEquiv_σ_one_circuitSimplex p y) (toSSetObjEquiv_σ_zero_circuitSimplex q y))

/-- The second simplex `(s₀ c_p, s₁ c_q)` of the shuffle product of the circuit simplices, read on
`Δ²`, is `y ↦ ([y₁ p], [(y₀ + y₁) q])`. -/
private theorem toSSetObjEquiv_upper (y : fullSimplex 2) :
    (TopCat.of (AddCircle p × AddCircle q)).toSSetObjEquiv _
        ((Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (AddCircle p))
          (TopCat.of (AddCircle q))).app _
          (((TopCat.toSSet.obj _).σ 0 (AddCircle.circuitSimplex p),
            (TopCat.toSSet.obj _).σ 1 (AddCircle.circuitSimplex q)) :
            (TopCat.toSSet.obj (TopCat.of (AddCircle p)) ⊗
              TopCat.toSSet.obj (TopCat.of (AddCircle q))) _⦋2⦌))
        (fullSimplexEquivStdSimplex 2 y) =
      Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) (upperMap p q y) :=
  (TopCat.toSSetObjEquiv_μ_apply (X := TopCat.of (AddCircle p)) (Y := TopCat.of (AddCircle q)) _ _
    (fullSimplexEquivStdSimplex 2 y)).trans
    (Prod.ext (toSSetObjEquiv_σ_zero_circuitSimplex p y) (toSSetObjEquiv_σ_one_circuitSimplex q y))

end Simplex

/-! ### Integrals over the simplices of the torus -/

section Integral

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

/-- The value `φ_([s], [t])((1, 0), (0, 1))` of a two-form of the torus on the standard frame at
the image of `(s, t)`: the integrand of `AddCircle.integralTopForm_prod_eq_setIntegral`. -/
private abbrev torusIntegrand (φ : RoughForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) ℝ 2)
    (z : ℝ × ℝ) : ℝ :=
  φ ((z.1 : AddCircle p), (z.2 : AddCircle q)) ![((1 : ℝ), (0 : ℝ)), (0, 1)]

/-- The smooth singular simplex of the torus which, read on `Δ²`, is the quotient map composed with
a linear map `A`. -/
private def torusSimplex (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ)
    (τ : (TopCat.toSSet.obj (TopCat.of (AddCircle p × AddCircle q))) _⦋2⦌)
    (hτ : ∀ y : fullSimplex 2, (TopCat.of (AddCircle p × AddCircle q)).toSSetObjEquiv _ τ
      (fullSimplexEquivStdSimplex 2 y) =
        Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) (A y)) :
    SmoothSimplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) 2 :=
  ⟨τ, mem_smoothSingularSubcomplex_of_contMDiffOn τ
    ((AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞).contMDiff.comp A.contMDiff).contMDiffOn
    Filter.univ_mem hτ⟩

variable {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ}
  {τ : (TopCat.toSSet.obj (TopCat.of (AddCircle p × AddCircle q))) _⦋2⦌}
  {hτ : ∀ y : fullSimplex 2, (TopCat.of (AddCircle p × AddCircle q)).toSSetObjEquiv _ τ
    (fullSimplexEquivStdSimplex 2 y) =
      Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) (A y)}

/-- The integral of a two-form over a torus simplex with linear part `A` is the integral over `Δ²`
of the determinant of `A` times the torus integrand at `A y`. -/
private theorem integral_torusSimplex
    (φ : RoughForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) ℝ 2) :
    (torusSimplex A τ hτ).integral φ = ∫ y in fullSimplex 2,
      ((A (EuclideanSpace.single 0 1)).1 * (A (EuclideanSpace.single 1 1)).2 -
        (A (EuclideanSpace.single 0 1)).2 * (A (EuclideanSpace.single 1 1)).1) *
        torusIntegrand φ (A y) := by
  have hg : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓘(ℝ).prod 𝓘(ℝ))
      (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) ∘ A) :=
    ((AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞).contMDiff.comp A.contMDiff).mdifferentiable
      (by simp)
  refine ((torusSimplex A τ hτ).integral_eq_setIntegral_mpullback φ
    (fun y ↦ by
      rw [SmoothSimplex.toContinuousMap_apply]
      exact (hτ y).symm) fun y _ ↦ hg y).trans ?_
  refine setIntegral_congr_fun (isClosed_fullSimplex 2).measurableSet fun y _ ↦ ?_
  have hD (v : EuclideanSpace ℝ (Fin 2)) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) ∘ A) y v = A v := by
    rw [mfderiv_comp y ((AddCircle.hasMFDerivAt_prodMap_coe p q (A y)).mdifferentiableAt)
      A.mdifferentiableAt, ContinuousLinearMap.mfderiv_eq, AddCircle.mfderiv_prodMap_coe]
    -- The identity of `ℝ × ℝ` composed with `A`, applied to `v`.
    rfl
  refine (mpullback_apply _ φ y _).trans ?_
  have hv : (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓘(ℝ).prod 𝓘(ℝ))
      (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) ∘ A) y
        (EuclideanSpace.single i 1)) =
      ![A (EuclideanSpace.single 0 1), A (EuclideanSpace.single 1 1)] := by
    ext i : 1
    fin_cases i <;> exact hD _
  -- The tangent spaces of the torus are `ℝ × ℝ`, where a two-form is its value on the standard
  -- frame times the determinant.
  rw [hv]
  exact ((φ _).apply_eq_det_mul (Module.Basis.finTwoProd ℝ) _).trans
    (congrArg₂ (· * ·) (Module.Basis.det_finTwoProd_apply _ _)
      (congrArg (φ _) (Module.Basis.coe_finTwoProd ℝ)))

end Integral

/-! ### The torus cycle -/

section Cycle

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- The smooth simplex `y ↦ ([(y₀ + y₁) p], [y₁ q])` of the torus. -/
private abbrev lowerSimplex : SmoothSimplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) 2 :=
  torusSimplex (lowerMap p q) _ (toSSetObjEquiv_lower p q)

/-- The smooth simplex `y ↦ ([y₁ p], [(y₀ + y₁) q])` of the torus. -/
private abbrev upperSimplex : SmoothSimplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) 2 :=
  torusSimplex (upperMap p q) _ (toSSetObjEquiv_upper p q)

/-- The shuffle product of the circuits of the two circles, as a smooth singular chain. -/
private def smoothTorusChain : ((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ))
    (AddCircle p × AddCircle q) : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X 2 :=
  ((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (lowerSimplex p q)).hom 1 -
    ((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (upperSimplex p q)).hom 1

/-- As a singular chain, the smooth torus chain is the shuffle product of the circuit simplices. -/
private theorem chainComplexMap_ι_f_smoothTorusChain :
    ((SSet.chainComplexMap (smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ))
        (AddCircle p × AddCircle q)).ι (ModuleCat.of ℤ ℤ)).f 2).hom (smoothTorusChain p q) =
      TopCat.shuffleChainOneOne (AddCircle.circuitSimplex p) (AddCircle.circuitSimplex q) := by
  rw [smoothTorusChain, map_sub, chainComplexMap_ι_f_ιChainComplex,
    chainComplexMap_ι_f_ιChainComplex, TopCat.shuffleChainOneOne_def]
  -- The underlying singular simplices of the two torus simplices are the two shuffled simplices.
  rfl

/-- The smooth torus chain is a cycle, since its image among all singular chains is one and the
inclusion of smooth chains is injective. -/
private theorem d_smoothTorusChain :
    (((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).d 2 1).hom (smoothTorusChain p q) = 0 :=
  HomologicalComplex.d_apply_eq_zero_of_d_f_apply_eq_zero
    (SSet.chainComplexMap (smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ))
      (AddCircle p × AddCircle q)).ι (ModuleCat.of ℤ ℤ))
    (by
      rw [chainComplexMap_ι_f_smoothTorusChain]
      exact singularChains_d_shuffleChainOneOne_circuitSimplex p q)

/-- The class of the smooth torus cycle in smooth singular homology. -/
private def smoothTorusClass : ((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ))
    (AddCircle p × AddCircle q) : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology 2 :=
  (((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ 2).hom
    (((smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).moduleCatCyclesMk (smoothTorusChain p q) 1 (ChainComplex.next_nat_succ 1)
        (d_smoothTorusChain p q))

/-- The inclusion of smooth chains sends the smooth torus class to the class of the torus. -/
private theorem homologyMap_ι_smoothTorusClass :
    (SSet.homologyMap (smoothSingularSubcomplex (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q)).ι
      (ModuleCat.of ℤ ℤ) 2).hom (smoothTorusClass p q) = addCircleProdFundamentalClass p q := by
  rw [smoothTorusClass, SSet.homologyMap,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  exact (addCircleProdFundamentalClass_eq_homologyπ p q _
    ((HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).trans
      (chainComplexMap_ι_f_smoothTorusChain p q))).symm

end Cycle

/-! ### The period on the class of the torus -/

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- **The period of a closed two-form on the class of a torus is its integral.** For positive
periods `p` and `q` and a closed two-form `φ` on the torus `ℝ / pℤ × ℝ / qℤ`, the period of `φ` on
the class `[ℝ / pℤ] × [ℝ / qℤ]` of the torus is the integral of `φ` over the torus, oriented as
the product of the positive orientations of the two circles. -/
theorem closedFormHomologyPeriod_addCircleProdFundamentalClass
    (φ : closedForms (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) 2) :
    closedFormHomologyPeriod φ (addCircleProdFundamentalClass p q) =
      integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q)) φ.val := by
  have hp : 0 < p := Fact.out
  have hq : 0 < q := Fact.out
  -- The integrand `f` of the torus integral and its rescaling `F` to the unit square.
  let f := torusIntegrand (φ.val : RoughForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) ℝ 2)
  let F : ℝ × ℝ → ℝ := fun z ↦ f (p * z.1, q * z.2)
  have hfc : Continuous f := by
    have h := (φ.val.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv
      ((AddCircle.isLocalDiffeomorph_prodMap_coe p q 1).contMDiff) (1, 0) (0, 1)
    refine h.congr fun z ↦ ?_
    rw [AddCircle.mfderiv_prodMap_coe]
    -- The quotient map is `Prod.map` of the two coercions, and its derivative is the identity.
    rfl
  have hFc : Continuous F := hfc.comp (by fun_prop)
  rw [← homologyMap_ι_smoothTorusClass, smoothTorusClass,
    closedFormHomologyPeriod_homologyMap_ι_homologyπ, HomologicalComplex.iCycles_moduleCatCyclesMk,
    smoothTorusChain, map_sub, integrationCochain_ιChainComplex, integrationCochain_ιChainComplex,
    one_smul, one_smul, (integral_torusSimplex φ.val : (lowerSimplex p q).integral _ = _),
    (integral_torusSimplex φ.val : (upperSimplex p q).integral _ = _)]
  calc _ = p * q * ((∫ y in fullSimplex 2, F (y 0 + y 1, y 1)) +
        ∫ y in fullSimplex 2, F (y 0, y 0 + y 1)) := by
        -- The two simplices have determinants `p q` and `-p q`, and the second one covers the
        -- upper half of the unit square.
        rw [(setIntegral_fullSimplex_comp_shear_snd F).trans
          (setIntegral_fullSimplex_comp_swap_shear_snd F).symm, mul_add, ← integral_const_mul,
          ← integral_const_mul, sub_eq_add_neg, ← integral_neg]
        congr 1 <;> refine setIntegral_congr_fun (isClosed_fullSimplex 2).measurableSet
          fun y _ ↦ ?_
        · rw [lowerMap_apply p q y]
          congr 1
          simp [lowerMap_apply]
        · rw [upperMap_apply p q y, ← neg_mul]
          congr 1
          simp [upperMap_apply, mul_comm]
    _ = p * q * ∫ z in Icc (0, 0) (1, 1), F z := by
        rw [setIntegral_fullSimplex_add_setIntegral_fullSimplex hFc.integrableOn_Icc]
    _ = ∫ z in Icc 0 p ×ˢ Icc 0 q, f z := by
        rw [← Icc_prod_Icc, ← smul_eq_mul, ← setIntegral_Icc_mul_prod_Icc_mul_eq f hp hq, mul_zero,
          mul_one, mul_zero, mul_one]
    _ = ∫ z in Ico 0 p ×ˢ Ico 0 q, f z := by
        refine setIntegral_congr_set ?_
        rw [Measure.volume_eq_prod]
        exact (Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc).symm
    _ = _ := by
        rw [AddCircle.integralTopForm_prod_eq_setIntegral p q
          (φ.val.isSmoothForm.integrableTopForm
            (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
            (Module.Basis.finTwoProd ℝ)) 0 0, zero_add, zero_add]

variable {p q} in
/-- **The period of a closed two-form on the image of the torus class is an integral.** For a
smooth map `f` from the torus `ℝ / pℤ × ℝ / qℤ` to a manifold `N` and a closed two-form `φ` on `N`,
the period of `φ` on the image `f_*[T]` of the class of the torus is the integral of `f^* φ` over
the torus, oriented as the product of the positive orientations of the two circles. -/
theorem closedFormHomologyPeriod_singularHomologyMap_addCircleProdFundamentalClass
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N]
    [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]
    {f : AddCircle p × AddCircle q → N} (hf : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) J ∞ f)
    (φ : closedForms J N 2) :
    closedFormHomologyPeriod φ
        (ContinuousMap.singularHomologyMap ℤ 2 ⟨f, hf.continuous⟩
          (addCircleProdFundamentalClass p q)) =
      integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
        (SmoothForm.mpullback f hf φ.val).val := by
  rw [← closedFormHomologyPeriod_mpullback hf,
    closedFormHomologyPeriod_addCircleProdFundamentalClass, closedForms.coe_mpullback]

end TauCeti
