/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.DiscreteQuotient
public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.Topology.ContinuousMap.LocallyConstant

/-!
# Extension of coefficients of measures along bounded homomorphisms

Let `X` be a profinite space, `O` a topological commutative ring, `K` a complete ultrametric
normed commutative ring and `j : O →+* K` a ring homomorphism with `‖j a‖ ≤ B` for every `a`.
The extension of an `O`-valued measure `μ ∈ D(X, O)` is the `K`-valued measure
`ι_j(μ) = extendCoefficients j hj μ ∈ D(X, K)`.

On a locally constant function `Σ_i c_i 1_{U_i}` attached to a finite clopen partition the
extension is `Σ_i c_i j(μ(1_{U_i}))`. This is independent of the partition. The ultrametric
inequality bounds it by `B * max_i ‖c_i‖`, so it extends by density and completeness of `K` to
all of `C(X, K)`. The resulting measure is characterised by its finite projections. Along every
continuous map `q : X → A` to a finite discrete space, the coefficients of `ι_j(μ)` are the
images under `j` of those of `μ`. When `j` is continuous, `ι_j(μ)(j ∘ f) = j(μ(f))` for every
`f ∈ C(X, O)`, and this property determines `ι_j(μ)`. If `K` is a nontrivially normed field
and `j` is a topological embedding onto its closed unit ball, the measures `ι_j(μ)` are exactly
the `K`-valued measures of operator norm at most `1`: such a measure sends test functions
`j ∘ f` into the closed unit ball, hence into the image of `j`.

A uniform bound on `‖j a‖` is needed. Give `O = ℚ_p` the norm `max(1, |a|_p)` for `a ≠ 0`, so
that its topology is discrete. Then Haar averaging `f ↦ p^{-n} Σ_{a mod p^n} f(a)` is an
`O`-valued measure on `ℤ_p` with `μ(1_{p^n ℤ_p}) = p^{-n}`, and for `j = id` into the usual `ℚ_p`
no continuous extension exists, since `p^n 1_{p^n ℤ_p} → 0` would have integral `1`.

## Main definitions

* `AbstractMeasure.extendCoefficients j hj`: the additive map `D(X, O) → D(X, K)`.

## Main results

* `AbstractMeasure.finiteProjection_extendCoefficients`: the finite projections of
  `extendCoefficients j hj μ` are those of `μ` with `j` applied to the coefficients.
* `AbstractMeasure.extendCoefficients_apply_comp_eq_sum`: integration of a function factoring
  through a finite discrete quotient.
* `AbstractMeasure.extendCoefficients_apply_locallyConstant`: agreement with `j` on
  locally constant source-valued tests, without assuming continuity of `j`.
* `AbstractMeasure.norm_extendCoefficients_apply_le`: the evaluation is bounded by `B` times the
  supremum norm of the test function.
* `AbstractMeasure.norm_toCLMEquiv_extendCoefficients_le`: over a nontrivially normed field, the
  extension has operator norm at most `B`.
* `AbstractMeasure.extendCoefficients_apply_comp`: `ι_j(μ)(j ∘ f) = j(μ(f))` for continuous `j`.
* `AbstractMeasure.eq_extendCoefficients_of_apply_comp`: this property characterises `ι_j(μ)`.
* `AbstractMeasure.exists_apply_comp_eq_of_norm_le_one`: over a nontrivially normed field `K`,
  for an embedding `j` onto its closed unit ball and compact `X`, a `K`-valued measure of norm at
  most `1` restricts to an `O`-valued measure.
* `AbstractMeasure.mem_range_extendCoefficients_iff`,
  `AbstractMeasure.existsUnique_apply_comp_eq_iff_norm_le_one`: over a nontrivially normed field
  `K`, for an embedding `j` onto its closed unit ball, the extensions of coefficients form the
  closed unit ball of `D(X, K)`.
* `AbstractMeasure.extendCoefficients_smul`, `AbstractMeasure.extendCoefficients_dirac`,
  `AbstractMeasure.extendCoefficients_map`, `AbstractMeasure.extendCoefficients_injective` and
  `AbstractMeasure.extendCoefficients_surjective`.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X]

section TopologicalRing

variable {K O : Type*} [NormedCommRing K] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  (j : O →+* K) (μ : D(X, O))

section Cylinder

variable {A B : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [DiscreteTopology B] [Fintype B]

/-- The integral of the function `g ∘ q` against the coefficients of `μ` along `q`, transported to
`K` by `j`. -/
private def cylinderSum (q : C(X, A)) (g : A → K) : K :=
  ∑ a, g a * j (finiteProjection q μ a)

/-- Refining the finite quotient along `t` does not change `cylinderSum`. -/
private theorem cylinderSum_comp (r : C(X, B)) (t : C(B, A)) (g : A → K) :
    cylinderSum j μ (t.comp r) g = cylinderSum j μ r (g ∘ t) := by
  classical
  rw [cylinderSum, cylinderSum, finiteProjection_comp,
    ← Finsupp.sum_fintype _ (fun a c ↦ g a * j c) (fun _ ↦ by simp),
    ← Finsupp.sum_fintype _ (fun b c ↦ (g ∘ t) b * j c) (fun _ ↦ by simp)]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [map_add, mul_add])

/-- `cylinderSum` depends only on the function `g ∘ q`. -/
private theorem cylinderSum_eq_of_comp_eq (q : C(X, A)) (q' : C(X, B)) (g : A → K)
    (g' : B → K) (h : ∀ x, g (q x) = g' (q' x)) :
    cylinderSum j μ q g = cylinderSum j μ q' g' := by
  have hq : (ContinuousMap.fst).comp (q.prodMk q') = q := by ext; rfl
  have hq' : (ContinuousMap.snd).comp (q.prodMk q') = q' := by ext; rfl
  calc cylinderSum j μ q g = cylinderSum j μ ((ContinuousMap.fst).comp (q.prodMk q')) g := by
        rw [hq]
    _ = cylinderSum j μ (q.prodMk q') (g ∘ Prod.fst) := cylinderSum_comp j μ _ _ g
    _ = cylinderSum j μ (q.prodMk q') (g' ∘ Prod.snd) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        by_cases hp : p ∈ Set.range (q.prodMk q')
        · obtain ⟨x, rfl⟩ := hp
          simp [h x]
        · simp [finiteProjection_apply_of_notMem_range μ hp]
    _ = cylinderSum j μ ((ContinuousMap.snd).comp (q.prodMk q')) g' :=
        (cylinderSum_comp j μ (q.prodMk q') ContinuousMap.snd g').symm
    _ = cylinderSum j μ q' g' := by rw [hq']

private theorem cylinderSum_add (q : C(X, A)) (g g' : A → K) :
    cylinderSum j μ q (g + g') = cylinderSum j μ q g + cylinderSum j μ q g' := by
  simp [cylinderSum, add_mul, Finset.sum_add_distrib]

private theorem cylinderSum_smul (q : C(X, A)) (c : K) (g : A → K) :
    cylinderSum j μ q (c • g) = c * cylinderSum j μ q g := by
  simp [cylinderSum, Finset.mul_sum, mul_assoc]

/-- On a fibre indicator, `cylinderSum` is `j` applied to the corresponding coefficient. -/
private theorem cylinderSum_ite [DecidableEq A] (q : C(X, A)) (a : A) :
    cylinderSum j μ q (fun b ↦ if b = a then 1 else 0) = j (finiteProjection q μ a) := by
  simp [cylinderSum]

end Cylinder

/-- The finite discrete quotient of `X` attached to a locally constant function, as a continuous
map. -/
private def quotientMap {Y : Type*} (φ : LocallyConstant X Y) : C(X, φ.discreteQuotient) :=
  ⟨_, φ.discreteQuotient.proj_continuous⟩

private theorem lift_quotientMap {Y : Type*} (φ : LocallyConstant X Y) (x : X) :
    φ.lift (quotientMap φ x) = φ x :=
  congrFun φ.lift_comp_proj x

variable [CompactSpace X]

private instance {Y : Type*} (φ : LocallyConstant X Y) : Fintype φ.discreteQuotient :=
  Fintype.ofFinite _

/-- The extension of `μ` evaluated on a locally constant function, through the finite quotient
attached to it. -/
private def locallyConstantSum (φ : LocallyConstant X K) : K :=
  cylinderSum j μ (quotientMap φ) φ.lift

private theorem locallyConstantSum_eq {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Fintype A] (φ : LocallyConstant X K) (q : C(X, A)) (g : A → K) (h : ∀ x, g (q x) = φ x) :
    locallyConstantSum j μ φ = cylinderSum j μ q g :=
  cylinderSum_eq_of_comp_eq j μ _ _ _ _ fun x ↦ (lift_quotientMap φ x).trans (h x).symm

/-- The extension of `μ` on locally constant functions, as a `K`-linear map. -/
private def locallyConstantIntegral : LocallyConstant X K →ₗ[K] K where
  toFun := locallyConstantSum j μ
  map_add' φ ψ := by
    let r := (quotientMap φ).prodMk (quotientMap ψ)
    rw [locallyConstantSum_eq j μ (φ + ψ) r ((φ.lift ∘ Prod.fst) + (ψ.lift ∘ Prod.snd))
      fun _ ↦ rfl, cylinderSum_add, ← locallyConstantSum_eq j μ φ r _ fun _ ↦ rfl,
      ← locallyConstantSum_eq j μ ψ r _ fun _ ↦ rfl]
  map_smul' c φ := by
    rw [locallyConstantSum_eq j μ (c • φ) (quotientMap φ) (c • φ.lift)
      fun x ↦ by simp [lift_quotientMap],
      cylinderSum_smul, RingHom.id_apply, smul_eq_mul, locallyConstantSum]

private theorem locallyConstantIntegral_apply (φ : LocallyConstant X K) {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] [Fintype A] (q : C(X, A)) (g : A → K)
    (h : ∀ x, g (q x) = φ x) :
    locallyConstantIntegral j μ φ = cylinderSum j μ q g :=
  locallyConstantSum_eq j μ φ q g h

variable [IsUltrametricDist K] {B : ℝ}

/-- The ultrametric bound on a locally constant function. -/
private theorem norm_locallyConstantIntegral_le (hj : ∀ a, ‖j a‖ ≤ B)
    (φ : LocallyConstant X K) :
    ‖locallyConstantIntegral j μ φ‖ ≤ B * ‖LocallyConstant.toContinuousMapLinearMap K φ‖ := by
  rw [locallyConstantIntegral_apply j μ φ (quotientMap φ) φ.lift (lift_quotientMap φ), cylinderSum]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hj 0)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hB (norm_nonneg _))
    fun a _ ↦ ?_
  have hq : Function.Surjective (quotientMap φ) := by
    simpa only [quotientMap, ContinuousMap.coe_mk] using φ.discreteQuotient.proj_surjective
  obtain ⟨x, rfl⟩ := hq a
  rw [lift_quotientMap φ x, mul_comm B]
  have hφ : ‖φ x‖ ≤ ‖LocallyConstant.toContinuousMapLinearMap K φ‖ := by
    simpa only [LocallyConstant.toContinuousMapLinearMap_apply,
      LocallyConstant.coe_continuousMap] using
      (LocallyConstant.toContinuousMapLinearMap K φ).norm_coe_le_norm x
  exact (norm_mul_le _ _).trans <|
    mul_le_mul hφ (hj _) (norm_nonneg _) (norm_nonneg _)

variable [T2Space X] [TotallyDisconnectedSpace X] [CompleteSpace K]

variable (K) in
private abbrev locallyConstantTests :=
  (LocallyConstant.toContinuousMapLinearMap K (X := X) (Y := K)).range

variable (K) in
private def locallyConstantTestEquiv : LocallyConstant X K ≃ₗ[K] locallyConstantTests (X := X) K :=
  LinearEquiv.ofInjective (LocallyConstant.toContinuousMapLinearMap K)
    LocallyConstant.toContinuousMap_injective

private def integralOnLocallyConstantTests (hj : ∀ a, ‖j a‖ ≤ B) :
    locallyConstantTests (X := X) K →L[K] K :=
  ((locallyConstantIntegral j μ).comp (locallyConstantTestEquiv K).symm.toLinearMap).mkContinuous B
    (by
      intro f
      have hf := LinearEquiv.ofInjective_symm_apply (LocallyConstant.toContinuousMapLinearMap K)
        (h := LocallyConstant.toContinuousMap_injective) f
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, locallyConstantTestEquiv, hf,
        Submodule.norm_coe] using
        norm_locallyConstantIntegral_le j μ hj ((locallyConstantTestEquiv K).symm f))

/-- The extension of `μ` as a continuous linear functional on `C(X, K)`. -/
private def extendCoefficientsCLM (hj : ∀ a, ‖j a‖ ≤ B) : C(X, K) →L[K] K :=
  (integralOnLocallyConstantTests j μ hj).extend (locallyConstantTests (X := X) K).subtypeL

private theorem extendCoefficientsCLM_apply_test (hj : ∀ a, ‖j a‖ ≤ B) (φ : LocallyConstant X K) :
    extendCoefficientsCLM j μ hj (LocallyConstant.toContinuousMapLinearMap K φ) =
      locallyConstantIntegral j μ φ := by
  let e := locallyConstantTestEquiv (X := X) K
  have hφ : (locallyConstantTests (X := X) K).subtypeL (e φ) =
      LocallyConstant.toContinuousMapLinearMap K φ := by
    rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
    exact LinearEquiv.ofInjective_apply (LocallyConstant.toContinuousMapLinearMap K)
      (h := LocallyConstant.toContinuousMap_injective) φ
  have hd : DenseRange (locallyConstantTests (X := X) K).subtypeL := by
    rw [Submodule.coe_subtypeL]
    exact LocallyConstant.denseRange_toContinuousMapLinearMap_range_subtype K
  have he : IsUniformInducing (locallyConstantTests (X := X) K).subtypeL := by
    rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
    exact ⟨uniformity_subtype.symm⟩
  rw [← hφ, extendCoefficientsCLM, (integralOnLocallyConstantTests j μ hj).extend_eq
    (e := (locallyConstantTests (X := X) K).subtypeL)
    hd he (e φ)]
  simp only [integralOnLocallyConstantTests, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, e, LinearEquiv.symm_apply_apply]

private theorem extendCoefficientsCLM_apply_comp (hj : ∀ a, ‖j a‖ ≤ B) {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] [Fintype A] (q : C(X, A)) (g : A → K) :
    extendCoefficientsCLM j μ hj ((equivFnOfDiscrete.symm g).comp q) = cylinderSum j μ q g := by
  let φ : LocallyConstant X K :=
    ⟨g ∘ q, (IsLocallyConstant.of_discrete g).comp_continuous q.continuous⟩
  have hφ : (equivFnOfDiscrete.symm g).comp q = LocallyConstant.toContinuousMapLinearMap K φ := by
    ext
    simp [φ]
  rw [hφ, extendCoefficientsCLM_apply_test]
  exact locallyConstantIntegral_apply j μ φ q g fun _ ↦ rfl

private theorem finiteProjection_extendCoefficientsCLM (hj : ∀ a, ‖j a‖ ≤ B) {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] [Finite A] (q : C(X, A)) :
    finiteProjection q (toCLMEquiv.symm (extendCoefficientsCLM j μ hj)) =
      (finiteProjection q μ).mapRange j (map_zero j) := by
  classical
  let := Fintype.ofFinite A
  ext a
  have hfib : q.fiberIndicator (R := K) a =
      (equivFnOfDiscrete.symm fun b ↦ if b = a then 1 else 0).comp q := by
    ext
    simp [fiberIndicator_apply]
  rw [finiteProjection_apply, coe_symm_toCLMEquiv, hfib, extendCoefficientsCLM_apply_comp j μ hj,
    cylinderSum_ite, Finsupp.mapRange_apply]

/-- **Extension of coefficients along a bounded homomorphism.** If `j : O →+* K` is uniformly
bounded and `K` is a complete ultrametric normed ring, then `extendCoefficients j hj μ` is the
`K`-valued measure on the profinite space `X` whose coefficient on each fibre of a continuous map
to a finite discrete space is the image under `j` of the coefficient of `μ`
(`finiteProjection_extendCoefficients`). When `j` is continuous it is the unique `K`-valued measure
with `ι_j(μ)(j ∘ f) = j(μ(f))` for all `f ∈ C(X, O)` (`extendCoefficients_apply_comp`,
`eq_extendCoefficients_of_apply_comp`). -/
def extendCoefficients (hj : ∀ a, ‖j a‖ ≤ B) : D(X, O) →+ D(X, K) where
  toFun μ := toCLMEquiv.symm (extendCoefficientsCLM j μ hj)
  map_zero' := finiteProjection_ext _ _ fun q ↦ by
    rw [finiteProjection_extendCoefficientsCLM j 0 hj]
    simp
  map_add' μ ν := finiteProjection_ext _ _ fun q ↦ by
    simp only [map_add, finiteProjection_extendCoefficientsCLM]
    ext a
    simp

variable (hj : ∀ a, ‖j a‖ ≤ B)

private theorem toCLMEquiv_extendCoefficients :
    toCLMEquiv (extendCoefficients j hj μ) = extendCoefficientsCLM j μ hj :=
  toCLMEquiv.apply_symm_apply _

/-- The finite projections of `extendCoefficients j hj μ` are those of `μ`, with `j` applied to
the coefficients. -/
@[simp]
theorem finiteProjection_extendCoefficients {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] (q : C(X, A)) :
    finiteProjection q (extendCoefficients j hj μ) =
      (finiteProjection q μ).mapRange j (map_zero j) :=
  finiteProjection_extendCoefficientsCLM j μ hj q

/-- The coefficient extension depends only on `j`. A choice of uniform bound gives the same
additive map for every valid bound. -/
theorem extendCoefficients_eq_of_bound {B' : ℝ} (hj' : ∀ a, ‖j a‖ ≤ B') :
    extendCoefficients (X := X) j hj = extendCoefficients j hj' := by
  apply AddMonoidHom.ext
  intro μ
  apply finiteProjection_ext
  intro q
  simp only [finiteProjection_extendCoefficients]

/-- Integrating a function that factors through a finite discrete quotient against
`extendCoefficients j hj μ` is the finite sum of its values against the coefficients of `μ`
transported by `j`. -/
theorem extendCoefficients_apply_comp_eq_sum {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Fintype A] (q : C(X, A)) (g : A → K) :
    extendCoefficients j hj μ ((equivFnOfDiscrete.symm g).comp q) =
      ∑ a, g a * j (finiteProjection q μ a) := by
  rw [← coe_toCLMEquiv, toCLMEquiv_extendCoefficients, extendCoefficientsCLM_apply_comp j μ hj,
    cylinderSum]

/-- The integral of a continuous test is bounded by the uniform coefficient bound times its
supremum norm. -/
theorem norm_extendCoefficients_apply_le (f : C(X, K)) :
    ‖extendCoefficients j hj μ f‖ ≤ B * ‖f‖ := by
  rw [← coe_toCLMEquiv, toCLMEquiv_extendCoefficients]
  refine (LocallyConstant.denseRange_toContinuousMapLinearMap K).induction_on
    (p := fun g : C(X, K) ↦ ‖extendCoefficientsCLM j μ hj g‖ ≤ B * ‖g‖) f
    (isClosed_le ((extendCoefficientsCLM j μ hj).continuous.norm)
      (continuous_const.mul continuous_norm)) ?_
  intro φ
  rw [extendCoefficientsCLM_apply_test]
  exact norm_locallyConstantIntegral_le j μ hj φ

/-- Extension agrees with the coefficient homomorphism on locally constant source-valued tests,
without assuming that the coefficient homomorphism is continuous. -/
@[simp]
theorem extendCoefficients_apply_locallyConstant
    (f : LocallyConstant X O) :
    extendCoefficients j hj μ (f.map j) = j (μ f) := by
  classical
  let q : C(X, f.discreteQuotient) := ⟨_, f.discreteQuotient.proj_continuous⟩
  let := Fintype.ofFinite f.discreteQuotient
  have hf : (f : C(X, O)) = (equivFnOfDiscrete.symm f.lift).comp q := by
    ext x
    exact (congrFun f.lift_comp_proj x).symm
  have hjf : (f.map j : C(X, K)) =
      (equivFnOfDiscrete.symm (j ∘ f.lift)).comp q := by
    ext x
    exact congrArg j (congrFun f.lift_comp_proj x).symm
  rw [hjf, extendCoefficients_apply_comp_eq_sum, hf,
    apply_comp_eq_sum_finiteProjection, map_sum]
  simp

/-- Extension of coefficients is semilinear along `j`. -/
@[simp]
theorem extendCoefficients_smul (a : O) :
    extendCoefficients j hj (a • μ) = j a • extendCoefficients j hj μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext b
    simp

/-- Extension of coefficients sends Dirac measures to Dirac measures. -/
@[simp]
theorem extendCoefficients_dirac (x : X) :
    extendCoefficients j hj (dirac O x) = dirac K x :=
  finiteProjection_ext _ _ fun q ↦ by
    simp

/-- Extension of coefficients commutes with pushforward along continuous maps of profinite
spaces. -/
@[simp]
theorem extendCoefficients_map {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] (φ : C(X, Y)) :
    extendCoefficients j hj (map φ μ) = map φ (extendCoefficients j hj μ) :=
  finiteProjection_ext _ _ fun q ↦ by
    simp

/-- For continuous `j`, the extension of coefficients of `μ` integrates `j ∘ f` to `j (μ f)` for
every `f ∈ C(X, O)`. -/
theorem extendCoefficients_apply_comp (hjc : Continuous j) (f : C(X, O)) :
    extendCoefficients j hj μ ((⟨j, hjc⟩ : C(O, K)).comp f) = j (μ f) := by
  -- The density argument only needs the canonical uniformity of the additive group of `O`.
  let := IsTopologicalAddGroup.rightUniformSpace O
  refine congrFun (LocallyConstant.denseRange_toContinuousMap.equalizer
    ((map_continuous (extendCoefficients j hj μ)).comp (continuous_postcomp _))
    (hjc.comp (map_continuous μ)) (funext fun φ ↦ ?_)) f
  have hjφ : (⟨j, hjc⟩ : C(O, K)).comp φ = (φ.map j : C(X, K)) := by
    ext x
    rfl
  simpa only [Function.comp_apply, hjφ] using
    extendCoefficients_apply_locallyConstant j μ hj φ

/-- A `K`-valued measure taking the value `j (μ f)` on every test function `j ∘ f` is the extension
of coefficients of `μ`. -/
theorem eq_extendCoefficients_of_apply_comp (hjc : Continuous j) {ν : D(X, K)}
    (hν : ∀ f : C(X, O), ν ((⟨j, hjc⟩ : C(O, K)).comp f) = j (μ f)) :
    ν = extendCoefficients j hj μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext a
    rw [finiteProjection_extendCoefficients, Finsupp.mapRange_apply, finiteProjection_apply,
      finiteProjection_apply, ← hν]
    congr 1
    ext x
    classical
    by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]

omit [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [CompleteSpace K]
  [IsUltrametricDist K] in
private theorem exists_apply_comp_eq_of_mem_range (hje : Topology.IsEmbedding j) (ν : D(X, K))
    (hmem : ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) ∈ Set.range j) :
    ∃ μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f) := by
  let J : C(O, K) := ⟨j, hje.continuous⟩
  have hspec (f : C(X, O)) : j (hmem f).choose = ν (J.comp f) := (hmem f).choose_spec
  let L : C(X, O) →ₗ[O] O :=
    { toFun f := (hmem f).choose
      map_add' f g := hje.injective <| (hspec _).trans <| by
        have hJ : J.comp (f + g) = J.comp f + J.comp g := by
          ext
          simp [J]
        simp [hspec, hJ]
      map_smul' a f := hje.injective <| (hspec _).trans <| by
        have hJ : J.comp (a • f) = j a • J.comp f := by
          ext
          simp [J]
        simp [hspec, hJ] }
  have hLj (f : C(X, O)) : j (L f) = ν (J.comp f) := hspec f
  have hL : Continuous L := hje.continuous_iff.mpr <| by
    simpa only [Function.comp_def, hLj] using (map_continuous ν).comp (continuous_postcomp J)
  exact ⟨toCLMEquiv.symm ⟨L, hL⟩, fun f ↦ by
    rw [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', hLj]⟩

/-- Extension of coefficients along an injective `j` is injective. -/
theorem extendCoefficients_injective [T2Space O] (hinj : Function.Injective j) :
    Function.Injective (extendCoefficients (X := X) j hj) := fun μ ν h ↦
  finiteProjection_ext _ _ fun q ↦ by
    have := congrArg (finiteProjection q) h
    rw [finiteProjection_extendCoefficients, finiteProjection_extendCoefficients] at this
    exact Finsupp.mapRange_injective _ (map_zero j) hinj this

/-- Extension of coefficients is surjective when `j` is a surjective topological embedding. -/
theorem extendCoefficients_surjective (hje : Topology.IsEmbedding j)
    (hsurj : Function.Surjective j) : Function.Surjective (extendCoefficients (X := X) j hj) := by
  intro ν
  obtain ⟨μ, hμ⟩ := exists_apply_comp_eq_of_mem_range j hje ν fun _ ↦ hsurj _
  exact ⟨μ, (eq_extendCoefficients_of_apply_comp j μ hj hje.continuous hμ).symm⟩

/-- Extending coefficients along the identity preserves the measure. -/
@[simp]
theorem extendCoefficients_id (h : ∀ a : K, ‖a‖ ≤ B) (ν : D(X, K)) :
    extendCoefficients (RingHom.id K) h ν = ν := by
  apply finiteProjection_ext
  intro q
  ext a
  simp

end TopologicalRing

section OperatorNorm

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] {K O : Type*}
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CommRing O]
  [TopologicalSpace O] [IsTopologicalRing O] (j : O →+* K)

/-- The extension of coefficients has operator norm bounded by the uniform coefficient bound. -/
theorem norm_toCLMEquiv_extendCoefficients_le {B : ℝ} (hj : ∀ a, ‖j a‖ ≤ B) (μ : D(X, O)) :
    ‖toCLMEquiv (extendCoefficients j hj μ)‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hj 0)) fun f ↦ by
    rw [coe_toCLMEquiv]
    exact norm_extendCoefficients_apply_le j μ hj f

variable (hj : ∀ a, ‖j a‖ ≤ 1)
variable {j}

omit [T2Space X] [TotallyDisconnectedSpace X] [CompleteSpace K] in
include hj in
/-- If `j` is a topological embedding onto the closed unit ball of `K`, a `K`-valued measure `ν` of
norm at most `1` sends the test functions `j ∘ f` into the image of `j`, and the preimages form an
`O`-valued measure `μ` with `ν (j ∘ f) = j (μ f)`. -/
theorem exists_apply_comp_eq_of_norm_le_one (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) {ν : D(X, K)} (hν : ‖toCLMEquiv ν‖ ≤ 1) :
    ∃ μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f) := by
  let J : C(O, K) := ⟨j, hje.continuous⟩
  refine exists_apply_comp_eq_of_mem_range j hje ν fun f ↦ hjr ?_
  rw [mem_closedBall_zero_iff, ← coe_toCLMEquiv]
  have hf : ‖J.comp f‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x ↦ hj (f x)
  exact ((toCLMEquiv ν).le_of_opNorm_le_of_le hν hf).trans_eq (one_mul 1)

/-- **The dual unit ball.** If `j` is a topological embedding onto the closed unit ball of `K`,
the extensions of coefficients of `O`-valued measures are exactly the `K`-valued measures of
operator norm at most `1`. -/
theorem mem_range_extendCoefficients_iff (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) {ν : D(X, K)} :
    ν ∈ (extendCoefficients j hj).range ↔ ‖toCLMEquiv ν‖ ≤ 1 := by
  refine ⟨?_, fun hν ↦ ?_⟩
  · rintro ⟨μ, rfl⟩
    exact norm_toCLMEquiv_extendCoefficients_le j hj μ
  · obtain ⟨μ, hμ⟩ := exists_apply_comp_eq_of_norm_le_one hj hje hjr hν
    exact ⟨μ, (eq_extendCoefficients_of_apply_comp j μ hj hje.continuous hμ).symm⟩

omit [T2Space X] [TotallyDisconnectedSpace X] [CompleteSpace K] in
include hj in
/-- If `j` is a topological embedding onto the closed unit ball of `K`, a `K`-valued measure `ν`
has operator norm at most `1` exactly when there is a unique `O`-valued measure `μ` with
`ν (j ∘ f) = j (μ f)` for every `f ∈ C(X, O)`. -/
theorem existsUnique_apply_comp_eq_iff_norm_le_one (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) (ν : D(X, K)) :
    (∃! μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f)) ↔
      ‖toCLMEquiv ν‖ ≤ 1 := by
  refine ⟨fun ⟨μ, hμ, _⟩ ↦ ?_, fun hν ↦ ?_⟩
  · -- a test function of norm at most `1` factors through `j`, so `ν` does not increase it
    have hunit (g : C(X, K)) (hg : ‖g‖ ≤ 1) : ‖ν g‖ ≤ 1 := by
      have hmem (x : X) : g x ∈ Set.range j := hjr <| by
        rw [mem_closedBall_zero_iff]
        exact (ContinuousMap.norm_coe_le_norm g x).trans hg
      choose h hh using hmem
      have hcont : Continuous h := hje.continuous_iff.mpr <| by
        have : j ∘ h = g := funext hh
        rw [this]; exact g.continuous
      have hg' : g = (⟨j, hje.continuous⟩ : C(O, K)).comp ⟨h, hcont⟩ := by ext x; exact (hh x).symm
      rw [hg', hμ]
      exact hj _
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g ↦ ?_
    rw [coe_toCLMEquiv, one_mul]
    -- rescale by a value of `g` of maximal norm
    rcases isEmpty_or_nonempty X with hX | hX
    · have : g = 0 := Subsingleton.elim _ _
      simp [this]
    obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (continuous_norm.comp g.continuous).continuousOn
    have hgt : ‖g t‖ = ‖g‖ := le_antisymm (ContinuousMap.norm_coe_le_norm g t)
      ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ ht (Set.mem_univ x))
    rcases eq_or_ne (g t) 0 with h0 | h0
    · have : g = 0 := by
        rw [← norm_eq_zero, ← hgt, h0, norm_zero]
      simp [this]
    have hnorm : ‖(g t)⁻¹ • g‖ ≤ 1 := by
      rw [norm_smul, norm_inv, hgt, ← hgt]
      exact (inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)).le
    have := hunit _ hnorm
    rw [map_smul, smul_eq_mul, norm_mul, norm_inv] at this
    rw [← hgt]
    rwa [inv_mul_le_iff₀ (norm_pos_iff.2 h0), mul_one] at this
  · obtain ⟨μ, hμ⟩ := exists_apply_comp_eq_of_norm_le_one hj hje hjr hν
    exact ⟨μ, hμ, fun μ' hμ' ↦ ext fun f ↦ hje.injective ((hμ' f).symm.trans (hμ f))⟩

end OperatorNorm

section Examples

variable {p : ℕ} [Fact p.Prime]

/- The arithmetic case: coefficients extended from `ℤ_p` to `ℚ_p`. The extension of a Dirac measure
evaluates test functions at its point, and it does not forget multiplicities. -/

example (x : ℤ_[p]) (f : C(ℤ_[p], ℚ_[p])) :
    extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
      (dirac ℤ_[p] x) f = f x := by
  simp

example (x : ℤ_[p]) :
    extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
        (dirac ℤ_[p] x + dirac ℤ_[p] x) ≠
      extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
        (dirac ℤ_[p] x) := by
  intro h
  have := congrArg (fun ν : D(ℤ_[p], ℚ_[p]) ↦ ν 1) h
  norm_num at this

end Examples

end AbstractMeasure
