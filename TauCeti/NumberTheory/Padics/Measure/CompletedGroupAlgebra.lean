/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.FiniteAlgebra
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.ContinuousMap.LocallyConstant

/-!
# Measures on a compact group in its completed group algebra

For a compact topological group `Γ` and a topological commutative ring `R`, every open normal
subgroup `U` of `Γ` gives a finite discrete quotient `Γ ⧸ U`, and pushing a measure forward along
`Γ → Γ ⧸ U` gives its finite algebra projection in the group algebra `R[Γ ⧸ U]`. These projections
are compatible under the quotient maps `Γ ⧸ U → Γ ⧸ V` for `U ≤ V`, so they assemble, through the
universal property of the inverse limit, into an `R`-algebra homomorphism
`toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` from the convolution algebra of measures to the
completed group algebra. It sends the Dirac measure at `γ` to the group element `γ`.

The coefficients of the projection of `toCompletedGroupAlgebra μ` at level `U` are the measures of
the cosets of `U`, so integrating a function that factors through `Γ ⧸ U` is a finite sum against
them. When `Γ` is profinite such cylinder functions are dense, and hence the comparison map is
injective over every Hausdorff coefficient ring. For normed coefficients it is continuous from
the weak topology on measures to the inverse-limit topology on the completed group algebra.

## Main definitions

* `AbstractMeasure.toCompletedGroupAlgebra`: the `R`-algebra homomorphism
  `D(Γ, R) →ₐ[R] TauCeti.completedGroupAlgebra R Γ` whose projection to every level `R[Γ ⧸ U]` is
  the finite algebra projection along `Γ → Γ ⧸ U`.

## Main results

* `AbstractMeasure.toCompletedGroupAlgebra_dirac`: the Dirac measure at `γ` goes to `γ`.
* `AbstractMeasure.apply_eq_sum_coeff_proj_toCompletedGroupAlgebra`: integration of a function
  factoring through `Γ ⧸ U` is the finite sum of its values against the coefficients at level `U`.
* `AbstractMeasure.toCompletedGroupAlgebra_injective`: for profinite `Γ` and Hausdorff `R`, a
  measure is determined by its image in the completed group algebra.
* `AbstractMeasure.toCompletedGroupAlgebra_surjective`: every element of `ℤ_p[[Γ]]` is the image
  of a unique integral measure.
* `AbstractMeasure.completedGroupAlgebraEquiv`: the resulting `ℤ_p`-algebra equivalence between
  integral measures and the completed group algebra.
* `AbstractMeasure.continuous_toCompletedGroupAlgebra`: for normed `R`, the comparison map is
  continuous for the weak topology on measures.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.3,
  Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap TauCeti

namespace AbstractMeasure

variable {Γ R : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

section TopologicalRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The finite algebra projections of a measure along the quotient maps `Γ → Γ ⧸ U` are
compatible: for `U ≤ V`, pushing the projection at `U` forward along `Γ ⧸ U → Γ ⧸ V` gives the
projection at `V`. -/
theorem mapDomain_finiteProjectionAlgHom_quotientMk {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V)
    (μ : D(Γ, R)) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV)
        (U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ) =
      V.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ := by
  -- The quotient map at `V` is the quotient map at `U` followed by the transition map.
  have hq : (V.toSubgroup.quotientMkContinuousMonoidHom : C(Γ, Γ ⧸ V.toSubgroup)) =
      (⟨QuotientGroup.mapOfLE hUV, continuous_of_discreteTopology⟩ :
        C(Γ ⧸ U.toSubgroup, Γ ⧸ V.toSubgroup)).comp
        U.toSubgroup.quotientMkContinuousMonoidHom := by
    ext
    simp
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_mapDomain, ContinuousMonoidHom.finiteProjectionAlgHom_apply,
    ContinuousMonoidHom.finiteProjectionAlgHom_apply, MonoidAlgebra.coeff_ofCoeff,
    MonoidAlgebra.coeff_ofCoeff, hq, finiteProjection_comp]
  rfl

/-- **Measures in the completed group algebra.** The `R`-algebra homomorphism from measures on a
compact group `Γ` to its completed group algebra `R[[Γ]]` whose projection to every level
`R[Γ ⧸ U]` is the finite algebra projection along the quotient map `Γ → Γ ⧸ U`
(`proj_toCompletedGroupAlgebra`). -/
def toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ :=
  completedGroupAlgebra.lift R Γ
    (fun U ↦ U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom)
    fun _ _ hUV μ ↦ mapDomain_finiteProjectionAlgHom_quotientMk hUV μ

/-- The projection of `toCompletedGroupAlgebra μ` to the level `R[Γ ⧸ U]` is the finite algebra
projection of `μ` along the quotient map. -/
@[simp]
theorem proj_toCompletedGroupAlgebra (U : OpenNormalSubgroup Γ) (μ : D(Γ, R)) :
    completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra μ) =
      U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ :=
  completedGroupAlgebra.proj_lift ..

/-- The Dirac measure at `γ` goes to the group element `γ` of the completed group algebra. -/
@[simp]
theorem toCompletedGroupAlgebra_dirac (γ : Γ) :
    toCompletedGroupAlgebra (dirac R γ) = completedGroupAlgebra.of R Γ γ := by
  ext U
  simp

/-- Integrating a function that factors through `Γ ⧸ U` as `g` is the finite sum of the values
of `g` against the coefficients of the projection of `toCompletedGroupAlgebra μ` at level `U`,
which are the measures of the cosets of `U`. -/
theorem apply_eq_sum_coeff_proj_toCompletedGroupAlgebra {U : OpenNormalSubgroup Γ}
    [Fintype (Γ ⧸ U.toSubgroup)] (μ : D(Γ, R)) {F : C(Γ, R)} {g : Γ ⧸ U.toSubgroup → R}
    (hF : g ∘ (↑) = ⇑F) :
    μ F = ∑ a, g a * (completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra μ)).coeff a := by
  have hF' : F = (equivFnOfDiscrete.symm g).comp U.toSubgroup.quotientMkContinuousMonoidHom := by
    ext x
    simp [← hF]
  rw [hF', apply_comp_eq_sum_finiteProjection]
  simp

/-- **Injectivity of the comparison.** Over a Hausdorff coefficient ring, a measure on a
profinite group is determined by its image in the completed group algebra. -/
theorem toCompletedGroupAlgebra_injective [T2Space R] [TotallyDisconnectedSpace Γ] :
    Function.Injective (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) := by
  intro μ ν h
  -- The two measures agree on the dense set of functions factoring through a finite quotient.
  let := IsTopologicalAddGroup.rightUniformSpace R
  have hEqOn : Set.EqOn μ ν {F : C(Γ, R) |
      ∃ (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → R), g ∘ (↑) = F} := by
    rintro F ⟨U, g, hF⟩
    let _ := Fintype.ofFinite (Γ ⧸ U.toSubgroup)
    rw [apply_eq_sum_coeff_proj_toCompletedGroupAlgebra μ hF,
      apply_eq_sum_coeff_proj_toCompletedGroupAlgebra ν hF, h]
  exact AbstractMeasure.ext fun F ↦ congrFun
    (Continuous.ext_on (dense_setOf_comp_quotientMk R) μ.continuous ν.continuous hEqOn) F

end TopologicalRing

section Normed

variable [NormedCommRing R]

/-- The comparison map is continuous from the weak topology on measures to the inverse-limit
topology on the completed group algebra: each coefficient of each projection is the measure of
a coset, which depends continuously on the measure. -/
theorem continuous_toCompletedGroupAlgebra :
    @Continuous _ _ (WeakTopology (X := Γ) (R := R) (E := R)) _
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) := by
  let : TopologicalSpace D(Γ, R) := WeakTopology
  refine completedGroupAlgebra.continuous_iff.mpr fun U a ↦ ?_
  simp only [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff]
  exact (continuous_apply a).comp (continuous_finiteProjection _)

end Normed

section PadicInt

variable {p : ℕ} [Fact p.Prime] [TotallyDisconnectedSpace Γ]

private def completedCylinderSum (x : completedGroupAlgebra ℤ_[p] Γ)
    (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → ℤ_[p]) : ℤ_[p] :=
  (completedGroupAlgebra.proj ℤ_[p] Γ U x).coeff.sum fun a c ↦ g a * c

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
private theorem completedCylinderSum_mapOfLE (x : completedGroupAlgebra ℤ_[p] Γ)
    {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V) (g : Γ ⧸ V.toSubgroup → ℤ_[p]) :
    completedCylinderSum x V g =
      completedCylinderSum x U (g ∘ QuotientGroup.mapOfLE hUV) := by
  classical
  rw [completedCylinderSum, completedCylinderSum,
    ← completedGroupAlgebra.mapDomain_mapOfLE_proj hUV x]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [mul_add])

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
private theorem completedCylinderSum_eq_of_comp_eq (x : completedGroupAlgebra ℤ_[p] Γ)
    (U V : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → ℤ_[p])
    (h : Γ ⧸ V.toSubgroup → ℤ_[p])
    (hgh : ∀ y : Γ, g y = h y) :
    completedCylinderSum x U g = completedCylinderSum x V h := by
  rw [completedCylinderSum_mapOfLE x inf_le_left g,
    completedCylinderSum_mapOfLE x inf_le_right h]
  congr 1
  funext a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  simpa using hgh y

private noncomputable def completedLocallyConstantValue
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p]) : ℤ_[p] :=
  let hφ := φ.isLocallyConstant.exists_comp_quotientMk_eq
  completedCylinderSum x hφ.choose hφ.choose_spec.choose

omit [TotallyDisconnectedSpace Γ] in
private theorem completedLocallyConstantValue_eq
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p])
    (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → ℤ_[p])
    (hφ : ∀ y : Γ, g y = φ y) :
    completedLocallyConstantValue x φ = completedCylinderSum x U g := by
  apply completedCylinderSum_eq_of_comp_eq
  intro y
  exact (congrFun
    (φ.isLocallyConstant.exists_comp_quotientMk_eq.choose_spec.choose_spec) y).trans (hφ y).symm

private noncomputable def completedLocallyConstantIntegral
    (x : completedGroupAlgebra ℤ_[p] Γ) : LocallyConstant Γ ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p] where
  toFun := completedLocallyConstantValue x
  map_add' φ ψ := by
    let hφ := φ.isLocallyConstant.exists_comp_quotientMk_eq
    let hψ := ψ.isLocallyConstant.exists_comp_quotientMk_eq
    let U := hφ.choose ⊓ hψ.choose
    let gφ := hφ.choose_spec.choose ∘ QuotientGroup.mapOfLE (inf_le_left : U ≤ hφ.choose)
    let gψ := hψ.choose_spec.choose ∘ QuotientGroup.mapOfLE (inf_le_right : U ≤ hψ.choose)
    have hφU : ∀ y : Γ, gφ y = φ y := fun y ↦ by
      simpa [gφ, U] using congrFun hφ.choose_spec.choose_spec y
    have hψU : ∀ y : Γ, gψ y = ψ y := fun y ↦ by
      simpa [gψ, U] using congrFun hψ.choose_spec.choose_spec y
    have h_add_value : completedLocallyConstantValue x (φ + ψ) =
        completedCylinderSum x U (gφ + gψ) :=
      completedLocallyConstantValue_eq x _ U _ fun y ↦ by
        rw [Pi.add_apply, hφU, hψU]
        exact congrArg (fun f : C(Γ, ℤ_[p]) ↦ f y)
          (map_add (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) φ ψ) |>.symm
    rw [h_add_value,
      completedLocallyConstantValue_eq x φ U gφ hφU,
      completedLocallyConstantValue_eq x ψ U gψ hψU]
    simp [completedCylinderSum, add_mul]
  map_smul' c φ := by
    let hφ := φ.isLocallyConstant.exists_comp_quotientMk_eq
    let U := hφ.choose
    let g := hφ.choose_spec.choose
    have hφU : ∀ y : Γ, g y = φ y := fun y ↦ congrFun hφ.choose_spec.choose_spec y
    have h_smul_value : completedLocallyConstantValue x (c • φ) =
        completedCylinderSum x U (c • g) :=
      completedLocallyConstantValue_eq x _ U _ fun y ↦ by
        rw [Pi.smul_apply, hφU]
        exact congrArg (fun f : C(Γ, ℤ_[p]) ↦ f y)
          (map_smul (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) c φ) |>.symm
    rw [h_smul_value,
      completedLocallyConstantValue_eq x φ U g hφU]
    simp only [completedCylinderSum, Pi.smul_apply, smul_eq_mul]
    rw [Finsupp.mul_sum]
    congr 1
    funext a c'
    simp only [RingHom.id_apply, mul_assoc]

omit [TotallyDisconnectedSpace Γ] in
private theorem completedLocallyConstantIntegral_eq
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p])
    (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → ℤ_[p])
    (hφ : ∀ y : Γ, g y = φ y) :
    completedLocallyConstantIntegral x φ = completedCylinderSum x U g :=
  completedLocallyConstantValue_eq x φ U g hφ

omit [TotallyDisconnectedSpace Γ] in
private theorem norm_completedLocallyConstantIntegral_le
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p]) :
    ‖completedLocallyConstantIntegral x φ‖ ≤
      1 * ‖LocallyConstant.toContinuousMapLinearMap ℤ_[p] φ‖ := by
  let hφ := φ.isLocallyConstant.exists_comp_quotientMk_eq
  let U := hφ.choose
  let g := hφ.choose_spec.choose
  have hφU : ∀ y : Γ, g y = φ y := fun y ↦ congrFun hφ.choose_spec.choose_spec y
  rw [one_mul, completedLocallyConstantIntegral_eq x φ U g hφU]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun a ha ↦ ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  calc
    ‖g y * (completedGroupAlgebra.proj ℤ_[p] Γ U x).coeff y‖
        ≤ ‖g y‖ * 1 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ ≤ ‖LocallyConstant.toContinuousMapLinearMap ℤ_[p] φ‖ := by
      rw [mul_one, hφU]
      exact (LocallyConstant.toContinuousMapLinearMap ℤ_[p] φ).norm_coe_le_norm y

private abbrev completedLocallyConstantTests : Submodule ℤ_[p] C(Γ, ℤ_[p]) :=
  (LocallyConstant.toContinuousMapLinearMap ℤ_[p]).range

private theorem dense_completedLocallyConstantTests :
    DenseRange (completedLocallyConstantTests (Γ := Γ) (p := p)).subtype := by
  apply denseRange_subtype_val.mpr
  apply (dense_setOf_comp_quotientMk ℤ_[p]).mono
  rintro f ⟨U, g, hg⟩
  have hloc : IsLocallyConstant (f : Γ → ℤ_[p]) := by
    rw [← hg]
    exact (IsLocallyConstant.of_discrete g).comp_continuous QuotientGroup.continuous_mk
  exact ⟨⟨f, hloc⟩, rfl⟩

private def completedIntegralOnLocallyConstantTests
    (x : completedGroupAlgebra ℤ_[p] Γ) :
    completedLocallyConstantTests (Γ := Γ) (p := p) →L[ℤ_[p]] ℤ_[p] :=
  let e := LinearEquiv.ofInjective (LocallyConstant.toContinuousMapLinearMap ℤ_[p])
    LocallyConstant.toContinuousMap_injective
  ((completedLocallyConstantIntegral x).comp e.symm.toLinearMap).mkContinuous 1 (by
    intro f
    have he : (e.symm f).toContinuousMap = f.val := by
      simpa only [LocallyConstant.toContinuousMapLinearMap_apply] using
        LinearEquiv.ofInjective_symm_apply (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) f
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    calc
      ‖completedLocallyConstantIntegral x (e.symm f)‖ ≤
          1 * ‖LocallyConstant.toContinuousMapLinearMap ℤ_[p] (e.symm f)‖ :=
        norm_completedLocallyConstantIntegral_le x (e.symm f)
      _ = 1 * ‖f‖ := by
        rw [LocallyConstant.toContinuousMapLinearMap_apply, he, Submodule.norm_coe])

omit [TotallyDisconnectedSpace Γ] in
private theorem completedIntegralOnLocallyConstantTests_apply
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p]) :
    completedIntegralOnLocallyConstantTests x
        ⟨φ.toContinuousMap, ⟨φ, rfl⟩⟩ = completedLocallyConstantIntegral x φ := by
  let e : LocallyConstant Γ ℤ_[p] ≃ₗ[ℤ_[p]]
      completedLocallyConstantTests (Γ := Γ) (p := p) :=
    LinearEquiv.ofInjective (LocallyConstant.toContinuousMapLinearMap ℤ_[p])
      LocallyConstant.toContinuousMap_injective
  have he : (⟨φ.toContinuousMap, ⟨φ, rfl⟩⟩ :
      completedLocallyConstantTests (Γ := Γ) (p := p)) = e φ := by
    apply Subtype.ext
    exact (LinearEquiv.ofInjective_apply
      (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) φ).symm
  simp only [completedIntegralOnLocallyConstantTests, LinearMap.mkContinuous_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  exact congrArg (completedLocallyConstantIntegral x) (he ▸ e.symm_apply_apply φ)

private noncomputable def ofCompletedGroupAlgebra
    (x : completedGroupAlgebra ℤ_[p] Γ) : D(Γ, ℤ_[p]) :=
  toCLMEquiv.symm <| (completedIntegralOnLocallyConstantTests x).extend
    (completedLocallyConstantTests (Γ := Γ) (p := p)).subtypeL

private theorem ofCompletedGroupAlgebra_apply_locallyConstant
    (x : completedGroupAlgebra ℤ_[p] Γ) (φ : LocallyConstant Γ ℤ_[p]) :
    ofCompletedGroupAlgebra x φ.toContinuousMap = completedLocallyConstantIntegral x φ := by
  have he := (completedIntegralOnLocallyConstantTests x).extend_eq
    (e := (completedLocallyConstantTests (Γ := Γ) (p := p)).subtypeL)
    dense_completedLocallyConstantTests isUniformEmbedding_subtype_val.isUniformInducing
    ⟨φ.toContinuousMap, ⟨φ, rfl⟩⟩
  rw [ofCompletedGroupAlgebra, coe_symm_toCLMEquiv]
  exact he.trans (completedIntegralOnLocallyConstantTests_apply x φ)

private theorem ofCompletedGroupAlgebra_apply_comp
    (x : completedGroupAlgebra ℤ_[p] Γ) (U : OpenNormalSubgroup Γ)
    (g : Γ ⧸ U.toSubgroup → ℤ_[p]) :
    ofCompletedGroupAlgebra x
        ((ContinuousMap.equivFnOfDiscrete.symm g).comp
          U.toSubgroup.quotientMkContinuousMonoidHom) = completedCylinderSum x U g := by
  let φ : LocallyConstant Γ ℤ_[p] :=
    ⟨g ∘ (↑), (IsLocallyConstant.of_discrete g).comp_continuous
      QuotientGroup.continuous_mk⟩
  have hφ : (ContinuousMap.equivFnOfDiscrete.symm g).comp
      U.toSubgroup.quotientMkContinuousMonoidHom =
      LocallyConstant.toContinuousMapLinearMap ℤ_[p] φ := by
    ext
    simp [φ]
  rw [hφ, LocallyConstant.toContinuousMapLinearMap_apply,
    ofCompletedGroupAlgebra_apply_locallyConstant]
  exact completedLocallyConstantIntegral_eq x φ U g fun _ ↦ rfl

private theorem proj_toCompletedGroupAlgebra_ofCompletedGroupAlgebra
    (x : completedGroupAlgebra ℤ_[p] Γ) (U : OpenNormalSubgroup Γ) :
    completedGroupAlgebra.proj ℤ_[p] Γ U
        (toCompletedGroupAlgebra (ofCompletedGroupAlgebra x)) =
      completedGroupAlgebra.proj ℤ_[p] Γ U x := by
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  rw [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff,
    finiteProjection_apply]
  have hfib : (↑U.toSubgroup.quotientMkContinuousMonoidHom :
      C(Γ, Γ ⧸ U.toSubgroup)).fiberIndicator (R := ℤ_[p]) a =
      (ContinuousMap.equivFnOfDiscrete.symm fun b ↦ if b = a then 1 else 0).comp
        U.toSubgroup.quotientMkContinuousMonoidHom := by
    ext
    simp [fiberIndicator_apply]
  rw [hfib, ofCompletedGroupAlgebra_apply_comp]
  rw [completedCylinderSum]
  calc
    (completedGroupAlgebra.proj ℤ_[p] Γ U x).coeff.sum
        (fun b c ↦ (if b = a then 1 else 0) * c) =
        (if a = a then 1 else 0) *
          (completedGroupAlgebra.proj ℤ_[p] Γ U x).coeff a := by
      apply Finsupp.sum_eq_single a
      · intro b _ hba
        simp [hba]
      · simp
    _ = (completedGroupAlgebra.proj ℤ_[p] Γ U x).coeff a := by simp

/-- **Surjectivity of the measure comparison.** Every element of the completed group algebra
`ℤ_p[[Γ]]` of a profinite group is represented by an integral measure. -/
theorem toCompletedGroupAlgebra_surjective :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) := by
  intro x
  refine ⟨ofCompletedGroupAlgebra x, ?_⟩
  apply completedGroupAlgebra.ext
  intro U
  exact proj_toCompletedGroupAlgebra_ofCompletedGroupAlgebra x U

/-- **Integral measures are the completed group algebra.** The canonical algebra equivalence
between integral measures on a profinite group and its completed group algebra. -/
noncomputable def completedGroupAlgebraEquiv :
    D(Γ, ℤ_[p]) ≃ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective⟩

/-- The integral-measure equivalence has `toCompletedGroupAlgebra` as its forward map. -/
@[simp]
theorem completedGroupAlgebraEquiv_apply (μ : D(Γ, ℤ_[p])) :
    completedGroupAlgebraEquiv μ = toCompletedGroupAlgebra μ :=
  AlgEquiv.ofBijective_apply _ _ _

end PadicInt

/-! The comparison on products of Dirac measures, and on distinct points of a profinite group. -/

example [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (x y : Γ)
    (U : OpenNormalSubgroup Γ) :
    completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra (dirac R x * dirac R y)) =
      MonoidAlgebra.single ((x * y : Γ) : Γ ⧸ U.toSubgroup) 1 := by
  simp [dirac_mul_dirac]

example [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Nontrivial R]
    [TotallyDisconnectedSpace Γ] {x y : Γ} (hxy : x ≠ y) :
    toCompletedGroupAlgebra (dirac R x) ≠ toCompletedGroupAlgebra (dirac R y) := by
  simpa using (completedGroupAlgebra.of_injective R Γ).ne hxy

end AbstractMeasure
