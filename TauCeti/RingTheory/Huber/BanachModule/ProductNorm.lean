/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm
import Mathlib.Analysis.Normed.Group.Completion

/-!
# The completed nonarchimedean product seminorm and norm

Whenever the nonarchimedean product seminorm `TauCeti.Huber.BanachModule.productSeminorm A V W`
from `TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm` is uniformly continuous for
`banachTensorUniformSpace A V W`, extending it across `CompletedTensor.toCompletion` yields the
additive group seminorm
`TauCeti.Huber.BanachModule.CompletedTensor.productSeminormOfUniformContinuous`, specialised under
a contractive scalar action on `V` to
`TauCeti.Huber.BanachModule.CompletedTensor.productSeminorm A V W`.

When `A` is Tate (`TauCeti.NormedRing.IsTate A`) and both scalar actions are bounded, this
extension separates points (`productSeminorm_eq_zero_iff`), its positive-radius balls form a
neighbourhood basis of `0` on `V ⊗̂_A W` (`hasBasis_nhds_zero_productSeminorm`), and `productNorm`
/ `productNormedAddCommGroup` (together with `productNormOfNormSmulLe` /
`productNormedAddCommGroupOfNormSmulLe` for non-contractive bounded actions) bundle it as a
compatible `AddGroupNorm` and `NormedAddCommGroup` retaining the completion uniformity
definitionally (following the pattern of `TauCeti.Huber.tateNorm`, `TauCeti.Huber.tateRingNorm`
and `TauCeti.Huber.tateNormedCommRing`).

Over a complete nontrivially normed field `L`, for ultrametric normed `L`-spaces `V` and `W`,
definiteness of `BanachModule.productSeminorm L V W` implies that
`toCompletion L V W : V ⊗[L] W → V ⊗̂_L W` is injective (`CompletedTensor.toCompletion_injective`),
`CompletedTensor.productNorm L V W` is a cross norm on elementary tensors
(`CompletedTensor.productNorm_tmul`), and tensoring with a unit vector `w` preserves distances
(`CompletedTensor.productNorm_unitVector`).

## Main definitions

* `TauCeti.Huber.BanachModule.CompletedTensor.productSeminormOfUniformContinuous`: the continuous
  extension of `productSeminorm A V W` to `CompletedTensor A V W` from uniform continuity, as an
  `AddGroupSeminorm`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productSeminorm A V W`:
  `productSeminormOfUniformContinuous` for a contractive scalar action on `V`, as an
  `AddGroupSeminorm`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormOfNormSmulLe` and `productNorm`: the
  completed product norm bundled as a definite `AddGroupNorm` over a Tate ring with bounded scalar
  actions.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormedAddCommGroupOfNormSmulLe` and
  `productNormedAddCommGroup`: the compatible `NormedAddCommGroup` structure on
  `CompletedTensor A V W` retaining its uniformity definitionally.

## Main results

* `TauCeti.Huber.BanachModule.CompletedTensor.productSeminormOfUniformContinuous_toCompletion`,
  `productSeminorm_toCompletion`, `productSeminorm_add_le_max`, `productSeminorm_smul`,
  `hasBasis_nhds_zero_productSeminorm`, `productSeminorm_eq_zero_iff`,
  `hasBasis_nhds_zero_productNorm`: structure of the completed product seminorm and norm.
* `TauCeti.Huber.BanachModule.CompletedTensor.toCompletion_injective`, `productSeminorm_tmul`,
  `productNorm_tmul`, `productNorm_unitVector`: injectivity of `toCompletion` and cross-norm
  property over a complete nontrivially normed field.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.9(a).
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §2.1.7.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge University Press, 2010, §10.1.
-/

public section

open Filter TensorProduct Topology UniformSpace
open scoped NNReal Uniformity

namespace TauCeti.Huber

namespace BanachModule

namespace CompletedTensor

/-- The uniformity of the tensor topology, registered locally on the algebraic tensor product. -/
noncomputable local instance tensorUniformSpace {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    UniformSpace (V ⊗[A] W) :=
  banachTensorUniformSpace A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    IsUniformAddGroup (V ⊗[A] W) :=
  isUniformAddGroup_banachTensorUniformSpace A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    ContinuousSMul A (V ⊗[A] W) := by
  rw [banachTensorUniformSpace_toTopologicalSpace]
  exact continuousSMul_banachTensorTopology A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    UniformContinuousConstSMul A (V ⊗[A] W) :=
  uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)

section Extension

variable {A V W : Type*} [CommRing A] [TopologicalSpace A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

private theorem extension_toCompletion
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance] (productSeminorm A V W))
    (u : V ⊗[A] W) :
    (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W)
        (toCompletion A V W u) =
      productSeminorm A V W u := by
  simp only [Function.comp_apply, equivCompletion_toCompletion]
  exact Completion.extension_coe h u

private theorem continuous_extension_comp :
    Continuous (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) :=
  (Completion.uniformContinuous_extension.comp
    (equivCompletion A V W).toContinuousLinearMap.uniformContinuous).continuous

private theorem extension_nonneg
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance] (productSeminorm A V W))
    (z : CompletedTensor A V W) :
    0 ≤ (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le continuous_const continuous_extension_comp) fun u ↦ by
      rw [extension_toCompletion h]
      exact apply_nonneg _ u

private theorem extension_zero
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (productSeminorm A V W)) :
    (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) 0 = 0 := by
  simpa using extension_toCompletion h (0 : V ⊗[A] W)

private theorem extension_neg
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance] (productSeminorm A V W))
    (z : CompletedTensor A V W) :
    (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) (-z) =
      (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_extension_comp.comp continuous_neg) continuous_extension_comp)
    fun u ↦ by
      rw [← map_neg, extension_toCompletion h, extension_toCompletion h, map_neg_eq_map]

private theorem extension_add_le_max
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance] (productSeminorm A V W))
    (z₁ z₂ : CompletedTensor A V W) :
    (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) (z₁ + z₂) ≤
      max ((Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z₁)
        ((Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z₂) := by
  refine (denseRange_toCompletion A V W).induction_on₂
    (p := fun z₁ z₂ ↦
      (Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) (z₁ + z₂) ≤
        max ((Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z₁)
          ((Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W) z₂))
    ?_ (fun u₁ u₂ ↦ ?_) z₁ z₂
  · exact isClosed_le (continuous_extension_comp.comp continuous_add)
      ((continuous_extension_comp.comp continuous_fst).max
        (continuous_extension_comp.comp continuous_snd))
  · rw [← map_add, extension_toCompletion h, extension_toCompletion h, extension_toCompletion h]
    exact productSeminorm_add_le_max u₁ u₂

section OfUniformContinuous

variable (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
  (productSeminorm A V W))

/-- **The completed product seminorm from uniform continuity**: when `productSeminorm A V W` is
uniformly continuous for `banachTensorUniformSpace A V W`, its continuous extension across
`CompletedTensor.toCompletion` is an additive group seminorm on `CompletedTensor A V W`. -/
noncomputable def productSeminormOfUniformContinuous :
    AddGroupSeminorm (CompletedTensor A V W) where
  toFun := Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W
  map_zero' := extension_zero h
  add_le' z₁ z₂ := (extension_add_le_max h z₁ z₂).trans <|
    max_le_add_of_nonneg (extension_nonneg h z₁) (extension_nonneg h z₂)
  neg' := extension_neg h

/-- Evaluation of `productSeminormOfUniformContinuous h` via `UniformSpace.Completion.extension`
and `CompletedTensor.equivCompletion`. -/
theorem productSeminormOfUniformContinuous_apply (z : CompletedTensor A V W) :
    productSeminormOfUniformContinuous h z =
      @Completion.extension (V ⊗[A] W) (banachTensorUniformSpace A V W) ℝ _
        (productSeminorm A V W) (equivCompletion A V W z) := (rfl)

/-- `productSeminormOfUniformContinuous h` extends `productSeminorm A V W` across
`toCompletion`. -/
@[simp]
theorem productSeminormOfUniformContinuous_toCompletion (u : V ⊗[A] W) :
    productSeminormOfUniformContinuous h (toCompletion A V W u) = productSeminorm A V W u :=
  extension_toCompletion h u

/-- `productSeminormOfUniformContinuous h` is uniformly continuous. -/
theorem uniformContinuous_productSeminormOfUniformContinuous :
    UniformContinuous (productSeminormOfUniformContinuous h) :=
  Completion.uniformContinuous_extension.comp
    (equivCompletion A V W).toContinuousLinearMap.uniformContinuous

/-- `productSeminormOfUniformContinuous h` is continuous. -/
theorem continuous_productSeminormOfUniformContinuous :
    Continuous (productSeminormOfUniformContinuous h) :=
  (uniformContinuous_productSeminormOfUniformContinuous h).continuous

/-- **Ultrametric inequality** for `productSeminormOfUniformContinuous`. -/
theorem productSeminormOfUniformContinuous_add_le_max (z₁ z₂ : CompletedTensor A V W) :
    productSeminormOfUniformContinuous h (z₁ + z₂) ≤
      max (productSeminormOfUniformContinuous h z₁) (productSeminormOfUniformContinuous h z₂) :=
  extension_add_le_max h z₁ z₂

/-- `productSeminormOfUniformContinuous h` is a nonarchimedean additive group seminorm. -/
theorem isNonarchimedean_productSeminormOfUniformContinuous :
    IsNonarchimedean (productSeminormOfUniformContinuous h) :=
  productSeminormOfUniformContinuous_add_le_max h

/-- Ultrametric bound for differences under `productSeminormOfUniformContinuous`. -/
theorem productSeminormOfUniformContinuous_sub_le_max (z₁ z₂ : CompletedTensor A V W) :
    productSeminormOfUniformContinuous h (z₁ - z₂) ≤
      max (productSeminormOfUniformContinuous h z₁) (productSeminormOfUniformContinuous h z₂) := by
  simpa [sub_eq_add_neg] using productSeminormOfUniformContinuous_add_le_max h z₁ (-z₂)

/-- Elementary-tensor bound for `productSeminormOfUniformContinuous`. -/
theorem productSeminormOfUniformContinuous_tmul_le (v : V) (w : W) :
    productSeminormOfUniformContinuous h (tmul A V W v w) ≤ ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productSeminormOfUniformContinuous_toCompletion]
  exact productSeminorm_tmul_le v w

/-- **Universal bound on the completion.** For an `A`-bilinear map `β : V →ₗ[A] W →ₗ[A] M` into a
complete ultrametric normed `A`-module with continuous action, bounded by `C * ‖v‖ * ‖w‖`
(`0 ≤ C`), the induced map `lift β` satisfies
`‖lift β _ z‖ ≤ C * productSeminormOfUniformContinuous h z`. -/
theorem norm_lift_le_mul_productSeminormOfUniformContinuous
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productSeminormOfUniformContinuous h z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_norm.comp (lift β hβ).continuous)
      (continuous_const.mul (continuous_productSeminormOfUniformContinuous h))) fun u ↦ by
      rw [lift_toCompletion, productSeminormOfUniformContinuous_toCompletion]
      exact norm_lift_le_mul_productSeminorm β hC hb u

end OfUniformContinuous

/-- Functoriality bound for `productSeminormOfUniformContinuous` under bounded continuous
`A`-linear maps. -/
theorem productSeminormOfUniformContinuous_map_le [IsTopologicalRing A] {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [SeminormedAddCommGroup W'] [Module A W']
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance] (productSeminorm A V W))
    (h' : UniformContinuous[banachTensorUniformSpace A V' W', inferInstance]
      (productSeminorm A V' W'))
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hC₂ : 0 ≤ C₂) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productSeminormOfUniformContinuous h' (map f g z) ≤
      C₁ * C₂ * productSeminormOfUniformContinuous h z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productSeminormOfUniformContinuous h').comp (map f g).continuous)
      (continuous_const.mul (continuous_productSeminormOfUniformContinuous h))) fun u ↦ by
      rw [map_toCompletion, productSeminormOfUniformContinuous_toCompletion,
        productSeminormOfUniformContinuous_toCompletion]
      exact productSeminorm_map_le f.toLinearMap g.toLinearMap hC₁ hf hC₂ hg u

/-- Whenever `banachTensorUniformSpace A V W` coincides with the uniformity of
`productSeminorm A V W`, the positive-radius open balls of `productSeminormOfUniformContinuous h`
form a neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productSeminormOfUniformContinuous
    (hu : banachTensorUniformSpace A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace)
    {h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (productSeminorm A V W)} :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productSeminormOfUniformContinuous h z < r}) := by
  have hb_gen : ∀ (u : UniformSpace (V ⊗[A] W)),
      u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace →
      (@nhds (@Completion (V ⊗[A] W) u)
          (@UniformSpace.toTopologicalSpace _ (@Completion.uniformSpace _ u))
          (@Completion.coe' (V ⊗[A] W) u 0)).HasBasis (0 < ·)
        (fun r ↦ {z | @Completion.extension (V ⊗[A] W) u ℝ _ (productSeminorm A V W) z < r}) := by
    rintro _ rfl
    let _ : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
    exact NormedAddGroup.nhds_zero_basis_norm_lt
  have hb := hb_gen (banachTensorUniformSpace A V W) hu
  have heq : 𝓝 (0 : CompletedTensor A V W) =
      Filter.comap (equivCompletion A V W) (𝓝 (0 : Completion (V ⊗[A] W))) := by
    simpa using (equivCompletion A V W).toHomeomorph.isInducing.nhds_eq_comap 0
  rw [heq]
  exact hb.comap (equivCompletion A V W)

/-- Whenever `banachTensorUniformSpace A V W` coincides with the uniformity of
`productSeminorm A V W`, `productSeminormOfUniformContinuous h` vanishes only at `0`. -/
theorem productSeminormOfUniformContinuous_eq_zero_iff
    (hu : banachTensorUniformSpace A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace)
    {h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (productSeminorm A V W)}
    {z : CompletedTensor A V W} :
    productSeminormOfUniformContinuous h z = 0 ↔ z = 0 := by
  have hdef_gen : ∀ (u : UniformSpace (V ⊗[A] W)),
      u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace →
      ∀ w : @Completion (V ⊗[A] W) u,
        @Completion.extension (V ⊗[A] W) u ℝ _ (productSeminorm A V W) w = 0 ↔
          w = @Completion.coe' (V ⊗[A] W) u 0 := by
    rintro _ rfl
    let inst : SeminormedAddCommGroup (V ⊗[A] W) :=
      (productSeminorm A V W).toSeminormedAddCommGroup
    exact fun w ↦ @norm_eq_zero (@Completion (V ⊗[A] W) inst.toUniformSpace) inferInstance w
  have hdef := hdef_gen (banachTensorUniformSpace A V W) hu (equivCompletion A V W z)
  rw [productSeminormOfUniformContinuous_apply]
  simpa only [UniformSpace.Completion.coe_zero,
    map_eq_zero_iff _ (equivCompletion A V W).injective] using hdef

end Extension

section SeminormedRing

variable {A V W : Type*} [SeminormedCommRing A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- Scalar-action bound for `productSeminormOfUniformContinuous` under
`‖a • v‖ ≤ C * ‖a‖ * ‖v‖`. -/
theorem productSeminormOfUniformContinuous_smul_le_of_norm_smul_le {C : ℝ≥0}
    (hV : ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (BanachModule.productSeminorm A V W)}
    (a : A) (z : CompletedTensor A V W) :
    productSeminormOfUniformContinuous h (a • z) ≤
      C * ‖a‖ * productSeminormOfUniformContinuous h z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productSeminormOfUniformContinuous h).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productSeminormOfUniformContinuous h))) fun u ↦ by
      rw [← map_smul, productSeminormOfUniformContinuous_toCompletion,
        productSeminormOfUniformContinuous_toCompletion]
      exact BanachModule.productSeminorm_smul_le_of_norm_smul_le hV a u

variable (A V W) in
/-- **The completed product seminorm** on `V ⊗̂_A W` under a contractive scalar action on `V`: the
continuous extension of `BanachModule.productSeminorm A V W` across `CompletedTensor.toCompletion`,
as an additive group seminorm. -/
noncomputable def productSeminorm [IsBoundedSMul A V] :
    AddGroupSeminorm (CompletedTensor A V W) :=
  productSeminormOfUniformContinuous Huber.uniformContinuous_productSeminorm

/-- `CompletedTensor.productSeminorm A V W` agrees with `productSeminormOfUniformContinuous h` for
any uniform-continuity witness `h`. -/
theorem productSeminorm_eq_productSeminormOfUniformContinuous [IsBoundedSMul A V]
    (h : UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (BanachModule.productSeminorm A V W)) :
    productSeminorm A V W = productSeminormOfUniformContinuous h :=
  (rfl)

/-- On the image of `V ⊗[A] W`, `CompletedTensor.productSeminorm` agrees with
`BanachModule.productSeminorm`. -/
@[simp]
theorem productSeminorm_toCompletion [IsBoundedSMul A V] (u : V ⊗[A] W) :
    productSeminorm A V W (toCompletion A V W u) = BanachModule.productSeminorm A V W u :=
  productSeminormOfUniformContinuous_toCompletion _ u

/-- `CompletedTensor.productSeminorm A V W` is uniformly continuous. -/
theorem uniformContinuous_productSeminorm [IsBoundedSMul A V] :
    UniformContinuous (productSeminorm A V W) :=
  uniformContinuous_productSeminormOfUniformContinuous _

/-- `CompletedTensor.productSeminorm A V W` is continuous. -/
theorem continuous_productSeminorm [IsBoundedSMul A V] : Continuous (productSeminorm A V W) :=
  continuous_productSeminormOfUniformContinuous _

/-- **Ultrametric inequality** for `CompletedTensor.productSeminorm`. -/
theorem productSeminorm_add_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productSeminorm A V W (z₁ + z₂) ≤ max (productSeminorm A V W z₁) (productSeminorm A V W z₂) :=
  productSeminormOfUniformContinuous_add_le_max _ z₁ z₂

/-- `CompletedTensor.productSeminorm A V W` is a nonarchimedean additive group seminorm. -/
theorem isNonarchimedean_productSeminorm [IsBoundedSMul A V] :
    IsNonarchimedean (productSeminorm A V W) :=
  isNonarchimedean_productSeminormOfUniformContinuous _

/-- Ultrametric bound for differences under `CompletedTensor.productSeminorm`. -/
theorem productSeminorm_sub_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productSeminorm A V W (z₁ - z₂) ≤ max (productSeminorm A V W z₁) (productSeminorm A V W z₂) :=
  productSeminormOfUniformContinuous_sub_le_max _ z₁ z₂

/-- Elementary-tensor bound for `CompletedTensor.productSeminorm`. -/
theorem productSeminorm_tmul_le [IsBoundedSMul A V] (v : V) (w : W) :
    productSeminorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ :=
  productSeminormOfUniformContinuous_tmul_le _ v w

/-- Scalar-action bound for `CompletedTensor.productSeminorm` under a contractive scalar action on
`V`. -/
theorem productSeminorm_smul_le [IsBoundedSMul A V] (a : A) (z : CompletedTensor A V W) :
    productSeminorm A V W (a • z) ≤ ‖a‖ * productSeminorm A V W z := by
  simpa [productSeminorm] using
    productSeminormOfUniformContinuous_smul_le_of_norm_smul_le (C := 1)
      (h := Huber.uniformContinuous_productSeminorm)
      (fun r v ↦ by simpa using norm_smul_le r v) a z

/-- **Universal bound on the completion** under a contractive scalar action on `V`. -/
theorem norm_lift_le_mul_productSeminorm [IsBoundedSMul A V]
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productSeminorm A V W z :=
  norm_lift_le_mul_productSeminormOfUniformContinuous _ β hβ hC h z

/-- Functoriality bound for `CompletedTensor.productSeminorm` under contractive scalar actions on
`V` and `V'`. -/
theorem productSeminorm_map_le {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [IsBoundedSMul A V']
    [SeminormedAddCommGroup W'] [Module A W'] [IsBoundedSMul A V]
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hC₂ : 0 ≤ C₂) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productSeminorm A V' W' (map f g z) ≤ C₁ * C₂ * productSeminorm A V W z :=
  productSeminormOfUniformContinuous_map_le _ _ f g hC₁ hf hC₂ hg z

/-- On `A ⊗̂_A M` with `‖1‖ = 1` and complete ultrametric normed `M` with contractive `A`-action,
`CompletedTensor.productSeminorm` is the norm of the image under `CompletedTensor.lid A M`. -/
@[simp]
theorem productSeminorm_eq_norm_lid [NormOneClass A] [IsBoundedSMul A A]
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [IsBoundedSMul A M] (z : CompletedTensor A A M) :
    productSeminorm A A M z = ‖lid A M z‖ :=
  (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq continuous_productSeminorm (continuous_norm.comp (lid A M).continuous)) fun u ↦ by
      rw [productSeminorm_toCompletion, lid_toCompletion, BanachModule.productSeminorm_eq_norm_lid]

end SeminormedRing

section NormedField

variable {L V W : Type*} [NormedField L]
  [SeminormedAddCommGroup V] [NormedSpace L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Over a normed field, `CompletedTensor.productSeminorm` is homogeneous under scalar
multiplication. -/
@[simp]
theorem productSeminorm_smul (a : L) (z : CompletedTensor L V W) :
    productSeminorm L V W (a • z) = ‖a‖ * productSeminorm L V W z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine (productSeminorm_smul_le a z).antisymm ?_
    calc ‖a‖ * productSeminorm L V W z
        = ‖a‖ * productSeminorm L V W (a⁻¹ • a • z) := by rw [inv_smul_smul₀ ha]
      _ ≤ ‖a‖ * (‖a⁻¹‖ * productSeminorm L V W (a • z)) :=
          mul_le_mul_of_nonneg_left (productSeminorm_smul_le a⁻¹ (a • z)) (norm_nonneg a)
      _ = productSeminorm L V W (a • z) := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

end NormedField

section IsTate

variable {A V W : Type*} [SeminormedCommRing A] [NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- **Neighbourhood basis on the completion.** Over a Tate seminormed commutative ring `A` with
contractive action on `V` and bounded action on `W`, the positive-radius open balls of
`CompletedTensor.productSeminorm A V W` form a neighbourhood basis of `0` in
`CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productSeminorm_of_norm_smul_le [IsBoundedSMul A V]
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productSeminorm A V W z < r}) :=
  hasBasis_nhds_zero_productSeminormOfUniformContinuous
    (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le
      ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ hW)

variable (A V W) in
/-- **Neighbourhood basis on the completion** for `CompletedTensor.productSeminorm` under
contractive scalar actions. -/
theorem hasBasis_nhds_zero_productSeminorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productSeminorm A V W z < r}) :=
  hasBasis_nhds_zero_productSeminorm_of_norm_smul_le
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- **Definiteness of `CompletedTensor.productSeminorm`** over a Tate seminormed commutative ring
with contractive action on `V` and bounded action on `W`. -/
theorem productSeminorm_eq_zero_iff_of_norm_smul_le [IsBoundedSMul A V]
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {z : CompletedTensor A V W} :
    productSeminorm A V W z = 0 ↔ z = 0 :=
  productSeminormOfUniformContinuous_eq_zero_iff
    (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le
      ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ hW)

/-- **Definiteness of `CompletedTensor.productSeminorm`** under contractive scalar actions. -/
@[simp]
theorem productSeminorm_eq_zero_iff [IsBoundedSMul A V] [IsBoundedSMul A W]
    {z : CompletedTensor A V W} :
    productSeminorm A V W z = 0 ↔ z = 0 :=
  productSeminorm_eq_zero_iff_of_norm_smul_le ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

section Bounded

variable (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
  (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)

/-- **The completed product norm** bundled as an `AddGroupNorm` under bounded scalar actions over a
Tate seminormed commutative ring. -/
noncomputable def productNormOfNormSmulLe : AddGroupNorm (CompletedTensor A V W) :=
  { productSeminormOfUniformContinuous (uniformContinuous_productSeminorm_of_norm_smul_le hV) with
    eq_zero_of_map_eq_zero' := fun _ hz ↦
      (productSeminormOfUniformContinuous_eq_zero_iff
        (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le hV hW)).mp hz }

/-- Evaluation of `productNormOfNormSmulLe`. -/
@[simp]
theorem productNormOfNormSmulLe_apply (z : CompletedTensor A V W) :
    productNormOfNormSmulLe hV hW z =
      productSeminormOfUniformContinuous
        (uniformContinuous_productSeminorm_of_norm_smul_le hV) z := (rfl)

/-- The uniformity of `CompletedTensor A V W` coincides with that induced by
`productNormOfNormSmulLe`. -/
theorem uniformity_eq_productNormOfNormSmulLe :
    𝓤 (CompletedTensor A V W) =
      @uniformity _
        (productNormOfNormSmulLe hV hW).toNormedAddCommGroup.toUniformSpace := by
  let N := productNormOfNormSmulLe hV hW
  let u₁ : UniformSpace (CompletedTensor A V W) := inferInstance
  have hu₁ : @IsUniformAddGroup (CompletedTensor A V W) u₁ _ := inferInstance
  have hb₁ : (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·) (fun r ↦ {z | N z < r}) :=
    hasBasis_nhds_zero_productSeminormOfUniformContinuous
      (h := uniformContinuous_productSeminorm_of_norm_smul_le hV)
      (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le hV hW)
  let _ : NormedAddCommGroup (CompletedTensor A V W) := N.toNormedAddCommGroup
  have hu : u₁ = N.toNormedAddCommGroup.toUniformSpace :=
    IsUniformAddGroup.ext hu₁ inferInstance
      (hb₁.eq_of_same_basis NormedAddGroup.nhds_zero_basis_norm_lt)
  exact congrArg (fun u ↦ @uniformity _ u) hu

/-- Compatible `NormedAddCommGroup` structure on `CompletedTensor A V W` under bounded scalar
actions, retaining its additive group, uniformity and topology definitionally. -/
noncomputable abbrev productNormedAddCommGroupOfNormSmulLe :
    NormedAddCommGroup (CompletedTensor A V W) :=
  let N := productNormOfNormSmulLe hV hW
  { N.toNormedAddCommGroup with
    toMetricSpace := N.toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (uniformity_eq_productNormOfNormSmulLe hV hW) }

/-- The norm of `productNormedAddCommGroupOfNormSmulLe` is
`productSeminormOfUniformContinuous`. -/
@[simp]
theorem norm_productNormedAddCommGroupOfNormSmulLe (z : CompletedTensor A V W) :
    @norm _ (productNormedAddCommGroupOfNormSmulLe hV hW).toNorm z =
      productSeminormOfUniformContinuous
        (uniformContinuous_productSeminorm_of_norm_smul_le hV) z := (rfl)

/-- `productNormedAddCommGroupOfNormSmulLe` retains the completion uniformity. -/
@[simp]
theorem uniformSpace_productNormedAddCommGroupOfNormSmulLe :
    (productNormedAddCommGroupOfNormSmulLe hV hW).toUniformSpace =
      (inferInstance : UniformSpace (CompletedTensor A V W)) := (rfl)

/-- `productNormedAddCommGroupOfNormSmulLe` defines an ultrametric distance. -/
theorem isUltrametricDist_productNormedAddCommGroupOfNormSmulLe :
    letI := productNormedAddCommGroupOfNormSmulLe hV hW
    IsUltrametricDist (CompletedTensor A V W) := by
  have h := isNonarchimedean_productSeminormOfUniformContinuous
    (W := W) (uniformContinuous_productSeminorm_of_norm_smul_le hV)
  let := productNormedAddCommGroupOfNormSmulLe hV hW
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h

end Bounded

section Contractive

variable [IsBoundedSMul A V] [IsBoundedSMul A W]

variable (A V W) in
/-- **The completed product norm** on `V ⊗̂_A W` bundled as an `AddGroupNorm` under contractive
scalar actions over a Tate seminormed commutative ring. -/
noncomputable def productNorm : AddGroupNorm (CompletedTensor A V W) :=
  productNormOfNormSmulLe
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- Evaluation of `productNorm`. -/
@[simp]
theorem productNorm_apply (z : CompletedTensor A V W) :
    productNorm A V W z = productSeminorm A V W z := (rfl)

variable (A V W) in
/-- **Neighbourhood basis on the completion** for `productNorm` under contractive scalar
actions. -/
theorem hasBasis_nhds_zero_productNorm :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productNorm A V W z < r}) :=
  hasBasis_nhds_zero_productSeminorm A V W

variable (A V W) in
/-- The uniformity of `CompletedTensor A V W` coincides with that induced by `productNorm` under
contractive scalar actions. -/
theorem uniformity_eq_productNorm :
    𝓤 (CompletedTensor A V W) =
      @uniformity _ (productNorm A V W).toNormedAddCommGroup.toUniformSpace :=
  uniformity_eq_productNormOfNormSmulLe
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

variable (A V W) in
/-- Compatible `NormedAddCommGroup` structure on `CompletedTensor A V W` under contractive scalar
actions, retaining its additive group, uniformity and topology definitionally. -/
noncomputable abbrev productNormedAddCommGroup :
    NormedAddCommGroup (CompletedTensor A V W) :=
  let N := productNorm A V W
  { N.toNormedAddCommGroup with
    toMetricSpace := N.toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (uniformity_eq_productNorm A V W) }

/-- The norm of `productNormedAddCommGroup` is `CompletedTensor.productSeminorm A V W`. -/
@[simp]
theorem norm_productNormedAddCommGroup (z : CompletedTensor A V W) :
    @norm _ (productNormedAddCommGroup A V W).toNorm z = productSeminorm A V W z := (rfl)

/-- `productNormedAddCommGroup` retains the completion uniformity. -/
@[simp]
theorem uniformSpace_productNormedAddCommGroup :
    (productNormedAddCommGroup A V W).toUniformSpace =
      (inferInstance : UniformSpace (CompletedTensor A V W)) := (rfl)

/-- `productNormedAddCommGroup` defines an ultrametric distance. -/
theorem isUltrametricDist_productNormedAddCommGroup :
    letI := productNormedAddCommGroup A V W
    IsUltrametricDist (CompletedTensor A V W) := by
  have h := isNonarchimedean_productSeminorm (A := A) (V := V) (W := W)
  let := productNormedAddCommGroup A V W
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h

/-- Under `productNormedAddCommGroup`, the scalar action of `A` is contractive. -/
theorem isBoundedSMul_productNormedAddCommGroup :
    letI := productNormedAddCommGroup A V W
    IsBoundedSMul A (CompletedTensor A V W) := by
  let := productNormedAddCommGroup A V W
  exact IsBoundedSMul.of_norm_smul_le (productSeminorm_smul_le (A := A) (V := V) (W := W))

end Contractive

end IsTate

section CompleteField

variable {L V W : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [IsUltrametricDist V] [NormedSpace L V]
  [NormedAddCommGroup W] [IsUltrametricDist W] [NormedSpace L W]

variable (L V W) in
/-- **Injectivity of `toCompletion` over a complete nonarchimedean field** (Kedlaya–Liu Lemma
2.2.9(a)): for ultrametric normed `L`-spaces `V` and `W`, the canonical map
`V ⊗[L] W → V ⊗̂_L W` is injective. -/
theorem toCompletion_injective : Function.Injective (toCompletion L V W) :=
  (injective_iff_map_eq_zero (toCompletion L V W)).mpr fun u hu ↦ by
    have h0 : BanachModule.productSeminorm L V W u = 0 := by
      rw [← productSeminorm_toCompletion, hu, map_zero]
    exact BanachModule.productSeminorm_eq_zero_iff.mp h0

/-- Equality after `toCompletion L V W` over a complete nonarchimedean field reduces to equality in
`V ⊗[L] W`. -/
@[simp]
theorem toCompletion_inj {u u' : V ⊗[L] W} :
    toCompletion L V W u = toCompletion L V W u' ↔ u = u' :=
  (toCompletion_injective L V W).eq_iff

/-- Over a complete nonarchimedean field, `toCompletion L V W u = 0` iff `u = 0`. -/
@[simp]
theorem toCompletion_eq_zero {u : V ⊗[L] W} :
    toCompletion L V W u = 0 ↔ u = 0 :=
  map_eq_zero_iff _ (toCompletion_injective L V W)

/-- **Cross-norm theorem for `CompletedTensor.productSeminorm`.** Over a complete nontrivially
normed field, on ultrametric normed `L`-spaces `V` and `W`, the completed product seminorm of
`v ⊗ w` is `‖v‖ * ‖w‖`. -/
@[simp]
theorem productSeminorm_tmul (v : V) (w : W) :
    productSeminorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productSeminorm_toCompletion, BanachModule.productSeminorm_tmul]

/-- **Cross-norm theorem for `productNorm`.** Over a complete nontrivially normed field, on
ultrametric normed `L`-spaces `V` and `W`, the completed product norm of `v ⊗ w` is `‖v‖ * ‖w‖`. -/
theorem productNorm_tmul (v : V) (w : W) :
    productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖ :=
  productSeminorm_tmul v w

/-- Distance between elementary tensors sharing the second factor under `productNorm`. -/
theorem productNorm_tmul_sub_tmul_right (v v' : V) (w : W) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ * ‖w‖ := by
  rw [← LinearMap.map_sub₂, productNorm_tmul]

/-- Distance between elementary tensors sharing the first factor under `productNorm`. -/
theorem productNorm_tmul_sub_tmul_left (v : V) (w w' : W) :
    productNorm L V W (tmul L V W v w - tmul L V W v w') = ‖v‖ * ‖w - w'‖ := by
  rw [← map_sub, productNorm_tmul]

/-- Tensoring on the right with a unit vector is isometric for `productNorm`. -/
theorem productNorm_unitVector (v v' : V) {w : W} (hw : ‖w‖ = 1) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ := by
  rw [productNorm_tmul_sub_tmul_right, hw, mul_one]

end CompleteField

end CompletedTensor

end BanachModule

end TauCeti.Huber
