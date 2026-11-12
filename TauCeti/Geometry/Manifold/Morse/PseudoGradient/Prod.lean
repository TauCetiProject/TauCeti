/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.NormedProd
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow

/-!
# Products of adapted pseudo-gradients

Let `X` be a pseudo-gradient adapted to a Morse function `f` on `M`, and `Y` one adapted to a
Morse function `g` on `N`, where `M` and `N` are charted on finite-dimensional normed spaces `E`
and `E'`. Read the product `M × N` on the normed space `E × E'`
(`TauCeti.prodNormedChartedSpace`). This file shows that the product field
`(x, y) ↦ (X x, Y y)` is a pseudo-gradient adapted to the separated sum
`f ∘ Prod.fst + g ∘ Prod.snd` (`TauCeti.IsAdaptedPseudoGradient.prod`), and that its flow is the
product of the two flows, so that its stable and unstable sets are products. These are the inputs
of the Morse complex of the product (`TauCeti.Geometry.Manifold.Morse.Boundary.Prod`).

The Morse charts of the separated sum are the products of Morse charts
(`TauCeti.MorseChart.prod`): if `f = f x + (1/2) Σᵢ wᵢ zᵢ²` near `x` and
`g = g y + (1/2) Σⱼ w'ⱼ z'ⱼ²` near `y`, then near `(x, y)` the sum is the quadratic form with the
concatenated coordinates and weights, indexed by `Fin (dim E + dim E')`, and the product field
reads linearly in these coordinates.

## Main declarations

* `TauCeti.MorseChart.prod`: the product of Morse charts, a Morse chart of the separated sum.
* `TauCeti.IsAdaptedPseudoGradient.prod`: the product field is adapted to the separated sum.
* `TauCeti.IsAdaptedPseudoGradient.flow_prod`: its flow is the product of the flows.
* `TauCeti.IsAdaptedPseudoGradient.stableSet_prod` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_prod`: its stable and unstable sets are products.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (adapted pseudo-gradients).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance 10] prodNormedChartedSpace
attribute [local instance] isManifold_prodNormedChartedSpace

variable {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]
  {f : M → ℝ} {g : N → ℝ}

/-! ### Products of Morse charts -/

namespace MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] {x : M} {y : N}

variable (E E') in
/-- The coordinates of `E × E'`, indexed by `Fin (dim (E × E'))`, are the coordinates of `E`
followed by those of `E'`. -/
noncomputable def prodIndexEquiv :
    Fin (Module.finrank ℝ (E × E')) ≃ Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E') :=
  (finCongr Module.finrank_prod).trans finSumFinEquiv.symm

/-- **The product of Morse charts.** If `φ` is a Morse chart for `f` at `x` and `ψ` one for `g` at
`y`, the product chart is a Morse chart for the separated sum at `(x, y)`: its coordinates and
weights are those of `φ` followed by those of `ψ`. -/
noncomputable def prod (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hg : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    MorseChart (E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) where
  toChart := φ.toChart.prod ψ.toChart
  mem_maximalAtlas :=
    mem_maximalAtlas_prodNormed φ.mem_maximalAtlas ψ.mem_maximalAtlas
  mem_source := ⟨φ.mem_source, ψ.mem_source⟩
  apply_self := by simp
  coord := (φ.coord.prodCongr ψ.coord).trans
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm.trans
      (LinearEquiv.funCongrLeft ℝ ℝ (prodIndexEquiv E E')))
  weight i := Sum.elim φ.weight ψ.weight (prodIndexEquiv E E' i)
  weight_eq_neg_one_or_eq_one i := by
    rcases prodIndexEquiv E E' i with a | b
    · exact φ.weight_eq_neg_one_or_eq_one a
    · exact ψ.weight_eq_neg_one_or_eq_one b
  ncard_weight_neg := by
    rw [hf.manifoldMorseIndex_comp_fst_add_comp_snd_prodNormed hg,
      ← φ.ncard_weight_neg, ← ψ.ncard_weight_neg]
    have hS : {s : Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E') |
        Sum.elim φ.weight ψ.weight s < 0} =
        Sum.inl '' {a | φ.weight a < 0} ∪ Sum.inr '' {b | ψ.weight b < 0} := by
      ext (a | b) <;> simp
    rw [show {i | Sum.elim φ.weight ψ.weight (prodIndexEquiv E E' i) < 0} =
        prodIndexEquiv E E' ⁻¹' {s | Sum.elim φ.weight ψ.weight s < 0} from rfl,
      Set.ncard_preimage_of_injective_subset_range (prodIndexEquiv E E').injective (by simp), hS,
      Set.ncard_union_eq (Set.disjoint_left.2 (by rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩; cases h))
        (toFinite _) (toFinite _),
      Set.ncard_image_of_injective _ Sum.inl_injective,
      Set.ncard_image_of_injective _ Sum.inr_injective]
  eq_quadratic z hz := by
    obtain ⟨hz₁, hz₂⟩ := hz
    simp only [Pi.add_apply, Function.comp_apply]
    rw [φ.eq_quadratic _ hz₁, ψ.eq_quadratic _ hz₂, ← (prodIndexEquiv E E').symm.sum_comp,
      Fintype.sum_sum_type]
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr,
      OpenPartialHomeomorph.prod_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]
    ring

variable (φ : MorseChart E f x) (ψ : MorseChart E' g y)
  (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
  (hg : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y)

/-- The chart of a product of Morse charts is the product of the charts. -/
@[simp]
theorem prod_toChart : (φ.prod ψ hf hg).toChart = φ.toChart.prod ψ.toChart := by
  rw [prod]

/-- The coordinates of a product of Morse charts are those of the first chart followed by those of
the second. -/
@[simp]
theorem prod_coord_apply (v : E × E') (i : Fin (Module.finrank ℝ (E × E'))) :
    (φ.prod ψ hf hg).coord v i = Sum.elim (φ.coord v.1) (ψ.coord v.2) (prodIndexEquiv E E' i) := by
  simp only [prod, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  cases prodIndexEquiv E E' i with
  | inl a => exact LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl _ _ a
  | inr b => exact LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr _ _ b

/-- The weights of a product of Morse charts are those of the first chart followed by those of the
second. -/
@[simp]
theorem prod_weight (i : Fin (Module.finrank ℝ (E × E'))) :
    (φ.prod ψ hf hg).weight i = Sum.elim φ.weight ψ.weight (prodIndexEquiv E E' i) := by
  rw [prod]

end MorseChart

/-! ### The product pseudo-gradient -/

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y}

/-- **Products of adapted pseudo-gradients.** If `X` is adapted to the Morse function `f` and `Y`
to the Morse function `g`, the product field `(x, y) ↦ (X x, Y y)` is adapted to the separated sum
`f ∘ Prod.fst + g ∘ Prod.snd`. -/
theorem prod (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) :
    IsAdaptedPseudoGradient (f ∘ Prod.fst + g ∘ Prod.snd)
      (fun z : M × N ↦ ((X z.1, Y z.2) : TangentSpace 𝓘(ℝ, E × E') z)) where
  contMDiff := contMDiff_prodMk_vectorField_prodNormed hX.contMDiff hY.contMDiff
  mvfderiv_apply_lt_zero z hz := by
    -- Away from the critical points, `d(f + g)(X, Y) = df(X) + dg(Y)` is negative, since both
    -- terms are nonpositive and one is negative.
    have hf₁ := hf.contMDiff.mdifferentiable (by simp) z.1
    have hg₂ := hg.contMDiff.mdifferentiable (by simp) z.2
    rw [Ne, mfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed hf₁ hg₂,
      not_and_or] at hz
    rw [mvfderiv_comp_fst_add_comp_snd_apply_prodNormed hf₁ hg₂]
    have h₁ := hX.mvfderiv_apply_nonpos z.1
    have h₂ := hY.mvfderiv_apply_nonpos z.2
    rcases hz with hz | hz
    · linarith [hX.mvfderiv_apply_lt_zero z.1 hz]
    · linarith [hY.mvfderiv_apply_lt_zero z.2 hz]
  exists_morseChart z hz := by
    have hf₁ := hf.contMDiff.mdifferentiable (by simp) z.1
    have hg₂ := hg.contMDiff.mdifferentiable (by simp) z.2
    obtain ⟨hz₁, hz₂⟩ := (mfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed
      hf₁ hg₂).1 hz
    obtain ⟨φ, hφ⟩ := hX.exists_morseChart z.1 hz₁
    obtain ⟨ψ, hψ⟩ := hY.exists_morseChart z.2 hz₂
    have hnf := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hz₁
    have hng := hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hz₂
    -- The product of the Morse charts at `z.1` and `z.2` in which `X` and `Y` are linear is a Morse
    -- chart in which the product field is linear.
    refine ⟨φ.prod ψ hnf hng, fun w hw ↦ ?_⟩
    obtain ⟨hw₁, hw₂⟩ := hw
    have hP := (φ.prod ψ hnf hng).mdifferentiableAt_toChart (y := w) ⟨hw₁, hw₂⟩
    -- The derivative of the product chart acts componentwise.
    have hd : mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (φ.prod ψ hnf hng).toChart w
        ((X w.1, Y w.2) : E × E') =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart w.1 (X w.1),
          mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart w.2 (Y w.2)) := by
      -- For maps into a normed space, `mvfderiv` is `mfderiv` read in the target, by definition.
      refine Prod.ext (((ContinuousLinearMap.fst ℝ E E').mvfderiv_comp_apply hP _).symm.trans ?_)
        (((ContinuousLinearMap.snd ℝ E E').mvfderiv_comp_apply hP _).symm.trans ?_)
      · exact mfderiv_comp_fst_apply_prodNormed (φ.mdifferentiableAt_toChart hw₁) _
      · exact mfderiv_comp_snd_apply_prodNormed (ψ.mdifferentiableAt_toChart hw₂) _
    rw [hd]
    funext i
    simp only [MorseChart.prod_weight, MorseChart.prod_coord_apply, MorseChart.prod_toChart,
      OpenPartialHomeomorph.prod_apply]
    refine (MorseChart.prod_coord_apply φ ψ hnf hng
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart w.1 (X w.1),
        mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart w.2 (Y w.2)) : E × E') i).trans ?_
    rcases MorseChart.prodIndexEquiv E E' i with a | b
    · exact congr_fun (hφ w.1 hw₁) a
    · exact congr_fun (hψ w.2 hw₂) b

variable [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
  (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)

/-- **The flow of the product pseudo-gradient is the product of the flows.** -/
@[simp]
theorem flow_prod (t : ℝ) (z : M × N) :
    (hX.prod hY hf hg).flow t z = (hX.flow t z.1, hY.flow t z.2) := by
  have hγ := isMIntegralCurve_prodMk_prodNormed (hX.isMIntegralCurve_flow z.1)
    (hY.isMIntegralCurve_flow z.2)
  have hv : ContMDiff 𝓘(ℝ, E × E') 𝓘(ℝ, E × E').tangent 1 (fun z : M × N ↦
      (⟨z, ((X z.1, Y z.2) : E × E')⟩ : TangentBundle 𝓘(ℝ, E × E') (M × N))) :=
    (hX.prod hY hf hg).contMDiff.of_le (by simp)
  have hc := (hX.prod hY hf hg).isCompleteVectorField
  have h := globalFlow_eq_of_isMIntegralCurve hv hc hγ t
  simp only [Flow.map_zero_apply] at h
  exact ((hX.prod hY hf hg).flow_apply t z).trans ((globalFlow_apply hv hc t z).symm.trans h)

/-- The stable set of `p` for the product pseudo-gradient is the product of the stable sets of its
components. -/
@[simp]
theorem stableSet_prod (p : M × N) :
    (hX.prod hY hf hg).flow.stableSet p = hX.flow.stableSet p.1 ×ˢ hY.flow.stableSet p.2 := by
  ext z
  simp only [Flow.mem_stableSet, mem_prod, Prod.tendsto_iff, flow_prod hX hY hf hg]

/-- The unstable set of `p` for the product pseudo-gradient is the product of the unstable sets of
its components. -/
@[simp]
theorem unstableSet_prod (p : M × N) :
    (hX.prod hY hf hg).flow.unstableSet p =
      hX.flow.unstableSet p.1 ×ˢ hY.flow.unstableSet p.2 := by
  ext z
  simp only [Flow.mem_unstableSet, mem_prod, Prod.tendsto_iff, flow_prod hX hY hf hg]

end IsAdaptedPseudoGradient

end TauCeti
