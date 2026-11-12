/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Products of adapted pseudo-gradients

Let `f` be a Morse function on a boundaryless manifold `M` modelled on a finite-dimensional real
normed space `E`, and `X` a pseudo-gradient adapted to `f`; let `g` and `Y` be the same data on `N`,
modelled on `E'`. Chart `M × N` on the normed space `E × E'` by `TauCeti.prodModelChartedSpace`,
so that it is a manifold of the kind on which the Morse complex is built. This file shows that the
product field `(X, Y)` (`TauCeti.Manifold.prodModelVectorField`) is a pseudo-gradient adapted to
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`, and that its dynamics is the product dynamics.

* Near a pair `(x, y)` of critical points, the product of a Morse chart at `x` and one at `y` is a
  Morse chart for the separated sum (`TauCeti.MorseChart.prod`), whose coordinates and weights are
  those of the first chart followed by those of the second. If `X` and `Y` are linear in the two
  charts, `(X, Y)` is linear in their product. Away from the critical points,
  `d(f + g)(X, Y) = df(X) + dg(Y)` is negative because one summand is negative and the other is
  not positive.
* On compact manifolds the flow of `(X, Y)` is the product of the flows of `X` and `Y`, so its
  stable and unstable sets are products of stable and unstable sets.
* If `X` and `Y` satisfy the Morse–Smale condition, so does `(X, Y)`: at a point of
  `W^u(a) ∩ W^s(b)` the tangent cones of the product sets contain the products of the tangent cones
  of the factors, and the sums of these span `TE × TE'`.

These are the product Morse data on which the Künneth formula for the mod-two Morse complex,
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_prod_morseBoundary`, is
computed.

## Main declarations

* `TauCeti.MorseChart.prod`: the product of two Morse charts.
* `TauCeti.IsAdaptedPseudoGradient.prod`: the product field `(X, Y)` is a pseudo-gradient adapted to
  `f ∘ Prod.fst + g ∘ Prod.snd`.
* `TauCeti.IsAdaptedPseudoGradient.prod_flow_apply`: its flow is the product of the flows.
* `TauCeti.IsAdaptedPseudoGradient.prod_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.prod_unstableSet`: stable and unstable sets are products.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`: products of Morse–Smale pseudo-gradients are
  Morse–Smale.
* `TauCeti.IsMorse.comp_fst_add_comp_snd_prodModel`,
  `TauCeti.mem_criticalPoints_comp_fst_add_comp_snd_iff` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd_prodModel`:
  the separated sum is Morse, with the pairs of critical points as critical points and additive
  Morse index, for the model `𝓘(ℝ, E × E')`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (adapted pseudo-gradient fields) and Chapter 4.
* M. Hutchings, *Lecture notes on Morse homology*, 2002, §3, Exercise 2 (the Morse complex of a
  product).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]

attribute [local instance low] prodModelChartedSpace

attribute [local instance] isManifold_prodModelChartedSpace

section Morse

variable {f : M → ℝ} {g : N → ℝ}

/-- The separated sum of two Morse functions is a Morse function on `M × N` modelled on the normed
space `E × E'`. -/
theorem IsMorse.comp_fst_add_comp_snd_prodModel (hf : IsMorse 𝓘(ℝ, E) f)
    (hg : IsMorse 𝓘(ℝ, E') g) : IsMorse 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) := by
  rw [modelWithCornersSelf_prod]
  exact hf.comp_fst_add_comp_snd hg

/-- **The critical points of a separated sum are the pairs of critical points**, on `M × N`
modelled on the normed space `E × E'`. -/
theorem mem_criticalPoints_comp_fst_add_comp_snd_iff (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) {p : M × N} :
    p ∈ criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) ↔
      p.1 ∈ criticalPoints 𝓘(ℝ, E) f ∧ p.2 ∈ criticalPoints 𝓘(ℝ, E') g := by
  rw [mem_criticalPoints, mem_criticalPoints, mem_criticalPoints, modelWithCornersSelf_prod]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff (hf p.1) (hg p.2)

/-- The differential of a separated sum at `p` sends `(v, w)` to `df(v) + dg(w)`, on `M × N`
modelled on the normed space `E × E'`. -/
theorem mvfderiv_comp_fst_add_comp_snd_apply (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : M × N) (v : TangentSpace 𝓘(ℝ, E × E') p) :
    mvfderiv 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) p v =
      mvfderiv 𝓘(ℝ, E) f p.1 v.1 + mvfderiv 𝓘(ℝ, E') g p.2 v.2 := by
  rw [modelWithCornersSelf_prod, mvfderiv_add ((hf p.1).comp p mdifferentiableAt_fst)
    ((hg p.2).comp p mdifferentiableAt_snd)]
  exact congrArg₂ (· + ·) (mvfderiv_comp_fst_apply f p v) (mvfderiv_comp_snd_apply g p v)

/-- The Morse index of a separated sum at a pair of nondegenerate critical points is the sum of
the two Morse indices, on `M × N` modelled on the normed space `E × E'`. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd_prodModel
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {x : M} {y : N}
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) =
      manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E') g y := by
  rw [modelWithCornersSelf_prod]
  exact hx.manifoldMorseIndex_comp_fst_add_comp_snd hy

end Morse

namespace MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {f : M → ℝ} {g : N → ℝ} {x : M} {y : N}

/-- The coordinates of the product of two Morse charts are indexed by the disjoint union of the
coordinates of the factors. -/
noncomputable def prodIndexEquiv :
    Fin (Module.finrank ℝ (E × E')) ≃ Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E') :=
  (finCongr Module.finrank_prod).trans finSumFinEquiv.symm

/-- **The product of two Morse charts.** Charts `φ` for `f` at `x` and `ψ` for `g` at `y` give the
product chart for `f ∘ Prod.fst + g ∘ Prod.snd` at `(x, y)`, whose coordinates and weights are
those of `φ` followed by those of `ψ`. -/
noncomputable def prod (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    MorseChart (E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) where
  toChart := φ.toChart.prod ψ.toChart
  mem_maximalAtlas := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod φ.mem_maximalAtlas ψ.mem_maximalAtlas
  mem_source := ⟨φ.mem_source, ψ.mem_source⟩
  apply_self := by simp
  coord := (φ.coord.prodCongr ψ.coord).trans
    (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm).trans
      (LinearEquiv.funCongrLeft ℝ ℝ prodIndexEquiv))
  weight i := Sum.elim φ.weight ψ.weight (prodIndexEquiv i)
  weight_eq_neg_one_or_eq_one i := by
    rcases prodIndexEquiv i with j | j
    · exact φ.weight_eq_neg_one_or_eq_one j
    · exact ψ.weight_eq_neg_one_or_eq_one j
  ncard_weight_neg := by
    have hset : {i | Sum.elim φ.weight ψ.weight (prodIndexEquiv i) < 0} =
        prodIndexEquiv ⁻¹' (Sum.inl '' {i | φ.weight i < 0} ∪ Sum.inr '' {j | ψ.weight j < 0}) := by
      ext i
      simp only [mem_ofPred_eq, mem_preimage]
      generalize prodIndexEquiv i = s
      rcases s with j | j <;> simp
    rw [hset, ncard_preimage_of_injective_subset_range prodIndexEquiv.injective (by simp),
      ncard_union_eq (by simp [disjoint_left]), ncard_image_of_injective _ Sum.inl_injective,
      ncard_image_of_injective _ Sum.inr_injective, φ.ncard_weight_neg, ψ.ncard_weight_neg,
      hx.manifoldMorseIndex_comp_fst_add_comp_snd_prodModel hy]
  eq_quadratic z hz := by
    obtain ⟨hz₁, hz₂⟩ := hz
    simp only [Pi.add_apply, comp_apply, φ.eq_quadratic z.1 hz₁, ψ.eq_quadratic z.2 hz₂,
      OpenPartialHomeomorph.prod_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [prodIndexEquiv.sum_comp (fun s ↦ Sum.elim φ.weight ψ.weight s *
      ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm
        (φ.coord (φ.toChart z.1), ψ.coord (ψ.toChart z.2)) s) ^ 2), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]
    ring

/-- The chart of the product of two Morse charts is the product of their charts. -/
@[simp]
theorem prod_toChart (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    (φ.prod ψ hx hy).toChart = φ.toChart.prod ψ.toChart :=
  (rfl)

/-- The weights of the product of two Morse charts are those of the first chart followed by those
of the second. -/
@[simp]
theorem prod_weight (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) (i : Fin (Module.finrank ℝ (E × E'))) :
    (φ.prod ψ hx hy).weight i = Sum.elim φ.weight ψ.weight (prodIndexEquiv i) :=
  (rfl)

/-- The coordinates of the product of two Morse charts are those of the first chart followed by
those of the second. -/
@[simp]
theorem prod_coord_apply (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) (v : E × E')
    (i : Fin (Module.finrank ℝ (E × E'))) :
    (φ.prod ψ hx hy).coord v i = Sum.elim (φ.coord v.1) (ψ.coord v.2) (prodIndexEquiv i) := by
  simp only [prod, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  generalize prodIndexEquiv i = s
  rcases s with j | j
  · exact LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl _ _ j
  · exact LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr _ _ j

/-- The derivative of the chart of a product of Morse charts is the product of the derivatives of
the two charts. -/
theorem mfderiv_prod_toChart_apply (φ : MorseChart E f x) (ψ : MorseChart E' g y)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) {z : M × N}
    (hz : z ∈ (φ.prod ψ hx hy).toChart.source) (v : E × E') :
    mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (φ.prod ψ hx hy).toChart z v =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z.1 v.1,
        mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart z.2 v.2) := by
  -- The coercion of a product of partial homeomorphisms is `Prod.map` by definition, and Mathlib
  -- states the derivative of a product map only for `Prod.map`.
  change mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (Prod.map φ.toChart ψ.toChart) z v = _
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
    mfderiv_prodMap (φ.mdifferentiableAt_toChart hz.1)
      (ψ.mdifferentiableAt_toChart hz.2)]
  -- The two sides differ only in the tangent spaces in which the components are read.
  rfl

end MorseChart

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {f : M → ℝ} {g : N → ℝ}
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y}

/-- **Products of adapted pseudo-gradients.** If `X` is a pseudo-gradient adapted to a Morse
function `f` on `M` and `Y` one adapted to a Morse function `g` on `N`, then the product field
`(X, Y)` is a pseudo-gradient adapted to `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`. Near a pair of
critical points the product of the two Morse charts linearizes it. -/
theorem prod (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) :
    IsAdaptedPseudoGradient (f ∘ Prod.fst + g ∘ Prod.snd) (Manifold.prodModelVectorField X Y) where
  contMDiff := Manifold.contMDiff_prodModelVectorField hX.contMDiff hY.contMDiff
  mvfderiv_apply_lt_zero p hp := by
    have hfd := hf.mdifferentiable
    have hgd := hg.mdifferentiable
    rw [Manifold.prodModelVectorField_apply]
    refine lt_of_eq_of_lt (mvfderiv_comp_fst_add_comp_snd_apply hfd hgd p (X p.1, Y p.2)) ?_
    have h₁ := hX.mvfderiv_apply_nonpos p.1
    have h₂ := hY.mvfderiv_apply_nonpos p.2
    by_cases hp₁ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p.1 = 0
    · by_cases hp₂ : mfderiv 𝓘(ℝ, E') 𝓘(ℝ) g p.2 = 0
      · refine absurd ?_ hp
        rw [← mvfderiv_eq_zero_iff]
        ext v
        rw [mvfderiv_comp_fst_add_comp_snd_apply hfd hgd, mvfderiv_eq_zero_iff.2 hp₁,
          mvfderiv_eq_zero_iff.2 hp₂]
        -- The zero maps are applied to the components `v.1` and `v.2`, typed in the model spaces
        -- rather than in the tangent spaces, so `ContinuousLinearMap.zero_apply` cannot rewrite
        -- them; they are `0` by definition.
        exact add_zero (0 : ℝ)
      · exact add_neg_of_nonpos_of_neg h₁ (hY.mvfderiv_apply_lt_zero p.2 hp₂)
    · exact add_neg_of_neg_of_nonpos (hX.mvfderiv_apply_lt_zero p.1 hp₁) h₂
  exists_morseChart p hp := by
    obtain ⟨x, y⟩ := p
    rw [← mvfderiv_eq_zero_iff, modelWithCornersSelf_prod,
      mvfderiv_comp_fst_add_comp_snd_eq_zero_iff (hf.mdifferentiable x)
        (hg.mdifferentiable y), mvfderiv_eq_zero_iff,
      mvfderiv_eq_zero_iff] at hp
    obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hp.1
    obtain ⟨ψ, hψ⟩ := hY.exists_morseChart y hp.2
    have hx := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hp.1
    have hy := hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hp.2
    refine ⟨φ.prod ψ hx hy, fun z hz ↦ ?_⟩
    rw [Manifold.prodModelVectorField_apply]
    refine (congrArg (φ.prod ψ hx hy).coord
      (MorseChart.mfderiv_prod_toChart_apply φ ψ hx hy hz (X z.1, Y z.2))).trans ?_
    ext i
    refine (MorseChart.prod_coord_apply φ ψ hx hy _ i).trans ?_
    rw [MorseChart.prod_weight, MorseChart.prod_coord_apply]
    generalize MorseChart.prodIndexEquiv i = s
    rcases s with j | j
    · exact congrFun (hφ z.1 hz.1) j
    · exact congrFun (hψ z.2 hz.2) j

section Flow

variable [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
  (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)

/-- **The flow of a product of adapted pseudo-gradients is the product of the flows.** -/
theorem prod_flow_apply (t : ℝ) (p : M × N) :
    (hX.prod hY hf hg).flow t p = (hX.flow t p.1, hY.flow t p.2) := by
  have hγ : IsMIntegralCurve (I := 𝓘(ℝ, E × E')) (fun s ↦ (hX.flow s p.1, hY.flow s p.2))
      (Manifold.prodModelVectorField X Y) := by
    intro s
    rw [modelWithCornersSelf_prod]
    refine ((hX.isMIntegralCurve_flow p.1 s).prodMk
      (hY.isMIntegralCurve_flow p.2 s)).congr_mfderiv ?_
    beta_reduce
    rw [Manifold.prodModelVectorField_apply]
    -- Both derivatives send `1` to `(X (γ s), Y (δ s))`, read in different tangent spaces.
    ext <;> rfl
  have h := globalFlow_eq_of_isMIntegralCurve ((hX.prod hY hf hg).contMDiff.of_le (by simp))
    (hX.prod hY hf hg).isCompleteVectorField hγ t
  simp only [Flow.map_zero_apply] at h
  rw [(hX.prod hY hf hg).flow_apply]
  exact (globalFlow_apply ..).symm.trans h

/-- The stable set of a point for the product flow is the product of the stable sets of its
components. -/
theorem prod_stableSet (a : M × N) :
    (hX.prod hY hf hg).flow.stableSet a = hX.flow.stableSet a.1 ×ˢ hY.flow.stableSet a.2 := by
  ext p
  rw [Flow.mem_stableSet, mem_prod, Flow.mem_stableSet, Flow.mem_stableSet,
    funext (prod_flow_apply hX hY hf hg · p), nhds_prod_eq, Filter.tendsto_prod_iff']

/-- The unstable set of a point for the product flow is the product of the unstable sets of its
components. -/
theorem prod_unstableSet (a : M × N) :
    (hX.prod hY hf hg).flow.unstableSet a =
      hX.flow.unstableSet a.1 ×ˢ hY.flow.unstableSet a.2 := by
  ext p
  rw [Flow.mem_unstableSet, mem_prod, Flow.mem_unstableSet, Flow.mem_unstableSet,
    funext (prod_flow_apply hX hY hf hg · p), nhds_prod_eq, Filter.tendsto_prod_iff']

variable {hX hY} in
/-- **Products of Morse–Smale pseudo-gradients are Morse–Smale.** If the stable and unstable
manifolds of `X` meet transversally, and so do those of `Y`, then so do those of the product field
`(X, Y)`: the tangent spaces of the products are the products of the tangent spaces. -/
theorem IsMorseSmale.prod (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) :
    (hX.prod hY hf hg).IsMorseSmale := by
  refine IsMorseSmale.of_forall fun a b z _ _ hz ↦ ?_
  rw [prod_unstableSet hX hY hf hg, prod_stableSet hX hY hf hg] at hz ⊢
  obtain ⟨⟨hz₁, hz₂⟩, hz₁', hz₂'⟩ := hz
  rw [eq_top_iff, ← Submodule.prod_top, ← hXs.span_mtangentConeAt_sup_eq_top ⟨hz₁, hz₁'⟩,
    ← hYs.span_mtangentConeAt_sup_eq_top ⟨hz₂, hz₂'⟩, ← Submodule.prod_sup_prod,
    modelWithCornersSelf_prod]
  exact sup_le_sup (span_mtangentConeAt_prod_le hz₁ hz₂) (span_mtangentConeAt_prod_le hz₁' hz₂')

end Flow

end IsAdaptedPseudoGradient

end TauCeti
