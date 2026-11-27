/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Comp
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Product
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Products of distributions under pullback along submersions

Let `k` be a submersion from an open set `Ω₀` of a finite-dimensional real inner product space
`E₀` into an open set `Ω` of `E`: smooth, with surjective derivative at every point of `Ω₀`. Every
distribution `T` on `Ω` has a pullback `k^* T` to `Ω₀`, by integration over the fibres of `k`
(`Distribution.compCLMOfSubmersion`), which depends on a choice of Haar measures on `E₀` and `E`.
Rescaling one of them scales `k^*` by a constant. With Lebesgue measure (`volume`) on both sides,
`k^*` sends the distribution of a function `g`, taken with respect to Lebesgue measure, to that of
`g ∘ k` (`Distribution.compCLMOfSubmersion_ofFun`), so it should be multiplicative. This file
proves that it is, for the product of distributions under Hörmander's wave front condition
(`Distribution.product`):

`k^* (S T) = (k^* S) (k^* T)`, the pullbacks being taken with Lebesgue measure on both sides

(`Distribution.compCLMOfSubmersion_product`). For other Haar measures the two sides differ by the
scaling constant of `k^*`, and the identity fails unless that constant is `1`. The wave front
condition passes to the pullbacks (`Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`):
covectors of `WF(k^* S)` over `x` are the images `Dk(x)ᵀ η` of covectors `η` of `WF(S)` over
`k x` (`Distribution.waveFrontSet_compCLMOfSubmersion`), and `Dk(x)ᵀ` is injective, so opposite
covectors of `WF(k^* S)` and `WF(k^* T)` come from opposite covectors of `WF(S)` and `WF(T)`.

A smooth change of variables is a submersion, so the product of distributions does not depend on
the coordinates (`Distribution.compCLMOfOpenPartialHomeomorph_product`). This is what lets the
product of distributions be read in the charts of a manifold.

## The argument

The product is the pullback of the tensor product along the diagonal
(`Distribution.pullback_diagonal_transportCLM_tensorProduct_eq_product`), and pullbacks compose
with submersions on either side (`Distribution.pullback_comp_of_surjective`,
`Distribution.pullback_eq_pullback_compCLMOfSubmersion`). Since `Δ ∘ k = (k × k) ∘ Δ₀` for the
diagonals `Δ` and `Δ₀`,

`k^* (S T) = k^* Δ^* (S ⊗ T) = Δ₀^* (k × k)^* (S ⊗ T)`.

It remains to use that the tensor product commutes with pullback along products of submersions,
`(k × k)^* (S ⊗ T) = k^* S ⊗ k^* T` (`Distribution.compCLMOfSubmersion_prodMap_tensorProduct`),
after moving it from `E × E` to the Euclidean product `WithLp 2 (E × E)` on which the diagonal
pullback lives. Lebesgue measure on `WithLp 2 (E × E)` corresponds to the product of the Lebesgue
measures on `E × E`, which is why the product identity is stated for `volume`.

## Main results

* `Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`: the wave front condition for the
  product passes to pullbacks along submersions.
* `Distribution.compCLMOfSubmersion_product`: `k^* (S T) = (k^* S) (k^* T)`, the pullbacks being
  taken with Lebesgue measure on both sides.
* `Distribution.compCLMOfOpenPartialHomeomorph_product`: the same for a smooth change of
  variables `e`, `e^* (S T) = (e^* S) (e^* T)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorems 8.2.4 and 8.2.10.
-/

public section

noncomputable section

open Function MeasureTheory Set TopologicalSpace TestFunction WithLp TauCeti
open scoped Distributions ContDiff

namespace Distribution

/-! ### The product under submersions -/

variable {E₀ E : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω₀ : Opens E₀} {Ω : Opens E} {k : E₀ → E}
  (hk : ContDiffOn ℝ ∞ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω) (hks : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k x))
  {S T : 𝓓'(Ω, ℂ)}

include hk hks in
/-- **The wave front condition under pullback along a submersion.** If `S` and `T` have no
opposite covectors over `k x`, then their pullbacks along the submersion `k` have none over `x`: a
covector of `WF(k^* S)` over `x` is `Dk(x)ᵀ η` for a covector `η` of `WF(S)` over `k x`, and
`Dk(x)ᵀ` is injective. -/
theorem NoOppositeCovectorsOn.compCLMOfSubmersion {μ : Measure E₀} [μ.IsAddHaarMeasure]
    {ν : Measure E} [ν.IsAddHaarMeasure] {x : E₀} (h : NoOppositeCovectorsOn S T {k x}) :
    NoOppositeCovectorsOn (compCLMOfSubmersion μ ν k hk hkΩ hks S)
      (compCLMOfSubmersion μ ν k hk hkΩ hks T) {x} := by
  rw [noOppositeCovectorsOn_singleton_iff] at h ⊢
  intro ξ hS hT
  rw [waveFrontSet_compCLMOfSubmersion] at hS hT
  obtain ⟨hxΩ, η₁, hη₁, hξ₁⟩ := hS
  obtain ⟨-, η₂, hη₂, hξ₂⟩ := hT
  dsimp only at hxΩ hη₁ hξ₁ hη₂ hξ₂
  have hinj : Injective (fderiv ℝ k x).adjoint :=
    ContinuousLinearMap.adjoint_injective_iff_denseRange.2 (hks x hxΩ).denseRange
  have : η₂ = -η₁ := hinj (by rw [hξ₂, map_neg, hξ₁])
  exact h η₁ hη₁ (this ▸ hη₂)

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hk hks in
/-- The product `k × k` of a submersion with itself is a submersion on `Ω₀ ×ˢ Ω₀`. -/
private theorem surjective_fderiv_prodMap_self {p : E₀ × E₀}
    (hp : p ∈ (Ω₀ : Set E₀) ×ˢ (Ω₀ : Set E₀)) : Surjective (fderiv ℝ (Prod.map k k) p) :=
  surjective_fderiv_prodMap ((hk.contDiffAt (Ω₀.isOpen.mem_nhds hp.1)).differentiableAt (by simp))
    ((hk.contDiffAt (Ω₀.isOpen.mem_nhds hp.2)).differentiableAt (by simp)) (hks _ hp.1)
    (hks _ hp.2)

/-- The product `k × k` of a submersion with itself, on the Euclidean products `WithLp 2 (E₀ × E₀)`
and `WithLp 2 (E × E)`. -/
private abbrev prodMapL2 (k : E₀ → E) : WithLp 2 (E₀ × E₀) → WithLp 2 (E × E) :=
  (prodContinuousLinearEquiv 2 ℝ E E).symm ∘ Prod.map k k ∘ prodContinuousLinearEquiv 2 ℝ E₀ E₀

variable {W₀ : Opens (WithLp 2 (E₀ × E₀))} {W : Opens (WithLp 2 (E × E))}
  (hW₀ : ∀ q ∈ W₀, prodContinuousLinearEquiv 2 ℝ E₀ E₀ q ∈ (Ω₀ : Set E₀) ×ˢ (Ω₀ : Set E₀))

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hk hW₀ in
private theorem contDiffOn_prodMapL2 : ContDiffOn ℝ ∞ (prodMapL2 k) W₀ :=
  (prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff.comp_contDiffOn
    ((hk.prodMap hk).comp (prodContinuousLinearEquiv 2 ℝ E₀ E₀).contDiff.contDiffOn hW₀)

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hk hks hW₀ in
private theorem surjective_fderiv_prodMapL2 :
    ∀ q ∈ W₀, Surjective (fderiv ℝ (prodMapL2 k) q) := by
  intro q hq
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (ContinuousLinearEquiv.surjective _).comp
    ((surjective_fderiv_prodMap_self hk hks (hW₀ q hq)).comp (ContinuousLinearEquiv.surjective _))

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hkΩ hW₀ in
private theorem mapsTo_prodMapL2
    (hW : ∀ q, prodContinuousLinearEquiv 2 ℝ E E q ∈ (Ω : Set E) ×ˢ (Ω : Set E) → q ∈ W) :
    MapsTo (prodMapL2 k) W₀ W := fun q hq ↦
  hW _ (by simpa using (hkΩ.prodMap hkΩ) (hW₀ q hq))

/-- The open set `Ω ×ˢ Ω` of `E × E`. -/
private abbrev prodOpens (Ω : Opens E) : Opens (E × E) :=
  ⟨(Ω : Set E) ×ˢ (Ω : Set E), Ω.isOpen.prod Ω.isOpen⟩

/-- The open set `Ω ×ˢ Ω`, read in the Euclidean product `WithLp 2 (E × E)`. -/
private abbrev prodL2Opens (Ω : Opens E) : Opens (WithLp 2 (E × E)) :=
  ⟨prodContinuousLinearEquiv 2 ℝ E E ⁻¹' ((Ω : Set E) ×ˢ (Ω : Set E)),
    (Ω.isOpen.prod Ω.isOpen).preimage (prodContinuousLinearEquiv 2 ℝ E E).continuous⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem mapsTo_prodL2Opens (Ω : Opens E) :
    MapsTo (prodContinuousLinearEquiv 2 ℝ E E) (prodL2Opens Ω) (prodOpens Ω) :=
  fun _ hq ↦ hq

/-- The pullback of `S ⊗ T`, moved to `WithLp 2 (E × E)`, along `k × k` is `k^* S ⊗ k^* T`, moved
to `WithLp 2 (E₀ × E₀)`. -/
private theorem compCLMOfSubmersion_prodMapL2_transportCLM_tensorProduct (S T : 𝓓'(Ω, ℂ)) :
    compCLMOfSubmersion volume volume (prodMapL2 k)
        (contDiffOn_prodMapL2 hk (W₀ := prodL2Opens Ω₀) fun _ hq ↦ hq)
        (mapsTo_prodMapL2 hkΩ (fun _ hq ↦ hq) fun _ hq ↦ hq)
        (surjective_fderiv_prodMapL2 hk hks fun _ hq ↦ hq)
        (transportCLM (prodContinuousLinearEquiv 2 ℝ E E) (mapsTo_prodL2Opens Ω)
          (S.tensorProduct T (V := prodOpens Ω) subset_rfl)) =
      transportCLM (prodContinuousLinearEquiv 2 ℝ E₀ E₀) (mapsTo_prodL2Opens Ω₀)
        ((compCLMOfSubmersion volume volume k hk hkΩ hks S).tensorProduct
          (compCLMOfSubmersion volume volume k hk hkΩ hks T) (V := prodOpens Ω₀) subset_rfl) := by
  have hL : MeasurePreserving (prodContinuousLinearEquiv 2 ℝ E E) volume (volume.prod volume) :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E E
  have hL₀ : MeasurePreserving (prodContinuousLinearEquiv 2 ℝ E₀ E₀) volume (volume.prod volume) :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E₀ E₀
  ext φ
  rw [compCLMOfSubmersion_apply, transportCLM_apply, transportCLM_apply,
    ← compCLMOfSubmersion_prodMap_tensorProduct volume volume volume volume hk hkΩ hks hk hkΩ hks
      (V₀ := prodOpens Ω₀) rfl (V := prodOpens Ω) rfl (hk := hk.prodMap hk)
      (hkV := hkΩ.prodMap hkΩ) (hks := fun _ ↦ surjective_fderiv_prodMap_self hk hks) S T,
    compCLMOfSubmersion_apply]
  congr 1
  refine (eq_fiberIntegralCLM_iff _ _ _ _ _).2 fun g hg _ _ ↦ ?_
  simp only [ContinuousLinearEquiv.transportTestFunction_apply]
  rw [← hL.integral_comp (prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph.measurableEmbedding,
    ← hL₀.integral_comp
      (prodContinuousLinearEquiv 2 ℝ E₀ E₀).toHomeomorph.measurableEmbedding]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  refine (integral_fiberIntegralCLM_smul volume volume _ _ _ φ
    (g := fun y ↦ g (prodContinuousLinearEquiv 2 ℝ E E y))
    (hg.continuous.comp (prodContinuousLinearEquiv 2 ℝ E E).continuous).continuousOn).trans ?_
  simp [prodMapL2]

/-- **The product of distributions commutes with pullback along submersions**: if at every point
no covector of the wave front set of `S` is opposite to a covector of the wave front set of `T`,
then the same holds for their pullbacks along a submersion `k`
(`Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`), and

`k^* (S T) = (k^* S) (k^* T)`,

the pullbacks being taken with Lebesgue measure on both sides. -/
theorem compCLMOfSubmersion_product (h : ∀ y, NoOppositeCovectorsOn S T {y}) :
    compCLMOfSubmersion volume volume k hk hkΩ hks (S.product T h) =
      (compCLMOfSubmersion volume volume k hk hkΩ hks S).product
        (compCLMOfSubmersion volume volume k hk hkΩ hks T)
        (fun x ↦ (h (k x)).compCLMOfSubmersion hk hkΩ hks) := by
  symm
  have hΔ : MapsTo (fun x : E ↦ toLp 2 (x, x)) Ω (prodL2Opens Ω) := fun x hx ↦ by
    simp [prodL2Opens, hx]
  have hΔ₀ : MapsTo (fun x : E₀ ↦ toLp 2 (x, x)) Ω₀ (prodL2Opens Ω₀) := fun x hx ↦ by
    simp [prodL2Opens, hx]
  -- `k^* (S T) = k^* Δ^* (S ⊗ T) = (Δ ∘ k)^* (S ⊗ T) = Δ₀^* (k × k)^* (S ⊗ T)`, since
  -- `Δ ∘ k = (k × k) ∘ Δ₀`; then `(k × k)^* (S ⊗ T) = k^* S ⊗ k^* T` and `Δ₀^*` gives the product.
  conv_rhs => rw [← pullback_diagonal_transportCLM_tensorProduct_eq_product (V := prodOpens Ω) rfl
      (mapsTo_prodL2Opens Ω) h hΔ, ← pullback_eq_compCLMOfSubmersion hk hkΩ hks,
    ← pullback_comp_of_surjective (contDiff_toLp_diag ℝ E).contDiffOn hΔ hk hkΩ hks,
    pullback_eq_pullback_compCLMOfSubmersion (contDiff_toLp_diag ℝ E₀).contDiffOn hΔ₀
      (contDiffOn_prodMapL2 hk fun _ hq ↦ hq) (mapsTo_prodMapL2 hkΩ (fun _ hq ↦ hq) fun _ hq ↦ hq)
      (surjective_fderiv_prodMapL2 hk hks fun _ hq ↦ hq) (g := (fun x : E ↦ toLp 2 (x, x)) ∘ k) _ _
      (fun _ _ ↦ by simp [prodMapL2])]
  rw [← pullback_diagonal_transportCLM_tensorProduct_eq_product (V := prodOpens Ω₀) rfl
    (mapsTo_prodL2Opens Ω₀) _ hΔ₀]
  congr 1
  exact (compCLMOfSubmersion_prodMapL2_transportCLM_tensorProduct hk hkΩ hks S T).symm

/-! ### Changes of variables -/

section ChangeOfVariables

variable {e : OpenPartialHomeomorph E E} (he : ContDiffOn ℝ ∞ e e.source)
  (he' : ContDiffOn ℝ ∞ e.symm e.target) {U : Opens E} (hU : (U : Set E) ⊆ e.source)
  (hUΩ : MapsTo e U Ω)

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] in
/-- **The wave front condition under a change of variables.** If `S` and `T` have no opposite
covectors over `e x`, then `e^* S` and `e^* T` have none over `x`. -/
theorem NoOppositeCovectorsOn.compCLMOfOpenPartialHomeomorph {x : E}
    (h : NoOppositeCovectorsOn S T {e x}) :
    NoOppositeCovectorsOn (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ S)
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) {x} := by
  rw [← compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph volume he he' hU hUΩ
    (hsurj := fun _ hx ↦ e.surjective_fderiv_of_contDiffOn he he' (by simp) (hU hx))]
  exact h.compCLMOfSubmersion (he.mono hU) hUΩ _

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] in
/-- **The product of distributions does not depend on the coordinates**: for a smooth change of
variables `e`, if `S` and `T` satisfy Hörmander's condition at every point, then
`e^* (S T) = (e^* S) (e^* T)`. -/
theorem compCLMOfOpenPartialHomeomorph_product (h : ∀ y, NoOppositeCovectorsOn S T {y}) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUΩ (S.product T h) =
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ S).product
        (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T)
        (fun x ↦ (h (e x)).compCLMOfOpenPartialHomeomorph he he' hU hUΩ) := by
  have hsurj : ∀ x ∈ U, Surjective (fderiv ℝ e x) := fun _ hx ↦
    e.surjective_fderiv_of_contDiffOn he he' (by simp) (hU hx)
  simp only [← compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph volume he he' hU hUΩ
    (hsurj := hsurj)]
  exact compCLMOfSubmersion_product (he.mono hU) hUΩ hsurj h

end ChangeOfVariables

end Distribution
