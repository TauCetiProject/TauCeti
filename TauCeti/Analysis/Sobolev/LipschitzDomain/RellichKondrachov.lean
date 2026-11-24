/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Compactness
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Components
import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.Rescale

/-!
# Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `1 ≤ p ≤ ∞`, the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. Unlike `TauCeti.W1p0.isCompactOperator_valueL`, this
concerns the whole Sobolev space, with no vanishing boundary values. The boundary regularity enters
only through the extension operator `TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the
value map factors as extension to the whole space followed by restriction to `Ω`, and the latter is
compact by local Rellich compactness (`TauCeti.W1p.isCompactOperator_valueL_restrictL`), since
`closure Ω` is compact. At `p = ∞`, the local compactness theorem uses Arzelà–Ascoli for
the uniformly bounded equi-Lipschitz whole-space representatives.

Compactness then gives the Poincaré–Wirtinger inequality on bounded connected Lipschitz domains,
with a constant that is not explicit. On a finite disjoint union of bounded preconnected
Lipschitz open sets, one instead subtracts the mean on each piece, with a constant uniform in
the Sobolev function. Empty pieces are allowed, and no separation of the closures is required.

Compactness passes to every subcritical target exponent: if `Ω` has dimension `n`, `1 ≤ p < ∞`
and `1 ≤ q < ∞` with `1/p - 1/q < 1/n`, then `W^{1,p}(Ω) → L^q(Ω)` is compact. For `p < n` this is
the range `q < p⋆` below the Sobolev conjugate `1/p⋆ = 1/p - 1/n`, and for `p ≥ n` it is every
finite `q`. For `q ≤ p` the inclusion factors through `Lᵖ(Ω)`, as `Ω` has finite measure. For
`q > p` choose a finite `s > q` still in the subcritical range: the inclusion is bounded into
`L^s(Ω)` (`TauCeti.W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith`), and
`1/q = (1 - θ)/p + θ/s` with `0 ≤ θ < 1`, so the interpolation inequality
`‖u‖_{L^q} ≤ ‖u‖_{Lᵖ} ^ (1 - θ) ‖u‖_{L^s} ^ θ` transfers compactness from `Lᵖ(Ω)` to `L^q(Ω)`
(`IsCompactOperator.of_forall_ae_eq_of_interpolation`). The inequality `1/p - 1/q < 1/n` is
strict: at `q = p⋆` the inclusion is bounded but not compact.

Compactness of the value map is invariant under measure-preserving changes of variables with a
Lipschitz inverse. Transporting along the affine isometries of the boundary charts, it holds for
every bounded open subset of a finite-dimensional inner product space satisfying the intrinsic
Lipschitz-domain predicate `Set.IsLipschitzDomain`, such as a bounded Lipschitz domain of
`EuclideanSpace ℝ (Fin n)`, on which the energy forms of divergence-form operators live.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`.
* `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith`: the
  Poincaré–Wirtinger inequality on a bounded connected Lipschitz domain.
* `TauCeti.W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_finite_isLipschitzDomain`:
  Poincaré–Wirtinger after subtracting the mean on each piece of a finite disjoint cover.
* `TauCeti.W1p.exists_isCompactOperator_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → L^q(Ω)` for every subcritical `q`.
* `TauCeti.W1p.isCompactOperator_valueL_of_measurePreserving`: compactness of the value map
  transported along a change of variables.
* `TauCeti.W1p.isCompactOperator_valueL_of_frontier_eq_empty`: compactness of the value map on a
  bounded open set with empty frontier.
* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_image` and
  `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`: Rellich–Kondrachov compactness on
  isometric copies of Lipschitz domains and for the intrinsic predicate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.7, Theorem 1, and §5.8.1, Theorem 1.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 6.3.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal Function

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich–Kondrachov on bounded Lipschitz domains.** If `Ω` is a bounded Lipschitz domain and
`1 ≤ p ≤ ∞`, the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  obtain ⟨T, hT, _⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hK : IsCompactOperator
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)) :=
    W1p.isCompactOperator_valueL_restrictL hb.isCompact_closure (subset_univ _)
  -- The value map is the value of the restriction of the extension.
  have heq : W1p.valueL (mu := volume) (Omega := Ω) (p := p) =
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)).comp T := by
    rw [ContinuousLinearMap.comp_assoc, hT, ContinuousLinearMap.comp_id]
  rw [heq]
  exact hK.comp_clm T

/-- **The Poincaré–Wirtinger inequality on bounded connected Lipschitz domains.** Let `Ω` be a
bounded, preconnected Lipschitz domain, let `S ⊆ Ω` have positive measure, and let `1 ≤ p ≤ ∞`.
There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at
most `C` times the `Lᵖ` norm of its weak gradient. -/
theorem W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    {S : Set (WithLp 2 (ℝ × E))} (hS : S ⊆ Ω) (hS0 : volume S ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p volume Ω p,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y) p (volume.restrict Ω) ≤
        ENNReal.ofReal C * ‖W1p.gradient u‖ₑ :=
  W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb) hconn
    hb.measure_lt_top.ne hS hS0

/-- **Poincaré–Wirtinger on finitely many components.** On a finite disjoint union of bounded
preconnected Lipschitz open sets, the gradient controls the deviation from the mean on each
piece, for every `1 ≤ p ≤ ∞`. Empty pieces are allowed. The constant is uniform in the Sobolev
function. -/
theorem W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_finite_isLipschitzDomain
    {ι : Type*} [Finite ι] {U : ι → Opens (WithLp 2 (ℝ × E))}
    (hd : Pairwise (Disjoint on fun i ↦ (U i : Set (WithLp 2 (ℝ × E)))))
    (hcover : ⋃ i, (U i : Set (WithLp 2 (ℝ × E))) = Ω)
    (hL : ∀ i, (U i : Set (WithLp 2 (ℝ × E))).IsLipschitzDomain E)
    (hb : ∀ i, IsBounded (U i : Set (WithLp 2 (ℝ × E))))
    (hc : ∀ i, IsPreconnected (U i : Set (WithLp 2 (ℝ × E)))) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p, ∃ m : WithLp 2 (ℝ × E) → ℝ,
      (∀ i, EqOn m (fun _ ↦ ⨍ y in U i, W1p.value u y) (U i)) ∧
      eLpNorm (fun x ↦ W1p.value u x - m x) p (volume.restrict Ω) ≤ C * ‖W1p.gradient u‖ₑ := by
  classical
  let := Fintype.ofFinite ι
  have hP (i : ι) : ∃ C : ℝ≥0, ∀ v : W1p volume (U i) p,
      eLpNorm (fun x ↦ W1p.value v x - ⨍ y in U i, W1p.value v y)
        p (volume.restrict (U i)) ≤ C * ‖W1p.gradient v‖ₑ := by
    rcases (U i : Set (WithLp 2 (ℝ × E))).eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, fun v ↦ by simp [hemp]⟩
    obtain ⟨L, hLi⟩ := (hL i).exists_isLipschitzDomainWith
      ((hb i).isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    obtain ⟨C, hC, hP⟩ := W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith
      (p := p) hLi (hb i) (hc i) subset_rfl
      ((U i).isOpen.measure_pos volume hne).ne'
    rw [ENNReal.ofReal_eq_coe_nnreal hC] at hP
    exact ⟨⟨C, hC⟩, hP⟩
  choose C hC using hP
  refine ⟨Finset.univ.sup C, fun u ↦
    W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_pairwise_disjoint
      hd hcover _ (fun i v ↦ ?_) u⟩
  exact (hC i v).trans <| mul_le_mul_left (by
    exact_mod_cast (Finset.le_sup (f := C) (Finset.mem_univ i))) _

/-- **Rellich–Kondrachov for subcritical target exponents.** Let `Ω ⊆ ℝ × E` be a bounded
Lipschitz domain of dimension `n`, let `1 ≤ p ≤ ∞`, and let `1 ≤ q < ∞` with `1/p - 1/q < 1/n`.
Then the inclusion `W^{1,p}(Ω) → L^q(Ω)` is a compact operator. For `p < n` the condition says
`q < p⋆`, where `1/p⋆ = 1/p - 1/n`; for `p ≥ n` every finite `q` is allowed. -/
theorem W1p.exists_isCompactOperator_of_isLipschitzDomainWith {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ∞)
    (hpq : p⁻¹ < q⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ S : W1p volume Ω p →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      IsCompactOperator S ∧
        ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
  obtain ⟨S, hS⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hq hpq hΩ hb)
  refine ⟨S, ?_, hS⟩
  have hK := W1p.isCompactOperator_valueL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hS₀ (u : W1p volume Ω p) :
      ⇑(S u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] ⇑(W1p.valueL (p := p) u) := by
    rw [W1p.valueL_apply]
    exact hS u
  rcases le_total q p with hqp | hpq'
  · -- For `q ≤ p`, compactness into `Lᵖ(Ω)` passes down, as `Ω` has finite measure.
    have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
      isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
    exact hK.of_forall_ae_eq_of_le hqp hS₀
  -- For `p ≤ q`, interpolate between `Lᵖ(Ω)` and `L^s(Ω)` for a finite `s > q` in the
  -- subcritical range.
  obtain ⟨s, θ, hs₁, hs, hps, hθ0, hθ1, hrel⟩ :=
    exists_inv_eq_of_inv_lt_inv_add Fact.out hq hpq' hpq
  have : Fact (1 ≤ s) := ⟨hs₁⟩
  obtain ⟨T, hT⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hs hps hΩ hb)
  exact hK.of_forall_ae_eq_of_interpolation T hθ0 hθ1 hrel hS₀ fun u => (hS u).trans (hT u).symm

end TauCeti

/-! ### Changes of variables and the intrinsic Lipschitz-domain predicate -/

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Transport

variable {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
  [FiniteDimensional ℝ F'] [MeasurableSpace F'] [BorelSpace F']
  {μ : Measure F} [μ.IsAddHaarMeasure] {ν : Measure F'} [ν.IsAddHaarMeasure]
  {U : Opens F} {V : Opens F'}

/-- **Compactness of the value map is invariant under Lipschitz changes of variables.** Let
`Φ : F → F'` and `Ψ : F' → F` be measure-preserving, with `U = Φ⁻¹(V)`, `V = Ψ⁻¹(U)` and `Ψ` a left
inverse of `Φ` on `U`, and let `Ψ` be locally Lipschitz on `V` with bounded derivative there. If
the value map `W^{1,p}(V) → Lᵖ(V)` is compact, so is `W^{1,p}(U) → Lᵖ(U)`: it is the value map of
`V` conjugated by the precompositions with `Ψ` and with `Φ`. -/
theorem W1p.isCompactOperator_valueL_of_measurePreserving {Φ : F → F'} {Ψ : F' → F} {M : ℝ}
    (hΦ : MeasurePreserving Φ μ ν) (hΨ : MeasurePreserving Ψ ν μ)
    (hUV : (U : Set F) = Φ ⁻¹' V) (hVU : (V : Set F') = Ψ ⁻¹' U)
    (hΨl : LocallyLipschitzOn V Ψ) (hM : ∀ y ∈ (V : Set F'), ‖fderiv ℝ Ψ y‖ ≤ M)
    (hΨΦ : ∀ x ∈ (U : Set F), Ψ (Φ x) = x)
    (hK : IsCompactOperator (W1p.valueL (mu := ν) (Omega := V) (p := p))) :
    IsCompactOperator (W1p.valueL (mu := μ) (Omega := U) (p := p)) := by
  have hΦr : MeasurePreserving Φ (μ.restrict U) (ν.restrict V) :=
    hUV ▸ hΦ.restrict_preimage V.isOpen.measurableSet
  let S := W1p.compMeasurePreservingL (p := p) hΨ hVU hΨl hM
  let R : Lp ℝ p (ν.restrict V) →L[ℝ] Lp ℝ p (μ.restrict U) :=
    (Lp.compMeasurePreservingₗᵢ ℝ Φ hΦr).toContinuousLinearMap
  have heq : W1p.valueL (mu := μ) (Omega := U) (p := p) = R.comp (W1p.valueL.comp S) := by
    ext1 u
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (W1p.value (S u)) hΦr,
      hΦr.quasiMeasurePreserving.ae_eq_comp
        (W1p.value_compMeasurePreservingL_ae hΨ hVU hΨl hM u),
      ae_restrict_mem U.isOpen.measurableSet] with x h₁ h₂ hx
    simp only [ContinuousLinearMap.comp_apply, W1p.valueL_apply, R,
      LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply]
    rw [h₁]
    exact (h₂.trans (congrArg (W1p.value u) (hΨΦ x hx))).symm
  rw [heq]
  exact (hK.comp_clm S).clm_comp R

end Transport

section Intrinsic

open scoped Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens F} {L : ℝ≥0}

/-- **Rellich–Kondrachov on isometric copies of bounded Lipschitz domains.** Let
`g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` be an affine isometry equivalence and `Ω ⊆ F` a bounded open set
whose image `g '' Ω` is a Lipschitz domain with constant `L`. Then the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is compact for `1 ≤ p ≤ ∞`. No inner-product, finite-dimensionality or
measurability instances are assumed on `E`, as `g` embeds `E` linearly and isometrically into
`F`. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_image
    (g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hΩ : (g '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  -- The inner product of `F` restricts to `E` along the isometric embedding given by `g`.
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := g.linearIsometryEquiv
  let ι : E →ₗᵢ[ℝ] F :=
    { toLinearMap := e.symm.toLinearEquiv.toLinearMap.comp
        ((WithLp.linearEquiv 2 ℝ (ℝ × E)).symm.toLinearMap.comp (LinearMap.inr ℝ ℝ E))
      norm_map' y := by simp }
  let _ : InnerProductSpace ℝ E :=
    { inner x y := inner ℝ (ι x) (ι y)
      norm_sq_eq_re_inner x := by simp
      conj_inner_symm x y := by simp [real_inner_comm]
      add_left x y z := by simp [inner_add_left]
      smul_left x y r := by simp [inner_smul_left] }
  have _ : FiniteDimensional ℝ E := Module.Finite.of_injective ι.toLinearMap ι.injective
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨g '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  have hWΩ : (W : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ω :=
    congrFun (image_eq_preimage_of_inverse g.symm_apply_apply g.apply_symm_apply) _
  exact W1p.isCompactOperator_valueL_of_measurePreserving (Ψ := g.symm) (M := 1)
    g.measurePreserving g.symm.measurePreserving (g.toEquiv.preimage_image _).symm hWΩ
    g.symm.lipschitzWith.locallyLipschitz.locallyLipschitzOn
    (fun y _ => g.symm.norm_fderiv_le y) (fun x _ => g.symm_apply_apply x)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ
      (g.lipschitzWith.isBounded_image hb))

/-- With empty frontier, a bounded open set has compact closure inside itself, so the value map is
compact by local Rellich–Kondrachov compactness. -/
theorem W1p.isCompactOperator_valueL_of_frontier_eq_empty {μ : Measure F}
    [μ.IsAddHaarMeasure] (hb : IsBounded (Ω : Set F)) (hfr : frontier (Ω : Set F) = ∅) :
    IsCompactOperator (W1p.valueL (mu := μ) (Omega := Ω) (p := p)) := by
  have hcl : closure (Ω : Set F) ⊆ (Ω : Set F) :=
    (isClopen_iff_frontier_eq_empty.mpr hfr).isClosed.closure_subset
  have hK : IsCompactOperator
      ((W1p.valueL (mu := μ) (Omega := Ω) (p := p)).comp (W1p.restrictL le_rfl)) :=
    W1p.isCompactOperator_valueL_restrictL hb.isCompact_closure hcl
  have heq : W1p.valueL (mu := μ) (Omega := Ω) (p := p) =
      (W1p.valueL (mu := μ) (Omega := Ω) (p := p)).comp (W1p.restrictL le_rfl) := by
    ext1 u
    simp
  exact heq ▸ hK

/-- Rellich–Kondrachov for the intrinsic predicate and Lebesgue measure. -/
private theorem W1p.isCompactOperator_valueL_volume_of_isLipschitzDomain {Ω : Opens F}
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | ⟨x₀, hx₀⟩
  · exact W1p.isCompactOperator_valueL_of_frontier_eq_empty hb hfr
  obtain ⟨g, -, -, -, -, -, -⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.mp hΩ x₀ hx₀
  have hfr_cpt : IsCompact (frontier (g '' (Ω : Set F))) := by
    rw [← g.coe_toHomeomorph, ← g.toHomeomorph.image_frontier]
    exact (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).image
      g.continuous
  obtain ⟨L, hL⟩ := (hΩ.image g).exists_isLipschitzDomainWith hfr_cpt
  exact W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_image g hL hb

/-- **Rellich–Kondrachov on bounded Lipschitz domains of a Euclidean space.** Let `F` be a
finite-dimensional real inner product space with an additive Haar measure `μ`, and `Ω ⊆ F` a
bounded open set satisfying the intrinsic Lipschitz-domain condition
`(Ω : Set F).IsLipschitzDomain E` for some normed tangential model space `E`. Then the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is compact for `1 ≤ p ≤ ∞`. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomain {μ : Measure F} [μ.IsAddHaarMeasure]
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (W1p.valueL (mu := μ) (Omega := Ω) (p := p)) := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | ⟨x₀, hx₀⟩
  · exact W1p.isCompactOperator_valueL_of_frontier_eq_empty hb hfr
  -- A set with nonempty frontier lives in a nontrivial space.
  have : Nontrivial F := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rcases (Ω : Set F).eq_empty_or_nonempty with he | hne
    · simp [he] at hx₀
    · rw [Subsingleton.eq_univ_of_nonempty hne, frontier_univ] at hx₀
      exact hx₀
  -- A dilation by `t` carries `μ` to `volume`, and `Ω` to the Lipschitz domain `t • Ω`.
  obtain ⟨t, ht, hmap⟩ := μ.exists_pos_map_smul_eq volume
  let V : Opens F := ⟨t • (Ω : Set F), Ω.isOpen.smul₀ ht.ne'⟩
  have hΦ : MeasurePreserving (t • · : F → F) μ volume := ⟨measurable_const_smul t, hmap⟩
  have hΨ : MeasurePreserving (t⁻¹ • · : F → F) volume μ := by
    refine ⟨measurable_const_smul _, ?_⟩
    rw [← hmap, Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
    simp [Function.comp_def, smul_smul, inv_mul_cancel₀ ht.ne']
  exact W1p.isCompactOperator_valueL_of_measurePreserving hΦ hΨ
    (by simp [V, preimage_smul₀ ht.ne', smul_smul, inv_mul_cancel₀ ht.ne'])
    (preimage_smul_inv₀ ht.ne' _).symm
    (lipschitzWith_smul t⁻¹).locallyLipschitz.locallyLipschitzOn
    (fun _ _ => norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_smul t⁻¹))
    (fun x _ => inv_smul_smul₀ ht.ne' x)
    (W1p.isCompactOperator_valueL_volume_of_isLipschitzDomain (Ω := V) (hΩ.smul ht)
      (hb.smul₀ t))

end Intrinsic

end TauCeti

end
