/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Compactness
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Components
import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
import TauCeti.Analysis.Sobolev.W1p.AddHaar
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Data.ENNReal.InterpolatedExponent

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

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`.
* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`: the same
  on an affine-isometric copy of `Ω`.
* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`: the same on a bounded open set of
  a finite-dimensional real inner product space satisfying the intrinsic Lipschitz-domain
  condition, for every additive Haar measure.
* `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith`: the
  Poincaré–Wirtinger inequality on a bounded connected Lipschitz domain.
* `TauCeti.W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_finite_isLipschitzDomain`:
  Poincaré–Wirtinger after subtracting the mean on each piece of a finite disjoint cover.
* `TauCeti.W1p.exists_isCompactOperator_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → L^q(Ω)` for every subcritical `q`.

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

/-- **Rellich–Kondrachov on rigid copies of bounded Lipschitz domains.** Let an affine isometry
`e` carry `U` onto a bounded Lipschitz domain `Ω ⊆ ℝ × E`, in the sense that `Ω = e⁻¹⁻¹(U)`.
Then for `1 ≤ p ≤ ∞` the value map `W^{1,p}(U) → Lᵖ(U)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {U : Opens F}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hΩU : (Ω : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' U) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := U) (p := p)) :=
  W1p.isCompactOperator_valueL_of_affineIsometryEquiv e
    (hΩU ▸ (e.toHomeomorph.toEquiv.preimage_symm_preimage U).symm)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb)

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

/-! ### Intrinsic Lipschitz domains -/

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {mu : Measure F} [mu.IsAddHaarMeasure] {U : Opens F}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **Rellich–Kondrachov on intrinsic bounded Lipschitz domains.** Let `F` be a finite-dimensional
real inner product space and `U ⊆ F` a bounded open set satisfying the intrinsic Lipschitz-domain
condition `(U : Set F).IsLipschitzDomain E'` for some normed tangential model space `E'`. For every
additive Haar measure `μ` on `F` and `1 ≤ p ≤ ∞`, the value map `W^{1,p}(U) → Lᵖ(U)` is a compact
operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomain
    (hU : (U : Set F).IsLipschitzDomain E') (hb : IsBounded (U : Set F)) :
    IsCompactOperator (W1p.valueL (mu := mu) (Omega := U) (p := p)) := by
  -- When `frontier U` is empty, `closure U ⊆ U` is compact and local Rellich compactness applies.
  -- Otherwise a boundary chart carries `U` onto a Lipschitz domain of the model space `ℝ × E'`,
  -- followed by a change of Haar measure.
  rcases (frontier (U : Set F)).eq_empty_or_nonempty with hfr | hne
  · have hcl : closure (U : Set F) ⊆ U :=
      (isClopen_iff_frontier_eq_empty.mpr hfr).isClosed.closure_subset
    convert W1p.isCompactOperator_valueL_restrictL (mu := mu) (p := p)
      hb.isCompact_closure hcl using 1
    ext1 u
    simp
  obtain ⟨g, L, hL⟩ := hU.exists_isLipschitzDomainWith_image hb hne
  -- Give `E'` the inner product, finite dimension and Borel structure of its image in `F`.
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E') := g.linearIsometryEquiv
  let _ : InnerProductSpace ℝ E' := .ofLinearIsometry e.symmInr
  have _ : FiniteDimensional ℝ E' := e.finiteDimensional_snd
  let _ : MeasurableSpace E' := borel E'
  have _ : BorelSpace E' := ⟨rfl⟩
  let V : Opens (WithLp 2 (ℝ × E')) := ⟨g '' U, ((isLipschitzDomainWith_iff _ _).1 hL).1⟩
  exact W1p.isCompactOperator_valueL_of_addHaar (nu := volume)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv (Ω := V) hL
      (g.lipschitzWith.isBounded_image hb) g (g.toHomeomorph.image_eq_preimage_symm U))

end Intrinsic

end TauCeti

end
