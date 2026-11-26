/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc
import TauCeti.Analysis.Sobolev.WeakDeriv.AddHaar
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving

/-!
# First-order local Sobolev classes on Euclidean domains

For an open subset `Ω` of a real normed space `E` carrying a measure `μ` (defaulting to `volume`)
and a real normed codomain `F`, a map `u : E → F` belongs to the first-order local Sobolev class
`TauCeti.MemW1pLoc p Ω u μ` when `u` is locally `Lᵖ` on `Ω` (`TauCeti.MemLpLoc p Ω u μ`) and admits
a weak Fréchet derivative `Du : E → E →L[ℝ] F` on `Ω` (`TauCeti.HasWeakFDerivOn μ Ω u Du`) that is
itself locally `Lᵖ` on `Ω`.

The definition applies to actual functions without quotienting by almost-everywhere equality and
imposes no global integrability condition on `Ω`. Completeness of `F` is not a typeclass argument
on `MemW1pLoc`; it is carried by `HasWeakFDerivOn` and recovered by
`TauCeti.MemW1pLoc.completeSpace`. Comparison with `TauCeti.W1p` and with the planar order-one class
`TauCeti.MemWkpLoc p Ω 1` lives in `TauCeti.Analysis.Sobolev.Local.W1p`, and counterexamples and
sharpness checks live in `TauCeti.Analysis.Sobolev.Local.FirstOrder.Examples`.

## Main results

* **Uniqueness transfer and measurability.** By almost-everywhere uniqueness of weak derivatives
  (`TauCeti.HasWeakFDerivOn.ae_eq`), *every* weak derivative of `u ∈ MemW1pLoc p Ω` on `Ω` belongs
  to `MemLpLoc p Ω` (`TauCeti.MemW1pLoc.memLpLoc_of_hasWeakFDerivOn`). Every member is locally
  integrable (`TauCeti.MemW1pLoc.locallyIntegrableOn`) and, on second-countable domains,
  almost-everywhere strongly measurable (`TauCeti.MemW1pLoc.aestronglyMeasurable_restrict`) for all
  exponents `p : ℝ≥0∞`.
* **Restriction, monotonicity, and algebraic structure.** `MemW1pLoc` restricts to smaller open
  sets, depends only on almost-everywhere values on `Ω`, decreases in the exponent `p` when compact
  sets have finite measure, and is closed under addition, negation, subtraction, scalar
  multiplication, finite sums, continuous linear maps on the codomain, Banach rays `x ↦ a x • v`,
  and finite products.
* **Classical and Lipschitz maps.** `C¹` maps (`ContDiffOn.memW1pLoc`, `ContDiff.memW1pLoc`),
  differentiable maps with continuous derivative
  (`DifferentiableOn.memW1pLoc_of_continuousOn_fderiv`), and—when domain and codomain are
  finite-dimensional—locally Lipschitz maps (`LocallyLipschitzOn.memW1pLoc`,
  `LipschitzOnWith.memW1pLoc`, `LipschitzWith.memW1pLoc`) belong to `MemW1pLoc p Ω` for every
  exponent `p`; for `u ∈ MemW1pLoc p Ω` agreeing almost everywhere with a `C¹` map `g`, `fderiv ℝ g`
  is a weak derivative of `u` in `MemLpLoc p Ω`
  (`TauCeti.MemW1pLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`).
* **Sheaf property and locality.** On finite-dimensional Borel spaces with complete codomain,
  `MemW1pLoc` satisfies the sheaf condition on arbitrary open covers (`TauCeti.memW1pLoc_iSup_iff`)
  and is detected on open neighbourhoods of each point (`TauCeti.memW1pLoc_iff_locally`).
* **Coordinates and dual testing.** Membership is detected in any finite basis of the codomain
  (`Module.Basis.memW1pLoc_iff`) and by directional weak derivatives along any finite basis of the
  domain (`Module.Basis.memW1pLoc_iff_apply`). For an arbitrary Banach codomain and `1 ≤ p`,
  testing against `StrongDual ℝ F` characterizes `MemW1pLoc` *once* `u` and its candidate derivative
  lie in `MemLpLoc p Ω` (`TauCeti.memW1pLoc_iff_forall_strongDual`,
  `TauCeti.MemLpLoc.memW1pLoc_of_forall_strongDual`).
* **Haar-measure and linear invariance.** On finite-dimensional real normed spaces, `MemW1pLoc` is
  independent of the choice of additive Haar measure (`TauCeti.memW1pLoc_iff_of_isAddHaarMeasure`),
  invariant under finite nonzero measure rescaling (`TauCeti.memW1pLoc_smul_measure_iff`), and
  preserved and reflected by every continuous linear equivalence `e : E₁ ≃L[ℝ] E`
  (`ContinuousLinearEquiv.memW1pLoc_comp_iff`), regardless of Jacobian determinant or choice of
  equivalent norm (`TauCeti.memW1pLoc_comp_toLp_iff`); the corresponding `MemLpLoc` invariance
  results live in `TauCeti.MeasureTheory.Function.MemLpLoc`.

## References

* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §2.1–§2.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299 (Bochner strong measurability vs. scalar weak differentiability).
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology

namespace TauCeti

section Basic

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E} {p q : ℝ≥0∞} {Ω Ω' : Opens E} {u v : E → F}

/-- A map `u : E → F` on an open set `Ω ⊆ E` belongs to the first-order local Sobolev class
`MemW1pLoc p Ω u μ` when `u` is locally `Lᵖ(μ)` on `Ω` and has a weak Fréchet derivative on `Ω` with
respect to `μ` that is also locally `Lᵖ(μ)` on `Ω`. -/
def MemW1pLoc (p : ℝ≥0∞) (Ω : Opens E) (u : E → F) (μ : Measure E := by volume_tac) : Prop :=
  MemLpLoc p Ω u μ ∧ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u Du ∧ MemLpLoc p Ω Du μ

/-- Unfolding characterization of `MemW1pLoc`. -/
theorem memW1pLoc_iff :
    MemW1pLoc p Ω u μ ↔
      MemLpLoc p Ω u μ ∧ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u Du ∧ MemLpLoc p Ω Du μ :=
  Iff.rfl

/-- Every member of `MemW1pLoc p Ω` belongs to `MemLpLoc p Ω`. -/
theorem MemW1pLoc.memLpLoc (hu : MemW1pLoc p Ω u μ) : MemLpLoc p Ω u μ :=
  hu.1

/-- Every member of `MemW1pLoc p Ω` admits a weak Fréchet derivative in `MemLpLoc p Ω`. -/
theorem MemW1pLoc.exists_hasWeakFDerivOn (hu : MemW1pLoc p Ω u μ) :
    ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u Du ∧ MemLpLoc p Ω Du μ :=
  hu.2

/-- Membership in `MemW1pLoc` supplies completeness of the codomain, inherited from
`HasWeakFDerivOn`. -/
theorem MemW1pLoc.completeSpace (hu : MemW1pLoc p Ω u μ) : CompleteSpace F := by
  obtain ⟨_, hDu, _⟩ := hu.exists_hasWeakFDerivOn
  exact hDu.completeSpace

/-- Every weak derivative of a member of `MemW1pLoc p Ω` is locally `Lᵖ` on `Ω`, not only the
existential witness, since weak derivatives on `Ω` agree almost everywhere. -/
theorem MemW1pLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hu : MemW1pLoc p Ω u μ) {Du : E → E →L[ℝ] F} (hDu : HasWeakFDerivOn μ Ω u Du) :
    MemLpLoc p Ω Du μ := by
  obtain ⟨Du', hDu', hLp⟩ := hu.exists_hasWeakFDerivOn
  exact hLp.congr_ae (hDu'.ae_eq hDu)

/-- Every member of `MemW1pLoc p Ω` is locally integrable on `Ω` for *every* exponent `p : ℝ≥0∞`,
since local integrability is part of `HasWeakFDerivOn`. -/
theorem MemW1pLoc.locallyIntegrableOn (hu : MemW1pLoc p Ω u μ) :
    LocallyIntegrableOn u Ω μ := by
  obtain ⟨_, hDu, _⟩ := hu.exists_hasWeakFDerivOn
  exact hDu.locallyIntegrableOn

/-- On a second-countable domain, every member of `MemW1pLoc p Ω` is almost-everywhere strongly
measurable on `Ω`, for every exponent `p : ℝ≥0∞`. -/
theorem MemW1pLoc.aestronglyMeasurable_restrict [SecondCountableTopology E]
    (hu : MemW1pLoc p Ω u μ) : AEStronglyMeasurable u (μ.restrict Ω) :=
  hu.locallyIntegrableOn.aestronglyMeasurable

/-- `MemW1pLoc` restricts to any smaller open subset. -/
theorem MemW1pLoc.mono (hu : MemW1pLoc p Ω u μ) (hΩ : Ω' ≤ Ω) : MemW1pLoc p Ω' u μ := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.mono_set hΩ, Du, hDu.mono hΩ, hDuLp.mono_set hΩ⟩

/-- Almost-everywhere equality on `Ω` preserves `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.congr_ae (hu : MemW1pLoc p Ω u μ) (huv : u =ᵐ[μ.restrict Ω] v) :
    MemW1pLoc p Ω v μ := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.congr_ae huv, Du, hDu.congr_ae huv, hDuLp⟩

/-- Restricting to a smaller open subset preserves `MemW1pLoc` for any map agreeing with the
original one there. -/
theorem MemW1pLoc.congr_mono [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u μ)
    (hvu : Set.EqOn v u Ω') (hΩ : Ω' ≤ Ω) : MemW1pLoc p Ω' v μ :=
  (hu.mono hΩ).congr_ae <| by
    filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with x hx using (hvu hx).symm

/-- `MemW1pLoc p Ω` depends only on the values of the map on `Ω`. -/
theorem MemW1pLoc.congr [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u μ)
    (hvu : Set.EqOn v u Ω) : MemW1pLoc p Ω v μ :=
  hu.congr_mono hvu le_rfl

/-- Decreasing the exponent preserves `MemW1pLoc` whenever compact subsets have finite measure. -/
theorem MemW1pLoc.mono_exponent [IsFiniteMeasureOnCompacts μ]
    (hu : MemW1pLoc p Ω u μ) (hqp : q ≤ p) : MemW1pLoc q Ω u μ := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.mono_exponent hqp, Du, hDu, hDuLp.mono_exponent hqp⟩

/-! ### Algebraic and linear operations -/

/-- The zero map belongs to `MemW1pLoc p Ω` for every complete codomain. -/
@[simp]
theorem memW1pLoc_zero [CompleteSpace F] : MemW1pLoc p Ω (0 : E → F) μ :=
  ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, memLpLoc_zero⟩

/-- Every constant map belongs to `MemW1pLoc p Ω` on a finite-dimensional space with a Borel
additive Haar measure. -/
@[simp]
theorem memW1pLoc_const [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (c : F) :
    MemW1pLoc p Ω (fun _ => c) μ :=
  ⟨memLpLoc_const c, 0, hasWeakFDerivOn_iff.2 fun w =>
    hasWeakLineDerivOn_const (μ := μ) (Ω := Ω) (v := w) c, memLpLoc_zero⟩

/-- `MemW1pLoc` is closed under addition. -/
theorem MemW1pLoc.add [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u μ)
    (hv : MemW1pLoc p Ω v μ) : MemW1pLoc p Ω (u + v) μ := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  obtain ⟨hvLp, Dv, hDv, hDvLp⟩ := hv
  exact ⟨huLp.add hvLp, Du + Dv, hDu.add hDv, hDuLp.add hDvLp⟩

/-- `MemW1pLoc` is closed under negation. -/
theorem MemW1pLoc.neg (hu : MemW1pLoc p Ω u μ) : MemW1pLoc p Ω (-u) μ := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.neg, -Du, hDu.neg, hDuLp.neg⟩

/-- `MemW1pLoc` is closed under subtraction. -/
theorem MemW1pLoc.sub [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u μ)
    (hv : MemW1pLoc p Ω v μ) : MemW1pLoc p Ω (u - v) μ := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- `MemW1pLoc` is closed under real scalar multiplication. -/
theorem MemW1pLoc.const_smul (hu : MemW1pLoc p Ω u μ) (c : ℝ) : MemW1pLoc p Ω (c • u) μ := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.const_smul c, c • Du, hDu.const_smul c, hDuLp.const_smul c⟩

/-- Finite sums preserve `MemW1pLoc`. -/
theorem MemW1pLoc.sum {ι : Type*} [OpensMeasurableSpace E] [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemW1pLoc p Ω (f i) μ) :
    MemW1pLoc p Ω (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memW1pLoc_zero (p := p) (Ω := Ω))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Postcomposition with a continuous linear map into a complete codomain preserves `MemW1pLoc`. -/
theorem MemW1pLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hu : MemW1pLoc p Ω u μ)
    (L : F →L[ℝ] G) : MemW1pLoc p Ω (fun x => L (u x)) μ := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.clm_comp L, fun x => L.comp (Du x), hDu.clm_comp L,
    hDuLp.clm_comp ((ContinuousLinearMap.compL ℝ E F G) L)⟩

/-- Postcomposition with a continuous linear equivalence preserves and reflects `MemW1pLoc`,
transferring completeness between codomains automatically. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memW1pLoc_iff [OpensMeasurableSpace E] (e : F ≃L[ℝ] G) :
    MemW1pLoc p Ω (fun x => e (u x)) μ ↔ MemW1pLoc p Ω u μ := by
  constructor
  · intro h
    have : CompleteSpace G := h.completeSpace
    have : CompleteSpace F :=
      (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      h.clm_comp e.symm.toContinuousLinearMap
  · intro h
    have : CompleteSpace F := h.completeSpace
    have : CompleteSpace G :=
      (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance
    exact h.clm_comp e.toContinuousLinearMap

/-- **Banach rays.** Scaling a fixed vector `v : F` in a complete space by a scalar function
`a ∈ MemW1pLoc p Ω` produces a map `x ↦ a x • v` in `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemW1pLoc p Ω a μ) (v : F) : MemW1pLoc p Ω (fun x => a x • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- Pairing two maps in `MemW1pLoc p Ω` produces a product-valued map in `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.prodMk [OpensMeasurableSpace E] {w : E → G} (hu : MemW1pLoc p Ω u μ)
    (hw : MemW1pLoc p Ω w μ) : MemW1pLoc p Ω (fun x => (u x, w x)) μ := by
  have : CompleteSpace F := hu.completeSpace
  have : CompleteSpace G := hw.completeSpace
  have h := (hu.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hw.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext x <;> simp

/-- The pointwise product map `x ↦ (A x).prodMap (B x)` of two operator fields in `MemW1pLoc p Ω`
(acting componentwise on `E₁ × E₃`) belongs to `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.prodMap {E₁ E₂ E₃ E₄ : Type*} [OpensMeasurableSpace E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemW1pLoc p Ω A μ)
    (hB : MemW1pLoc p Ω B μ) :
    MemW1pLoc p Ω (fun x => (A x).prodMap (B x)) μ := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-! ### Classical differentiability and Lipschitz maps -/

/-- A map continuous on `Ω` lies in `MemW1pLoc p Ω` if and only if it admits a weak derivative on
`Ω` lying in `MemLpLoc p Ω`. -/
theorem _root_.ContinuousOn.memW1pLoc_iff [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    (hu : ContinuousOn u Ω) :
    MemW1pLoc p Ω u μ ↔ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u Du ∧ MemLpLoc p Ω Du μ :=
  ⟨MemW1pLoc.exists_hasWeakFDerivOn, fun h => ⟨hu.memLpLoc, h⟩⟩

/-- On a finite-dimensional space with a Borel additive Haar measure, a map differentiable on `Ω`
with continuous Fréchet derivative on `Ω` belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.DifferentiableOn.memW1pLoc_of_continuousOn_fderiv [FiniteDimensional ℝ E]
    [BorelSpace E] [μ.IsAddHaarMeasure] [CompleteSpace F]
    (hu : DifferentiableOn ℝ u Ω) (hDu : ContinuousOn (fderiv ℝ u) Ω) : MemW1pLoc p Ω u μ :=
  ⟨hu.continuousOn.memLpLoc, fderiv ℝ u,
    hasWeakFDerivOn_of_differentiableOn (hDu.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun _ hx => hu.differentiableAt (Ω.isOpen.mem_nhds hx),
    hDu.memLpLoc⟩

/-- A `C¹` map on `Ω` belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.ContDiffOn.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (hu : ContDiffOn ℝ 1 u Ω) :
    MemW1pLoc p Ω u μ :=
  ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    (hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).memLpLoc⟩

/-- A globally `C¹` map belongs to `MemW1pLoc p Ω` on every open set and for every exponent `p`. -/
theorem _root_.ContDiff.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (hu : ContDiff ℝ 1 u) :
    MemW1pLoc p Ω u μ :=
  hu.contDiffOn.memW1pLoc

/-- Every continuous linear map belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.ContinuousLinearMap.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (L : E →L[ℝ] F) :
    MemW1pLoc p Ω L μ :=
  L.contDiff.memW1pLoc

/-- If a `C¹` map `g` on `Ω` agrees almost everywhere on `Ω` with `u ∈ MemW1pLoc p Ω`, then
`fderiv ℝ g` is a weak derivative of `u` on `Ω` and belongs to `MemLpLoc p Ω`. -/
theorem MemW1pLoc.hasWeakFDerivOn_fderiv_of_contDiffOn [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {g : E → F} (hu : MemW1pLoc p Ω u μ)
    (hg : ContDiffOn ℝ 1 g Ω) (hug : u =ᵐ[μ.restrict Ω] g) :
    HasWeakFDerivOn μ Ω u (fderiv ℝ g) ∧ MemLpLoc p Ω (fderiv ℝ g) μ := by
  have := hu.completeSpace
  have hg' : HasWeakFDerivOn μ Ω g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  exact ⟨hg'.congr_ae hug.symm, hu.memLpLoc_of_hasWeakFDerivOn (hg'.congr_ae hug.symm)⟩

/-- **Rademacher's theorem in `MemW1pLoc`.** A map locally Lipschitz on `Ω` between
finite-dimensional real normed spaces belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.LocallyLipschitzOn.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F]
    (hu : LocallyLipschitzOn Ω u) : MemW1pLoc p Ω u μ := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  refine ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    memLpLoc_of_forall_eventually_norm_le (measurable_fderiv ℝ u).aestronglyMeasurable
      fun x hx => ?_⟩
  obtain ⟨K, t, ht, hK⟩ := hu hx
  rw [nhdsWithin_eq_nhds.2 (Ω.isOpen.mem_nhds hx)] at ht
  exact ⟨K, (eventually_mem_nhds_iff.2 ht).mono fun _ hy => norm_fderiv_le_of_lipschitzOn ℝ hy hK⟩

/-- A map Lipschitz on `Ω` between finite-dimensional real normed spaces belongs to `MemW1pLoc p Ω`
for every exponent `p`. -/
theorem _root_.LipschitzOnWith.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] {K : ℝ≥0}
    (hu : LipschitzOnWith K u Ω) : MemW1pLoc p Ω u μ :=
  LocallyLipschitzOn.memW1pLoc fun _ _ => ⟨K, Ω, self_mem_nhdsWithin, hu⟩

/-- A globally Lipschitz map between finite-dimensional real normed spaces belongs to
`MemW1pLoc p Ω` on every open set and for every exponent `p`. -/
theorem _root_.LipschitzWith.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] {K : ℝ≥0}
    (hu : LipschitzWith K u) : MemW1pLoc p Ω u μ :=
  hu.locallyLipschitz.locallyLipschitzOn.memW1pLoc

/-! ### Sheaf and locality properties -/

/-- **Sheaf property for `MemW1pLoc`.** On a finite-dimensional Borel space with complete codomain,
`MemW1pLoc p` on a union of open sets is equivalent to `MemW1pLoc p` on each member of the cover.
Completeness of `F` is assumed so that the equivalence holds for an empty cover. -/
theorem memW1pLoc_iSup_iff [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {ι : Type*} (V : ι → Opens E) :
    MemW1pLoc p (⨆ i, V i) u μ ↔ ∀ i, MemW1pLoc p (V i) u μ := by
  refine ⟨fun hu i => hu.mono (le_iSup V i), fun h => ?_⟩
  choose D hD hDLp using fun i => (h i).exists_hasWeakFDerivOn
  obtain ⟨G, hG, hGD⟩ := exists_hasWeakFDerivOn_iSup V D hD
  refine ⟨(memLpLoc_iSup_iff V).2 fun i => (h i).memLpLoc, G, hG,
    (memLpLoc_iSup_iff V).2 fun i => (hDLp i).congr_ae (hGD i).symm⟩

/-- **Pointwise locality of `MemW1pLoc`.** Membership on `Ω` holds if and only if every point of
`Ω` has an open neighbourhood inside `Ω` on which membership holds. -/
theorem memW1pLoc_iff_locally [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    MemW1pLoc p Ω u μ ↔ ∀ x ∈ Ω, ∃ W : Opens E, x ∈ W ∧ W ≤ Ω ∧ MemW1pLoc p W u μ := by
  refine ⟨fun hu x hx => ⟨Ω, hx, le_rfl, hu⟩, fun h => ?_⟩
  choose W hxW hWΩ hWu using fun x : Ω => h x.val x.property
  have hsup : (⨆ x : Ω, W x) = Ω :=
    le_antisymm (iSup_le hWΩ) fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  exact hsup ▸ (memW1pLoc_iSup_iff W).2 hWu

end Basic

/-! ### Coordinates and dual testing -/

section Coordinates

/-- **Codomain basis characterization.** Membership in `MemW1pLoc p Ω` into a space with a finite
basis `b` is equivalent to membership of every scalar coordinate `x ↦ b.repr (u x) i`. -/
theorem _root_.Module.Basis.memW1pLoc_iff {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Finite ι] {μ : Measure E} {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (b : Module.Basis ι ℝ F) :
    MemW1pLoc p Ω u μ ↔ ∀ i, MemW1pLoc p Ω (fun x => b.repr (u x) i) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemW1pLoc p Ω (fun x => ∑ i, b.repr (u x) i • b i) μ :=
      MemW1pLoc.sum Finset.univ fun i _ => (h i).smul_const (b i)
    simpa only [b.sum_repr] using hs

/-- **Domain basis characterization (partial derivatives).** Given a finite basis `b` of `E`,
`u ∈ MemW1pLoc p Ω` if and only if `u ∈ MemLpLoc p Ω` and, in each basis direction `b i`, `u` has
a weak directional derivative `u_i` on `Ω` belonging to `MemLpLoc p Ω`. Completeness of `F` and
finite measure on compacts handle the zero-dimensional domain (`IsEmpty ι`). -/
theorem _root_.Module.Basis.memW1pLoc_iff_apply {E F ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Finite ι]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (b : Module.Basis ι ℝ E) :
    MemW1pLoc p Ω u μ ↔
      MemLpLoc p Ω u μ ∧
        ∀ i, ∃ u' : E → F, HasWeakLineDerivOn μ Ω u u' (b i) ∧ MemLpLoc p Ω u' μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  constructor
  · rintro ⟨huLp, Du, hDu, hDuLp⟩
    exact ⟨huLp, fun i => ⟨fun x => Du x (b i), hDu.hasWeakLineDerivOn (b i),
      hDuLp.clm_comp (ContinuousLinearMap.apply ℝ F (b i))⟩⟩
  · rintro ⟨huLp, h⟩
    choose u' hu' hu'Lp using h
    have huLoc : LocallyIntegrableOn u Ω μ := by
      rcases isEmpty_or_nonempty ι with h0 | ⟨⟨i₀⟩⟩
      · have : Subsingleton E := b.repr.toEquiv.subsingleton
        have huc : u = fun _ => u 0 := funext fun x => congrArg u (Subsingleton.elim x 0)
        rw [huc]
        exact (integrableOn_const
          (hs := (Set.toFinite (Ω : Set E)).isCompact.measure_lt_top.ne)).locallyIntegrableOn
      · exact (hu' i₀).locallyIntegrableOn
    let coordCLM : ι → E →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
    let Du : E → E →L[ℝ] F := fun x => ∑ i, (coordCLM i).smulRight (u' i x)
    have hDu_apply : ∀ i x, Du x (b i) = u' i x := fun i x => by
      simp [Du, coordCLM, b.coord_apply, b.repr_self, Finsupp.single_apply]
    have hDu : HasWeakFDerivOn μ Ω u Du :=
      b.hasWeakFDerivOn_of_forall huLoc fun i => by simpa only [hDu_apply] using hu' i
    have hDuLp : MemLpLoc p Ω Du μ :=
      MemLpLoc.sum Finset.univ fun i _ =>
        (hu'Lp i).clm_comp (ContinuousLinearMap.smulRightL ℝ ℝ ℝ E F (coordCLM i))
    exact ⟨huLp, Du, hDu, hDuLp⟩

/-- **Testing `MemW1pLoc` against the continuous dual.** For `1 ≤ p` and a complete codomain `F`,
once `u : E → F` and a candidate `Du : E → E →L[ℝ] F` already belong to `MemLpLoc p Ω`, testing
`ℓ ∘ Du` as weak derivative of `ℓ ∘ u` for every `ℓ : StrongDual ℝ F` certifies `MemW1pLoc p Ω u`.
Prior `MemLpLoc` membership cannot be dropped in infinite dimensions
(see `TauCeti.forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle` in
`TauCeti.Analysis.Sobolev.Local.FirstOrder.Examples`). -/
theorem MemLpLoc.memW1pLoc_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}
    (hu : MemLpLoc p Ω u μ) (hDu : MemLpLoc p Ω Du μ) (hp : 1 ≤ p)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn μ Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (Du x))) :
    MemW1pLoc p Ω u μ :=
  ⟨hu, Du, hasWeakFDerivOn_of_forall_strongDual
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)
    (fun v => (hDu.clm_comp (ContinuousLinearMap.apply ℝ F v)).locallyIntegrableOn hp
      Ω.isOpen.isLocallyClosed) h, hDu⟩

/-- **Characterization of `MemW1pLoc` through the continuous dual.** For `1 ≤ p` and a complete
codomain `F`, `u ∈ MemW1pLoc p Ω` if and only if `u ∈ MemLpLoc p Ω` and there exists
`Du ∈ MemLpLoc p Ω` such that `ℓ ∘ Du` is a weak derivative of `ℓ ∘ u` on `Ω` for every
`ℓ : StrongDual ℝ F`. -/
theorem memW1pLoc_iff_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (hp : 1 ≤ p) :
    MemW1pLoc p Ω u μ ↔
      MemLpLoc p Ω u μ ∧ ∃ Du : E → E →L[ℝ] F, MemLpLoc p Ω Du μ ∧
        ∀ ℓ : StrongDual ℝ F,
          HasWeakFDerivOn μ Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (Du x)) := by
  refine ⟨fun ⟨hu, Du, hDu, hDuLp⟩ => ⟨hu, Du, hDuLp, fun ℓ => hDu.clm_comp (ℓ : F →L[ℝ] ℝ)⟩, ?_⟩
  rintro ⟨hu, Du, hDuLp, h⟩
  exact hu.memW1pLoc_of_forall_strongDual hDuLp hp h

end Coordinates

/-! ### Haar-measure independence and linear invariance -/

section HaarAndLinear

/-- **Haar-measure independence of `MemW1pLoc`.** On a finite-dimensional real normed space,
`MemW1pLoc` does not depend on the choice of Borel additive Haar measure. -/
theorem memW1pLoc_iff_of_isAddHaarMeasure {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    MemW1pLoc p Ω u μ ↔ MemW1pLoc p Ω u ν := by
  simp only [memW1pLoc_iff, memLpLoc_iff_of_isAddHaarMeasure μ ν,
    hasWeakFDerivOn_iff_of_isAddHaarMeasure μ ν]

/-- Multiplying the measure by a finite nonzero constant leaves `MemW1pLoc` unchanged. -/
theorem memW1pLoc_smul_measure_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ⊤) {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    MemW1pLoc p Ω u (c • μ) ↔ MemW1pLoc p Ω u μ := by
  simp only [memW1pLoc_iff, memLpLoc_smul_measure_iff hc₀ hc,
    hasWeakFDerivOn_smul_measure_iff hc₀ hc]

/-- **Precomposition with a continuous linear equivalence in `MemW1pLoc`.** Any continuous linear
equivalence `e : E₁ ≃L[ℝ] E` between finite-dimensional real normed spaces carrying Borel additive
Haar measures pulls `MemW1pLoc p V` back to `MemW1pLoc p U` whenever `MapsTo e U V`. -/
theorem MemW1pLoc.comp_continuousLinearEquiv {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasurableSpace E₁] [BorelSpace E₁]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E₁} [μ.IsAddHaarMeasure] {ν : Measure E} [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Opens E₁} {V : Opens E} {u : E → F}
    (hu : MemW1pLoc p V u ν) (e : E₁ ≃L[ℝ] E) (hUV : MapsTo e U V) :
    MemW1pLoc p U (u ∘ e) μ := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  refine ⟨((e.memLpLoc_comp_right_iff μ ν).2 huLp).mono_set hUV,
    fun x => (Du (e x)).comp (e : E₁ →L[ℝ] E),
    hDu.comp_continuousLinearEquiv_of_isAddHaarMeasure e hUV, ?_⟩
  exact (((e.memLpLoc_comp_right_iff μ ν).2 hDuLp).mono_set hUV).clm_comp
    ((ContinuousLinearMap.compL ℝ E₁ E F).flip (e : E₁ →L[ℝ] E))

/-- **Linear and norm invariance of `MemW1pLoc`.** For any continuous linear equivalence
`e : E₁ ≃L[ℝ] E` between finite-dimensional real normed spaces carrying Borel additive Haar
measures, `u ∘ e ∈ MemW1pLoc p (Ω.comap (e.toHomeomorph : C(E₁, E)))` if and only if
`u ∈ MemW1pLoc p Ω`. -/
theorem _root_.ContinuousLinearEquiv.memW1pLoc_comp_iff {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasurableSpace E₁] [BorelSpace E₁] {μ : Measure E₁} [μ.IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [ν.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (e : E₁ ≃L[ℝ] E) :
    MemW1pLoc p (Ω.comap (e.toHomeomorph : C(E₁, E))) (u ∘ e) μ ↔ MemW1pLoc p Ω u ν := by
  refine ⟨fun h => ?_, fun h =>
    h.comp_continuousLinearEquiv e (mapsTo_preimage e (Ω : Set E))⟩
  have hVU : MapsTo e.symm Ω (Ω.comap (e.toHomeomorph : C(E₁, E))) := fun y hy => by
    simpa using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv (ν := μ) (μ := ν) e.symm hVU

/-- **Equivalence of supremum and Euclidean norms on `ℝⁿ`.** Identifying `(Fin n → ℝ)` (carrying the
supremum norm) with `EuclideanSpace ℝ (Fin n)` (carrying the `ℓ²` norm) via `WithLp.toLp 2`
preserves and reflects `MemW1pLoc`. -/
theorem memW1pLoc_comp_toLp_iff {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Opens (Fin n → ℝ)} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → F} (hU : (U : Set (Fin n → ℝ)) = WithLp.toLp 2 ⁻¹' Ω) :
    MemW1pLoc p U (u ∘ WithLp.toLp 2) ↔ MemW1pLoc p Ω u := by
  let e : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).symm
  have he : ⇑e = WithLp.toLp 2 := PiLp.coe_symm_continuousLinearEquiv 2 ℝ _
  have hUe : U = Ω.comap (e.toHomeomorph : C(Fin n → ℝ, EuclideanSpace ℝ (Fin n))) :=
    SetLike.ext' <| by
      rw [hU, ← he, Opens.coe_comap, ContinuousMap.coe_ofClass, e.coe_toHomeomorph]
  rw [hUe, ← he]
  exact e.memW1pLoc_comp_iff

end HaarAndLinear

end TauCeti
