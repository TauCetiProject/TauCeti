/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.Hyperplane
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# First-order local Sobolev classes on Euclidean domains

For an open subset `Ω` of a real normed space `E` carrying a `MeasureSpace` instance and a real
normed codomain `F`, a map `u : E → F` belongs to the first-order local Sobolev class
`TauCeti.MemW1pLoc p Ω u` when `u` is locally `Lᵖ` on `Ω` (`TauCeti.MemLpLoc p Ω u`) and admits a
weak Fréchet derivative `Du : E → E →L[ℝ] F` on `Ω` (`TauCeti.HasWeakFDerivOn volume Ω u Du`) that
is itself locally `Lᵖ` on `Ω`.

The definition applies to actual functions without quotienting by almost-everywhere equality and
imposes no global integrability condition on `Ω`. Completeness of `F` is not a typeclass argument
on `MemW1pLoc`; it is carried by `HasWeakFDerivOn` and recovered by
`TauCeti.MemW1pLoc.completeSpace`. On open subsets of `ℂ`, `MemW1pLoc p Ω u` agrees with the
order-one planar class `TauCeti.MemWkpLoc p Ω 1 u` (`TauCeti.memWkpLoc_one_iff_memW1pLoc`).

## Main results

* **Uniqueness transfer and measurability.** By almost-everywhere uniqueness of weak derivatives
  (`TauCeti.HasWeakFDerivOn.ae_eq`), *every* weak derivative of `u ∈ MemW1pLoc p Ω` on `Ω` belongs
  to `MemLpLoc p Ω` (`TauCeti.MemW1pLoc.memLpLoc_of_hasWeakFDerivOn`). Every member is locally
  integrable (`TauCeti.MemW1pLoc.locallyIntegrableOn`) and, on locally compact second-countable
  domains, almost-everywhere strongly measurable (`TauCeti.MemW1pLoc.aestronglyMeasurable_restrict`)
  for all exponents `p : ℝ≥0∞`.
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
  exponent `p`, with classical Fréchet derivative as weak derivative.
* **Sheaf property and locality.** On finite-dimensional Borel spaces with complete codomain,
  `MemW1pLoc` satisfies the sheaf condition on arbitrary open covers (`TauCeti.memW1pLoc_iSup_iff`)
  and is detected on open neighbourhoods of each point (`TauCeti.memW1pLoc_iff_locally`).
* **Coordinates and dual testing.** Membership is detected in any finite basis of the codomain
  (`Module.Basis.memW1pLoc_iff`) and by directional weak derivatives along any finite basis of the
  domain (`Module.Basis.memW1pLoc_iff_apply`). For an arbitrary Banach codomain and `1 ≤ p`,
  testing against `StrongDual ℝ F` characterizes `MemW1pLoc` *once* `u` and its candidate derivative
  lie in `MemLpLoc p Ω` (`TauCeti.memW1pLoc_iff_forall_strongDual`,
  `TauCeti.MemLpLoc.memW1pLoc_of_forall_strongDual`); without prior Bochner strong measurability,
  `t ↦ lp.single 2 t 1` into non-separable `ℓ²(ℝ)` satisfies scalar `MemW1pLoc p ⊤` after every
  continuous linear functional while failing `MemLpLoc p Set.univ`
  (`TauCeti.forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle`, cf. Arendt–Kreuter).
* **Haar-measure and linear invariance.** On finite-dimensional real normed spaces, `MemLpLoc` and
  `MemW1pLoc` are independent of the choice of additive Haar measure and are preserved and reflected
  by every continuous linear equivalence `e : E₁ ≃L[ℝ] E`
  (`ContinuousLinearEquiv.memW1pLoc_comp_iff`), regardless of Jacobian determinant or choice of
  equivalent norm (`TauCeti.memW1pLoc_comp_toLp_iff`).
* **Sharpness checks.** The identity is in `MemW1pLoc p Ω` without belonging to global `Lᵖ` for
  `p ≠ 0` on a nontrivial space; `x ↦ ‖x‖` lies in `MemW1pLoc p Ω` for all `p` (with
  non-inner-product derivative on `(Fin 2 → ℝ)` equipped with the supremum norm); the unit radial
  map `x ↦ ‖x‖⁻¹ • x` on an inner product space of dimension `d ≥ 2` with `0 ∈ Ω` belongs to
  `MemW1pLoc p Ω` if and only if `p < d` (`TauCeti.memW1pLoc_norm_inv_smul_iff`); and the indicator
  of an open half-space `{x | 0 < ℓ x}` (`ℓ ≠ 0`) belongs to `MemLpLoc p Ω` for all `p` but never to
  `MemW1pLoc p Ω` when `Ω` meets `{x | ℓ x = 0}` (`TauCeti.not_memW1pLoc_indicator_pos`).

## References

* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §2.1–§2.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299 (Bochner strong measurability vs. scalar weak differentiability).
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology RealInnerProductSpace

namespace TauCeti

section Basic

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p q : ℝ≥0∞} {Ω Ω' : Opens E} {u v : E → F}

/-- A map `u : E → F` on an open set `Ω ⊆ E` belongs to the first-order local Sobolev class
`MemW1pLoc p Ω u` when `u` is locally `Lᵖ` on `Ω` and has a weak Fréchet derivative on `Ω` that is
also locally `Lᵖ` on `Ω`. -/
def MemW1pLoc (p : ℝ≥0∞) (Ω : Opens E) (u : E → F) : Prop :=
  MemLpLoc p Ω u ∧ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω u Du ∧ MemLpLoc p Ω Du

/-- Unfolding characterization of `MemW1pLoc`. -/
theorem memW1pLoc_iff :
    MemW1pLoc p Ω u ↔
      MemLpLoc p Ω u ∧ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω u Du ∧ MemLpLoc p Ω Du :=
  Iff.rfl

/-- Every member of `MemW1pLoc p Ω` belongs to `MemLpLoc p Ω`. -/
theorem MemW1pLoc.memLpLoc (hu : MemW1pLoc p Ω u) : MemLpLoc p Ω u :=
  hu.1

/-- Every member of `MemW1pLoc p Ω` admits a weak Fréchet derivative in `MemLpLoc p Ω`. -/
theorem MemW1pLoc.exists_hasWeakFDerivOn (hu : MemW1pLoc p Ω u) :
    ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω u Du ∧ MemLpLoc p Ω Du :=
  hu.2

/-- Membership in `MemW1pLoc` supplies completeness of the codomain, inherited from
`HasWeakFDerivOn`. -/
theorem MemW1pLoc.completeSpace (hu : MemW1pLoc p Ω u) : CompleteSpace F := by
  obtain ⟨_, hDu, _⟩ := hu.exists_hasWeakFDerivOn
  exact hDu.completeSpace

/-- On open subsets of `ℂ`, the order-one planar class `MemWkpLoc p Ω 1` is `MemW1pLoc p Ω`. -/
@[simp]
theorem memWkpLoc_one_iff_memW1pLoc {Ω : Opens ℂ} {u : ℂ → F} :
    MemWkpLoc p Ω 1 u ↔ MemW1pLoc p Ω u := by
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff, memW1pLoc_iff]

/-- Every weak derivative of a member of `MemW1pLoc p Ω` is locally `Lᵖ` on `Ω`, not only the
existential witness, since weak derivatives on `Ω` agree almost everywhere. -/
theorem MemW1pLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hu : MemW1pLoc p Ω u) {Du : E → E →L[ℝ] F} (hDu : HasWeakFDerivOn volume Ω u Du) :
    MemLpLoc p Ω Du := by
  obtain ⟨Du', hDu', hLp⟩ := hu.exists_hasWeakFDerivOn
  exact hLp.congr_ae (hDu'.ae_eq hDu)

/-- Every member of `MemW1pLoc p Ω` is locally integrable on `Ω` for *every* exponent `p : ℝ≥0∞`,
since local integrability is part of `HasWeakFDerivOn`. -/
theorem MemW1pLoc.locallyIntegrableOn (hu : MemW1pLoc p Ω u) :
    LocallyIntegrableOn u Ω volume := by
  obtain ⟨_, hDu, _⟩ := hu.exists_hasWeakFDerivOn
  exact hDu.locallyIntegrableOn

/-- On a locally compact second-countable domain, every member of `MemW1pLoc p Ω` is
almost-everywhere strongly measurable on `Ω`, for every exponent `p : ℝ≥0∞`. -/
theorem MemW1pLoc.aestronglyMeasurable_restrict [LocallyCompactSpace E] [SecondCountableTopology E]
    (hu : MemW1pLoc p Ω u) : AEStronglyMeasurable u (volume.restrict Ω) :=
  hu.memLpLoc.aestronglyMeasurable_restrict Ω.isOpen.isLocallyClosed

/-- `MemW1pLoc` restricts to any smaller open subset. -/
theorem MemW1pLoc.mono (hu : MemW1pLoc p Ω u) (hΩ : Ω' ≤ Ω) : MemW1pLoc p Ω' u := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.mono_set hΩ, Du, hDu.mono hΩ, hDuLp.mono_set hΩ⟩

/-- Almost-everywhere equality on `Ω` preserves `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.congr_ae (hu : MemW1pLoc p Ω u) (huv : u =ᵐ[volume.restrict Ω] v) :
    MemW1pLoc p Ω v := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.congr_ae huv, Du, hDu.congr_ae huv, hDuLp⟩

/-- Restricting to a smaller open subset preserves `MemW1pLoc` for any map agreeing with the
original one there. -/
theorem MemW1pLoc.congr_mono [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u)
    (hvu : Set.EqOn v u Ω') (hΩ : Ω' ≤ Ω) : MemW1pLoc p Ω' v :=
  (hu.mono hΩ).congr_ae <| by
    filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with x hx using (hvu hx).symm

/-- `MemW1pLoc p Ω` depends only on the values of the map on `Ω`. -/
theorem MemW1pLoc.congr [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u) (hvu : Set.EqOn v u Ω) :
    MemW1pLoc p Ω v :=
  hu.congr_mono hvu le_rfl

/-- Decreasing the exponent preserves `MemW1pLoc` whenever compact subsets have finite measure. -/
theorem MemW1pLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hu : MemW1pLoc p Ω u) (hqp : q ≤ p) : MemW1pLoc q Ω u := by
  obtain ⟨hLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨hLp.mono_exponent hqp, Du, hDu, hDuLp.mono_exponent hqp⟩

/-! ### Algebraic and linear operations -/

/-- The zero map belongs to `MemW1pLoc p Ω` for every complete codomain. -/
@[simp]
theorem memW1pLoc_zero [CompleteSpace F] : MemW1pLoc p Ω (0 : E → F) :=
  ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, memLpLoc_zero⟩

/-- Every constant map belongs to `MemW1pLoc p Ω` on a finite-dimensional space with a Borel
additive Haar measure. -/
@[simp]
theorem memW1pLoc_const [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (c : F) :
    MemW1pLoc p Ω (fun _ => c) :=
  ⟨memLpLoc_const c, 0, hasWeakFDerivOn_iff.2 fun w =>
    hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := w) c, memLpLoc_zero⟩

/-- `MemW1pLoc` is closed under addition. -/
theorem MemW1pLoc.add [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u) (hv : MemW1pLoc p Ω v) :
    MemW1pLoc p Ω (u + v) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  obtain ⟨hvLp, Dv, hDv, hDvLp⟩ := hv
  exact ⟨huLp.add hvLp, Du + Dv, hDu.add hDv, hDuLp.add hDvLp⟩

/-- `MemW1pLoc` is closed under negation. -/
theorem MemW1pLoc.neg (hu : MemW1pLoc p Ω u) : MemW1pLoc p Ω (-u) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.neg, -Du, hDu.neg, hDuLp.neg⟩

/-- `MemW1pLoc` is closed under subtraction. -/
theorem MemW1pLoc.sub [OpensMeasurableSpace E] (hu : MemW1pLoc p Ω u) (hv : MemW1pLoc p Ω v) :
    MemW1pLoc p Ω (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- `MemW1pLoc` is closed under real scalar multiplication. -/
theorem MemW1pLoc.const_smul (hu : MemW1pLoc p Ω u) (c : ℝ) : MemW1pLoc p Ω (c • u) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.const_smul c, c • Du, hDu.const_smul c, hDuLp.const_smul c⟩

/-- Finite sums preserve `MemW1pLoc`. -/
theorem MemW1pLoc.sum {ι : Type*} [OpensMeasurableSpace E] [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemW1pLoc p Ω (f i)) :
    MemW1pLoc p Ω (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memW1pLoc_zero (p := p) (Ω := Ω))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Postcomposition with a continuous linear map into a complete codomain preserves `MemW1pLoc`. -/
theorem MemW1pLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hu : MemW1pLoc p Ω u)
    (L : F →L[ℝ] G) : MemW1pLoc p Ω (fun x => L (u x)) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  exact ⟨huLp.clm_comp L, fun x => L.comp (Du x), hDu.clm_comp L,
    hDuLp.clm_comp ((ContinuousLinearMap.compL ℝ E F G) L)⟩

/-- Postcomposition with a continuous linear equivalence preserves and reflects `MemW1pLoc`,
transferring completeness between codomains automatically. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memW1pLoc_iff [OpensMeasurableSpace E] (e : F ≃L[ℝ] G) :
    MemW1pLoc p Ω (fun x => e (u x)) ↔ MemW1pLoc p Ω u := by
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
theorem MemW1pLoc.smulRight [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemW1pLoc p Ω a) (v : F) : MemW1pLoc p Ω (fun x => a x • v) :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- Pairing two maps in `MemW1pLoc p Ω` produces a product-valued map in `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.prodMk [OpensMeasurableSpace E] {w : E → G} (hu : MemW1pLoc p Ω u)
    (hw : MemW1pLoc p Ω w) : MemW1pLoc p Ω (fun x => (u x, w x)) := by
  have : CompleteSpace F := hu.completeSpace
  have : CompleteSpace G := hw.completeSpace
  have h := (hu.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hw.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext x <;> simp

/-- Pointwise product of two operator fields in `MemW1pLoc p Ω`. -/
theorem MemW1pLoc.prodMap {E₁ E₂ E₃ E₄ : Type*} [OpensMeasurableSpace E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemW1pLoc p Ω A) (hB : MemW1pLoc p Ω B) :
    MemW1pLoc p Ω (fun x => (A x).prodMap (B x)) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-! ### Classical differentiability and Lipschitz maps -/

/-- A map continuous on `Ω` lies in `MemW1pLoc p Ω` if and only if it admits a weak derivative on
`Ω` lying in `MemLpLoc p Ω`. -/
theorem _root_.ContinuousOn.memW1pLoc_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hu : ContinuousOn u Ω) :
    MemW1pLoc p Ω u ↔ ∃ Du : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω u Du ∧ MemLpLoc p Ω Du :=
  ⟨MemW1pLoc.exists_hasWeakFDerivOn, fun h => ⟨hu.memLpLoc, h⟩⟩

/-- On a finite-dimensional space with a Borel additive Haar measure, a map differentiable on `Ω`
with continuous Fréchet derivative on `Ω` belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.DifferentiableOn.memW1pLoc_of_continuousOn_fderiv [FiniteDimensional ℝ E]
    [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F]
    (hu : DifferentiableOn ℝ u Ω) (hDu : ContinuousOn (fderiv ℝ u) Ω) : MemW1pLoc p Ω u :=
  ⟨hu.continuousOn.memLpLoc, fderiv ℝ u,
    hasWeakFDerivOn_of_differentiableOn (hDu.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun _ hx => hu.differentiableAt (Ω.isOpen.mem_nhds hx),
    hDu.memLpLoc⟩

/-- A `C¹` map on `Ω` belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.ContDiffOn.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hu : ContDiffOn ℝ 1 u Ω) :
    MemW1pLoc p Ω u :=
  ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    (hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).memLpLoc⟩

/-- A globally `C¹` map belongs to `MemW1pLoc p Ω` on every open set and for every exponent `p`. -/
theorem _root_.ContDiff.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hu : ContDiff ℝ 1 u) :
    MemW1pLoc p Ω u :=
  hu.contDiffOn.memW1pLoc

/-- Every continuous linear map belongs to `MemW1pLoc p Ω` for every exponent `p`. -/
theorem _root_.ContinuousLinearMap.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (L : E →L[ℝ] F) :
    MemW1pLoc p Ω L :=
  L.contDiff.memW1pLoc

/-- If a `C¹` map `g` on `Ω` agrees almost everywhere on `Ω` with `u ∈ MemW1pLoc p Ω`, then
`fderiv ℝ g` is a weak derivative of `u` on `Ω` and belongs to `MemLpLoc p Ω`. -/
theorem MemW1pLoc.hasWeakFDerivOn_fderiv_of_contDiffOn [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {g : E → F} (hu : MemW1pLoc p Ω u)
    (hg : ContDiffOn ℝ 1 g Ω) (hug : u =ᵐ[volume.restrict Ω] g) :
    HasWeakFDerivOn volume Ω u (fderiv ℝ g) ∧ MemLpLoc p Ω (fderiv ℝ g) := by
  have := hu.completeSpace
  have hg' : HasWeakFDerivOn volume Ω g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  exact ⟨hg'.congr_ae hug.symm, hu.memLpLoc_of_hasWeakFDerivOn (hg'.congr_ae hug.symm)⟩

/-- **Rademacher's theorem in `MemW1pLoc`.** A map locally Lipschitz on `Ω` between
finite-dimensional real normed spaces belongs to `MemW1pLoc p Ω` for every exponent `p`, with weak
derivative `fderiv ℝ u`. -/
theorem _root_.LocallyLipschitzOn.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
    (hu : LocallyLipschitzOn Ω u) : MemW1pLoc p Ω u := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  refine ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    memLpLoc_iff.2 fun L hLΩ hL => ?_⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hL.exists_cthickening_subset_open Ω.isOpen hLΩ
  obtain ⟨C, hC⟩ := (hu.mono hδΩ).exists_lipschitzOnWith_of_compact hL.cthickening
  have : IsFiniteMeasure (volume.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
  refine MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hL.measurableSet] with x hx
  have hnhds : cthickening δ L ∈ 𝓝 x :=
    mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx))
      (thickening_subset_cthickening _ _)
  exact norm_fderiv_le_of_lipschitzOn ℝ hnhds hC

/-- A map Lipschitz on `Ω` between finite-dimensional real normed spaces belongs to `MemW1pLoc p Ω`
for every exponent `p`. -/
theorem _root_.LipschitzOnWith.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F] {K : ℝ≥0}
    (hu : LipschitzOnWith K u Ω) : MemW1pLoc p Ω u :=
  LocallyLipschitzOn.memW1pLoc fun _ _ => ⟨K, Ω, self_mem_nhdsWithin, hu⟩

/-- A globally Lipschitz map between finite-dimensional real normed spaces belongs to
`MemW1pLoc p Ω` on every open set and for every exponent `p`. -/
theorem _root_.LipschitzWith.memW1pLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F] {K : ℝ≥0}
    (hu : LipschitzWith K u) : MemW1pLoc p Ω u :=
  hu.locallyLipschitz.locallyLipschitzOn.memW1pLoc

/-! ### Sheaf and locality properties -/

/-- **Sheaf property for `MemW1pLoc`.** On a finite-dimensional Borel space with complete codomain,
`MemW1pLoc p` on a union of open sets is equivalent to `MemW1pLoc p` on each member of the cover.
Completeness of `F` is assumed so that the equivalence holds for an empty cover. -/
theorem memW1pLoc_iSup_iff [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {ι : Type*} (V : ι → Opens E) :
    MemW1pLoc p (⨆ i, V i) u ↔ ∀ i, MemW1pLoc p (V i) u := by
  refine ⟨fun hu i => hu.mono (le_iSup V i), fun h => ?_⟩
  choose D hD hDLp using fun i => (h i).exists_hasWeakFDerivOn
  obtain ⟨G, hG, hGD⟩ := exists_hasWeakFDerivOn_iSup V D hD
  refine ⟨(memLpLoc_iSup_iff V).2 fun i => (h i).memLpLoc, G, hG,
    (memLpLoc_iSup_iff V).2 fun i => (hDLp i).congr_ae (hGD i).symm⟩

/-- **Pointwise locality of `MemW1pLoc`.** Membership on `Ω` holds if and only if every point of
`Ω` has an open neighbourhood inside `Ω` on which membership holds. -/
theorem memW1pLoc_iff_locally [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    MemW1pLoc p Ω u ↔ ∀ x ∈ Ω, ∃ W : Opens E, x ∈ W ∧ W ≤ Ω ∧ MemW1pLoc p W u := by
  refine ⟨fun hu x hx => ⟨Ω, hx, le_rfl, hu⟩, fun h => ?_⟩
  choose W hxW hWΩ hWu using fun x : Ω => h x.1 x.2
  have hsup : (⨆ x : Ω, W x) = Ω :=
    le_antisymm (iSup_le hWΩ) fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  exact hsup ▸ (memW1pLoc_iSup_iff W).2 hWu

end Basic

/-! ### Coordinates and dual testing -/

section Coordinates

/-- **Codomain basis characterization.** Membership in `MemW1pLoc p Ω` into a space with a finite
basis `b` is equivalent to membership of every scalar coordinate `x ↦ b.repr (u x) i`. -/
theorem _root_.Module.Basis.memW1pLoc_iff {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (b : Module.Basis ι ℝ F) :
    MemW1pLoc p Ω u ↔ ∀ i, MemW1pLoc p Ω (fun x => b.repr (u x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemW1pLoc p Ω (fun x => ∑ i, b.repr (u x) i • b i) :=
      MemW1pLoc.sum Finset.univ fun i _ => (h i).smulRight (b i)
    simpa only [b.sum_repr] using hs

/-- **Domain basis characterization (partial derivatives).** Given a finite basis `b` of `E`,
`u ∈ MemW1pLoc p Ω` if and only if `u ∈ MemLpLoc p Ω` and, in each basis direction `b i`, `u` has
a weak directional derivative `u_i` on `Ω` belonging to `MemLpLoc p Ω`. Completeness of `F` and
finite measure on compacts handle the zero-dimensional domain (`IsEmpty ι`). -/
theorem _root_.Module.Basis.memW1pLoc_iff_apply {E F ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Finite ι]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (b : Module.Basis ι ℝ E) :
    MemW1pLoc p Ω u ↔
      MemLpLoc p Ω u ∧
        ∀ i, ∃ u' : E → F, HasWeakLineDerivOn volume Ω u u' (b i) ∧ MemLpLoc p Ω u' := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  constructor
  · rintro ⟨huLp, Du, hDu, hDuLp⟩
    exact ⟨huLp, fun i => ⟨fun x => Du x (b i), hDu.hasWeakLineDerivOn (b i),
      hDuLp.clm_comp (ContinuousLinearMap.apply ℝ F (b i))⟩⟩
  · rintro ⟨huLp, h⟩
    choose u' hu' hu'Lp using h
    have huLoc : LocallyIntegrableOn u Ω volume := by
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
    have hDu : HasWeakFDerivOn volume Ω u Du :=
      b.hasWeakFDerivOn_of_forall huLoc fun i => by simpa only [hDu_apply] using hu' i
    have hDuLp : MemLpLoc p Ω Du :=
      MemLpLoc.sum Finset.univ fun i _ =>
        (hu'Lp i).clm_comp (ContinuousLinearMap.smulRightL ℝ E F (coordCLM i))
    exact ⟨huLp, Du, hDu, hDuLp⟩

/-- **Testing `MemW1pLoc` against the continuous dual.** For `1 ≤ p` and a complete codomain `F`,
once `u : E → F` and a candidate `Du : E → E →L[ℝ] F` already belong to `MemLpLoc p Ω`, testing
`ℓ ∘ Du` as weak derivative of `ℓ ∘ u` for every `ℓ : StrongDual ℝ F` certifies `MemW1pLoc p Ω u`
with weak derivative `Du`. Prior `MemLpLoc` membership cannot be dropped in infinite dimensions
(see `TauCeti.forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle`). -/
theorem MemLpLoc.memW1pLoc_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}
    (hu : MemLpLoc p Ω u) (hDu : MemLpLoc p Ω Du) (hp : 1 ≤ p)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn volume Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (Du x))) :
    MemW1pLoc p Ω u :=
  ⟨hu, Du, hasWeakFDerivOn_of_forall_strongDual
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)
    (fun v => (hDu.clm_comp (ContinuousLinearMap.apply ℝ F v)).locallyIntegrableOn hp
      Ω.isOpen.isLocallyClosed) h, hDu⟩

/-- **Characterization of `MemW1pLoc` through the continuous dual.** For `1 ≤ p` and a complete
codomain `F`, `u ∈ MemW1pLoc p Ω` if and only if `u ∈ MemLpLoc p Ω` and there exists
`Du ∈ MemLpLoc p Ω` such that `ℓ ∘ Du` is a weak derivative of `ℓ ∘ u` on `Ω` for every
`ℓ : StrongDual ℝ F`. -/
theorem memW1pLoc_iff_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (hp : 1 ≤ p) :
    MemW1pLoc p Ω u ↔
      MemLpLoc p Ω u ∧ ∃ Du : E → E →L[ℝ] F, MemLpLoc p Ω Du ∧
        ∀ ℓ : StrongDual ℝ F,
          HasWeakFDerivOn volume Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (Du x)) := by
  refine ⟨fun ⟨hu, Du, hDu, hDuLp⟩ => ⟨hu, Du, hDuLp, fun ℓ => hDu.clm_comp (ℓ : F →L[ℝ] ℝ)⟩, ?_⟩
  rintro ⟨hu, Du, hDuLp, h⟩
  exact hu.memW1pLoc_of_forall_strongDual hDuLp hp h

/-- **Scalar Sobolev regularity does not imply Bochner measurability.** Let
`u : ℝ → lp (fun _ : ℝ => ℝ) 2` send `t` to the basis vector `lp.single 2 t 1` in non-separable
`ℓ²(ℝ)`. Every continuous linear functional `ℓ` vanishes on `u t` outside a countable set, so
`ℓ ∘ u =ᵐ[volume] 0` and `MemW1pLoc p ⊤ (ℓ ∘ u)` holds for every `p : ℝ≥0∞`; yet `u` has discrete
uncountable essential range on `[0, 1]`, so `u` fails `MemLpLoc p Set.univ` (and hence
`MemW1pLoc p ⊤`) for every `p : ℝ≥0∞`. -/
theorem forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle (p : ℝ≥0∞) :
    (∀ ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2),
      MemW1pLoc p ⊤ (fun t : ℝ => ℓ (lp.single 2 t (1 : ℝ)))) ∧
    ¬ MemLpLoc p (Set.univ : Set ℝ) (fun t : ℝ => lp.single 2 t (1 : ℝ)) := by
  classical
  set H := lp (fun _ : ℝ => ℝ) 2
  set u : ℝ → H := fun t => lp.single 2 t (1 : ℝ)
  constructor
  · intro ℓ
    let w : H := (InnerProductSpace.toDual ℝ H).symm ℓ
    have hw_eval : ∀ t : ℝ, ℓ (u t) = w t := fun t => by
      have h1 : ℓ (u t) = ⟪w, lp.single 2 t (1 : ℝ)⟫ := by simp [u, w]
      rw [h1, lp.inner_single_right]
      simp
    have hcnt : (Function.support fun t : ℝ => (w : ℝ → ℝ) t).Countable := by
      have hs : Summable fun t : ℝ => ‖(w : ℝ → ℝ) t‖ ^ (2 : ℝ≥0∞).toReal :=
        (lp.memℓp w).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      refine hs.countable_support.mono fun t ht => ?_
      simp [ht]
    have hae : (0 : ℝ → ℝ) =ᵐ[volume.restrict (⊤ : Opens ℝ)] fun t : ℝ => ℓ (u t) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [compl_mem_ae_iff.2 (hcnt.measure_zero _)] with t ht
      rw [Pi.zero_apply, hw_eval]
      exact (Function.notMem_support.1 ht).symm
    exact (memW1pLoc_zero (p := p) (Ω := (⊤ : Opens ℝ)) (F := ℝ)).congr_ae hae
  · intro hu
    have hmeas : AEStronglyMeasurable u (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLpLoc_iff.1 hu (Icc 0 1) (subset_univ _) isCompact_Icc).aestronglyMeasurable
    obtain ⟨t, ht_sep, ht_ae⟩ := hmeas.isSeparable_ae_range
    have hpair : PairwiseDisjoint (u ⁻¹' t) fun x : ℝ => ball (u x) ((1 : ℝ) / 2) := by
      intro x _ y _ hxy
      refine Set.disjoint_left.2 fun z hzx hzy => ?_
      have hsub : 1 ≤ ‖u x - u y‖ := by
        have hle : |(u x - u y) x| ≤ ‖u x - u y‖ := lp.norm_apply_le_norm two_ne_zero (u x - u y) x
        have heval : (u x - u y) x = 1 := by simp [u, lp.single_apply, hxy]
        simpa [heval] using hle
      have htri : dist (u x) (u y) ≤ dist (u x) z + dist z (u y) := dist_triangle _ _ _
      have hdx : dist (u x) z < 1 / 2 := by simpa [dist_comm] using mem_ball.1 hzx
      have hdy : dist z (u y) < 1 / 2 := mem_ball.1 hzy
      linarith [dist_eq_norm (u x) (u y)]
    have hcnt_pre : (u ⁻¹' t).Countable := by
      have hsep_img : IsSeparable (u '' (u ⁻¹' t)) := ht_sep.mono (image_preimage_subset u t)
      obtain ⟨s, hsc, hsub⟩ := hsep_img
      -- Every open ball of radius `1 / 2` around `u x` meets the countable dense set `s`, and
      -- those balls are pairwise disjoint.
      have hmeet : ∀ x ∈ u ⁻¹' t, ∃ z ∈ s, z ∈ ball (u x) (1 / 2) := fun x hx => by
        obtain ⟨z, hz⟩ :=
          Metric.mem_closure_iff.1 (hsub (mem_image_of_mem u hx)) (1 / 2) (by positivity)
        exact ⟨z, hz.1, mem_ball_comm.1 hz.2⟩
      choose z hzs hzb using hmeet
      have hinj : Function.Injective fun x : u ⁻¹' t => (⟨z x.1 x.2, hzs x.1 x.2⟩ : s) := by
        intro x y heq
        have hz_eq : z x.1 x.2 = z y.1 y.2 := Subtype.ext_iff.1 heq
        by_contra hne
        have hx_ne_y : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
        exact Set.disjoint_left.1 (hpair x.2 y.2 hx_ne_y) (hzb x.1 x.2) (hz_eq ▸ hzb y.1 y.2)
      have : Countable s := hsc.to_subtype
      exact Set.countable_coe_iff.1 hinj.countable
    have hnull_Icc : volume (Icc (0 : ℝ) 1) = 0 := by
      have hsub_ae : (Icc (0 : ℝ) 1 : Set ℝ) ≤ᵐ[volume] u ⁻¹' t :=
        (ae_restrict_iff' measurableSet_Icc).1 ht_ae
      exact measure_mono_null_ae hsub_ae (hcnt_pre.measure_zero _)
    have hone : volume (Icc (0 : ℝ) 1) = 1 := by simp [Real.volume_Icc]
    exact one_ne_zero (hone.symm.trans hnull_Icc)

end Coordinates

/-! ### Haar-measure independence and linear invariance -/

section HaarAndLinear

/-- **Haar-measure independence of `MemLpLoc`.** On a locally compact second-countable topological
additive group, `MemLpLoc` does not depend on the choice of Borel additive Haar measure. -/
theorem memLpLoc_iff_of_isAddHaarMeasure {G F : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set G} {f : G → F} :
    @MemLpLoc G F _ (MeasureSpace.mk μ) _ p U f ↔
      @MemLpLoc G F _ (MeasureSpace.mk ν) _ p U f := by
  have aux : ∀ (μ₁ μ₂ : Measure G) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure],
      @MemLpLoc G F _ (MeasureSpace.mk μ₁) _ p U f →
        @MemLpLoc G F _ (MeasureSpace.mk μ₂) _ p U f := by
    intro μ₁ μ₂ _ _ h
    rw [@memLpLoc_iff G F _ (MeasureSpace.mk μ₁)] at h
    rw [@memLpLoc_iff G F _ (MeasureSpace.mk μ₂)]
    dsimp only [volume] at h ⊢
    intro K hKU hK
    rw [Measure.isAddLeftInvariant_eq_smul μ₂ μ₁, Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top
  exact ⟨aux μ ν, aux ν μ⟩

/-- **Haar-measure independence of `MemW1pLoc`.** On a finite-dimensional real normed space,
`MemW1pLoc` does not depend on the choice of Borel additive Haar measure. -/
theorem memW1pLoc_iff_of_isAddHaarMeasure {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    @MemW1pLoc E F _ _ (MeasureSpace.mk μ) _ _ p Ω u ↔
      @MemW1pLoc E F _ _ (MeasureSpace.mk ν) _ _ p Ω u := by
  dsimp only [MemW1pLoc]
  rw [memLpLoc_iff_of_isAddHaarMeasure μ ν]
  refine and_congr_right' (exists_congr fun Du => ?_)
  exact and_congr (hasWeakFDerivOn_iff_of_isAddHaarMeasure μ ν)
    (memLpLoc_iff_of_isAddHaarMeasure μ ν)

/-- Rescaling `volume` by any positive factor `c : ℝ≥0` (`c ≠ 0`) leaves `MemLpLoc` unchanged. -/
theorem memLpLoc_smul_volume_iff {X F : Type*} [TopologicalSpace X] [MeasureSpace X]
    [NormedAddCommGroup F] {c : ℝ≥0} (hc : c ≠ 0) {p : ℝ≥0∞} {U : Set X} {f : X → F} :
    @MemLpLoc X F _ (MeasureSpace.mk ((c : ℝ≥0∞) • (volume : Measure X))) _ p U f ↔
      MemLpLoc p U f := by
  rw [@memLpLoc_iff X F _ (MeasureSpace.mk ((c : ℝ≥0∞) • (volume : Measure X))), memLpLoc_iff]
  dsimp only [volume]
  constructor
  · intro h K hKU hK
    have h1 : MemLp f p (((c : ℝ≥0∞) • (volume : Measure X)).restrict K) := h K hKU hK
    rw [Measure.restrict_smul] at h1
    have h2 := h1.smul_measure (c := (c⁻¹ : ℝ≥0)) ENNReal.coe_ne_top
    rwa [smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc, ENNReal.coe_one, one_smul] at h2
  · intro h K hKU hK
    rw [Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top

/-- Rescaling `volume` by any positive factor `c : ℝ≥0` (`c ≠ 0`) leaves `MemW1pLoc` unchanged. -/
theorem memW1pLoc_smul_volume_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℝ≥0} (hc : c ≠ 0) {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    @MemW1pLoc E F _ _ (MeasureSpace.mk ((c : ℝ≥0∞) • (volume : Measure E))) _ _ p Ω u ↔
      MemW1pLoc p Ω u := by
  have hderiv : ∀ Du : E → E →L[ℝ] F,
      HasWeakFDerivOn ((c : ℝ≥0∞) • (volume : Measure E)) Ω u Du ↔
        HasWeakFDerivOn (volume : Measure E) Ω u Du := fun Du => by
    refine ⟨fun h => ?_, fun h => h.smul_measure_nnreal c⟩
    have h2 := h.smul_measure_nnreal c⁻¹
    rwa [smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc, ENNReal.coe_one, one_smul] at h2
  dsimp only [MemW1pLoc]
  rw [memLpLoc_smul_volume_iff hc]
  exact and_congr_right' (exists_congr fun Du =>
    and_congr (hderiv Du) (memLpLoc_smul_volume_iff hc))

/-- Precomposition with a continuous linear equivalence into a finite-dimensional space carrying a
Borel additive Haar measure preserves `MemLpLoc`. -/
theorem MemLpLoc.comp_continuousLinearEquiv {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F]
    {p : ℝ≥0∞} {U : Set E₁} {V : Set E} {u : E → F}
    (hu : MemLpLoc p V u) (e : E₁ ≃L[ℝ] E) (hUV : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) := by
  have : ((volume : Measure E₁).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hu_map : @MemLpLoc E F _ (MeasureSpace.mk ((volume : Measure E₁).map e)) _ p V u :=
    (memLpLoc_iff_of_isAddHaarMeasure volume ((volume : Measure E₁).map e)).1 hu
  rw [@memLpLoc_iff E F _ (MeasureSpace.mk ((volume : Measure E₁).map e))] at hu_map
  dsimp only [volume] at hu_map
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hKe : IsCompact (e '' K) := hK.image e.continuous
  have h1 : MemLp u p (((volume : Measure E₁).map e).restrict (e '' K)) :=
    hu_map (e '' K) ((image_mono hKU).trans hUV.image_subset) hKe
  have hemp : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hres : ((volume : Measure E₁).map e).restrict (e '' K) =
      ((volume : Measure E₁).restrict K).map e := by
    rw [hemp.restrict_map, Set.preimage_image_eq _ e.injective]
  rw [hres, hemp.memLp_map_measure_iff] at h1
  exact h1

/-- Precomposition with a continuous linear equivalence preserves and reflects `MemLpLoc`. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F]
    {p : ℝ≥0∞} {V : Set E} {u : E → F} (e : E₁ ≃L[ℝ] E) :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V (e ⁻¹' V) := fun y hy => by simpa using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv e.symm hVU

/-- **Precomposition with a continuous linear equivalence in `MemW1pLoc`.** Any continuous linear
equivalence `e : E₁ ≃L[ℝ] E` between finite-dimensional real normed spaces carrying Borel additive
Haar measures pulls `MemW1pLoc p V` back to `MemW1pLoc p U` whenever `MapsTo e U V`, with weak
derivative `x ↦ Du (e x) ∘L e`. -/
theorem MemW1pLoc.comp_continuousLinearEquiv {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Opens E₁} {V : Opens E} {u : E → F}
    (hu : MemW1pLoc p V u) (e : E₁ ≃L[ℝ] E) (hUV : MapsTo e U V) :
    MemW1pLoc p U (u ∘ e) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := hu
  refine ⟨huLp.comp_continuousLinearEquiv e hUV, fun x => (Du (e x)).comp (e : E₁ →L[ℝ] E),
    hDu.comp_continuousLinearEquiv_of_isAddHaarMeasure e hUV, ?_⟩
  exact (hDuLp.comp_continuousLinearEquiv e hUV).clm_comp
    ((ContinuousLinearMap.compL ℝ E₁ E F).flip (e : E₁ →L[ℝ] E))

/-- **Linear and norm invariance of `MemW1pLoc`.** For any continuous linear equivalence
`e : E₁ ≃L[ℝ] E` between finite-dimensional real normed spaces carrying Borel additive Haar
measures, `u ∘ e ∈ MemW1pLoc p (Ω.comap (e.toHomeomorph : C(E₁, E)))` if and only if
`u ∈ MemW1pLoc p Ω`. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memW1pLoc_comp_iff {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (e : E₁ ≃L[ℝ] E) :
    MemW1pLoc p (Ω.comap (e.toHomeomorph : C(E₁, E))) (u ∘ e) ↔ MemW1pLoc p Ω u := by
  refine ⟨fun h => ?_, fun h =>
    h.comp_continuousLinearEquiv e (mapsTo_preimage e (Ω : Set E))⟩
  have hVU : MapsTo e.symm Ω (Ω.comap (e.toHomeomorph : C(E₁, E))) := fun y hy => by
    simpa using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv e.symm hVU

/-- **Equivalence of supremum and Euclidean norms on `ℝⁿ`.** Identifying `(Fin n → ℝ)` (carrying the
supremum norm) with `EuclideanSpace ℝ (Fin n)` (carrying the `ℓ²` norm) via `WithLp.toLp 2`
preserves and reflects `MemW1pLoc`. -/
theorem memW1pLoc_comp_toLp_iff {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Opens (Fin n → ℝ)} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → F} (hU : (U : Set (Fin n → ℝ)) = WithLp.toLp 2 ⁻¹' Ω) :
    MemW1pLoc p U (u ∘ WithLp.toLp 2) ↔ MemW1pLoc p Ω u := by
  let e : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).symm
  have hUe : U = Ω.comap (e.toHomeomorph : C(Fin n → ℝ, EuclideanSpace ℝ (Fin n))) :=
    SetLike.ext' hU
  rw [hUe]
  exact e.memW1pLoc_comp_iff

end HaarAndLinear

/-! ### Concrete membership and sharpness checks -/

section Examples

/-- The identity map of a finite-dimensional real normed space belongs to `MemW1pLoc p Ω` on every
open set and for every exponent `p : ℝ≥0∞`. -/
theorem memW1pLoc_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (p : ℝ≥0∞) (Ω : Opens E) : MemW1pLoc p Ω (id : E → E) :=
  (ContinuousLinearMap.id ℝ E).memW1pLoc

/-- On a nontrivial finite-dimensional real normed space with an additive Haar measure, the
identity map does *not* belong to global `Lᵖ` for any nonzero exponent `p`, witnessing that
`MemW1pLoc` imposes no growth bound at infinity. -/
theorem not_memLp_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    {p : ℝ≥0∞} (hp : p ≠ 0) : ¬ MemLp (id : E → E) p (volume : Measure E) := by
  intro h
  rcases eq_or_ne p ∞ with rfl | hptop
  · have htop : eLpNormEssSup (id : E → E) volume < ⊤ := by
      simpa [eLpNorm_exponent_top h.aestronglyMeasurable] using h.eLpNorm_lt_top
    obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.1 htop
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    let R : ℝ := (C : ℝ) + 1
    let x₀ : E := ((2 * R) / ‖v‖) • v
    have hx₀ : ‖x₀‖ = 2 * R := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hv0.ne']
    have hsub : ball x₀ 1 ⊆ {x : E | (C : ℝ) < ‖x‖} := fun x hx => by
      simp only [mem_ofPred]
      have hdist : ‖x₀ - x‖ < 1 := by simpa [dist_eq_norm'] using mem_ball.1 hx
      have htri : ‖x₀‖ - ‖x₀ - x‖ ≤ ‖x‖ := by
        simpa using norm_sub_norm_le x₀ (x₀ - x)
      linarith [NNReal.coe_nonneg C]
    have hnull : volume (ball x₀ 1) = 0 := by
      refine measure_mono_null hsub ?_
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hC] with x hx
      exact not_lt.2 (NNReal.coe_le_coe.2 hx)
    exact (measure_ball_pos volume x₀ one_pos).ne' hnull
  · have hint : IntegrableOn (fun x : E => ‖x‖ ^ p.toReal) (closedBall 0 1)ᶜ volume :=
      ((integrable_norm_rpow_iff h.aestronglyMeasurable hp hptop).2 h).integrableOn
    have hlt := (integrableOn_norm_rpow_compl_closedBall_iff (E := E) (mu := volume)
      (s := p.toReal) one_pos).1 hint
    have hpos : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    linarith [(Nat.cast_pos (α := ℝ)).2 (Module.finrank_pos (R := ℝ) (M := E))]

/-- On a nontrivial finite-dimensional real normed space, `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc p U` on
a neighbourhood `U` of the origin if and only if `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff_lt_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK => hK.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- The norm `x ↦ ‖x‖` on any finite-dimensional real normed space belongs to `MemW1pLoc p Ω` for
every open set `Ω` and every exponent `p`, with weak derivative `fderiv ℝ (‖·‖)` of operator norm at
most `1` everywhere. -/
theorem memW1pLoc_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (p : ℝ≥0∞) (Ω : Opens E) :
    MemW1pLoc p Ω (‖·‖ : E → ℝ) ∧ ∀ x : E, ‖fderiv ℝ (‖·‖ : E → ℝ) x‖ ≤ 1 :=
  ⟨lipschitzWith_one_norm.memW1pLoc, fun _ =>
    NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm⟩

/-- On `Fin 2 → ℝ` (with the supremum norm `‖v‖ = max |v 0| |v 1|`), the Fréchet derivative of
`‖·‖` at `![1, 1 / 2]` is the first coordinate projection, so it vanishes on `![0, 1]`: the weak
derivative of `‖·‖` reflects the geometry of the unit sphere rather than an inner product. -/
theorem fderiv_norm_pi_fin_two_apply :
    fderiv ℝ (‖·‖ : (Fin 2 → ℝ) → ℝ) ![1, 1 / 2] ![0, 1] = 0 := by
  let S : Set (Fin 2 → ℝ) := {y | |y 1| < y 0}
  have hS_open : IsOpen S :=
    isOpen_lt (continuous_abs.comp (continuous_apply 1)) (continuous_apply 0)
  have hxS : (![1, 1 / 2] : Fin 2 → ℝ) ∈ S := by
    simp only [S, mem_ofPred, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  have heq : (‖·‖ : (Fin 2 → ℝ) → ℝ) =ᶠ[𝓝 ![1, 1 / 2]] ContinuousLinearMap.proj (R := ℝ) 0 := by
    filter_upwards [hS_open.mem_nhds hxS] with y hy
    have hy0 : 0 ≤ y 0 := (abs_nonneg _).trans hy.le
    have hsup : ‖y‖ = max |y 0| |y 1| :=
      le_antisymm
        ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).2
          (Fin.forall_fin_two.2 ⟨le_max_left _ _, le_max_right _ _⟩))
        (max_le (norm_le_pi_norm y 0) (norm_le_pi_norm y 1))
    rw [hsup, abs_of_nonneg hy0, max_eq_left hy.le]
    rfl
  let p₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) 0
  have hfd : HasFDerivAt (‖·‖ : (Fin 2 → ℝ) → ℝ) p₀ ![1, 1 / 2] :=
    p₀.hasFDerivAt.congr_of_eventuallyEq heq
  rw [hfd.fderiv]
  simp [p₀]

/-- **Sharpness on the unit radial map.** On a finite-dimensional real inner product space `E` of
dimension `d ≥ 2` and an open set `Ω` containing `0`, the unit radial map `x ↦ ‖x‖⁻¹ • x` belongs
to `MemW1pLoc p Ω` if and only if `p < Module.finrank ℝ E`. -/
theorem memW1pLoc_norm_inv_smul_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    {p : ℝ≥0∞} {Ω : Opens E} (hd : 2 ≤ Module.finrank ℝ E) (h0 : (0 : E) ∈ Ω) :
    MemW1pLoc p Ω (fun x : E => ‖x‖⁻¹ • x) ↔ p < Module.finrank ℝ E := by
  have hd1 : 1 < Module.finrank ℝ E := lt_of_lt_of_le one_lt_two hd
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd1)
  let b := stdOrthonormalBasis ℝ E
  have hcoord : ∀ i (x : E), b.toBasis.repr (‖x‖⁻¹ • x) i = ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
    intro i x
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_smul_right,
      Real.rpow_neg_one, real_inner_comm]
  let D : Fin (Module.finrank ℝ E) → E → E →L[ℝ] ℝ := fun i x =>
    ‖x‖ ^ (-1 : ℝ) • innerSL ℝ (b i) - (‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫) • innerSL ℝ x
  have hweak : ∀ i, HasWeakFDerivOn volume Ω (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫) (D i) :=
    fun i => hasWeakFDerivOn_norm_rpow_neg_one_mul_inner hd1 (b i) Ω
  constructor
  · intro hu
    obtain ⟨_, Du, hDu, hDuLp⟩ := hu
    -- Compare each coordinate's weak derivative with `D i` by uniqueness, then take the trace.
    have hae_coord : ∀ i, (fun x => (innerSL ℝ (b i)).comp (Du x)) =ᵐ[volume.restrict Ω] D i := by
      intro i
      have h1 : HasWeakFDerivOn volume Ω (fun x : E => ⟪b i, ‖x‖⁻¹ • x⟫)
          (fun x => (innerSL ℝ (b i)).comp (Du x)) := hDu.clm_comp (innerSL ℝ (b i))
      have heq_fun : (fun x : E => ⟪b i, ‖x‖⁻¹ • x⟫) = fun x => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
        funext x
        rw [real_inner_smul_right, Real.rpow_neg_one, real_inner_comm]
      exact (heq_fun ▸ h1).ae_eq (hweak i)
    let trCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
      ∑ i : Fin (Module.finrank ℝ E),
        (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ E (b i))
    have htrLp : MemLpLoc p Ω (fun x => trCLM (Du x)) := hDuLp.clm_comp trCLM
    have htr_ae : (fun x => trCLM (Du x)) =ᵐ[volume.restrict Ω]
        fun x : E => ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ := by
      have hall : ∀ᵐ x ∂volume.restrict Ω, ∀ i, ((innerSL ℝ (b i)).comp (Du x)) = D i x :=
        ae_all_iff.2 hae_coord
      have hne0 : ∀ᵐ (x : E) ∂volume.restrict (Ω : Set E), x ≠ 0 :=
        ae_restrict_of_ae (ae_iff.2 (by simp))
      filter_upwards [hall, hne0] with x hx hx0
      have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hsum_eval : trCLM (Du x) = ∑ i : Fin (Module.finrank ℝ E), D i x (b i) := by
        simp only [trCLM, FunLike.coe_sum, Finset.sum_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hxi := congrArg (fun L : E →L[ℝ] ℝ => L (b i)) (hx i)
        simpa using hxi
      have hDi : ∀ i, D i x (b i) = ‖x‖⁻¹ - ‖x‖ ^ (-3 : ℝ) * (⟪x, b i⟫ * ⟪b i, x⟫) := by
        intro i
        simp only [D, sub_apply, smul_apply,
          innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq, b.norm_eq_one,
          one_pow, mul_one, Real.rpow_neg_one, real_inner_comm (b i) x]
        ring
      have hparseval : (∑ i : Fin (Module.finrank ℝ E), ⟪x, b i⟫ * ⟪b i, x⟫) = ‖x‖ ^ 2 := by
        rw [b.sum_inner_mul_inner x x, real_inner_self_eq_norm_sq]
      rw [hsum_eval, Finset.sum_congr rfl fun i _ => hDi i, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hparseval]
      have hrpow3 : ‖x‖ ^ (-3 : ℝ) * ‖x‖ ^ 2 = ‖x‖⁻¹ := by
        rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_add hx_pos]
        norm_num [Real.rpow_neg_one]
      rw [hrpow3]
      ring
    have hscLp : MemLpLoc p Ω (fun x : E => ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹) :=
      htrLp.congr_ae htr_ae
    have hc_ne : ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_le.2 hd
      linarith
    have hinvLp : MemLpLoc p Ω (fun x : E => ‖x‖⁻¹) := by
      simpa [Pi.smul_def, smul_eq_mul, inv_mul_cancel_left₀ hc_ne] using
        hscLp.const_smul ((Module.finrank ℝ E : ℝ) - 1)⁻¹
    exact (memLpLoc_norm_inv_iff_lt_finrank (Ω.isOpen.mem_nhds h0)).1 hinvLp
  · intro hp
    rw [b.toBasis.memW1pLoc_iff]
    intro i
    simp_rw [hcoord i]
    refine ⟨memLpLoc_iff.2 fun K _ hK => ?_, D i, hweak i, memLpLoc_iff.2 fun K _ hK => ?_⟩
    · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
      exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖b i‖
        (Eventually.of_forall fun x => abs_norm_rpow_neg_one_mul_inner_le (b i) x)
    · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict K) :=
        hK.memLp_norm_inv_restrict hp
      refine (hker.const_mul (2 * ‖b i‖)).of_le
        (by fun_prop : Measurable (D i)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
      exact norm_norm_rpow_neg_one_smul_innerSL_sub_le (b i) x

/-- The indicator of an open half-space `{x : E | 0 < ℓ x}` belongs to `MemLpLoc p U` on every
subset `U` and for every exponent `p : ℝ≥0∞`. -/
theorem memLpLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (ℓ : StrongDual ℝ E) (p : ℝ≥0∞) (U : Set E) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (isOpen_lt continuous_const ℓ.continuous).measurableSet.nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- **Jump discontinuities across hyperplanes are not in `MemW1pLoc`.** While the indicator of
`{x : E | 0 < ℓ x}` belongs to `MemLpLoc p Ω` for every `p` (`TauCeti.memLpLoc_indicator_pos`), it
belongs to `MemW1pLoc p Ω` for *no* exponent `p : ℝ≥0∞` whenever `ℓ ≠ 0` and `Ω` meets
`{x | ℓ x = 0}`. -/
theorem not_memW1pLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0) {p : ℝ≥0∞} {Ω : Opens E} {x₀ : E}
    (hx₀ : x₀ ∈ Ω) (hx₀0 : ℓ x₀ = 0) :
    ¬ MemW1pLoc p Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  rintro ⟨_, Du, hDu, _⟩
  exact not_hasWeakFDerivOn_indicator_pos hℓ hx₀ hx₀0 Du hDu

end Examples

end TauCeti
