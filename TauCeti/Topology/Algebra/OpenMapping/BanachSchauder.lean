/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Sequences
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.Algebra.Group.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# The Banach–Schauder open mapping, closed graph, and closed range theorems

This file packages the Banach–Schauder mapping theorems for complete first-countable uniform
additive modules over any topological ring carrying a zero sequence of units
(`TauCeti.HasZeroSequenceOfUnits`). Throughout, the standing scalar-action compatibility is
jointly continuous scalar multiplication on the source (`ContinuousSMul R E`) and continuous
fixed scalar actions on the target (`ContinuousConstSMul R F`), except that the closed-graph
theorems assume only scalar-orbit continuity at zero on both `E` and `F` and continuous fixed
scalar actions on `E` (`ContinuousConstSMul R E`). This covers Fréchet spaces, F-spaces, and
Banach spaces over any nontrivially normed field (`ℝ`, `ℂ`, `ℚ_[p]`, …; normed-field users can
import `TauCeti.Analysis.Normed.Ring.PseudoUniformizer` for the `HasZeroSequenceOfUnits`
instance via `TauCeti.NormedRing.IsTate.of_nontriviallyNormedField`), as well as complete
first-countable modules over Tate rings, without assuming local convexity, normability, or
separability.

## Main results

* **Open mapping and quotient theorems**:
  `LinearMap.isOpenMap_of_complete`, `LinearMap.isQuotientMap_of_complete`,
  `ContinuousLinearMap.isOpenMap_of_complete`, `ContinuousLinearMap.isQuotientMap_of_complete`.
  A surjective continuous linear map between complete first-countable uniform modules (with `T₀`
  target, `ContinuousSMul R E` on the source, and `ContinuousConstSMul R F` on the target) over a
  topological ring with a zero sequence of units is open and a quotient map.
* **Continuous inverse theorem and uniqueness of complete uniformities**:
  `LinearEquiv.continuous_symm_of_complete`,
  `LinearEquiv.toContinuousLinearEquivOfContinuousOfComplete`,
  `ContinuousLinearEquiv.ofBijectiveOfComplete`,
  `ContinuousLinearMap.isUnit_iff_bijective_of_complete`,
  `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap_of_complete`,
  `IsUniformAddGroup.eq_of_toTopologicalSpace_le_of_complete`.
  Under the same standing scalar-action hypotheses (`ContinuousSMul R E` on the source and
  `ContinuousConstSMul R F` on the target; `ContinuousSMul R E` on the single module for the unit
  criteria), a continuous linear equivalence has continuous inverse, a bijective continuous linear
  map is a `ContinuousLinearEquiv`, and an endomorphism is a unit iff it is bijective. In
  particular, two comparable complete first-countable uniform group structures making a module over
  a topological ring with a zero sequence of units topological (with the coarser one `T₀`,
  `ContinuousSMul` for the finer one, and `ContinuousConstSMul` for the coarser one) must
  coincide.
* **Closed graph and sequential closed graph theorems**:
  `LinearMap.continuous_of_isClosed_graph_of_complete`,
  `LinearMap.continuous_of_seq_closed_graph_of_complete`,
  `ContinuousLinearMap.ofIsClosedGraphOfComplete`,
  `ContinuousLinearMap.ofSeqClosedGraphOfComplete`.
  Assuming scalar-orbit continuity at zero on both modules and `ContinuousConstSMul R E` on the
  domain over a topological ring with a zero sequence of units, a linear map with closed (or
  sequentially closed) graph into a complete first-countable uniform module from a `T₀` complete
  first-countable uniform module is continuous. First-countability of the product comes directly
  from countable generation of `𝓝 0` (`TauCeti.ContinuousConstVAdd.toFirstCountableTopology`), with
  no metric required.
* **Closed-range strictness**:
  `ContinuousLinearMap.isStrictMap_of_isClosed_range_of_complete`.
  Under `ContinuousSMul R E` on the source and `ContinuousConstSMul R F` on the `T₀` target, a
  continuous linear map with closed range between complete first-countable uniform modules is
  strict.

Complement and closed-range applications built on these results live in
`TauCeti.Topology.Algebra.OpenMapping.Complement` and
`TauCeti.Topology.Algebra.OpenMapping.ClosedRange`, respectively.

## Attribution

The API shapes and constructor packaging for the continuous inverse, bijectivity unit criteria,
closed-graph theorems, and open-mapping equivalences generalise the Banach-space theorems in
`Mathlib/Analysis/Normed/Operator/Banach.lean` (`LinearEquiv.continuous_symm`,
`ContinuousLinearEquiv.ofBijective`, `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap`,
`LinearMap.continuous_of_isClosed_graph`, `ContinuousLinearMap.ofIsClosedGraph`).

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter I, §3, no. 3 (Banach–Schauder and closed
  graph theorems).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, §§1.7–1.10.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Function Topology
open scoped Uniformity

/-! ### Open mapping, quotient map, continuous inverse, and uniqueness of uniformity -/

section Ring

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [uE : UniformSpace E] [huE : IsUniformAddGroup E] [hcE : CompleteSpace E]
  [hcgE : (𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [hsmulE : ContinuousSMul R E]
  [AddCommGroup F] [uF : UniformSpace F] [huF : IsUniformAddGroup F] [hcF : CompleteSpace F]
  [hcgF : (𝓝 (0 : F)).IsCountablyGenerated] [ht0F : T0Space F] [Module R F]
  [hsmulF : ContinuousConstSMul R F]

namespace LinearMap

/-- **Banach–Schauder open mapping theorem for linear maps.** A surjective linear map, continuous
at zero, between complete first-countable uniform modules (with `T₀` target, `ContinuousSMul R E`
on the source, and `ContinuousConstSMul R F` on the target) over a topological ring with a zero
sequence of units is open. -/
theorem isOpenMap_of_complete (f : E →ₗ[R] F) (hf : Surjective f)
    (hfc : ContinuousAt (f : E → F) 0) : IsOpenMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact TauCeti.HasZeroSequenceOfUnits.isOpenMap_of_continuousSMul f hf hfc

/-- **Banach–Schauder quotient map theorem for linear maps.** Under the hypotheses of
`LinearMap.isOpenMap_of_complete` (including `ContinuousSMul R E` and `ContinuousConstSMul R F`),
the topology of `F` is coinduced by `f`. -/
theorem isQuotientMap_of_complete (f : E →ₗ[R] F) (hf : Surjective f)
    (hfc : ContinuousAt (f : E → F) 0) : IsQuotientMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact TauCeti.HasZeroSequenceOfUnits.isQuotientMap_of_continuousSMul f hf hfc

end LinearMap

namespace ContinuousLinearMap

/-- **Banach–Schauder / Fréchet open mapping theorem.** Every surjective continuous linear map
between complete first-countable uniform modules (with `T₀` target, `ContinuousSMul R E` on the
source, and `ContinuousConstSMul R F` on the target) over a topological ring with a zero
sequence of units is an open map.

This covers Fréchet spaces, F-spaces, and Banach spaces over any nontrivially normed field (such
as `ℝ`, `ℂ`, or `ℚ_[p]`) as well as complete first-countable modules over Tate rings, without
assuming local convexity, normability, or separability. -/
theorem isOpenMap_of_complete (f : E →L[R] F) (hf : Surjective f) : IsOpenMap f :=
  f.toLinearMap.isOpenMap_of_complete hf f.continuous.continuousAt

/-- **Banach–Schauder / Fréchet quotient map theorem.** Under the hypotheses of
`ContinuousLinearMap.isOpenMap_of_complete` (including `ContinuousSMul R E` and
`ContinuousConstSMul R F`, over a topological ring with a zero sequence of units), every
surjective continuous linear map between complete first-countable uniform modules (with `T₀` target)
is a quotient map. -/
theorem isQuotientMap_of_complete (f : E →L[R] F) (hf : Surjective f) : IsQuotientMap f :=
  f.toLinearMap.isQuotientMap_of_complete hf f.continuous.continuousAt

end ContinuousLinearMap

namespace LinearEquiv

/-- **Banach–Schauder continuous inverse theorem.** If a linear equivalence between complete
first-countable uniform modules (with `T₀` target, `ContinuousSMul R E` on the source, and
`ContinuousConstSMul R F` on the target) over a topological ring with a zero sequence of units
is continuous, then its inverse is also continuous. -/
theorem continuous_symm_of_complete (e : E ≃ₗ[R] F) (he : Continuous e) : Continuous e.symm :=
  e.toEquiv.continuous_symm_iff.mpr
    (e.toLinearMap.isOpenMap_of_complete e.surjective he.continuousAt)

/-- Promote a continuous linear equivalence between complete first-countable uniform modules (with
`T₀` target, `ContinuousSMul R E` on the source, and `ContinuousConstSMul R F` on the target) over
a topological ring with a zero sequence of units to a `ContinuousLinearEquiv`. -/
def toContinuousLinearEquivOfContinuousOfComplete (e : E ≃ₗ[R] F) (he : Continuous e) :
    E ≃L[R] F where
  toLinearEquiv := e
  continuous_toFun := he
  continuous_invFun := e.continuous_symm_of_complete he

@[simp]
theorem toLinearEquiv_toContinuousLinearEquivOfContinuousOfComplete (e : E ≃ₗ[R] F)
    (he : Continuous e) :
    (e.toContinuousLinearEquivOfContinuousOfComplete he).toLinearEquiv = e :=
  (rfl)

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuousOfComplete (e : E ≃ₗ[R] F) (he : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuousOfComplete he) = e :=
  (rfl)

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuousOfComplete_symm (e : E ≃ₗ[R] F)
    (he : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuousOfComplete he).symm = e.symm :=
  (rfl)

@[simp]
theorem toContinuousLinearEquivOfContinuousOfComplete_apply (e : E ≃ₗ[R] F) (he : Continuous e)
    (x : E) :
    e.toContinuousLinearEquivOfContinuousOfComplete he x = e x :=
  (rfl)

@[simp]
theorem toContinuousLinearEquivOfContinuousOfComplete_symm_apply (e : E ≃ₗ[R] F)
    (he : Continuous e) (y : F) :
    (e.toContinuousLinearEquivOfContinuousOfComplete he).symm y = e.symm y :=
  (rfl)

end LinearEquiv

namespace ContinuousLinearEquiv

/-- **Banach–Schauder isomorphism theorem.** A bijective continuous linear map between complete
first-countable uniform modules (with `T₀` target, `ContinuousSMul R E` on the source, and
`ContinuousConstSMul R F` on the target) over a topological ring with a zero sequence of units
is a continuous linear equivalence. -/
noncomputable def ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) : E ≃L[R] F :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuousOfComplete
    (f.continuous.congr fun x ↦ (LinearEquiv.ofBijective_apply f.toLinearMap (hf := hf) x).symm)

@[simp]
theorem toLinearEquiv_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    (ofBijectiveOfComplete f hf).toLinearEquiv = LinearEquiv.ofBijective f.toLinearMap hf :=
  (rfl)

@[simp]
theorem ofBijectiveOfComplete_apply (f : E →L[R] F) (hf : Bijective f) (x : E) :
    ofBijectiveOfComplete f hf x = f x :=
  (LinearEquiv.toContinuousLinearEquivOfContinuousOfComplete_apply _ _ x).trans
    (LinearEquiv.ofBijective_apply f.toLinearMap x)

@[simp]
theorem coeFn_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    ⇑(ofBijectiveOfComplete f hf) = f :=
  funext (ofBijectiveOfComplete_apply f hf)

@[simp]
theorem coe_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    (ofBijectiveOfComplete f hf : E →L[R] F) = f :=
  ContinuousLinearMap.ext (ofBijectiveOfComplete_apply f hf)

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module with jointly
continuous scalar multiplication (`ContinuousSMul R E`) over a topological ring with a zero
sequence of units is a unit in `E →L[R] E` if and only if it is bijective. -/
theorem isUnit_iff_bijective_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, hu⟩ ↦ hu ▸ (ContinuousLinearEquiv.ofUnit u).bijective,
    fun hf ↦ ⟨(ContinuousLinearEquiv.ofBijectiveOfComplete f hf).toUnit,
      ContinuousLinearEquiv.coe_ofBijectiveOfComplete f hf⟩⟩

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module with jointly
continuous scalar multiplication (`ContinuousSMul R E`) over a topological ring with a zero
sequence of units is a unit in `E →L[R] E` if and only if it is a unit as a bare linear
endomorphism. -/
theorem isUnit_iff_isUnit_toLinearMap_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ IsUnit (f : E →ₗ[R] E) :=
  f.isUnit_iff_bijective_of_complete.trans (Module.End.isUnit_iff _).symm

end ContinuousLinearMap

end Ring

namespace IsUniformAddGroup

/-- **Uniqueness of comparable complete first-countable uniformities.** If `u₁` and `u₂` are two
complete first-countable uniform additive group structures on a module `E` over a topological
ring `R` with a zero sequence of units, satisfying
`u₁.toTopologicalSpace ≤ u₂.toTopologicalSpace` (`u₁` finer than `u₂`), `u₂` `T₀`, `ContinuousSMul`
for `u₁`, and `ContinuousConstSMul` for `u₂`, then `u₁ = u₂` (and in particular their topologies
agree). -/
theorem eq_of_toTopologicalSpace_le_of_complete (R : Type*) {E : Type*} [Ring R]
    [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R] [AddCommGroup E] [Module R E]
    {u₁ u₂ : UniformSpace E}
    (hu₁ : @IsUniformAddGroup E u₁ _) (hu₂ : @IsUniformAddGroup E u₂ _)
    (hc₁ : @CompleteSpace E u₁) (hc₂ : @CompleteSpace E u₂)
    (hcg₁ : (@nhds E u₁.toTopologicalSpace 0).IsCountablyGenerated)
    (hcg₂ : (@nhds E u₂.toTopologicalSpace 0).IsCountablyGenerated)
    (ht0 : @T0Space E u₂.toTopologicalSpace)
    (hsmul₁ : @ContinuousSMul R E _ _ u₁.toTopologicalSpace)
    (hsmul₂ : @ContinuousConstSMul R E u₂.toTopologicalSpace _)
    (hle : u₁.toTopologicalSpace ≤ u₂.toTopologicalSpace) :
    u₁ = u₂ := by
  have ho :=
    LinearMap.isOpenMap_of_complete (R := R) (E := E) (F := E)
      (uE := u₁) (huE := hu₁) (hcE := hc₁) (hcgE := hcg₁) (hsmulE := hsmul₁)
      (uF := u₂) (huF := hu₂) (hcF := hc₂) (hcgF := hcg₂) (ht0F := ht0) (hsmulF := hsmul₂)
      LinearMap.id surjective_id (Filter.tendsto_id.mono_left (nhds_mono hle))
  have hle' : u₂.toTopologicalSpace ≤ u₁.toTopologicalSpace := fun s hs ↦ by
    simpa only [LinearMap.id_coe, Set.image_id] using ho s hs
  exact hu₁.ext hu₂ (by rw [le_antisymm hle hle'])

end IsUniformAddGroup

/-! ### Closed graph theorem -/

section ClosedGraph

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [T0Space E] [Module R E] [ContinuousConstSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [Module R F]

namespace LinearMap

/-- **Banach–Schauder closed graph theorem.** A linear map between complete first-countable
uniform modules (with `T₀` domain, `ContinuousConstSMul R E`, and scalar-orbit continuity at zero
on both `E` and `F`) over a topological ring with a zero sequence of units is continuous if its
graph is closed in `E × F`.

Only the domain `E` needs to be `T₀` and `ContinuousConstSMul`, because Henkel's open mapping
theorem is applied to the first projection `f.graph → E`. -/
theorem continuous_of_isClosed_graph_of_complete (f : E →ₗ[R] F)
    (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : IsClosed (f.graph : Set (E × F))) : Continuous f := by
  have : CompleteSpace f.graph := hg.completeSpace_coe
  have : FirstCountableTopology f.graph :=
    inferInstanceAs (FirstCountableTopology (f.graph : Set (E × F)))
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have hcg : ∀ p : f.graph, ContinuousAt (fun a : R ↦ a • p) 0 := fun p ↦
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      ((hcE (p : E × F).1).prodMk (hcF (p : E × F).2))
  have hsymm_cont : Continuous (f.graphEquiv.symm : f.graph → E) :=
    continuous_subtypeVal.fst.congr fun p ↦ (f.graphEquiv_symm_apply p).symm
  have hopen : IsOpenMap (f.graphEquiv.symm : f.graph → E) :=
    TauCeti.HasZeroSequenceOfUnits.isOpenMap f.graphEquiv.symm.toLinearMap
      f.graphEquiv.symm.surjective hsymm_cont.continuousAt hcg
  have hcont : Continuous (f.graphEquiv : E → f.graph) :=
    f.graphEquiv.symm.toEquiv.continuous_symm_iff.mpr hopen
  have hfn : (fun x ↦ (f.graphEquiv x : E × F).snd) = f := by
    ext x
    simp
  rw [← hfn]
  exact continuous_snd.comp (continuous_subtypeVal.comp hcont)

/-- **Sequential closed graph theorem.** A linear map between complete first-countable uniform
modules (with `T₀` domain, `ContinuousConstSMul R E`, and scalar-orbit continuity at zero on both
`E` and `F`) over a topological ring with a zero sequence of units is continuous if its graph
is sequentially closed: whenever `u n → x` and `f (u n) → y`, one has `y = f x`.

First-countability of `E × F` follows from countable generation of `𝓝 (0 : E)` and `𝓝 (0 : F)`
without introducing a metric. -/
theorem continuous_of_seq_closed_graph_of_complete (f : E →ₗ[R] F)
    (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    Continuous f := by
  refine f.continuous_of_isClosed_graph_of_complete hcE hcF (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have hcomp : f ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact ((LinearMap.mem_graph_iff f (φ n)).mp (hφg n)).symm
  rw [hcomp]
  exact (continuous_snd.tendsto _).comp hφ

end LinearMap

namespace ContinuousLinearMap

variable {f : E →ₗ[R] F}

/-- Bundle a linear map with closed graph between complete first-countable uniform modules (with
`T₀` domain, `ContinuousConstSMul R E`, and scalar-orbit continuity at zero on both `E` and `F`)
over a topological ring with a zero sequence of units as a `ContinuousLinearMap`. -/
def ofIsClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : IsClosed (f.graph : Set (E × F))) : E →L[R] F where
  toLinearMap := f
  cont := f.continuous_of_isClosed_graph_of_complete hcE hcF hg

@[simp]
theorem coeFn_ofIsClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : IsClosed (f.graph : Set (E × F))) :
    ⇑(ofIsClosedGraphOfComplete hcE hcF hg) = f :=
  (rfl)

@[simp]
theorem coe_ofIsClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : IsClosed (f.graph : Set (E × F))) :
    (ofIsClosedGraphOfComplete hcE hcF hg : E →ₗ[R] F) = f :=
  (rfl)

@[simp]
theorem ofIsClosedGraphOfComplete_apply (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : IsClosed (f.graph : Set (E × F))) (x : E) :
    ofIsClosedGraphOfComplete hcE hcF hg x = f x :=
  (rfl)

/-- Bundle a linear map with sequentially closed graph between complete first-countable uniform
modules (with `T₀` domain, `ContinuousConstSMul R E`, and scalar-orbit continuity at zero on both
`E` and `F`) over a topological ring with a zero sequence of units as a
`ContinuousLinearMap`. -/
def ofSeqClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    E →L[R] F where
  toLinearMap := f
  cont := f.continuous_of_seq_closed_graph_of_complete hcE hcF hg

@[simp]
theorem coeFn_ofSeqClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    ⇑(ofSeqClosedGraphOfComplete hcE hcF hg) = f :=
  (rfl)

@[simp]
theorem coe_ofSeqClosedGraphOfComplete (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    (ofSeqClosedGraphOfComplete hcE hcF hg : E →ₗ[R] F) = f :=
  (rfl)

@[simp]
theorem ofSeqClosedGraphOfComplete_apply (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcF : ∀ y : F, ContinuousAt (fun a : R ↦ a • y) 0)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) (x : E) :
    ofSeqClosedGraphOfComplete hcE hcF hg x = f x :=
  (rfl)

end ContinuousLinearMap

end ClosedGraph

/-! ### Closed-range strictness -/

section Strict

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousConstSMul R F]

namespace ContinuousLinearMap

/-- A continuous linear map with closed range between complete first-countable uniform modules
(with `T₀` target, `ContinuousSMul R E` on the source, and `ContinuousConstSMul R F` on the
target) over a topological ring with a zero sequence of units is strict
(`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_complete (f : E →L[R] F)
    (hr : IsClosed (f.range : Set F)) : Topology.IsStrictMap f := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact f.toLinearMap.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits_of_continuousSMul
    f.continuous.continuousAt hr

end ContinuousLinearMap

end Strict

end
