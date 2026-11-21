/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Sequences
import TauCeti.Topology.Algebra.Group.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# The Banach–Schauder open mapping, closed graph, and closed range theorems

This file packages the Banach–Schauder mapping theorems for complete first-countable uniform
additive modules over any topological semiring or ring carrying a zero sequence of units
(`TauCeti.HasZeroSequenceOfUnits`). This covers Fréchet spaces, F-spaces, and Banach spaces over
any nontrivially normed field (`ℝ`, `ℂ`, `ℚ_[p]`, …; normed-field users can import
`TauCeti.Analysis.Normed.Ring.ZeroSequenceOfUnits` for the `HasZeroSequenceOfUnits` instance),
as well as complete first-countable modules over Tate rings, without assuming local convexity,
normability, or separability.

## Main results

* **Open mapping and quotient theorems**:
  `LinearMap.isOpenMap_of_complete`, `LinearMap.isQuotientMap_of_complete`,
  `ContinuousLinearMap.isOpenMap_of_complete`, `ContinuousLinearMap.isQuotientMap_of_complete`.
  A surjective continuous linear map between complete first-countable uniform modules (with `T₀`
  target) over a topological semiring with a zero sequence of units is open and a quotient map.
* **Continuous inverse theorem and uniqueness of complete uniformities**:
  `LinearEquiv.continuous_symm_of_complete`,
  `LinearEquiv.toContinuousLinearEquivOfContinuousOfComplete`,
  `ContinuousLinearEquiv.ofBijectiveOfComplete`,
  `ContinuousLinearMap.isUnit_iff_bijective_of_complete`,
  `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap_of_complete`,
  `IsUniformAddGroup.eq_of_le_of_complete`.
  In particular, two comparable complete first-countable uniform group structures making a module
  over a topological semiring with a zero sequence of units topological (with the coarser one
  `T₀`) must coincide.
* **Closed graph and sequential closed graph theorems**:
  `LinearMap.continuous_of_isClosed_graph_of_complete`,
  `LinearMap.continuous_of_seq_closed_graph_of_complete`,
  `ContinuousLinearMap.ofIsClosedGraphOfComplete`,
  `ContinuousLinearMap.ofSeqClosedGraphOfComplete`.
  First-countability of the product comes directly from countable generation of `𝓝 0`
  (`TauCeti.ContinuousConstVAdd.toFirstCountableTopology`), with no metric required.
* **Strictness and range equivalence**:
  `LinearMap.isStrictMap_of_isClosed_range_of_complete`,
  `ContinuousLinearMap.isStrictMap_of_isClosed_range_of_complete`,
  `ContinuousLinearMap.isOpenMap_rangeRestrict_of_isClosed_range_of_complete`, and
  `ContinuousLinearMap.equivRangeOfComplete`.

Complement and finite-cokernel closed-range applications built on these results live in
`TauCeti.Topology.Algebra.Module.Complement` and `TauCeti.Topology.Algebra.Module.FiniteDimension`,
respectively.

## Attribution

The API shapes for the continuous inverse, closed graph, and range-equivalence results generalise
the Banach-space theorems in `Mathlib/Analysis/Normed/Operator/Banach.lean`, and their proofs and
constructor packaging are adapted directly from the Tate-ring formalisation in
`TauCeti/Analysis/Normed/Operator/RingOpNorm/OpenMapping.lean` (covering the inverse and
bijective-equivalence constructors, unit criterion, closed-graph theorems and constructors, and
closed-range strictness, openness, and range-equivalence results).

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

section Semiring

variable {R E F : Type*} [Semiring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousConstSMul R F]

namespace LinearMap

/-- **Banach–Schauder open mapping theorem for linear maps.** A surjective linear map, continuous
at zero, between complete first-countable uniform modules (with `T₀` target) over a topological
semiring with a zero sequence of units is open. -/
theorem isOpenMap_of_complete (f : E →ₗ[R] F) (hf : Surjective f)
    (hfc : ContinuousAt (f : E → F) 0) : IsOpenMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact TauCeti.HasZeroSequenceOfUnits.isOpenMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **Banach–Schauder quotient map theorem for linear maps.** Under the hypotheses of
`LinearMap.isOpenMap_of_complete`, the topology of `F` is coinduced by `f`. -/
theorem isQuotientMap_of_complete (f : E →ₗ[R] F) (hf : Surjective f)
    (hfc : ContinuousAt (f : E → F) 0) : IsQuotientMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact TauCeti.HasZeroSequenceOfUnits.isQuotientMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

end LinearMap

namespace ContinuousLinearMap

/-- **Banach–Schauder / Fréchet open mapping theorem.** Every surjective continuous linear map
between complete first-countable uniform modules (with `T₀` target) over a topological semiring
with a zero sequence of units is an open map.

This covers Fréchet spaces, F-spaces, and Banach spaces over any nontrivially normed field (such
as `ℝ`, `ℂ`, or `ℚ_[p]`) as well as complete first-countable modules over Tate rings, without
assuming local convexity, normability, or separability. -/
theorem isOpenMap_of_complete (f : E →L[R] F) (hf : Surjective f) : IsOpenMap f :=
  f.toLinearMap.isOpenMap_of_complete hf f.continuous.continuousAt

/-- **Banach–Schauder / Fréchet quotient map theorem.** Under the hypotheses of
`ContinuousLinearMap.isOpenMap_of_complete` (over a topological semiring with a zero sequence of
units), every surjective continuous linear map between complete first-countable uniform modules
(with `T₀` target) is a quotient map. -/
theorem isQuotientMap_of_complete (f : E →L[R] F) (hf : Surjective f) : IsQuotientMap f :=
  f.toLinearMap.isQuotientMap_of_complete hf f.continuous.continuousAt

end ContinuousLinearMap

namespace LinearEquiv

/-- **Banach–Schauder continuous inverse theorem.** If a linear equivalence between complete
first-countable uniform modules (with `T₀` target) over a topological semiring with a zero
sequence of units is continuous, then its inverse is also continuous. -/
theorem continuous_symm_of_complete (e : E ≃ₗ[R] F) (he : Continuous e) : Continuous e.symm :=
  e.toEquiv.continuous_symm_iff.mpr
    (e.toLinearMap.isOpenMap_of_complete e.surjective he.continuousAt)

/-- Promote a continuous linear equivalence between complete first-countable uniform modules (with
`T₀` target) over a topological semiring with a zero sequence of units to a
`ContinuousLinearEquiv`. -/
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
first-countable uniform modules (with `T₀` target) over a topological semiring with a zero
sequence of units is a continuous linear equivalence. -/
noncomputable def ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) : E ≃L[R] F :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuousOfComplete
    f.continuous

@[simp]
theorem toLinearEquiv_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    (ofBijectiveOfComplete f hf).toLinearEquiv = LinearEquiv.ofBijective f.toLinearMap hf :=
  (rfl)

@[simp]
theorem coeFn_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    ⇑(ofBijectiveOfComplete f hf) = f :=
  (rfl)

@[simp]
theorem coe_ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) :
    (ofBijectiveOfComplete f hf : E →L[R] F) = f := by
  ext
  rfl

@[simp]
theorem ofBijectiveOfComplete_apply (f : E →L[R] F) (hf : Bijective f) (x : E) :
    ofBijectiveOfComplete f hf x = f x :=
  (rfl)

@[simp]
theorem ofBijectiveOfComplete_symm_apply_apply (f : E →L[R] F) (hf : Bijective f) (x : E) :
    (ofBijectiveOfComplete f hf).symm (f x) = x :=
  (ofBijectiveOfComplete f hf).symm_apply_apply x

@[simp]
theorem ofBijectiveOfComplete_apply_symm_apply (f : E →L[R] F) (hf : Bijective f) (y : F) :
    f ((ofBijectiveOfComplete f hf).symm y) = y :=
  (ofBijectiveOfComplete f hf).apply_symm_apply y

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module over a
topological semiring with a zero sequence of units is a unit in `E →L[R] E` if and only if it is
bijective. -/
theorem isUnit_iff_bijective_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, hu⟩ ↦ hu ▸ (ContinuousLinearEquiv.ofUnit u).bijective,
    fun hf ↦ ⟨(ContinuousLinearEquiv.ofBijectiveOfComplete f hf).toUnit,
      ContinuousLinearEquiv.coe_ofBijectiveOfComplete f hf⟩⟩

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module over a
topological semiring with a zero sequence of units is a unit in `E →L[R] E` if and only if it is
a unit as a bare linear endomorphism. -/
theorem isUnit_iff_isUnit_toLinearMap_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ IsUnit (f : E →ₗ[R] E) :=
  f.isUnit_iff_bijective_of_complete.trans (Module.End.isUnit_iff _).symm

end ContinuousLinearMap

end Semiring

namespace IsUniformAddGroup

/-- **Uniqueness of comparable complete first-countable uniformities.** If `u₁` and `u₂` are two
complete first-countable uniform additive group structures on a module `E` over a topological
semiring `R` with a zero sequence of units, satisfying
`u₁.toTopologicalSpace ≤ u₂.toTopologicalSpace` (`u₁` finer than `u₂`), `u₂` `T₀`, `ContinuousSMul`
for `u₁`, and `ContinuousConstSMul` for `u₂`, then `u₁ = u₂` (and in particular their topologies
agree). -/
theorem eq_of_le_of_complete (R : Type*) {E : Type*} [Semiring R] [TopologicalSpace R]
    [TauCeti.HasZeroSequenceOfUnits R] [AddCommGroup E] [Module R E]
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
  have hsmul₁' : ∀ x : E, @ContinuousAt R E _ u₁.toTopologicalSpace (fun r : R ↦ r • x) 0 := by
    let : TopologicalSpace E := u₁.toTopologicalSpace
    exact fun _ ↦ (continuous_id.smul continuous_const).continuousAt
  have hucg₂ : (@uniformity E u₂).IsCountablyGenerated :=
    @IsUniformAddGroup.uniformity_countably_generated E u₂ _ hu₂ hcg₂
  have htopgrp₂ : @IsTopologicalAddGroup E u₂.toTopologicalSpace _ :=
    let : UniformSpace E := u₂
    have : IsUniformAddGroup E := hu₂
    inferInstance
  have hbaire₂ : @BaireSpace E u₂.toTopologicalSpace :=
    let : UniformSpace E := u₂
    have : CompleteSpace E := hc₂
    have : (𝓤 E).IsCountablyGenerated := hucg₂
    inferInstance
  have hopen_lin : @IsOpenMap E E u₁.toTopologicalSpace u₂.toTopologicalSpace
      (LinearMap.id : E →ₗ[R] E) :=
    @TauCeti.HasZeroSequenceOfUnits.isOpenMap R E E _ _ _ _ u₁ hu₁ hc₁ hcg₁ _
      _ u₂.toTopologicalSpace htopgrp₂ ht0 hbaire₂ _ hsmul₂
      (E →ₗ[R] E) _ _ _ LinearMap.id
      (by simpa only [LinearMap.id_coe] using surjective_id)
      (by
        simpa only [LinearMap.id_coe] using
          (@Continuous.continuousAt E E u₁.toTopologicalSpace u₂.toTopologicalSpace id 0
            (continuous_id_iff_le.mpr hle)))
      hsmul₁'
  have hopen : @IsOpenMap E E u₁.toTopologicalSpace u₂.toTopologicalSpace id := by
    simpa only [LinearMap.id_coe] using hopen_lin
  have hle' : u₂.toTopologicalSpace ≤ u₁.toTopologicalSpace :=
    continuous_id_iff_le.mp <|
      (@continuous_def E E u₂.toTopologicalSpace u₁.toTopologicalSpace id).mpr fun s hs ↦ by
        simpa only [Set.preimage_id, Set.image_id] using hopen s hs
  have htop : u₁.toTopologicalSpace = u₂.toTopologicalSpace := le_antisymm hle hle'
  exact hu₁.ext hu₂ (by rw [htop])

end IsUniformAddGroup

/-! ### Closed graph theorem -/

section ClosedGraph

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [T0Space E] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [Module R F] [ContinuousSMul R F]

namespace LinearMap

/-- **Banach–Schauder closed graph theorem.** A linear map between complete first-countable
uniform modules (with `T₀` domain) over a ring with a zero sequence of units is continuous if its
graph is closed in `E × F`.

Only the domain `E` needs to be `T₀`, because the continuous inverse theorem is applied to the
first projection `f.graph → E`. -/
theorem continuous_of_isClosed_graph_of_complete (f : E →ₗ[R] F)
    (hg : IsClosed (f.graph : Set (E × F))) : Continuous f := by
  have : CompleteSpace f.graph := hg.completeSpace_coe
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let φ₀ : E →ₗ[R] E × F := LinearMap.id.prod f
  have hleft : LeftInverse Prod.fst φ₀ := fun _ ↦ rfl
  let φ : E ≃ₗ[R] f.graph :=
    (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)
  have hφ : Continuous φ :=
    φ.symm.continuous_symm_of_complete continuous_subtypeVal.fst
  exact (continuous_subtypeVal.comp hφ).snd

/-- **Sequential closed graph theorem.** A linear map between complete first-countable uniform
modules (with `T₀` domain) over a topological ring with a zero sequence of units is continuous if
its graph is sequentially closed: whenever `u n → x` and `f (u n) → y`, one has `y = f x`.

First-countability of `E × F` follows from countable generation of `𝓝 (0 : E)` and `𝓝 (0 : F)`
without introducing a metric. -/
theorem continuous_of_seq_closed_graph_of_complete (f : E →ₗ[R] F)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    Continuous f := by
  refine f.continuous_of_isClosed_graph_of_complete (IsSeqClosed.isClosed ?_)
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
`T₀` domain) over a topological ring with a zero sequence of units as a `ContinuousLinearMap`. -/
def ofIsClosedGraphOfComplete (hg : IsClosed (f.graph : Set (E × F))) : E →L[R] F where
  toLinearMap := f
  cont := f.continuous_of_isClosed_graph_of_complete hg

@[simp]
theorem coeFn_ofIsClosedGraphOfComplete (hg : IsClosed (f.graph : Set (E × F))) :
    ⇑(ofIsClosedGraphOfComplete hg) = f :=
  (rfl)

@[simp]
theorem coe_ofIsClosedGraphOfComplete (hg : IsClosed (f.graph : Set (E × F))) :
    (ofIsClosedGraphOfComplete hg : E →ₗ[R] F) = f :=
  (rfl)

@[simp]
theorem ofIsClosedGraphOfComplete_apply (hg : IsClosed (f.graph : Set (E × F))) (x : E) :
    ofIsClosedGraphOfComplete hg x = f x :=
  (rfl)

/-- Bundle a linear map with sequentially closed graph between complete first-countable uniform
modules (with `T₀` domain) over a topological ring with a zero sequence of units as a
`ContinuousLinearMap`. -/
def ofSeqClosedGraphOfComplete
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    E →L[R] F where
  toLinearMap := f
  cont := f.continuous_of_seq_closed_graph_of_complete hg

@[simp]
theorem coeFn_ofSeqClosedGraphOfComplete
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    ⇑(ofSeqClosedGraphOfComplete hg) = f :=
  (rfl)

@[simp]
theorem coe_ofSeqClosedGraphOfComplete
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    (ofSeqClosedGraphOfComplete hg : E →ₗ[R] F) = f :=
  (rfl)

@[simp]
theorem ofSeqClosedGraphOfComplete_apply
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) (x : E) :
    ofSeqClosedGraphOfComplete hg x = f x :=
  (rfl)

end ContinuousLinearMap

end ClosedGraph

/-! ### Strictness and range equivalence -/

section StrictAndRangeEquiv

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousConstSMul R F]

namespace LinearMap

/-- A linear map continuous at zero with closed range between complete first-countable uniform
modules (with `T₀` target) over a topological ring with a zero sequence of units is strict
(`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_complete (f : E →ₗ[R] F)
    (hfc : ContinuousAt (f : E → F) 0) (hr : IsClosed (f.range : Set F)) :
    Topology.IsStrictMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact f.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits hfc
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt) hr

end LinearMap

namespace ContinuousLinearMap

/-- A continuous linear map with closed range between complete first-countable uniform modules
(with `T₀` target) over a topological ring with a zero sequence of units is strict
(`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_complete (f : E →L[R] F)
    (hr : IsClosed (f.range : Set F)) : Topology.IsStrictMap f :=
  f.toLinearMap.isStrictMap_of_isClosed_range_of_complete f.continuous.continuousAt hr

/-- A continuous linear map with closed range between complete first-countable uniform modules
(with `T₀` target) over a topological ring with a zero sequence of units is open onto its
range. -/
theorem isOpenMap_rangeRestrict_of_isClosed_range_of_complete (f : E →L[R] F)
    (hr : IsClosed (f.range : Set F)) : IsOpenMap f.rangeRestrict :=
  (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp
    (f.isStrictMap_of_isClosed_range_of_complete hr)).isOpenMap

/-- An injective continuous linear map with closed range between complete first-countable uniform
modules (with `T₀` target) over a topological ring with a zero sequence of units induces a
continuous linear equivalence onto its range. -/
noncomputable def equivRangeOfComplete (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) : E ≃L[R] f.range := by
  have : CompleteSpace f.range := hr.completeSpace_coe
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact (LinearEquiv.ofInjective f.toLinearMap hinj).toContinuousLinearEquivOfContinuousOfComplete
    ((f.continuous.codRestrict _).congr fun _ ↦ rfl)

@[simp]
theorem toLinearEquiv_equivRangeOfComplete (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) :
    (f.equivRangeOfComplete hinj hr).toLinearEquiv = LinearEquiv.ofInjective f.toLinearMap hinj :=
  (rfl)

@[simp]
theorem coeFn_equivRangeOfComplete (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) :
    ⇑(f.equivRangeOfComplete hinj hr) = f.rangeRestrict :=
  (rfl)

@[simp]
theorem coe_equivRangeOfComplete (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) :
    (f.equivRangeOfComplete hinj hr : E →L[R] f.range) = f.rangeRestrict := by
  ext
  rfl

@[simp]
theorem equivRangeOfComplete_apply (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) (x : E) :
    f.equivRangeOfComplete hinj hr x = f.rangeRestrict x :=
  (rfl)

@[simp]
theorem equivRangeOfComplete_symm_apply_apply (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) (x : E) :
    (f.equivRangeOfComplete hinj hr).symm ⟨f x, f.mem_range_self x⟩ = x :=
  (f.equivRangeOfComplete hinj hr).symm_apply_apply x

end ContinuousLinearMap

end StrictAndRangeEquiv

end
