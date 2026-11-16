/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Henkel
public import TauCeti.Analysis.Normed.Ring.ZeroSequenceOfUnits
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.Algebra.Group.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# The Banach–Schauder open mapping, closed graph, and complement theorems

This file packages the Banach–Schauder mapping theorems for complete first-countable uniform
additive modules over any topological ring carrying a zero sequence of units
(`TauCeti.HasZeroSequenceOfUnits`). In particular, by
`TauCeti.HasZeroSequenceOfUnits.of_nontriviallyNormedField`, every result applies uniformly to
Fréchet spaces, F-spaces, and Banach spaces over any nontrivially normed field (`ℝ`, `ℂ`,
`ℚ_[p]`, …), as well as to complete first-countable modules over Tate rings, without assuming
local convexity, normability, or separability.

## Main results

* **Open mapping and quotient theorems**:
  `TauCeti.HasZeroSequenceOfUnits.isOpenMap_of_complete`,
  `TauCeti.HasZeroSequenceOfUnits.isQuotientMap_of_complete`,
  `LinearMap.isOpenMap_of_complete`, `LinearMap.isQuotientMap_of_complete`,
  `ContinuousLinearMap.isOpenMap_of_complete`, `ContinuousLinearMap.isQuotientMap_of_complete`.
  A surjective continuous linear map between complete first-countable uniform modules (with `T₀`
  target) is open and a quotient map.
* **Continuous inverse theorem and uniqueness of complete uniformities**:
  `LinearEquiv.continuous_symm_of_complete`,
  `LinearEquiv.toContinuousLinearEquivOfContinuousOfComplete`,
  `ContinuousLinearEquiv.ofBijectiveOfComplete`,
  `ContinuousLinearMap.isUnit_iff_bijective_of_complete`,
  `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap_of_complete`,
  `IsUniformAddGroup.eq_of_le_of_complete`.
  In particular, two comparable complete first-countable uniform group structures making a module
  topological (with the coarser one `T₀`) must coincide.
* **Closed graph and sequential closed graph theorems**:
  `LinearMap.continuous_of_isClosed_graph_of_complete`,
  `LinearMap.continuous_of_seq_closed_graph_of_complete`,
  `ContinuousLinearMap.ofIsClosedGraphOfComplete`,
  `ContinuousLinearMap.ofSeqClosedGraphOfComplete`.
  First-countability of the product comes directly from countable generation of `𝓝 0`
  (`TauCeti.ContinuousConstVAdd.toFirstCountableTopology`), with no metric required.
* **Strictness, closed complements, and closed range**:
  `LinearMap.isStrictMap_of_isClosed_range_of_complete`,
  `ContinuousLinearMap.isStrictMap_of_isClosed_range_of_complete`,
  `ContinuousLinearMap.isOpenMap_rangeRestrict_of_isClosed_range_of_complete`,
  `ContinuousLinearMap.equivRangeOfComplete`,
  `ContinuousLinearMap.equivProdOfSurjectiveOfIsComplOfComplete`,
  `Submodule.IsCompl.isTopCompl_of_isClosed_of_complete`,
  `Submodule.isTopCompl_iff_isCompl_isClosed_of_complete`,
  `Submodule.ClosedComplemented.of_isCompl_isClosed_of_complete`,
  `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl_of_complete`,
  `ContinuousLinearMap.isClosed_range_of_isCompl_of_complete`, and
  `ContinuousLinearMap.isClosed_range_of_finite_coker_of_complete`.
  A continuous linear map whose range admits a closed algebraic complement (and in particular,
  over a complete nontrivially normed field, any map with finite-dimensional cokernel)
  automatically has closed range, with no injectivity hypothesis on the map.

## Attribution

The API shapes for the continuous inverse, closed graph, range equivalence, and complemented
subspace results generalise the Banach-space theorems in
`Mathlib/Analysis/Normed/Operator/Banach.lean` and
`Mathlib/Analysis/Normed/Module/Complemented.lean` to complete first-countable uniform modules.
The quotient-map proof of `ContinuousLinearMap.isClosed_range_of_isCompl_of_complete` and
`ContinuousLinearMap.isClosed_range_of_finite_coker_of_complete` generalises the Banach-space
argument in `TauCeti/Analysis/Fredholm/ClosedRange.lean`.

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

/-! ### Equivariant open mapping and quotient theorems for complete targets -/

namespace TauCeti.HasZeroSequenceOfUnits

variable {A M N : Type*} [MonoidWithZero A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓝 (0 : M)).IsCountablyGenerated] [MulActionWithZero A M]
  [AddGroup N] [UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
  [(𝓝 (0 : N)).IsCountablyGenerated] [T0Space N] [MulAction A N] [ContinuousConstSMul A N]

/-- **Banach–Schauder / Henkel open mapping theorem for complete first-countable targets.**
A surjective `A`-equivariant additive map, continuous at zero, between complete first-countable
uniform additive groups (with `T₀` target) is open, provided `A` carries a zero sequence of units
and the scalar action on the source is continuous in the scalar at zero.

Countable generation of `𝓝 (0 : N)` yields a countably generated uniformity on `N`, which
together with completeness makes `N` completely pseudometrisable and hence a Baire space. -/
theorem isOpenMap_of_complete {F : Type*} [FunLike F M N] [MulActionHomClass F A M N]
    [AddMonoidHomClass F M N] (f : F) (hf : Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsOpenMap (f : M → N) := by
  have : (𝓤 N).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact HasZeroSequenceOfUnits.isOpenMap f hf hfc hc

/-- **Quotient form of the Banach–Schauder / Henkel open mapping theorem.** Under the hypotheses
of `TauCeti.HasZeroSequenceOfUnits.isOpenMap_of_complete`, the target carries the quotient
topology coinduced by `f`. -/
theorem isQuotientMap_of_complete {F : Type*} [FunLike F M N] [MulActionHomClass F A M N]
    [AddMonoidHomClass F M N] (f : F) (hf : Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsQuotientMap (f : M → N) := by
  have : (𝓤 N).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact HasZeroSequenceOfUnits.isQuotientMap f hf hfc hc

end TauCeti.HasZeroSequenceOfUnits

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
    (hfc : ContinuousAt (f : E → F) 0) : IsOpenMap (f : E → F) :=
  TauCeti.HasZeroSequenceOfUnits.isOpenMap_of_complete f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **Banach–Schauder quotient map theorem for linear maps.** Under the hypotheses of
`LinearMap.isOpenMap_of_complete`, the topology of `F` is coinduced by `f`. -/
theorem isQuotientMap_of_complete (f : E →ₗ[R] F) (hf : Surjective f)
    (hfc : ContinuousAt (f : E → F) 0) : IsQuotientMap (f : E → F) :=
  TauCeti.HasZeroSequenceOfUnits.isQuotientMap_of_complete f hf hfc
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

/-- **Banach–Schauder / Fréchet quotient map theorem.** Every surjective continuous linear map
between complete first-countable uniform modules (with `T₀` target) is a quotient map. -/
theorem isQuotientMap_of_complete (f : E →L[R] F) (hf : Surjective f) : IsQuotientMap f :=
  f.toLinearMap.isQuotientMap_of_complete hf f.continuous.continuousAt

end ContinuousLinearMap

namespace LinearEquiv

/-- **Banach–Schauder continuous inverse theorem.** If a linear equivalence between complete
first-countable uniform modules (with `T₀` target) is continuous, then its inverse is also
continuous. -/
theorem continuous_symm_of_complete (e : E ≃ₗ[R] F) (he : Continuous e) : Continuous e.symm :=
  continuous_def.mpr fun s hs ↦
    e.toEquiv.image_eq_preimage_symm s ▸
      e.toLinearMap.isOpenMap_of_complete e.surjective he.continuousAt s hs

/-- Promote a continuous linear equivalence between complete first-countable uniform modules (with
`T₀` target) to a `ContinuousLinearEquiv`. -/
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
first-countable uniform modules (with `T₀` target) is a continuous linear equivalence. -/
noncomputable def ofBijectiveOfComplete (f : E →L[R] F) (hf : Bijective f) : E ≃L[R] F :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuousOfComplete
    f.continuous

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

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module is a unit
in `E →L[R] E` if and only if it is bijective. -/
theorem isUnit_iff_bijective_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, hu⟩ ↦ hu ▸ (ContinuousLinearEquiv.ofUnit u).bijective,
    fun hf ↦ ⟨(ContinuousLinearEquiv.ofBijectiveOfComplete f hf).toUnit,
      ContinuousLinearEquiv.coe_ofBijectiveOfComplete f hf⟩⟩

/-- A continuous linear endomorphism of a `T₀` complete first-countable uniform module is a unit
in `E →L[R] E` if and only if it is a unit as a bare linear endomorphism. -/
theorem isUnit_iff_isUnit_toLinearMap_of_complete [T0Space E] (f : E →L[R] E) :
    IsUnit f ↔ IsUnit (f : E →ₗ[R] E) :=
  f.isUnit_iff_bijective_of_complete.trans (Module.End.isUnit_iff _).symm

end ContinuousLinearMap

end Semiring

namespace IsUniformAddGroup

/-- **Uniqueness of comparable complete first-countable uniformities.** If `u₁` and `u₂` are two
complete first-countable uniform additive group structures on an `R`-module `E` with
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
  have hopen : @IsOpenMap E E u₁.toTopologicalSpace u₂.toTopologicalSpace id :=
    @TauCeti.HasZeroSequenceOfUnits.isOpenMap_of_complete R E E _ _ _ _ u₁ hu₁ hc₁ hcg₁ _
      _ u₂ hu₂ hc₂ hcg₂ ht0 _ hsmul₂ (E →ₗ[R] E) _ _ _ LinearMap.id surjective_id
      (@Continuous.continuousAt E E u₁.toTopologicalSpace u₂.toTopologicalSpace id 0
        (continuous_id_iff_le.mpr hle))
      hsmul₁'
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
    φ.symm.continuous_symm_of_complete continuous_subtype_val.fst
  exact (continuous_subtype_val.comp hφ).snd

/-- **Sequential closed graph theorem.** A linear map between complete first-countable uniform
modules (with `T₀` domain) is continuous if its graph is sequentially closed: whenever `u n → x`
and `f (u n) → y`, one has `y = f x`.

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
    exact (hφg n).symm
  rw [hcomp]
  exact (continuous_snd.tendsto _).comp hφ

end LinearMap

namespace ContinuousLinearMap

variable {f : E →ₗ[R] F}

/-- Bundle a linear map with closed graph between complete first-countable uniform modules (with
`T₀` domain) as a `ContinuousLinearMap`. -/
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
modules (with `T₀` domain) as a `ContinuousLinearMap`. -/
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

/-! ### Strictness, closed complements, and closed range -/

section StrictAndClosedRange

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousConstSMul R F]

namespace LinearMap

/-- A linear map continuous at zero with closed range between complete first-countable uniform
modules (with `T₀` target) is strict (`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_complete (f : E →ₗ[R] F)
    (hfc : ContinuousAt (f : E → F) 0) (hr : IsClosed (f.range : Set F)) :
    Topology.IsStrictMap (f : E → F) := by
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact f.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits hfc
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt) hr

end LinearMap

namespace ContinuousLinearMap

/-- A continuous linear map with closed range between complete first-countable uniform modules
(with `T₀` target) is strict (`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_complete (f : E →L[R] F)
    (hr : IsClosed (f.range : Set F)) : Topology.IsStrictMap f :=
  f.toLinearMap.isStrictMap_of_isClosed_range_of_complete f.continuous.continuousAt hr

/-- A continuous linear map with closed range between complete first-countable uniform modules
(with `T₀` target) is open onto its range. -/
theorem isOpenMap_rangeRestrict_of_isClosed_range_of_complete (f : E →L[R] F)
    (hr : IsClosed (f.range : Set F)) : IsOpenMap f.rangeRestrict :=
  (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp
    (f.isStrictMap_of_isClosed_range_of_complete hr)).isOpenMap

/-- An injective continuous linear map with closed range between complete first-countable uniform
modules (with `T₀` target) induces a continuous linear equivalence onto its range. -/
noncomputable def equivRangeOfComplete (f : E →L[R] F) (hinj : Injective f)
    (hr : IsClosed (f.range : Set F)) : E ≃L[R] f.range := by
  have : CompleteSpace f.range := hr.completeSpace_coe
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact ContinuousLinearEquiv.ofBijectiveOfComplete f.rangeRestrict
    ⟨fun _ _ hxy ↦ hinj (congrArg Subtype.val hxy), f.toLinearMap.surjective_rangeRestrict⟩

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

/-- If `f : E →L[R] F` and `g : E →L[R] G` are surjective continuous linear maps between complete
first-countable uniform modules (with `T₀` targets) whose kernels are algebraic complements, then
`x ↦ (f x, g x)` defines a continuous linear equivalence `E ≃L[R] F × G`. -/
noncomputable def equivProdOfSurjectiveOfIsComplOfComplete {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) : E ≃L[R] F × G :=
  (f.toLinearMap.equivProdOfSurjectiveOfIsCompl g.toLinearMap hf hg
    hfg).toContinuousLinearEquivOfContinuousOfComplete (f.continuous.prodMk g.continuous)

@[simp]
theorem coe_equivProdOfSurjectiveOfIsComplOfComplete {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) :
    (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg : E →L[R] F × G) = f.prod g := by
  ext <;> rfl

@[simp]
theorem equivProdOfSurjectiveOfIsComplOfComplete_toLinearEquiv {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) :
    (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).toLinearEquiv =
      f.toLinearMap.equivProdOfSurjectiveOfIsCompl g.toLinearMap hf hg hfg :=
  (rfl)

@[simp]
theorem equivProdOfSurjectiveOfIsComplOfComplete_apply {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) (x : E) :
    f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg x = (f x, g x) :=
  (rfl)

end ContinuousLinearMap

end StrictAndClosedRange

namespace ContinuousLinearMap

/-- **Closed range from a closed algebraic complement.** If `f : E →L[R] F` is a continuous linear
map between complete first-countable uniform modules (with `T₀` target) and `G` is a closed
algebraic complement of `f.range`, then `f.range` is closed.

No injectivity assumption (`f.ker = ⊥`) is required: the coproduct `Φ(x, y) = f x + y` from
`E × G` onto `F` is a quotient map by `ContinuousLinearMap.isQuotientMap_of_complete`, and the
preimage `Φ ⁻¹' f.range = {p | p.2 = 0}` is closed. -/
theorem isClosed_range_of_isCompl_of_complete {R E F : Type*}
    [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
    [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
    [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
    [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousSMul R F]
    (f : E →L[R] F) (G : Submodule R F) (hG : IsCompl f.range G)
    (hG_closed : IsClosed (G : Set F)) :
    IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG_closed.completeSpace_coe
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let Φ : (E × G) →L[R] F := f.coprod G.subtypeL
  have hsurj : Surjective Φ := LinearMap.range_eq_top.mp <| by
    simpa [Φ, LinearMap.range_coprod] using hG.sup_eq_top
  have hpre : Φ ⁻¹' (f.range : Set F) = {p : E × G | p.2 = 0} := by
    ext p
    simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_ofPred_eq, Φ, coprod_apply,
      Submodule.coe_subtypeL, Submodule.coe_subtype]
    have hfp : f p.1 ∈ f.range := f.mem_range_self p.1
    refine ⟨fun hmem ↦ ?_, fun h0 ↦ by simp [h0]⟩
    have hb : (p.2 : F) ∈ f.range := by simpa using f.range.sub_mem hmem hfp
    have hbot : (p.2 : F) ∈ f.range ⊓ G := ⟨hb, p.2.2⟩
    rw [hG.inf_eq_bot] at hbot
    exact Submodule.coe_eq_zero.mp (by simpa using hbot)
  have hclosed : IsClosed (Φ ⁻¹' (f.range : Set F)) := by
    rw [hpre]
    exact isClosed_eq continuous_snd continuous_const
  exact (Φ.isQuotientMap_of_complete hsurj).isClosed_preimage.mp hclosed

end ContinuousLinearMap

namespace Submodule

variable {R E : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [T0Space E] [Module R E] [ContinuousSMul R E]
  {p q : Submodule R E}

/-- In a `T₀` complete first-countable uniform module over a ring with a zero sequence of units,
two closed algebraic complements are topological complements (`Submodule.IsTopCompl`). -/
theorem IsCompl.isTopCompl_of_isClosed_of_complete (h : IsCompl p q)
    (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) : IsTopCompl p q := by
  have : CompleteSpace p := hp.completeSpace_coe
  have : CompleteSpace q := hq.completeSpace_coe
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  rw [IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl h]
  exact (p.prodEquivOfIsCompl q h).continuous_symm_of_complete (continuous_prodEquivOfIsCompl h)

/-- In a `T₀` complete first-countable uniform module over a ring with a zero sequence of units,
two submodules are topological complements if and only if they are closed algebraic complements. -/
theorem isTopCompl_iff_isCompl_isClosed_of_complete :
    IsTopCompl p q ↔ IsCompl p q ∧ IsClosed (p : Set E) ∧ IsClosed (q : Set E) :=
  ⟨fun h ↦ ⟨h.isCompl, h.isClosed, h.isClosed'⟩,
    fun h ↦ IsCompl.isTopCompl_of_isClosed_of_complete h.1 h.2.1 h.2.2⟩

/-- A closed submodule admitting a closed algebraic complement in a `T₀` complete first-countable
uniform module is topologically complemented (`Submodule.ClosedComplemented`). -/
theorem ClosedComplemented.of_isCompl_isClosed_of_complete (h : IsCompl p q)
    (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  (IsCompl.isTopCompl_of_isClosed_of_complete h hp hq).closedComplemented

/-- In a `T₀` complete first-countable uniform module over a ring with a zero sequence of units,
a submodule is topologically complemented if and only if it is closed and admits a closed algebraic
complement. -/
theorem closedComplemented_iff_isClosed_exists_isClosed_isCompl_of_complete :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ q : Submodule R E, IsClosed (q : Set E) ∧ IsCompl p q :=
  ⟨fun h ↦ ⟨h.isClosed, h.exists_isClosed_isCompl⟩,
    fun ⟨hp, _, hq, h⟩ ↦ .of_isCompl_isClosed_of_complete h hp hq⟩

end Submodule

namespace ContinuousLinearMap

/-- **Closed range from a finite-dimensional cokernel in complete first-countable vector spaces.**
Let `f : E →L[𝕜] F` be a continuous linear map between complete first-countable uniform vector
spaces (with `T₀` target) over a complete nontrivially normed field `𝕜`. If the cokernel
`F ⧸ f.range` is finite dimensional, then `f.range` is closed.

This applies to all Fréchet spaces, F-spaces, and Banach spaces over `ℝ`, `ℂ`, or `ℚ_[p]`, with
no local convexity, normability, or injectivity hypothesis. -/
theorem isClosed_range_of_finite_coker_of_complete {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
    [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (f : E →L[𝕜] F) [FiniteDimensional 𝕜 (F ⧸ f.range)] :
    IsClosed (f.range : Set F) := by
  obtain ⟨G, hG⟩ := f.range.exists_isCompl
  have : FiniteDimensional 𝕜 G := (f.range.quotientEquivOfIsCompl G hG).finiteDimensional
  exact f.isClosed_range_of_isCompl_of_complete G hG G.isClosed_of_finiteDimensional

end ContinuousLinearMap

end
