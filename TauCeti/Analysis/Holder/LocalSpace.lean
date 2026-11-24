/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# The local Hölder spaces `C^{k,α}_loc(Ω)`

For an open set `Ω` of a real normed space `E`, this file constructs the space
`C^{k,α}_loc(Ω, F)` of maps `Ω → F` that are `C^{k,α}` near every compact subset of `Ω`, with its
compact-exhaustion topology. An element is a function `f` on `Ω` such that every compact `K ⊆ Ω`
has an open neighbourhood `U ⊆ Ω` on which `f` lies in the Banach space `C^{k,α}(U)` of
`TauCeti.CkHolderSpaceOn`. On a finite-dimensional `E` these are exactly the functions that are
`C^k` on `Ω` and whose `k`-th derivative is `α`-Hölder on every compact subset of `Ω`
(`TauCeti.CkHolderSpaceLoc.ofContDiffOn`, `TauCeti.CkHolderSpaceLoc.contDiffOn` and
`TauCeti.CkHolderSpaceLoc.exists_holderOnWith_iteratedFDeriv`; a real normed space is locally
compact exactly when it is finite dimensional): this is the space written
`C^{k,α}(Ω)` in Gilbarg–Trudinger, Section 4.1.

The topology is the coarsest one making every restriction map
`C^{k,α}_loc(Ω) → C^{k,α}(U)` continuous, where `U` runs over the open sets with compact closure
contained in `Ω`. Since the `C^{k,α}(U)` norm is the sum of the supremum norms over `U` of the
derivatives through order `k` and the Hölder seminorm over `U` of the `k`-th derivative, this is
the locally convex topology of these seminorms on the relatively compact open subsets of `Ω`. When
`E` is finite dimensional, a countable compact exhaustion of `Ω` already generates it, so the space
is metrizable; with a Banach codomain it is complete, hence a Fréchet space. When `E` is not
locally compact, that is infinite dimensional, the empty set is the only open set with compact
closure, so the topology is indiscrete: the construction is meaningful only for
finite-dimensional `E`.

`C^{k,α}_loc(Ω)` is not the Banach space `C^{k,α}(Ω)` of `TauCeti.CkHolderSpaceOn`, which asks
for bounded derivatives and a global Hölder seminorm over all of `Ω`; the latter includes
continuously into the former (`TauCeti.CkHolderSpaceOn.toLocL`). On `Ω = (-1, 0) ∪ (0, 1)` the
sign function lies in `C^{0,α}_loc(Ω)` but not in `C^{0,α}(Ω)`, and on `(0, 1)` the function
`x ↦ 1 / x` lies in every `C^{k,α}_loc` but is unbounded. Nor is `C^{k,α}_loc(Ω)` a Banach space
under some other norm: for `α ≤ 1`, nonempty `Ω` in a nontrivial finite-dimensional space and a
nontrivial codomain `F`, no neighbourhood of zero is bounded
(`TauCeti.CkHolderSpaceLoc.not_exists_isVonNBounded_mem_nhds_zero`), so no norm induces its
topology.

## Main declarations

* `TauCeti.CkHolderSpaceLoc k α Ω F`: the space `C^{k,α}_loc(Ω, F)` for `Ω : Opens E`.
* `TauCeti.CkHolderSpaceLoc.IsLoc`: the defining property of an element of `C^{k,α}_loc(Ω, F)`.
* `TauCeti.CkHolderSpaceLoc.mk`: the element defined by a function on `Ω` that lies in `C^{k,α}`
  on an open neighbourhood in `Ω` of every compact subset of `Ω`.
* `TauCeti.CkHolderSpaceLoc.exists_ckHolderSpaceOn`: every compact subset of `Ω` has an open
  neighbourhood in `Ω` on which an element lies in `C^{k,α}`.
* `TauCeti.CkHolderSpaceLoc.restrictL`: the continuous linear restriction map to `C^{k,α}(U)` for
  an open `U` with compact closure contained in `Ω`; these maps define the topology
  (`TauCeti.CkHolderSpaceLoc.continuous_iff`, `TauCeti.CkHolderSpaceLoc.tendsto_nhds_iff`).
* `TauCeti.CkHolderSpaceLoc.ofContDiffOn`: on a finite-dimensional space, the element defined by
  a function that is `C^k` on `Ω` with `k`-th derivative `α`-Hölder on every compact subset of `Ω`.
* `TauCeti.CkHolderSpaceLoc.instLocallyConvexSpace`, `TauCeti.CkHolderSpaceLoc.instT2Space`,
  `TauCeti.CkHolderSpaceLoc.instCompleteSpace` and
  `TauCeti.CkHolderSpaceLoc.instMetrizableSpace`: together with the topological vector space
  structure, these make `C^{k,α}_loc(Ω, F)` a Fréchet space when `E` is finite dimensional and `F`
  is complete.
* `TauCeti.CkHolderSpaceLoc.not_exists_isVonNBounded_mem_nhds_zero`: for `α ≤ 1`, nonempty `Ω`,
  `E` nontrivial and finite dimensional, and `F` nontrivial, `C^{k,α}_loc(Ω)` has no bounded
  neighbourhood of zero, so it is not normable.
* `TauCeti.CkHolderSpaceOn.toLocL`: the continuous inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)`.

## Implementation notes

The topology, the uniform structure, the topological vector space and local convexity instances,
`TauCeti.CkHolderSpaceLoc.continuous_iff` and the completeness argument through the uniform
embedding into the product of the spaces `C^{k,α}(U)` follow Mathlib's `ContDiffMapSupportedIn`
(`Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean`).

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open TopologicalSpace Filter Set
open scoped NNReal Topology Uniformity

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {Ω F} in
/-- The defining property of an element of `C^{k,α}_loc(Ω, F)`: every compact subset of `Ω` has an
open neighbourhood `U ⊆ Ω` on which `f` agrees with an element of `C^{k,α}(U, F)`. -/
@[expose] def CkHolderSpaceLoc.IsLoc (f : Ω → F) : Prop :=
  ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ U : Opens E, K ⊆ U ∧
    ∃ hU : U ≤ Ω, ∃ g : CkHolderSpaceOn k α U F, ∀ x : U, g x = f ⟨x, hU x.property⟩

/-- The space `C^{k,α}_loc(Ω, F)` of maps `f : Ω → F` such that every compact subset of `Ω` has an
open neighbourhood `U ⊆ Ω` on which `f` lies in `C^{k,α}(U, F)`. Its topology is the coarsest one
making the restrictions to the open sets with compact closure in `Ω` continuous into
`C^{k,α}(U, F)`. When `E` is not locally compact, that is infinite dimensional, the only such open
set is empty and the topology is indiscrete, so the construction is meaningful only for
finite-dimensional `E`. -/
-- The module system requires exposure while the declarations below construct and project through
-- this submodule alias. The `irreducible` attribute after the basic API restores the abstraction
-- boundary.
@[expose] def CkHolderSpaceLoc : Type _ :=
  ({ carrier := {f : Ω → F | CkHolderSpaceLoc.IsLoc k α f}
     zero_mem' := fun K hKΩ _ ↦ ⟨Ω, hKΩ, le_rfl, 0, fun x ↦ by simp⟩
     add_mem' := fun {f₁ f₂} h₁ h₂ K hKΩ hK ↦ by
       obtain ⟨U₁, hK₁, hU₁, g₁, hg₁⟩ := h₁ K hKΩ hK
       obtain ⟨U₂, hK₂, hU₂, g₂, hg₂⟩ := h₂ K hKΩ hK
       refine ⟨U₁ ⊓ U₂, by simpa using subset_inter hK₁ hK₂, inf_le_left.trans hU₁,
         CkHolderSpaceOn.restrictL inf_le_left g₁ + CkHolderSpaceOn.restrictL inf_le_right g₂,
         fun x ↦ ?_⟩
       simp [hg₁, hg₂]
     smul_mem' := fun c {f} h K hKΩ hK ↦ by
       obtain ⟨U, hKU, hU, g, hg⟩ := h K hKΩ hK
       exact ⟨U, hKU, hU, c • g, fun x ↦ by simp [hg]⟩ } : Submodule ℝ (Ω → F))

namespace CkHolderSpaceLoc

variable {k α Ω F}

/-- Elements are the functions with the defining property. This is the identity map. -/
private def equivSubtype : CkHolderSpaceLoc k α Ω F ≃ {f : Ω → F // IsLoc k α f} :=
  Equiv.refl _

/-- `C^{k,α}_loc(Ω)` is an additive group under pointwise addition. -/
instance instAddCommGroup : AddCommGroup (CkHolderSpaceLoc k α Ω F) := by
  unfold CkHolderSpaceLoc
  infer_instance

/-- `C^{k,α}_loc(Ω)` is a real vector space under pointwise operations. -/
instance instModule : Module ℝ (CkHolderSpaceLoc k α Ω F) := by
  unfold CkHolderSpaceLoc
  infer_instance

/-- The underlying function on `Ω` of an element of `C^{k,α}_loc(Ω)`. Use the coercion `⇑f`
instead. -/
def toFun (f : CkHolderSpaceLoc k α Ω F) : Ω → F :=
  (equivSubtype f).val

/-- An element of `C^{k,α}_loc(Ω)` is determined by its values on `Ω`. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

/-- An element of `C^{k,α}_loc(Ω)` is coerced to its underlying function on `Ω`. -/
instance instFunLike : FunLike (CkHolderSpaceLoc k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

/-- `CkHolderSpaceLoc.toFun f` is equal to the coercion `⇑f` of `f` to a function. -/
@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceLoc k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}_loc(Ω)` are equal when their underlying functions agree on `Ω`. -/
@[ext]
theorem ext {f g : CkHolderSpaceLoc k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The zero element is the zero function. -/
@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpaceLoc k α Ω F) = 0 :=
  (rfl)

/-- Addition is pointwise. -/
@[simp]
theorem coe_add (f g : CkHolderSpaceLoc k α Ω F) : ⇑(f + g) = f + g :=
  (rfl)

/-- Scalar multiplication is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpaceLoc k α Ω F) : ⇑(c • f) = c • ⇑f :=
  (rfl)

attribute [irreducible] instAddCommGroup instModule _root_.TauCeti.CkHolderSpaceLoc

/-- Every compact subset of `Ω` has an open neighbourhood `U ⊆ Ω` on which an element of
`C^{k,α}_loc(Ω)` agrees with an element of `C^{k,α}(U)`. -/
theorem exists_ckHolderSpaceOn (f : CkHolderSpaceLoc k α Ω F) {K : Set E}
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ U : Opens E, K ⊆ U ∧ ∃ hU : U ≤ Ω, ∃ g : CkHolderSpaceOn k α U F,
      ∀ x : U, g x = f ⟨x, hU x.property⟩ :=
  (equivSubtype f).property K hKΩ hK

/-- The element of `C^{k,α}_loc(Ω)` defined by a function `f` on `Ω` such that every compact
subset of `Ω` has an open neighbourhood `U ⊆ Ω` on which `f` agrees with an element of
`C^{k,α}(U)`. -/
def mk (f : Ω → F) (hf : IsLoc k α f) : CkHolderSpaceLoc k α Ω F :=
  equivSubtype.symm ⟨f, hf⟩

/-- The underlying function of `mk f hf` is `f`. -/
@[simp]
theorem mk_apply (f : Ω → F) (hf : IsLoc k α f) (x : Ω) :
    mk f hf x = f x :=
  (rfl)

/-- On an open set whose closure is compact and contained in `Ω`, an element of `C^{k,α}_loc(Ω)`
agrees with an element of `C^{k,α}(U)`. -/
private theorem exists_restrict (f : CkHolderSpaceLoc k α Ω F) {U : Opens E}
    (hU : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω) :
    ∃ g : CkHolderSpaceOn k α U F, ∀ x : U, g x = f ⟨x, hUΩ (subset_closure x.property)⟩ := by
  obtain ⟨V, hUV, hV, g, hg⟩ := f.exists_ckHolderSpaceOn hUΩ hU
  have hUV' : U ≤ V := fun x hx ↦ hUV (subset_closure hx)
  exact ⟨CkHolderSpaceOn.restrictL hUV' g, fun x ↦ by simp [hg]⟩

/-- The restriction of an element of `C^{k,α}_loc(Ω)` to an open set with compact closure in `Ω`,
as a function to `C^{k,α}(U)`. -/
private def restrictFun (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceLoc k α Ω F) : CkHolderSpaceOn k α U F :=
  (f.exists_restrict hU hUΩ).choose

/-- The restriction to `U` has the same values on `U`. -/
@[simp]
private theorem restrictFun_apply (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceLoc k α Ω F) (x : U) :
    restrictFun U hU hUΩ f x = f ⟨x, hUΩ (subset_closure x.property)⟩ :=
  (f.exists_restrict hU hUΩ).choose_spec x

/-- The restriction of an element of `C^{k,α}_loc(Ω)` to an open set with compact closure in `Ω`,
as a linear map to `C^{k,α}(U)`. Use its continuous version `CkHolderSpaceLoc.restrictL` instead;
this linear map only defines the topology. -/
def restrictLM (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) : CkHolderSpaceLoc k α Ω F →ₗ[ℝ] CkHolderSpaceOn k α U F where
  toFun := restrictFun U hU hUΩ
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

/-- The linear restriction to `U` has the same values on `U`. -/
private theorem restrictLM_apply (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceLoc k α Ω F) (x : U) :
    restrictLM U hU hUΩ f x = f ⟨x, hUΩ (subset_closure x.property)⟩ :=
  restrictFun_apply U hU hUΩ f x

variable (Ω) in
/-- The open sets whose closure is compact and contained in `Ω`; they index the restriction maps
defining the topology. -/
private abbrev Idx : Type u :=
  {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω}

/-- The restriction to an index set. -/
private abbrev res (i : Idx Ω) : CkHolderSpaceLoc k α Ω F →ₗ[ℝ] CkHolderSpaceOn k α i.val F :=
  restrictLM i.val i.property.1 i.property.2

/-- The compact-exhaustion topology: the coarsest topology making every restriction to an open
set with compact closure in `Ω` continuous into `C^{k,α}(U)`. -/
-- The index type is spelled out here and in `instUniformSpace` rather than written as `Idx Ω`, and
-- the maps as `restrictLM` rather than `res`, because a public instance body cannot mention the
-- private abbreviations `Idx` and `res`.
instance instTopologicalSpace : TopologicalSpace (CkHolderSpaceLoc k α Ω F) :=
  ⨅ i : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω},
    induced (restrictLM i.val i.property.1 i.property.2) inferInstance

/-- The uniform structure of the compact-exhaustion topology. -/
instance instUniformSpace : UniformSpace (CkHolderSpaceLoc k α Ω F) := .replaceTopology
  (⨅ i : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω},
    UniformSpace.comap (restrictLM i.val i.property.1 i.property.2) inferInstance)
  UniformSpace.toTopologicalSpace_iInf.symm

/-- The uniform structure is the infimum of those pulled back along the restrictions. -/
private theorem uniformSpace_eq_iInf :
    (instUniformSpace : UniformSpace (CkHolderSpaceLoc k α Ω F)) =
      ⨅ i : Idx Ω, UniformSpace.comap (res i) inferInstance :=
  UniformSpace.replaceTopology_eq _ UniformSpace.toTopologicalSpace_iInf.symm

/-- `C^{k,α}_loc(Ω)` is a topological additive group. -/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CkHolderSpaceLoc k α Ω F) :=
  isTopologicalAddGroup_iInf fun _ ↦ isTopologicalAddGroup_induced _

/-- `C^{k,α}_loc(Ω)` is a uniform additive group. -/
instance instIsUniformAddGroup : IsUniformAddGroup (CkHolderSpaceLoc k α Ω F) := by
  rw [uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _

/-- Scalar multiplication on `C^{k,α}_loc(Ω)` is continuous. -/
instance instContinuousSMul : ContinuousSMul ℝ (CkHolderSpaceLoc k α Ω F) :=
  continuousSMul_iInf fun i ↦ continuousSMul_induced
    (restrictLM (k := k) (α := α) (F := F) i.val i.property.1 i.property.2)

/-- `C^{k,α}_loc(Ω)` is locally convex: its topology is induced by the restriction maps to the
normed spaces `C^{k,α}(U)`. -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (CkHolderSpaceLoc k α Ω F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

/-- Restriction of an element of `C^{k,α}_loc(Ω)` to an open set `U` whose closure is compact and
contained in `Ω`, as a continuous linear map to `C^{k,α}(U)`. -/
def restrictL (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) : CkHolderSpaceLoc k α Ω F →L[ℝ] CkHolderSpaceOn k α U F where
  toLinearMap := restrictLM U hU hUΩ
  cont := continuous_iInf_dom (i := ⟨U, ⟨hU, hUΩ⟩⟩) continuous_induced_dom

/-- The restriction to `U` has the same values on `U`. -/
@[simp]
theorem restrictL_apply (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceLoc k α Ω F) (x : U) :
    restrictL U hU hUΩ f x = f ⟨x, hUΩ (subset_closure x.property)⟩ :=
  restrictLM_apply U hU hUΩ f x

/-- Restricting to `U` and then to a smaller `V` is restricting to `V`. -/
@[simp]
theorem restrictL_restrictL {U V : Opens E} (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (h : V ≤ U) (f : CkHolderSpaceLoc k α Ω F) :
    CkHolderSpaceOn.restrictL h (restrictL U hU hUΩ f) =
      restrictL V (hU.of_isClosed_subset isClosed_closure (closure_mono h))
        ((closure_mono h).trans hUΩ) f := by
  ext x
  simp

/-- The universal property of the topology of `C^{k,α}_loc(Ω)`: a map into it is continuous if
and only if its restrictions to the open sets with compact closure in `Ω` are continuous into
`C^{k,α}(U)`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (φ : X → CkHolderSpaceLoc k α Ω F) :
    Continuous φ ↔ ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω), Continuous (restrictL U hU hUΩ ∘ φ) := by
  simp only [continuous_iInf_rng, continuous_induced_rng, Subtype.forall]
  exact ⟨fun h U hU hUΩ ↦ h U ⟨hU, hUΩ⟩, fun h U hU ↦ h U hU.1 hU.2⟩

/-- Convergence in `C^{k,α}_loc(Ω)` is convergence in `C^{k,α}(U)` of the restrictions to every
open set `U` with compact closure in `Ω`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {φ : ι → CkHolderSpaceLoc k α Ω F}
    {f : CkHolderSpaceLoc k α Ω F} :
    Tendsto φ l (𝓝 f) ↔ ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω),
        Tendsto (restrictL U hU hUΩ ∘ φ) l (𝓝 (restrictL U hU hUΩ f)) := by
  simp only [nhds_iInf, nhds_induced, tendsto_iInf, tendsto_comap_iff, Subtype.forall]
  exact ⟨fun h U hU hUΩ ↦ h U ⟨hU, hUΩ⟩, fun h U hU ↦ h U hU.1 hU.2⟩

/-- A function on the whole space that agrees with an element of `C^{k,α}_loc(Ω)` on `Ω` is `C^k`
on `Ω`. -/
theorem contDiffOn (f : CkHolderSpaceLoc k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g Ω := by
  refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
  obtain ⟨U, hxU, hU, g', hg'⟩ :=
    f.exists_ckHolderSpaceOn (singleton_subset_iff.2 hx) isCompact_singleton
  exact ⟨U, U.isOpen, singleton_subset_iff.1 hxU,
    (g'.contDiffOn fun y ↦ (hg ⟨y, hU y.property⟩).trans (hg' y).symm).mono inter_subset_right⟩

/-- The `k`-th iterated derivative of a function on the whole space that agrees with an element of
`C^{k,α}_loc(Ω)` on `Ω` is `α`-Hölder on every compact subset of `Ω`. -/
theorem exists_holderOnWith_iteratedFDeriv (f : CkHolderSpaceLoc k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) {K : Set E} (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K := by
  obtain ⟨U, hKU, hU, g', hg'⟩ := f.exists_ckHolderSpaceOn hKΩ hK
  exact ⟨_, (g'.holderOnWith_iteratedFDeriv fun y ↦ (hg ⟨y, hU y.property⟩).trans
      (hg' y).symm).mono hKU⟩

omit [NormedSpace ℝ E] in
variable (Ω) in
/-- In a locally compact space, every compact subset of `Ω` lies in an open set whose closure is
compact and contained in `Ω`. -/
private theorem exists_idx_superset [LocallyCompactSpace E] {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ i : Idx Ω, K ⊆ i.val := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨⟨V, hVo⟩, hVc, hVΩ⟩, hKV⟩

omit [NormedSpace ℝ E] in
/-- In a locally compact space, every point of `Ω` lies in an open set whose closure is compact and
contained in `Ω`. -/
private theorem exists_idx_mem [LocallyCompactSpace E] {x : E} (hx : x ∈ Ω) :
    ∃ i : Idx Ω, x ∈ i.val := by
  obtain ⟨i, hi⟩ := exists_idx_superset Ω isCompact_singleton (singleton_subset_iff.2 hx)
  exact ⟨i, singleton_subset_iff.1 hi⟩

/-- On a locally compact, that is finite-dimensional, space, the element of `C^{k,α}_loc(Ω)`
defined by a function on the whole space that is `C^k` on `Ω` and whose `k`-th iterated
derivative is `α`-Hölder on every compact subset of `Ω`. Local compactness of `E` is what makes
every compact subset of `Ω` lie in an open set with compact closure in `Ω`, on which the
derivatives through order `k` are bounded. -/
def ofContDiffOn [LocallyCompactSpace E] (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hH : ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K) :
    CkHolderSpaceLoc k α Ω F :=
  mk (fun x ↦ g x) fun K hKΩ hK ↦ by
    obtain ⟨⟨U, hUc, hUΩ⟩, hKU⟩ := exists_idx_superset Ω hK hKΩ
    obtain ⟨C, hC⟩ := hH _ hUΩ hUc
    have hUΩ' : (U : Set E) ⊆ Ω := subset_closure.trans hUΩ
    refine ⟨U, hKU, hUΩ', CkHolderSpaceOn.ofContDiffOn g (hg.mono hUΩ') (fun i hi ↦ ?_)
      ⟨C, (hC.mono subset_closure).holderWith⟩,
      fun x ↦ CkHolderSpaceOn.ofContDiffOn_apply _ _ _ _ x⟩
    have hcont : ContinuousOn (iteratedFDeriv ℝ i g) Ω :=
      ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen (by exact_mod_cast hi)
    obtain ⟨M, hM⟩ := hUc.exists_bound_of_continuousOn (hcont.mono hUΩ)
    exact ⟨M, fun x ↦ hM x (subset_closure x.property)⟩

/-- The underlying function of `ofContDiffOn g` is the restriction of `g` to `Ω`. -/
@[simp]
theorem ofContDiffOn_apply [LocallyCompactSpace E] (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hH : ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K)
    (x : Ω) : ofContDiffOn g hg hH x = g x :=
  (rfl)

/-- On a locally compact, that is finite-dimensional, space, a function on the whole space agrees
on `Ω` with an element of `C^{k,α}_loc(Ω)` exactly when it is `C^k` on `Ω` and its `k`-th iterated
derivative is `α`-Hölder on every compact subset of `Ω`. -/
theorem exists_eq_iff [LocallyCompactSpace E] {g : E → F} :
    (∃ f : CkHolderSpaceLoc k α Ω F, ∀ x : Ω, g x = f x) ↔ ContDiffOn ℝ k g Ω ∧
      ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨f.contDiffOn hf, fun _ hKΩ hK ↦ f.exists_holderOnWith_iteratedFDeriv hf hKΩ hK⟩,
    fun ⟨hg, hH⟩ ↦ ⟨ofContDiffOn g hg hH, fun x ↦ (ofContDiffOn_apply g hg hH x).symm⟩⟩

/-- On a locally compact space, `C^{k,α}_loc(Ω)` is Hausdorff: the restrictions to the open sets
with compact closure in `Ω` separate points. -/
instance instT2Space [LocallyCompactSpace E] : T2Space (CkHolderSpaceLoc k α Ω F) := by
  refine T2Space.of_injective_continuous
    (f := fun f (i : Idx Ω) ↦ restrictL i.val i.property.1 i.property.2 f)
    (fun f g h ↦ ext fun x ↦ ?_) (continuous_pi fun i ↦ (restrictL _ _ _).continuous)
  obtain ⟨i, hi⟩ := exists_idx_mem x.property
  simpa using DFunLike.congr_fun (congr_fun h i) ⟨x, hi⟩

/-- Restricting to a smaller index factors through the restriction to the larger one. -/
private theorem res_eq_comp {i j : Idx Ω} (h : i.val ≤ j.val) :
    (res i : CkHolderSpaceLoc k α Ω F → CkHolderSpaceOn k α i.val F) =
      CkHolderSpaceOn.restrictL h ∘ res j :=
  funext fun f ↦ (restrictL_restrictL j.property.1 j.property.2 h f).symm

/-- The family of all restrictions is a uniform inducing map into the product of the spaces
`C^{k,α}(U)`. -/
private theorem isUniformInducing_pi_res :
    IsUniformInducing (fun f (i : Idx Ω) ↦ res (k := k) (α := α) (F := F) i f) := by
  simp_rw [isUniformInducing_iff_uniformSpace, uniformSpace_eq_iInf, Pi.uniformSpace_eq,
    UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  -- `Idx Ω` and `res i` are the index type and the restriction used to define `instUniformSpace`,
  -- and evaluating the family of restrictions at `i` is `res i` by beta reduction.
  rfl

omit [NormedSpace ℝ E] in
/-- The intersection of two open sets with compact closure in `Ω` is another one. -/
private theorem Idx.exists_coe_eq_inter (i j : Idx Ω) :
    ∃ m : Idx Ω, (m.val : Set E) = (i.val : Set E) ∩ j.val :=
  ⟨⟨i.val ⊓ j.val, i.property.1.of_isClosed_subset isClosed_closure
      (closure_mono inter_subset_left),
    (closure_mono inter_subset_left).trans i.property.2⟩, rfl⟩

/-- A family of elements of the spaces `C^{k,α}(U)` that is compatible under restriction comes from
an element of `C^{k,α}_loc(Ω)`, when `E` is locally compact. -/
private theorem range_pi_res [LocallyCompactSpace E] :
    range (fun f (i : Idx Ω) ↦ res (k := k) (α := α) (F := F) i f) =
      {G | ∀ (i j : Idx Ω) (h : i.val ≤ j.val), CkHolderSpaceOn.restrictL h (G j) = G i} := by
  ext G
  constructor
  · rintro ⟨f, rfl⟩ i j h
    ext x
    simp [restrictLM_apply]
  · intro hG
    have key : ∀ (i j : Idx Ω) (x : E) (hi : x ∈ i.val) (hj : x ∈ j.val),
        G i ⟨x, hi⟩ = G j ⟨x, hj⟩ := fun i j x hi hj ↦ by
      obtain ⟨m, hm⟩ := Idx.exists_coe_eq_inter i j
      have hmi : m.val ≤ i.val := by rw [← SetLike.coe_subset_coe, hm]; exact inter_subset_left
      have hmj : m.val ≤ j.val := by rw [← SetLike.coe_subset_coe, hm]; exact inter_subset_right
      have hxm : x ∈ (m.val : Set E) := by rw [hm]; exact ⟨hi, hj⟩
      have h₁ := DFunLike.congr_fun (hG m i hmi) ⟨x, hxm⟩
      have h₂ := DFunLike.congr_fun (hG m j hmj) ⟨x, hxm⟩
      rw [CkHolderSpaceOn.restrictL_apply] at h₁ h₂
      exact h₁.trans h₂.symm
    choose idx hidx using fun x : Ω ↦ exists_idx_mem x.property
    refine ⟨mk (fun x ↦ G (idx x) ⟨x, hidx x⟩) fun K hKΩ hK ↦ ?_, ?_⟩
    · obtain ⟨j, hKj⟩ := exists_idx_superset Ω hK hKΩ
      exact ⟨j.val, hKj, subset_closure.trans j.property.2, G j, fun y ↦ key _ _ _ _ _⟩
    · funext i
      ext y
      rw [restrictLM_apply]
      exact key _ _ _ _ _

/-- On a locally compact space and with a Banach codomain, `C^{k,α}_loc(Ω)` is complete. -/
instance instCompleteSpace [LocallyCompactSpace E] [CompleteSpace F] :
    CompleteSpace (CkHolderSpaceLoc k α Ω F) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_pi_res, range_pi_res]
  refine IsClosed.isComplete ?_
  simp only [ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun h ↦
    isClosed_eq ((CkHolderSpaceOn.restrictL h).continuous.comp (continuous_apply j))
      (continuous_apply i)

/-- On a locally compact space, the restrictions to a countable family of open sets with compact
closure in `Ω`, cofinal among all of them, already generate the uniformity of `C^{k,α}_loc(Ω)`;
so the uniformity is countably generated. -/
private theorem isCountablyGenerated_uniformity [LocallyCompactSpace E] :
    IsCountablyGenerated (𝓤 (CkHolderSpaceLoc k α Ω F)) := by
  have : ProperSpace E := ProperSpace.of_locallyCompactSpace ℝ
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨L, hLc, hLΩ, -, hL⟩ :=
    Ω.isOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset
  choose V hV using fun m ↦ exists_idx_superset Ω (hLc m) (hLΩ m)
  have hcof : ∀ i : Idx Ω, ∃ m, i.val ≤ (V m).val := fun i ↦ by
    obtain ⟨m, hm⟩ := hL _ i.property.1 i.property.2
    exact ⟨m, fun x hx ↦ hV m (hm (subset_closure hx))⟩
  let A : Idx Ω → Filter (CkHolderSpaceLoc k α Ω F × CkHolderSpaceLoc k α Ω F) := fun i ↦
    comap (Prod.map (res i) (res i)) (𝓤 (CkHolderSpaceOn k α i.val F))
  have hU : 𝓤 (CkHolderSpaceLoc k α Ω F) = ⨅ i, A i := by
    rw [congrArg (@uniformity _) uniformSpace_eq_iInf, iInf_uniformity]
    simp only [uniformity_comap, A]
  have hA : ⨅ i, A i = ⨅ m, A (V m) := by
    refine le_antisymm (le_iInf fun m ↦ iInf_le _ _) (le_iInf fun i ↦ ?_)
    obtain ⟨m, hm⟩ := hcof i
    refine iInf_le_of_le m ?_
    simp only [A, res_eq_comp hm]
    rw [← Prod.map_comp_map, ← comap_comap]
    exact comap_mono (CkHolderSpaceOn.restrictL hm).uniformContinuous.le_comap
  rw [hU, hA]
  infer_instance

/-- On a locally compact space, `C^{k,α}_loc(Ω)` is metrizable: a countable compact exhaustion of
`Ω` generates its topology. With a Banach codomain it is therefore a Fréchet space. -/
instance instMetrizableSpace [LocallyCompactSpace E] :
    MetrizableSpace (CkHolderSpaceLoc k α Ω F) :=
  haveI := isCountablyGenerated_uniformity (k := k) (α := α) (Ω := Ω) (F := F)
  UniformSpace.metrizableSpace

omit [NormedSpace ℝ E] in
/-- Two open sets with compact closure in `Ω` lie in a third one, their union. -/
private theorem Idx.exists_le_and_le (i j : Idx Ω) : ∃ m : Idx Ω, i.val ≤ m.val ∧ j.val ≤ m.val :=
  ⟨⟨i.val ⊔ j.val, by simpa [closure_union] using i.property.1.union j.property.1,
    by simpa [closure_union] using union_subset i.property.2 j.property.2⟩,
    le_sup_left, le_sup_right⟩

/-- In a nontrivial space, a nonempty open set `Ω` is never covered by the closure of an open set
with compact closure in `Ω`: otherwise `Ω` would be clopen, hence the whole space, hence
compact. -/
private theorem exists_mem_notMem_closure [Nontrivial E] (hΩ : (Ω : Set E).Nonempty)
    (i : Idx Ω) : ∃ x ∈ (Ω : Set E), x ∉ closure (i.val : Set E) := by
  by_contra! h
  have heq : (Ω : Set E) = closure (i.val : Set E) := subset_antisymm h i.property.2
  have hclosed : IsClosed (Ω : Set E) := by
    rw [heq]
    exact isClosed_closure
  have huniv : (Ω : Set E) = univ := IsClopen.eq_univ ⟨hclosed, Ω.isOpen⟩ hΩ
  have hcompact : IsCompact (univ : Set E) := by
    rw [← huniv, heq]
    exact i.property.1
  exact noncompact_univ E hcompact

/-- Every neighbourhood of zero in `C^{k,α}_loc(Ω)` contains the preimage of a neighbourhood of
zero under a single restriction: the restrictions form a directed family. -/
private theorem exists_res_preimage_subset {s : Set (CkHolderSpaceLoc k α Ω F)}
    (hs : s ∈ 𝓝 0) : ∃ i : Idx Ω, ∃ t ∈ 𝓝 (0 : CkHolderSpaceOn k α i.val F), res i ⁻¹' t ⊆ s := by
  have hdir : Directed (· ≥ ·)
      fun i : Idx Ω ↦ comap (res (k := k) (α := α) (F := F) i) (𝓝 0) := fun i j ↦ by
    obtain ⟨m, him, hjm⟩ := Idx.exists_le_and_le i j
    have key {i : Idx Ω} (h : i.val ≤ m.val) :
        comap (res (k := k) (α := α) (F := F) m) (𝓝 0) ≤ comap (res i) (𝓝 0) := by
      rw [res_eq_comp h, ← comap_comap]
      exact comap_mono ((CkHolderSpaceOn.restrictL h).continuous.tendsto' 0 0
        (map_zero _)).le_comap
    exact ⟨m, key him, key hjm⟩
  have hne : Nonempty (Idx Ω) := ⟨⟨⊥, by simp, by simp⟩⟩
  rw [nhds_iInf] at hs
  simp only [nhds_induced, map_zero] at hs
  obtain ⟨i, hi⟩ := (mem_iInf_of_directed hdir s).1 hs
  exact ⟨i, mem_comap.1 hi⟩

/-- A bump function: for `x ∈ Ω` outside the closure of an open set `U` with compact closure in
`Ω`, and `α ≤ 1`, some element of `C^{k,α}_loc(Ω)` takes the value `v` at `x` and vanishes on
`U`. -/
private theorem exists_res_eq_zero_apply_eq [LocallyCompactSpace E] (hα : α ≤ 1) (i : Idx Ω)
    {x : E} (hxΩ : x ∈ Ω) (hxi : x ∉ closure (i.val : Set E)) (v : F) :
    ∃ f : CkHolderSpaceLoc k α Ω F, res i f = 0 ∧ f ⟨x, hxΩ⟩ = v := by
  have : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Ω.isOpen.sdiff isClosed_closure) x ⟨hxΩ, hxi⟩
  let b : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : ContDiff ℝ (k + 1 : ℕ) fun y ↦ b y • v := b.contDiff.smul contDiff_const
  have hφc : HasCompactSupport fun y ↦ b y • v := b.hasCompactSupport.smul_right
  refine ⟨ofContDiffOn (fun y ↦ b y • v) (hφ.of_le (by exact_mod_cast k.le_succ)).contDiffOn
    fun K _ _ ↦ ?_, ?_, ?_⟩
  · obtain ⟨C, hC, -⟩ := (hφ.iteratedFDeriv_right (m := 1) (i := k) (by norm_cast; omega)
      ).exists_holderWith_and_norm_le_of_hasCompactSupport (hφc.iteratedFDeriv k) hα
    exact ⟨C, hC.holderOnWith _⟩
  · ext y
    have hby : b y = 0 :=
      b.zero_of_le_dist (not_lt.1 fun h ↦ (hball (Metric.mem_ball.2 h)).2
          (subset_closure y.property))
    simp [restrictLM_apply, hby]
  · rw [ofContDiffOn_apply,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr).le), one_smul]

/-- `C^{k,α}_loc(Ω)` is not normable: no neighbourhood of zero is von Neumann bounded, which by
Kolmogorov's criterion rules out any norm inducing its topology.

Each hypothesis is necessary: for `α > 1` and connected `Ω` the space consists of polynomials of
degree at most `k` and is normable (a finite product of spaces of symmetric multilinear maps into
`F`); for `E` not locally compact the topology is indiscrete, so every set is bounded; for `E`
trivial `Ω` is a point and the space is `F`; for `F` trivial or `Ω` empty the space is zero. -/
theorem not_exists_isVonNBounded_mem_nhds_zero [LocallyCompactSpace E] [Nontrivial E]
    [Nontrivial F] (hα : α ≤ 1) (hΩ : (Ω : Set E).Nonempty) :
    ¬ ∃ s ∈ 𝓝 (0 : CkHolderSpaceLoc k α Ω F), Bornology.IsVonNBounded ℝ s := by
  -- Every neighbourhood of zero contains all functions vanishing on some open set `U` with compact
  -- closure in `Ω`, while a bump function supported in `Ω` away from `U` is unbounded in the
  -- seminorm of a larger open set.
  rintro ⟨s, hs0, hs⟩
  obtain ⟨i, t, ht, hts⟩ := exists_res_preimage_subset hs0
  obtain ⟨x, hxΩ, hxi⟩ := exists_mem_notMem_closure hΩ i
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  obtain ⟨f, hres0, hfx⟩ := exists_res_eq_zero_apply_eq hα i hxΩ hxi v
  -- Every multiple of `f` lies in `s`, since its restriction to `i` vanishes.
  have hmem (c : ℝ) : c • f ∈ s := hts <| by
    rw [mem_preimage, map_smul, hres0, smul_zero]
    exact mem_of_mem_nhds ht
  -- But `f` has norm at least `‖v‖` on an open set containing `x`.
  obtain ⟨j, hj⟩ := exists_idx_mem hxΩ
  let V := restrictL (k := k) (α := α) (F := F) j.val j.property.1 j.property.2 ⁻¹' Metric.ball 0
      ‖v‖
  have hV : V ∈ 𝓝 (0 : CkHolderSpaceLoc k α Ω F) :=
    (restrictL j.val j.property.1 j.property.2).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Metric.ball_mem_nhds 0 (norm_pos_iff.2 hv))
  obtain ⟨R, hR, hRs⟩ := (hs hV).exists_pos
  have hfV : f ∈ V := (smul_mem_smul_set_iff₀ hR.ne' V f).1
    (hRs R (by rw [Real.norm_eq_abs, abs_of_pos hR]) (hmem R))
  have hle := CkHolderSpaceOn.norm_apply_le (restrictL j.val j.property.1 j.property.2 f) ⟨x, hj⟩
  rw [restrictL_apply, hfx] at hle
  have hlt := mem_ball_zero_iff.1 hfV
  linarith

end CkHolderSpaceLoc

namespace CkHolderSpaceOn

variable {k α Ω F}

/-- An element of `C^{k,α}(Ω)` has the defining property of `C^{k,α}_loc(Ω)`, with `U = Ω` for
every compact set. -/
private theorem isLoc (f : CkHolderSpaceOn k α Ω F) :
    CkHolderSpaceLoc.IsLoc k α (⇑f) :=
  fun _ hKΩ _ ↦ ⟨Ω, hKΩ, le_rfl, f, fun _ ↦ rfl⟩

/-- Restricting the element of `C^{k,α}_loc(Ω)` defined by `f ∈ C^{k,α}(Ω)` to `U` is restricting
`f` to `U`. -/
private theorem restrictL_mk {U : Opens E} (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceOn k α Ω F) :
    CkHolderSpaceLoc.restrictL U hU hUΩ (CkHolderSpaceLoc.mk f f.isLoc) =
      restrictL (fun _ hx ↦ hUΩ (subset_closure hx)) f := by
  ext
  simp

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)`, as a continuous linear map. -/
def toLocL : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceLoc k α Ω F where
  toFun f := CkHolderSpaceLoc.mk f f.isLoc
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp
  cont := (CkHolderSpaceLoc.continuous_iff _).2 fun U hU hUΩ ↦
    (restrictL fun _ hx ↦ hUΩ (subset_closure hx)).continuous.congr fun f ↦
      (restrictL_mk hU hUΩ f).symm

/-- Restricting the inclusion of `f ∈ C^{k,α}(Ω)` to `U` is restricting `f` to `U`. -/
@[simp]
theorem restrictL_toLocL {U : Opens E} (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceOn k α Ω F) :
    CkHolderSpaceLoc.restrictL U hU hUΩ (toLocL f) =
      restrictL (fun _ hx ↦ hUΩ (subset_closure hx)) f :=
  restrictL_mk hU hUΩ f

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` does not change the underlying function. -/
@[simp]
theorem toLocL_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) : toLocL f x = f x :=
  CkHolderSpaceLoc.mk_apply _ f.isLoc x

end CkHolderSpaceOn

end TauCeti
