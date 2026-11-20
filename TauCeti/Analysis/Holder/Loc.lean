/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import Mathlib.Algebra.Module.FunLike
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Normed.Module.Exhaustion

/-!
# The local Hölder spaces `C^{k,α}_loc(Ω)`

For an open set `Ω` of a real normed space `E`, this file constructs the space
`C^{k,α}_loc(Ω, F)` of functions on `Ω` whose restriction to every open set `U ⋐ Ω` (an open set
whose closure is compact and contained in `Ω`) lies in the Banach space `C^{k,α}(U, F)` of
`TauCeti.CkHolderSpaceOn`. Its topology is the compact-exhaustion topology: the coarsest one
making every restriction map `C^{k,α}_loc(Ω) → C^{k,α}(U)` continuous, given by the seminorms
`f ↦ ‖f|_U‖_{C^{k,α}(U)}`. It is a complete locally convex space, and when `E` is proper (for
instance `ℝⁿ`) countably many of these seminorms, along any compact exhaustion of `Ω`, already
define the topology, so for complete `F` the space is a Fréchet space.

`C^{k,α}_loc(Ω)` is not the Banach space `C^{k,α}(Ω)` of `TauCeti.CkHolderSpaceOn`, which it
contains through the continuous linear map `TauCeti.CkHolderSpaceOn.toCkHolderSpaceLocCLM`. Its
elements need not be bounded (`1/x` on `(0, 1)`), and its Hölder condition is local: on
`Ω = (-1, 0) ∪ (0, 1)` the sign function is in `C^{k,α}_loc(Ω)` for every `k` but has unbounded
Hölder quotients across the gap. No single seminorm controls the others, and the space is not
normable in general.

Membership has an intrinsic description
(`TauCeti.CkHolderSpaceLoc.exists_forall_eq_iff_contDiffOn`): when `E` is locally compact, a
function `g` on `E` restricts to an element of `C^{k,α}_loc(Ω)` exactly when it is `C^k` on `Ω`
and its `k`-th iterated derivative is `α`-Hölder on each compact subset of `Ω`.

## Main declarations

* `TauCeti.CkHolderSpaceLoc k α Ω F`: the space `C^{k,α}_loc(Ω, F)` for `Ω : Opens E`.
* `TauCeti.CkHolderSpaceLoc.restrictL`: restriction to an open `U ⋐ Ω`, a continuous linear map
  to `C^{k,α}(U, F)`.
* `TauCeti.CkHolderSpaceLoc.seminorm`: the seminorm `f ↦ ‖f|_U‖_{C^{k,α}(U)}`;
  `TauCeti.CkHolderSpaceLoc.withSeminorms` says that these seminorms define the topology, and
  `TauCeti.CkHolderSpaceLoc.withSeminorms_of_forall_isCompact` that the seminorms along any
  family of open sets `U ⋐ Ω` absorbing every compact subset of `Ω` already do.
* `TauCeti.CkHolderSpaceLoc.tendsto_nhds_iff` and `TauCeti.CkHolderSpaceLoc.continuous_iff`:
  convergence and continuity are tested on the restrictions.
* `TauCeti.CkHolderSpaceLoc.ofContDiffOn`, `TauCeti.CkHolderSpaceLoc.contDiffOn` and
  `TauCeti.CkHolderSpaceLoc.exists_holderOnWith_iteratedFDeriv`: introduction and elimination
  through `C^k` regularity on `Ω` and Hölder bounds on compact subsets.
* `TauCeti.CkHolderSpaceLoc.instCompleteSpace`: completeness, for locally compact `E` and complete
  `F`; `TauCeti.CkHolderSpaceLoc.instFirstCountableTopology` and
  `TauCeti.CkHolderSpaceLoc.instMetrizableSpace`: first countability and metrizability for proper
  `E`.
* `TauCeti.CkHolderSpaceOn.toCkHolderSpaceLocCLM`: the continuous inclusion
  `C^{k,α}(Ω) → C^{k,α}_loc(Ω)`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set TopologicalSpace
open scoped NNReal Topology Uniformity

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The local Hölder space `C^{k,α}_loc(Ω, F)`: functions on the open set `Ω` whose restriction
to every open set `U` with compact closure contained in `Ω` lies in `C^{k,α}(U, F)`, that is, is
`C^k` on `U` with derivatives through order `k` bounded on `U` and `k`-th derivative `α`-Hölder
on `U`. -/
structure CkHolderSpaceLoc where
  /-- The underlying function on `Ω`. Use the coercion instead. -/
  protected toFun : Ω → F
  /-- On every open `U ⋐ Ω` the function agrees with an element of `C^{k,α}(U)`. -/
  protected exists_eq' : ∀ (U : Opens E), IsCompact (closure (U : Set E)) →
    ∀ hUΩ : closure (U : Set E) ⊆ Ω, ∃ g : CkHolderSpaceOn k α U F,
      ∀ x : U, g x = toFun ⟨x, hUΩ (subset_closure x.2)⟩

namespace CkHolderSpaceLoc

variable {k α Ω F}

/-- An element of `C^{k,α}_loc(Ω, F)` is coerced to its underlying function on `Ω`. -/
instance instFunLike : FunLike (CkHolderSpaceLoc k α Ω F) Ω F where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- `CkHolderSpaceLoc.toFun f` is the coercion `⇑f`. -/
@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceLoc k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}_loc(Ω)` are equal when their underlying functions agree on `Ω`. -/
@[ext]
theorem ext {f g : CkHolderSpaceLoc k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The coercion of the element `⟨f, hf⟩` of `C^{k,α}_loc(Ω)` is `f`. -/
@[simp]
theorem coe_mk (f : Ω → F) (hf) : ⇑(⟨f, hf⟩ : CkHolderSpaceLoc k α Ω F) = f :=
  (rfl)

/-- On every open `U ⋐ Ω`, an element of `C^{k,α}_loc(Ω)` agrees with an element of
`C^{k,α}(U)`. -/
theorem exists_eq (f : CkHolderSpaceLoc k α Ω F) (U : Opens E)
    (hU : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω) :
    ∃ g : CkHolderSpaceOn k α U F, ∀ x : U, g x = f ⟨x, hUΩ (subset_closure x.2)⟩ :=
  f.exists_eq' U hU hUΩ

section Algebra

instance instZero : Zero (CkHolderSpaceLoc k α Ω F) where
  zero := ⟨0, fun _ _ _ ↦ ⟨0, fun x ↦ by simp⟩⟩

instance : IsZeroApply (CkHolderSpaceLoc k α Ω F) where

instance instAdd : Add (CkHolderSpaceLoc k α Ω F) where
  add f g := ⟨f + g, fun U hU hUΩ ↦ by
    obtain ⟨f', hf'⟩ := f.exists_eq U hU hUΩ
    obtain ⟨g', hg'⟩ := g.exists_eq U hU hUΩ
    exact ⟨f' + g', fun x ↦ by simp [hf', hg']⟩⟩

instance : IsAddApply (CkHolderSpaceLoc k α Ω F) where

/-- Scalar multiplication by any scalars acting on `F` through `ℝ`; this gives the `ℝ`-module
structure together with the `ℕ`- and `ℤ`-actions of the additive group. -/
instance instSMul {R : Type*} [SMul R ℝ] [SMul R F] [IsScalarTower R ℝ F] :
    SMul R (CkHolderSpaceLoc k α Ω F) where
  smul c f := ⟨c • ⇑f, fun U hU hUΩ ↦ by
    obtain ⟨f', hf'⟩ := f.exists_eq U hU hUΩ
    exact ⟨(c • (1 : ℝ)) • f', fun x ↦ by simp [hf']⟩⟩

instance {R : Type*} [SMul R ℝ] [SMul R F] [IsScalarTower R ℝ F] :
    IsSMulApply R (CkHolderSpaceLoc k α Ω F) where

instance instNeg : Neg (CkHolderSpaceLoc k α Ω F) where
  neg f := ⟨-⇑f, fun U hU hUΩ ↦ by
    obtain ⟨f', hf'⟩ := f.exists_eq U hU hUΩ
    exact ⟨(-1 : ℝ) • f', fun x ↦ by
      rw [CkHolderSpaceOn.coe_smul, Pi.smul_apply, hf', neg_one_smul, Pi.neg_apply]⟩⟩

instance : IsNegApply (CkHolderSpaceLoc k α Ω F) where

instance instSub : Sub (CkHolderSpaceLoc k α Ω F) where
  sub f g := ⟨f - g, fun U hU hUΩ ↦ by
    obtain ⟨f', hf'⟩ := f.exists_eq U hU hUΩ
    obtain ⟨g', hg'⟩ := g.exists_eq U hU hUΩ
    exact ⟨f' + (-1 : ℝ) • g', fun x ↦ by
      rw [CkHolderSpaceOn.coe_add, CkHolderSpaceOn.coe_smul, Pi.add_apply, Pi.smul_apply, hf', hg',
        neg_one_smul, Pi.sub_apply, sub_eq_add_neg]⟩⟩

instance : IsSubApply (CkHolderSpaceLoc k α Ω F) where

instance instAddCommGroup : AddCommGroup (CkHolderSpaceLoc k α Ω F) :=
  fast_instance% FunLike.addCommGroup

instance instModule : Module ℝ (CkHolderSpaceLoc k α Ω F) :=
  fast_instance% FunLike.module

end Algebra

section restrict

variable {U : Opens E} {hU : IsCompact (closure (U : Set E))} {hUΩ : closure (U : Set E) ⊆ Ω}

/-- Restriction to an open `U ⋐ Ω`, as a linear map; it is bundled with its continuity as
`CkHolderSpaceLoc.restrictL`, which should be used instead. -/
def restrictLM (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) :
    CkHolderSpaceLoc k α Ω F →ₗ[ℝ] CkHolderSpaceOn k α U F where
  toFun f := (f.exists_eq U hU hUΩ).choose
  map_add' f g := CkHolderSpaceOn.ext fun x ↦ by
    simp only [CkHolderSpaceOn.coe_add, Pi.add_apply, (f.exists_eq U hU hUΩ).choose_spec,
      (g.exists_eq U hU hUΩ).choose_spec, ((f + g).exists_eq U hU hUΩ).choose_spec,
      FunLike.coe_add]
  map_smul' c f := CkHolderSpaceOn.ext fun x ↦ by
    simp only [CkHolderSpaceOn.coe_smul, Pi.smul_apply, (f.exists_eq U hU hUΩ).choose_spec,
      ((c • f).exists_eq U hU hUΩ).choose_spec, FunLike.coe_smul, RingHom.id_apply]

/-- The linear restriction map does not change the values on `U`. -/
theorem restrictLM_apply (f : CkHolderSpaceLoc k α Ω F) (x : U) :
    restrictLM U hU hUΩ f x = f ⟨x, hUΩ (subset_closure x.2)⟩ :=
  (f.exists_eq U hU hUΩ).choose_spec x

/-- The compact-exhaustion topology of `C^{k,α}_loc(Ω)`: the coarsest topology making restriction
to every open `U ⋐ Ω` continuous into `C^{k,α}(U)`. -/
instance instTopologicalSpace : TopologicalSpace (CkHolderSpaceLoc k α Ω F) :=
  ⨅ U : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω},
    induced (restrictLM U.1 U.2.1 U.2.2) inferInstance

/-- The uniform structure of `C^{k,α}_loc(Ω)`: uniform convergence of every restriction to an
open `U ⋐ Ω` in `C^{k,α}(U)`. Its topology is `CkHolderSpaceLoc.instTopologicalSpace`. -/
instance instUniformSpace : UniformSpace (CkHolderSpaceLoc k α Ω F) := .replaceTopology
  (⨅ U : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω},
    UniformSpace.comap (restrictLM U.1 U.2.1 U.2.2) inferInstance)
  UniformSpace.toTopologicalSpace_iInf.symm

private theorem uniformSpace_eq_iInf :
    (instUniformSpace : UniformSpace (CkHolderSpaceLoc k α Ω F)) =
      ⨅ U : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω},
        UniformSpace.comap (restrictLM U.1 U.2.1 U.2.2) inferInstance :=
  UniformSpace.replaceTopology_eq _ UniformSpace.toTopologicalSpace_iInf.symm

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CkHolderSpaceLoc k α Ω F) :=
  isTopologicalAddGroup_iInf fun _ ↦ isTopologicalAddGroup_induced _

instance instIsUniformAddGroup : IsUniformAddGroup (CkHolderSpaceLoc k α Ω F) := by
  rw [uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _

instance instContinuousSMul : ContinuousSMul ℝ (CkHolderSpaceLoc k α Ω F) :=
  continuousSMul_iInf fun U ↦ continuousSMul_induced (restrictLM U.1 U.2.1 U.2.2)

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (CkHolderSpaceLoc k α Ω F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

variable (U hU hUΩ) in
/-- Restriction of an element of `C^{k,α}_loc(Ω)` to an open set `U` whose closure is compact and
contained in `Ω`, as a continuous linear map to `C^{k,α}(U)`. -/
def restrictL : CkHolderSpaceLoc k α Ω F →L[ℝ] CkHolderSpaceOn k α U F where
  toLinearMap := restrictLM U hU hUΩ
  cont := continuous_iInf_dom (i := ⟨U, hU, hUΩ⟩) continuous_induced_dom

/-- The restriction to `U ⋐ Ω` has the same values on `U`. -/
@[simp]
theorem restrictL_apply_apply (f : CkHolderSpaceLoc k α Ω F) (x : U) :
    restrictL U hU hUΩ f x = f ⟨x, hUΩ (subset_closure x.2)⟩ :=
  restrictLM_apply (hU := hU) f x

/-- The restriction to `U ⋐ Ω` is the unique element of `C^{k,α}(U)` with the right values. -/
theorem restrictL_apply_eq_iff {f : CkHolderSpaceLoc k α Ω F} {g : CkHolderSpaceOn k α U F} :
    restrictL U hU hUΩ f = g ↔ ∀ x : U, g x = f ⟨x, hUΩ (subset_closure x.2)⟩ := by
  refine ⟨fun h x ↦ by rw [← h, restrictL_apply_apply], fun h ↦ ?_⟩
  ext x
  rw [restrictL_apply_apply, h]

/-- Restricting from `U ⋐ Ω` to a smaller open `V ⋐ Ω` is restriction from `Ω` to `V`. -/
theorem restrictL_restrictL {V : Opens E} {hV : IsCompact (closure (V : Set E))}
    {hVΩ : closure (V : Set E) ⊆ Ω} (hVU : V ≤ U) (f : CkHolderSpaceLoc k α Ω F) :
    CkHolderSpaceOn.restrictL hVU (restrictL U hU hUΩ f) = restrictL V hV hVΩ f := by
  ext x
  simp

end restrict

section Topology

/-- A family converges in `C^{k,α}_loc(Ω)` exactly when its restrictions to every open `U ⋐ Ω`
converge in `C^{k,α}(U)`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {φ : ι → CkHolderSpaceLoc k α Ω F}
    {f : CkHolderSpaceLoc k α Ω F} :
    Tendsto φ l (𝓝 f) ↔ ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω),
        Tendsto (fun i ↦ restrictL U hU hUΩ (φ i)) l (𝓝 (restrictL U hU hUΩ f)) := by
  rw [nhds_iInf, tendsto_iInf]
  simp only [nhds_induced, tendsto_comap_iff]
  exact ⟨fun h U hU hUΩ ↦ h ⟨U, hU, hUΩ⟩, fun h U ↦ h U.1 U.2.1 U.2.2⟩

/-- A map into `C^{k,α}_loc(Ω)` is continuous exactly when its restrictions to every open
`U ⋐ Ω` are continuous into `C^{k,α}(U)`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → CkHolderSpaceLoc k α Ω F} :
    Continuous φ ↔ ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω), Continuous fun x ↦ restrictL U hU hUΩ (φ x) := by
  rw [continuous_iInf_rng]
  simp only [continuous_induced_rng]
  exact ⟨fun h U hU hUΩ ↦ h ⟨U, hU, hUΩ⟩, fun h U ↦ h U.1 U.2.1 U.2.2⟩

variable (U : Opens E) (hU : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)

/-- The seminorm `f ↦ ‖f|_U‖_{C^{k,α}(U)}` of `C^{k,α}_loc(Ω)` attached to an open `U ⋐ Ω`. -/
def seminorm : Seminorm ℝ (CkHolderSpaceLoc k α Ω F) :=
  (normSeminorm ℝ (CkHolderSpaceOn k α U F)).comp (restrictL U hU hUΩ).toLinearMap

/-- The seminorm attached to `U ⋐ Ω` is the `C^{k,α}(U)` norm of the restriction to `U`. -/
@[simp]
theorem seminorm_apply (f : CkHolderSpaceLoc k α Ω F) :
    seminorm U hU hUΩ f = ‖restrictL U hU hUΩ f‖ :=
  (rfl)

variable {U hU hUΩ} in
/-- The seminorms of `C^{k,α}_loc(Ω)` increase with the open set. -/
theorem seminorm_le_seminorm {V : Opens E} {hV : IsCompact (closure (V : Set E))}
    {hVΩ : closure (V : Set E) ⊆ Ω} (hVU : V ≤ U) (f : CkHolderSpaceLoc k α Ω F) :
    seminorm V hV hVΩ f ≤ seminorm U hU hUΩ f := by
  rw [seminorm_apply, seminorm_apply, ← restrictL_restrictL (hU := hU) (hUΩ := hUΩ) hVU]
  exact (CkHolderSpaceOn.restrictL hVU).le_of_opNorm_le
    (CkHolderSpaceOn.norm_restrictL_le_one hVU) _ |>.trans_eq (one_mul _)

/-- The seminorms `f ↦ ‖f|_U‖_{C^{k,α}(U)}`, over all open `U ⋐ Ω`, define the topology of
`C^{k,α}_loc(Ω)`. -/
theorem withSeminorms :
    WithSeminorms fun U : {U : Opens E // IsCompact (closure (U : Set E)) ∧
      closure (U : Set E) ⊆ Ω} ↦ seminorm (k := k) (α := α) (F := F) U.1 U.2.1 U.2.2 := by
  let p : SeminormFamily ℝ (CkHolderSpaceLoc k α Ω F)
      ((_ : {U : Opens E // IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω}) × Unit) :=
    SeminormFamily.sigma fun U _ ↦
      (normSeminorm ℝ (CkHolderSpaceOn k α U.1 F)).comp (restrictLM U.1 U.2.1 U.2.2)
  have : WithSeminorms p :=
    withSeminorms_iInf fun _ ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

/-- **Compact exhaustions.** If every compact subset of `Ω` lies in one of the open sets
`U i ⋐ Ω`, then the seminorms attached to the `U i` alone define the topology of
`C^{k,α}_loc(Ω)`. -/
theorem withSeminorms_of_forall_isCompact {ι : Type*} (U : ι → Opens E)
    (hU : ∀ i, IsCompact (closure (U i : Set E))) (hUΩ : ∀ i, closure (U i : Set E) ⊆ Ω)
    (hcover : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ i, K ⊆ U i) :
    WithSeminorms fun i ↦ seminorm (k := k) (α := α) (F := F) (U i) (hU i) (hUΩ i) := by
  refine withSeminorms.congr (fun i ↦ ⟨{⟨U i, hU i, hUΩ i⟩}, 1, ?_⟩) fun V ↦ ?_
  · intro f
    simp
  · obtain ⟨i, hi⟩ := hcover _ V.2.1 V.2.2
    refine ⟨{i}, 1, fun f ↦ ?_⟩
    simp only [Finset.sup_singleton, one_smul]
    exact seminorm_le_seminorm (hU := hU i) (hUΩ := hUΩ i) (fun x hx ↦ hi (subset_closure hx)) f

end Topology

section ofContDiffOn

/-- The element of `C^{k,α}_loc(Ω)` defined by a function on the whole space that is `C^k` on `Ω`
and whose `k`-th iterated derivative is `α`-Hölder on every compact subset of `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hH : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K) :
    CkHolderSpaceLoc k α Ω F where
  toFun x := g x
  exists_eq' U hU hUΩ := by
    have hgU : ContDiffOn ℝ k g U := hg.mono (subset_closure.trans hUΩ)
    refine ⟨CkHolderSpaceOn.ofContDiffOn g hgU (fun i hi ↦ ?_) ?_,
      fun x ↦ CkHolderSpaceOn.ofContDiffOn_apply _ _ _ _ x⟩
    · obtain ⟨C, hC⟩ := hU.exists_bound_of_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen (by exact_mod_cast hi)).mono hUΩ)
      exact ⟨C, fun x ↦ hC x (subset_closure x.2)⟩
    · obtain ⟨C, hC⟩ := hH _ hU hUΩ
      exact ⟨C, (hC.mono subset_closure).holderWith⟩

/-- The underlying function of `ofContDiffOn g` is the restriction of `g` to `Ω`. -/
@[simp]
theorem ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hH : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K)
    (x : Ω) : ofContDiffOn g hg hH x = g x :=
  (rfl)

variable [LocallyCompactSpace E]

omit [NormedSpace ℝ E] in
/-- In a locally compact space, a compact subset of the open set `Ω` lies in an open set whose
closure is compact and contained in `Ω`. -/
private theorem exists_opens_between {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ U ∧ IsCompact (closure (U : Set E)) ∧ closure (U : Set E) ⊆ Ω := by
  obtain ⟨V, hV, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨V, hV⟩, hKV, hVc, hVΩ⟩

/-- A function on the whole space that agrees with an element of `C^{k,α}_loc(Ω)` on `Ω` is `C^k`
on `Ω`. -/
theorem contDiffOn (f : CkHolderSpaceLoc k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g Ω := by
  refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
  obtain ⟨U, hxU, hU, hUΩ⟩ := exists_opens_between (isCompact_singleton (x := x))
    (singleton_subset_iff.2 hx)
  refine ⟨U, U.isOpen, hxU rfl, ((restrictL U hU hUΩ f).contDiffOn fun y ↦ ?_).mono
    inter_subset_right⟩
  rw [restrictL_apply_apply]
  exact hg ⟨y, hUΩ (subset_closure y.2)⟩

/-- The `k`-th iterated derivative of a function agreeing with an element of `C^{k,α}_loc(Ω)` on
`Ω` is `α`-Hölder on every compact subset of `Ω`. -/
theorem exists_holderOnWith_iteratedFDeriv (f : CkHolderSpaceLoc k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K := by
  obtain ⟨U, hKU, hU, hUΩ⟩ := exists_opens_between hK hKΩ
  exact ⟨_, ((restrictL U hU hUΩ f).holderOnWith_iteratedFDeriv fun y ↦ by
    rw [restrictL_apply_apply]
    exact hg ⟨y, hUΩ (subset_closure y.2)⟩).mono hKU⟩

/-- **Intrinsic description.** On a locally compact space, a function `g` agrees on `Ω` with an
element of `C^{k,α}_loc(Ω)` exactly when it is `C^k` on `Ω` and its `k`-th iterated derivative is
`α`-Hölder on every compact subset of `Ω`. -/
theorem exists_forall_eq_iff_contDiffOn {g : E → F} :
    (∃ f : CkHolderSpaceLoc k α Ω F, ∀ x : Ω, g x = f x) ↔ ContDiffOn ℝ k g Ω ∧
      ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K := by
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f.contDiffOn hf, fun _ hK hKΩ ↦
    f.exists_holderOnWith_iteratedFDeriv hf hK hKΩ⟩, fun ⟨hg, hH⟩ ↦
    ⟨ofContDiffOn g hg hH, fun _ ↦ rfl⟩⟩

end ofContDiffOn

section Complete

variable [LocallyCompactSpace E]

/-- Evaluation at a point of `Ω` is continuous on `C^{k,α}_loc(Ω)`. -/
instance instContinuousEvalConst : ContinuousEvalConst (CkHolderSpaceLoc k α Ω F) Ω F where
  continuous_eval_const x := by
    obtain ⟨U, hxU, hU, hUΩ⟩ := exists_opens_between (isCompact_singleton (x := (x : E)))
      (singleton_subset_iff.2 x.2)
    refine ((continuous_eval_const ⟨(x : E), hxU rfl⟩).comp
      (CkHolderSpaceOn.toBoundedContinuousFunctionCLM.continuous.comp
        (restrictL U hU hUΩ).continuous)).congr fun f ↦ ?_
    simp

instance instT2Space : T2Space (CkHolderSpaceLoc k α Ω F) :=
  .of_injective_continuous DFunLike.coe_injective (continuous_pi continuous_eval_const)

/-- An element of `C^{k,α}_loc(Ω)` glued from a compatible family of elements of `C^{k,α}(U)`,
one for each open `U ⋐ Ω`. -/
private theorem exists_restrictL_eq
    (g : ∀ (U : Opens E), IsCompact (closure (U : Set E)) → closure (U : Set E) ⊆ Ω →
      CkHolderSpaceOn k α U F)
    (hg : ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω) (V : Opens E) (hV : IsCompact (closure (V : Set E)))
      (hVΩ : closure (V : Set E) ⊆ Ω) (hVU : V ≤ U),
        CkHolderSpaceOn.restrictL hVU (g U hU hUΩ) = g V hV hVΩ) :
    ∃ f : CkHolderSpaceLoc k α Ω F, ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω), restrictL U hU hUΩ f = g U hU hUΩ := by
  choose W hxW hW hWΩ using fun x : Ω ↦
    exists_opens_between (isCompact_singleton (x := (x : E))) (singleton_subset_iff.2 x.2)
  -- On `U ⊓ W x`, both `g U` and `g (W x)` restrict to the element attached to the intersection.
  have hval : ∀ (U : Opens E) (hU : IsCompact (closure (U : Set E)))
      (hUΩ : closure (U : Set E) ⊆ Ω) (y : U),
        g U hU hUΩ y = g (W ⟨y, hUΩ (subset_closure y.2)⟩) (hW _) (hWΩ _) ⟨y, hxW _ rfl⟩ := by
    intro U hU hUΩ y
    set x : Ω := ⟨y, hUΩ (subset_closure y.2)⟩
    have hcl : closure ((U ⊓ W x : Opens E) : Set E) ⊆ closure (U : Set E) :=
      closure_mono inter_subset_left
    have hI := hg U hU hUΩ (U ⊓ W x) (hU.of_isClosed_subset isClosed_closure hcl)
      (hcl.trans hUΩ) inf_le_left
    have hI' := hg (W x) (hW x) (hWΩ x) (U ⊓ W x) (hU.of_isClosed_subset isClosed_closure hcl)
      (hcl.trans hUΩ) inf_le_right
    have h1 := DFunLike.congr_fun hI ⟨y, y.2, hxW x rfl⟩
    have h2 := DFunLike.congr_fun hI' ⟨y, y.2, hxW x rfl⟩
    rw [CkHolderSpaceOn.restrictL_apply] at h1 h2
    exact h1.trans h2.symm
  refine ⟨⟨fun x ↦ g (W x) (hW x) (hWΩ x) ⟨x, hxW x rfl⟩, fun U hU hUΩ ↦
    ⟨g U hU hUΩ, hval U hU hUΩ⟩⟩, fun U hU hUΩ ↦ ?_⟩
  rw [restrictL_apply_eq_iff]
  exact hval U hU hUΩ

/-- On a locally compact space, `C^{k,α}_loc(Ω)` with values in a Banach space is complete. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderSpaceLoc k α Ω F) := by
  refine ⟨fun {l} hl ↦ ?_⟩
  have hl' := hl.1
  choose g hg using fun (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) ↦
      CompleteSpace.complete (hl.map (restrictL U hU hUΩ).uniformContinuous)
  -- The limits on nested open sets are compatible, since restriction is continuous.
  obtain ⟨f, hf⟩ := exists_restrictL_eq g fun U hU hUΩ V hV hVΩ hVU ↦ by
    have h := ((CkHolderSpaceOn.restrictL hVU).continuous.tendsto _).comp (hg U hU hUΩ)
    rw [show (CkHolderSpaceOn.restrictL hVU ∘ restrictL U hU hUΩ) = restrictL V hV hVΩ from
      funext (restrictL_restrictL hVU)] at h
    exact tendsto_nhds_unique h (hg V hV hVΩ)
  refine ⟨f, tendsto_nhds_iff.2 fun U hU hUΩ ↦ ?_⟩
  rw [hf]
  exact hg U hU hUΩ

end Complete

section Metrizable

variable [ProperSpace E]

/-- In a proper space, the seminorms along the interiors of the filled exhaustion of `Ω` define the
topology of `C^{k,α}_loc(Ω)`: countably many seminorms suffice. -/
private theorem exists_withSeminorms_nat :
    ∃ (U : ℕ → Opens E) (hU : ∀ n, IsCompact (closure (U n : Set E)))
      (hUΩ : ∀ n, closure (U n : Set E) ⊆ Ω),
        WithSeminorms fun n ↦ seminorm (k := k) (α := α) (F := F) (U n) (hU n) (hUΩ n) := by
  have hcl : ∀ n, closure (interior (filledExhaustion (Ω : Set E) n)) ⊆
      filledExhaustion (Ω : Set E) n :=
    fun n ↦ closure_minimal interior_subset (isClosed_filledExhaustion _ n)
  exact ⟨fun n ↦ ⟨_, isOpen_interior⟩,
    fun n ↦ (isCompact_filledExhaustion _ n).of_isClosed_subset isClosed_closure (hcl n),
    fun n ↦ (hcl n).trans (filledExhaustion_subset _ n),
    withSeminorms_of_forall_isCompact _ _ _ fun _ hK hKΩ ↦
      Ω.isOpen.exists_subset_interior_filledExhaustion hK hKΩ⟩

instance instFirstCountableTopology : FirstCountableTopology (CkHolderSpaceLoc k α Ω F) := by
  obtain ⟨_, _, _, h⟩ := exists_withSeminorms_nat (k := k) (α := α) (Ω := Ω) (F := F)
  exact h.firstCountableTopology

instance instIsCountablyGeneratedUniformity :
    (𝓤 (CkHolderSpaceLoc k α Ω F)).IsCountablyGenerated :=
  IsUniformAddGroup.uniformity_countably_generated

/-- On a proper space, `C^{k,α}_loc(Ω)` is metrizable; with completeness it is a Fréchet space. -/
instance instMetrizableSpace : TopologicalSpace.MetrizableSpace (CkHolderSpaceLoc k α Ω F) :=
  UniformSpace.metrizableSpace

end Metrizable

end CkHolderSpaceLoc

namespace CkHolderSpaceOn

variable {k α Ω F}

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)`, as a continuous linear map. -/
def toCkHolderSpaceLocCLM : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceLoc k α Ω F where
  toFun f := ⟨f, fun U _ hUΩ ↦
    ⟨restrictL (fun _ hx ↦ hUΩ (subset_closure hx)) f, fun x ↦ by simp⟩⟩
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  cont := CkHolderSpaceLoc.continuous_iff.2 fun U hU hUΩ ↦
    (restrictL (fun _ hx ↦ hUΩ (subset_closure hx))).continuous.congr fun f ↦ by
      rw [eq_comm, CkHolderSpaceLoc.restrictL_apply_eq_iff]
      intro x
      simp

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` does not change the underlying function. -/
@[simp]
theorem coe_toCkHolderSpaceLocCLM (f : CkHolderSpaceOn k α Ω F) :
    ⇑(toCkHolderSpaceLocCLM f) = ⇑f :=
  (rfl)

/-- Restricting the inclusion of `f ∈ C^{k,α}(Ω)` to an open `U ⋐ Ω` is the restriction of `f`
in the Banach spaces `C^{k,α}`. -/
@[simp]
theorem restrictL_toCkHolderSpaceLocCLM (U : Opens E) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (f : CkHolderSpaceOn k α Ω F) :
    CkHolderSpaceLoc.restrictL U hU hUΩ (toCkHolderSpaceLocCLM f) =
      restrictL (fun _ hx ↦ hUΩ (subset_closure hx)) f := by
  rw [CkHolderSpaceLoc.restrictL_apply_eq_iff]
  simp

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` is injective. -/
theorem toCkHolderSpaceLocCLM_injective :
    Function.Injective (toCkHolderSpaceLocCLM (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun f g h ↦ DFunLike.coe_injective (by simpa using congrArg DFunLike.coe h)

end CkHolderSpaceOn

end TauCeti
