/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Topology.Metrizable.ContinuousMap
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Reparametrization
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Unparametrized maps of the projective line

Let `𝕜` be a proper nontrivially normed field, such as `ℂ`, and `X` a metrizable space. The group
`PSL(2, 𝕜)` of Möbius transformations acts on the continuous maps `u : OnePoint 𝕜 → X` by
reparametrization. This file builds the spaces of unparametrized maps, with and without a marked
point, and shows that they are Hausdorff. For `𝕜 = ℂ` these are the spaces of unparametrized and
one-marked continuous spheres in `X`; the moduli spaces of unparametrized pseudoholomorphic spheres
are subsets of them.

The reparametrization action is restricted to the **nonconstant** maps
(`OnePoint.NonconstantMap 𝕜 X`), with the compact-open topology; a constant map is fixed by every
Möbius transformation, so no action containing it can be proper. It is the left action
`g • u = u ∘ (g⁻¹ • ·)` (`OnePoint.NonconstantMap.smul_apply`); its orbits are those of the right
action `u ↦ u ∘ (g • ·)` by precomposition.

* The action is continuous (`OnePoint.NonconstantMap.instContinuousSMul`), since composition is
  continuous for the compact-open topology on maps out of the locally compact space `OnePoint 𝕜`.
* The action is **proper** (`OnePoint.NonconstantMap.instProperSMul`). For compact sets `U` and `V`
  of maps, the Möbius transformations `g` with `g • U ∩ V` nonempty form a compact set. This rests
  on the sequential properness of the reparametrization action
  (`OnePoint.NonconstantMap.exists_tendsto_of_smul_eq`, from
  `OnePoint.exists_tendsto_psl_of_tendsto`): a sequence `g n` with `g n • u n = v n`, `u n → u₀`
  and `v n → v₀` cannot escape to infinity, since otherwise `v₀` would be constant, so a
  subsequence converges. The space of maps is metrizable, so sequences suffice to detect compact
  sets in it, and `PSL(2, 𝕜)` is second countable, so sequential compactness implies compactness
  there.

The **unparametrized maps** `OnePoint.UnparametrizedMap 𝕜 X` form the orbit space of this action
and the **one-marked unparametrized maps** `OnePoint.MarkedUnparametrizedMap 𝕜 X` the orbit space of
the diagonal action `g • (u, z) = (g • u, g • z)` on pairs of a map and a point of the projective
line. Both actions are proper, the second because a proper action times a continuous one is proper
(`TauCeti.properSMul_prod`), so both orbit spaces are Hausdorff
(`t2Space_quotient_mulAction_of_properSMul`). The evaluation `(u, z) ↦ u z` is invariant, since
`(g • u) (g • z) = u z`, so it descends to a continuous **evaluation map**
`OnePoint.MarkedUnparametrizedMap.eval` on one-marked unparametrized maps. Forgetting the marked
point gives a continuous surjection `OnePoint.MarkedUnparametrizedMap.forget` onto unparametrized
maps.

Freeness of the action on maps with an injective point is
`Matrix.ProjectiveSpecialLinearGroup.eq_of_forall_apply_smul_eq_apply_smul`. The properness proved
here passes to every invariant subspace with the subspace topology
(`Topology.IsEmbedding.properSMul`). The sequential statement
`OnePoint.NonconstantMap.exists_tendsto_of_smul_eq` also applies to sequences converging in any
finer topology, such as a `C^∞` topology on pseudoholomorphic spheres.

## Main definitions

* `OnePoint.NonconstantMap 𝕜 X`: the nonconstant continuous maps `OnePoint 𝕜 → X`, with the
  reparametrization action of `PSL(2, 𝕜)`.
* `OnePoint.UnparametrizedMap 𝕜 X`: its orbit space.
* `OnePoint.MarkedUnparametrizedMap 𝕜 X`: the orbit space of pairs of a nonconstant map and a point.
* `OnePoint.MarkedUnparametrizedMap.eval`: the evaluation `[u, z] ↦ u z`.
* `OnePoint.MarkedUnparametrizedMap.forget`: the map `[u, z] ↦ [u]`.

## Main results

* `OnePoint.NonconstantMap.instContinuousSMul`: the reparametrization action is continuous.
* `OnePoint.NonconstantMap.exists_tendsto_of_smul_eq`: its sequential properness.
* `OnePoint.NonconstantMap.instProperSMul`: the reparametrization action on nonconstant maps into
  a metrizable space is proper, so `OnePoint.UnparametrizedMap 𝕜 X` and
  `OnePoint.MarkedUnparametrizedMap 𝕜 X` are Hausdorff.
* `OnePoint.MarkedUnparametrizedMap.continuous_eval`: the evaluation map is continuous.
* `OnePoint.MarkedUnparametrizedMap.continuous_forget`,
  `OnePoint.MarkedUnparametrizedMap.surjective_forget`: forgetting the marked point is a continuous
  surjection.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012 (the moduli spaces of unparametrized and
  marked spheres and their evaluation maps).
-/

public section

open Filter Function Topology TopologicalSpace
open scoped MatrixGroups Pointwise

namespace OnePoint

variable (𝕜 X : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace X]

/-- The nonconstant continuous maps `OnePoint 𝕜 → X` from the projective line, with the
compact-open topology. For `𝕜 = ℂ` these are the nonconstant parametrized spheres in `X`. -/
structure NonconstantMap where
  /-- The underlying continuous map of a nonconstant map. -/
  toContinuousMap : C(OnePoint 𝕜, X)
  /-- A nonconstant map takes two different values. -/
  exists_apply_ne' : ∃ z w, toContinuousMap z ≠ toContinuousMap w

namespace NonconstantMap

variable {𝕜 X}

instance : FunLike (NonconstantMap 𝕜 X) (OnePoint 𝕜) X where
  coe u := u.toContinuousMap
  coe_injective := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    congr
    exact DFunLike.coe_injective h

instance : ContinuousMapClass (NonconstantMap 𝕜 X) (OnePoint 𝕜) X where
  map_continuous u := u.toContinuousMap.continuous

@[simp]
theorem coe_toContinuousMap (u : NonconstantMap 𝕜 X) : ⇑u.toContinuousMap = u :=
  (rfl)

@[simp]
theorem mk_apply (u : C(OnePoint 𝕜, X)) (hu : ∃ z w, u z ≠ u w) (z : OnePoint 𝕜) :
    mk u hu z = u z :=
  (rfl)

theorem toContinuousMap_injective :
    Injective (toContinuousMap : NonconstantMap 𝕜 X → C(OnePoint 𝕜, X)) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩ rfl
  rfl

@[ext]
theorem ext {u v : NonconstantMap 𝕜 X} (h : ∀ z, u z = v z) : u = v :=
  DFunLike.ext _ _ h

/-- A nonconstant map takes two different values. -/
theorem exists_apply_ne (u : NonconstantMap 𝕜 X) : ∃ z w, u z ≠ u w :=
  u.exists_apply_ne'

/-- The compact-open topology on nonconstant maps, induced from all continuous maps. -/
instance : TopologicalSpace (NonconstantMap 𝕜 X) :=
  .induced toContinuousMap inferInstance

/-- The topology of the nonconstant maps is induced by the compact-open topology. -/
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : NonconstantMap 𝕜 X → C(OnePoint 𝕜, X)) :=
  ⟨⟨rfl⟩, toContinuousMap_injective⟩

@[fun_prop]
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : NonconstantMap 𝕜 X → C(OnePoint 𝕜, X)) :=
  isEmbedding_toContinuousMap.continuous

instance [T2Space X] : T2Space (NonconstantMap 𝕜 X) :=
  isEmbedding_toContinuousMap.t2Space

instance [MetrizableSpace X] : MetrizableSpace (NonconstantMap 𝕜 X) :=
  isEmbedding_toContinuousMap.metrizableSpace

variable [ProperSpace 𝕜]

/-- The evaluation `(u, z) ↦ u z` is jointly continuous. -/
instance : ContinuousEval (NonconstantMap 𝕜 X) (OnePoint 𝕜) X where
  continuous_eval :=
    (ContinuousEval.continuous_eval (F := C(OnePoint 𝕜, X))).comp
      (continuous_toContinuousMap.prodMap continuous_id)

variable [DecidableEq 𝕜]

/-- The **reparametrization action** of `PSL(2, 𝕜)` on nonconstant maps, `g • u = u ∘ (g⁻¹ • ·)`.
Its orbits are those of the right action `u ↦ u ∘ (g • ·)` by precomposition. -/
noncomputable instance : SMul PSL(2, 𝕜) (NonconstantMap 𝕜 X) where
  smul g u := ⟨u.toContinuousMap.comp ⟨(g⁻¹ • ·), continuous_const_smul _⟩, by
    obtain ⟨z, w, h⟩ := u.exists_apply_ne
    exact ⟨g • z, g • w, by simpa using h⟩⟩

@[simp]
theorem smul_apply (g : PSL(2, 𝕜)) (u : NonconstantMap 𝕜 X) (z : OnePoint 𝕜) :
    (g • u) z = u (g⁻¹ • z) :=
  (rfl)

noncomputable instance : MulAction PSL(2, 𝕜) (NonconstantMap 𝕜 X) where
  one_smul u := ext fun z ↦ by simp
  mul_smul g h u := ext fun z ↦ by simp [mul_smul]

theorem smul_apply_smul (g : PSL(2, 𝕜)) (u : NonconstantMap 𝕜 X) (z : OnePoint 𝕜) :
    (g • u) (g • z) = u z := by
  simp

/-- The Möbius transformation `z ↦ g • z` depends continuously on `g`, as a continuous map of the
projective line. -/
private theorem continuous_mobius : Continuous fun g : PSL(2, 𝕜) ↦
    (⟨(g • ·), continuous_const_smul g⟩ : C(OnePoint 𝕜, OnePoint 𝕜)) :=
  (ContinuousMap.curry ⟨fun p : PSL(2, 𝕜) × OnePoint 𝕜 ↦ p.1 • p.2, continuous_smul⟩).continuous

/-- The reparametrization action is continuous: composition of maps out of the compact space
`OnePoint 𝕜` is continuous for the compact-open topology. -/
instance instContinuousSMul : ContinuousSMul PSL(2, 𝕜) (NonconstantMap 𝕜 X) where
  continuous_smul := by
    refine isEmbedding_toContinuousMap.continuous_iff.2 ?_
    exact ContinuousMap.continuous_comp'.comp
      ((continuous_mobius.comp continuous_inv.fst').prodMk continuous_toContinuousMap.snd')

/-- **Sequential properness of the reparametrization action.** If `g n • u n = v n` with `u n → u₀`
and `v n → v₀`, then a subsequence of `g n` converges, to some `g₀` with `g₀ • u₀ = v₀`. -/
theorem exists_tendsto_of_smul_eq [T2Space X] {u v : ℕ → NonconstantMap 𝕜 X}
    {u₀ v₀ : NonconstantMap 𝕜 X} {g : ℕ → PSL(2, 𝕜)} (hu : Tendsto u atTop (𝓝 u₀))
    (hv : Tendsto v atTop (𝓝 v₀)) (huv : ∀ n, g n • u n = v n) :
    ∃ (φ : ℕ → ℕ) (g₀ : PSL(2, 𝕜)), StrictMono φ ∧ Tendsto (g ∘ φ) atTop (𝓝 g₀) ∧
      g₀ • u₀ = v₀ := by
  -- Apply the properness theorem for maps to the inverses `(g n)⁻¹`, along which `u n`
  -- reparametrizes to `v n`.
  obtain ⟨φ, h₀, hφ, hconv, hh₀⟩ := exists_tendsto_psl_of_tendsto (g := fun n ↦ (g n)⁻¹)
    (u := fun n ↦ u n) (u₀ := u₀) (v₀ := v₀)
    (fun y ↦ (ContinuousEval.continuous_eval.tendsto (u₀, y)).comp
      ((hu.comp tendsto_fst).prodMk_nhds tendsto_snd))
    (fun z ↦ by
      simpa [comp_def, ← huv] using
        (ContinuousEval.continuous_eval.tendsto (v₀, z)).comp (hv.prodMk_nhds tendsto_const_nhds))
    (map_continuous v₀) v₀.exists_apply_ne
  refine ⟨φ, h₀⁻¹, hφ, by simpa [comp_def] using hconv.inv, ext fun z ↦ ?_⟩
  simp [hh₀]

/-- **The reparametrization action on nonconstant maps into a metrizable space is proper.** For
compact sets `U` and `V` of maps, the Möbius transformations `g` with `g • U ∩ V` nonempty form a
sequentially compact, hence compact, subset of the second countable group `PSL(2, 𝕜)`. -/
instance instProperSMul [MetrizableSpace X] : ProperSMul PSL(2, 𝕜) (NonconstantMap 𝕜 X) := by
  refine MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty.2 fun {U V} hU hV ↦ ?_
  refine IsCountablyCompact.isCompact (IsSeqCompact.isCountablyCompact fun g hg ↦ ?_)
  -- Pick `u n ∈ U` with `g n • u n ∈ V`, then pass to a subsequence along which both converge.
  choose u hu hgu using fun n ↦ (hg n : ((g n • U) ∩ V).Nonempty)
  choose u' hu' hu'u using hu
  obtain ⟨u₀, hu₀, φ₁, hφ₁, hconv₁⟩ := hU.tendsto_subseq hu'
  obtain ⟨v₀, hv₀, φ₂, hφ₂, hconv₂⟩ := hV.tendsto_subseq fun n ↦ hgu (φ₁ n)
  obtain ⟨φ₃, g₀, hφ₃, hconv₃, hg₀⟩ := exists_tendsto_of_smul_eq
    (g := g ∘ φ₁ ∘ φ₂) (u := u' ∘ φ₁ ∘ φ₂) (hconv₁.comp hφ₂.tendsto_atTop) hconv₂
    fun n ↦ hu'u (φ₁ (φ₂ n))
  exact ⟨g₀, ⟨v₀, ⟨u₀, hu₀, hg₀⟩, hv₀⟩, φ₁ ∘ φ₂ ∘ φ₃, hφ₁.comp (hφ₂.comp hφ₃), hconv₃⟩

end NonconstantMap

variable [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- The **unparametrized maps** `OnePoint 𝕜 → X`: the orbit space of the nonconstant maps under
reparametrization by Möbius transformations. It is Hausdorff when `X` is metrizable, since the
action is proper (`OnePoint.NonconstantMap.instProperSMul`). -/
abbrev UnparametrizedMap : Type _ :=
  MulAction.orbitRel.Quotient PSL(2, 𝕜) (NonconstantMap 𝕜 X)

/-- The **one-marked unparametrized maps** `OnePoint 𝕜 → X`: the orbit space of pairs `(u, z)` of
a nonconstant map and a point under `g • (u, z) = (g • u, g • z)`, which identifies `(u ∘ g, z)`
with `(u, g • z)`. It is Hausdorff when `X` is metrizable, since the action is proper
(`TauCeti.properSMul_prod`). -/
abbrev MarkedUnparametrizedMap : Type _ :=
  MulAction.orbitRel.Quotient PSL(2, 𝕜) (NonconstantMap 𝕜 X × OnePoint 𝕜)

namespace MarkedUnparametrizedMap

variable {𝕜 X}

/-- The **evaluation map** `[u, z] ↦ u z` on one-marked unparametrized maps. -/
noncomputable def eval : MarkedUnparametrizedMap 𝕜 X → X :=
  Quotient.lift (fun p ↦ p.1 p.2) <| by
    rintro _ ⟨u, z⟩ ⟨g, rfl⟩
    exact NonconstantMap.smul_apply_smul g u z

@[simp]
theorem eval_mk (u : NonconstantMap 𝕜 X) (z : OnePoint 𝕜) :
    eval (Quotient.mk _ (u, z) : MarkedUnparametrizedMap 𝕜 X) = u z :=
  (rfl)

/-- The evaluation map is continuous. -/
@[fun_prop]
theorem continuous_eval : Continuous (eval : MarkedUnparametrizedMap 𝕜 X → X) :=
  isQuotientMap_quotient_mk'.continuous_iff.2 <|
    ContinuousEval.continuous_eval.congr fun p : NonconstantMap 𝕜 X × OnePoint 𝕜 ↦
      (eval_mk p.1 p.2).symm

/-- Forgetting the marked point, `[u, z] ↦ [u]`. -/
noncomputable def forget : MarkedUnparametrizedMap 𝕜 X → UnparametrizedMap 𝕜 X :=
  Quotient.map' Prod.fst <| by
    rintro _ ⟨u, z⟩ ⟨g, rfl⟩
    exact ⟨g, rfl⟩

@[simp]
theorem forget_mk (u : NonconstantMap 𝕜 X) (z : OnePoint 𝕜) :
    forget (Quotient.mk _ (u, z) : MarkedUnparametrizedMap 𝕜 X) = Quotient.mk _ u :=
  (rfl)

@[fun_prop]
theorem continuous_forget : Continuous (forget : MarkedUnparametrizedMap 𝕜 X → _) :=
  isQuotientMap_quotient_mk'.continuous_iff.2 <|
    (continuous_quotient_mk'.comp continuous_fst).congr fun p : NonconstantMap 𝕜 X × OnePoint 𝕜 ↦
      (forget_mk p.1 p.2).symm

theorem surjective_forget : Surjective (forget : MarkedUnparametrizedMap 𝕜 X → _) := by
  rintro ⟨u⟩
  exact ⟨Quotient.mk _ (u, ∞), rfl⟩

end MarkedUnparametrizedMap

end OnePoint
