/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Sobolev.W1p.Convex
public import TauCeti.Analysis.Sobolev.Wkp.HolderRepresentative
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Lipschitz representatives of `W^{k,∞}` functions

Let `Ω` be a convex open subset of a finite-dimensional real inner product space. A function
`u ∈ W^{1,∞}(Ω)` has a representative that is Lipschitz on `Ω` with constant `‖∇u‖_∞`
(`TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_convex`). Being uniformly continuous, it
extends to `closure Ω`, with the same Lipschitz constant and the same supremum bound `‖u‖_∞`.
This defines a bounded linear map

`W^{1,∞}(Ω) → C^{0,1}(closure Ω)` (`TauCeti.W1p.lipschitzRepresentativeL`),

characterised by agreeing almost everywhere on `Ω` with `u`
(`TauCeti.W1p.lipschitzRepresentativeL_eq_iff`). Neither boundedness nor boundary regularity of
`Ω` is needed; convexity is what makes the local Lipschitz bound global.

Applying it to the derivatives of every order gives the endpoint `p = ∞` of the Sobolev
embedding into Hölder spaces, `W^{k,∞} ⊆ C^{k-1,1}` for `k ≥ 1`: every `u ∈ W^{j+1,∞}(Ω)` has a
representative that is `Cʲ` on `Ω` and whose derivatives of every order `i ≤ j` are bounded by
`K ‖u‖` and Lipschitz with constant `K ‖u‖` on `Ω`
(`TauCeti.Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex`). This is the
domain-independent induction
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL` at Hölder
exponent `1`. On the whole space the representative lies in the Banach space
`C_b^{j,1}(E)` of `TauCeti.CkHolderSpace`, and depends linearly and boundedly on `u`
(`TauCeti.Wkp.toCkHolderSpaceOne`).

Unlike the embeddings for `p < ∞`, there is no gain of a fractional exponent here: the exponent
`1` is that of the Lipschitz bound itself, and it is sharp, since `x ↦ |x|` lies in
`W^{1,∞}(-1, 1)` and is not `C¹`.

## Main declarations

* `TauCeti.W1p.lipschitzRepresentativeL`: the Lipschitz representative on `closure Ω` as a
  continuous linear map `W^{1,∞}(Ω) → C^{0,1}(closure Ω)`, with
  `TauCeti.W1p.lipschitzRepresentativeL_apply` (it is the precise representative on `Ω`),
  `TauCeti.W1p.ae_lipschitzRepresentativeL_eq`, `TauCeti.W1p.lipschitzRepresentativeL_eq_iff`,
  `TauCeti.W1p.lipschitzWith_lipschitzRepresentativeL` (the sharp constant `‖∇u‖_∞`) and
  `TauCeti.W1p.norm_lipschitzRepresentativeL_apply_le`.
* `TauCeti.Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex`:
  `W^{j+1,∞}(Ω) ⊆ C^{j,1}(Ω)` on convex `Ω`, with bounds linear in `‖u‖`.
* `TauCeti.Wkp.toCkHolderSpaceOne`: the embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)` as a continuous
  linear map, characterised by `TauCeti.Wkp.toCkHolderSpaceOne_eq_iff`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The Lipschitz representative of a `W^{1,∞}` function -/

section FirstOrder

variable {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The points of `Ω` are dense in `closure Ω`. -/
private theorem dense_setOf_mem_opens :
    Dense {x : closure (Ω : Set E) | (x : E) ∈ Ω} := by
  rw [Subtype.dense_iff]
  exact closure_mono fun x hx ↦ ⟨⟨x, subset_closure hx⟩, hx, rfl⟩

variable (hΩ : Convex ℝ (Ω : Set E))
include hΩ

/-- **The Lipschitz representative on the closure.** On a convex domain, the precise
representative of `u ∈ W^{1,∞}(Ω)` extends to a function on `closure Ω` bounded by `‖u‖_∞` and
Lipschitz with constant `‖∇u‖_∞`. -/
private theorem W1p.exists_lipschitzRepresentative (u : W1p μ Ω ∞) :
    ∃ G : HolderSpace 1 (closure (Ω : Set E)) ℝ,
      (∀ x (hx : x ∈ Ω), G ⟨x, subset_closure hx⟩ = preciseRepresentative μ (W1p.value u) x) ∧
        LipschitzWith ‖W1p.gradient u‖₊ G ∧ ∀ x, ‖G x‖ ≤ ‖W1p.value u‖ := by
  set f := preciseRepresentative μ (W1p.value u)
  set s : Set (closure (Ω : Set E)) := {x | (x : E) ∈ Ω}
  have hd : Dense s := dense_setOf_mem_opens
  -- On the points of `Ω`, the representative is Lipschitz with constant `‖∇u‖_∞`.
  have hL : HolderOnWith ‖W1p.gradient u‖₊ 1 (fun x : closure (Ω : Set E) ↦ f x) s := by
    rw [holderOnWith_one]
    have h := (W1p.lipschitzOnWith_preciseRepresentative_of_convex u hΩ subset_rfl).comp
      (LipschitzWith.subtype_val (closure (Ω : Set E))).lipschitzOnWith
      (fun _ hx ↦ hx : MapsTo Subtype.val s (Ω : Set E))
    rw [mul_one] at h
    exact h
  obtain ⟨g, hg, hgf⟩ := hL.extend_of_dense hd
  have hgc : Continuous g := (holderWith_one.1 hg).continuous
  -- The bound by `‖u‖_∞` holds on the dense set `s`, hence everywhere.
  have hbd : ∀ x, ‖g x‖ ≤ ‖W1p.value u‖ := by
    have hcl : IsClosed {x | ‖g x‖ ≤ ‖W1p.value u‖} := isClosed_le hgc.norm continuous_const
    have hsub : s ⊆ {x | ‖g x‖ ≤ ‖W1p.value u‖} := fun x (hx : (x : E) ∈ Ω) ↦ by
      simpa [← hgf hx] using W1p.norm_preciseRepresentative_le u hx
    intro x
    exact hcl.closure_subset_iff.2 hsub (hd.closure_eq ▸ mem_univ x)
  let G : HolderSpace 1 (closure (Ω : Set E)) ℝ :=
    HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup g hgc _ hbd) ⟨_, hg⟩
  have hG : ⇑G = g := funext fun x ↦ HolderSpace.ofBoundedContinuousFunction_apply _ _ x
  refine ⟨G, fun x hx ↦ ?_, hG ▸ holderWith_one.1 hg, hG ▸ hbd⟩
  rw [hG]
  exact (hgf (x := ⟨x, subset_closure hx⟩) hx).symm

/-- The Lipschitz representative of `u` on `closure Ω`, chosen by
`W1p.exists_lipschitzRepresentative`. -/
private def W1p.lipschitzRepresentative (u : W1p μ Ω ∞) : HolderSpace 1 (closure (Ω : Set E)) ℝ :=
  (W1p.exists_lipschitzRepresentative hΩ u).choose

private theorem W1p.lipschitzRepresentative_spec (u : W1p μ Ω ∞) :
    (∀ x (hx : x ∈ Ω), W1p.lipschitzRepresentative hΩ u ⟨x, subset_closure hx⟩ =
        preciseRepresentative μ (W1p.value u) x) ∧
      LipschitzWith ‖W1p.gradient u‖₊ (W1p.lipschitzRepresentative hΩ u) ∧
        ∀ x, ‖W1p.lipschitzRepresentative hΩ u x‖ ≤ ‖W1p.value u‖ :=
  (W1p.exists_lipschitzRepresentative hΩ u).choose_spec

/-- The Lipschitz representative agrees almost everywhere on `Ω` with `u`. -/
private theorem W1p.ae_lipschitzRepresentative_eq (u : W1p μ Ω ∞) :
    ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, W1p.lipschitzRepresentative hΩ u ⟨x, subset_closure hx⟩ =
      W1p.value u x := by
  have h := W1p.ae_eq_preciseRepresentative u
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet] at h
  filter_upwards [h] with x hx hxΩ
  rw [(W1p.lipschitzRepresentative_spec hΩ u).1 x hxΩ, hx hxΩ]

/-- **The Lipschitz representative** of `W^{1,∞}` functions on a convex domain `Ω`, as a bounded
linear map `W^{1,∞}(Ω) → C^{0,1}(closure Ω)`. On `Ω` it is the precise representative
(`TauCeti.W1p.lipschitzRepresentativeL_apply`); it is the only element of `C^{0,1}(closure Ω)`
agreeing almost everywhere on `Ω` with `u` (`TauCeti.W1p.lipschitzRepresentativeL_eq_iff`). -/
def W1p.lipschitzRepresentativeL : W1p μ Ω ∞ →L[ℝ] HolderSpace 1 (closure (Ω : Set E)) ℝ :=
  LinearMap.mkContinuous
    { toFun := W1p.lipschitzRepresentative hΩ
      map_add' u v := HolderSpace.ext <| congrFun <|
        Ω.isOpen.ext_closure_of_ae_eq (μ := μ) (HolderSpace.continuous _)
          (HolderSpace.continuous _) <| by
        filter_upwards [W1p.ae_lipschitzRepresentative_eq hΩ (u + v),
          W1p.ae_lipschitzRepresentative_eq hΩ u, W1p.ae_lipschitzRepresentative_eq hΩ v,
          (ae_restrict_iff' Ω.isOpen.measurableSet).1
            (W1p.value_add u v ▸ Lp.coeFn_add (W1p.value u) (W1p.value v))]
          with x h h₁ h₂ h₃ hx
        rw [HolderSpace.add_apply, h hx, h₁ hx, h₂ hx, h₃ hx, Pi.add_apply]
      map_smul' c u := HolderSpace.ext <| congrFun <|
        Ω.isOpen.ext_closure_of_ae_eq (μ := μ) (HolderSpace.continuous _)
          (HolderSpace.continuous _) <| by
        filter_upwards [W1p.ae_lipschitzRepresentative_eq hΩ (c • u),
          W1p.ae_lipschitzRepresentative_eq hΩ u,
          (ae_restrict_iff' Ω.isOpen.measurableSet).1
            (W1p.value_smul c u ▸ Lp.coeFn_smul c (W1p.value u))]
          with x h h₁ h₂ hx
        rw [RingHom.id_apply, HolderSpace.smul_apply, h hx, h₁ hx, h₂ hx, Pi.smul_apply] }
    2 fun u ↦ by
      obtain ⟨-, hL, hbd⟩ := W1p.lipschitzRepresentative_spec hΩ u
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg _) hbd
        (holderWith_one.2 hL)).trans ?_
      rw [coe_nnNorm, two_mul]
      exact add_le_add (W1p.norm_value_le u) (W1p.norm_gradient_le u)

/-- On `Ω`, the Lipschitz representative is the precise representative. -/
theorem W1p.lipschitzRepresentativeL_apply (u : W1p μ Ω ∞) {x : E} (hx : x ∈ Ω) :
    W1p.lipschitzRepresentativeL hΩ u ⟨x, subset_closure hx⟩ =
      preciseRepresentative μ (W1p.value u) x :=
  (W1p.lipschitzRepresentative_spec hΩ u).1 x hx

/-- The Lipschitz representative agrees almost everywhere on `Ω` with `u`. -/
theorem W1p.ae_lipschitzRepresentativeL_eq (u : W1p μ Ω ∞) :
    ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, W1p.lipschitzRepresentativeL hΩ u ⟨x, subset_closure hx⟩ =
      W1p.value u x :=
  W1p.ae_lipschitzRepresentative_eq hΩ u

/-- The Lipschitz representative is the only element of `C^{0,1}(closure Ω)` that agrees almost
everywhere on `Ω` with `u`. -/
theorem W1p.lipschitzRepresentativeL_eq_iff (u : W1p μ Ω ∞)
    {G : HolderSpace 1 (closure (Ω : Set E)) ℝ} :
    W1p.lipschitzRepresentativeL hΩ u = G ↔
      ∀ᵐ x ∂μ, ∀ hx : x ∈ Ω, G ⟨x, subset_closure hx⟩ = W1p.value u x := by
  refine ⟨fun h ↦ h ▸ W1p.ae_lipschitzRepresentativeL_eq hΩ u,
    fun h ↦ HolderSpace.ext <| congrFun <| Ω.isOpen.ext_closure_of_ae_eq (μ := μ)
      (HolderSpace.continuous _) (HolderSpace.continuous _) ?_⟩
  filter_upwards [W1p.ae_lipschitzRepresentativeL_eq hΩ u, h] with x h₁ h₂ hx
  rw [h₁ hx, h₂ hx]

/-- **The sharp Lipschitz constant.** The Lipschitz representative of `u` is Lipschitz on
`closure Ω` with constant the essential supremum `‖∇u‖_∞` of the weak gradient. -/
theorem W1p.lipschitzWith_lipschitzRepresentativeL (u : W1p μ Ω ∞) :
    LipschitzWith ‖W1p.gradient u‖₊ (W1p.lipschitzRepresentativeL hΩ u) :=
  (W1p.lipschitzRepresentative_spec hΩ u).2.1

/-- The Lipschitz representative of `u` is bounded by `‖u‖_∞`. -/
theorem W1p.norm_lipschitzRepresentativeL_apply_le (u : W1p μ Ω ∞)
    (x : closure (Ω : Set E)) : ‖W1p.lipschitzRepresentativeL hΩ u x‖ ≤ ‖W1p.value u‖ :=
  (W1p.lipschitzRepresentative_spec hΩ u).2.2 x

end FirstOrder

/-! ### Higher orders -/

namespace Wkp

/-- **The Sobolev embedding `W^{j+1,∞} ⊆ C^{j,1}` on convex domains.** Let `Ω` be a convex open
set. There is a constant `K` such that every `u ∈ W^{j+1,∞}(Ω)` agrees almost everywhere on `Ω`
with a function `g` that is `Cʲ` on `Ω`, whose derivatives of order `i ≤ j` are bounded by `K ‖u‖`
and Lipschitz with constant `K ‖u‖` on `Ω`. -/
theorem exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex {Ω : Opens E}
    (hΩ : Convex ℝ (Ω : Set E)) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : Wkp volume Ω ∞ (j + 1), ∃ g : E → ℝ, ContDiffOn ℝ j g Ω ∧
      (value (j + 1) u : E → ℝ) =ᵐ[volume.restrict Ω] g ∧ ∀ i ≤ j,
        (∀ x ∈ Ω, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
          LipschitzOnWith (K * ‖u‖₊) (iteratedFDeriv ℝ i g) Ω := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL
    one_pos (fun k ↦ ⟨(W1p.lipschitzRepresentativeL hΩ).comp (firstOrderL k), fun u ↦ by
      have h := W1p.ae_lipschitzRepresentativeL_eq (μ := volume) hΩ (firstOrder k u)
      rw [value_firstOrder] at h
      rwa [ContinuousLinearMap.comp_apply, firstOrderL_apply]⟩) j
  refine ⟨K, fun u ↦ ?_⟩
  obtain ⟨g, hg, hug, hbd⟩ := hK u
  exact ⟨g, hg, hug, fun i hi ↦ ⟨(hbd i hi).1, holderOnWith_one.1 (hbd i hi).2⟩⟩

/-- A choice of the representative of `exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex`
on the whole space, with the constant `K`. -/
private theorem exists_ckHolderSpaceOne (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : Wkp volume (⊤ : Opens E) ∞ (j + 1), ∃ f : CkHolderSpace j 1 E ℝ,
      (value (j + 1) u : E → ℝ) =ᵐ[volume] f ∧ ‖f‖ ≤ (j + 2) * K * ‖u‖ := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex
    (Ω := (⊤ : Opens E)) convex_univ j
  refine ⟨K, fun u ↦ ?_⟩
  obtain ⟨g, hg, hug, hbd⟩ := hK u
  simp only [Opens.coe_top, Measure.restrict_univ, contDiffOn_univ] at hg hug
  replace hbd : ∀ i ≤ j, (∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
      LipschitzWith (K * ‖u‖₊) (iteratedFDeriv ℝ i g) := fun i hi ↦
    ⟨fun x ↦ (hbd i hi).1 x (by simp), by simpa using (hbd i hi).2⟩
  let f : CkHolderSpace j 1 E ℝ := CkHolderSpace.ofContDiff g hg
    (fun i hi ↦ ⟨_, (hbd i hi).1⟩) ⟨_, holderWith_one.2 (hbd j le_rfl).2⟩
  have hf : ⇑f = g := CkHolderSpace.coe_ofContDiff g hg _ _
  refine ⟨f, hf ▸ hug, ?_⟩
  refine (CkHolderSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith (M := K * ‖u‖)
    (K := K * ‖u‖₊) (fun i hi x ↦ hf ▸ (hbd i hi).1 x)
    (hf ▸ holderWith_one.2 (hbd j le_rfl).2)).trans_eq ?_
  push_cast
  ring

/-- **The Sobolev embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)`.** On the whole space, every
`u ∈ W^{j+1,∞}(E)` has a representative that is `Cʲ` with bounded derivatives through order `j`
and a Lipschitz `j`-th derivative. It depends linearly and boundedly on `u`, and is the only
element of `C_b^{j,1}(E)` agreeing almost everywhere with `u`
(`TauCeti.Wkp.toCkHolderSpaceOne_eq_iff`). -/
def toCkHolderSpaceOne (j : ℕ) : Wkp volume (⊤ : Opens E) ∞ (j + 1) →L[ℝ] CkHolderSpace j 1 E ℝ :=
  LinearMap.mkContinuous
    { toFun u := ((exists_ckHolderSpaceOne j).choose_spec u).choose
      map_add' u v := by
        refine CkHolderSpace.ext <| congrFun <| (Continuous.ae_eq_iff_eq volume ?_ ?_).1 ?_
        · exact (CkHolderSpace.contDiff _).continuous
        · exact (CkHolderSpace.contDiff _).continuous
        filter_upwards [((exists_ckHolderSpaceOne j).choose_spec (u + v)).choose_spec.1,
          ((exists_ckHolderSpaceOne j).choose_spec u).choose_spec.1,
          ((exists_ckHolderSpaceOne j).choose_spec v).choose_spec.1,
          (ae_restrict_iff' MeasurableSet.univ).1 (value_add (j + 1) u v ▸
            Lp.coeFn_add (value (j + 1) u) (value (j + 1) v))] with x h h₁ h₂ h₃
        rw [← h, CkHolderSpace.coe_add, Pi.add_apply, ← h₁, ← h₂]
        simpa using h₃ (mem_univ x)
      map_smul' c u := by
        refine CkHolderSpace.ext <| congrFun <| (Continuous.ae_eq_iff_eq volume ?_ ?_).1 ?_
        · exact (CkHolderSpace.contDiff _).continuous
        · exact (CkHolderSpace.contDiff _).continuous
        filter_upwards [((exists_ckHolderSpaceOne j).choose_spec (c • u)).choose_spec.1,
          ((exists_ckHolderSpaceOne j).choose_spec u).choose_spec.1,
          (ae_restrict_iff' MeasurableSet.univ).1
            (value_smul (j + 1) c u ▸ Lp.coeFn_smul c (value (j + 1) u))]
          with x h h₁ h₂
        rw [← h, RingHom.id_apply, CkHolderSpace.coe_smul, Pi.smul_apply, ← h₁]
        simpa using h₂ (mem_univ x) }
    ((j + 2) * (exists_ckHolderSpaceOne (E := E) j).choose) fun u ↦
      ((exists_ckHolderSpaceOne j).choose_spec u).choose_spec.2

/-- The embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)` gives a representative of `u`. -/
theorem value_ae_eq_toCkHolderSpaceOne (j : ℕ) (u : Wkp volume (⊤ : Opens E) ∞ (j + 1)) :
    (value (j + 1) u : E → ℝ) =ᵐ[volume] toCkHolderSpaceOne j u :=
  ((exists_ckHolderSpaceOne j).choose_spec u).choose_spec.1

/-- `toCkHolderSpaceOne j u` is the only element of `C_b^{j,1}(E)` representing `u`. -/
theorem toCkHolderSpaceOne_eq_iff (j : ℕ) {u : Wkp volume (⊤ : Opens E) ∞ (j + 1)}
    {f : CkHolderSpace j 1 E ℝ} :
    toCkHolderSpaceOne j u = f ↔ (value (j + 1) u : E → ℝ) =ᵐ[volume] f := by
  refine ⟨fun h ↦ h ▸ value_ae_eq_toCkHolderSpaceOne j u, fun h ↦ CkHolderSpace.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq volume (CkHolderSpace.contDiff _).continuous
      (CkHolderSpace.contDiff _).continuous).1 ?_⟩
  exact (value_ae_eq_toCkHolderSpaceOne j u).symm.trans h

end Wkp

end TauCeti
