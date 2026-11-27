/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong

/-!
# The trivial bundle in local frames

A family of *local frames* of the trivial bundle `B × 𝕜ⁿ` assigns to each point `i` of `B` an open
neighbourhood `U i` and a continuous family of automorphisms `frame i x` of `𝕜ⁿ`, `x ∈ U i`
(`TauCeti.FiniteRankBundleCore.LocalFrames`). Reading the trivial bundle in these frames gives a
point-indexed core `LocalFrames.core`: its chart at `i` has domain `U i`, and a vector with
coordinates `v` in the chart at `i` over `x` is the vector `frame i x v` of `𝕜ⁿ`, so the transition
from the chart at `i` to the chart at `j` is `(frame j x)⁻¹ ∘ frame i x`. The core is isomorphic to
the trivial core by the frame at `x` on the fibre over `x` (`LocalFrames.isoTrivial`). The frames
are only given over their domains; `LocalFrames.frameAt` extends them by the identity.

The point of the construction is that the charts carry more structure than the trivial bundle. For
`𝕜 = ℂ` and a subset `A ⊆ B`, the core is real along `A` exactly when, at each point `a` of `A`,
the frames at `a` all span the same real subspace `frame i a (ℝⁿ)`
(`LocalFrames.isRealAlong_core_iff`). Then the pair `(core, F)` is the trivial bundle `ℂⁿ` with
the totally real subbundle `F_a = frame a a (ℝⁿ)` over `A`, and the isomorphism with the trivial
core carries the real coordinate subspace over `a` onto `F_a`. This presents a totally real
subbundle of a trivial bundle which need not have a global frame, such as the line field
`F_z = z^{k/2} ℝ` along the unit circle for odd `k`.
-/

public section

noncomputable section

open Bundle CategoryTheory Set Topology

namespace TauCeti.FiniteRankBundleCore

universe u v

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (B : Type u) [TopologicalSpace B] (n : ℕ)

/-- Local frames of the trivial bundle `B × 𝕜ⁿ`: for every point `i`, an open neighbourhood
`domain i` of `i` and a continuous family `frame i x`, `x ∈ domain i`, of automorphisms of `𝕜ⁿ`. -/
structure LocalFrames where
  /-- The domain of the frame at `i`. -/
  domain : B → Set B
  isOpen_domain : ∀ i, IsOpen (domain i)
  mem_domain_self : ∀ i, i ∈ domain i
  /-- The frame at `i` over a point `x` of its domain. -/
  frame : ∀ i, domain i → (Fin n → 𝕜) ≃L[𝕜] (Fin n → 𝕜)
  continuous_frame : ∀ i, Continuous fun x ↦ (frame i x : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜))

namespace LocalFrames

variable {𝕜 B n}

/-- Two families of local frames are equal when they have the same domains and the same frames. -/
@[ext (iff := false)]
theorem ext {F G : LocalFrames 𝕜 B n} (hd : F.domain = G.domain)
    (hf : ∀ i x (hx : x ∈ F.domain i), F.frame i ⟨x, hx⟩ = G.frame i ⟨x, hd ▸ hx⟩) : F = G := by
  cases F
  cases G
  dsimp only at hd hf
  subst hd
  congr
  exact funext fun i ↦ funext fun x ↦ hf i x x.property

variable (F : LocalFrames 𝕜 B n)

open Classical in
/-- The frame at `i` over any point `x`: `F.frame i x` on the domain of the frame, and the identity
elsewhere. -/
def frameAt (i x : B) : (Fin n → 𝕜) ≃L[𝕜] (Fin n → 𝕜) :=
  if hx : x ∈ F.domain i then F.frame i ⟨x, hx⟩ else ContinuousLinearEquiv.refl 𝕜 _

@[simp] theorem frameAt_of_mem {i x : B} (hx : x ∈ F.domain i) :
    F.frameAt i x = F.frame i ⟨x, hx⟩ := by
  simp only [frameAt, hx, ↓reduceDIte]

/-- Off its domain the frame at `i` is extended by the identity. -/
@[simp] theorem frameAt_of_notMem {i x : B} (hx : x ∉ F.domain i) :
    F.frameAt i x = ContinuousLinearEquiv.refl 𝕜 _ := by
  simp only [frameAt, hx, ↓reduceDIte]

/-- The frames are continuous on their domains. -/
theorem continuousOn_frameAt (i : B) :
    ContinuousOn (fun x ↦ (F.frameAt i x : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜))) (F.domain i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (F.continuous_frame i).congr fun x ↦ ?_
  rw [domRestrict_apply, F.frameAt_of_mem x.property]

/-- The inverse frames are continuous on the domain of the frame. -/
theorem continuousOn_frameAt_symm (i : B) :
    ContinuousOn (fun x ↦ ((F.frameAt i x).symm : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)))
      (F.domain i) :=
  fun x hx ↦ (F.continuousOn_frameAt i x hx).continuousLinearEquiv_symm

/-- The trivial bundle `B × 𝕜ⁿ` read in the local frames `F`: the chart at `i` has domain
`F.domain i`, and the transition from the chart at `i` to the chart at `j` over `x` is
`(F.frame j x)⁻¹ ∘ F.frame i x`. -/
@[expose]
def core : FiniteRankBundleCore 𝕜 B where
  rank := n
  core :=
    { baseSet := F.domain
      isOpen_baseSet := F.isOpen_domain
      indexAt := id
      mem_baseSet_at := F.mem_domain_self
      coordChange := fun i j x ↦ ((F.frameAt i x).trans (F.frameAt j x).symm : _ →L[𝕜] _)
      coordChange_self := fun i x _ v ↦ (F.frameAt i x).symm_apply_apply v
      continuousOn_coordChange := fun i j ↦
        ((F.continuousOn_frameAt_symm j).mono inter_subset_right).clm_comp
          ((F.continuousOn_frameAt i).mono inter_subset_left)
      coordChange_comp := fun i j k x _ v ↦ by
        simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
          ContinuousLinearEquiv.apply_symm_apply] }
  indexAt_eq := fun _ ↦ rfl

/-- The core of local frames of `𝕜ⁿ` has rank `n`. -/
@[simp] theorem rank_core : F.core.rank = n := (rfl)

/-- The chart of `F.core` at `i` is defined over the domain of the frame at `i`. -/
@[simp] theorem localTriv_baseSet_core (i : B) : (F.core.core.localTriv i).baseSet = F.domain i :=
  (rfl)

/-- The transition of `F.core` from the chart at `i` to the chart at `j` is the frame at `i`
followed by the inverse of the frame at `j`. -/
theorem coordChange_core (i j x : B) :
    F.core.core.coordChange i j x =
      ((F.frameAt i x).trans (F.frameAt j x).symm : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
  (rfl)

/-- The transition of `F.core` from the chart at `i` to the chart at `j`, applied to a vector. -/
@[simp] theorem coordChange_core_apply (i j x : B) (v : Fin n → 𝕜) :
    F.core.core.coordChange i j x v = (F.frameAt j x).symm (F.frameAt i x v) := (rfl)

/-- The bundle map from `F.core` to the trivial core: the frame at `i` in the chart at `i`. -/
def toTrivial : F.core ⟶ trivial 𝕜 B n where
  operator i _ := ⟨fun x ↦ (F.frameAt i x : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)),
    (F.continuousOn_frameAt i).comp_continuous continuous_subtypeVal fun x ↦ x.property.1⟩
  -- The transitions of the trivial core are identities, and those of `F.core` are
  -- `(F.frameAt i' x)⁻¹ ∘ F.frameAt i x` (`coordChange_core_apply`).
  compatible i i' _ _ x _ _ _ _ v := ((F.frameAt i' x).apply_symm_apply (F.frameAt i x v)).symm

/-- The bundle map from the trivial core to `F.core`: the inverse of the frame at `j` in the chart
at `j`. -/
def ofTrivial : trivial 𝕜 B n ⟶ F.core where
  operator _ j := ⟨fun x ↦ ((F.frameAt j x).symm : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)),
    (F.continuousOn_frameAt_symm j).comp_continuous continuous_subtypeVal fun x ↦ x.property.2⟩
  -- The transitions of the trivial core are identities, and those of `F.core` are
  -- `(F.frameAt j' x)⁻¹ ∘ F.frameAt j x` (`coordChange_core_apply`).
  compatible _ _ j j' x _ _ _ _ v :=
    congrArg (F.frameAt j' x).symm ((F.frameAt j x).apply_symm_apply v)

/-- The bundle map to the trivial core is the frame at `x` on the fibre over `x`. -/
@[simp] theorem fiberMap_toTrivial (x : B) :
    F.toTrivial.fiberMap x =
      (F.frame x ⟨x, F.mem_domain_self x⟩ : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) := by
  rw [← F.frameAt_of_mem (F.mem_domain_self x)]
  -- The fibre map is the operator in the charts at `x`, both cores being point-indexed.
  exact VectorBundleCore.CoordinateHom.fiberMap_def _ x

/-- The bundle map from the trivial core is the inverse of the frame at `x` on the fibre over
`x`. -/
@[simp] theorem fiberMap_ofTrivial (x : B) :
    F.ofTrivial.fiberMap x =
      ((F.frame x ⟨x, F.mem_domain_self x⟩).symm : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) := by
  rw [← F.frameAt_of_mem (F.mem_domain_self x)]
  -- The fibre map is the operator in the charts at `x`, both cores being point-indexed.
  exact VectorBundleCore.CoordinateHom.fiberMap_def _ x

/-- **The trivial bundle read in local frames is trivial**: `F.core` is isomorphic to the trivial
core by the frame at `x` on the fibre over `x`. -/
def isoTrivial : F.core ≅ trivial 𝕜 B n where
  hom := F.toTrivial
  inv := F.ofTrivial
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_toTrivial, fiberMap_ofTrivial, fiberMap_id]
    exact (F.frame x _).coe_symm_comp_coe
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_toTrivial, fiberMap_ofTrivial, fiberMap_id]
    exact (F.frame x _).coe_comp_coe_symm

@[simp] theorem isoTrivial_hom : F.isoTrivial.hom = F.toTrivial := (rfl)

@[simp] theorem isoTrivial_inv : F.isoTrivial.inv = F.ofTrivial := (rfl)

/-- **Local frames and totally real subbundles.** For complex local frames and `A ⊆ B`, the core
`F.core` is real along `A` exactly when, at each point `a ∈ A`, the frames at `a` differ by
transitions commuting with coordinatewise conjugation, that is, all span the same real subspace
`F.frame i a (ℝⁿ)` of `ℂⁿ`. -/
theorem isRealAlong_core_iff (F : LocalFrames ℂ B n) {A : Set B} :
    F.core.IsRealAlong A ↔ ∀ i j a, a ∈ A → ∀ (hi : a ∈ F.domain i) (hj : a ∈ F.domain j) v,
      (F.frame j ⟨a, hj⟩).symm (F.frame i ⟨a, hi⟩ (star v)) =
        star ((F.frame j ⟨a, hj⟩).symm (F.frame i ⟨a, hi⟩ v)) := by
  rw [isRealAlong_iff_coordChange_star]
  refine forall₄_congr fun i j a _ ↦ forall₂_congr fun hi hj ↦
    forall_congr' fun (v : Fin n → ℂ) ↦ ?_
  rw [coordChange_core]
  simp only [F.frameAt_of_mem hi, F.frameAt_of_mem hj]
  -- Both sides apply `(F.frame j _)⁻¹ ∘ F.frame i _`, once as the continuous linear map of
  -- `ContinuousLinearEquiv.trans` (`ContinuousLinearEquiv.coe_coe`,
  -- `ContinuousLinearEquiv.trans_apply`). These lemmas do not rewrite here: the transition acts on
  -- the fibre `Fin F.core.rank → ℂ`, which is `Fin n → ℂ` only by `rank_core`.
  exact Iff.rfl

end LocalFrames

end TauCeti.FiniteRankBundleCore
