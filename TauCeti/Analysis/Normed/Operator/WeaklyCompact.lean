/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import TauCeti.Analysis.Normed.Module.Dual.Functoriality
import TauCeti.Analysis.Normed.Module.Dual.Submodule
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# Weakly compact operators

A bounded operator `T : E →L[𝕜] F` between real or complex normed spaces is *weakly compact*
if the image of the closed unit ball of `E` is relatively compact in the weak topology of `F`,
that is, its closure in `WeakSpace 𝕜 F` is compact. Equivalently, `T` is a compact operator
into `WeakSpace 𝕜 F`; this lets weak compactness reuse Mathlib's `IsCompactOperator` API.

## Main results

* `ContinuousLinearMap.isWeaklyCompact_iff_isCompactOperator`: weak compactness as compactness
  into the weak topology.
* `ContinuousLinearMap.IsWeaklyCompact.add`, `.smul`, `.comp_clm`, `.clm_comp`: weakly compact
  operators are stable under sums, scalar multiples and composition with bounded operators.
* `IsCompactOperator.isWeaklyCompact`: compact operators are weakly compact.
* `ContinuousLinearMap.isWeaklyCompact_id_iff`: the identity is weakly compact exactly on a
  reflexive space; on an infinite-dimensional reflexive space it is weakly compact but not
  compact.
* `ContinuousLinearMap.isWeaklyCompact_iff_range_subset`: **Gantmacher's criterion**, `T` is
  weakly compact iff its bidual adjoint `T**` takes values in the canonical image of `F`.
* `ContinuousLinearMap.isWeaklyCompact_precomp_iff`: **Gantmacher's theorem**, an operator into
  a Banach space is weakly compact iff its adjoint is.

The adjoint of `T` is `ContinuousLinearMap.precomp 𝕜 T`, and the bidual adjoint is obtained by
applying `precomp` twice.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §3.5.
-/

public section

open Bornology Function Metric Set NormedSpace

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded operator is *weakly compact* if the image of the closed unit ball is relatively
compact in the weak topology of the codomain: its closure in `WeakSpace 𝕜 F` is compact. -/
def IsWeaklyCompact (T : E →L[𝕜] F) : Prop :=
  IsCompact (closure (toWeakSpace 𝕜 F '' (T '' closedBall 0 1)))

/-- Unfolding lemma for `ContinuousLinearMap.IsWeaklyCompact`. -/
theorem isWeaklyCompact_def {T : E →L[𝕜] F} :
    T.IsWeaklyCompact ↔ IsCompact (closure (toWeakSpace 𝕜 F '' (T '' closedBall 0 1))) :=
  Iff.rfl

/-- A bounded operator is weakly compact iff, as a map into the weak topology of its codomain,
it is a compact operator. -/
theorem isWeaklyCompact_iff_isCompactOperator {T : E →L[𝕜] F} :
    T.IsWeaklyCompact ↔ IsCompactOperator (toWeakSpace 𝕜 F ∘ T) := by
  rw [isWeaklyCompact_def, image_image]
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    ((toWeakSpace 𝕜 F).toLinearMap ∘ₗ T.toLinearMap) zero_lt_one).symm

alias ⟨IsWeaklyCompact.isCompactOperator, IsWeaklyCompact.of_isCompactOperator⟩ :=
  isWeaklyCompact_iff_isCompactOperator

/-- A weakly compact operator maps every bounded set to a relatively weakly compact set. -/
theorem IsWeaklyCompact.isCompact_closure_image {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact)
    {s : Set E} (hs : IsBounded s) :
    IsCompact (closure (toWeakSpace 𝕜 F '' (T '' s))) := by
  rw [image_image]
  exact hT.isCompactOperator.isCompact_closure_image_of_bounded
    (f := (toWeakSpace 𝕜 F).toLinearMap ∘ₗ T.toLinearMap) hs

/-- A bounded operator is weakly compact iff the image of the unit ball lies in a weakly compact
set. -/
theorem isWeaklyCompact_iff_exists_isCompact {T : E →L[𝕜] F} :
    T.IsWeaklyCompact ↔
      ∃ K : Set (WeakSpace 𝕜 F), IsCompact K ∧ toWeakSpace 𝕜 F '' (T '' closedBall 0 1) ⊆ K :=
  ⟨fun hT ↦ ⟨_, hT, subset_closure⟩, fun ⟨_, hK, hsub⟩ ↦ hK.closure_of_subset hsub⟩

/-! ### Algebraic operations -/

/-- The zero operator is weakly compact. -/
@[simp]
theorem isWeaklyCompact_zero : (0 : E →L[𝕜] F).IsWeaklyCompact :=
  .of_isCompactOperator <| by
    have h : toWeakSpace 𝕜 F ∘ ⇑(0 : E →L[𝕜] F) = 0 := by
      ext x
      simp
    rw [h]
    exact isCompactOperator_zero

/-- The sum of two weakly compact operators is weakly compact. -/
theorem IsWeaklyCompact.add {T S : E →L[𝕜] F} (hT : T.IsWeaklyCompact)
    (hS : S.IsWeaklyCompact) : (T + S).IsWeaklyCompact := by
  refine .of_isCompactOperator ?_
  have h : toWeakSpace 𝕜 F ∘ ⇑(T + S) = toWeakSpace 𝕜 F ∘ T + toWeakSpace 𝕜 F ∘ S := by
    ext x
    simp
  rw [h]
  exact hT.isCompactOperator.add hS.isCompactOperator

/-- A scalar multiple of a weakly compact operator is weakly compact. -/
theorem IsWeaklyCompact.smul {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact) (c : 𝕜) :
    (c • T).IsWeaklyCompact := by
  refine .of_isCompactOperator ?_
  have h : toWeakSpace 𝕜 F ∘ ⇑(c • T) = c • (toWeakSpace 𝕜 F ∘ T) := by
    ext x
    simp
  rw [h]
  exact hT.isCompactOperator.smul c

/-- The negative of a weakly compact operator is weakly compact. -/
theorem IsWeaklyCompact.neg {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact) :
    (-T).IsWeaklyCompact := by
  simpa using hT.smul (-1)

/-- The difference of two weakly compact operators is weakly compact. -/
theorem IsWeaklyCompact.sub {T S : E →L[𝕜] F} (hT : T.IsWeaklyCompact)
    (hS : S.IsWeaklyCompact) : (T - S).IsWeaklyCompact := by
  simpa only [sub_eq_add_neg] using hT.add hS.neg

/-- Precomposing a weakly compact operator with a bounded operator gives a weakly compact
operator. -/
theorem IsWeaklyCompact.comp_clm {D : Type*} [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
    {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact) (S : D →L[𝕜] E) :
    (T.comp S).IsWeaklyCompact :=
  .of_isCompactOperator (hT.isCompactOperator.comp_clm S)

/-- Postcomposing a weakly compact operator with a bounded operator gives a weakly compact
operator, since bounded operators are continuous for the weak topologies. -/
theorem IsWeaklyCompact.clm_comp {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact) (S : F →L[𝕜] G) :
    (S.comp T).IsWeaklyCompact :=
  -- `WeakSpace.map S` is `S` on the underlying spaces, and `toWeakSpace` is the identity map of
  -- the underlying space, so `WeakSpace.map S ∘ toWeakSpace ∘ T` is `toWeakSpace ∘ S ∘ T`.
  .of_isCompactOperator (hT.isCompactOperator.clm_comp (WeakSpace.map S))

end ContinuousLinearMap

/-- Every compact operator is weakly compact. -/
theorem IsCompactOperator.isWeaklyCompact {𝕜 E F : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : E →L[𝕜] F} (hT : IsCompactOperator T) : T.IsWeaklyCompact := by
  have h : ⇑(toWeakSpaceCLM 𝕜 F) = toWeakSpace 𝕜 F := funext (toWeakSpaceCLM_eq_toWeakSpace 𝕜 F)
  exact .of_isCompactOperator (h ▸ hT.continuous_comp (toWeakSpaceCLM 𝕜 F).continuous)

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ### The identity operator -/

/-- The identity of a normed space is weakly compact iff the space is reflexive. -/
theorem isWeaklyCompact_id_iff :
    (ContinuousLinearMap.id 𝕜 F).IsWeaklyCompact ↔ Surjective (inclusionInDoubleDual 𝕜 F) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : IsScalarTower ℝ 𝕜 F := .of_algebraMap_smul fun _ _ ↦ rfl
  rw [TauCeti.surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall,
    isWeaklyCompact_def, coe_id', image_id, ← (convex_closedBall (0 : F) 1).toWeakSpace_closure 𝕜,
    closure_closedBall]

/-- On an infinite-dimensional reflexive space, the identity is weakly compact but not compact.
Thus weak compactness of operators is strictly weaker than compactness. -/
theorem isWeaklyCompact_id_and_not_isCompactOperator_id
    (hF : Surjective (inclusionInDoubleDual 𝕜 F)) (hdim : ¬FiniteDimensional 𝕜 F) :
    (ContinuousLinearMap.id 𝕜 F).IsWeaklyCompact ∧
      ¬IsCompactOperator (ContinuousLinearMap.id 𝕜 F) :=
  ⟨isWeaklyCompact_id_iff.2 hF, fun h ↦ hdim (.of_isCompactOperator_id h)⟩

/-! ### Gantmacher's theorem -/

/-- **Gantmacher's criterion.** A bounded operator is weakly compact iff its bidual adjoint
`T**` takes values in the canonical image of the codomain in its bidual. No completeness is
assumed. -/
theorem isWeaklyCompact_iff_range_subset {T : E →L[𝕜] F} :
    T.IsWeaklyCompact ↔
      range (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)) ⊆
        range (inclusionInDoubleDual 𝕜 F) := by
  -- `A` is the bidual adjoint, viewed between the weak-star topologies of the biduals.
  set A : WeakDual 𝕜 (StrongDual 𝕜 E) → WeakDual 𝕜 (StrongDual 𝕜 F) := fun Φ ↦
    StrongDual.toWeakDual
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) (WeakDual.toStrongDual Φ))
  have hA : Continuous A :=
    WeakDual.continuous_of_continuous_eval fun f ↦ WeakDual.eval_continuous (f.comp T)
  have hnat (x : E) : A (inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E x)) =
      inclusionInDoubleDualWeak 𝕜 F (toWeakSpace 𝕜 F (T x)) := by
    simp [A, inclusionInDoubleDualWeak_apply]
  have hmem (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
      A (StrongDual.toWeakDual Φ) ∈ range (inclusionInDoubleDualWeak 𝕜 F) ↔
        precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) Φ ∈
          range (inclusionInDoubleDual 𝕜 F) := by
    simp only [A, mem_range, inclusionInDoubleDualWeak_apply, StrongDual.toStrongDual_toWeakDual,
      EmbeddingLike.apply_eq_iff_eq, (toWeakSpace 𝕜 F).symm.surjective.exists]
  constructor
  · -- By Goldstine, `Φ` lies in the weak-star closure of the image of a ball of `E`, so `A Φ`
    -- lies in the weak-star closure of the image of the weakly compact set `K`.
    rintro hT _ ⟨Φ, rfl⟩
    rw [← hmem]
    set K := closure (toWeakSpace 𝕜 F '' (T '' closedBall 0 ‖Φ‖))
    have hK : IsCompact K := hT.isCompact_closure_image isBounded_closedBall
    have hΦ : StrongDual.toWeakDual Φ ∈
        closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 ‖Φ‖)) := by
      rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero, mem_preimage,
        StrongDual.toStrongDual_toWeakDual,
        mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))]
    have hsub : A '' (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 ‖Φ‖)) ⊆
        inclusionInDoubleDualWeak 𝕜 F '' K := by
      rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, subset_closure ⟨T x, ⟨x, hx, rfl⟩, rfl⟩, (hnat x).symm⟩
    obtain ⟨y, -, hy⟩ := closure_minimal hsub
      (hK.image (inclusionInDoubleDualWeak 𝕜 F).continuous).isClosed
      (image_closure_subset_closure_image hA ⟨_, hΦ, rfl⟩)
    exact ⟨y, hy⟩
  · -- The image of the unit ball of `E` lands in `A` of the weak-star compact bidual ball,
    -- which lies in the canonical image of `F`.
    intro h
    apply isCompact_closure_weakSpace_of_isBounded 𝕜 F
    · rw [preimage_image_eq _ (toWeakSpace 𝕜 F).injective]
      exact T.lipschitzWith.isBounded_image isBounded_closedBall
    · have hsub : inclusionInDoubleDualWeak 𝕜 F '' (toWeakSpace 𝕜 F '' (T '' closedBall 0 1)) ⊆
          A '' (WeakDual.toStrongDual ⁻¹' closedBall 0 1) := by
        rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
        refine ⟨_, ?_, hnat x⟩
        rw [mem_preimage, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
          StrongDual.toStrongDual_toWeakDual,
          mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))]
        exact (double_dual_bound 𝕜 E x).trans (mem_closedBall_zero_iff.1 hx)
      refine (closure_minimal hsub ((WeakDual.isCompact_closedBall 0 1).image hA).isClosed).trans ?_
      rintro _ ⟨Φ, -, rfl⟩
      simpa using (hmem (WeakDual.toStrongDual Φ)).2 (h ⟨_, rfl⟩)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Gantmacher's theorem**, forward direction: the adjoint of a weakly compact operator is
weakly compact. -/
theorem IsWeaklyCompact.precomp {T : E →L[𝕜] F} (hT : T.IsWeaklyCompact) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).IsWeaklyCompact := by
  rw [isWeaklyCompact_iff_range_subset]
  rintro _ ⟨ψ, rfl⟩
  -- `T***ψ` is the canonical image of `T*(ψ ∘ J_F)`.
  refine ⟨ContinuousLinearMap.precomp 𝕜 T (ψ.comp (inclusionInDoubleDual 𝕜 F)),
    ContinuousLinearMap.ext fun Φ ↦ ?_⟩
  obtain ⟨y, hy⟩ := isWeaklyCompact_iff_range_subset.1 hT ⟨Φ, rfl⟩
  have h := congrArg (fun Ψ ↦ Ψ (ψ.comp (inclusionInDoubleDual 𝕜 F))) hy
  have hy' : Φ.comp (ContinuousLinearMap.precomp 𝕜 T) = inclusionInDoubleDual 𝕜 F y := by
    simpa using hy.symm
  simp only [dual_def, precomp_apply, comp_apply] at h ⊢
  rw [hy', h]

/-- **Gantmacher's theorem**, reverse direction: an operator into a Banach space whose adjoint is
weakly compact is weakly compact. -/
theorem IsWeaklyCompact.of_precomp [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).IsWeaklyCompact) :
    T.IsWeaklyCompact := by
  rw [isWeaklyCompact_iff_range_subset]
  rintro _ ⟨Φ, rfl⟩
  -- The canonical image of `F` is closed in the bidual. If `T**Φ` were outside it, a functional
  -- `ψ` on the bidual vanishing on that image would detect it. Gantmacher's criterion for the
  -- adjoint writes `T***ψ` as the canonical image of some `g`; then `g` vanishes on `E`, so
  -- `ψ (T**Φ) = Φ g = 0`.
  set S : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) :=
    LinearMap.range (inclusionInDoubleDual 𝕜 F).toLinearMap
  have hS : IsClosed (S : Set (StrongDual 𝕜 (StrongDual 𝕜 F))) := by
    rw [LinearMap.coe_range]
    exact (inclusionInDoubleDualLi 𝕜 (E := F)).isometry.isUniformInducing.isComplete_range.isClosed
  by_contra hΦ
  obtain ⟨ψ, hψS, hψ⟩ := Submodule.exists_dual_forall_mem_eq_zero_ne_zero (𝕜 := 𝕜) hS
    (x := ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 T) Φ)
    fun h ↦ hΦ (LinearMap.mem_range.1 h)
  obtain ⟨g, hg⟩ := isWeaklyCompact_iff_range_subset.1 hT ⟨ψ, rfl⟩
  have hg0 : g = 0 := by
    ext x
    have h := congrArg (fun Ψ ↦ Ψ (inclusionInDoubleDual 𝕜 E x)) hg
    simp only [dual_def, precomp_apply, comp_apply] at h
    rw [h, zero_apply]
    exact hψS _ (LinearMap.mem_range_self _ (T x))
  have h := congrArg (fun Ψ ↦ Ψ Φ) hg
  simp only [hg0, precomp_apply, comp_apply, map_zero] at h
  exact hψ h.symm

/-- **Gantmacher's theorem.** An operator into a Banach space is weakly compact iff its adjoint
is weakly compact. -/
theorem isWeaklyCompact_precomp_iff [CompleteSpace F] {T : E →L[𝕜] F} :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).IsWeaklyCompact ↔
      T.IsWeaklyCompact :=
  ⟨.of_precomp, .precomp⟩

end ContinuousLinearMap
