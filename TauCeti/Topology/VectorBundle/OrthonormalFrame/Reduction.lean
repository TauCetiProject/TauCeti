/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal

/-!
# Local trivializations of reductions of the orthonormal frame bundle

Let `E → B` be a vector bundle with fibre inner products, let `V` be a real inner product space,
and let `T` be a trivialization of the orthonormal frame bundle of `E` modelled on `V` that is
*equivariant*, `T.orthonormalFrameBundleFiber.IsEquivariant`: it turns the right action of the
orthogonal group `unitary (V →L[ℝ] V)` into right multiplication on the fibre coordinate. Over its
base set every frame is then the local frame `T.symm (y, 1)` acted on by its fibre coordinate
(`Bundle.Trivialization.symm_apply_eq_smul`).

Let `H` be a subgroup of the orthogonal group and `S` a set of frames such that, for `p ∈ S`,
`op g • p ∈ S` exactly when `g ∈ H`. The positively oriented frames of an oriented bundle with
`H = SO(n)`, and the unitary frames of a fibrewise complex structure with `H = U(n)`, are examples:
`S` is then the total space of a reduction of the structure group to `H`. If on an open subset `U`
of the base set of `T` the local frame can be corrected into `S` by a continuous map
`c : B → unitary (V →L[ℝ] V)`, that is `op (c y) • T.symm (y, 1) ∈ S`, then `S` is trivial over `U`
with fibre `H`, equivariantly for the right action of `H`
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`): a frame `p` of
`S` over `y` goes to `(y, (c y)⁻¹ * (T p).2)`. This is how a continuous local section of the
reduced frames trivializes a reduction of the structure group.

## Main results

* `TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`: a set of frames
  stable exactly under `H` is locally trivial with fibre `H` wherever a local frame can be
  corrected into it continuously.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

noncomputable section

open Bundle Set MulOpposite

namespace TauCeti.OrthonormalFrameBundle

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]
  {T : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle ℝ F E V → B)}

section Equivariant

variable [T.orthonormalFrameBundleFiber.IsEquivariant]

/-- The inverse of an equivariant trivialization at `(y, g)` is the local frame `T.symm (y, 1)`
acted on by `g`: `Bundle.Trivialization.symm_apply_eq_smul` read through `totalSpaceEquiv`. -/
private theorem symm_apply_eq_smul_symm_apply_one {y : B} (hy : y ∈ T.baseSet)
    (g : unitary (V →L[ℝ] V)) :
    T.toOpenPartialHomeomorph.symm (y, g) = op g • T.toOpenPartialHomeomorph.symm (y, 1) := by
  have h := congrArg totalSpaceEquiv (T.orthonormalFrameBundleFiber.symm_apply_eq_smul
    (T.baseSet_orthonormalFrameBundleFiber ▸ hy) g)
  rwa [← TotalSpace.smul_mk, TotalSpace.eta, totalSpaceEquiv_smul,
    Trivialization.orthonormalFrameBundleFiber_symm_apply,
    Trivialization.orthonormalFrameBundleFiber_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-- Over the base set of an equivariant trivialization `T`, every frame is the local frame
`T.symm (y, 1)` acted on by its fibre coordinate. -/
private theorem eq_smul_symm_apply_one {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p.proj ∈ T.baseSet) : p = op (T p).2 • T.toOpenPartialHomeomorph.symm (p.proj, 1) :=
  (T.symm_apply_mk_proj (T.mem_source.2 hp)).symm.trans (symm_apply_eq_smul_symm_apply_one hp _)

end Equivariant

section Reduction

variable {H : Subgroup (unitary (V →L[ℝ] V))} {S : Set (OrthonormalFrameBundle ℝ F E V)}
  {U : Set B} {c : B → unitary (V →L[ℝ] V)}

variable (H) in
open scoped Classical in
/-- An orthogonal transformation, as an element of `H` when it is one, and `1` otherwise. -/
private def toSubgroup (g : unitary (V →L[ℝ] V)) : H :=
  if h : g ∈ H then ⟨g, h⟩ else 1

private theorem coe_toSubgroup {g : unitary (V →L[ℝ] V)} (hg : g ∈ H) :
    (toSubgroup H g : unitary (V →L[ℝ] V)) = g := by
  simp [toSubgroup, hg]

variable (T c) in
open scoped Classical in
/-- The inverse map of `reductionTrivialization`: it sends `(y, g)` to `T.symm (y, c y * g)` when
this lies in `S`, and to `p₀` otherwise. -/
private def reductionTrivializationInv (p₀ : S) (q : B × H) : S :=
  if h : T.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2) ∈ S then ⟨_, h⟩ else p₀

variable [T.orthonormalFrameBundleFiber.IsEquivariant]
  (hS : ∀ p ∈ S, ∀ g, op g • p ∈ S ↔ g ∈ H) (hUT : U ⊆ T.baseSet)
  (hcS : ∀ y ∈ U, op (c y) • T.toOpenPartialHomeomorph.symm (y, 1) ∈ S)

include hS hUT hcS

/-- Over `U`, the fibre coordinate of a frame of `S`, multiplied by the inverse correction, lies in
`H`. -/
private theorem inv_mul_mem {p : OrthonormalFrameBundle ℝ F E V} (hp : p.proj ∈ U) (h : p ∈ S) :
    (c p.proj)⁻¹ * (T p).2 ∈ H := by
  rw [← hS _ (hcS _ hp), smul_smul, ← op_mul, mul_inv_cancel_left,
    ← eq_smul_symm_apply_one (hUT hp)]
  exact h

/-- Over `U`, the inverse of `T` at the correction times an element of `H` lies in `S`. -/
private theorem symm_apply_mul_mem {y : B} (hy : y ∈ U) {g : unitary (V →L[ℝ] V)} (hg : g ∈ H) :
    T.toOpenPartialHomeomorph.symm (y, c y * g) ∈ S := by
  rw [symm_apply_eq_smul_symm_apply_one (hUT hy), op_mul, mul_smul]
  exact (hS _ (hcS y hy) g).2 hg

private theorem coe_reductionTrivializationInv (p₀ : S) {q : B × H} (hq : q.1 ∈ U) :
    (reductionTrivializationInv T c p₀ q : OrthonormalFrameBundle ℝ F E V) =
      T.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2) := by
  rw [reductionTrivializationInv, dite_eq_left (symm_apply_mul_mem hS hUT hcS hq q.2.property)]

variable [NormedAddCommGroup F] [FiberBundle F E] (hU : IsOpen U) (hc : ContinuousOn c U)

variable (U) in
/-- The trivialization of `S` over `U` with fibre `H`: a frame `p` over `y` goes to
`(y, (c y)⁻¹ * (T p).2)`. The frame `p₀` of `S` is a junk value of the inverse off its target. -/
private def reductionTrivialization (p₀ : S) :
    Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj) where
  toFun p := (p.val.proj, toSubgroup H ((c p.val.proj)⁻¹ * (T p.val).2))
  invFun := reductionTrivializationInv T c p₀
  source := {p | p.val.proj ∈ U}
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [mem_ofPred_eq, coe_reductionTrivializationInv hS hUT hcS p₀ hq.1,
      T.proj_symm_apply' (hUT hq.1)]
    exact hq.1
  left_inv' p hp := by
    apply Subtype.ext
    rw [coe_reductionTrivializationInv (q := (p.val.proj, _)) hS hUT hcS p₀ hp,
      coe_toSubgroup (inv_mul_mem hS hUT hcS hp p.property), mul_inv_cancel_left]
    exact T.symm_apply_mk_proj (T.mem_source.2 (hUT hp))
  right_inv' := by
    rintro ⟨y, g⟩ hq
    rw [Prod.mk.injEq, coe_reductionTrivializationInv hS hUT hcS p₀ hq.1,
      T.proj_symm_apply' (hUT hq.1), T.apply_symm_apply' (hUT hq.1), inv_mul_cancel_left]
    exact ⟨rfl, Subtype.ext (coe_toSubgroup g.property)⟩
  open_source := hU.preimage (continuous_proj.comp continuous_subtypeVal)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    have hproj : Continuous fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj :=
      continuous_proj.comp continuous_subtypeVal
    refine hproj.continuousOn.prodMk (Topology.IsInducing.subtypeVal.continuousOn_iff.2
      (ContinuousOn.congr ?_ fun p hp ↦ coe_toSubgroup (inv_mul_mem hS hUT hcS hp p.property)))
    exact ((hc.comp hproj.continuousOn fun _ hp ↦ hp).inv).mul (continuous_snd.comp_continuousOn
      (T.continuousOn_toFun.comp continuous_subtypeVal.continuousOn
        fun _ hp ↦ T.mem_source.2 (hUT hp)))
  continuousOn_invFun := by
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
      (f := fun q : B × H ↦ T.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2)) ?_
      fun q hq ↦ coe_reductionTrivializationInv hS hUT hcS p₀ hq.1)
    refine T.toOpenPartialHomeomorph.continuousOn_symm.comp (continuousOn_fst.prodMk ?_)
      fun _ hq ↦ T.mem_target.2 (hUT hq.1)
    exact (hc.comp continuousOn_fst mapsTo_fst_prod).mul
      (continuous_subtypeVal.comp continuous_snd).continuousOn
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private theorem reductionTrivialization_apply (p₀ p : S) :
    reductionTrivialization U hS hUT hcS hU hc p₀ p =
      (p.val.proj, toSubgroup H ((c p.val.proj)⁻¹ * (T p.val).2)) :=
  rfl

/-- The trivialization `reductionTrivialization` is equivariant over its base set. -/
private theorem reductionTrivialization_smul (p₀ : S) (g : H) {p : S}
    (hp : (p : OrthonormalFrameBundle ℝ F E V).proj ∈ U) :
    reductionTrivialization U hS hUT hcS hU hc p₀
        ⟨op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V),
          (hS _ p.property g).2 g.property⟩ =
      ((reductionTrivialization U hS hUT hcS hU hc p₀ p).1,
        (reductionTrivialization U hS hUT hcS hU hc p₀ p).2 * g) := by
  have h₁ := inv_mul_mem hS hUT hcS hp p.property
  have h₂ := inv_mul_mem hS hUT hcS (p := op (g : unitary (V →L[ℝ] V)) • p.val)
    (by rwa [proj_smul]) ((hS _ p.property g).2 g.property)
  rw [proj_smul] at h₂
  simp only [reductionTrivialization_apply, proj_smul]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [Subgroup.coe_mul, coe_toSubgroup h₁, coe_toSubgroup h₂,
    T.isEquivariant_orthonormalFrameBundleFiber_iff.1 inferInstance _ (hUT hp), mul_assoc]

include hU hc in
/-- A set `S` of orthonormal frames, carried into itself by exactly the elements of a subgroup `H`
of the orthogonal group, is trivial with fibre `H`, equivariantly for the right action of `H`,
over every open subset `U` of the base set of an equivariant trivialization `T` on which the local
frame `T.symm (y, 1)` can be corrected into `S` by a continuous `c : B → unitary (V →L[ℝ] V)`. -/
theorem exists_trivialization_of_continuousOn_smul_mem {x : B} (hx : x ∈ U) :
    ∃ t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      t.baseSet = U ∧ ∀ (g : H) (p : S), (p : OrthonormalFrameBundle ℝ F E V).proj ∈ U →
        t ⟨op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V),
          (hS _ p.property g).2 g.property⟩ = ((t p).1, (t p).2 * g) :=
  ⟨reductionTrivialization U hS hUT hcS hU hc ⟨_, hcS x hx⟩, rfl,
    fun g _ hp ↦ reductionTrivialization_smul hS hUT hcS hU hc _ g hp⟩

end Reduction

end TauCeti.OrthonormalFrameBundle
