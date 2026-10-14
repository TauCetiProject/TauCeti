/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Topology.Sets.Clopens
public import TauCeti.Topology.ContinuousMap.Basic

/-!
# Extension by zero from a clopen subset

`TauCeti.zeroExtendClopen` extends continuous functions from a clopen subset by zero,
as a continuous linear map. It preserves the supremum norm, including for the empty subset.
Restriction followed by extension is multiplication by the clopen characteristic function;
the two complementary projectors sum to the identity.

The extension uses Mathlib’s `ContinuousMap.liftCover` to glue the function and zero.

These test-function operators give restriction and decomposition of abstract measures.
See Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, §3.5.3,
Remark 3.31, for their use in p-adic integration.
-/

public section

open TopologicalSpace ContinuousMap

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

variable (s : Clopens X) (R : Type*) [NormedCommRing R]

omit [CompactSpace X] in
private noncomputable def zeroExtendClopenFun (f : C(s, R)) : C(X, R) :=
  ContinuousMap.liftCover (fun b : Bool ↦ if b then (s : Set X) else (s : Set X)ᶜ)
    (fun b ↦ by
      cases b
      · exact 0
      · exact f)
    (by
      intro i j x hi hj
      cases i <;> cases j
      · rfl
      · exact (hi hj).elim
      · exact (hj hi).elim
      · rfl)
    (by
      intro x
      by_cases hx : x ∈ s
      · exact ⟨true, s.isOpen.mem_nhds hx⟩
      · exact ⟨false, s.isClopen.compl.isOpen.mem_nhds hx⟩)

omit [CompactSpace X] in
private lemma zeroExtendClopenFun_mem (f : C(s, R)) (x : s) :
    zeroExtendClopenFun s R f x = f x := by
  unfold zeroExtendClopenFun
  exact ContinuousMap.liftCover_coe
    (S := fun b : Bool ↦ if b then (s : Set X) else (s : Set X)ᶜ)
    (i := true) ⟨x.val, x.property⟩

omit [CompactSpace X] in
private lemma zeroExtendClopenFun_not_mem (f : C(s, R)) {x : X} (hx : x ∉ s) :
    zeroExtendClopenFun s R f x = 0 := by
  unfold zeroExtendClopenFun
  exact ContinuousMap.liftCover_coe
    (S := fun b : Bool ↦ if b then (s : Set X) else (s : Set X)ᶜ)
    (i := false) ⟨x, hx⟩

/-- Extension by zero from a clopen subset, as a continuous linear map. -/
noncomputable def zeroExtendClopen : C(s, R) →L[R] C(X, R) :=
  LinearMap.mkContinuous
    { toFun := zeroExtendClopenFun s R
      map_add' := by
        intro f g
        ext x
        by_cases hx : x ∈ s
        · simp only [ContinuousMap.add_apply,
            zeroExtendClopenFun_mem s R _ ⟨x, hx⟩]
        · simp [zeroExtendClopenFun_not_mem, hx]
      map_smul' := by
        intro a f
        ext x
        by_cases hx : x ∈ s
        · simp only [ContinuousMap.smul_apply, RingHom.id_apply,
            zeroExtendClopenFun_mem s R _ ⟨x, hx⟩]
        · simp [zeroExtendClopenFun_not_mem, hx] }
    1 (fun f ↦ by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro x
      by_cases hx : x ∈ s
      · exact (congrArg norm (zeroExtendClopenFun_mem s R f ⟨x, hx⟩)).trans_le
          (f.norm_coe_le_norm ⟨x, hx⟩)
      · exact (congrArg norm (zeroExtendClopenFun_not_mem s R f hx)).trans_le
          (by simp))

@[simp]
theorem zeroExtendClopen_apply_mem (f : C(s, R)) (x : s) :
    zeroExtendClopen s R f x = f x :=
  zeroExtendClopenFun_mem s R f x

@[simp]
theorem zeroExtendClopen_apply_notMem (f : C(s, R)) {x : X} (hx : x ∉ s) :
    zeroExtendClopen s R f x = 0 :=
  zeroExtendClopenFun_not_mem s R f hx

/-- Extension by zero preserves the supremum norm, even when the clopen is empty. -/
@[simp]
theorem norm_zeroExtendClopen (f : C(s, R)) : ‖zeroExtendClopen s R f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x ↦ by
      by_cases hx : x ∈ s
      · rw [zeroExtendClopen_apply_mem s R f ⟨x, hx⟩]
        exact f.norm_coe_le_norm ⟨x, hx⟩
      · simp [hx]
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ by
      rw [← zeroExtendClopen_apply_mem s R f x]
      exact (zeroExtendClopen s R f).norm_coe_le_norm x

@[simp]
theorem restrict_zeroExtendClopen (f : C(s, R)) :
    (zeroExtendClopen s R f).restrict s = f := by
  ext x
  rw [ContinuousMap.restrict_apply]
  exact zeroExtendClopen_apply_mem s R f x

/-- Restriction followed by extension is the clopen characteristic-function projector. -/
theorem zeroExtendClopen_restrict (f : C(X, R)) :
    zeroExtendClopen s R (f.restrict s) =
      (LocallyConstant.charFn R s.isClopen).toContinuousMap * f := by
  ext x
  by_cases hx : x ∈ s
  · simp only [zeroExtendClopen_apply_mem s R _ ⟨x, hx⟩,
      ContinuousMap.restrict_apply f s ⟨x, hx⟩, ContinuousMap.mul_apply,
      LocallyConstant.toContinuousMap, ContinuousMap.coe_mk, LocallyConstant.coe_charFn,
      Set.indicator_of_mem hx, Pi.one_apply, one_mul]
  · simp [LocallyConstant.coe_charFn, hx]

/-- Every test function is the sum of its two complementary clopen projections. -/
theorem zeroExtendClopen_restrict_add_compl (f : C(X, R)) :
    zeroExtendClopen s R (f.restrict s) +
      zeroExtendClopen sᶜ R (f.restrict (sᶜ : Clopens X)) = f := by
  rw [zeroExtendClopen_restrict, zeroExtendClopen_restrict]
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, LocallyConstant.toContinuousMap,
    ContinuousMap.coe_mk, LocallyConstant.coe_charFn, ← Set.indicator_mul_left,
    Pi.one_apply, one_mul, Clopens.coe_compl]
  exact congrFun (Set.indicator_self_add_compl (s : Set X) (f : X → R)) x

/-- Extension by zero commutes with pullback when the source clopen is the preimage. -/
theorem zeroExtendClopen_comp_restrictPreimage {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (t : Clopens Y) (f : C(X, Y)) (g : C(t, R)) :
    let s : Clopens X := ⟨f ⁻¹' (t : Set Y), t.isClopen.preimage f.continuous⟩
    (zeroExtendClopen t R g).comp f =
      zeroExtendClopen s R (g.comp (f.restrictPreimage t)) := by
  intro s
  ext x
  by_cases hx : f x ∈ t
  · have hxs : x ∈ s := hx
    simp only [ContinuousMap.comp_apply, zeroExtendClopen_apply_mem t R g ⟨f x, hx⟩,
      zeroExtendClopen_apply_mem s R _ ⟨x, hxs⟩]
    rfl
  · have hxs : x ∉ s := hx
    simp only [ContinuousMap.comp_apply, zeroExtendClopen_apply_notMem t R g hx,
      zeroExtendClopen_apply_notMem s R _ hxs]

end TauCeti
