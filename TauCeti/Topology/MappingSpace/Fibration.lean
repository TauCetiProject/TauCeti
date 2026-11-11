/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Prod
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic
public import TauCeti.Topology.MappingSpace.FreeLoop
import TauCeti.Topology.Homotopy.Extension.Cube

/-!
# Restriction fibrations of mapping spaces

For a closed cofibration `A ⊆ K`, restriction `C(K, X) → C(A, X)` is a Hurewicz fibration
when `K` is locally compact. Its closed subspace `A` is then locally compact as well.
In particular this applies to closed cofibrations of compact Hausdorff spaces. The mapping
spaces have the compact-open topology.

A homotopy of restricted maps is extended over `K` while retaining an arbitrary parameter
space. Local compactness is needed only to evaluate the original families continuously;
there is no compactness or separation assumption on the parameter space or the target `X`.

Evaluation of free loops `C(S¹, Q) → Q` at `1 ∈ S¹` is such a fibration
(`TauCeti.isHurewiczFibration_mappingSpaceEval_one`): a free loop is a path `I → Q` whose
restriction to `{0, 1}` is constant, so evaluation is the base change of restriction to
`{0, 1} ⊆ I` along the constant maps. Its restriction to the contractible free loops `𝓛₀Q`, a
union of path components, is a Hurewicz fibration as well
(`TauCeti.isHurewiczFibration_basepointContractibleLoop`). Both have the constant loops as a
section.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I, cofibrations and mapping spaces.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

variable {K : Type u} {X : Type v} [TopologicalSpace K] [TopologicalSpace X]
  {A : Set K} [LocallyCompactSpace K]

/-- Restriction along a closed cofibration is a Hurewicz fibration of compact-open mapping
spaces. The test spaces can lie in any universe. -/
theorem HasHomotopyExtensionProperty.isHurewiczFibration_restrict
    (h : HasHomotopyExtensionProperty A) (hA : IsClosed A) :
    IsHurewiczFibration.{w} (fun f : C(K, X) ↦ f.restrict A) := by
  let _ : LocallyCompactSpace A := hA.locallyCompactSpace
  refine isHurewiczFibration_iff.mpr ⟨ContinuousMap.continuous_restrict A,
    fun T _ f H hH ↦ ?_⟩
  let F : C(T × K, X) := f.uncurry
  let H' : C(I × ((univ : Set T) ×ˢ A), X) :=
    ⟨fun q ↦ H (q.1, q.2.val.1) ⟨q.2.val.2, q.2.property.2⟩,
      (H.continuous.comp (by fun_prop)).eval (by fun_prop)⟩
  have hH' : ∀ z : (univ : Set T) ×ˢ A, H' (0, z) = F z := fun z ↦
    ContinuousMap.congr_fun (hH z.val.1) ⟨z.val.2, z.property.2⟩
  obtain ⟨G, hG₀, hG₁⟩ := (h.univ_prod hA).exists_extension_of_isClosed
    (isClosed_univ.prod hA) F H' hH'
  let G' : C(I × T, C(K, X)) :=
    (G.comp ⟨fun q : (I × T) × K ↦ (q.1.1, (q.1.2, q.2)), by fun_prop⟩).curry
  refine ⟨G', funext fun q ↦ ContinuousMap.ext fun a ↦ ?_, fun t ↦ ?_⟩
  · simpa only [G', H', Function.comp_apply, ContinuousMap.restrict_apply,
      ContinuousMap.curry_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
      hG₁ q.1 ⟨(q.2, a.val), ⟨mem_univ _, a.property⟩⟩
  · apply ContinuousMap.ext
    intro k
    simpa only [G', F, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using
      hG₀ (t, k)

/-! ### Evaluation of free loops -/

section FreeLoop

variable {Q : Type v} [TopologicalSpace Q]

/-- The closed unit-interval paths are the pullback of restriction to `{0, 1} ⊆ I` along the
constant maps: a path is closed exactly when its restriction to `{0, 1}` is constant. -/
private def closedUnitPathHomeomorphPullback :
    ClosedUnitPath Q ≃ₜ
      {x : Q × C(I, Q) // ContinuousMap.const' (X := ({0, 1} : Set I)) x.1 =
        x.2.restrict ({0, 1} : Set I)} where
  toFun γ := ⟨(γ.1 0, γ.1), ContinuousMap.ext fun t ↦ by
    obtain ⟨t, rfl | rfl⟩ := t
    · rfl
    · exact γ.2⟩
  invFun x := ⟨x.1.2, by
    have h₀ : x.1.1 = x.1.2 0 := ContinuousMap.congr_fun x.2 ⟨0, Or.inl rfl⟩
    have h₁ : x.1.1 = x.1.2 1 := ContinuousMap.congr_fun x.2 ⟨1, Or.inr rfl⟩
    exact h₀.symm.trans h₁⟩
  left_inv _ := rfl
  right_inv x := by
    have h₀ : x.1.1 = x.1.2 0 := ContinuousMap.congr_fun x.2 ⟨0, Or.inl rfl⟩
    exact Subtype.ext (Prod.ext h₀.symm rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem coe_closedUnitPathHomeomorphPullback (γ : ClosedUnitPath Q) :
    (closedUnitPathHomeomorphPullback γ : Q × C(I, Q)) = (γ.1 0, γ.1) :=
  rfl

/-- **Evaluation of free loops is a Hurewicz fibration.** Evaluation `C(S¹, Q) → Q` at
`1 ∈ S¹` is a Hurewicz fibration. -/
theorem isHurewiczFibration_mappingSpaceEval_one :
    IsHurewiczFibration.{w} (mappingSpaceEval (X := Q) (1 : Circle)) := by
  have hρ : IsHurewiczFibration.{w} fun f : C(I, Q) ↦ f.restrict ({0, 1} : Set I) :=
    hasHomotopyExtensionProperty_zero_one.isHurewiczFibration_restrict (Set.toFinite _).isClosed
  convert (hρ.pullback ContinuousMap.const').comp_homeomorph
    (circleMapHomeomorphClosedUnitPath.trans closedUnitPathHomeomorphPullback) using 1
  funext γ
  rw [Function.comp_apply, Homeomorph.trans_apply, coe_closedUnitPathHomeomorphPullback,
    circleMapHomeomorphClosedUnitPath_apply, unitToCircle_zero, mappingSpaceEval_apply]

/-- **Evaluation of contractible free loops is a Hurewicz fibration.** Evaluation `𝓛₀Q → Q` at
`1 ∈ S¹` is a Hurewicz fibration, since `𝓛₀Q` is a union of path components of `C(S¹, Q)`. -/
theorem isHurewiczFibration_basepointContractibleLoop :
    IsHurewiczFibration.{w} (basepointContractibleLoop (Q := Q)) := by
  have h := (isHurewiczFibration_mappingSpaceEval_one.{w} (Q := Q)).comp_subtypeVal
    (S := contractibleLoops Q) fun _ _ hγ h ↦ by
      obtain ⟨q, hq⟩ := mem_contractibleLoops_iff.1 hγ
      exact mem_contractibleLoops_iff.2 ⟨q, h.symm.trans hq⟩
  convert h using 1
  funext γ
  rw [basepointContractibleLoop_apply, Function.comp_apply, mappingSpaceEval_apply]

end FreeLoop

end TauCeti
