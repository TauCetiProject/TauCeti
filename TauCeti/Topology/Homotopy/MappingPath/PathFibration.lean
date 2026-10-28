/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction

/-!
# The source projection of a mapping-path fibre

For `f : C(B, K)` and `k : K`, the mapping-path fibre `MappingPathFiber f k` consists of a point
`b` of `B` and a path in `K` from `f b` to `k`. Its projection to `B` is a Hurewicz fibration with
an explicit lifting function: the lift of a path `β` from `(b, γ)` at time `s` is `β s` together
with `f ∘ β` run backwards on `[0, s]` followed by `γ`, at speed `1 + s`. At `s = 1` this is the
concatenation `(f ∘ β)⁻¹ * γ`, so transport in this fibration prepends the reversed image path.

For `f = id` the projection is the fixed-end path fibration of `K`, sending a path ending at `k`
to its starting point. The fibre projection for a general `f` is its base change along `f`, by an
explicit homeomorphism over `B`. The fibre of the projection over `b` is the native path space
`Path (f b) k`; it may be empty.

The path-prepending construction below adapts
`MappingPathSpace.endpointLiftingFunction` from `MappingPath/LiftingFunction.lean`, reversing the
attachment direction so that the new segment is prepended rather than appended.

## Main definitions

* `TauCeti.MappingPathFiber.proj f k`: the source projection `MappingPathFiber f k → B`.
* `TauCeti.MappingPathFiber.projLiftingFunction f k`: its path-prepending lifting function.
* `TauCeti.MappingPathFiber.pullbackHomeomorph f k`: the identification of
  `MappingPathFiber f k` with the base change along `f` of the fixed-end path fibration.
* `TauCeti.MappingPathFiber.projFiberHomeomorphPath f k b`: the fibre of the projection over `b`
  is `Path (f b) k`.

## Main results

* `TauCeti.MappingPathFiber.isHurewiczFibration_proj`: the source projection is a Hurewicz
  fibration, for test spaces in every universe.
* `TauCeti.MappingPathFiber.projLiftingFunction_lift_one_val_snd`: the lift at time `1` carries
  the concatenation `(f ∘ β)⁻¹ * γ`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

namespace MappingPathFiber

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]
variable (f : C(B, K)) (k : K)

/-- The path `δ` run backwards on `[0, s]`, followed by `γ`, at speed `1 + s`. When
`δ 0 = γ 0` this is a continuous path from `δ s` to `γ 1`, equal to `γ` at `s = 0`. -/
private noncomputable def prependPath (δ γ : C(I, K)) (s u : I) : K :=
  if (1 + (s : ℝ)) * u ≤ s then IccExtend zero_le_one δ (s - (1 + (s : ℝ)) * u)
  else IccExtend zero_le_one γ ((1 + (s : ℝ)) * u - s)

private theorem continuous_prependPath {Y : Type*} [TopologicalSpace Y] {δ γ : Y → C(I, K)}
    (hδ : Continuous δ) (hγ : Continuous γ) (h : ∀ y, δ y 0 = γ y 0) {s u : Y → I}
    (hs : Continuous s) (hu : Continuous u) :
    Continuous fun y ↦ prependPath (δ y) (γ y) (s y) (u y) := by
  have hδ' : Continuous fun q : Y × I ↦ δ q.1 q.2 := by fun_prop
  have hγ' : Continuous fun q : Y × I ↦ γ q.1 q.2 := by fun_prop
  refine Continuous.if_le (Continuous.IccExtend hδ' (by fun_prop))
    (Continuous.IccExtend hγ' (by fun_prop)) (by fun_prop) (by fun_prop) fun y hy ↦ ?_
  rw [hy, sub_self, IccExtend_left, IccExtend_left]
  exact h y

private theorem prependPath_zero_left {δ γ : C(I, K)} (h : δ 0 = γ 0) (u : I) :
    prependPath δ γ 0 u = γ u := by
  by_cases hu : (u : ℝ) ≤ 0
  · have hu : u = 0 := Subtype.ext (le_antisymm hu u.2.1)
    simp [prependPath, hu, IccExtend_left, h]
  · simp [prependPath, hu]

private theorem prependPath_zero_right (δ γ : C(I, K)) (s : I) : prependPath δ γ s 0 = δ s := by
  simp [prependPath, s.2.1]

private theorem prependPath_one_right (δ γ : C(I, K)) (s : I) : prependPath δ γ s 1 = γ 1 := by
  simp [prependPath, IccExtend_right]

private theorem path_zero_eq (x : MappingPathSpace (proj f k)) :
    f.comp x.val.2 0 = x.val.1.val.2 0 := by
  rw [ContinuousMap.comp_apply, x.property, proj_apply, x.val.1.property.1]

/-- The lifting function of the source projection of `MappingPathFiber f k`: the lift of a path
`β` from `(b, γ)` at time `s` is `β s` together with `f ∘ β` run backwards on `[0, s]` followed by
`γ`, at speed `1 + s`. -/
noncomputable def projLiftingFunction : LiftingFunction (proj f k) where
  toContinuousMap := ContinuousMap.curry
    { toFun q := ⟨(q.1.val.2 q.2,
        ⟨prependPath (f.comp q.1.val.2) q.1.val.1.val.2 q.2, continuous_prependPath
          continuous_const continuous_const (fun _ ↦ path_zero_eq f k q.1) continuous_const
          continuous_id⟩),
        by simp [prependPath_zero_right], by simpa [prependPath_one_right] using
          q.1.val.1.property.2⟩
      continuous_toFun := by
        refine (by fun_prop : Continuous fun q : MappingPathSpace (proj f k) × I ↦
          q.1.val.2 q.2).prodMk ?_ |>.subtype_mk _
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        exact continuous_prependPath (by fun_prop) (by fun_prop)
          (fun q : (MappingPathSpace (proj f k) × I) × I ↦ path_zero_eq f k q.1.1)
          (by fun_prop) (by fun_prop) }
  apply_zero' x := by
    refine Subtype.ext (Prod.ext ?_ (ContinuousMap.ext fun u ↦ ?_))
    · simpa using x.property
    · simpa using prependPath_zero_left (path_zero_eq f k x) u
  comp_apply' x := by
    ext s
    simp

/-- The lifts of the source projection lie over the given path. -/
@[simp]
theorem projLiftingFunction_lift_val_fst (x : MappingPathFiber f k) (β : C(I, B))
    (h : β 0 = proj f k x) (s : I) :
    ((projLiftingFunction f k).lift x β h s).val.1 = β s := by
  simp [LiftingFunction.lift_def, projLiftingFunction]

/-- The path of a lift of the source projection: at time `s`, the image path `f ∘ β` run
backwards on `[0, s]` and followed by the original path `γ`, at speed `1 + s`. -/
theorem projLiftingFunction_lift_val_snd (x : MappingPathFiber f k) (β : C(I, B))
    (h : β 0 = proj f k x) (s u : I) :
    ((projLiftingFunction f k).lift x β h s).val.2 u =
      if (1 + (s : ℝ)) * u ≤ s then IccExtend zero_le_one (f.comp β) (s - (1 + (s : ℝ)) * u)
      else IccExtend zero_le_one x.val.2 ((1 + (s : ℝ)) * u - s) := by
  simp [LiftingFunction.lift_def, projLiftingFunction, prependPath]

/-- At time `1`, the lift of `β` from `(b, γ)` carries the concatenation `(f ∘ β)⁻¹ * γ`. -/
theorem projLiftingFunction_lift_one_val_snd (x : MappingPathFiber f k) (β : C(I, B))
    (h : β 0 = proj f k x) :
    ((projLiftingFunction f k).lift x β h 1).val.2 =
      ((⟨f.comp β, rfl, rfl⟩ : Path (f (β 0)) (f (β 1))).symm.trans
        (⟨x.val.2, x.property.1.trans (congrArg f (h.trans (proj_apply f k x))).symm,
          x.property.2⟩ :
          Path (f (β 0)) k)).toContinuousMap := by
  ext u
  rw [projLiftingFunction_lift_val_snd, Path.coe_toContinuousMap, Path.trans_apply]
  simp only [Set.Icc.coe_one]
  split_ifs with h₁ h₂ h₂
  · rw [IccExtend_of_mem _ _ ⟨by linarith, by linarith [u.2.1]⟩, Path.symm_apply, Path.coe_mk']
    exact congrArg _ (Subtype.ext (by rw [coe_symm_eq]; ring))
  · exact absurd (by linarith) h₂
  · exact absurd (by linarith) h₁
  · rw [IccExtend_of_mem _ _ ⟨by linarith, by linarith [u.2.2]⟩, Path.coe_mk']
    exact congrArg _ (Subtype.ext (by ring))

/-- The source projection of a mapping-path fibre is a Hurewicz fibration, for test spaces in
every universe. -/
theorem isHurewiczFibration_proj : IsHurewiczFibration.{w} (proj f k) :=
  (projLiftingFunction f k).isHurewiczFibration

end MappingPathFiber

end TauCeti
