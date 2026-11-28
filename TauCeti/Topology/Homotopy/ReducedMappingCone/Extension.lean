/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.ReducedMappingCone.Basic
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Pointed homotopy extension for the reduced mapping cone

A based homotopy on `Y` of the restriction of a map `C_f → Z` extends to a based
homotopy on `C_f`. Thus a map `C_f → Z` factors through the collapse to `ΣX` up to
pointed homotopy if and only if its restriction to `Y` is pointed-nullhomotopic.
This is exactness at `[C_f,Z]` in the sequence of pointed homotopy classes.

## References

* A. Hatcher, *Algebraic Topology*, §4.3, the mapping cone and the cofiber sequence.
-/

public section

noncomputable section

universe u

open Set
open scoped unitInterval

namespace TauCeti.BasedTopologicalSpace.reducedMappingCone

variable {X Y Z : BasedTopologicalSpace.{u}} (f : Hom X Y) (h : Hom (reducedMappingCone f) Z)
  {g : Hom Y Z} (K : (h.comp (incl f)).toContinuousMap.HomotopyRel g.toContinuousMap
    {Y.basepoint})

/- Along the positive half of each line keep the old map. Along the negative half
follow the homotopy on the attaching point backwards to meet it at zero. -/
private def joinedLine : C(ℝ × X.carrier, Z.carrier) where
  toFun p := if p.1 ≤ 0 then K (projIcc 0 1 zero_le_one (-p.1), f p.2)
    else h (line f (projIcc 0 1 zero_le_one p.1, p.2))
  continuous_toFun := Continuous.if_le (by fun_prop) (by fun_prop) continuous_fst continuous_const
    fun p hp ↦ by simp [hp]

private lemma joinedLine_neg (t : I) (x : X.carrier) : joinedLine f h K (-t, x) = K (t, f x) := by
  simp [joinedLine, t.property.1]

private lemma joinedLine_pos (s : I) (x : X.carrier) :
    joinedLine f h K (s, x) = h (line f (s, x)) := by
  by_cases hs : s = 0
  · subst s
    simp [joinedLine]
  · have hs' : 0 < (s : ℝ) := unitInterval.coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hs)
    simp [joinedLine, hs'.not_ge]

private lemma joinedLine_basepoint (r : ℝ) : joinedLine f h K (r, X.basepoint) = Z.basepoint := by
  simp only [joinedLine, ContinuousMap.coe_mk, Hom.map_basepoint_apply, line_basepoint]
  split_ifs
  · exact (K.eq_snd _ (mem_singleton _)).trans g.map_basepoint
  · rfl

private abbrev trackSpace (Z : BasedTopologicalSpace.{u}) : BasedTopologicalSpace.{u} :=
  ⟨C(I, Z.carrier), .const _ Z.basepoint⟩

private def targetTrack : Hom Y (trackSpace Z) where
  toContinuousMap := (K.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  map_basepoint := ContinuousMap.ext fun t ↦ (K.eq_snd t (mem_singleton _)).trans g.map_basepoint

private lemma targetTrack_apply (y : Y.carrier) (t : I) :
    (targetTrack f h K).toContinuousMap y t = K (t, y) := by
  simp [targetTrack]

/-- At time `t`, stretch the cone coordinate `s` over the signed interval `[-t,1]`.
This leaves the apex fixed and runs the prescribed homotopy on the attaching face. -/
private def coneTrack : C(I × X.carrier, C(I, Z.carrier)) :=
  ((joinedLine f h K).comp
    (⟨fun p : (I × X.carrier) × I ↦
      ((p.1.1 : ℝ) - p.2 * (1 - p.1.1), p.1.2), by fun_prop⟩ : C(_, _))).curry

private lemma coneTrack_apply (s : I) (x : X.carrier) (t : I) :
    coneTrack f h K (s, x) t = joinedLine f h K ((s : ℝ) - t * (1 - s), x) := (rfl)

private def extensionTrack : Hom (reducedMappingCone f) (trackSpace Z) :=
  desc f (targetTrack f h K)
    { toContinuousMap := coneTrack f h K
      map_zero_left := fun x ↦ ContinuousMap.ext fun t ↦ by
        simpa [ContinuousMap.toFun_eq_coe, coneTrack_apply] using
          (joinedLine_neg f h K t x).trans (targetTrack_apply f h K (f x) t).symm
      map_one_left := fun x ↦ ContinuousMap.ext fun t ↦ by
        simpa only [ContinuousMap.toFun_eq_coe, coneTrack_apply, Icc.coe_one, sub_self, mul_zero,
          sub_zero, line_one, Hom.map_basepoint_apply, ContinuousMap.const_apply] using
          (joinedLine_pos f h K 1 x)
      prop' := fun s x hx ↦ by
        obtain rfl := mem_singleton_iff.1 hx
        exact ContinuousMap.ext fun t ↦ (joinedLine_basepoint f h K _).trans
          ((K.eq_snd t (by simp)).trans (by simp)).symm }

private lemma extensionTrack_incl (y : Y.carrier) (t : I) :
    extensionTrack f h K (incl f y) t = K (t, y) := by
  rw [extensionTrack, desc_incl, ← Hom.coe_toContinuousMap (targetTrack f h K), targetTrack_apply]

private lemma extensionTrack_zero (z : (reducedMappingCone f).carrier) :
    extensionTrack f h K z 0 = h z := by
  induction z using ind f with
  | target y =>
    rw [extensionTrack_incl, K.apply_zero, Hom.coe_toContinuousMap, Hom.comp_apply]
  | cone p =>
    obtain ⟨s, x⟩ := p
    rw [extensionTrack, desc_line]
    -- On a cone line the track is the signed-coordinate formula at time zero.
    change coneTrack f h K (s, x) 0 = _
    simpa only [coneTrack_apply, Icc.coe_zero, zero_mul, sub_zero] using
      (joinedLine_pos f h K s x)

/-- **Pointed homotopy extension along the target inclusion.** A pointed homotopy starting at
the restriction of `h` extends over the whole cone, agreeing at every time on the target. -/
theorem exists_homotopy_extension :
    ∃ (h' : Hom (reducedMappingCone f) Z)
      (L : h.toContinuousMap.HomotopyRel h'.toContinuousMap {(reducedMappingCone f).basepoint}),
      ∀ t y, L (t, incl f y) = K (t, y) := by
  let e := extensionTrack f h K
  let h' : Hom (reducedMappingCone f) Z :=
    ⟨⟨fun z ↦ e z 1, (continuous_eval_const _).comp e.toContinuousMap.continuous⟩,
      DFunLike.congr_fun e.map_basepoint 1⟩
  let L : h.toContinuousMap.HomotopyRel h'.toContinuousMap {(reducedMappingCone f).basepoint} :=
    { toContinuousMap := e.toContinuousMap.uncurry.comp ⟨Prod.swap, continuous_swap⟩
      map_zero_left := extensionTrack_zero f h K
      map_one_left := fun _ ↦ rfl
      prop' := fun t z hz ↦ by
        obtain rfl := mem_singleton_iff.1 hz
        exact (DFunLike.congr_fun e.map_basepoint t).trans h.map_basepoint.symm }
  exact ⟨h', L, fun t y ↦ extensionTrack_incl f h K y t⟩

/-- **Exactness at the mapping cone.** Up to pointed homotopy, a map on the cone factors
through the suspension precisely when its restriction to the target is pointed-nullhomotopic. -/
theorem exists_homotopicRel_comp_collapse_iff :
    (∃ d : Hom (reducedSuspension.obj X) Z,
      h.toContinuousMap.HomotopicRel (d.comp (collapse f)).toContinuousMap
        {(reducedMappingCone f).basepoint}) ↔
      (h.comp (incl f)).toContinuousMap.HomotopicRel (.const _ Z.basepoint) {Y.basepoint} := by
  constructor
  · rintro ⟨d, hd⟩
    have hr := (hd.precomp (incl f).toContinuousMap).mono (T := {Y.basepoint}) (by simp)
    have hc : (d.comp (collapse f)).toContinuousMap.comp (incl f).toContinuousMap =
        .const _ Z.basepoint := ContinuousMap.ext fun y ↦ by
      simp only [Hom.toContinuousMap_comp, ContinuousMap.comp_apply, Hom.coe_toContinuousMap,
        collapse_incl, Hom.map_basepoint_apply, ContinuousMap.const_apply]
    simpa only [Hom.toContinuousMap_comp, ← hc] using hr
  · rintro ⟨H⟩
    obtain ⟨h', L, hL⟩ := exists_homotopy_extension f h (g := ⟨.const _ Z.basepoint, rfl⟩) H
    have hy (y : Y.carrier) : h' (incl f y) = Z.basepoint :=
      (L.apply_one _).symm.trans ((hL 1 y).trans (H.apply_one y))
    let P := targetPair f
    let d := P.ordinaryPairQuotientDesc (_root_.TopCat.ofHom h'.toContinuousMap) Z.basepoint
      (fun ⟨_, y, hy'⟩ ↦ hy' ▸ hy y)
    let e := quotientTargetHomeomorph f
    let k : Hom (reducedSuspension.obj X) Z :=
      ⟨d.hom.comp (e.symm : C(ReducedSuspension X.carrier X.basepoint, P.ordinaryPairQuotient)),
        (congrArg d (quotientTargetHomeomorph_symm_basepoint f)).trans
          (P.ordinaryPairQuotientDesc_basepoint _ _ _)⟩
    refine ⟨k, ⟨L.cast rfl (ContinuousMap.ext fun z ↦ ?_)⟩⟩
    have hz := e.symm_apply_apply (P.ordinaryPairQuotientπ z)
    rw [quotientTargetHomeomorph_π] at hz
    rw [Hom.toContinuousMap_comp, ContinuousMap.comp_apply]
    exact ((congrArg d hz).trans (P.ordinaryPairQuotientπ_desc_apply _ _ _ z)).symm

end TauCeti.BasedTopologicalSpace.reducedMappingCone
