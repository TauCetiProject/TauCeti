/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.Homotopy.HurewiczFibration.Universe
public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction
public import TauCeti.Topology.Homotopy.MappingPath.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Fibrewise weak homotopy equivalences between Hurewicz fibrations

For Hurewicz fibrations `p : C(E, B)` and `q : C(E', B)` over a common base `B` in possibly
distinct universes, lifting all three spaces to a common universe via `Homeomorph.ulift` transfers
the Serre-fibration fibrewise weak-equivalence criterion
`TauCeti.TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap` without universe restrictions.
Applying this to the mapping-path replacement `MappingPathSpace.incl p` yields the
strict-to-homotopy fibre weak homotopy equivalence `MappingPathFiber.ofFiber p b` across arbitrary
universes.

## Main results

* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_fiberMap`: over a common base
  `B`, a map `f` between Hurewicz fibrations in arbitrary universes is a weak homotopy equivalence
  if and only if `TauCeti.fiberMap f hf b` is one for every `b : B`.
* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_ofFiber`: for a Hurewicz fibration `p` in
  arbitrary universes, the constant-path inclusion `MappingPathFiber.ofFiber p b` is a weak
  homotopy equivalence for every `b : B`.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory

universe u u' v w w'

namespace TauCeti.IsHurewiczFibration

/-- Over a common base `B`, a map `f` between Hurewicz fibrations `p : C(E, B)` and `q : C(E', B)`
in arbitrary universes is a weak homotopy equivalence if and only if `fiberMap f hf b` is one for
every `b : B`. -/
theorem isWeakHomotopyEquivalence_iff_forall_fiberMap {E : Type u} {E' : Type u'} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] {p : C(E, B)} {q : C(E', B)}
    (hp : IsHurewiczFibration.{w} p) (hq : IsHurewiczFibration.{w'} q)
    {f : C(E, E')} (hf : q.comp f = p) :
    f.IsWeakHomotopyEquivalence ↔ ∀ b : B, (fiberMap f hf b).IsWeakHomotopyEquivalence := by
  let eE : ULift.{max u' v} E ≃ₜ E := Homeomorph.ulift
  let eE' : ULift.{max u v} E' ≃ₜ E' := Homeomorph.ulift
  let pu : _root_.TopCat.of (ULift.{max u' v} E) ⟶ _root_.TopCat.of (ULift.{max u u'} B) :=
    _root_.TopCat.ofHom ⟨fun e ↦ ULift.up (p e.down),
      continuous_uliftUp.comp (p.continuous.comp continuous_uliftDown)⟩
  let qu : _root_.TopCat.of (ULift.{max u v} E') ⟶ _root_.TopCat.of (ULift.{max u u'} B) :=
    _root_.TopCat.ofHom ⟨fun e ↦ ULift.up (q e.down),
      continuous_uliftUp.comp (q.continuous.comp continuous_uliftDown)⟩
  let fu : _root_.TopCat.of (ULift.{max u' v} E) ⟶ _root_.TopCat.of (ULift.{max u v} E') :=
    _root_.TopCat.ofHom ((eE'.symm : C(E', _)).comp (f.comp (eE : C(_, E))))
  have hpu : TopCat.serreFibrations pu := (isHurewiczFibration_ulift_iff.mpr hp).mem_serreFibrations
  have hqu : TopCat.serreFibrations qu := (isHurewiczFibration_ulift_iff.mpr hq).mem_serreFibrations
  have sq : CommSq fu pu qu (𝟙 _) := ⟨_root_.TopCat.ext fun x ↦
    congrArg ULift.up (ContinuousMap.congr_fun hf x.down)⟩
  have hfib (b : B) : (sq.fiberMap (ULift.up b)).hom.IsWeakHomotopyEquivalence ↔
      (fiberMap f hf b).IsWeakHomotopyEquivalence := by
    let epFib : pu.fiber (ULift.up b) ≃ₜ {e : E // p e = b} :=
      eE.subtype fun _ ↦ ULift.up_inj
    let eqFib : {e' : E' // q e' = b} ≃ₜ
        qu.fiber ((𝟙 (_root_.TopCat.of (ULift.{max u u'} B))) (ULift.up b)) :=
      eE'.symm.subtype fun _ ↦ ULift.up_inj.symm
    have hconj : (sq.fiberMap (ULift.up b)).hom =
        (eqFib : C(_, _)).comp ((fiberMap f hf b).comp (epFib : C(_, _))) := by
      ext x : 1; apply Subtype.ext
      refine (sq.fiberMap_apply_coe (ULift.up b) x).trans ?_
      simp only [fu, _root_.TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_apply]
      exact (congrArg (fun y ↦ eE'.symm (f y))
          (Homeomorph.subtype_apply_coe (h := eE) _ x).symm).trans <|
        (congrArg eE'.symm (coe_fiberMap f hf b (epFib x)).symm).trans
          (Homeomorph.subtype_apply_coe (h := eE'.symm) _ (fiberMap f hf b (epFib x))).symm
    rw [hconj]
    exact Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff epFib eqFib (fiberMap f hf b)
  rw [← Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff eE eE'.symm f]
  exact (TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap hpu hqu sq .id).trans
    ⟨fun h b ↦ (hfib b).mp (h (ULift.up b)), fun h bu ↦ (hfib bu.down).mpr (h bu.down)⟩

/-- **Strict-to-homotopy fibre comparison for Hurewicz fibrations.** For a Hurewicz fibration
`p : C(E, B)` in arbitrary universes and any point `b : B` (including when `p ⁻¹' {b}` is empty),
the constant-path inclusion `MappingPathFiber.ofFiber p b` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofFiber {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)} (hp : IsHurewiczFibration.{w} p)
    (b : B) : (MappingPathFiber.ofFiber p b).IsWeakHomotopyEquivalence := by
  have hfib := (hp.isWeakHomotopyEquivalence_iff_forall_fiberMap
    (MappingPathSpace.isHurewiczFibration_endpoint.{0} p)
    (MappingPathSpace.endpoint_comp_incl p)).mp
      (MappingPathSpace.isWeakHomotopyEquivalence_incl p) b
  have hcomp :
      (MappingPathFiber.endpointHomeomorph p b : C(_, _)).comp (MappingPathFiber.ofFiber p b) =
        fiberMap (MappingPathSpace.incl p) (MappingPathSpace.endpoint_comp_incl p) b := by
    ext x : 1; apply Subtype.ext
    rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply]
    exact (MappingPathFiber.endpointHomeomorph_ofFiber_val p b x).trans
      (coe_fiberMap (MappingPathSpace.incl p) (MappingPathSpace.endpoint_comp_incl p) b x).symm
  exact (MappingPathFiber.endpointHomeomorph p b).isWeakHomotopyEquivalence.of_postcomp
    (hcomp.symm ▸ hfib)

end TauCeti.IsHurewiczFibration
