/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.MappingPath
public import TauCeti.Topology.Homotopy.HurewiczFibration.Universe
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Strict fibres and mapping-path fibres of Serre fibrations

Every map `p : E → B` factors through its mapping-path replacement `MappingPathSpace p` as the
homotopy equivalence `MappingPathSpace.incl p` followed by the Hurewicz fibration
`MappingPathSpace.endpoint p`. When `p` is a Serre fibration in `TopCat`, this factorization is a
commutative square of Serre fibrations over the identity of `B` whose map of total spaces is a weak
homotopy equivalence. By `TauCeti.TopCat.isWeakHomotopyEquivalence_fiberMap`, the induced map on
every fibre is a weak homotopy equivalence; identifying the endpoint fibre with
`MappingPathFiber p b` shows that `MappingPathFiber.ofFiber p b : p⁻¹(b) → MappingPathFiber p b` is
a weak homotopy equivalence for every `b : B`, including when `p⁻¹(b)` is empty.

For Hurewicz fibrations over a common base in possibly distinct universes, lifting all three spaces
to a common universe via `Homeomorph.ulift` transfers the fibrewise weak-equivalence criterion
`TauCeti.TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap` without universe restrictions.

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_ofFiber`: for a Serre fibration `p : E ⟶ B`, the
  constant-path inclusion `p⁻¹(b) → MappingPathFiber p.hom b` is a weak homotopy equivalence for
  every `b : B`.
* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_fiberMap`: over a common base
  `B`, a map between Hurewicz fibrations in arbitrary universes is a weak homotopy equivalence if
  and only if `fiberMap f hf b` is one for every `b : B`.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval

universe u v u' w w'

namespace TauCeti

/-- `MappingPathSpace.incl` is a weak homotopy equivalence. -/
theorem MappingPathSpace.isWeakHomotopyEquivalence_incl {B : Type u} {K : Type v}
    [TopologicalSpace B] [TopologicalSpace K] (f : C(B, K)) :
    (MappingPathSpace.incl f).IsWeakHomotopyEquivalence := by
  convert (MappingPathSpace.homotopyEquiv f).isWeakHomotopyEquivalence using 1
  ext x : 1
  exact (MappingPathSpace.homotopyEquiv_apply f x).symm

namespace TopCat

/-- **Strict-to-homotopy fibre comparison for Serre fibrations.** For a Serre fibration
`p : E ⟶ B` and any point `b : B` (including when the fibre over `b` is empty), the constant-path
inclusion `MappingPathFiber.ofFiber p.hom b` from the strict fibre `p ⁻¹' {b}` to the mapping-path
fibre `MappingPathFiber p.hom b` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofFiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (b : B) :
    (MappingPathFiber.ofFiber p.hom b).IsWeakHomotopyEquivalence := by
  let sq : CommSq (_root_.TopCat.ofHom (MappingPathSpace.incl p.hom)) p
      (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)) (𝟙 B) :=
    ⟨_root_.TopCat.ext fun x ↦
      ContinuousMap.congr_fun (MappingPathSpace.endpoint_comp_incl p.hom) x⟩
  have hp' : serreFibrations (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)) :=
    (MappingPathSpace.isHurewiczFibration_endpoint.{0} p.hom).mem_serreFibrations
  let eEnd : (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber ((𝟙 B) b) ≃ₜ
      MappingPathFiber p.hom b :=
    { toFun y := ⟨y.1.val, y.1.property, by simpa [MappingPathSpace.endpoint_apply] using y.2⟩
      invFun z := ⟨⟨z.val, z.property.1⟩,
        by simpa [MappingPathSpace.endpoint_apply] using z.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hcomp : (eEnd : C((_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber ((𝟙 B) b),
      MappingPathFiber p.hom b)).comp (sq.fiberMap b).hom =
      MappingPathFiber.ofFiber p.hom b := by
    ext x : 1
    apply Subtype.ext
    change (sq.fiberMap b x : (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber _).1.val
      = (MappingPathFiber.ofFiber p.hom b x).val
    rw [show (sq.fiberMap b x : (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber _).1 =
        MappingPathSpace.incl p.hom x.1 from sq.fiberMap_apply_coe b x,
      MappingPathSpace.incl_val]
    exact (congrArg (x.1, ContinuousMap.const I ·) x.2).trans
      (MappingPathFiber.ofFiber_val p.hom b x).symm
  rw [← hcomp]
  exact eEnd.isWeakHomotopyEquivalence.comp
    (isWeakHomotopyEquivalence_fiberMap hp hp' sq
      (MappingPathSpace.isWeakHomotopyEquivalence_incl p.hom) .id b)

end TopCat

namespace IsHurewiczFibration

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
      { toFun x := ⟨x.1.down, congrArg ULift.down x.2⟩
        invFun x := ⟨ULift.up x.1, congrArg ULift.up x.2⟩
        left_inv _ := rfl, right_inv _ := rfl
        continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _ }
    let eqFib : {e' : E' // q e' = b} ≃ₜ
        qu.fiber ((𝟙 (_root_.TopCat.of (ULift.{max u u'} B))) (ULift.up b)) :=
      { toFun x := ⟨ULift.up x.1, congrArg ULift.up x.2⟩
        invFun x := ⟨x.1.down, congrArg ULift.down x.2⟩
        left_inv _ := rfl, right_inv _ := rfl
        continuous_toFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _ }
    have hconj : (sq.fiberMap (ULift.up b)).hom =
        (eqFib : C(_, _)).comp ((fiberMap f hf b).comp (epFib : C(_, _))) := by
      ext x : 1; apply Subtype.ext
      exact (sq.fiberMap_apply_coe (ULift.up b) x).trans
        (congrArg ULift.up (coe_fiberMap f hf b (epFib x))).symm
    rw [hconj]
    exact Homeomorph.isWeakHomotopyEquivalence_conj_iff epFib eqFib (fiberMap f hf b)
  rw [← Homeomorph.isWeakHomotopyEquivalence_conj_iff eE eE'.symm f]
  exact (TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap hpu hqu sq .id).trans
    ⟨fun h b ↦ (hfib b).mp (h (ULift.up b)), fun h bu ↦ (hfib bu.down).mpr (h bu.down)⟩

end IsHurewiczFibration

end TauCeti
