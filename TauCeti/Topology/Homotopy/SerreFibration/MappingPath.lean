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
homotopy equivalence. By the fibrewise five-lemma
(`TauCeti.TopCat.isWeakHomotopyEquivalence_fiberMap`), the induced map on every fibre is a weak
homotopy equivalence; identifying the endpoint fibre with `MappingPathFiber p b` shows that the
constant-path inclusion `MappingPathFiber.ofFiber p b : p⁻¹(b) → MappingPathFiber p b` is a weak
homotopy equivalence for every `b : B`, including when `p⁻¹(b)` is empty.

For Hurewicz fibrations between spaces in possibly distinct universes, lifting all spaces to a
common universe via `Homeomorph.ulift` transfers the Serre fibration square criterion
(`TauCeti.TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap`) without universe restrictions.

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_ofFiber`: for a Serre fibration `p : E ⟶ B`, the
  constant-path inclusion `p⁻¹(b) → MappingPathFiber p.hom b` is a weak homotopy equivalence for
  every `b : B`.
* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_ofFiber`: the corresponding statement for
  Hurewicz fibrations in arbitrary universes.
* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_sqFiberMap` and
  `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_fiberMap`: over a weak homotopy
  equivalence of bases (in particular over the identity), a map between Hurewicz fibrations in
  arbitrary universes is a weak homotopy equivalence if and only if it is one on every fibre.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval

universe u v u' v' w w'

namespace TauCeti

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
  have hincl : MappingPathSpace.incl p.hom = (MappingPathSpace.homotopyEquiv p.hom).toFun := by
    ext x : 1
    exact (MappingPathSpace.homotopyEquiv_apply p.hom x).symm
  have hf : (_root_.TopCat.ofHom (MappingPathSpace.incl p.hom)).hom.IsWeakHomotopyEquivalence := by
    change (MappingPathSpace.incl p.hom).IsWeakHomotopyEquivalence
    rw [hincl]
    exact (MappingPathSpace.homotopyEquiv p.hom).isWeakHomotopyEquivalence
  have hfib := isWeakHomotopyEquivalence_fiberMap hp hp' sq hf .id b
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
  have he : (eEnd : C((_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber ((𝟙 B) b),
      MappingPathFiber p.hom b)).IsWeakHomotopyEquivalence := by
    convert eEnd.toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext : 1
    rfl
  exact he.comp hfib

end TopCat

namespace IsHurewiczFibration

/-- For a Hurewicz fibration `p : C(E, B)` in arbitrary universes, the constant-path inclusion
`MappingPathFiber.ofFiber p b` is a weak homotopy equivalence for every `b : B`. -/
theorem isWeakHomotopyEquivalence_ofFiber {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
    (hp : IsHurewiczFibration.{w} p) (b : B) :
    (MappingPathFiber.ofFiber p b).IsWeakHomotopyEquivalence := by
  let eE : ULift.{v} E ≃ₜ E := Homeomorph.ulift
  let eB : ULift.{u} B ≃ₜ B := Homeomorph.ulift
  let pu : _root_.TopCat.of (ULift.{v} E) ⟶ _root_.TopCat.of (ULift.{u} B) :=
    _root_.TopCat.ofHom ((eB.symm : C(B, ULift.{u} B)).comp (p.comp (eE : C(ULift.{v} E, E))))
  have hpu : TopCat.serreFibrations pu :=
    (isHurewiczFibration_ulift_iff.mpr hp).mem_serreFibrations
  have hfib := TopCat.isWeakHomotopyEquivalence_ofFiber hpu (ULift.up b)
  let eDom : (pu ⁻¹' {ULift.up b}) ≃ₜ (p ⁻¹' {b}) :=
    { toFun x := ⟨x.1.down, congrArg ULift.down x.2⟩
      invFun x := ⟨ULift.up x.1, congrArg ULift.up x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eCod : MappingPathFiber pu.hom (ULift.up b) ≃ₜ MappingPathFiber p b :=
    { toFun q := ⟨(q.1.1.down, (eB : C(ULift.{u} B, B)).comp q.1.2),
        congrArg ULift.down q.2.1, congrArg ULift.down q.2.2⟩
      invFun q := ⟨(ULift.up q.1.1, (eB.symm : C(B, ULift.{u} B)).comp q.1.2),
        congrArg ULift.up q.2.1, congrArg ULift.up q.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := ((continuous_uliftDown.comp continuous_subtype_val.fst).prodMk
        ((ContinuousMap.continuous_postcomp _).comp continuous_subtype_val.snd)).subtype_mk _
      continuous_invFun := ((continuous_uliftUp.comp continuous_subtype_val.fst).prodMk
        ((ContinuousMap.continuous_postcomp _).comp continuous_subtype_val.snd)).subtype_mk _ }
  have heDom : (eDom.symm : C(p ⁻¹' {b}, pu ⁻¹' {ULift.up b})).IsWeakHomotopyEquivalence := by
    convert eDom.symm.toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext : 1; rfl
  have heCod : (eCod : C(MappingPathFiber pu.hom (ULift.up b),
      MappingPathFiber p b)).IsWeakHomotopyEquivalence := by
    convert eCod.toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext : 1; rfl
  have hcomp : MappingPathFiber.ofFiber p b =
      (eCod : C(MappingPathFiber pu.hom (ULift.up b), MappingPathFiber p b)).comp
        ((MappingPathFiber.ofFiber pu.hom (ULift.up b)).comp
          (eDom.symm : C(p ⁻¹' {b}, pu ⁻¹' {ULift.up b}))) := by
    ext x : 1
    apply Subtype.ext
    rw [MappingPathFiber.ofFiber_val]
    change (x.1, ContinuousMap.const I b) =
      ((MappingPathFiber.ofFiber pu.hom (ULift.up b) (eDom.symm x)).val.1.down,
        (eB : C(ULift.{u} B, B)).comp
          (MappingPathFiber.ofFiber pu.hom (ULift.up b) (eDom.symm x)).val.2)
    rw [MappingPathFiber.ofFiber_val]
    rfl
  rw [hcomp]
  exact heCod.comp (hfib.comp heDom)

section Square

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {p : C(E, B)} {p' : C(E', B')}

/-- Conjugating a map by homeomorphisms preserves and reflects weak homotopy equivalences. -/
private theorem isWeakHomotopyEquivalence_conj_iff {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (eX : X' ≃ₜ X) (eY : Y' ≃ₜ Y) (φ : C(X, Y)) :
    ((eY.symm : C(Y, Y')).comp (φ.comp (eX : C(X', X)))).IsWeakHomotopyEquivalence ↔
      φ.IsWeakHomotopyEquivalence := by
  have heX : (eX : C(X', X)).IsWeakHomotopyEquivalence := by
    convert eX.toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext : 1
    rfl
  have heY : (eY.symm : C(Y, Y')).IsWeakHomotopyEquivalence := by
    convert eY.symm.toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext : 1
    rfl
  exact ⟨fun h ↦ heX.of_precomp (heY.of_postcomp h),
    fun h ↦ heY.comp (h.comp heX)⟩

/-- **Fibrewise weak-equivalence criterion for Hurewicz fibrations in arbitrary universes.** Given a
commutative square `p' ∘ f = g ∘ p` of Hurewicz fibrations whose base map `g` is a weak homotopy
equivalence, `f` is a weak homotopy equivalence if and only if the induced map `p⁻¹(b) → p'⁻¹(g b)`
is a weak homotopy equivalence for every `b : B`. -/
theorem isWeakHomotopyEquivalence_iff_forall_sqFiberMap
    (hp : IsHurewiczFibration.{w} p) (hp' : IsHurewiczFibration.{w'} p')
    {f : C(E, E')} {g : C(B, B')} (h : p'.comp f = g.comp p)
    (hg : g.IsWeakHomotopyEquivalence) :
    f.IsWeakHomotopyEquivalence ↔
      ∀ b : B, (sqFiberMap f g h b).IsWeakHomotopyEquivalence := by
  let eE : ULift.{max v (max u' v')} E ≃ₜ E := Homeomorph.ulift
  let eB : ULift.{max u (max u' v')} B ≃ₜ B := Homeomorph.ulift
  let eE' : ULift.{max (max u v) v'} E' ≃ₜ E' := Homeomorph.ulift
  let eB' : ULift.{max (max u v) u'} B' ≃ₜ B' := Homeomorph.ulift
  let pu : _root_.TopCat.of (ULift.{max v (max u' v')} E) ⟶
      _root_.TopCat.of (ULift.{max u (max u' v')} B) :=
    _root_.TopCat.ofHom ((eB.symm : C(B, _)).comp (p.comp (eE : C(_, E))))
  let p'u : _root_.TopCat.of (ULift.{max (max u v) v'} E') ⟶
      _root_.TopCat.of (ULift.{max (max u v) u'} B') :=
    _root_.TopCat.ofHom ((eB'.symm : C(B', _)).comp (p'.comp (eE' : C(_, E'))))
  let fu : _root_.TopCat.of (ULift.{max v (max u' v')} E) ⟶
      _root_.TopCat.of (ULift.{max (max u v) v'} E') :=
    _root_.TopCat.ofHom ((eE'.symm : C(E', _)).comp (f.comp (eE : C(_, E))))
  let gu : _root_.TopCat.of (ULift.{max u (max u' v')} B) ⟶
      _root_.TopCat.of (ULift.{max (max u v) u'} B') :=
    _root_.TopCat.ofHom ((eB'.symm : C(B', _)).comp (g.comp (eB : C(_, B))))
  have hpu : TopCat.serreFibrations pu :=
    (isHurewiczFibration_ulift_iff.mpr hp).mem_serreFibrations
  have hp'u : TopCat.serreFibrations p'u :=
    (isHurewiczFibration_ulift_iff.mpr hp').mem_serreFibrations
  have sq : CommSq fu pu p'u gu := ⟨_root_.TopCat.ext fun x ↦
    congrArg ULift.up (ContinuousMap.congr_fun h x.down)⟩
  have hgu : gu.hom.IsWeakHomotopyEquivalence :=
    (isWeakHomotopyEquivalence_conj_iff eB eB' g).mpr hg
  have hfib_iff (b : B) :
      (sq.fiberMap (ULift.up b)).hom.IsWeakHomotopyEquivalence ↔
        (sqFiberMap f g h b).IsWeakHomotopyEquivalence := by
    let eFib : pu.fiber (ULift.up b) ≃ₜ (p ⁻¹' {b}) :=
      { toFun x := ⟨x.1.down, congrArg ULift.down x.2⟩
        invFun x := ⟨ULift.up x.1, congrArg ULift.up x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _ }
    let eFib' : p'u.fiber (gu (ULift.up b)) ≃ₜ (p' ⁻¹' {g b}) :=
      { toFun x := ⟨x.1.down, congrArg ULift.down x.2⟩
        invFun x := ⟨ULift.up x.1, congrArg ULift.up x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _ }
    have hconj : (sq.fiberMap (ULift.up b)).hom =
        (eFib'.symm : C(_, _)).comp ((sqFiberMap f g h b).comp (eFib : C(_, _))) := by
      ext x : 1
      apply Subtype.ext
      refine (sq.fiberMap_apply_coe (ULift.up b) x).trans ?_
      exact congrArg ULift.up
        (coe_sqFiberMap f g h b ⟨x.1.down, congrArg ULift.down x.2⟩).symm
    rw [hconj]
    exact isWeakHomotopyEquivalence_conj_iff eFib eFib' (sqFiberMap f g h b)
  rw [← isWeakHomotopyEquivalence_conj_iff eE eE' f]
  exact (TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap hpu hp'u sq hgu).trans
    ⟨fun hfib b ↦ (hfib_iff b).mp (hfib (ULift.up b)),
      fun hfib bu ↦ (hfib_iff bu.down).mpr (hfib bu.down)⟩

/-- Over a common base `B`, a map `f` between Hurewicz fibrations `p : C(E, B)` and `q : C(E', B)`
is a weak homotopy equivalence if and only if `fiberMap f hf b` is one for every `b : B`. -/
theorem isWeakHomotopyEquivalence_iff_forall_fiberMap {q : C(E', B)}
    (hp : IsHurewiczFibration.{w} p) (hq : IsHurewiczFibration.{w'} q)
    {f : C(E, E')} (hf : q.comp f = p) :
    f.IsWeakHomotopyEquivalence ↔ ∀ b : B, (fiberMap f hf b).IsWeakHomotopyEquivalence := by
  have heq (b : B) : fiberMap f hf b =
      sqFiberMap f (.id B) (hf.trans (ContinuousMap.id_comp p).symm) b := by
    ext e : 1
    apply Subtype.ext
    exact (coe_fiberMap f hf b e).trans (coe_sqFiberMap f (.id B) _ b e).symm
  simp_rw [heq]
  exact hp.isWeakHomotopyEquivalence_iff_forall_sqFiberMap hq
    (hf.trans (ContinuousMap.id_comp p).symm) .id

end Square

end IsHurewiczFibration

end TauCeti
