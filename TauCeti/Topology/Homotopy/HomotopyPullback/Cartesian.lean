/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyPullback.Basic
public import TauCeti.Topology.Homotopy.HurewiczFibration.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.MappingPath.Homotopy
public import TauCeti.Topology.Homotopy.SerreFibration.MappingPath

/-!
# Homotopy-cartesian squares and fibration pullbacks

A homotopy-commutative square `H : (p.comp α).Homotopy (h.comp p')` (`E' → E` over `B' → B`)
is **homotopy-cartesian** (`ContinuousMap.Homotopy.IsHomotopyCartesian`) when
`HomotopyPullback.lift α p' H : C(E', HomotopyPullback p h)` is a weak homotopy equivalence; strict
squares (`TauCeti.IsHomotopyCartesian`, `CategoryTheory.CommSq.IsHomotopyCartesian`) specialize via
`HomotopyPullback.liftStrict`.

Factoring `lift α p' H` up to homotopy through `MappingPathSpace p'` yields a map over `B'` between
Hurewicz fibrations, showing across arbitrary universes that `H` is homotopy-cartesian iff
`H.mappingPathFiberSqMap b' : MappingPathFiber p' b' → MappingPathFiber p (h b')` is a weak
homotopy equivalence for every `b' : B'`. From this we deduce homotopy base change of weak homotopy
equivalences and strict-vs.-homotopy pullback comparisons along Hurewicz and Serre fibrations.

## Main declarations

* `ContinuousMap.Homotopy.IsHomotopyCartesian`, `TauCeti.IsHomotopyCartesian`,
  `CategoryTheory.CommSq.IsHomotopyCartesian`: homotopy-cartesian squares.
* `ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber`,
  `TauCeti.isHomotopyCartesian_iff_forall_mappingPathFiber`,
  `TauCeti.isHomotopyCartesian_fiber_iff_ofFiber`: mapping-path fibre criteria.
* `TauCeti.HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_top_of_bot`: homotopy base change of weak
  homotopy equivalences.
* `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_ofPullback_left`,
  `TauCeti.TopCat.isWeakHomotopyEquivalence_ofPullback_of_left`,
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_forall_fiberMap`,
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_lift`,
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_pullbackLift_of_right`,
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_pullbackLift_of_bot`,
  `CategoryTheory.IsPullback.isHomotopyCartesian_of_right`,
  `CategoryTheory.IsPullback.isHomotopyCartesian_of_bot`: Hurewicz and Serre fibration squares.

## References

* M. Mather, *Pull-backs in homotopy theory*, Canadian Journal of Mathematics 28 (1976), 225–263.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval

universe u v u' v'

namespace TauCeti.HomotopyPullback

variable {A : Type u} {B : Type v} {C : Type u'}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- `HomotopyPullback.swap` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_swap (f : C(A, B)) (g : C(C, B)) :
    (swap f g).IsWeakHomotopyEquivalence :=
  coe_swapHomeomorph f g ▸ (swapHomeomorph f g).isWeakHomotopyEquivalence

/-- Swapping the two legs preserves and reflects whether `HomotopyPullback.ofPullback` is a weak
homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_comm_iff (f : C(A, B)) (g : C(C, B)) :
    (ofPullback g f).IsWeakHomotopyEquivalence ↔ (ofPullback f g).IsWeakHomotopyEquivalence := by
  rw [← Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff (Homeomorph.pullbackComm ⇑f ⇑g)
    (swapHomeomorph g f) (ofPullback g f), coe_swapHomeomorph,
    swap_comp_ofPullback_comp_pullbackComm]

/-- **Homotopy base change preserves weak homotopy equivalences (right leg).** If `g : C(C, B)` is
a weak homotopy equivalence, then for any continuous map `f : C(A, B)` the projection
`fst f g : C(HomotopyPullback f g, A)` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_fst_of_right (f : C(A, B)) {g : C(C, B)}
    (hg : g.IsWeakHomotopyEquivalence) : (fst f g).IsWeakHomotopyEquivalence := by
  have hend : (MappingPathSpace.endpoint g).IsWeakHomotopyEquivalence :=
    (MappingPathSpace.isWeakHomotopyEquivalence_incl g).of_precomp
      (by rwa [MappingPathSpace.endpoint_comp_incl])
  have hend_fib := ((MappingPathSpace.isHurewiczFibration_endpoint g :
      IsHurewiczFibration.{0} _).isWeakHomotopyEquivalence_iff_forall_fiberMap
    ((Homeomorph.refl B).isHurewiczFibration : IsHurewiczFibration.{0} _)
    (ContinuousMap.id_comp _)).mp hend
  rw [(isHurewiczFibration_fst f g :
      IsHurewiczFibration.{0} _).isWeakHomotopyEquivalence_iff_forall_fiberMap
    ((Homeomorph.refl A).isHurewiczFibration : IsHurewiczFibration.{0} _)
    (ContinuousMap.id_comp _)]
  intro a
  let eDom : {e // MappingPathSpace.endpoint g e = f a} ≃ₜ {e // fst f g e = a} :=
    (MappingPathFiber.endpointHomeomorph g (f a)).symm.trans (fstFiberHomeomorph f g a).symm
  let : Unique {e // ContinuousMap.id A e = a} := Unique.subtypeEq a
  let : Unique {e // ContinuousMap.id B e = f a} := Unique.subtypeEq (f a)
  let eCod : {e // ContinuousMap.id A e = a} ≃ₜ {e // ContinuousMap.id B e = f a} :=
    Homeomorph.homeomorphOfUnique _ _
  have hconj : (eCod : C(_, _)).comp
      ((fiberMap (fst f g) (ContinuousMap.id_comp _) a).comp (eDom : C(_, _))) =
      fiberMap (MappingPathSpace.endpoint g) (ContinuousMap.id_comp _) (f a) :=
    ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _
  exact (Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff eDom eCod _).mp
    (hconj ▸ hend_fib (f a))

/-- **Homotopy base change preserves weak homotopy equivalences (left leg).** If `f : C(A, B)` is
a weak homotopy equivalence, then for any continuous map `g : C(C, B)` the projection
`snd f g : C(HomotopyPullback f g, C)` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_snd_of_left {f : C(A, B)} (hf : f.IsWeakHomotopyEquivalence)
    (g : C(C, B)) : (snd f g).IsWeakHomotopyEquivalence := by
  rw [← fst_comp_swap f g]
  exact (isWeakHomotopyEquivalence_fst_of_right g hf).comp (isWeakHomotopyEquivalence_swap f g)

end TauCeti.HomotopyPullback

/-! ### Homotopy-cartesian squares -/

namespace ContinuousMap.Homotopy

open TauCeti

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- A homotopy-commutative square `H : (p.comp α).Homotopy (h.comp p')` is
**homotopy-cartesian** if the induced map
`HomotopyPullback.lift α p' H : C(E', HomotopyPullback p h)` is a weak homotopy equivalence. -/
def IsHomotopyCartesian (H : (p.comp α).Homotopy (h.comp p')) : Prop :=
  (HomotopyPullback.lift α p' H).IsWeakHomotopyEquivalence

theorem isHomotopyCartesian_iff (H : (p.comp α).Homotopy (h.comp p')) :
    H.IsHomotopyCartesian ↔ (HomotopyPullback.lift α p' H).IsWeakHomotopyEquivalence := Iff.rfl

/-- Reversing the square `H` swaps the two legs of `HomotopyPullback p h` via `swapHomeomorph`, so
`H.symm` is homotopy-cartesian when `H` is. -/
theorem IsHomotopyCartesian.symm {H : (p.comp α).Homotopy (h.comp p')}
    (hH : H.IsHomotopyCartesian) : H.symm.IsHomotopyCartesian := by
  rw [IsHomotopyCartesian, ← HomotopyPullback.swap_comp_lift α p' H]
  exact (HomotopyPullback.isWeakHomotopyEquivalence_swap p h).comp hH

theorem isHomotopyCartesian_symm_iff (H : (p.comp α).Homotopy (h.comp p')) :
    H.symm.IsHomotopyCartesian ↔ H.IsHomotopyCartesian :=
  ⟨fun hH ↦ by simpa using hH.symm, IsHomotopyCartesian.symm⟩

/-! ### Mapping-path fibre characterization -/

/-- The map over `B'` from `MappingPathSpace p'` to `HomotopyPullback p h` induced by
`H : (p.comp α).Homotopy (h.comp p')`, sending `(e', γ')` with `γ' 0 = p' e'` to
`(α e', γ' 1, (H.evalAt e').trans (γ'.map h))`. -/
private noncomputable def mappingPathReplacementLift (H : (p.comp α).Homotopy (h.comp p')) :
    C(MappingPathSpace p', HomotopyPullback p h) where
  toFun q := ⟨(α q.val.1, q.val.2 1,
    ((H.evalAt q.val.1).trans ((⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map
      h.continuous)).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun := by
    refine ((α.continuous.comp continuous_subtypeVal.fst).prodMk <|
      (continuous_subtypeVal.snd.eval continuous_const).prodMk ?_).subtype_mk _
    exact ContinuousMap.continuous_of_continuous_uncurry _ <| Path.trans_continuous_family
      (fun q : MappingPathSpace p' ↦ H.evalAt q.val.1)
      (H.continuous.comp (continuous_snd.prodMk (continuous_subtypeVal.fst.comp continuous_fst)))
      (fun q : MappingPathSpace p' ↦
        (⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map h.continuous)
      (h.continuous.comp ((continuous_subtypeVal.snd.comp continuous_fst).eval continuous_snd))

private theorem mappingPathReplacementLift_val (H : (p.comp α).Homotopy (h.comp p'))
    (q : MappingPathSpace p') :
    (H.mappingPathReplacementLift q).val = (α q.val.1, q.val.2 1,
      ((H.evalAt q.val.1).trans ((⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map
        h.continuous)).toContinuousMap) := (rfl)

private theorem snd_comp_mappingPathReplacementLift (H : (p.comp α).Homotopy (h.comp p')) :
    (HomotopyPullback.snd p h).comp H.mappingPathReplacementLift =
      MappingPathSpace.endpoint p' := by ext : 1; simp [mappingPathReplacementLift_val]

/-- Precomposing `H.mappingPathReplacementLift` with `MappingPathSpace.incl p'` appends a constant
path to `H.evalAt e'`, so it is homotopic to `HomotopyPullback.lift α p' H`. -/
private theorem lift_homotopic_mappingPathReplacementLift_comp_incl
    (H : (p.comp α).Homotopy (h.comp p')) :
    (HomotopyPullback.lift α p' H).Homotopic
      (H.mappingPathReplacementLift.comp (MappingPathSpace.incl p')) := by
  let φ : I → I := fun t ↦
    ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩
  have hφ : Continuous φ := by fun_prop
  have hφ₀ : φ 0 = 0 := Subtype.ext Path.Homotopy.transReflReparamAux_zero
  have hφ₁ : φ 1 = 1 := Subtype.ext Path.Homotopy.transReflReparamAux_one
  refine ⟨{
    toFun q := ⟨(α q.2, p' q.2,
      ((Path.Homotopy.reparam (H.evalAt q.2) φ hφ hφ₀ hφ₁).eval q.1).toContinuousMap),
      Path.source _, Path.target _⟩
    continuous_toFun := by
      refine ((α.continuous.comp continuous_snd).prodMk <|
        (p'.continuous.comp continuous_snd).prodMk ?_).subtype_mk _
      exact ContinuousMap.continuous_of_continuous_uncurry _ <|
        Path.reparamHomotopy_continuous_family (fun q : I × E' ↦ H.evalAt q.2)
          (H.continuous.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
          continuous_fst hφ hφ₀ hφ₁
    map_zero_left e' := HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp
    map_one_left e' := HomotopyPullback.ext
      (by simp [mappingPathReplacementLift_val])
      (by simp [mappingPathReplacementLift_val]) fun t ↦ by
        have h1 : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1 =
            (H.evalAt e').trans (.refl (h (p' e'))) :=
          (by simp : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1 =
            (H.evalAt e').reparam φ hφ hφ₀ hφ₁).trans
            (Path.Homotopy.trans_refl_reparam (H.evalAt e')).symm
        simp [HomotopyPullback.pathMap_apply, mappingPathReplacementLift_val, h1,
          Path.trans_apply] }⟩

/-- **Mapping-path fibre characterization of homotopy-cartesian squares.** A homotopy-commutative
square `H : (p.comp α).Homotopy (h.comp p')` between spaces in arbitrary universes is
homotopy-cartesian if and only if, for every `b' : B'`, the induced map
`H.mappingPathFiberSqMap b' : MappingPathFiber p' b' → MappingPathFiber p (h b')` on mapping-path
fibres is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_forall_mappingPathFiber (H : (p.comp α).Homotopy (h.comp p')) :
    H.IsHomotopyCartesian ↔
      ∀ b' : B', (H.mappingPathFiberSqMap b').IsWeakHomotopyEquivalence := by
  have hrep : H.IsHomotopyCartesian ↔ H.mappingPathReplacementLift.IsWeakHomotopyEquivalence := by
    rw [isHomotopyCartesian_iff, ← (MappingPathSpace.isWeakHomotopyEquivalence_incl p').precomp_iff]
    exact ⟨fun hH ↦ hH.of_homotopic H.lift_homotopic_mappingPathReplacementLift_comp_incl,
      fun hΦ ↦ hΦ.of_homotopic H.lift_homotopic_mappingPathReplacementLift_comp_incl.symm⟩
  rw [hrep, (MappingPathSpace.isHurewiczFibration_endpoint p' :
      IsHurewiczFibration.{0} _).isWeakHomotopyEquivalence_iff_forall_fiberMap
    (HomotopyPullback.isHurewiczFibration_snd p h : IsHurewiczFibration.{0} _)
    H.snd_comp_mappingPathReplacementLift]
  refine forall_congr' fun b' ↦ ?_
  let eX : MappingPathFiber p' b' ≃ₜ {e // MappingPathSpace.endpoint p' e = b'} :=
    MappingPathFiber.endpointHomeomorph p' b'
  let eY : {e' // HomotopyPullback.snd p h e' = b'} ≃ₜ MappingPathFiber p (h b') :=
    HomotopyPullback.sndFiberHomeomorph p h b'
  have hconj : H.mappingPathFiberSqMap b' = (eY : C(_, _)).comp
      ((fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b').comp
        (eX : C(_, _))) := by
    ext q : 1; apply Subtype.ext
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, eY]
    refine Eq.trans ?_ (HomotopyPullback.sndFiberHomeomorph_val p h b' _).symm
    refine Prod.ext (by simp [eX, mappingPathReplacementLift_val]) ?_
    ext t : 1; simp [eX, mappingPathReplacementLift_val, Path.trans_apply]
  rw [hconj]
  exact (Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff eX eY _).symm

/-- When the bottom map `h : C(B', B)` of `H : (p.comp α).Homotopy (h.comp p')` is a weak homotopy
equivalence, the square is homotopy-cartesian if and only if the top map `α : C(E', E)` is a weak
homotopy equivalence. -/
theorem isHomotopyCartesian_iff_top_of_bot (H : (p.comp α).Homotopy (h.comp p'))
    (hh : h.IsWeakHomotopyEquivalence) : H.IsHomotopyCartesian ↔ α.IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff,
    ← (HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right p hh).postcomp_iff,
    HomotopyPullback.fst_comp_lift]

/-- When the right vertical map `p : C(E, B)` of `H : (p.comp α).Homotopy (h.comp p')` is a weak
homotopy equivalence, the square is homotopy-cartesian if and only if the left vertical map
`p' : C(E', B')` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_left_of_right (H : (p.comp α).Homotopy (h.comp p'))
    (hp : p.IsWeakHomotopyEquivalence) : H.IsHomotopyCartesian ↔ p'.IsWeakHomotopyEquivalence := by
  rw [← isHomotopyCartesian_symm_iff]; exact H.symm.isHomotopyCartesian_iff_top_of_bot hp

/-- A homotopy-commutative square whose horizontal maps are weak homotopy equivalences is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_horiz (H : (p.comp α).Homotopy (h.comp p'))
    (hα : α.IsWeakHomotopyEquivalence) (hh : h.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian := (H.isHomotopyCartesian_iff_top_of_bot hh).mpr hα

/-- A homotopy-commutative square whose vertical maps are weak homotopy equivalences is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_vert (H : (p.comp α).Homotopy (h.comp p'))
    (hp' : p'.IsWeakHomotopyEquivalence) (hp : p.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian := (H.isHomotopyCartesian_iff_left_of_right hp).mpr hp'

end ContinuousMap.Homotopy

/-! ### Strict homotopy-cartesian squares -/

namespace TauCeti

section StrictSquare

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- A strictly commuting square `hcomm : p.comp α = h.comp p'` of continuous maps is
**homotopy-cartesian** if its constant-path lift `HomotopyPullback.liftStrict hcomm` is a weak
homotopy equivalence. -/
def IsHomotopyCartesian (hcomm : p.comp α = h.comp p') : Prop :=
  (HomotopyPullback.liftStrict hcomm).IsWeakHomotopyEquivalence

theorem isHomotopyCartesian_iff (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔ (HomotopyPullback.liftStrict hcomm).IsWeakHomotopyEquivalence :=
  Iff.rfl

theorem isHomotopyCartesian_iff_homotopy (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔
      ((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).IsHomotopyCartesian := by
  rw [isHomotopyCartesian_iff, ContinuousMap.Homotopy.isHomotopyCartesian_iff,
    HomotopyPullback.liftStrict_def]

theorem IsHomotopyCartesian.symm {hcomm : p.comp α = h.comp p'}
    (hcart : IsHomotopyCartesian hcomm) : IsHomotopyCartesian hcomm.symm := by
  rw [isHomotopyCartesian_iff, ← HomotopyPullback.swap_comp_liftStrict hcomm]
  exact (HomotopyPullback.isWeakHomotopyEquivalence_swap p h).comp hcart

theorem isHomotopyCartesian_symm_iff (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm.symm ↔ IsHomotopyCartesian hcomm :=
  ⟨IsHomotopyCartesian.symm, IsHomotopyCartesian.symm⟩

/-- **Strict-square mapping-path fibre criterion.** A strictly commuting square
`hcomm : p.comp α = h.comp p'` is homotopy-cartesian if and only if the induced map
`MappingPathFiber.map α h hcomm.symm rfl` on mapping-path fibres is a weak homotopy equivalence
over every `b' : B'`. -/
theorem isHomotopyCartesian_iff_forall_mappingPathFiber (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔
      ∀ b' : B', (MappingPathFiber.map α h hcomm.symm rfl :
        C(MappingPathFiber p' b', MappingPathFiber p (h b'))).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff_homotopy,
    ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber]
  refine forall_congr' fun b' ↦ ?_
  have hhom := ContinuousMap.Homotopy.mappingPathFiberSqMap_refl_homotopic_map hcomm b'
  exact ⟨fun hf ↦ hf.of_homotopic hhom, fun hf ↦ hf.of_homotopic hhom.symm⟩

/-- For any map `p : C(E, B)`, the square `p ∘ id = id ∘ p` is homotopy-cartesian. -/
theorem isHomotopyCartesian_id_horiz (p : C(E, B)) :
    IsHomotopyCartesian (p.comp_id.trans p.id_comp.symm) :=
  (isHomotopyCartesian_iff_homotopy _).mpr <|
    ContinuousMap.Homotopy.isHomotopyCartesian_of_horiz _ .id .id

/-- **Point-inclusion specialization.** Any commuting square from the strict fibre `p ⁻¹' {b}` over
a one-point space `B'` with `h default = b` is homotopy-cartesian if and only if
`MappingPathFiber.ofFiber p b` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_fiber_iff_ofFiber [Unique B']
    {p : C(E, B)} {h : C(B', B)} {b : B} (hb : h default = b) {p' : C(↥(p ⁻¹' {b}), B')}
    (hcomm : p.comp ⟨Subtype.val, continuous_subtypeVal⟩ = h.comp p') :
    IsHomotopyCartesian hcomm ↔ (MappingPathFiber.ofFiber p b).IsWeakHomotopyEquivalence := by
  subst hb
  rw [isHomotopyCartesian_iff,
    ← (HomotopyPullback.uniqueRightHomeomorph p h).isWeakHomotopyEquivalence.postcomp_iff,
    HomotopyPullback.uniqueRightHomeomorph_comp_liftStrict_eq_ofFiber]

end StrictSquare

/-! ### Comparison with the strict pullback along a Hurewicz fibration -/

namespace IsHurewiczFibration

variable {A : Type u} {B : Type v} {C : Type u'}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- When `p : C(A, B)` is a Hurewicz fibration in any lifting universe, the constant-path
comparison `HomotopyPullback.ofPullback p g` from the strict pullback `(⇑p).Pullback ⇑g` to
`HomotopyPullback p g` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_left {p : C(A, B)} (hp : IsHurewiczFibration.{v'} p)
    (g : C(C, B)) : (HomotopyPullback.ofPullback p g).IsWeakHomotopyEquivalence := by
  have hp_snd : IsHurewiczFibration.{v'} (ContinuousMap.pullbackSnd ⇑p ⇑g) := by
    convert (hp.pullback g).comp_homeomorph (Homeomorph.pullbackComm ⇑p ⇑g) using 1
    ext; simp [Function.Pullback.snd]
  rw [hp_snd.isWeakHomotopyEquivalence_iff_forall_fiberMap
    (HomotopyPullback.isHurewiczFibration_snd p g : IsHurewiczFibration.{0} _)
    (HomotopyPullback.snd_comp_ofPullback p g)]
  intro c
  let eDom : ↥(p ⁻¹' {g c}) ≃ₜ
      {x : (⇑p).Pullback ⇑g // ContinuousMap.pullbackSnd ⇑p ⇑g x = c} :=
    { toFun a :=
        ⟨⟨(a.val, c), Set.mem_singleton_iff.mp a.property⟩, by simp [Function.Pullback.snd]⟩
      invFun x := ⟨x.val.val.1, Set.mem_singleton_iff.mpr <|
        x.val.property.trans (congrArg g (by simpa [Function.Pullback.snd] using x.property))⟩
      left_inv _ := rfl
      right_inv x := Subtype.ext <| Subtype.ext <| Prod.ext rfl
        (by simpa [Function.Pullback.snd] using x.property.symm)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eCod : {y // HomotopyPullback.snd p g y = c} ≃ₜ MappingPathFiber p (g c) :=
    HomotopyPullback.sndFiberHomeomorph p g c
  have hconj : (eCod : C(_, _)).comp ((fiberMap (HomotopyPullback.ofPullback p g)
      (HomotopyPullback.snd_comp_ofPullback p g) c).comp (eDom : C(_, _))) =
      MappingPathFiber.ofFiber p (g c) := by
    ext a : 1; apply Subtype.ext
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, eCod]
    refine (HomotopyPullback.sndFiberHomeomorph_val p g c _).trans ?_
    simp [eDom, Set.mem_singleton_iff.mp a.property]
  exact (Homeomorph.isWeakHomotopyEquivalence_comp_comp_iff eDom eCod _).mp
    (hconj ▸ hp.isWeakHomotopyEquivalence_ofFiber (g c))

/-- When `q : C(C, B)` is a Hurewicz fibration in any lifting universe,
`HomotopyPullback.ofPullback f q` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_right (f : C(A, B)) {q : C(C, B)}
    (hq : IsHurewiczFibration.{v'} q) :
    (HomotopyPullback.ofPullback f q).IsWeakHomotopyEquivalence :=
  (HomotopyPullback.isWeakHomotopyEquivalence_ofPullback_comm_iff f q).mp
    (hq.isWeakHomotopyEquivalence_ofPullback_left f)

end IsHurewiczFibration

end TauCeti

/-! ### Homotopy-cartesian squares and Serre fibrations in `TopCat` -/

namespace CategoryTheory.CommSq

open TauCeti TauCeti.TopCat

variable {E B E' B' : TopCat.{u}} {α : E' ⟶ E} {p' : E' ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}

/-- A commutative square `sq : CommSq α p' p h` in `TopCat` is **homotopy-cartesian** if its
underlying square `p.hom.comp α.hom = h.hom.comp p'.hom` is homotopy-cartesian. -/
def IsHomotopyCartesian (sq : CommSq α p' p h) : Prop := TauCeti.IsHomotopyCartesian sq.hom_comp_eq

theorem isHomotopyCartesian_iff (sq : CommSq α p' p h) :
    sq.IsHomotopyCartesian ↔ TauCeti.IsHomotopyCartesian sq.hom_comp_eq := Iff.rfl

theorem IsHomotopyCartesian.flip {sq : CommSq α p' p h} (hsq : sq.IsHomotopyCartesian) :
    sq.flip.IsHomotopyCartesian := TauCeti.IsHomotopyCartesian.symm hsq

theorem isHomotopyCartesian_flip_iff (sq : CommSq α p' p h) :
    sq.flip.IsHomotopyCartesian ↔ sq.IsHomotopyCartesian := TauCeti.isHomotopyCartesian_symm_iff _

/-- **Strict-fibre criterion for squares of Serre fibrations.** When `p` and `p'` are Serre
fibrations in `TopCat`, a commutative square `sq : CommSq α p' p h` is homotopy-cartesian if and
only if the induced map `sq.fiberMap b'` on strict fibres is a weak homotopy equivalence for every
`b' : B'`. -/
theorem isHomotopyCartesian_iff_forall_fiberMap (sq : CommSq α p' p h)
    (hp : serreFibrations p) (hp' : serreFibrations p') :
    sq.IsHomotopyCartesian ↔ ∀ b' : B', (sq.fiberMap b').hom.IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff, TauCeti.isHomotopyCartesian_iff_forall_mappingPathFiber]
  refine forall_congr' fun b' ↦ ?_
  have hsq_of : (MappingPathFiber.map α.hom h.hom sq.hom_comp_eq.symm rfl :
      C(MappingPathFiber p'.hom b', MappingPathFiber p.hom (h b'))).comp
      (MappingPathFiber.ofFiber p'.hom b') =
      (MappingPathFiber.ofFiber p.hom (h b')).comp (sq.fiberMap b').hom := by
    ext x : 1; rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, MappingPathFiber.map_ofFiber]
    exact congrArg _ (Subtype.ext (sq.fiberMap_apply_coe b' x).symm)
  rw [← (isWeakHomotopyEquivalence_ofFiber hp' b').precomp_iff, hsq_of,
    (isWeakHomotopyEquivalence_ofFiber hp (h b')).postcomp_iff]

/-- Relative to any homotopy-cartesian pullback square `hpb : IsPullback β q p h`, a commutative
square `sq : CommSq α p' p h` in `TopCat` is homotopy-cartesian if and only if the induced cone map
`hpb.lift α p' sq.w` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_lift {P : _root_.TopCat.{u}} {β : P ⟶ E} {q : P ⟶ B'}
    (sq : CommSq α p' p h) (hpb : IsPullback β q p h) (hhpb : hpb.toCommSq.IsHomotopyCartesian) :
    sq.IsHomotopyCartesian ↔ (hpb.lift α p' sq.w).hom.IsWeakHomotopyEquivalence := by
  have hcomp := HomotopyPullback.liftStrict_comp hpb.toCommSq.hom_comp_eq sq.hom_comp_eq
    (hpb.lift α p' sq.w).hom
    ((_root_.TopCat.hom_comp _ _).symm.trans (congrArg _root_.TopCat.Hom.hom (hpb.lift_fst ..)))
    ((_root_.TopCat.hom_comp _ _).symm.trans (congrArg _root_.TopCat.Hom.hom (hpb.lift_snd ..)))
  rw [isHomotopyCartesian_iff, TauCeti.isHomotopyCartesian_iff, ← hcomp]
  exact hhpb.postcomp_iff

/-- When the right vertical map `p : E ⟶ B` is a Serre fibration, a commutative square
`sq : CommSq α p' p h` in `TopCat` is homotopy-cartesian if and only if the induced map into the
strict pullback `TopCat.pullbackCone h p` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_pullbackLift_of_right (sq : CommSq α p' p h)
    (hp : serreFibrations p) :
    sq.IsHomotopyCartesian ↔
      ((_root_.TopCat.pullbackConeIsLimit h p).lift
        (Limits.PullbackCone.mk p' α sq.w.symm)).hom.IsWeakHomotopyEquivalence := by
  let hc : IsPullback (_root_.TopCat.pullbackSnd h p) (_root_.TopCat.pullbackFst h p) p h :=
    (IsPullback.of_isLimit (_root_.TopCat.pullbackConeIsLimit h p)).flip
  have hcanon : hc.toCommSq.IsHomotopyCartesian := by
    rw [hc.toCommSq.isHomotopyCartesian_iff_forall_fiberMap hp
      (mem_serreFibrations_pullbackFst hp h)]
    intro b'; rw [hc.toCommSq.fiberMap_pullbackSnd b']
    exact (mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso _)
  have hlift : hc.lift α p' sq.w =
      (_root_.TopCat.pullbackConeIsLimit h p).lift (Limits.PullbackCone.mk p' α sq.w.symm) :=
    Limits.PullbackCone.IsLimit.hom_ext (_root_.TopCat.pullbackConeIsLimit h p)
      ((hc.lift_snd α p' sq.w).trans (by simp)) ((hc.lift_fst α p' sq.w).trans (by simp))
  exact hlift ▸ sq.isHomotopyCartesian_iff_lift hc hcanon

/-- When the bottom map `h : B' ⟶ B` is a Serre fibration, a commutative square
`sq : CommSq α p' p h` in `TopCat` is homotopy-cartesian if and only if the induced map into the
strict pullback `TopCat.pullbackCone p h` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_pullbackLift_of_bot (sq : CommSq α p' p h)
    (hh : serreFibrations h) :
    sq.IsHomotopyCartesian ↔
      ((_root_.TopCat.pullbackConeIsLimit p h).lift
        (Limits.PullbackCone.mk α p' sq.w)).hom.IsWeakHomotopyEquivalence :=
  sq.isHomotopyCartesian_flip_iff.symm.trans
    (sq.flip.isHomotopyCartesian_iff_pullbackLift_of_right hh)

end CategoryTheory.CommSq

namespace CategoryTheory.IsPullback

open TauCeti TauCeti.TopCat

variable {P E B B' : _root_.TopCat.{u}} {α : P ⟶ E} {p' : P ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}

/-- **Pullback along a Serre fibration is homotopy-cartesian (right vertical map).** Any
categorical pullback square `IsPullback α p' p h` in `TopCat` whose right vertical map `p` is a
Serre fibration is homotopy-cartesian. -/
theorem isHomotopyCartesian_of_right (hpb : IsPullback α p' p h) (hp : serreFibrations p) :
    hpb.toCommSq.IsHomotopyCartesian := by
  have : IsIso ((_root_.TopCat.pullbackConeIsLimit h p).lift
      (Limits.PullbackCone.mk p' α hpb.toCommSq.w.symm)) :=
    (_root_.TopCat.pullbackConeIsLimit h p).nonempty_isLimit_iff_isIso_lift.mp ⟨hpb.flip.isLimit⟩
  exact (hpb.toCommSq.isHomotopyCartesian_iff_pullbackLift_of_right hp).mpr
    ((mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso _))

/-- **Pullback along a Serre fibration is homotopy-cartesian (bottom map).** Any categorical
pullback square `IsPullback α p' p h` in `TopCat` whose bottom map `h` is a Serre fibration is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_bot (hpb : IsPullback α p' p h) (hh : serreFibrations h) :
    hpb.toCommSq.IsHomotopyCartesian := (hpb.flip.isHomotopyCartesian_of_right hh).flip

end CategoryTheory.IsPullback

namespace TauCeti.TopCat

/-- **Strict-to-homotopy pullback comparison along a Serre fibration (left leg).** When
`p : A ⟶ B` is a Serre fibration in `TopCat` and `g : C ⟶ B` is any morphism, the constant-path
map `HomotopyPullback.ofPullback p.hom g.hom` from `(⇑p.hom).Pullback ⇑g.hom` to
`HomotopyPullback p.hom g.hom` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_of_left {A B C : _root_.TopCat.{u}}
    {p : A ⟶ B} (hp : serreFibrations p) (g : C ⟶ B) :
    (HomotopyPullback.ofPullback p.hom g.hom).IsWeakHomotopyEquivalence := by
  have hc : IsPullback (_root_.TopCat.pullbackSnd g p) (_root_.TopCat.pullbackFst g p) p g :=
    (IsPullback.of_isLimit (_root_.TopCat.pullbackConeIsLimit g p)).flip
  have hcomp : HomotopyPullback.ofPullback p.hom g.hom =
      (HomotopyPullback.liftStrict hc.toCommSq.hom_comp_eq).comp
        (Homeomorph.pullbackComm ⇑p.hom ⇑g.hom : C(_, _)) := by
    ext x : 1; exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp
  exact hcomp ▸ (hc.isHomotopyCartesian_of_right hp).comp
    (Homeomorph.pullbackComm ⇑p.hom ⇑g.hom).isWeakHomotopyEquivalence

/-- **Strict-to-homotopy pullback comparison along a Serre fibration (right leg).** When
`q : C ⟶ B` is a Serre fibration in `TopCat` and `f : A ⟶ B` is any morphism,
`HomotopyPullback.ofPullback f.hom q.hom` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_of_right {A B C : _root_.TopCat.{u}}
    (f : A ⟶ B) {q : C ⟶ B} (hq : serreFibrations q) :
    (HomotopyPullback.ofPullback f.hom q.hom).IsWeakHomotopyEquivalence :=
  (HomotopyPullback.isWeakHomotopyEquivalence_ofPullback_comm_iff f.hom q.hom).mp
    (isWeakHomotopyEquivalence_ofPullback_of_left hq f)

end TauCeti.TopCat
