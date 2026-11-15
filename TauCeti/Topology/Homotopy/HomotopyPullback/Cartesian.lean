/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyPullback.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Functoriality
public import TauCeti.Topology.Homotopy.SerreFibration.MappingPath

/-!
# Homotopy-cartesian squares and fibration pullbacks

A homotopy-commutative square `H : (p.comp α).Homotopy (h.comp p')` (`E' → E` over `B' → B`)
induces a canonical map `E' → HomotopyPullback p h` via `TauCeti.HomotopyPullback.lift`. It is
**homotopy-cartesian** (`ContinuousMap.Homotopy.IsHomotopyCartesian`) when this map is a weak
homotopy equivalence; strict squares (`TauCeti.IsHomotopyCartesian` and
`CategoryTheory.CommSq.IsHomotopyCartesian`) specialize via `TauCeti.HomotopyPullback.liftStrict`.

To characterize homotopy-cartesian squares across four independent universes without embedding into
a single `TopCat.{u}`, we factor `lift α p' H` up to homotopy through `MappingPathSpace p'`, giving
a map over `B'` between the Hurewicz fibrations `MappingPathSpace.endpoint p'` and
`HomotopyPullback.snd p h`. By
`TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_fiberMap`, `H` is
homotopy-cartesian iff
`H.mappingPathFiberSqMap b' : MappingPathFiber p' b' → MappingPathFiber p (h b')` is a weak
homotopy equivalence for every `b' : B'`.

From this criterion we deduce homotopy base change of weak homotopy equivalences along arbitrary
maps and the comparison between strict and homotopy pullbacks along Hurewicz and Serre fibrations.

## Main declarations

* `ContinuousMap.Homotopy.IsHomotopyCartesian`, `TauCeti.IsHomotopyCartesian`,
  `CategoryTheory.CommSq.IsHomotopyCartesian`: homotopy-cartesian squares (up to homotopy and
  strict).
* `ContinuousMap.Homotopy.mappingPathFiberSqMap`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber`,
  `TauCeti.IsHomotopyCartesian.iff_forall_mappingPathFiber`,
  `TauCeti.isHomotopyCartesian_fiber_iff_ofFiber`: mapping-path fibre characterizations and
  point-inclusion specialization.
* `TauCeti.HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_top_of_bottom`: homotopy base change of weak
  homotopy equivalences.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_ofPullback_of_left`,
  `CategoryTheory.IsPullback.isHomotopyCartesian_of_right`,
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_forall_fiberMap`: strict pullbacks and squares of
  Serre fibrations in `TopCat`.

## References

* M. Mather, *Pull-backs in homotopy theory*, Canadian Journal of Mathematics 28 (1976), 225–263.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval

universe u v u' v'

/-! ### Auxiliary weak-equivalence and path-family lemmas -/

namespace TauCeti

/-- Reparametrizing a continuously varying family of paths with varying endpoints by a fixed
endpoint-preserving map `f : I → I` varies continuously with the homotopy parameter in `I`. -/
private theorem reparamHomotopy_continuous_family {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] {x y : A → X}
    (γ : ∀ a, Path (x a) (y a)) (hγ : Continuous ↿γ)
    {f : I → I} (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Continuous ↿fun q : I × A ↦
      (Path.Homotopy.reparam (γ q.2) f hf hf₀ hf₁).eval q.1 :=
  hγ.comp ((continuous_snd.comp continuous_fst).prodMk <|
    (by fun_prop : Continuous fun q : (I × A) × I ↦
      (σ q.1.1 : ℝ) * (q.2 : ℝ) + (q.1.1 : ℝ) * (f q.2 : ℝ)).subtype_mk fun q ↦
      show (σ q.1.1 : ℝ) • (q.2 : ℝ) + (q.1.1 : ℝ) • (f q.2 : ℝ) ∈ I from
        convex_Icc _ _ q.2.2 (f q.2).2 (by unit_interval) (by unit_interval) (by simp))

/-- `HomotopyPullback.swap` is a weak homotopy equivalence. -/
theorem HomotopyPullback.isWeakHomotopyEquivalence_swap {A : Type u} {B : Type v} {C : Type u'}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(C, B)) :
    (HomotopyPullback.swap f g).IsWeakHomotopyEquivalence :=
  HomotopyPullback.coe_swapHomeomorph f g ▸
    (HomotopyPullback.swapHomeomorph f g).isWeakHomotopyEquivalence

end TauCeti

/-! ### Homotopy-cartesian squares -/

namespace ContinuousMap.Homotopy

open TauCeti

section Basic

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- A homotopy-commutative square `H : (p.comp α).Homotopy (h.comp p')` is
**homotopy-cartesian** if the induced map
`HomotopyPullback.lift α p' H : C(E', HomotopyPullback p h)` is a weak homotopy equivalence. -/
def IsHomotopyCartesian (H : (p.comp α).Homotopy (h.comp p')) : Prop :=
  (HomotopyPullback.lift α p' H).IsWeakHomotopyEquivalence

theorem isHomotopyCartesian_iff (H : (p.comp α).Homotopy (h.comp p')) :
    H.IsHomotopyCartesian ↔ (HomotopyPullback.lift α p' H).IsWeakHomotopyEquivalence :=
  Iff.rfl

/-- Reversing the square `H` swaps the two legs of `HomotopyPullback p h` via `swapHomeomorph`, so
`H.symm` is homotopy-cartesian when `H` is. -/
theorem IsHomotopyCartesian.symm {H : (p.comp α).Homotopy (h.comp p')}
    (hH : H.IsHomotopyCartesian) : H.symm.IsHomotopyCartesian := by
  rw [IsHomotopyCartesian, ← HomotopyPullback.swap_comp_lift α p' H]
  exact (HomotopyPullback.isWeakHomotopyEquivalence_swap p h).comp hH

theorem isHomotopyCartesian_symm_iff (H : (p.comp α).Homotopy (h.comp p')) :
    H.symm.IsHomotopyCartesian ↔ H.IsHomotopyCartesian :=
  ⟨fun hH ↦ by simpa using hH.symm, IsHomotopyCartesian.symm⟩

/-- Casting the boundary equalities of a homotopy does not change whether the square is
homotopy-cartesian. -/
@[simp]
theorem isHomotopyCartesian_cast_iff {f₀ : C(E', B)} {f₁ : C(E', B)}
    (H : f₀.Homotopy f₁) (h₀ : f₀ = p.comp α) (h₁ : f₁ = h.comp p') :
    (H.cast h₀ h₁).IsHomotopyCartesian ↔
      (HomotopyPullback.lift α p' (H.cast h₀ h₁)).IsWeakHomotopyEquivalence :=
  Iff.rfl

/-! ### Mapping-path fibre map and fibrewise characterization -/

/-- The map over `B'` from `MappingPathSpace p'` to `HomotopyPullback p h` induced by
`H : (p.comp α).Homotopy (h.comp p')`, sending `(e', γ')` with `γ' 0 = p' e'` to
`(α e', γ' 1, (H.evalAt e').trans (γ'.map h))`. -/
noncomputable def mappingPathReplacementLift (H : (p.comp α).Homotopy (h.comp p')) :
    C(MappingPathSpace p', HomotopyPullback p h) where
  toFun q :=
    ⟨(α q.val.1, q.val.2 1,
      ((H.evalAt q.val.1).trans
        ((⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map
          h.continuous)).toContinuousMap),
      Path.source _, Path.target _⟩
  continuous_toFun := by
    refine ((α.continuous.comp continuous_subtype_val.fst).prodMk <|
      (continuous_subtype_val.snd.eval continuous_const).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun q : MappingPathSpace p' ↦ H.evalAt q.val.1)
      (H.continuous.comp (continuous_snd.prodMk (continuous_subtype_val.fst.comp continuous_fst)))
      (fun q : MappingPathSpace p' ↦
        (⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map h.continuous)
      (h.continuous.comp ((continuous_subtype_val.snd.comp continuous_fst).eval continuous_snd))

@[simp]
theorem mappingPathReplacementLift_val (H : (p.comp α).Homotopy (h.comp p'))
    (q : MappingPathSpace p') :
    (H.mappingPathReplacementLift q).val =
      (α q.val.1, q.val.2 1,
        ((H.evalAt q.val.1).trans
          ((⟨q.val.2, q.property, rfl⟩ : Path (p' q.val.1) (q.val.2 1)).map
            h.continuous)).toContinuousMap) :=
  (rfl)

@[simp]
theorem snd_comp_mappingPathReplacementLift (H : (p.comp α).Homotopy (h.comp p')) :
    (HomotopyPullback.snd p h).comp H.mappingPathReplacementLift =
      MappingPathSpace.endpoint p' := by
  ext q : 1
  simp

/-- Precomposing `H.mappingPathReplacementLift` with `MappingPathSpace.incl p'` appends a constant
path to `H.evalAt e'`, so it is homotopic to `HomotopyPullback.lift α p' H`. -/
theorem lift_homotopic_mappingPathReplacementLift_comp_incl
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
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact reparamHomotopy_continuous_family (fun e' : E' ↦ H.evalAt e')
        (H.continuous.comp (continuous_snd.prodMk continuous_fst)) hφ hφ₀ hφ₁
    map_zero_left e' := HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp
    map_one_left e' := by
      apply Subtype.ext
      change (α e', p' e',
          ((Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1).toContinuousMap) =
        (H.mappingPathReplacementLift (MappingPathSpace.incl p' e')).val
      rw [mappingPathReplacementLift_val]
      refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
      ext t : 1
      have h1 : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1 =
          (H.evalAt e').trans (.refl (h (p' e'))) :=
        (by simp : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1 =
          (H.evalAt e').reparam φ hφ hφ₀ hφ₁).trans
          (Path.Homotopy.trans_refl_reparam (H.evalAt e')).symm
      exact (congrArg (fun γ : Path (p (α e')) (h (p' e')) ↦ γ t) h1).trans
        (by simp [Path.trans_apply]) }⟩

/-- The map on mapping-path fibres over `b' : B'` induced by a homotopy-commutative square
`H : (p.comp α).Homotopy (h.comp p')`, sending `(e', γ')` (`γ' : p' e' ⇝ b'`) to
`(α e', (H.evalAt e').trans (γ'.map h))`. -/
noncomputable def mappingPathFiberSqMap (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    C(MappingPathFiber p' b', MappingPathFiber p (h b')) where
  toFun q :=
    ⟨(α q.val.1,
      ((H.evalAt q.val.1).trans
        ((⟨q.val.2, q.property.1, q.property.2⟩ : Path (p' q.val.1) b').map
          h.continuous)).toContinuousMap),
      Path.source _, Path.target _⟩
  continuous_toFun := by
    refine ((α.continuous.comp continuous_subtype_val.fst).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun q : MappingPathFiber p' b' ↦ H.evalAt q.val.1)
      (H.continuous.comp (continuous_snd.prodMk (continuous_subtype_val.fst.comp continuous_fst)))
      (fun q : MappingPathFiber p' b' ↦
        (⟨q.val.2, q.property.1, q.property.2⟩ : Path (p' q.val.1) b').map h.continuous)
      (h.continuous.comp ((continuous_subtype_val.snd.comp continuous_fst).eval continuous_snd))

@[simp]
theorem mappingPathFiberSqMap_val_fst (H : (p.comp α).Homotopy (h.comp p')) (b' : B')
    (q : MappingPathFiber p' b') :
    (H.mappingPathFiberSqMap b' q).val.1 = α q.val.1 :=
  (rfl)

@[simp]
theorem mappingPathFiberSqMap_val_snd_apply (H : (p.comp α).Homotopy (h.comp p')) (b' : B')
    (q : MappingPathFiber p' b') (t : I) :
    (H.mappingPathFiberSqMap b' q).val.2 t =
      ((H.evalAt q.val.1).trans
        ((⟨q.val.2, q.property.1, q.property.2⟩ : Path (p' q.val.1) b').map h.continuous)) t :=
  (rfl)

@[simp]
theorem proj_comp_mappingPathFiberSqMap (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    (MappingPathFiber.proj p (h b')).comp (H.mappingPathFiberSqMap b') =
      α.comp (MappingPathFiber.proj p' b') := by
  ext q : 1
  simp

/-- **Mapping-path fibre characterization of homotopy-cartesian squares.** A homotopy-commutative
square `H : (p.comp α).Homotopy (h.comp p')` between spaces in arbitrary universes is
homotopy-cartesian if and only if, for every `b' : B'`, the induced map
`H.mappingPathFiberSqMap b' : MappingPathFiber p' b' → MappingPathFiber p (h b')` on mapping-path
fibres is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_forall_mappingPathFiber
    (H : (p.comp α).Homotopy (h.comp p')) :
    H.IsHomotopyCartesian ↔
      ∀ b' : B', (H.mappingPathFiberSqMap b').IsWeakHomotopyEquivalence := by
  have hincl := MappingPathSpace.isWeakHomotopyEquivalence_incl p'
  have hrep : H.IsHomotopyCartesian ↔ H.mappingPathReplacementLift.IsWeakHomotopyEquivalence :=
    ⟨fun hH ↦ hincl.of_precomp
        (hH.of_homotopic H.lift_homotopic_mappingPathReplacementLift_comp_incl),
      fun hΦ ↦ (hΦ.comp hincl).of_homotopic
        H.lift_homotopic_mappingPathReplacementLift_comp_incl.symm⟩
  have hp_end : IsHurewiczFibration.{0} (MappingPathSpace.endpoint p') :=
    MappingPathSpace.isHurewiczFibration_endpoint p'
  have hp_snd : IsHurewiczFibration.{0} (HomotopyPullback.snd p h) :=
    HomotopyPullback.isHurewiczFibration_snd p h
  rw [hrep, hp_end.isWeakHomotopyEquivalence_iff_forall_fiberMap
    hp_snd H.snd_comp_mappingPathReplacementLift]
  refine forall_congr' fun b' ↦ ?_
  let eX : MappingPathFiber p' b' ≃ₜ {e // MappingPathSpace.endpoint p' e = b'} :=
    MappingPathFiber.endpointHomeomorph p' b'
  let eY : {e' // HomotopyPullback.snd p h e' = b'} ≃ₜ MappingPathFiber p (h b') :=
    HomotopyPullback.sndFiberHomeomorph p h b'
  have hconj : H.mappingPathFiberSqMap b' =
      (eY : C(_, _)).comp
        ((fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b').comp
          (eX : C(_, _))) := by
    ext q : 1
    apply Subtype.ext
    let x : (HomotopyPullback.snd p h) ⁻¹' {b'} :=
      fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b' (eX q)
    change (H.mappingPathFiberSqMap b' q).val =
      (HomotopyPullback.sndFiberHomeomorph p h b' x).val
    rw [HomotopyPullback.sndFiberHomeomorph_val]
    refine Prod.ext (by simp [x, eX]) ?_
    ext t : 1
    simp [x, eX, Path.trans_apply]
  rw [hconj]
  exact (Homeomorph.isWeakHomotopyEquivalence_conj_iff eX eY _).symm

end Basic

end ContinuousMap.Homotopy

/-! ### Homotopy base change of weak homotopy equivalences -/

namespace TauCeti.HomotopyPullback

section BaseChangeWeakEquiv

variable {A : Type u} {B : Type v} {C : Type u'}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- **Homotopy base change preserves weak homotopy equivalences (right leg).** If `g : C(C, B)` is
a weak homotopy equivalence, then for any continuous map `f : C(A, B)` the projection
`fst f g : C(HomotopyPullback f g, A)` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_fst_of_right (f : C(A, B)) {g : C(C, B)}
    (hg : g.IsWeakHomotopyEquivalence) :
    (fst f g).IsWeakHomotopyEquivalence := by
  have hincl := MappingPathSpace.isWeakHomotopyEquivalence_incl g
  have hend : (MappingPathSpace.endpoint g).IsWeakHomotopyEquivalence :=
    hincl.of_precomp (by rwa [MappingPathSpace.endpoint_comp_incl])
  have hp_end : IsHurewiczFibration.{0} (MappingPathSpace.endpoint g) :=
    MappingPathSpace.isHurewiczFibration_endpoint g
  have hp_idB : IsHurewiczFibration.{0} (ContinuousMap.id B) :=
    (Homeomorph.refl B).isHurewiczFibration
  have hp_fst : IsHurewiczFibration.{0} (fst f g) := isHurewiczFibration_fst f g
  have hp_idA : IsHurewiczFibration.{0} (ContinuousMap.id A) :=
    (Homeomorph.refl A).isHurewiczFibration
  have hend_fib := (hp_end.isWeakHomotopyEquivalence_iff_forall_fiberMap hp_idB
    (ContinuousMap.id_comp _)).mp hend
  rw [hp_fst.isWeakHomotopyEquivalence_iff_forall_fiberMap hp_idA (ContinuousMap.id_comp _)]
  intro a
  let eDom : {e // MappingPathSpace.endpoint g e = f a} ≃ₜ {e // fst f g e = a} :=
    (MappingPathFiber.endpointHomeomorph g (f a)).symm.trans (fstFiberHomeomorph f g a).symm
  let eCod : {e // ContinuousMap.id A e = a} ≃ₜ {e // ContinuousMap.id B e = f a} :=
    { toFun _ := ⟨f a, rfl⟩
      invFun _ := ⟨a, rfl⟩
      left_inv x := Subtype.ext x.2.symm
      right_inv y := Subtype.ext y.2.symm
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  have hconj : (eCod : C(_, _)).comp
      ((fiberMap (fst f g) (ContinuousMap.id_comp _) a).comp (eDom : C(_, _))) =
      fiberMap (MappingPathSpace.endpoint g) (ContinuousMap.id_comp _) (f a) := by
    ext x : 1; apply Subtype.ext
    rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply]
    have hy := (fiberMap (MappingPathSpace.endpoint g) (ContinuousMap.id_comp _) (f a) x).2
    rw [ContinuousMap.id_apply] at hy
    exact hy.symm
  exact (Homeomorph.isWeakHomotopyEquivalence_conj_iff eDom eCod _).mp (hconj ▸ hend_fib (f a))

/-- **Homotopy base change preserves weak homotopy equivalences (left leg).** If `f : C(A, B)` is
a weak homotopy equivalence, then for any continuous map `g : C(C, B)` the projection
`snd f g : C(HomotopyPullback f g, C)` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_snd_of_left {f : C(A, B)} (hf : f.IsWeakHomotopyEquivalence)
    (g : C(C, B)) :
    (snd f g).IsWeakHomotopyEquivalence := by
  have hswap_fst : (fst g f).comp (swap f g) = snd f g := ContinuousMap.ext (fst_swap f g)
  rw [← hswap_fst]
  exact (isWeakHomotopyEquivalence_fst_of_right g hf).comp (isWeakHomotopyEquivalence_swap f g)

end BaseChangeWeakEquiv

end TauCeti.HomotopyPullback

namespace ContinuousMap.Homotopy

open TauCeti

section WeakEquivLegs

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- When the bottom map `h : C(B', B)` of `H : (p.comp α).Homotopy (h.comp p')` is a weak homotopy
equivalence, the square is homotopy-cartesian if and only if the top map `α : C(E', E)` is a weak
homotopy equivalence. -/
theorem isHomotopyCartesian_iff_top_of_bottom (H : (p.comp α).Homotopy (h.comp p'))
    (hh : h.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian ↔ α.IsWeakHomotopyEquivalence := by
  have hfst := HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right p hh
  have hcomp := HomotopyPullback.fst_comp_lift α p' H
  exact ⟨fun hH ↦ hcomp ▸ hfst.comp hH, fun hα ↦ hfst.of_postcomp (hcomp.symm ▸ hα)⟩

/-- When the right vertical map `p : C(E, B)` of `H : (p.comp α).Homotopy (h.comp p')` is a weak
homotopy equivalence, the square is homotopy-cartesian if and only if the left vertical map
`p' : C(E', B')` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_left_of_right (H : (p.comp α).Homotopy (h.comp p'))
    (hp : p.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian ↔ p'.IsWeakHomotopyEquivalence := by
  rw [← isHomotopyCartesian_symm_iff]
  exact H.symm.isHomotopyCartesian_iff_top_of_bottom hp

/-- A homotopy-commutative square whose horizontal maps are weak homotopy equivalences is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_horizontal (H : (p.comp α).Homotopy (h.comp p'))
    (hα : α.IsWeakHomotopyEquivalence) (hh : h.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian :=
  (H.isHomotopyCartesian_iff_top_of_bottom hh).mpr hα

/-- A homotopy-commutative square whose vertical maps are weak homotopy equivalences is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_vertical (H : (p.comp α).Homotopy (h.comp p'))
    (hp' : p'.IsWeakHomotopyEquivalence) (hp : p.IsWeakHomotopyEquivalence) :
    H.IsHomotopyCartesian :=
  (H.isHomotopyCartesian_iff_left_of_right hp).mpr hp'

end WeakEquivLegs

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

theorem isHomotopyCartesian_iff_homotopy (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔
      ((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).IsHomotopyCartesian := by
  have heq : HomotopyPullback.liftStrict hcomm =
      HomotopyPullback.lift α p' ((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm) := by
    ext x : 1; exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp
  rw [IsHomotopyCartesian, ContinuousMap.Homotopy.IsHomotopyCartesian, heq]

theorem IsHomotopyCartesian.symm {hcomm : p.comp α = h.comp p'}
    (hcart : IsHomotopyCartesian hcomm) : IsHomotopyCartesian hcomm.symm := by
  have heq : HomotopyPullback.liftStrict hcomm.symm =
      (HomotopyPullback.swap p h).comp (HomotopyPullback.liftStrict hcomm) := by
    ext x : 1
    exact HomotopyPullback.ext (by simp) (by simp)
      fun _ ↦ by simpa using (ContinuousMap.congr_fun hcomm x).symm
  rw [IsHomotopyCartesian, heq]
  exact (HomotopyPullback.isWeakHomotopyEquivalence_swap p h).comp hcart

theorem isHomotopyCartesian_symm_iff (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm.symm ↔ IsHomotopyCartesian hcomm :=
  ⟨IsHomotopyCartesian.symm, IsHomotopyCartesian.symm⟩

/-- For a strictly commuting square `hcomm : p.comp α = h.comp p'`, `mappingPathFiberSqMap` differs
from `MappingPathFiber.map α h hcomm.symm rfl` only by prepending a constant path, so the two maps
are homotopic. -/
theorem mappingPathFiberSqMap_refl_homotopic_map (hcomm : p.comp α = h.comp p') (b' : B') :
    (((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).mappingPathFiberSqMap b').Homotopic
      (MappingPathFiber.map α h hcomm.symm rfl) := by
  let γ (q : MappingPathFiber p' b') : Path (p (α q.val.1)) (h b') :=
    ((⟨q.val.2, q.property.1, q.property.2⟩ : Path (p' q.val.1) b').map h.continuous).cast
      (show p (α q.val.1) = h (p' q.val.1) from ContinuousMap.congr_fun hcomm q.val.1) rfl
  have hγ : Continuous ↿γ :=
    h.continuous.comp ((continuous_subtype_val.snd.comp continuous_fst).eval continuous_snd)
  refine ⟨{
    toFun r := ⟨(α r.2.val.1, (Path.delayReflLeft r.1 (γ r.2)).toContinuousMap),
      Path.source _, Path.target _⟩
    continuous_toFun := by
      refine ((α.continuous.comp
        (continuous_subtype_val.fst.comp continuous_snd)).prodMk ?_).subtype_mk _
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact Path.delayReflLeft_continuous_family
        (fun r : I × MappingPathFiber p' b' ↦ γ r.2)
        (hγ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        ContinuousMap.fst
    map_zero_left q := by
      apply Subtype.ext; refine Prod.ext (by simp) ?_; ext t : 1
      change (Path.delayReflLeft 0 (γ q)) t =
        (((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).mappingPathFiberSqMap
          b' q).val.2 t
      rw [Path.delayReflLeft_zero, ContinuousMap.Homotopy.mappingPathFiberSqMap_val_snd_apply]
      simp [γ, Path.trans_apply]
    map_one_left q := by
      apply Subtype.ext; refine Prod.ext (by simp [MappingPathFiber.map_val]) ?_; ext t : 1
      change (Path.delayReflLeft 1 (γ q)) t =
        (MappingPathFiber.map α h hcomm.symm rfl q).val.2 t
      rw [Path.delayReflLeft_one, MappingPathFiber.map_val]; rfl }⟩

/-- **Strict-square mapping-path fibre criterion.** A strictly commuting square
`hcomm : p.comp α = h.comp p'` is homotopy-cartesian if and only if the induced map
`MappingPathFiber.map α h hcomm.symm rfl` on mapping-path fibres is a weak homotopy equivalence
over every `b' : B'`. -/
theorem IsHomotopyCartesian.iff_forall_mappingPathFiber (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔
      ∀ b' : B', (MappingPathFiber.map α h hcomm.symm rfl :
        C(MappingPathFiber p' b', MappingPathFiber p (h b'))).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff_homotopy,
    ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber]
  refine forall_congr' fun b' ↦ ?_
  have hhom := mappingPathFiberSqMap_refl_homotopic_map hcomm b'
  exact ⟨fun hf ↦ hf.of_homotopic hhom, fun hf ↦ hf.of_homotopic hhom.symm⟩

/-- For any map `p : C(E, B)`, the strict comparison of the horizontal-identity square
`p ∘ id = id ∘ p` identifies under `HomotopyPullback.idRightHomeomorph p` with the mapping-path
inclusion `MappingPathSpace.incl p`. -/
@[simp]
theorem idRightHomeomorph_comp_liftStrict_id (p : C(E, B)) :
    (HomotopyPullback.idRightHomeomorph p : C(_, _)).comp
      (HomotopyPullback.liftStrict (p.comp_id.trans p.id_comp.symm)) =
      MappingPathSpace.incl p := by
  ext x : 1; apply Subtype.ext
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply,
    HomotopyPullback.idRightHomeomorph_val, MappingPathSpace.incl_val]
  simp

/-- For any map `p : C(E, B)`, the square `p ∘ id = id ∘ p` is homotopy-cartesian. -/
theorem isHomotopyCartesian_id_horizontal (p : C(E, B)) :
    IsHomotopyCartesian (p.comp_id.trans p.id_comp.symm) := by
  rw [isHomotopyCartesian_iff_homotopy]
  exact ContinuousMap.Homotopy.isHomotopyCartesian_of_horizontal _ .id .id

/-- The canonical strict square exhibiting the strict fibre `p ⁻¹' {b}` over `Unit → B` at `b`. -/
theorem fiberSquare_comm (p : C(E, B)) (b : B) :
    p.comp ⟨Subtype.val, continuous_subtype_val⟩ =
      (ContinuousMap.const Unit b).comp (.const ↥(p ⁻¹' {b}) ()) :=
  ContinuousMap.ext fun x ↦ x.2

/-- Under `HomotopyPullback.constRightHomeomorphOfUnique p b`, the strict-square comparison of
`fiberSquare_comm p b` is the constant-path fibre inclusion `MappingPathFiber.ofFiber p b`. -/
@[simp]
theorem constRightHomeomorphOfUnique_comp_liftStrict_fiberSquare (p : C(E, B)) (b : B) :
    (HomotopyPullback.constRightHomeomorphOfUnique (C := Unit) p b : C(_, _)).comp
      (HomotopyPullback.liftStrict (fiberSquare_comm p b)) =
      MappingPathFiber.ofFiber p b := by
  ext x : 1; apply Subtype.ext
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply,
    HomotopyPullback.constRightHomeomorphOfUnique_val, MappingPathFiber.ofFiber_val]
  simp [show p x.1 = b from x.2]

/-- **Point-inclusion specialization.** The strict fibre square of `p ⁻¹' {b}` over `Unit → B`
at `b` is homotopy-cartesian if and only if `MappingPathFiber.ofFiber p b` is a weak homotopy
equivalence. -/
theorem isHomotopyCartesian_fiber_iff_ofFiber (p : C(E, B)) (b : B) :
    IsHomotopyCartesian (fiberSquare_comm p b) ↔
      (MappingPathFiber.ofFiber p b).IsWeakHomotopyEquivalence := by
  have he :=
    (HomotopyPullback.constRightHomeomorphOfUnique (C := Unit) p b).isWeakHomotopyEquivalence
  rw [IsHomotopyCartesian, ← constRightHomeomorphOfUnique_comp_liftStrict_fiberSquare p b]
  exact ⟨he.comp, he.of_postcomp⟩

end StrictSquare

/-! ### Comparison with the strict pullback along a Hurewicz fibration -/

namespace IsHurewiczFibration

/-- When `p : C(A, B)` is a Hurewicz fibration, the constant-path comparison
`HomotopyPullback.ofPullback p g` from the strict pullback `(⇑p).Pullback ⇑g` to
`HomotopyPullback p g` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_left {A : Type u} {B : Type v} {C : Type u'}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    (HomotopyPullback.ofPullback p g).IsWeakHomotopyEquivalence := by
  rw [← hp.pullbackHomotopyPullbackLeftEquiv_toFun g]
  convert (hp.pullbackHomotopyPullbackLeftEquiv g).toHomotopyEquiv.isWeakHomotopyEquivalence
    using 1
  ext x : 1
  exact ((hp.pullbackHomotopyPullbackLeftEquiv g).toHomotopyEquiv_apply x).symm

/-- When `q : C(C, B)` is a Hurewicz fibration, `HomotopyPullback.ofPullback f q` is a weak
homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_right {A : Type u} {B : Type v} {C : Type u'}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max u' v} q) :
    (HomotopyPullback.ofPullback f q).IsWeakHomotopyEquivalence := by
  rw [← hq.pullbackHomotopyPullbackRightEquiv_toFun f]
  convert (hq.pullbackHomotopyPullbackRightEquiv f).toHomotopyEquiv.isWeakHomotopyEquivalence
    using 1
  ext x : 1
  exact ((hq.pullbackHomotopyPullbackRightEquiv f).toHomotopyEquiv_apply x).symm

end IsHurewiczFibration

end TauCeti

/-! ### Homotopy-cartesian squares and Serre fibrations in `TopCat` -/

namespace CategoryTheory.CommSq

open TauCeti TauCeti.TopCat

section TopCat

variable {E B E' B' : TopCat.{u}} {α : E' ⟶ E} {p' : E' ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}

/-- Underlying `ContinuousMap` commutativity `p.hom.comp α.hom = h.hom.comp p'.hom` of a
commutative square `sq : CommSq α p' p h` in `TopCat`. -/
theorem hom_comp_eq (sq : CommSq α p' p h) : p.hom.comp α.hom = h.hom.comp p'.hom := by
  rw [← _root_.TopCat.hom_comp, ← _root_.TopCat.hom_comp, sq.w]

/-- A commutative square `sq : CommSq α p' p h` in `TopCat` is **homotopy-cartesian** if its
underlying square `p.hom.comp α.hom = h.hom.comp p'.hom` is homotopy-cartesian. -/
def IsHomotopyCartesian (sq : CommSq α p' p h) : Prop :=
  TauCeti.IsHomotopyCartesian sq.hom_comp_eq

theorem isHomotopyCartesian_iff (sq : CommSq α p' p h) :
    sq.IsHomotopyCartesian ↔ TauCeti.IsHomotopyCartesian sq.hom_comp_eq :=
  Iff.rfl

theorem IsHomotopyCartesian.flip {sq : CommSq α p' p h} (hsq : sq.IsHomotopyCartesian) :
    sq.flip.IsHomotopyCartesian :=
  TauCeti.IsHomotopyCartesian.symm hsq

theorem isHomotopyCartesian_flip_iff (sq : CommSq α p' p h) :
    sq.flip.IsHomotopyCartesian ↔ sq.IsHomotopyCartesian :=
  TauCeti.isHomotopyCartesian_symm_iff _

/-- **Strict-fibre criterion for squares of Serre fibrations.** When `p` and `p'` are Serre
fibrations in `TopCat`, a commutative square `sq : CommSq α p' p h` is homotopy-cartesian if and
only if the induced map `sq.fiberMap b'` on strict fibres is a weak homotopy equivalence for every
`b' : B'`. -/
theorem isHomotopyCartesian_iff_forall_fiberMap (sq : CommSq α p' p h)
    (hp : serreFibrations p) (hp' : serreFibrations p') :
    sq.IsHomotopyCartesian ↔
      ∀ b' : B', (sq.fiberMap b').hom.IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff, TauCeti.IsHomotopyCartesian.iff_forall_mappingPathFiber]
  refine forall_congr' fun b' ↦ ?_
  have hof' := isWeakHomotopyEquivalence_ofFiber hp' b'
  have hof := isWeakHomotopyEquivalence_ofFiber hp (h b')
  have hsq_of : (MappingPathFiber.map α.hom h.hom sq.hom_comp_eq.symm rfl :
      C(MappingPathFiber p'.hom b', MappingPathFiber p.hom (h b'))).comp
      (MappingPathFiber.ofFiber p'.hom b') =
      (MappingPathFiber.ofFiber p.hom (h b')).comp (sq.fiberMap b').hom := by
    ext x : 1
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, MappingPathFiber.map_ofFiber]
    congr 1
    apply Subtype.ext
    exact (sq.fiberMap_apply_coe b' x).symm
  exact ⟨fun hm ↦ hof.of_postcomp (hsq_of ▸ hm.comp hof'),
    fun hf ↦ hof'.of_precomp (hsq_of.symm ▸ hof.comp hf)⟩

end TopCat

end CategoryTheory.CommSq

namespace CategoryTheory.IsPullback

open TauCeti TauCeti.TopCat

/-- **Pullback along a Serre fibration is homotopy-cartesian (right leg).** Any categorical pullback
square `IsPullback α p' p h` in `TopCat` whose right vertical map `p` is a Serre fibration is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_right {P E B B' : _root_.TopCat.{u}}
    {α : P ⟶ E} {p' : P ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}
    (hpb : IsPullback α p' p h) (hp : serreFibrations p) :
    hpb.toCommSq.IsHomotopyCartesian := by
  have hc : IsPullback (_root_.TopCat.pullbackSnd h p) (_root_.TopCat.pullbackFst h p) p h :=
    (IsPullback.of_isLimit (_root_.TopCat.pullbackConeIsLimit h p)).flip
  have hcanon : hc.toCommSq.IsHomotopyCartesian := by
    rw [hc.toCommSq.isHomotopyCartesian_iff_forall_fiberMap hp
      (mem_serreFibrations_pullbackFst hp h)]
    intro b'
    have heq : hc.toCommSq.fiberMap b' = (p.fiberPullbackFstIso h b').hom := by
      ext x
      exact (hc.toCommSq.fiberMap_apply_coe b' x).trans
        (_root_.TopCat.Hom.fiberPullbackFstIso_hom_apply_coe p h b' x).symm
    rw [heq, ← mem_weakEquivalences_iff]
    exact MorphismProperty.isomorphisms_le_of_containsIdentities weakEquivalences _ inferInstance
  let e : P ≅ _root_.TopCat.of { q : B' × E // h q.1 = p q.2 } :=
    Limits.IsLimit.conePointUniqueUpToIso hpb.flip.isLimit (_root_.TopCat.pullbackConeIsLimit h p)
  have he_snd : e.hom ≫ _root_.TopCat.pullbackSnd h p = α :=
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp hpb.flip.isLimit
      (_root_.TopCat.pullbackConeIsLimit h p) Limits.WalkingCospan.right
  have he_fst : e.hom ≫ _root_.TopCat.pullbackFst h p = p' :=
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp hpb.flip.isLimit
      (_root_.TopCat.pullbackConeIsLimit h p) Limits.WalkingCospan.left
  have hcomp : HomotopyPullback.liftStrict hpb.toCommSq.hom_comp_eq =
      (HomotopyPullback.liftStrict hc.toCommSq.hom_comp_eq).comp e.hom.hom := by
    ext x : 1
    have hs : α.hom x = (_root_.TopCat.pullbackSnd h p).hom (e.hom.hom x) := by
      simpa [_root_.TopCat.hom_comp] using
        (ContinuousMap.congr_fun (congrArg _root_.TopCat.Hom.hom he_snd) x).symm
    have hf : p'.hom x = (_root_.TopCat.pullbackFst h p).hom (e.hom.hom x) := by
      simpa [_root_.TopCat.hom_comp] using
        (ContinuousMap.congr_fun (congrArg _root_.TopCat.Hom.hom he_fst) x).symm
    exact HomotopyPullback.ext (by simpa using hs) (by simpa using hf)
      fun _ ↦ by simpa using congrArg p.hom hs
  have he : e.hom.hom.IsWeakHomotopyEquivalence := by
    convert (_root_.TopCat.homeoOfIso e).isWeakHomotopyEquivalence using 1
    ext x : 1; exact (_root_.TopCat.homeoOfIso_apply e x).symm
  change (HomotopyPullback.liftStrict hpb.toCommSq.hom_comp_eq).IsWeakHomotopyEquivalence
  exact hcomp ▸ hcanon.comp he

/-- **Pullback along a Serre fibration is homotopy-cartesian (left leg).** Any categorical pullback
square `IsPullback α p' p h` in `TopCat` whose bottom map `h` is a Serre fibration is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_left {P E B B' : _root_.TopCat.{u}}
    {α : P ⟶ E} {p' : P ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}
    (hpb : IsPullback α p' p h) (hh : serreFibrations h) :
    hpb.toCommSq.IsHomotopyCartesian :=
  (hpb.flip.isHomotopyCartesian_of_right hh).flip

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
    ext x : 1
    exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp
  exact hcomp ▸ (hc.isHomotopyCartesian_of_right hp).comp
    (Homeomorph.pullbackComm ⇑p.hom ⇑g.hom).isWeakHomotopyEquivalence

/-- **Strict-to-homotopy pullback comparison along a Serre fibration (right leg).** When
`q : C ⟶ B` is a Serre fibration in `TopCat` and `f : A ⟶ B` is any morphism,
`HomotopyPullback.ofPullback f.hom q.hom` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_of_right {A B C : _root_.TopCat.{u}}
    (f : A ⟶ B) {q : C ⟶ B} (hq : serreFibrations q) :
    (HomotopyPullback.ofPullback f.hom q.hom).IsWeakHomotopyEquivalence := by
  have hcomp : HomotopyPullback.ofPullback f.hom q.hom =
      (HomotopyPullback.swap q.hom f.hom).comp
        ((HomotopyPullback.ofPullback q.hom f.hom).comp
          (Homeomorph.pullbackComm ⇑f.hom ⇑q.hom : C(_, _))) := by
    ext x : 1; exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp [x.2]
  exact hcomp ▸ (HomotopyPullback.isWeakHomotopyEquivalence_swap q.hom f.hom).comp
    ((isWeakHomotopyEquivalence_ofPullback_of_left hq f).comp
      (Homeomorph.pullbackComm ⇑f.hom ⇑q.hom).isWeakHomotopyEquivalence)

/-- When the right vertical map `p : E ⟶ B` is a Serre fibration, a commutative square
`sq : CommSq α p' p h` in `TopCat` is homotopy-cartesian if and only if the induced map into the
strict pullback `TopCat.pullbackCone h p` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_pullbackLift {E B E' B' : _root_.TopCat.{u}}
    {α : E' ⟶ E} {p' : E' ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}
    (sq : CommSq α p' p h) (hp : serreFibrations p) :
    sq.IsHomotopyCartesian ↔
      ((_root_.TopCat.pullbackConeIsLimit h p).lift
        (Limits.PullbackCone.mk p' α sq.w.symm)).hom.IsWeakHomotopyEquivalence := by
  let hc : IsPullback (_root_.TopCat.pullbackSnd h p) (_root_.TopCat.pullbackFst h p) p h :=
    (IsPullback.of_isLimit (_root_.TopCat.pullbackConeIsLimit h p)).flip
  let φ : E' ⟶ _root_.TopCat.of { q : B' × E // h q.1 = p q.2 } :=
    (_root_.TopCat.pullbackConeIsLimit h p).lift (Limits.PullbackCone.mk p' α sq.w.symm)
  have hφ_fst : φ ≫ _root_.TopCat.pullbackFst h p = p' :=
    (_root_.TopCat.pullbackConeIsLimit h p).fac _ Limits.WalkingCospan.left
  have hφ_snd : φ ≫ _root_.TopCat.pullbackSnd h p = α :=
    (_root_.TopCat.pullbackConeIsLimit h p).fac _ Limits.WalkingCospan.right
  have hcartR := hc.isHomotopyCartesian_of_right hp
  have hcomp : HomotopyPullback.liftStrict sq.hom_comp_eq =
      (HomotopyPullback.liftStrict hc.toCommSq.hom_comp_eq).comp φ.hom := by
    ext x : 1
    have hs : α.hom x = (_root_.TopCat.pullbackSnd h p).hom (φ.hom x) := by
      simpa [_root_.TopCat.hom_comp] using
        (ContinuousMap.congr_fun (congrArg _root_.TopCat.Hom.hom hφ_snd) x).symm
    have hf : p'.hom x = (_root_.TopCat.pullbackFst h p).hom (φ.hom x) := by
      simpa [_root_.TopCat.hom_comp] using
        (ContinuousMap.congr_fun (congrArg _root_.TopCat.Hom.hom hφ_fst) x).symm
    exact HomotopyPullback.ext (by simpa using hs) (by simpa using hf)
      fun _ ↦ by simpa using congrArg p.hom hs
  change (HomotopyPullback.liftStrict sq.hom_comp_eq).IsWeakHomotopyEquivalence ↔
    φ.hom.IsWeakHomotopyEquivalence
  rw [hcomp]
  exact ⟨hcartR.of_postcomp, hcartR.comp⟩

end TauCeti.TopCat
