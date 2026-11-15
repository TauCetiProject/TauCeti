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
# Homotopy-cartesian squares, Serre pullbacks, and pasting

Consider a homotopy-commutative square of topological spaces

```
E' --α--> E
|         |
p'        p
v         v
B' --h--> B
```

witnessed by a homotopy `H : (p.comp α).Homotopy (h.comp p')`. By the universal property of the
homotopy pullback (`TauCeti.HomotopyPullback.lift`), such a square corresponds to a canonical
comparison map `E' → HomotopyPullback p h`. The square is **homotopy-cartesian**
(`ContinuousMap.Homotopy.IsHomotopyCartesian`) when this comparison map is a weak homotopy
equivalence. Strictly commuting squares `p.comp α = h.comp p'` (and `CategoryTheory.CommSq` in
`TopCat`) inherit this predicate via `TauCeti.HomotopyPullback.liftStrict`.

Because `E, B, E', B'` may live in four independent universes, the homotopy-fibre and pasting
characterizations cannot rely on placing all four spaces inside a single `TopCat.{u}`. Instead, we
factor `lift α p' H` up to homotopy through the mapping-path replacement `MappingPathSpace p'`,
which maps to `HomotopyPullback p h` over `B'` as a morphism between Hurewicz fibrations
(`MappingPathSpace.endpoint p'` and `HomotopyPullback.snd p h`). Applying the universe-polymorphic
fibrewise criterion `TauCeti.IsHurewiczFibration.isWeakHomotopyEquivalence_iff_forall_fiberMap`
shows that `H` is homotopy-cartesian if and only if, for every `b' : B'`, the induced map
`H.mappingPathFiberSqMap b' : MappingPathFiber p' b' → MappingPathFiber p (h b')` on mapping-path
fibres is a weak homotopy equivalence
(`ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber`).

From this characterization we deduce:
* **Homotopy base change of weak homotopy equivalences**
  (`TauCeti.HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right`,
  `TauCeti.HomotopyPullback.isWeakHomotopyEquivalence_snd_of_left`): if one leg of a cospan is a
  weak homotopy equivalence, the opposite projection from the homotopy pullback is a weak homotopy
  equivalence; consequently a square over a weak homotopy equivalence on the bottom is
  homotopy-cartesian if and only if its top map is a weak homotopy equivalence.
* **Strict vs. homotopy pullbacks along Serre and Hurewicz fibrations**: when `p : E ⟶ B` in
  `TopCat` is a Serre fibration, the constant-path inclusion `ofPullback p.hom h.hom` from the
  strict pullback to `HomotopyPullback p.hom h.hom` is a weak homotopy equivalence, every
  categorical pullback square along `p` is homotopy-cartesian, and a square of Serre fibrations is
  homotopy-cartesian if and only if the induced map on every strict fibre is a weak homotopy
  equivalence.
* **Horizontal and vertical pasting** (`ContinuousMap.Homotopy.isHomotopyCartesian_hcompSq_iff`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_vcompSq_iff`, and their strict counterparts): when the
  right (respectively bottom) square is homotopy-cartesian, the pasted rectangle is
  homotopy-cartesian if and only if the left (respectively top) square is homotopy-cartesian.

## Main declarations

* `ContinuousMap.Homotopy.IsHomotopyCartesian`: homotopy-cartesianness of a homotopy-commutative
  square `H : (p.comp α).Homotopy (h.comp p')`.
* `TauCeti.IsHomotopyCartesian` and `CategoryTheory.CommSq.IsHomotopyCartesian`: strict-square
  specializations.
* `ContinuousMap.Homotopy.mappingPathFiberSqMap` and
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_forall_mappingPathFiber`: characterization on
  mapping-path fibres over every `b' : B'`.
* `TauCeti.IsHomotopyCartesian.iff_forall_mappingPathFiber`: the strict-square mapping-path fibre
  criterion in terms of `MappingPathFiber.map`.
* `TauCeti.HomotopyPullback.isWeakHomotopyEquivalence_fst_of_right` and
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_top_of_bottom`: stability of weak homotopy
  equivalences under homotopy pullback.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_ofPullback_of_left`,
  `CategoryTheory.IsPullback.isHomotopyCartesian_of_right`, and
  `CategoryTheory.CommSq.isHomotopyCartesian_iff_forall_fiberMap`: strict pullbacks and squares of
  Serre fibrations in `TopCat`.
* `ContinuousMap.Homotopy.hcompSq`, `ContinuousMap.Homotopy.vcompSq`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_hcompSq_iff`, and
  `ContinuousMap.Homotopy.isHomotopyCartesian_vcompSq_iff`: horizontal and vertical pasting and
  right/top cancellation of homotopy-cartesian squares.

## References

* M. Mather, *Pull-backs in homotopy theory*, Canadian Journal of Mathematics 28 (1976), 225–263.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval

universe u v u' v' u'' v'' w

/-! ### Auxiliary weak-equivalence and path-family lemmas -/

namespace TauCeti

/-- Reparametrizing a continuously varying family of paths with varying endpoints by a fixed
endpoint-preserving map `f : I → I` varies continuously with the homotopy parameter in `I`. -/
private theorem reparamHomotopy_continuous_family {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] {x y : A → X}
    (γ : ∀ a, Path (x a) (y a)) (hγ : Continuous ↿γ)
    {f : I → I} (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Continuous ↿fun q : I × A ↦
      (Path.Homotopy.reparam (γ q.2) f hf hf₀ hf₁).eval q.1 := by
  have h : Continuous (fun q : (I × A) × I ↦
      γ q.1.2 ⟨σ q.1.1 * q.2 + q.1.1 * f q.2,
        show (σ q.1.1 : ℝ) • (q.2 : ℝ) + (q.1.1 : ℝ) • (f q.2 : ℝ) ∈ I from
          convex_Icc _ _ q.2.2 (f q.2).2 (by unit_interval) (by unit_interval) (by simp)⟩) :=
    hγ.comp ((continuous_snd.comp continuous_fst).prodMk <|
      (by fun_prop : Continuous fun q : (I × A) × I ↦
        (σ q.1.1 : ℝ) * (q.2 : ℝ) + (q.1.1 : ℝ) * (f q.2 : ℝ)).subtype_mk _)
  exact h

/-- Conjugating a continuous map by homeomorphisms preserves and reflects weak homotopy
equivalences. -/
private theorem isWeakHomotopyEquivalence_conj_homeomorph_iff {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (eX : X' ≃ₜ X) (eY : Y ≃ₜ Y') (φ : C(X, Y)) :
    (eY.toHomotopyEquiv.toFun.comp
      (φ.comp eX.toHomotopyEquiv.toFun)).IsWeakHomotopyEquivalence ↔
      φ.IsWeakHomotopyEquivalence := by
  have heX := eX.toHomotopyEquiv.isWeakHomotopyEquivalence
  have heY := eY.toHomotopyEquiv.isWeakHomotopyEquivalence
  exact ⟨fun h ↦ heX.of_precomp (heY.of_postcomp h), fun h ↦ heY.comp (h.comp heX)⟩

/-- `HomotopyPullback.swap` is a weak homotopy equivalence. -/
theorem HomotopyPullback.isWeakHomotopyEquivalence_swap {A : Type u} {B : Type v} {C : Type u'}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(C, B)) :
    (HomotopyPullback.swap f g).IsWeakHomotopyEquivalence := by
  convert (HomotopyPullback.swapHomeomorph f g).toHomotopyEquiv.isWeakHomotopyEquivalence using 1
  ext x : 1
  exact (HomotopyPullback.swapHomeomorph_apply f g x).symm

/-- `MappingPathSpace.incl` is a weak homotopy equivalence. -/
theorem MappingPathSpace.isWeakHomotopyEquivalence_incl {B : Type u} {K : Type v}
    [TopologicalSpace B] [TopologicalSpace K] (f : C(B, K)) :
    (MappingPathSpace.incl f).IsWeakHomotopyEquivalence := by
  convert (MappingPathSpace.homotopyEquiv f).isWeakHomotopyEquivalence using 1
  ext x : 1
  exact (MappingPathSpace.homotopyEquiv_apply f x).symm

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
        (H.continuous.comp (continuous_snd.prodMk continuous_fst))
        hφ hφ₀ hφ₁
    map_zero_left e' := by
      apply Subtype.ext
      rw [HomotopyPullback.lift_val]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      ext t : 1
      have h0 : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 0 =
          H.evalAt e' := by simp
      exact congrArg (fun γ : Path (p (α e')) (h (p' e')) ↦ γ t) h0
    map_one_left e' := by
      apply Subtype.ext
      change (α e', p' e',
          ((Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1).toContinuousMap) =
        (H.mappingPathReplacementLift (MappingPathSpace.incl p' e')).val
      rw [mappingPathReplacementLift_val]
      refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
      ext t : 1
      have h1 : (Path.Homotopy.reparam (H.evalAt e') φ hφ hφ₀ hφ₁).eval 1 =
          (H.evalAt e').reparam φ hφ hφ₀ hφ₁ := by simp
      have hrep := (Path.Homotopy.trans_refl_reparam (H.evalAt e')).symm
      have hlhs := congrArg (fun γ : Path (p (α e')) (h (p' e')) ↦ γ t) (h1.trans hrep)
      exact hlhs.trans (by simp [Path.trans_apply]) }⟩

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
  have hconj : H.mappingPathFiberSqMap b' =
      (HomotopyPullback.sndFiberHomeomorph p h b').toHomotopyEquiv.toFun.comp
        ((fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b').comp
          (MappingPathFiber.endpointHomeomorph p' b').toHomotopyEquiv.toFun) := by
    ext q : 1
    apply Subtype.ext
    let x : (HomotopyPullback.snd p h) ⁻¹' {b'} :=
      fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b'
        (MappingPathFiber.endpointHomeomorph p' b' q)
    change (H.mappingPathFiberSqMap b' q).val =
      (HomotopyPullback.sndFiberHomeomorph p h b' x).val
    rw [HomotopyPullback.sndFiberHomeomorph_val]
    refine Prod.ext (by simp [x]) ?_
    ext t : 1
    simp [x, Path.trans_apply]
  rw [hconj]
  exact (isWeakHomotopyEquivalence_conj_homeomorph_iff
    (MappingPathFiber.endpointHomeomorph p' b')
    (HomotopyPullback.sndFiberHomeomorph p h b')
    (fiberMap H.mappingPathReplacementLift H.snd_comp_mappingPathReplacementLift b')).symm

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
  have hend : (MappingPathSpace.endpoint g).IsWeakHomotopyEquivalence := by
    have hcomp :
        ((MappingPathSpace.endpoint g).comp
          (MappingPathSpace.incl g)).IsWeakHomotopyEquivalence := by
      rwa [MappingPathSpace.endpoint_comp_incl]
    exact hincl.of_precomp hcomp
  have hp_end : IsHurewiczFibration.{0} (MappingPathSpace.endpoint g) :=
    MappingPathSpace.isHurewiczFibration_endpoint g
  have hp_idB : IsHurewiczFibration.{0} (ContinuousMap.id B) :=
    (Homeomorph.refl B).isHurewiczFibration
  have hp_fst : IsHurewiczFibration.{0} (fst f g) := isHurewiczFibration_fst f g
  have hp_idA : IsHurewiczFibration.{0} (ContinuousMap.id A) :=
    (Homeomorph.refl A).isHurewiczFibration
  have hend_fib : ∀ b : B,
      (fiberMap (MappingPathSpace.endpoint g)
        (ContinuousMap.id_comp _) b).IsWeakHomotopyEquivalence :=
    (hp_end.isWeakHomotopyEquivalence_iff_forall_fiberMap hp_idB
      (ContinuousMap.id_comp _)).mp hend
  rw [hp_fst.isWeakHomotopyEquivalence_iff_forall_fiberMap hp_idA (ContinuousMap.id_comp _)]
  intro a
  let eDom : (MappingPathSpace.endpoint g) ⁻¹' {f a} ≃ₜ (fst f g) ⁻¹' {a} :=
    (MappingPathFiber.endpointHomeomorph g (f a)).symm.trans (fstFiberHomeomorph f g a).symm
  let eCod : ((ContinuousMap.id A) ⁻¹' {a}) ≃ₜ ((ContinuousMap.id B) ⁻¹' {f a}) :=
    { toFun _ := ⟨f a, rfl⟩
      invFun _ := ⟨a, rfl⟩
      left_inv x := Subtype.ext x.2.symm
      right_inv y := Subtype.ext y.2.symm
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  have hconj : eCod.toHomotopyEquiv.toFun.comp
      ((fiberMap (fst f g) (ContinuousMap.id_comp _) a).comp eDom.toHomotopyEquiv.toFun) =
      fiberMap (MappingPathSpace.endpoint g) (ContinuousMap.id_comp _) (f a) := by
    ext x : 1
    apply Subtype.ext
    exact (fiberMap (MappingPathSpace.endpoint g) (ContinuousMap.id_comp _) (f a) x).2.symm
  exact (isWeakHomotopyEquivalence_conj_homeomorph_iff eDom eCod
    (fiberMap (fst f g) (ContinuousMap.id_comp _) a)).mp (hconj ▸ hend_fib (f a))

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

/-! ### Horizontal and vertical pasting of homotopy-commutative squares -/

section Pasting

/-- **Horizontal pasting of homotopy-commutative squares.** Given
`H : (p.comp α).Homotopy (h.comp p')` on the right and `H' : (p'.comp α').Homotopy (h'.comp p'')`
on the left, concatenate `H` at `α' x` with `h` applied to `H'` at `x`. -/
noncomputable def hcompSq
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    (H : (p.comp α).Homotopy (h.comp p')) (H' : (p'.comp α').Homotopy (h'.comp p'')) :
    (p.comp (α.comp α')).Homotopy ((h.comp h').comp p'') where
  toFun q := ((H.evalAt (α' q.2)).trans ((H'.evalAt q.2).map h.continuous)) q.1
  continuous_toFun := by
    have hfam := Path.trans_continuous_family
      (fun e'' : E'' ↦ H.evalAt (α' e''))
      (H.continuous.comp (continuous_snd.prodMk (α'.continuous.comp continuous_fst)))
      (fun e'' : E'' ↦ (H'.evalAt e'').map h.continuous)
      (h.continuous.comp (H'.continuous.comp (continuous_snd.prodMk continuous_fst)))
    exact hfam.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left e'' := Path.source _
  map_one_left e'' := Path.target _

@[simp]
theorem hcompSq_evalAt
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    (H : (p.comp α).Homotopy (h.comp p')) (H' : (p'.comp α').Homotopy (h'.comp p''))
    (e'' : E'') :
    (H.hcompSq H').evalAt e'' =
      (H.evalAt (α' e'')).trans ((H'.evalAt e'').map h.continuous) :=
  Path.ext rfl

/-- On mapping-path fibres over `b'' : B''`, the map induced by the horizontal paste `H.hcompSq H'`
is homotopic to `(H.mappingPathFiberSqMap (h' b'')).comp (H'.mappingPathFiberSqMap b'')` by path
associativity. -/
theorem mappingPathFiberSqMap_comp_homotopic_hcompSq
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    (H : (p.comp α).Homotopy (h.comp p')) (H' : (p'.comp α').Homotopy (h'.comp p''))
    (b'' : B'') :
    ((H.mappingPathFiberSqMap (h' b'')).comp (H'.mappingPathFiberSqMap b'')).Homotopic
      ((H.hcompSq H').mappingPathFiberSqMap b'') := by
  let φ : I → I := fun t ↦
    ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩
  have hφ : Continuous φ := by fun_prop
  have hφ₀ : φ 0 = 0 := Subtype.ext Path.Homotopy.transAssocReparamAux_zero
  have hφ₁ : φ 1 = 1 := Subtype.ext Path.Homotopy.transAssocReparamAux_one
  let P₁ (q : MappingPathFiber p'' b'') : Path (p (α (α' q.val.1))) (h (p' (α' q.val.1))) :=
    H.evalAt (α' q.val.1)
  let P₂ (q : MappingPathFiber p'' b'') : Path (h (p' (α' q.val.1))) (h (h' (p'' q.val.1))) :=
    (H'.evalAt q.val.1).map h.continuous
  let P₃ (q : MappingPathFiber p'' b'') : Path (h (h' (p'' q.val.1))) (h (h' b'')) :=
    (⟨q.val.2, q.property.1, q.property.2⟩ : Path (p'' q.val.1) b'').map (h.comp h').continuous
  have hP₁ : Continuous ↿P₁ := H.continuous.comp
    (continuous_snd.prodMk (α'.continuous.comp (continuous_subtype_val.fst.comp continuous_fst)))
  have hP₂ : Continuous ↿P₂ := h.continuous.comp
    (H'.continuous.comp (continuous_snd.prodMk (continuous_subtype_val.fst.comp continuous_fst)))
  have hP₃ : Continuous ↿P₃ := (h.comp h').continuous.comp
    ((continuous_subtype_val.snd.comp continuous_fst).eval continuous_snd)
  have hP₂₃ : Continuous ↿fun q ↦ (P₂ q).trans (P₃ q) :=
    Path.trans_continuous_family P₂ hP₂ P₃ hP₃
  have hP₁₂₃ : Continuous ↿fun q ↦ (P₁ q).trans ((P₂ q).trans (P₃ q)) :=
    Path.trans_continuous_family P₁ hP₁ _ hP₂₃
  refine ⟨{
    toFun r := ⟨(α (α' r.2.val.1),
      ((Path.Homotopy.reparam ((P₁ r.2).trans ((P₂ r.2).trans (P₃ r.2)))
        φ hφ hφ₀ hφ₁).eval r.1).toContinuousMap),
      Path.source _, Path.target _⟩
    continuous_toFun := by
      refine (((α.comp α').continuous.comp
        (continuous_subtype_val.fst.comp continuous_snd)).prodMk ?_).subtype_mk _
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact reparamHomotopy_continuous_family
        (fun q : MappingPathFiber p'' b'' ↦ (P₁ q).trans ((P₂ q).trans (P₃ q)))
        hP₁₂₃ hφ hφ₀ hφ₁
    map_zero_left q := by
      apply Subtype.ext
      refine Prod.ext (by simp) ?_
      ext t : 1
      have h0 : (Path.Homotopy.reparam ((P₁ q).trans ((P₂ q).trans (P₃ q)))
          φ hφ hφ₀ hφ₁).eval 0 = (P₁ q).trans ((P₂ q).trans (P₃ q)) := by simp
      change ((Path.Homotopy.reparam ((P₁ q).trans ((P₂ q).trans (P₃ q)))
          φ hφ hφ₀ hφ₁).eval 0) t =
        (H.mappingPathFiberSqMap (h' b'') (H'.mappingPathFiberSqMap b'' q)).val.2 t
      rw [h0, mappingPathFiberSqMap_val_snd_apply]
      have hmap : (((H'.evalAt q.val.1).trans
          ((⟨q.val.2, q.property.1, q.property.2⟩ : Path (p'' q.val.1) b'').map
            h'.continuous)).map h.continuous) = (P₂ q).trans (P₃ q) := by
        apply Path.ext
        funext s
        simp [P₂, P₃, Path.trans_apply]
      change ((P₁ q).trans ((P₂ q).trans (P₃ q))) t =
        ((P₁ q).trans (((H'.evalAt q.val.1).trans
          ((⟨q.val.2, q.property.1, q.property.2⟩ : Path (p'' q.val.1) b'').map
            h'.continuous)).map h.continuous)) t
      rw [hmap]
    map_one_left q := by
      apply Subtype.ext
      refine Prod.ext (by simp) ?_
      ext t : 1
      have h1 : (Path.Homotopy.reparam ((P₁ q).trans ((P₂ q).trans (P₃ q)))
          φ hφ hφ₀ hφ₁).eval 1 =
          ((P₁ q).trans ((P₂ q).trans (P₃ q))).reparam φ hφ hφ₀ hφ₁ := by simp
      change ((Path.Homotopy.reparam ((P₁ q).trans ((P₂ q).trans (P₃ q)))
          φ hφ hφ₀ hφ₁).eval 1) t =
        ((H.hcompSq H').mappingPathFiberSqMap b'' q).val.2 t
      rw [h1, ← Path.Homotopy.trans_assoc_reparam, mappingPathFiberSqMap_val_snd_apply,
        hcompSq_evalAt] }⟩

/-- **Horizontal pasting and cancellation of homotopy-cartesian squares.** When the right square
`H : (p.comp α).Homotopy (h.comp p')` is homotopy-cartesian, the horizontally pasted rectangle
`H.hcompSq H'` is homotopy-cartesian if and only if the left square
`H' : (p'.comp α').Homotopy (h'.comp p'')` is homotopy-cartesian. -/
theorem isHomotopyCartesian_hcompSq_iff
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    {H : (p.comp α).Homotopy (h.comp p')} (hH : H.IsHomotopyCartesian)
    (H' : (p'.comp α').Homotopy (h'.comp p'')) :
    (H.hcompSq H').IsHomotopyCartesian ↔ H'.IsHomotopyCartesian := by
  rw [isHomotopyCartesian_iff_forall_mappingPathFiber,
    isHomotopyCartesian_iff_forall_mappingPathFiber]
  have hH_fib := (isHomotopyCartesian_iff_forall_mappingPathFiber H).mp hH
  refine forall_congr' fun b'' ↦ ?_
  have hhom := H.mappingPathFiberSqMap_comp_homotopic_hcompSq H' b''
  exact ⟨fun hcomp ↦ (hH_fib (h' b'')).of_postcomp (hcomp.of_homotopic hhom.symm),
    fun h'fib ↦ ((hH_fib (h' b'')).comp h'fib).of_homotopic hhom⟩

/-- Horizontal pasting of two homotopy-cartesian squares is homotopy-cartesian. -/
theorem IsHomotopyCartesian.hcompSq
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    {H : (p.comp α).Homotopy (h.comp p')} {H' : (p'.comp α').Homotopy (h'.comp p'')}
    (hH : H.IsHomotopyCartesian) (hH' : H'.IsHomotopyCartesian) :
    (H.hcompSq H').IsHomotopyCartesian :=
  (isHomotopyCartesian_hcompSq_iff hH H').mpr hH'

/-- Right cancellation for horizontal pasting: if the right square `H` and the outer rectangle
`H.hcompSq H'` are homotopy-cartesian, then the left square `H'` is homotopy-cartesian. -/
theorem IsHomotopyCartesian.of_hcompSq
    {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'} {E'' : Type u''} {B'' : Type v''}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace E''] [TopologicalSpace B'']
    {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    {H : (p.comp α).Homotopy (h.comp p')} {H' : (p'.comp α').Homotopy (h'.comp p'')}
    (hH : H.IsHomotopyCartesian) (hHH' : (H.hcompSq H').IsHomotopyCartesian) :
    H'.IsHomotopyCartesian :=
  (isHomotopyCartesian_hcompSq_iff hH H').mp hHH'

/-- **Vertical pasting of homotopy-commutative squares.** Given a bottom square
`H : (p.comp α').Homotopy (h.comp p')` and a top square
`H' : (q.comp α'').Homotopy (α'.comp q')`, concatenate `p` applied to `H'` with `H` at `q'`. -/
noncomputable def vcompSq
    {E : Type u} {M : Type u'} {B : Type v} {E' : Type u''} {M' : Type w} {B' : Type v'}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace M'] [TopologicalSpace B']
    {α' : C(M', M)} {p : C(M, B)} {p' : C(M', B')} {h : C(B', B)}
    {α'' : C(E', E)} {q : C(E, M)} {q' : C(E', M')}
    (H : (p.comp α').Homotopy (h.comp p')) (H' : (q.comp α'').Homotopy (α'.comp q')) :
    ((p.comp q).comp α'').Homotopy (h.comp (p'.comp q')) :=
  (H.symm.hcompSq H'.symm).symm

@[simp]
theorem vcompSq_evalAt
    {E : Type u} {M : Type u'} {B : Type v} {E' : Type u''} {M' : Type w} {B' : Type v'}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace M'] [TopologicalSpace B']
    {α' : C(M', M)} {p : C(M, B)} {p' : C(M', B')} {h : C(B', B)}
    {α'' : C(E', E)} {q : C(E, M)} {q' : C(E', M')}
    (H : (p.comp α').Homotopy (h.comp p')) (H' : (q.comp α'').Homotopy (α'.comp q'))
    (e' : E') :
    (H.vcompSq H').evalAt e' =
      ((H'.evalAt e').map p.continuous).trans (H.evalAt (q' e')) := by
  apply Path.ext
  funext t
  change ((H.symm.hcompSq H'.symm).evalAt e').symm t = _
  rw [hcompSq_evalAt, Path.trans_symm]
  simp [Path.trans_apply, unitInterval.symm_symm]

/-- **Vertical pasting and cancellation of homotopy-cartesian squares.** When the bottom square
`H : (p.comp α').Homotopy (h.comp p')` is homotopy-cartesian, the vertically pasted rectangle
`H.vcompSq H'` is homotopy-cartesian if and only if the top square
`H' : (q.comp α'').Homotopy (α'.comp q')` is homotopy-cartesian. -/
theorem isHomotopyCartesian_vcompSq_iff
    {E : Type u} {M : Type u'} {B : Type v} {E' : Type u''} {M' : Type w} {B' : Type v'}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace M'] [TopologicalSpace B']
    {α' : C(M', M)} {p : C(M, B)} {p' : C(M', B')} {h : C(B', B)}
    {α'' : C(E', E)} {q : C(E, M)} {q' : C(E', M')}
    {H : (p.comp α').Homotopy (h.comp p')} (hH : H.IsHomotopyCartesian)
    (H' : (q.comp α'').Homotopy (α'.comp q')) :
    (H.vcompSq H').IsHomotopyCartesian ↔ H'.IsHomotopyCartesian := by
  rw [vcompSq, isHomotopyCartesian_symm_iff, isHomotopyCartesian_hcompSq_iff hH.symm,
    isHomotopyCartesian_symm_iff]

/-- Vertical pasting of two homotopy-cartesian squares is homotopy-cartesian. -/
theorem IsHomotopyCartesian.vcompSq
    {E : Type u} {M : Type u'} {B : Type v} {E' : Type u''} {M' : Type w} {B' : Type v'}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace M'] [TopologicalSpace B']
    {α' : C(M', M)} {p : C(M, B)} {p' : C(M', B')} {h : C(B', B)}
    {α'' : C(E', E)} {q : C(E, M)} {q' : C(E', M')}
    {H : (p.comp α').Homotopy (h.comp p')} {H' : (q.comp α'').Homotopy (α'.comp q')}
    (hH : H.IsHomotopyCartesian) (hH' : H'.IsHomotopyCartesian) :
    (H.vcompSq H').IsHomotopyCartesian :=
  (isHomotopyCartesian_vcompSq_iff hH H').mpr hH'

/-- Bottom cancellation for vertical pasting: if the bottom square `H` and the outer vertical
rectangle `H.vcompSq H'` are homotopy-cartesian, then the top square `H'` is homotopy-cartesian. -/
theorem IsHomotopyCartesian.of_vcompSq
    {E : Type u} {M : Type u'} {B : Type v} {E' : Type u''} {M' : Type w} {B' : Type v'}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace M'] [TopologicalSpace B']
    {α' : C(M', M)} {p : C(M, B)} {p' : C(M', B')} {h : C(B', B)}
    {α'' : C(E', E)} {q : C(E, M)} {q' : C(E', M')}
    {H : (p.comp α').Homotopy (h.comp p')} {H' : (q.comp α'').Homotopy (α'.comp q')}
    (hH : H.IsHomotopyCartesian) (hHH' : (H.vcompSq H').IsHomotopyCartesian) :
    H'.IsHomotopyCartesian :=
  (isHomotopyCartesian_vcompSq_iff hH H').mp hHH'

end Pasting

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
    ext x : 1
    apply Subtype.ext
    rw [HomotopyPullback.liftStrict_val, HomotopyPullback.lift_val]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    ext _ : 1
    rfl
  rw [IsHomotopyCartesian, ContinuousMap.Homotopy.IsHomotopyCartesian, heq]

theorem IsHomotopyCartesian.symm {hcomm : p.comp α = h.comp p'}
    (hcart : IsHomotopyCartesian hcomm) : IsHomotopyCartesian hcomm.symm := by
  have heq : HomotopyPullback.liftStrict hcomm.symm =
      (HomotopyPullback.swap p h).comp (HomotopyPullback.liftStrict hcomm) := by
    ext x : 1
    apply Subtype.ext
    rw [ContinuousMap.comp_apply, HomotopyPullback.liftStrict_val, HomotopyPullback.swap_val,
      HomotopyPullback.liftStrict_val]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    ext _ : 1
    exact (ContinuousMap.congr_fun hcomm x).symm
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
      apply Subtype.ext
      refine Prod.ext (by simp) ?_
      ext t : 1
      change (Path.delayReflLeft 0 (γ q)) t =
        (((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).mappingPathFiberSqMap
          b' q).val.2 t
      rw [Path.delayReflLeft_zero, ContinuousMap.Homotopy.mappingPathFiberSqMap_val_snd_apply]
      simp [γ, Path.trans_apply]
    map_one_left q := by
      apply Subtype.ext
      refine Prod.ext (by simp [MappingPathFiber.map_val]) ?_
      ext t : 1
      change (Path.delayReflLeft 1 (γ q)) t =
        (MappingPathFiber.map α h hcomm.symm rfl q).val.2 t
      rw [Path.delayReflLeft_one, MappingPathFiber.map_val]
      rfl }⟩

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

/-- **Horizontal pasting of strict squares.** When the right strict square
`hcomm : p.comp α = h.comp p'` is homotopy-cartesian, the composite rectangle with
`hcomm' : p'.comp α' = h'.comp p''` on the left is homotopy-cartesian iff `hcomm'` is. -/
theorem isHomotopyCartesian_hcomp_iff
    {E'' : Type u''} {B'' : Type v''} [TopologicalSpace E''] [TopologicalSpace B'']
    {α' : C(E'', E')} {p'' : C(E'', B'')} {h' : C(B'', B')}
    {hcomm : p.comp α = h.comp p'} (hcart : IsHomotopyCartesian hcomm)
    (hcomm' : p'.comp α' = h'.comp p'') :
    IsHomotopyCartesian
        (show p.comp (α.comp α') = (h.comp h').comp p'' by
          rw [← ContinuousMap.comp_assoc, hcomm, ContinuousMap.comp_assoc, hcomm',
            ← ContinuousMap.comp_assoc]) ↔
      IsHomotopyCartesian hcomm' := by
  let houter : p.comp (α.comp α') = (h.comp h').comp p'' := by
    rw [← ContinuousMap.comp_assoc, hcomm, ContinuousMap.comp_assoc, hcomm',
      ← ContinuousMap.comp_assoc]
  change IsHomotopyCartesian houter ↔ IsHomotopyCartesian hcomm'
  rw [IsHomotopyCartesian.iff_forall_mappingPathFiber,
    IsHomotopyCartesian.iff_forall_mappingPathFiber]
  have hfib := (IsHomotopyCartesian.iff_forall_mappingPathFiber hcomm).mp hcart
  refine forall_congr' fun b'' ↦ ?_
  have hcomp : (MappingPathFiber.map α h hcomm.symm rfl :
      C(MappingPathFiber p' (h' b''), MappingPathFiber p (h (h' b'')))).comp
      (MappingPathFiber.map α' h' hcomm'.symm rfl) =
      MappingPathFiber.map (α.comp α') (h.comp h') houter.symm rfl := by
    ext q : 1
    apply Subtype.ext
    simp
  rw [← hcomp]
  exact ⟨fun hc ↦ (hfib (h' b'')).of_postcomp hc, fun hc ↦ (hfib (h' b'')).comp hc⟩

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

/-- A commutative square `sq : CommSq α p' p h` in `TopCat` is **homotopy-cartesian** if its
underlying square `p.hom.comp α.hom = h.hom.comp p'.hom` is homotopy-cartesian. -/
def IsHomotopyCartesian (sq : CommSq α p' p h) : Prop :=
  TauCeti.IsHomotopyCartesian (congrArg TopCat.Hom.hom sq.w)

theorem isHomotopyCartesian_iff (sq : CommSq α p' p h) :
    sq.IsHomotopyCartesian ↔ TauCeti.IsHomotopyCartesian (congrArg TopCat.Hom.hom sq.w) :=
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
  have hsq_of : (MappingPathFiber.map α.hom h.hom (congrArg TopCat.Hom.hom sq.w).symm rfl :
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

/-- **Horizontal pasting of commutative squares in `TopCat`.** When the right square `sq₂` is
homotopy-cartesian, the horizontal composite `sq₁.horiz_comp sq₂` is homotopy-cartesian iff the
left square `sq₁` is homotopy-cartesian. -/
theorem isHomotopyCartesian_horiz_comp_iff {E'' B'' : TopCat.{u}}
    {α' : E'' ⟶ E'} {p'' : E'' ⟶ B''} {h' : B'' ⟶ B'}
    (sq₁ : CommSq α' p'' p' h') {sq₂ : CommSq α p' p h} (hsq₂ : sq₂.IsHomotopyCartesian) :
    (sq₁.horiz_comp sq₂).IsHomotopyCartesian ↔ sq₁.IsHomotopyCartesian :=
  TauCeti.isHomotopyCartesian_hcomp_iff hsq₂ (congrArg TopCat.Hom.hom sq₁.w)

/-- **Vertical pasting of commutative squares in `TopCat`.** When the bottom square `sq₂` is
homotopy-cartesian, the vertical composite `sq₁.vert_comp sq₂` is homotopy-cartesian iff the top
square `sq₁` is homotopy-cartesian. -/
theorem isHomotopyCartesian_vert_comp_iff {M M' : TopCat.{u}}
    {α'' : E' ⟶ E} {q' : E' ⟶ M'} {q : E ⟶ M} {α' : M' ⟶ M}
    {pM' : M' ⟶ B'} {pM : M ⟶ B}
    (sq₁ : CommSq α'' q' q α') {sq₂ : CommSq α' pM' pM h}
    (hsq₂ : sq₂.IsHomotopyCartesian) :
    (sq₁.vert_comp sq₂).IsHomotopyCartesian ↔ sq₁.IsHomotopyCartesian := by
  rw [← isHomotopyCartesian_flip_iff, ← sq₁.isHomotopyCartesian_flip_iff]
  exact isHomotopyCartesian_horiz_comp_iff sq₁.flip hsq₂.flip

end TopCat

end CategoryTheory.CommSq

namespace CategoryTheory.IsPullback

open TauCeti TauCeti.TopCat

/-- **Pullback along a Serre fibration is homotopy-cartesian (right leg).** Any categorical pullback
square `IsPullback α p' p h` in `TopCat` whose right vertical map `p` is a Serre fibration is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_right {P E B B' : TopCat.{u}}
    {α : P ⟶ E} {p' : P ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}
    (hpb : IsPullback α p' p h) (hp : serreFibrations p) :
    hpb.toCommSq.IsHomotopyCartesian := by
  have hp' : serreFibrations p' := serreFibrations.of_isPullback hpb hp
  rw [hpb.toCommSq.isHomotopyCartesian_iff_forall_fiberMap hp hp']
  -- Reduce to the explicit `TopCat.pullbackCone` along the limit isomorphism.
  have hc : IsPullback (TopCat.pullbackSnd h p) (TopCat.pullbackFst h p) p h :=
    (IsPullback.of_isLimit (TopCat.pullbackConeIsLimit h p)).flip
  have hcanon : hc.toCommSq.IsHomotopyCartesian := by
    rw [hc.toCommSq.isHomotopyCartesian_iff_forall_fiberMap hp
      (mem_serreFibrations_pullbackFst hp h)]
    intro b'
    have heq : hc.toCommSq.fiberMap b' = (p.fiberPullbackFstIso h b').hom := by
      ext x
      exact (hc.toCommSq.fiberMap_apply_coe b' x).trans
        (TopCat.Hom.fiberPullbackFstIso_hom_apply_coe p h b' x).symm
    rw [heq, ← mem_weakEquivalences_iff]
    exact MorphismProperty.isomorphisms_le_of_containsIdentities weakEquivalences _ inferInstance
  -- Paste with the top isomorphism `P ≅ {q : B' × E // h q.1 = p q.2}` over `B'`.
  let e : P ≅ TopCat.of { q : B' × E // h q.1 = p q.2 } :=
    Limits.IsLimit.conePointUniqueUpToIso hpb.flip.isLimit (TopCat.pullbackConeIsLimit h p)
  have he_snd : e.hom ≫ TopCat.pullbackSnd h p = α :=
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp hpb.flip.isLimit
      (TopCat.pullbackConeIsLimit h p) Limits.WalkingCospan.right
  have he_fst : e.hom ≫ TopCat.pullbackFst h p = p' :=
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp hpb.flip.isLimit
      (TopCat.pullbackConeIsLimit h p) Limits.WalkingCospan.left
  let sqIso : CommSq e.hom p' (TopCat.pullbackFst h p) (𝟙 B') :=
    ⟨he_fst.trans (Category.comp_id p').symm⟩
  have hsqIso : sqIso.IsHomotopyCartesian := by
    rw [CommSq.isHomotopyCartesian_iff, TauCeti.isHomotopyCartesian_iff_homotopy]
    refine ContinuousMap.Homotopy.isHomotopyCartesian_of_horizontal _ ?_ .id
    convert (TopCat.homeoOfIso e).toHomotopyEquiv.isWeakHomotopyEquivalence using 1
    ext p₀ : 1
    exact (TopCat.homeoOfIso_apply e p₀).symm
  have hpasted := (sqIso.isHomotopyCartesian_horiz_comp_iff hcanon).mpr hsqIso
  have hcomm_eq {t : P ⟶ E} {b : B' ⟶ B} (ht : t = α) (hb : b = h) (sq' : CommSq t p' p b) :
      sq'.IsHomotopyCartesian ↔ hpb.toCommSq.IsHomotopyCartesian := by
    subst ht hb
    rfl
  exact (hpb.toCommSq.isHomotopyCartesian_iff_forall_fiberMap hp hp').mp
    ((hcomm_eq he_snd (Category.id_comp h) (sqIso.horiz_comp hc.toCommSq)).mp hpasted)

/-- **Pullback along a Serre fibration is homotopy-cartesian (left leg).** Any categorical pullback
square `IsPullback α p' p h` in `TopCat` whose bottom map `h` is a Serre fibration is
homotopy-cartesian. -/
theorem isHomotopyCartesian_of_left {P E B B' : TopCat.{u}}
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
  have hcart := hc.isHomotopyCartesian_of_right hp
  let eDom : (⇑p.hom).Pullback ⇑g.hom ≃ₜ { q : C × A // g q.1 = p q.2 } :=
    { toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
      invFun y := ⟨(y.1.2, y.1.1), y.2.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _ }
  have heDom := eDom.toHomotopyEquiv.isWeakHomotopyEquivalence
  have hcomp : HomotopyPullback.ofPullback p.hom g.hom =
      (HomotopyPullback.liftStrict
        (congrArg _root_.TopCat.Hom.hom hc.w)).comp eDom.toHomotopyEquiv.toFun := by
    ext x : 1
    apply Subtype.ext
    rw [HomotopyPullback.ofPullback_val, ContinuousMap.comp_apply,
      HomotopyPullback.liftStrict_val]
    rfl
  rw [hcomp]
  exact hcart.comp heDom

/-- **Strict-to-homotopy pullback comparison along a Serre fibration (right leg).** When
`q : C ⟶ B` is a Serre fibration in `TopCat` and `f : A ⟶ B` is any morphism,
`HomotopyPullback.ofPullback f.hom q.hom` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofPullback_of_right {A B C : _root_.TopCat.{u}}
    (f : A ⟶ B) {q : C ⟶ B} (hq : serreFibrations q) :
    (HomotopyPullback.ofPullback f.hom q.hom).IsWeakHomotopyEquivalence := by
  let eDom : (⇑f.hom).Pullback ⇑q.hom ≃ₜ (⇑q.hom).Pullback ⇑f.hom :=
    { toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
      invFun y := ⟨(y.1.2, y.1.1), y.2.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _ }
  have heDom := eDom.toHomotopyEquiv.isWeakHomotopyEquivalence
  have hswap := HomotopyPullback.isWeakHomotopyEquivalence_swap q.hom f.hom
  have hcomp : HomotopyPullback.ofPullback f.hom q.hom =
      (HomotopyPullback.swap q.hom f.hom).comp
        ((HomotopyPullback.ofPullback q.hom f.hom).comp eDom.toHomotopyEquiv.toFun) := by
    ext x : 1
    apply Subtype.ext
    rw [HomotopyPullback.ofPullback_val, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
      HomotopyPullback.swap_val, HomotopyPullback.ofPullback_val]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    ext _ : 1
    exact x.2
  rw [hcomp]
  exact hswap.comp ((isWeakHomotopyEquivalence_ofPullback_of_left hq f).comp heDom)

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
  let sqL : CommSq φ p' (_root_.TopCat.pullbackFst h p) (𝟙 B') :=
    ⟨hφ_fst.trans (Category.comp_id p').symm⟩
  have hcartR := hc.isHomotopyCartesian_of_right hp
  have hsqL_iff : sqL.IsHomotopyCartesian ↔ φ.hom.IsWeakHomotopyEquivalence := by
    rw [CommSq.isHomotopyCartesian_iff, TauCeti.isHomotopyCartesian_iff_homotopy]
    exact ContinuousMap.Homotopy.isHomotopyCartesian_iff_top_of_bottom _ .id
  have hcomm_eq {t : E' ⟶ E} {b : B' ⟶ B} (ht : t = α) (hb : b = h) (sq' : CommSq t p' p b) :
      sq'.IsHomotopyCartesian ↔ sq.IsHomotopyCartesian := by
    subst ht hb
    rfl
  change sq.IsHomotopyCartesian ↔ φ.hom.IsWeakHomotopyEquivalence
  rw [← hsqL_iff, ← sqL.isHomotopyCartesian_horiz_comp_iff hcartR,
    hcomm_eq hφ_snd (Category.id_comp h) (sqL.horiz_comp hc.toCommSq)]

end TauCeti.TopCat
