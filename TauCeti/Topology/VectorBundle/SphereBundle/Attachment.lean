/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.ULift
public import TauCeti.Topology.VectorBundle.SphereBundle.CWComplex

/-!
# Relative CW models of disc-bundle attachments

Let `E → X` be a continuous Riemannian vector bundle of rank `r` over a Hausdorff space `X` carrying
a classical CW structure, and let `g : S(E) → Z` be a continuous attaching map from the unit sphere
bundle of `E` into an arbitrary topological space `Z`. Gluing the unit disc bundle `D(E)` to `Z`
along `g` produces the adjunction space `Z ∪_g D(E)` (`TauCeti.bundleDiskAttachmentSpace`), the
geometric building block of negative-disc bundle attachments in Morse–Bott theory and of Thom spaces
when `Z` is a point.

This file puts a classical relative CW structure `TauCeti.bundleDiskAttachmentCWModel` on
`Z ∪_g D(E)` relative to the embedded image of `Z`, without assuming any CW structure on `Z`:

* `TauCeti.bundleSphereRelCWBaseHomeomorph`: the canonical homeomorphism from the `A = ∅` relative
  base subtype `↥(Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅)` in `D(E)` onto `S(E)`, forgetting the disc
  norm bound in one direction and using `‖v‖ = 1 ⇒ ‖v‖ ≤ 1` in the other;
* `TauCeti.bundleDiskSphereRelCWUlift`: universe-polymorphic lift of `TauCeti.bundleDiskSphereRelCW`
  to `ULift.{v, u} (discBundle F E)` so that `D(E) : Type u` and `Z : Type v` can live in
  independent universes;
* `TauCeti.bundleDiskRelAttachmentSpace` and `TauCeti.bundleDiskRelAttachmentCWModel`: the general
  relative attachment `Z ∪_g D(E)` along a map `g` defined on `S(E) ∪ D(E)|_A` over a relative CW
  pair `(X, A)`, with closed base embedding `TauCeti.isClosedEmbedding_bundleDiskRelAttachmentInr`,
  Hausdorffness over Hausdorff `Z`, and `(q + r)`-cells in bijection with the relative `q`-cells of
  `(X, A)` (`TauCeti.bundleDiskRelAttachmentCellEquiv`);
* `TauCeti.bundleDiskAttachmentSpace` and `TauCeti.bundleDiskAttachmentCWModel`: the `A = ∅`
  specialization for a continuous map `g : S(E) → Z` over a Hausdorff CW complex `X`, transporting
  `g` through `TauCeti.bundleSphereRelCWBaseHomeomorph` to the relative CW pushout, together with
  its cell equivalence (`TauCeti.bundleDiskAttachmentCellEquiv`), characteristic-map formula
  (`TauCeti.bundleDiskAttachmentCWModel_map_apply`), finiteness preservation, and homotopy
  invariance in `Z` (`TauCeti.exists_homotopyEquiv_bundleDiskAttachmentSpace`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §10 and §18.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0 and
  §4.D.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics **60** (1954), 248–261.
-/

public section

noncomputable section

open Bundle CategoryTheory ContinuousMap Limits Metric Set Topology Topology.RelCWComplex

universe u v

namespace TauCeti

/-! ### Homeomorphism between the `A = ∅` relative base subtype and `S(E)` -/

section BaseHomeomorph

variable {X : Type u} [TopologicalSpace X]
  (F : Type*) [NormedAddCommGroup F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [FiberBundle F E]

/-- **Homeomorphism from the `A = ∅` relative base of `D(E)` to `S(E)`.** The forward map forgets
the unit-disc bound `‖v‖ ≤ 1`; the inverse uses `‖v‖ = 1 ⇒ ‖v‖ ≤ 1`
(`sphereBundle_subset_discBundle`) and injects into the sphere summand of
`Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅`. -/
def bundleSphereRelCWBaseHomeomorph :
    ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X)) ≃ₜ
      sphereBundle F E where
  toFun x := ⟨x.1.1, x.2.elim id False.elim⟩
  invFun s := ⟨⟨s.1, sphereBundle_subset_discBundle F E s.2⟩, Or.inl s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem coe_bundleSphereRelCWBaseHomeomorph_apply
    (x : ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X))) :
    (bundleSphereRelCWBaseHomeomorph F E x : TotalSpace F E) = x.1.1 :=
  (rfl)

theorem coe_bundleSphereRelCWBaseHomeomorph_symm_apply (s : sphereBundle F E) :
    ((bundleSphereRelCWBaseHomeomorph F E).symm s : discBundle F E) =
      ⟨s.1, sphereBundle_subset_discBundle F E s.2⟩ :=
  (rfl)

end BaseHomeomorph

/-! ### Auxiliary `ULift` transport of homeomorphisms and homotopy equivalences -/

section ULiftAux

private def uliftUpHomeomorph (Y : Type v) [TopologicalSpace Y] : Y ≃ₜ ULift.{u, v} Y where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_uliftUp
  continuous_invFun := continuous_uliftDown

private def uliftHomotopyEquiv {Z Z' : Type v} [TopologicalSpace Z] [TopologicalSpace Z']
    (e : Z ≃ₕ Z') : ULift.{u, v} Z ≃ₕ ULift.{u, v} Z' where
  toFun := ⟨fun z ↦ ULift.up (e.toFun z.down),
    continuous_uliftUp.comp (e.toFun.continuous.comp continuous_uliftDown)⟩
  invFun := ⟨fun z' ↦ ULift.up (e.invFun z'.down),
    continuous_uliftUp.comp (e.invFun.continuous.comp continuous_uliftDown)⟩
  left_inv := by
    let up : C(Z, ULift.{u, v} Z) := ⟨ULift.up, continuous_uliftUp⟩
    let down : C(ULift.{u, v} Z, Z) := ⟨ULift.down, continuous_uliftDown⟩
    exact ContinuousMap.Homotopic.comp (.refl up) (.comp e.left_inv (.refl down))
  right_inv := by
    let up : C(Z', ULift.{u, v} Z') := ⟨ULift.up, continuous_uliftUp⟩
    let down : C(ULift.{u, v} Z', Z') := ⟨ULift.down, continuous_uliftDown⟩
    exact ContinuousMap.Homotopic.comp (.refl up) (.comp e.right_inv (.refl down))

end ULiftAux

/-! ### Relative disc-bundle attachment along `S(E) ∪ D(E)|_A` -/

section RelAttachment

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  (A : Set X) [RelCWComplex (univ : Set X) A] {r : ℕ} (hr : Module.finrank ℝ F = r)

/-- **Universe lift of `bundleDiskSphereRelCW`.** Lifting `discBundle F E : Type u` to
`ULift.{v, u} (discBundle F E) : Type (max u v)` transports `bundleDiskSphereRelCW` with unchanged
cell dimensions and characteristic maps composed with `ULift.up`. -/
@[instance_reducible]
def bundleDiskSphereRelCWUlift :
    RelCWComplex (univ : Set (ULift.{v, u} (discBundle F E)))
      (ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A)) :=
  @Topology.RelCWComplex.ulift.{v, u} (discBundle F E) _ univ _ (bundleDiskSphereRelCW F E A hr)

private def liftedRelAttachingMap {Z : Type v} [TopologicalSpace Z]
    (g : C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A), Z)) :
    C(↥(ULift.down ⁻¹' (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :
        Set (ULift.{v, u} (discBundle F E))),
      ULift.{u, v} Z) :=
  ⟨fun x ↦ ULift.up (g ⟨x.1.down, x.2⟩),
    continuous_uliftUp.comp
      (g.continuous.comp ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _))⟩

variable {Z : Type v} [TopologicalSpace Z]
  (g : C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A), Z))

/-- The adjunction space `Z ∪_g D(E)` obtained by attaching `D(E)` to `Z` along a continuous map
`g : S(E) ∪ D(E)|_A → Z`, constructed in the common universe `max u v`. -/
def bundleDiskRelAttachmentSpace : TopCat.{max u v} :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  relCWAdjunctionSpace (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)

/-- The canonical inclusion `Z → Z ∪_g D(E)` into the relative disc-bundle attachment. -/
def bundleDiskRelAttachmentInr : C(Z, bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (pushout.inr
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))).hom.comp
    ⟨ULift.up, continuous_uliftUp⟩

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)` into the relative disc-bundle
attachment. -/
def bundleDiskRelAttachmentInl : C(discBundle F E, bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (pushout.inl
    (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
    (TopCat.ofHom (liftedRelAttachingMap F E A g))).hom.comp
    ⟨fun v ↦ ⟨ULift.up v, mem_univ _⟩, continuous_uliftUp.subtype_mk _⟩

/-- On the relative base `S(E) ∪ D(E)|_A`, `bundleDiskRelAttachmentInl` agrees with
`bundleDiskRelAttachmentInr ∘ g`. -/
theorem bundleDiskRelAttachmentInl_eq_inr
    (b : ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A)) :
    bundleDiskRelAttachmentInl F E A hr g b.1 =
      bundleDiskRelAttachmentInr F E A hr g (g b) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  ConcreteCategory.congr_hom
    (pushout.condition
      (f := relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (g := TopCat.ofHom (liftedRelAttachingMap F E A g)))
    ⟨ULift.up b.1, b.2⟩

/-- The canonical map `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_bundleDiskRelAttachmentInr :
    IsClosedEmbedding (bundleDiskRelAttachmentInr F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := (univ : Set (ULift.{v, u} (discBundle F E))))
    (liftedRelAttachingMap F E A g)).comp (uliftUpHomeomorph.{u, v} Z).isClosedEmbedding

/-- When `Z` is Hausdorff, the relative disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_bundleDiskRelAttachmentSpace [T2Space Z] :
    T2Space (bundleDiskRelAttachmentSpace F E A hr g) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  t2Space_relCWAdjunctionSpace (C := (univ : Set (ULift.{v, u} (discBundle F E))))
    (liftedRelAttachingMap F E A g)

private lemma range_bundleDiskRelAttachmentInr :
    letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
    range (pushout.inr
        (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
        (TopCat.ofHom (liftedRelAttachingMap F E A g))) =
      range (bundleDiskRelAttachmentInr F E A hr g) := by
  ext p
  simp only [mem_range, bundleDiskRelAttachmentInr, ULift.exists]
  rfl

/-- **Classical relative CW model of a relative disc-bundle attachment.** Attaching `D(E)` to `Z`
along `g : S(E) ∪ D(E)|_A → Z` equips `Z ∪_g D(E)` with a classical relative CW structure relative
to the image of `Z`, with one `(q + r)`-cell for each relative `q`-cell of `(X, A)`. -/
@[instance_reducible]
def bundleDiskRelAttachmentCWModel :
    RelCWComplex (univ : Set (bundleDiskRelAttachmentSpace F E A hr g))
      (range (bundleDiskRelAttachmentInr F E A hr g)) :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  letI I := relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)
  have hbase := range_bundleDiskRelAttachmentInr F E A hr g
  { cell := I.cell
    map := I.map
    source_eq := I.source_eq
    continuousOn := I.continuousOn
    continuousOn_symm := I.continuousOn_symm
    pairwiseDisjoint' := I.pairwiseDisjoint'
    disjointBase' n c := hbase ▸ I.disjointBase' n c
    mapsTo n c := hbase ▸ I.mapsTo n c
    closed' S hS := hbase ▸ I.closed' S hS
    isClosedBase := hbase ▸ I.isClosedBase
    union' := hbase ▸ I.union' }

/-- Raw cell equivalence in every dimension `n` between `bundleDiskRelAttachmentCWModel` and
`bundleDiskSphereRelCW`. -/
private def bundleDiskRelAttachmentRawCellEquiv (n : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) n ≃
      @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) n :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  (relativeCWPushoutCellEquiv (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g) n).trans
    (@uliftCellEquiv.{v, u} (discBundle F E) _ univ _ (bundleDiskSphereRelCW F E A hr) n)

/-- The `(q + r)`-cells of `Z ∪_g D(E)` correspond bijectively to the relative `q`-cells of
`(X, A)`. -/
def bundleDiskRelAttachmentCellEquiv (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) ≃
      cell (univ : Set X) q :=
  (bundleDiskRelAttachmentRawCellEquiv F E A hr g (thomCellDimension r q)).trans
    (bundleDiskSphereCellEquiv F E A hr q)

/-- Below the fibre rank `r`, `bundleDiskRelAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_bundleDiskRelAttachmentCWModel_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) n) :=
  have := isEmpty_cell_bundleDiskSphereRelCW_of_lt F E A hr hn
  (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).isEmpty_congr.2 inferInstance

/-- Each characteristic map of `bundleDiskRelAttachmentCWModel` is the corresponding characteristic
map of `bundleDiskSphereRelCW` in `D(E)` followed by `bundleDiskRelAttachmentInl`. -/
theorem bundleDiskRelAttachmentCWModel_map_apply (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
      (thomCellDimension r q))
    (x : closedBall (0 : Fin (thomCellDimension r q) → ℝ) 1) :
    @RelCWComplex.map _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
        (thomCellDimension r q) i x =
      bundleDiskRelAttachmentInl F E A hr g
        (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E A hr q).symm
            (bundleDiskRelAttachmentCellEquiv F E A hr g q i)) x) :=
  letI := bundleDiskSphereRelCW F E A hr
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  letI := relativeCWPushout (univ : Set (ULift.{v, u} (discBundle F E)))
    (liftedRelAttachingMap F E A g)
  by
    have hpush := relativeCWPushout_map_apply
      (C := (univ : Set (ULift.{v, u} (discBundle F E))))
      (a := liftedRelAttachingMap F E A g) (thomCellDimension r q) i x
    refine hpush.trans ?_
    let j := relativeCWPushoutCellEquiv (univ : Set (ULift.{v, u} (discBundle F E)))
      (liftedRelAttachingMap F E A g) (thomCellDimension r q) i
    let ι := (pushout.inl
      (relCWBaseInclusion (univ : Set (ULift.{v, u} (discBundle F E))))
      (TopCat.ofHom (liftedRelAttachingMap F E A g))).hom
    change ι ⟨map (thomCellDimension r q) j x, _⟩ =
      ι ⟨ULift.up (map (thomCellDimension r q) _ x), mem_univ _⟩
    congr 1
    apply Subtype.ext
    refine (congrFun (@coe_map_ulift.{v, u} (discBundle F E) _ univ _
      (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) j) x).trans ?_
    dsimp only [Function.comp_apply, bundleDiskRelAttachmentCellEquiv,
      bundleDiskRelAttachmentRawCellEquiv, Equiv.trans_apply]
    rw [Equiv.symm_apply_apply]
    rfl

theorem finiteDimensional_bundleDiskRelAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set X)] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) := by
  have hfd := finiteDimensional_bundleDiskSphereRelCW F E A hr
  refine @RelCWComplex.FiniteDimensional.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) ?_
  filter_upwards [hfd.eventually_isEmpty_cell] with n hn
  exact (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).isEmpty_congr.2 hn

theorem finiteType_bundleDiskRelAttachmentCWModel [RelCWComplex.FiniteType (univ : Set X)] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) := by
  have hft := finiteType_bundleDiskSphereRelCW F E A hr
  refine @RelCWComplex.FiniteType.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) fun n ↦ ?_
  have := hft.finite_cell n
  exact (bundleDiskRelAttachmentRawCellEquiv F E A hr g n).finite_iff.2 inferInstance

theorem finite_bundleDiskRelAttachmentCWModel [RelCWComplex.Finite (univ : Set X)] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g) :=
  @RelCWComplex.Finite.mk _ _ _ _ (bundleDiskRelAttachmentCWModel F E A hr g)
    (finiteDimensional_bundleDiskRelAttachmentCWModel F E A hr g)
    (finiteType_bundleDiskRelAttachmentCWModel F E A hr g)

/-- **Base homotopy invariance of relative disc-bundle attachments.** A homotopy equivalence
`e : Z ≃ₕ Z'` induces a homotopy equivalence `Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` compatible with the
inclusions of `Z` and `Z'`. -/
theorem exists_homotopyEquiv_bundleDiskRelAttachmentSpace {Z' : Type v} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : bundleDiskRelAttachmentSpace F E A hr g ≃ₕ
        bundleDiskRelAttachmentSpace F E A hr (e.toFun.comp g),
      (∀ z, H (bundleDiskRelAttachmentInr F E A hr g z) =
        bundleDiskRelAttachmentInr F E A hr (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (bundleDiskRelAttachmentInr F E A hr (e.toFun.comp g) z') =
        bundleDiskRelAttachmentInr F E A hr g (e.symm z') :=
  letI := bundleDiskSphereRelCWUlift.{u, v} F E A hr
  by
    obtain ⟨H, hH, hHsymm⟩ :=
      (uliftHomotopyEquiv.{u, v} e).exists_homotopyEquiv_relCWAdjunctionSpace
        (univ : Set (ULift.{v, u} (discBundle F E))) (liftedRelAttachingMap F E A g)
    exact ⟨H, fun z ↦ hH (ULift.up z), fun z' ↦ hHsymm (ULift.up z')⟩

end RelAttachment

/-! ### Disc-bundle attachment `Z ∪_g D(E)` along `g : S(E) → Z` (`A = ∅`) -/

section SphereAttachment

variable {X : Type u} [TopologicalSpace X] [T2Space X] [Topology.CWComplex (univ : Set X)]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {r : ℕ} (hr : Module.finrank ℝ F = r)
  {Z : Type v} [TopologicalSpace Z] (g : C(sphereBundle F E, Z))

/-- Transport an attaching map `g : S(E) → Z` along `bundleSphereRelCWBaseHomeomorph` to the
literal `A = ∅` relative base `Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' ∅` of `bundleDiskSphereRelCW`. -/
def bundleSphereBaseAttachingMap :
    C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set X)), Z) :=
  g.comp (bundleSphereRelCWBaseHomeomorph F E)

/-- **Disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by attaching the
unit disc bundle `D(E)` to `Z` along `g : S(E) → Z`. -/
def bundleDiskAttachmentSpace : TopCat.{max u v} :=
  bundleDiskRelAttachmentSpace F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The canonical closed embedding `Z → Z ∪_g D(E)`. -/
def bundleDiskAttachmentInr : C(Z, bundleDiskAttachmentSpace F E hr g) :=
  bundleDiskRelAttachmentInr F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The canonical map `D(E) → Z ∪_g D(E)`. -/
def bundleDiskAttachmentInl : C(discBundle F E, bundleDiskAttachmentSpace F E hr g) :=
  bundleDiskRelAttachmentInl F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- On the unit sphere bundle `S(E)`, `bundleDiskAttachmentInl` glues each vector `s` to `g s` in
`Z`. -/
theorem bundleDiskAttachmentInl_sphere (s : sphereBundle F E) :
    bundleDiskAttachmentInl F E hr g ⟨s.1, sphereBundle_subset_discBundle F E s.2⟩ =
      bundleDiskAttachmentInr F E hr g (g s) :=
  bundleDiskRelAttachmentInl_eq_inr F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)
    ((bundleSphereRelCWBaseHomeomorph F E).symm s)

/-- The inclusion `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_bundleDiskAttachmentInr :
    IsClosedEmbedding (bundleDiskAttachmentInr F E hr g) :=
  isClosedEmbedding_bundleDiskRelAttachmentInr F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- When `Z` is Hausdorff, the disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_bundleDiskAttachmentSpace [T2Space Z] :
    T2Space (bundleDiskAttachmentSpace F E hr g) :=
  t2Space_bundleDiskRelAttachmentSpace F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- **Classical relative CW model of a disc-bundle attachment `Z ∪_g D(E)`.** For a continuous
Riemannian rank-`r` vector bundle `E → X` over a Hausdorff CW complex `X` and any continuous
attaching map `g : S(E) → Z`, the adjunction space `Z ∪_g D(E)` carries a classical relative CW
structure relative to `range (bundleDiskAttachmentInr F E hr g)`, whose `(q + r)`-cells correspond
to the `q`-cells of `X`. -/
@[instance_reducible]
def bundleDiskAttachmentCWModel :
    RelCWComplex (univ : Set (bundleDiskAttachmentSpace F E hr g))
      (range (bundleDiskAttachmentInr F E hr g)) :=
  bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g)

/-- The `(q + r)`-cells of `bundleDiskAttachmentCWModel` correspond bijectively to the `q`-cells of
`X`. -/
def bundleDiskAttachmentCellEquiv (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) (thomCellDimension r q) ≃
      Topology.CWComplex.cell (univ : Set X) q :=
  bundleDiskRelAttachmentCellEquiv F E (∅ : Set X) hr (bundleSphereBaseAttachingMap F E g) q

/-- Below the fibre rank `r`, `bundleDiskAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_bundleDiskAttachmentCWModel_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) n) :=
  isEmpty_cell_bundleDiskRelAttachmentCWModel_of_lt F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) hn

/-- Each characteristic map of `bundleDiskAttachmentCWModel` is the characteristic map of the
corresponding `(q + r)`-cell of `bundleDiskSphereRelCW` in `D(E)` followed by
`bundleDiskAttachmentInl`. -/
theorem bundleDiskAttachmentCWModel_map_apply (q : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
      (thomCellDimension r q))
    (x : closedBall (0 : Fin (thomCellDimension r q) → ℝ) 1) :
    @RelCWComplex.map _ _ _ _ (bundleDiskAttachmentCWModel F E hr g)
        (thomCellDimension r q) i x =
      bundleDiskAttachmentInl F E hr g
        (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E (∅ : Set X) hr)
          (thomCellDimension r q)
          ((bundleDiskSphereCellEquiv F E (∅ : Set X) hr q).symm
            (bundleDiskAttachmentCellEquiv F E hr g q i)) x) :=
  bundleDiskRelAttachmentCWModel_map_apply F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) q i x

theorem finiteDimensional_bundleDiskAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set X)] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finiteDimensional_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

theorem finiteType_bundleDiskAttachmentCWModel [RelCWComplex.FiniteType (univ : Set X)] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finiteType_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

theorem finite_bundleDiskAttachmentCWModel [RelCWComplex.Finite (univ : Set X)] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskAttachmentCWModel F E hr g) :=
  finite_bundleDiskRelAttachmentCWModel F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g)

/-- **Base homotopy invariance of disc-bundle attachments.** A homotopy equivalence `e : Z ≃ₕ Z'`
induces a homotopy equivalence `Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` restricting to `e` on `Z` and to
`e.symm` on `Z'`. -/
theorem exists_homotopyEquiv_bundleDiskAttachmentSpace {Z' : Type v} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : bundleDiskAttachmentSpace F E hr g ≃ₕ
        bundleDiskAttachmentSpace F E hr (e.toFun.comp g),
      (∀ z, H (bundleDiskAttachmentInr F E hr g z) =
        bundleDiskAttachmentInr F E hr (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (bundleDiskAttachmentInr F E hr (e.toFun.comp g) z') =
        bundleDiskAttachmentInr F E hr g (e.symm z') :=
  exists_homotopyEquiv_bundleDiskRelAttachmentSpace F E (∅ : Set X) hr
    (bundleSphereBaseAttachingMap F E g) e

end SphereAttachment

end TauCeti
