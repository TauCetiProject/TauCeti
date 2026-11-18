/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.Topology.Homotopy.Monodromy.BasepointChange
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.Topology.Homotopy.Monodromy.Functoriality
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The orientation character of a real vector bundle

Let `E → B` be a real vector bundle of rank `card ι`. Going once around a loop `γ` at `b`, an
orientation of the fibre `E_b` either comes back to itself or to its opposite: path lifting in the
orientation double cover permutes the two orientations of `E_b`. The sign of this permutation is
the **orientation character** `w₁ : π₁(B, b) →* ℤˣ`
(`TauCeti.VectorBundleOrientationCover.orientationCharacter`): the first Stiefel–Whitney class of
the bundle in the form of a homomorphism on the fundamental group (no cohomology class is
constructed here). It is `1` on a loop exactly when
transport along the loop preserves an orientation of `E_b`, and `-1` exactly when it reverses it
(`orientationCharacter_eq_one_iff_monodromy_eq`, `orientationCharacter_eq_neg_one_iff`).

* An orientation of the bundle is preserved by transport along every loop, so the character of an
  orientable bundle is trivial (`TauCeti.VectorBundleOrientation.orientationCharacter_eq_one`).
  Over a connected, locally path-connected base the converse holds: a bundle with trivial
  character is orientable (`nonempty_iff_orientationCharacter_eq_one`).
* Transport along a loop `γ` in the orientation local system `o(E)` is multiplication by `w₁(γ)`
  (`signLocalSystemFiberEquiv_map_asHom`): the character is the monodromy of `o(E)`.
* Changing the basepoint along a path does not change the character
  (`orientationCharacter_fundamentalGroupMulEquivOfPath`), since the two monodromy permutations
  are conjugate by path lifting and the sign is invariant under conjugation.

The character is a homomorphism to the commutative group `ℤˣ`, so it is constant on conjugacy
classes. Free loops `f : S¹ → B` in one path component of the free loop space `C(S¹, B)` give
conjugate classes after a change of basepoint (`Path.joined_toCircle_iff_isConj`), so the
character of the loop `t ↦ f(e^{2πit})` at `f 1` is an invariant of the path component of `f`
(`freeLoopOrientationCharacter`, `freeLoopOrientationCharacter_eq_of_joined`). It is `1` exactly
when the orientations of the fibres `E_{f z}` can be chosen continuously in `z ∈ S¹`, that is when
`f` lifts to the orientation double cover (`freeLoopOrientationCharacter_eq_one_iff`). Such a lift
is a continuous choice of orientations of the fibres of `E` along `f`, the data of an orientation
of the pulled-back bundle `f*E`; the pullback bundle itself is not formed here.

For the tangent bundle of a closed manifold `Q`, these are the orientation data in the degree-zero
twist `η₀` of the Viterbo isomorphism with local coefficients of Barraud–Damian–Humilière–Oancea:
its exponent `w(f)` is `0` where `freeLoopOrientationCharacter` is `1` and `-1` where it is `-1`,
and the orientation local system of `Q` has the orientation character as its monodromy.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.orientationCharacter`: the orientation character
  `π₁(B, b) →* ℤˣ`.
* `TauCeti.VectorBundleOrientationCover.freeLoopOrientationCharacter`: the orientation character
  of a free loop `S¹ → B`.

## Main results

* `orientationCharacter_eq_one_iff_monodromy_eq`, `orientationCharacter_eq_neg_one_iff`: the
  character is `1` where transport preserves an orientation and `-1` where it reverses it.
* `TauCeti.VectorBundleOrientation.orientationCharacter_eq_one`,
  `nonempty_iff_orientationCharacter_eq_one`: a bundle over a connected, locally path-connected
  base is orientable exactly when its orientation character is trivial.
* `signLocalSystemFiberEquiv_map_asHom`: transport in the orientation local system along a loop
  is multiplication by its orientation character.
* `orientationCharacter_fundamentalGroupMulEquivOfPath`: invariance under change of basepoint.
* `freeLoopOrientationCharacter_toCircle`: the character of the free loop of a based loop.
* `freeLoopOrientationCharacter_eq_of_joined`: the character of a free loop only depends on its
  path component in `C(S¹, B)`.
* `freeLoopOrientationCharacter_eq_one_iff`: the character of a free loop is `1` exactly when the
  loop lifts to the orientation double cover.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and `w₁`).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (the orientation
  double cover and orientability along loops).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1 (the twist `η` on the free
  loop space).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe u uB uE uι

variable {B : Type uB} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)

namespace TauCeti

namespace VectorBundleOrientationCover

/-- The fibres of the orientation double cover of a bundle of rank `card ι` are finite: they have
two points. -/
theorem finite_fiber (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [ncard_fiber hι]; exact two_ne_zero)

variable (F E) in
open Classical in
/-- The **orientation character** `w₁ : π₁(B, b) →* ℤˣ` of a real vector bundle `E` of rank
`card ι`: the sign of the permutation of the two orientations of `E_b` obtained by transporting
them along a loop, that is by path lifting in the orientation double cover. -/
def orientationCharacter (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    FundamentalGroup B b →* ℤˣ :=
  letI := (finite_fiber (F := F) (E := E) hι b).fintype
  Equiv.Perm.sign.comp ((isCoveringMap_proj (F := F) (E := E) hι).monodromyPerm b)

/-- The orientation character is trivial on a loop exactly when transport along the loop fixes
both orientations of the fibre. -/
theorem orientationCharacter_eq_one_iff {b : B} (g : FundamentalGroup B b) :
    orientationCharacter F E hι b g = 1 ↔
      (isCoveringMap_proj (F := F) (E := E) hι).monodromyPerm b g = 1 := by
  classical
  let := (finite_fiber (F := F) (E := E) hι b).fintype
  -- A permutation of a set with two elements has sign `1` exactly when it is the identity, since
  -- the alternating group of such a set is trivial.
  rw [orientationCharacter, MonoidHom.comp_apply, ← Equiv.Perm.mem_alternatingGroup,
    alternatingGroup.eq_bot_of_card_le_two (by rw [Nat.card_coe_set_eq, ncard_fiber hι]),
    Subgroup.mem_bot]

/-- **The orientation character detects orientation-preserving loops.** It is `1` on a loop
exactly when transport along the loop brings a given orientation `e` of the fibre back to
itself. -/
theorem orientationCharacter_eq_one_iff_monodromy_eq {b : B} (g : FundamentalGroup B b)
    (e : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :
    orientationCharacter F E hι b g = 1 ↔ (isCoveringMap_proj hι).monodromy g.toPath e = e := by
  rw [orientationCharacter_eq_one_iff]
  refine ⟨fun h ↦ by simpa using Equiv.ext_iff.1 h e, fun h ↦ Equiv.ext fun e' ↦ ?_⟩
  simp only [IsCoveringMap.coe_monodromyPerm, Equiv.Perm.coe_one, id_eq]
  rcases eq_or_eq_deck hι (e'.2.trans e.2.symm) with he' | he'
  · rw [Subtype.ext he', h]
  -- The other orientation `deck e` does not go to `e = monodromy e`, so it goes to itself.
  have hm : ((isCoveringMap_proj hι).monodromy g.toPath e' : VectorBundleOrientationCover F E ι) =
      e ∨ ((isCoveringMap_proj hι).monodromy g.toPath e' : VectorBundleOrientationCover F E ι) =
        deck e :=
    eq_or_eq_deck hι (((isCoveringMap_proj hι).monodromy g.toPath e').2.trans e.2.symm)
  rcases hm with hm | hm
  · have := ((isCoveringMap_proj hι).monodromy_bijective g.toPath).1
      ((Subtype.ext hm).trans h.symm)
    exact absurd (congrArg Subtype.val this) (by rw [he']; exact deck_ne_self _)
  · exact Subtype.ext (hm.trans he'.symm)

/-- **The orientation character detects orientation-reversing loops.** It is `-1` on a loop
exactly when transport along the loop carries a given orientation `e` of the fibre to the opposite
orientation. -/
theorem orientationCharacter_eq_neg_one_iff {b : B} (g : FundamentalGroup B b)
    (e : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :
    orientationCharacter F E hι b g = -1 ↔
      ((isCoveringMap_proj hι).monodromy g.toPath e : VectorBundleOrientationCover F E ι) =
        deck e := by
  have hm := eq_or_eq_deck hι (((isCoveringMap_proj hι).monodromy g.toPath e).2.trans e.2.symm)
  rcases Int.units_eq_one_or (orientationCharacter F E hι b g) with h | h
  · have h' := (orientationCharacter_eq_one_iff_monodromy_eq hι g e).1 h
    rw [h, h']
    exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h.symm (deck_ne_self _)⟩
  · refine ⟨fun _ ↦ hm.resolve_left fun hm ↦ ?_, fun _ ↦ h⟩
    have := (orientationCharacter_eq_one_iff_monodromy_eq hι g e).2 (Subtype.ext hm)
    rw [h] at this
    exact absurd this (by decide)

/-! ### Orientability -/

/-- **The orientation character of an orientable bundle is trivial**: transport along a loop
follows the chosen orientation. -/
theorem _root_.TauCeti.VectorBundleOrientation.orientationCharacter_eq_one
    (o : VectorBundleOrientation F E ι) {b : B} (g : FundamentalGroup B b) :
    orientationCharacter F E hι b g = 1 :=
  (orientationCharacter_eq_one_iff_monodromy_eq hι g ⟨⟨b, o b⟩, rfl⟩).2
    ((isCoveringMap_proj hι).monodromy_section (o.continuous_mk_cover hι) (fun _ ↦ rfl) _)

/-- **Orientability from the fundamental group.** A real vector bundle of rank `card ι` over a
connected, locally path-connected base is orientable exactly when its orientation character at
some point is trivial. If it is not orientable, its orientation double cover is path connected, and
a path from an orientation of `E_b` to the opposite orientation projects to a loop reversing it. -/
theorem nonempty_iff_orientationCharacter_eq_one [ConnectedSpace B] [LocallyPathConnectedSpace B]
    (b : B) :
    Nonempty (VectorBundleOrientation F E ι) ↔ orientationCharacter F E hι b = 1 := by
  refine ⟨fun ⟨o⟩ ↦ MonoidHom.ext fun g ↦ o.orientationCharacter_eq_one hι g, fun h ↦ ?_⟩
  by_contra hno
  have hp := isCoveringMap_proj (F := F) (E := E) hι
  have : ConnectedSpace (VectorBundleOrientationCover F E ι) := by
    by_contra hc
    exact hno ((VectorBundleOrientation.nonempty_iff_not_connectedSpace hι).2 hc)
  have : LocallyPathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨e, he⟩ := surjective_proj (F := F) (E := E) hι b
  obtain ⟨g, hg⟩ := hp.exists_monodromy_eq (⟨e, he⟩ : (proj ⁻¹' {b} : Set _))
    ⟨deck e, (proj_deck e).trans he⟩
  have := (orientationCharacter_eq_neg_one_iff hι g ⟨e, he⟩).2 (congrArg Subtype.val hg)
  rw [h, MonoidHom.one_apply] at this
  exact absurd this (by decide)

/-! ### The orientation local system -/

/-- **Transport in the orientation local system is multiplication by the orientation
character.** Read through an orientation `o` of `E_b`, transport along a loop `g` at `b` in the
orientation local system `o(E)` multiplies by `w₁(g)`. -/
theorem signLocalSystemFiberEquiv_map_asHom {R : Type u} [Ring R] {b : B}
    (o : Orientation ℝ (E b) ι) (g : FundamentalGroup B b)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    signLocalSystemFiberEquiv hι o (((signLocalSystem F E R hι).map g.asHom).hom f) =
      (orientationCharacter F E hι b g : ℤ) • signLocalSystemFiberEquiv hι o f := by
  rw [signLocalSystemFiberEquiv_apply, signLocalSystemObjEquiv_map_apply,
    signLocalSystemFiberEquiv_apply]
  -- Transport precomposes with monodromy along the inverse loop, whose character is the same.
  -- In `π₁` the product `g⁻¹ * g` is the composite `g ≫ g⁻¹` of arrows.
  have hinv : inv g.asHom = (g⁻¹).toPath :=
    IsIso.inv_eq_of_hom_inv_id
      (congrArg (fun p : FundamentalGroup B b ↦ p.asHom) (inv_mul_cancel g))
  have hχ : orientationCharacter F E hι b g⁻¹ = orientationCharacter F E hι b g := by
    rw [map_inv]
    rcases Int.units_eq_one_or (orientationCharacter F E hι b g) with h | h <;> rw [h] <;> rfl
  rw [hinv]
  rcases Int.units_eq_one_or (orientationCharacter F E hι b g) with h | h
  · rw [(orientationCharacter_eq_one_iff_monodromy_eq hι g⁻¹
      (⟨⟨b, o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)))).1
      (hχ.trans h), h]
    simp
  · have hm := (orientationCharacter_eq_neg_one_iff hι g⁻¹ ⟨⟨b, o⟩, rfl⟩).1 (hχ.trans h)
    have hm' : (isCoveringMap_proj (F := F) (E := E) hι).monodromy (g⁻¹).toPath ⟨⟨b, o⟩, rfl⟩ =
        (⟨⟨b, -o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :=
      Subtype.ext (hm.trans (by simp [deck_apply]))
    rw [hm', h, Units.val_neg, Units.val_one, neg_one_zsmul, ← signLocalSystemFiberEquiv_apply,
      signLocalSystemFiberEquiv_neg, signLocalSystemFiberEquiv_apply]

/-! ### Change of basepoint -/

/-- **Invariance under change of basepoint.** Transporting a loop class back along a path `δ` does
not change its orientation character: the two monodromy permutations are conjugate by path lifting
along `δ`. -/
theorem orientationCharacter_fundamentalGroupMulEquivOfPath_symm {b₀ b₁ : B} (δ : Path b₀ b₁)
    (g : FundamentalGroup B b₁) :
    orientationCharacter F E hι b₀ ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ).symm g) =
      orientationCharacter F E hι b₁ g := by
  classical
  let := (finite_fiber (F := F) (E := E) hι b₀).fintype
  let := (finite_fiber (F := F) (E := E) hι b₁).fintype
  simp only [orientationCharacter, MonoidHom.comp_apply,
    IsCoveringMap.monodromyPerm_fundamentalGroupMulEquivOfPath_symm, Equiv.Perm.sign_permCongr]

/-- **Invariance under change of basepoint.** Transporting a loop class along a path `δ` does not
change its orientation character. -/
theorem orientationCharacter_fundamentalGroupMulEquivOfPath {b₀ b₁ : B} (δ : Path b₀ b₁)
    (g : FundamentalGroup B b₀) :
    orientationCharacter F E hι b₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath δ g) =
      orientationCharacter F E hι b₀ g := by
  rw [← orientationCharacter_fundamentalGroupMulEquivOfPath_symm hι δ, MulEquiv.symm_apply_apply]

/-- The orientation character of a loop is unchanged by casting the loop along an equality of
basepoints. -/
private theorem orientationCharacter_fromPath_cast {b b' : B} (h : b' = b) (γ : Path b b) :
    orientationCharacter F E hι b' (FundamentalGroup.fromPath (.mk (γ.cast h h))) =
      orientationCharacter F E hι b (FundamentalGroup.fromPath (.mk γ)) := by
  subst h
  rfl

/-! ### Free loops -/

variable (F E) in
/-- The **orientation character of a free loop** `f : S¹ → B`: the orientation character of the
loop `t ↦ f(e^{2πit})` at `f 1`. It is `1` exactly when the orientations of the fibres along `f`
can be chosen continuously (`freeLoopOrientationCharacter_eq_one_iff`), and it is constant on the
path components of the free loop space (`freeLoopOrientationCharacter_eq_of_joined`). -/
def freeLoopOrientationCharacter (hι : Fintype.card ι = finrank ℝ F) (f : C(Circle, B)) : ℤˣ :=
  orientationCharacter F E hι (f 1) (FundamentalGroup.fromPath (.mk f.toBasedLoop))

/-- The orientation character of the free loop `γ.toCircle` of a loop `γ` at `b` is the
orientation character of `γ`. -/
@[simp]
theorem freeLoopOrientationCharacter_toCircle {b : B} (γ : Path b b) :
    freeLoopOrientationCharacter F E hι γ.toCircle =
      orientationCharacter F E hι b (FundamentalGroup.fromPath (.mk γ)) := by
  have hγ : γ.toCircle.toBasedLoop = γ.cast γ.toCircle_one γ.toCircle_one := by
    ext t
    rw [ContinuousMap.toBasedLoop_apply, Path.cast_coe, Path.toCircle_unitToCircle]
  rw [freeLoopOrientationCharacter, hγ, orientationCharacter_fromPath_cast]

/-- **The orientation character of a free loop is an invariant of its path component** in the
free loop space `C(S¹, B)`. Joined free loops are, after transport of the basepoint along the
track of the basepoint, conjugate loops, and the character is invariant under both operations. -/
theorem freeLoopOrientationCharacter_eq_of_joined {f g : C(Circle, B)} (h : Joined f g) :
    freeLoopOrientationCharacter F E hι f = freeLoopOrientationCharacter F E hι g := by
  -- The track `δ` of the basepoint, and the loop `δ · g · δ⁻¹` at `f 1`, joined to `f`.
  let δ : Path (f 1) (g 1) := h.somePath.map ((continuous_eval_const (1 : Circle)))
  have hj : Joined f.toBasedLoop.toCircle ((δ.trans g.toBasedLoop).trans δ.symm).toCircle := by
    rw [ContinuousMap.toBasedLoop_toCircle]
    exact h.trans (g.joined_toCircle_trans_trans_symm_toBasedLoop δ).symm
  have hconj :=
    (orientationCharacter F E hι (f 1)).map_isConj (Path.joined_toCircle_iff_isConj.1 hj)
  rw [isConj_iff_eq] at hconj
  rw [freeLoopOrientationCharacter, freeLoopOrientationCharacter, hconj,
    ← orientationCharacter_fundamentalGroupMulEquivOfPath_symm hι δ,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
  have hq : Path.Homotopic.Quotient.mk ((δ.trans g.toBasedLoop).trans δ.symm) =
      (Path.Homotopic.Quotient.mk δ).trans
        ((Path.Homotopic.Quotient.mk g.toBasedLoop).trans (Path.Homotopic.Quotient.mk δ).symm) := by
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]
  exact congrArg (fun q ↦ orientationCharacter F E hι (f 1) (FundamentalGroup.fromPath q)) hq

/-- **Orientability along a free loop.** The orientation character of a free loop `f` is `1`
exactly when `f` lifts to the orientation double cover, that is when the orientations of the
fibres `E_{f z}` can be chosen continuously in `z ∈ S¹`, which is the data of an orientation of
the pullback of `E` along `f`. -/
theorem freeLoopOrientationCharacter_eq_one_iff (f : C(Circle, B)) :
    freeLoopOrientationCharacter F E hι f = 1 ↔
      ∃ s : C(Circle, VectorBundleOrientationCover F E ι), ∀ z, (s z).proj = f z := by
  have hp := isCoveringMap_proj (F := F) (E := E) hι
  obtain ⟨e, he⟩ := surjective_proj (F := F) (E := E) hι (f 1)
  rw [freeLoopOrientationCharacter, orientationCharacter_eq_one_iff_monodromy_eq hι _ ⟨e, he⟩]
  constructor
  · intro h
    -- The lift of the loop `t ↦ f(e^{2πit})` starting at `e` is closed, so it descends to the
    -- circle.
    let Γ : Path e e :=
      { toContinuousMap := hp.liftPath f.toBasedLoop.toContinuousMap e (by simp [he])
        source' := hp.liftPath_zero ..
        target' := by
          -- `FundamentalGroup.toPath` and `FundamentalGroup.fromPath` are abbreviations, inverse
          -- to each other by definition.
          have h' : hp.monodromy (Path.Homotopic.Quotient.mk f.toBasedLoop) ⟨e, he⟩ = ⟨e, he⟩ := h
          have := congrArg Subtype.val h'
          rwa [IsCoveringMap.coe_monodromy_mk] at this }
    refine ⟨Γ.toCircle, fun z ↦ ?_⟩
    obtain ⟨t, rfl⟩ := unitToCircle_surjective z
    rw [Path.toCircle_unitToCircle, ← ContinuousMap.toBasedLoop_apply]
    exact congrFun (hp.liftPath_lifts f.toBasedLoop.toContinuousMap e (by simp [he])) t
  · rintro ⟨s, hs⟩
    -- The loop `t ↦ s(e^{2πit})` lifts the loop of `f`, from `s 1`; if it starts at `deck e`
    -- instead of `e`, its image under the deck involution starts at `e`.
    have hΓ (s : C(Circle, VectorBundleOrientationCover F E ι)) (hs : ∀ z, (s z).proj = f z)
        (hs1 : s 1 = e) :
        hp.monodromy (FundamentalGroup.fromPath (.mk f.toBasedLoop)).toPath ⟨e, he⟩ = ⟨e, he⟩ := by
      refine Subtype.ext ((hp.monodromy_eq_apply_one (γ := f.toBasedLoop)
        (Γ := s.comp unitToCircle) (funext fun t ↦ by
          rw [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.toBasedLoop_apply]
          exact hs _)
        (by simpa using hs1)).trans ?_)
      simpa using hs1
    rcases eq_or_eq_deck hι ((hs 1).trans he.symm) with h1 | h1
    · exact hΓ s hs h1
    · refine hΓ (ContinuousMap.comp ⟨deck, deck.continuous⟩ s)
        (fun z ↦ by simp [hs]) ?_
      simp [h1]

/-- The orientation character of a free loop in an orientable bundle is `1`. -/
theorem _root_.TauCeti.VectorBundleOrientation.freeLoopOrientationCharacter_eq_one
    (o : VectorBundleOrientation F E ι) (f : C(Circle, B)) :
    freeLoopOrientationCharacter F E hι f = 1 :=
  o.orientationCharacter_eq_one hι _

/-- The orientation character of a constant loop is `1`. -/
@[simp]
theorem freeLoopOrientationCharacter_const (x : B) :
    freeLoopOrientationCharacter F E hι (ContinuousMap.const Circle x) = 1 := by
  obtain ⟨e, he⟩ := surjective_proj (F := F) (E := E) hι x
  exact (freeLoopOrientationCharacter_eq_one_iff hι _).2 ⟨ContinuousMap.const Circle e, fun _ ↦ he⟩

end VectorBundleOrientationCover

end TauCeti
