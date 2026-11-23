/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Character
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.Topology.Homotopy.Monodromy.Functoriality
import TauCeti.Topology.VectorBundle.Orientation.Cover.FundamentalGroup

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

The orientation character is the sign character `IsCoveringMap.signCharacter` of the orientation
double cover, and the results below specialize the double-cover results of
`TauCeti.Topology.Homotopy.Monodromy.SignCharacter` and
`TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Character`, with the deck involution exchanging
the two orientations of each fibre.

* An orientation of the bundle is preserved by transport along every loop, so the character of an
  orientable bundle is trivial (`TauCeti.VectorBundleOrientation.orientationCharacter_eq_one`).
  Over a connected, locally path-connected base the converse holds: a bundle with trivial
  character is orientable
  (`TauCeti.VectorBundleOrientation.nonempty_iff_orientationCharacter_eq_one`).
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
  `TauCeti.VectorBundleOrientation.nonempty_iff_orientationCharacter_eq_one`: a bundle over a
  connected, locally path-connected base is orientable exactly when its orientation character is
  trivial.
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

variable (F E) in
/-- The **orientation character** `w₁ : π₁(B, b) →* ℤˣ` of a real vector bundle `E` of rank
`card ι`: the sign of the permutation of the two orientations of `E_b` obtained by transporting
them along a loop, that is the sign character of the orientation double cover. -/
def orientationCharacter (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    FundamentalGroup B b →* ℤˣ :=
  (isCoveringMap_proj (F := F) (E := E) hι).signCharacter (finite_fiber hι b)

/-- The orientation character is the sign character of the orientation double cover. -/
theorem orientationCharacter_eq_signCharacter (b : B) :
    orientationCharacter F E hι b =
      (isCoveringMap_proj (F := F) (E := E) hι).signCharacter (finite_fiber hι b) :=
  (rfl)

/-- The orientation character is the sign of the permutation of the orientations of `E_b` given
by path lifting in the orientation double cover. -/
theorem orientationCharacter_apply {b : B}
    [Fintype (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))]
    [DecidableEq (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))]
    (g : FundamentalGroup B b) :
    orientationCharacter F E hι b g =
      Equiv.Perm.sign ((isCoveringMap_proj (F := F) (E := E) hι).monodromyPerm b g) :=
  IsCoveringMap.signCharacter_apply _ _ g

/-- The orientation character is trivial on a loop exactly when transport along the loop fixes
both orientations of the fibre. -/
theorem orientationCharacter_eq_one_iff {b : B} (g : FundamentalGroup B b) :
    orientationCharacter F E hι b g = 1 ↔
      (isCoveringMap_proj (F := F) (E := E) hι).monodromyPerm b g = 1 :=
  IsCoveringMap.signCharacter_eq_one_iff _ _ (by rw [Nat.card_coe_set_eq, ncard_fiber hι]) g

/-- **The orientation character detects orientation-preserving loops.** It is `1` on a loop
exactly when transport along the loop brings a given orientation `e` of the fibre back to
itself. -/
theorem orientationCharacter_eq_one_iff_monodromy_eq {b : B} (g : FundamentalGroup B b)
    (e : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :
    orientationCharacter F E hι b g = 1 ↔ (isCoveringMap_proj hι).monodromy g.toPath e = e :=
  IsCoveringMap.signCharacter_eq_one_iff_monodromy_eq _ (fun _ _ h ↦ eq_or_eq_deck hι h) _ g e

/-- **The orientation character detects orientation-reversing loops.** It is `-1` on a loop
exactly when transport along the loop carries a given orientation `e` of the fibre to the opposite
orientation. -/
theorem orientationCharacter_eq_neg_one_iff {b : B} (g : FundamentalGroup B b)
    (e : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι))) :
    orientationCharacter F E hι b g = -1 ↔
      ((isCoveringMap_proj hι).monodromy g.toPath e : VectorBundleOrientationCover F E ι) =
        deck e :=
  IsCoveringMap.signCharacter_eq_neg_one_iff _ deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) _ g e

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
theorem _root_.TauCeti.VectorBundleOrientation.nonempty_iff_orientationCharacter_eq_one
    [ConnectedSpace B] [LocallyPathConnectedSpace B] (b : B) :
    Nonempty (VectorBundleOrientation F E ι) ↔ orientationCharacter F E hι b = 1 := by
  refine ⟨fun ⟨o⟩ ↦ MonoidHom.ext fun g ↦ o.orientationCharacter_eq_one hι g, fun h ↦ ?_⟩
  by_contra hno
  have := not_nonempty_iff.1 hno
  have := pathConnectedSpace_of_isEmpty (F := F) (E := E) hι
  obtain ⟨e, he⟩ := surjective_proj (F := F) (E := E) hι b
  obtain ⟨g, hg⟩ := (isCoveringMap_proj hι).exists_monodromy_eq
    (⟨e, he⟩ : (proj ⁻¹' {b} : Set _)) ⟨deck e, (proj_deck e).trans he⟩
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
  exact (isCoveringMap_proj hι).apply_monodromy_inv_asHom_of_mem_signFiber deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (finite_fiber hι b) g
    (signLocalSystemObjEquiv hι _ f).property _

/-! ### Change of basepoint -/

/-- **Invariance under change of basepoint.** Transporting a loop class back along a path `δ` does
not change its orientation character: the two monodromy permutations are conjugate by path lifting
along `δ`. -/
theorem orientationCharacter_fundamentalGroupMulEquivOfPath_symm {b₀ b₁ : B} (δ : Path b₀ b₁)
    (g : FundamentalGroup B b₁) :
    orientationCharacter F E hι b₀ ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ).symm g) =
      orientationCharacter F E hι b₁ g :=
  IsCoveringMap.signCharacter_fundamentalGroupMulEquivOfPath_symm _ _ _ δ g

/-- **Invariance under change of basepoint.** Transporting a loop class along a path `δ` does not
change its orientation character. -/
theorem orientationCharacter_fundamentalGroupMulEquivOfPath {b₀ b₁ : B} (δ : Path b₀ b₁)
    (g : FundamentalGroup B b₀) :
    orientationCharacter F E hι b₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath δ g) =
      orientationCharacter F E hι b₀ g :=
  IsCoveringMap.signCharacter_fundamentalGroupMulEquivOfPath _ _ _ δ g

/-! ### Free loops -/

variable (F E) in
/-- The **orientation character of a free loop** `f : S¹ → B`: the orientation character of the
loop `t ↦ f(e^{2πit})` at `f 1`, that is the sign character of `f` in the orientation double
cover. It is `1` exactly when the orientations of the fibres along `f` can be chosen continuously
(`freeLoopOrientationCharacter_eq_one_iff`), and it is constant on the path components of the free
loop space (`freeLoopOrientationCharacter_eq_of_joined`). -/
def freeLoopOrientationCharacter (hι : Fintype.card ι = finrank ℝ F) (f : C(Circle, B)) : ℤˣ :=
  (isCoveringMap_proj (F := F) (E := E) hι).freeLoopSignCharacter (finite_fiber hι) f

/-- The orientation character of a free loop is the orientation character of its based loop at
`f 1`. -/
theorem freeLoopOrientationCharacter_def (f : C(Circle, B)) :
    freeLoopOrientationCharacter F E hι f =
      orientationCharacter F E hι (f 1) (FundamentalGroup.fromPath (.mk f.toBasedLoop)) :=
  IsCoveringMap.freeLoopSignCharacter_def _ _ f

/-- The orientation character of the free loop `γ.toCircle` of a loop `γ` at `b` is the
orientation character of `γ`. -/
@[simp]
theorem freeLoopOrientationCharacter_toCircle {b : B} (γ : Path b b) :
    freeLoopOrientationCharacter F E hι γ.toCircle =
      orientationCharacter F E hι b (FundamentalGroup.fromPath (.mk γ)) :=
  IsCoveringMap.freeLoopSignCharacter_toCircle _ _ γ

/-- **The orientation character of a free loop is an invariant of its path component** in the
free loop space `C(S¹, B)`. Joined free loops are, after transport of the basepoint along the
track of the basepoint, conjugate loops, and the character is invariant under both operations. -/
theorem freeLoopOrientationCharacter_eq_of_joined {f g : C(Circle, B)} (h : Joined f g) :
    freeLoopOrientationCharacter F E hι f = freeLoopOrientationCharacter F E hι g :=
  IsCoveringMap.freeLoopSignCharacter_eq_of_joined _ _ h

/-- **Orientability along a free loop.** The orientation character of a free loop `f` is `1`
exactly when `f` lifts to the orientation double cover, that is when the orientations of the
fibres `E_{f z}` can be chosen continuously in `z ∈ S¹`, which is the data of an orientation of
the pullback of `E` along `f`. -/
theorem freeLoopOrientationCharacter_eq_one_iff (f : C(Circle, B)) :
    freeLoopOrientationCharacter F E hι f = 1 ↔
      ∃ s : C(Circle, VectorBundleOrientationCover F E ι), ∀ z, (s z).proj = f z :=
  IsCoveringMap.freeLoopSignCharacter_eq_one_iff _ _ (fun _ _ h ↦ eq_or_eq_deck hι h) f
    (surjective_proj hι (f 1))

/-- The orientation character of a free loop in an orientable bundle is `1`. -/
theorem _root_.TauCeti.VectorBundleOrientation.freeLoopOrientationCharacter_eq_one
    (o : VectorBundleOrientation F E ι) (f : C(Circle, B)) :
    freeLoopOrientationCharacter F E hι f = 1 := by
  rw [freeLoopOrientationCharacter_def]
  exact o.orientationCharacter_eq_one hι _

/-- The orientation character of a constant loop is `1`. -/
@[simp]
theorem freeLoopOrientationCharacter_const (x : B) :
    freeLoopOrientationCharacter F E hι (ContinuousMap.const Circle x) = 1 :=
  IsCoveringMap.freeLoopSignCharacter_const _ _ x

end VectorBundleOrientationCover

end TauCeti
