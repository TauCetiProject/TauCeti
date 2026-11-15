/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The tangent representation of an isotropy group

Let a group `G` act on a manifold `M`, and let `x : M`. If every element of the stabilizer of `x`
acts by a map differentiable at `x`, the chain rule makes `g ↦ mfderiv I I (g • ·) x` a continuous
representation `TauCeti.tangentRepresentation` of the stabilizer on the tangent space `T_x M`.
Moving `x` along its orbit by `h` conjugates this representation: the derivative of `h • ·` at `x`
intertwines it with the tangent representation at `h • x`, along Mathlib's conjugation isomorphism
`MulAction.stabilizerEquivStabilizer` of the two stabilizers. When `G` is a manifold acting by a
`C¹` map `G × M → M`, the tangent representation is continuous in the group element.

For a group acting by smooth maps, the invariant vectors `TauCeti.tangentInvariants` of the tangent
representation sort the fixed points into strata `TauCeti.fixedPointsFinrank` by their dimension.
The differential of any map into the fixed set takes values in these invariant vectors.

For a finite stabilizer acting by `C¹` maps on a manifold without boundary over `ℝ` or `ℂ`,
Bochner linearization identifies this representation with the linear action in an equivariant
chart. Hence an element of the stabilizer has derivative the identity at `x` exactly when it acts
as the identity near `x`: the kernel of the tangent representation is the germ kernel at `x`, the
ineffective part of the isotropy. No faithfulness is assumed, and elements acting trivially are
retained as elements of the stabilizer. On a connected Hausdorff manifold the identity principle
for finite-order actions upgrades this to the elements acting trivially on all of `M`. So for an
effective action the tangent representation is faithful: an element fixing a point and a frame
there is the identity. This is the freeness of the action on frames used to present an effective
orbifold as a quotient of its frame bundle by an orthogonal group.

## Main definitions

* `TauCeti.tangentRepresentation`: the representation of the stabilizer of `x` on `T_x M` by
  derivatives at `x`.
* `TauCeti.tangentInvariants I G x`: for a group acting by smooth maps, the invariants of the
  tangent representation, the tangent vectors fixed by every differential `d(g •)_x`.
* `TauCeti.fixedPointsFinrank I G M d`: the stratum of the fixed set made of the fixed points `p`
  whose invariant tangent vectors form a subspace of dimension `d`.

## Main results

* `TauCeti.mem_invariants_tangentRepresentation_iff`: the invariant vectors are the tangent vectors
  fixed by the differential of every element of the stabilizer.
* `TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`: at a point fixed by the
  whole group, they are the tangent vectors fixed by the differential of every group element.
* `TauCeti.range_mfderiv_le_tangentInvariants`, `TauCeti.range_mfderiv_eq_tangentInvariants`: the
  differential of a map into the fixed set takes values in the invariant tangent vectors, and an
  immersion of a `d`-dimensional manifold into the stratum of dimension `d` fills them.
* `TauCeti.mfderiv_smul_comp_tangentRepresentation`: the tangent representations at `x` and
  `h • x` are intertwined by the derivative of `h • ·`.
* `TauCeti.continuous_tangentRepresentation`: for a jointly `C¹` action of a manifold group, the
  tangent representation is continuous.
* `TauCeti.tangentRepresentation_eq_one_iff`, `TauCeti.ker_tangentRepresentation`: the kernel of
  the tangent representation of a finite stabilizer acting by `C¹` maps is the germ kernel.
* `TauCeti.tangentRepresentation_eq_one_iff_forall_smul_eq`: on a connected Hausdorff manifold, an
  element of a finite stabilizer has derivative the identity at `x` exactly when it acts trivially.
* `TauCeti.injective_tangentRepresentation`: for a faithful action on a connected Hausdorff
  manifold, the tangent representation of a finite stabilizer is injective.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* I. Moerdijk and D. A. Pronk, *Orbifolds, sheaves and groupoids*, K-Theory 12 (1997), 3–21, for
  the frame bundle of an effective orbifold and the freeness of the action on frames.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Ch. 1, for the linear isotropy action and the
  ineffective kernel.
-/

public section

open MulAction TauCeti.MulAction Set Filter Topology
open scoped Manifold

namespace TauCeti

section Defs

variable {𝕜 E H M G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [Group G] [MulAction G M] {x : M}

/-- The tangent representation of the stabilizer of `x` on `T_x M`: an element `g` of the
stabilizer acts by the derivative of `g • ·` at `x`, which maps `T_x M` to `T_{g • x} M = T_x M`.
Multiplicativity is the chain rule at the fixed point `x`. -/
noncomputable def tangentRepresentation
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    ContRepresentation 𝕜 (stabilizer G x) (TangentSpace I x) :=
  .ofMonoidHom
    { toFun g := mfderiv I I (fun y : M ↦ (g : G) • y) x
      map_one' := by
        have h1 : (fun y : M ↦ ((1 : stabilizer G x) : G) • y) = id := funext fun y ↦ by simp
        rw [h1, mfderiv_id, ContinuousLinearMap.one_def]
      map_mul' g h := by
        have hgh : (fun y : M ↦ ((g * h : stabilizer G x) : G) • y) =
            (fun y : M ↦ (g : G) • y) ∘ fun y : M ↦ (h : G) • y := by
          ext y
          simp [mul_smul]
        rw [hgh]
        exact mfderiv_comp_of_apply_eq_self (hd g g.2) (hd h h.2) h.2 }

@[simp]
theorem tangentRepresentation_apply
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (g : stabilizer G x) :
    tangentRepresentation hd g = mfderiv I I (fun y : M ↦ (g : G) • y) x :=
  (rfl)

/-- The invariant vectors of the tangent representation at `x` are the tangent vectors fixed by
the differential at `x` of every element of the stabilizer of `x`. -/
theorem mem_invariants_tangentRepresentation_iff
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    {v : TangentSpace I x} :
    v ∈ (tangentRepresentation hd).toRepresentation.invariants ↔
      ∀ g ∈ stabilizer G x, mfderiv I I (fun y : M ↦ g • y) x v = v := by
  simp only [Representation.mem_invariants, ContRepresentation.toRepresentation_apply,
    tangentRepresentation_apply, Subtype.forall]
  -- The two sides compare `d(g • ·)_x v` with `v` in the tangent spaces at `x` and at `g • x`.
  rfl

/-- At a point fixed by the whole group, the invariant vectors of the tangent representation are
the tangent vectors fixed by the differential of every group element. -/
theorem mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (hx : x ∈ fixedPoints G M) {v : TangentSpace I x} :
    v ∈ (tangentRepresentation hd).toRepresentation.invariants ↔
      ∀ g : G, mfderiv I I (fun y : M ↦ g • y) x v = v := by
  rw [mem_invariants_tangentRepresentation_iff]
  exact ⟨fun h g ↦ h g (hx g), fun h g _ ↦ h g⟩

/-- **Conjugation of tangent representations along an orbit.** The derivative at `x` of the action
of `h` intertwines the tangent representation at `x` with the tangent representation at `h • x`,
along the conjugation isomorphism `g ↦ h * g * h⁻¹` between the stabilizers. -/
theorem mfderiv_smul_comp_tangentRepresentation {h : G}
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (hd' : ∀ g ∈ stabilizer G (h • x), MDifferentiableAt I I (fun y : M ↦ g • y) (h • x))
    (hh : MDifferentiableAt I I (fun y : M ↦ h • y) x) (g : stabilizer G x) :
    (mfderiv I I (fun y : M ↦ h • y) x).comp (tangentRepresentation hd g) =
      (tangentRepresentation hd' (stabilizerEquivStabilizer rfl g)).comp
        (mfderiv I I (fun y : M ↦ h • y) x) := by
  let g' := stabilizerEquivStabilizer (rfl : h • x = h • x) g
  have hcomm : (fun y : M ↦ h • y) ∘ (fun y : M ↦ (g : G) • y) =
      (fun y : M ↦ (g' : G) • y) ∘ fun y : M ↦ h • y := by
    ext y
    simp [g', stabilizerEquivStabilizer_apply, mul_smul]
  have hl := mfderiv_comp_of_apply_eq_self hh (hd g g.2) g.2
  rw [hcomm, mfderiv_comp x (hd' g' g'.2) hh] at hl
  rw [tangentRepresentation_apply, tangentRepresentation_apply]
  exact hl.symm

end Defs

section Invariants

open scoped ContDiff

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Group G] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [MulAction G M] [ContMDiffConstSMul I ∞ G M]

variable (I G) in
/-- The tangent vectors at `x` fixed by the differential at `x` of every element of the stabilizer
of `x`, for a group acting by smooth maps: the invariants of the tangent representation. -/
noncomputable def tangentInvariants (x : M) : Submodule 𝕜 (TangentSpace I x) :=
  (tangentRepresentation fun g (_ : g ∈ stabilizer G x) ↦
    (contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt
      (by simp)).toRepresentation.invariants

/-- The invariant tangent vectors are the invariants of the tangent representation, for any proof
that the stabilizer acts by maps differentiable at `x`. -/
theorem tangentInvariants_eq {x : M}
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    tangentInvariants I G x = (tangentRepresentation hd).toRepresentation.invariants :=
  (rfl)

/-- The invariant tangent vectors at `x` are those fixed by the differential at `x` of every element
of the stabilizer of `x`. -/
theorem mem_tangentInvariants_iff {x : M} {v : TangentSpace I x} :
    v ∈ tangentInvariants I G x ↔ ∀ g ∈ stabilizer G x, mfderiv I I (g • ·) x v = v :=
  mem_invariants_tangentRepresentation_iff _

/-- At a point fixed by the whole group, the invariant tangent vectors are those fixed by the
differential of every group element. -/
theorem mem_tangentInvariants_iff_of_mem_fixedPoints {x : M} (hx : x ∈ fixedPoints G M)
    {v : TangentSpace I x} :
    v ∈ tangentInvariants I G x ↔ ∀ g : G, mfderiv I I (g • ·) x v = v :=
  mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints _ hx

variable (I G M) in
/-- The **stratum of dimension `d`** of the fixed set: the fixed points `p` at which the tangent
vectors fixed by every differential `d(g •)_p` form a subspace of dimension `d`. -/
@[expose] def fixedPointsFinrank (d : ℕ) : Set M :=
  {p | p ∈ fixedPoints G M ∧ Module.finrank 𝕜 (tangentInvariants I G p) = d}

@[simp]
theorem mem_fixedPointsFinrank_iff {d : ℕ} {p : M} :
    p ∈ fixedPointsFinrank I G M d ↔
      p ∈ fixedPoints G M ∧ Module.finrank 𝕜 (tangentInvariants I G p) = d :=
  Iff.rfl

theorem fixedPointsFinrank_subset_fixedPoints (d : ℕ) :
    fixedPointsFinrank I G M d ⊆ fixedPoints G M :=
  fun _ hp ↦ hp.1

/-- Every fixed point lies in the stratum of the dimension of its invariant tangent vectors. -/
theorem iUnion_fixedPointsFinrank : ⋃ d, fixedPointsFinrank I G M d = fixedPoints G M :=
  subset_antisymm (iUnion_subset fixedPointsFinrank_subset_fixedPoints)
    fun _ hp ↦ mem_iUnion.2 ⟨_, hp, rfl⟩

/-- Strata of different dimensions are disjoint. -/
theorem disjoint_fixedPointsFinrank {d d' : ℕ} (h : d ≠ d') :
    Disjoint (fixedPointsFinrank I G M d) (fixedPointsFinrank I G M d') :=
  disjoint_left.2 fun _ hp hp' ↦ h (hp.2.symm.trans hp'.2)

/-- The differential of a map into the fixed set takes values in the invariant tangent vectors. -/
theorem range_mfderiv_le_tangentInvariants {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {f : N → M} (hf : ∀ y, f y ∈ fixedPoints G M) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap ≤ tangentInvariants I G (f y) := by
  by_cases hfy : MDifferentiableAt J I f y
  swap
  · simp [mfderiv_zero_of_not_mdifferentiableAt hfy]
  rintro _ ⟨u, rfl⟩
  refine (mem_tangentInvariants_iff_of_mem_fixedPoints (hf y)).2 fun g ↦ ?_
  have hg : MDifferentiableAt I I (g • ·) (f y) :=
    (contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt (by simp)
  have hcomp : (g • ·) ∘ f = f := funext fun z ↦ hf z g
  have h := mfderiv_comp y hg hfy
  rw [hcomp] at h
  exact (DFunLike.congr_fun h u).symm

/-- **The tangent spaces of a stratum.** An immersion of a manifold of dimension `d` into the
stratum of dimension `d` of the fixed set has, as tangent images, the invariant tangent vectors. -/
theorem range_mfderiv_eq_tangentInvariants [FiniteDimensional 𝕜 E] {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] {d : ℕ} {f : N → M}
    (hf : ∀ y, f y ∈ fixedPointsFinrank I G M d) (hE' : Module.finrank 𝕜 E' = d) {y : N}
    (hinj : Function.Injective (mfderiv J I f y)) :
    LinearMap.range (mfderiv J I f y).toLinearMap = tangentInvariants I G (f y) := by
  have : FiniteDimensional 𝕜 E' := FiniteDimensional.of_injective (mfderiv J I f y).toLinearMap hinj
  refine Submodule.eq_of_le_of_finrank_eq
    (range_mfderiv_le_tangentInvariants (fun z ↦ (hf z).1) y) ?_
  rw [LinearMap.finrank_range_of_inj hinj, (hf y).2]
  exact hE'

end Invariants

section Continuity

variable {𝕜 E H M F HG G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G] [Group G] [MulAction G M] {x : M}

/-- **Continuity of the tangent representation.** If a group `G`, modelled on `IG`, acts on `M`
by a map `G × M → M` that is jointly `C¹`, then the tangent representation of the stabilizer of
`x` is continuous for the subspace topology of the stabilizer. -/
theorem continuous_tangentRepresentation (IG : ModelWithCorners 𝕜 F HG) [IsManifold IG 1 G]
    [ContMDiffSMul IG I 1 G M]
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    Continuous (tangentRepresentation hd) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  -- The derivative of `g • ·` at `x`, read in the tangent coordinates of the base points `x`
  -- and `g • x`, is continuous in `g` at `g₀`.
  have hf : ContMDiffAt (IG.prod I) I 1 (Function.uncurry fun (g : G) (y : M) ↦ g • y)
      ((g₀ : G), x) :=
    (ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := 1) (G := G) (M := M)).contMDiffAt
  have h := (ContMDiffAt.mfderiv (fun (g : G) (y : M) ↦ g • y) (fun _ ↦ x) hf
    (contMDiffAt_const (n := 0)) (by simp)).continuousAt
  -- On the stabilizer both base points are `x`, so the coordinate changes are the identity.
  have hcomp : inTangentCoordinates I I (fun _ : G ↦ x) (fun g : G ↦ g • x)
      (fun g : G ↦ mfderiv I I (fun y : M ↦ g • y) x) (g₀ : G) ∘ Subtype.val =
        (tangentRepresentation hd : stabilizer G x → _) :=
    funext fun g ↦ (Manifold.inTangentCoordinates_eq_self_of_eq (x₀ := (g₀ : G)) (x := g) _ _ _
      rfl (g.2.trans g₀.2.symm)).trans (tangentRepresentation_apply hd g).symm
  rw [← hcomp]
  exact h.comp continuous_subtype_val.continuousAt

end Continuity

section Detection

variable {𝕜 E H M G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [Group G] [MulAction G M] [ContinuousConstSMul G M]
  {x : M} [Finite (stabilizer G x)]

omit [CompleteSpace E] in
/-- **The tangent representation detects the ineffective kernel.** Let the finite stabilizer of
`x` act by maps that are `C¹` at `x` on a manifold without boundary. An element of the stabilizer
has derivative the identity at `x` exactly when it acts as the identity near `x`, that is, lies in
the germ kernel at `x`. -/
theorem tangentRepresentation_eq_one_iff
    (hs : ∀ g ∈ stabilizer G x, ContMDiffAt I I 1 (fun y : M ↦ g • y) x) (g : stabilizer G x) :
    tangentRepresentation (fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero) g = 1 ↔
      (g : G) ∈ germKernel G x := by
  let : Fintype (stabilizer G x) := Fintype.ofFinite _
  have : ContinuousConstSMul (stabilizer G x) M := ⟨fun g ↦ continuous_const_smul (g : G)⟩
  let : Invertible (Fintype.card (stabilizer G x) : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- The chart of `M` at `x`, as an open partial homeomorphism to `E`.
  let χ := (chartAt H x).transHomeomorph I.toHomeomorph
  have hxχ : x ∈ χ.source := mem_chart_source H x
  have hχ : ⇑χ = extChartAt I x := by
    ext
    simp [χ]
  have hχs : ⇑χ.symm = (extChartAt I x).symm := by
    ext
    simp [χ]
  let σ := tangentRepresentation (fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero)
  -- In the chart `χ`, each element of the stabilizer has strict derivative its image under `σ`.
  have hσ (k : stabilizer G x) :
      HasStrictFDerivAt (χ ∘ (k • ·) ∘ χ.symm) (σ k) (χ x) := by
    have h := (hs k k.2).hasStrictFDerivAt_extChartAt_conj
    rw [mem_stabilizer_iff.mp k.2] at h
    rw [tangentRepresentation_apply, ((hs k k.2).mdifferentiableAt one_ne_zero
      ).mfderiv_eq_fderiv_extChartAt_conj k.2, hχ, hχs]
    exact h
  -- `σ`, a representation on `T_x M`, is used as a representation on the model space `E`.
  refine (χ.map_eq_one_iff_mem_germKernel hxχ (fun k ↦ k.2) σ hσ g).trans ?_
  simp only [mem_germKernel, Subgroup.smul_def]

omit [CompleteSpace E] in
/-- The kernel of the tangent representation of a finite stabilizer acting by maps that are `C¹`
at `x` is the germ kernel at `x`, viewed as a subgroup of the stabilizer. -/
theorem ker_tangentRepresentation
    (hs : ∀ g ∈ stabilizer G x, ContMDiffAt I I 1 (fun y : M ↦ g • y) x) :
    (tangentRepresentation (fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero)).toMonoidHom.ker =
      (germKernel G x).subgroupOf (stabilizer G x) := by
  ext g
  rw [MonoidHom.mem_ker, ContRepresentation.toMonoidHom_apply, Subgroup.mem_subgroupOf,
    tangentRepresentation_eq_one_iff hs]

/-- **The tangent representation detects trivially acting elements.** For a finite stabilizer
acting by `C¹` maps on a connected Hausdorff manifold without boundary, an element of the
stabilizer of `x` has derivative the identity at `x` exactly when it acts trivially on `M`. -/
theorem tangentRepresentation_eq_one_iff_forall_smul_eq [T2Space M] [PreconnectedSpace M]
    (hs : ∀ g ∈ stabilizer G x, ContMDiff I I 1 fun y : M ↦ g • y) (g : stabilizer G x) :
    tangentRepresentation (fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero) g = 1 ↔
      ∀ y : M, (g : G) • y = y := by
  rw [tangentRepresentation_eq_one_iff fun g hg ↦ (hs g hg).contMDiffAt,
    mem_germKernel_iff_mem_interior_fixedBy]
  refine ⟨fun h y ↦ ?_, fun h ↦ ?_⟩
  · have hg : IsOfFinOrder (g : G) :=
      (stabilizer G x).subtype.isOfFinOrder (isOfFinOrder_of_finite g)
    exact interior_subset (subset_interior_fixedBy_of_isPreconnected (g : G) hg (hs g g.2)
      isPreconnected_univ ⟨x, mem_univ x, h⟩ (mem_univ y))
  · rw [(Set.eq_univ_iff_forall (s := fixedBy M (g : G))).mpr h, interior_univ]
    exact mem_univ x

/-- **Effective actions act freely on frames.** For a faithful action by `C¹` maps on a connected
Hausdorff manifold without boundary, the tangent representation of a finite stabilizer is
injective: the only element fixing `x` with derivative the identity at `x` is `1`. -/
theorem injective_tangentRepresentation [T2Space M] [PreconnectedSpace M] [FaithfulSMul G M]
    (hs : ∀ g ∈ stabilizer G x, ContMDiff I I 1 fun y : M ↦ g • y) :
    Function.Injective
      (tangentRepresentation fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ Subtype.ext ?_
  refine eq_of_smul_eq_smul (α := M) fun y ↦ ?_
  rw [(tangentRepresentation_eq_one_iff_forall_smul_eq hs g).mp hg y, OneMemClass.coe_one,
    one_smul]

end Detection

end TauCeti
