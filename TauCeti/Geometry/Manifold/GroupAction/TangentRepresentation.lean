/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel

import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# The tangent representation of an isotropy group

Let a group `G` act on a manifold `M`, and let `x : M`. If every element of the stabilizer of `x`
acts by a map differentiable at `x`, the chain rule makes `g ↦ mfderiv I I (g • ·) x` a continuous
representation `TauCeti.tangentRepresentation` of the stabilizer on the tangent space `T_x M`.
Moving `x` along its orbit by `h` conjugates this representation: the derivative of `h • ·` at `x`
intertwines it with the tangent representation at `h • x`, along Mathlib's conjugation isomorphism
`MulAction.stabilizerEquivStabilizer` of the two stabilizers.

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

## Main results

* `TauCeti.mfderiv_smul_comp_tangentRepresentation`: the tangent representations at `x` and
  `h • x` are intertwined by the derivative of `h • ·`.
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

section Detection

variable {𝕜 E H M G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [Group G] [MulAction G M] [ContinuousConstSMul G M]
  {x : M} [Finite (stabilizer G x)]

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
