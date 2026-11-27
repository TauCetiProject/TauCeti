/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Connection

/-!
# Local potentials of connection forms

Let `A` be a connection form on a smooth principal `G`-bundle `P → B`
(`TauCeti.PrincipalBundle.IsConnectionForm`), a one-form on the charted total space
`TauCeti.ManifoldTotalSpace G P` with values in the Lie algebra `𝔤`. Pulled back along a local
section `s` of `P`, it becomes the **local potential** `s^* A`, a `𝔤`-valued one-form on the base.
This file proves how the local potential changes with the section, and that the potential along
one section through a point determines the connection over that point. The converse, gluing a
connection form from local potentials which transform correctly, is not treated here.

**The transformation law.** If the section `s` is changed to `s · g` by a map `g` into `G`, the
potential changes by

`(s · g)^* A = Ad(g⁻¹) (s^* A) + g^* θ`,

where `θ` is the left Maurer–Cartan form of `G` (`TauCeti.leftMaurerCartanForm`), so that
`g^* θ = g⁻¹ dg` for a matrix group
(`TauCeti.PrincipalBundle.IsConnectionForm.mpullback_op_smul_apply_sub_mpullback_apply`). The
law holds for maps `s` and `g` defined on any manifold, not only for sections over the base. The
derivative of `y ↦ s y · g y` is `d(R_g) (ds v) + (θ (dg v))♯` by the Leibniz rule for the action
(`TauCeti.PrincipalBundle.mfderiv_op_smul_apply`); equivariance of `A` turns the first term into
`Ad(g⁻¹) (A (ds v))`, and reproduction `A(ξ♯) = ξ` evaluates the second. For a commutative group
the adjoint action is trivial and the law reads `(s · g)^* A = s^* A + g^* θ`
(`TauCeti.PrincipalBundle.IsConnectionForm.mpullback_op_smul_apply_of_isMulCommutative`); for the
circle and `g = exp (i φ)` this is the familiar change `A + i dφ` of an abelian gauge potential.
Applied with `s` the identity of the total space and `g` a smooth map `u : P → G`, the same
theorem computes the pullback of `A` by the map `p ↦ p · u(p)`, which for an equivariant `u` is
a gauge transformation.

**Uniqueness.** A connection form is determined over a point `b` of the base by its local
potential at `b` along one section through `b`. At the point `s b` every tangent vector `w` is
`ds (dπ w)` plus a vertical vector `ξ♯`, since `π ∘ s = id` near `b`
(`TauCeti.PrincipalBundle.exists_eq_mfderiv_add_rightFundamentalVectorField`), so
`A (w) = (s^* A)(dπ w) + ξ`, and equivariance carries this to the whole fibre over `b`, which is
the orbit of `s b`. Hence two connection forms whose potentials along `s` agree at `b` agree at
every point of the fibre over `b`
(`TauCeti.PrincipalBundle.IsConnectionForm.apply_eq_of_mpullback_apply_eq`).

## Main results

* `TauCeti.PrincipalBundle.mfderiv_op_smul_apply`: the Leibniz rule
  `d(s · g) v = d(R_g)(ds v) + (θ (dg v))♯`.
* `TauCeti.PrincipalBundle.IsConnectionForm.mpullback_op_smul_apply_sub_mpullback_apply`: the
  transformation law `(s · g)^* A = Ad(g⁻¹) (s^* A) + g^* θ`.
* `TauCeti.PrincipalBundle.exists_eq_mfderiv_add_rightFundamentalVectorField`: at a point of a
  local section, every tangent vector is the image of its projection plus a vertical vector.
* `TauCeti.PrincipalBundle.IsConnectionForm.apply_eq_of_mpullback_apply_eq`: a connection form is
  determined over a point by its local potential there.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §1, Proposition 1.4 (the local form of a connection and its transformation law).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §11.4 (local descriptions of principal connections).
-/

public section

noncomputable section

open Bundle Function Manifold MulOpposite Set
open scoped ContDiff Manifold Topology

namespace TauCeti.PrincipalBundle

variable {B G : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [IsManifold IB ∞ B] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-! ### The Leibniz rule for the action -/

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- **The Leibniz rule for the right action.** For maps `s` into the total space and `g` into the
structure group, differentiable at `x`, the derivative of `y ↦ s y · g y` at `x` is the right
translate of the derivative of `s`, plus the fundamental vector field generated by the
Maurer–Cartan form `θ (dg v) = g⁻¹ dg (v)`:

`d(s · g) v = d(R_{g x}) (ds v) + (θ (dg v))♯ (s x · g x)`. -/
theorem mfderiv_op_smul_apply {s : M → ManifoldTotalSpace G P} {g : M → G} {x : M}
    (hs : MDifferentiableAt IM (IB.prod IG) s x) (hg : MDifferentiableAt IM IG g x)
    (v : TangentSpace IM x) :
    mfderiv IM (IB.prod IG) (fun y ↦ op (g y) • s y) x v =
      mfderiv (IB.prod IG) (IB.prod IG) (fun p ↦ op (g x) • p) (s x)
          (mfderiv IM (IB.prod IG) s x v) +
        rightFundamentalVectorField (I := IG) (G := G) (IB.prod IG)
          ((leftMaurerCartanForm IG G).val (g x) ![mfderiv IM IG g x v]) (op (g x) • s x) := by
  have hact : MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
      (fun p : ManifoldTotalSpace G P × G ↦ op p.2 • p.1) (s x, g x) :=
    (contMDiff_op_smul (n := 1) _).mdifferentiableAt one_ne_zero
  -- The map is the action composed with `y ↦ (s y, g y)`, and the derivative of the action is the
  -- sum of its partial derivatives.
  have hcomp := mfderiv_comp_apply_of_eq (f := fun y ↦ (s y, g y))
    (g := fun p : ManifoldTotalSpace G P × G ↦ op p.2 • p.1) x hact (hs.prodMk hg) rfl v
  rw [mfderiv_prodMk hs hg, mfderiv_prod_eq_add_apply hact] at hcomp
  dsimp only [ContinuousLinearMap.prod_apply] at hcomp
  refine hcomp.trans (congrArg _ ?_)
  -- The partial derivative in the group variable sends the left-invariant vector field of `ξ` to
  -- the fundamental vector field of `ξ`, and `dg v` is the left-invariant field of `θ (dg v)`.
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (mfderiv IM IG g x v)
  rw [← hξ, leftMaurerCartanForm_apply_mulInvariantVectorField]
  exact (congrArg (mfderiv IG (IB.prod IG) (fun h ↦ op h • s x) (g x)) hξ.symm).trans
    (mfderiv_op_smul_mulInvariantVectorField (mdifferentiableAt_orbit one_ne_zero (s x) (g x)) ξ)

namespace IsConnectionForm

variable {A A' : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}

/-! ### The transformation law -/

/-- **The transformation law of local potentials.** Let `A` be a connection form, and `s` and `g`
maps from a manifold into the total space and into the structure group, differentiable at `x`.
The pullback of `A` along `y ↦ s y · g y` satisfies

`(s · g)^* A - g^* θ = Ad(g⁻¹) (s^* A)`

at `x`, where `θ` is the left Maurer–Cartan form, so `g^* θ = g⁻¹ dg` for a matrix group. For a
local section `s` of the bundle this is the change `(s · g)^* A = Ad(g⁻¹) (s^* A) + g^* θ` of the
local potential `s^* A` under the change of section `s ↦ s · g`. -/
theorem mpullback_op_smul_apply_sub_mpullback_apply (hA : IsConnectionForm A)
    {s : M → ManifoldTotalSpace G P} {g : M → G} {x : M}
    (hs : MDifferentiableAt IM (IB.prod IG) s x) (hg : MDifferentiableAt IM IG g x)
    (v : TangentSpace IM x) :
    mpullback (F := EG) IM (IB.prod IG) (fun y ↦ op (g y) • s y) A.val x ![v] -
        mpullback (F := EG) IM IG g (leftMaurerCartanForm IG G).val x ![v] =
      Lie.adjointContinuousLinearMap (I := IG) (g x)⁻¹
        (mpullback (F := EG) IM (IB.prod IG) s A.val x ![v]) := by
  rw [mpullback_apply_one, mpullback_apply_one, mpullback_apply_one, mfderiv_op_smul_apply hs hg,
    ContinuousAlternatingMap.vecCons_add, hA.apply_mfderiv_op_smul]
  -- By reproduction, `A` takes the value `θ (dg v)` on the vertical term.
  have hθ : A.val (op (g x) • s x) ![rightFundamentalVectorField (I := IG) (G := G) (IB.prod IG)
      ((leftMaurerCartanForm IG G).val (g x) ![mfderiv IM IG g x v]) (op (g x) • s x)] =
      (leftMaurerCartanForm IG G).val (g x) ![mfderiv IM IG g x v] :=
    hA.apply_rightFundamentalVectorField _ _
  rw [hθ]
  exact add_sub_cancel_right _ _

/-- **The transformation law for a commutative structure group.** When `G` is commutative its
adjoint action is trivial, and the pullback of a connection form `A` along `y ↦ s y · g y` is
`(s · g)^* A = s^* A + g^* θ`. -/
theorem mpullback_op_smul_apply_of_isMulCommutative [IsMulCommutative G]
    (hA : IsConnectionForm A) {s : M → ManifoldTotalSpace G P} {g : M → G} {x : M}
    (hs : MDifferentiableAt IM (IB.prod IG) s x) (hg : MDifferentiableAt IM IG g x)
    (v : TangentSpace IM x) :
    mpullback (F := EG) IM (IB.prod IG) (fun y ↦ op (g y) • s y) A.val x ![v] =
      mpullback (F := EG) IM (IB.prod IG) s A.val x ![v] +
        mpullback (F := EG) IM IG g (leftMaurerCartanForm IG G).val x ![v] := by
  rw [← sub_eq_iff_eq_add, hA.mpullback_op_smul_apply_sub_mpullback_apply hs hg,
    Lie.adjointContinuousLinearMap_eq_id]
  -- The identity of the Lie algebra applied to a value in the model space `EG`.
  rfl

end IsConnectionForm

/-! ### Uniqueness -/

omit [IsManifold IB ∞ B] in
/-- **Tangent vectors along a local section.** Let `s` be a map from the base into the total space
which is a section near `b`, that is `π (s y) = y` for `y` near `b`, and differentiable at `b`.
Every tangent vector `w` at `s b` is the image `ds (dπ w)` of its projection plus a vertical
vector, the fundamental vector field of some `ξ`. -/
theorem exists_eq_mfderiv_add_rightFundamentalVectorField {s : B → ManifoldTotalSpace G P}
    {b : B} (hs : MDifferentiableAt IB (IB.prod IG) s b)
    (hsec : (fun y ↦ ((ManifoldTotalSpace.homeomorph G P).symm (s y)).proj) =ᶠ[𝓝 b] id)
    (w : TangentSpace (IB.prod IG) (s b)) :
    ∃ ξ : GroupLieAlgebra IG G, w = mfderiv IB (IB.prod IG) s b
        (mfderiv (IB.prod IG) IB
          (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
          (s b) w) +
      rightFundamentalVectorField (IB.prod IG) ξ (s b) := by
  set proj := fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj
  have hπ : MDifferentiableAt (IB.prod IG) IB proj (s b) :=
    (ManifoldTotalSpace.contMDiff_proj 1 G P IB IG _).mdifferentiableAt one_ne_zero
  -- Since `proj ∘ s = id` near `b`, the vector `w - ds (dπ w)` is vertical.
  have hsec' : proj ∘ s =ᶠ[𝓝 b] id := hsec
  have hcomp := mfderiv_comp_apply_of_eq b hπ hs rfl (mfderiv (IB.prod IG) IB proj (s b) w)
  rw [hsec'.mfderiv_eq, mfderiv_id] at hcomp
  have hvert : w - mfderiv IB (IB.prod IG) s b (mfderiv (IB.prod IG) IB proj (s b) w) ∈
      (mfderiv (IB.prod IG) IB proj (s b)).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, ← hcomp, sub_eq_zero]
    -- `hcomp` holds up to the cast between the tangent spaces at `b` and at `π (s b) = b`.
    rfl
  rw [← range_rightFundamentalLinearMap_eq_ker_mfderiv_proj] at hvert
  obtain ⟨ξ, hξ⟩ := hvert
  exact ⟨ξ, by rw [← rightFundamentalLinearMap_apply, hξ, add_sub_cancel]⟩

namespace IsConnectionForm

variable {A A' : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}

/-- **A connection form is determined by a local potential.** Let `s` be a map from the base into
the total space which is a section near `b` and differentiable at `b`. If two connection forms
have the same local potential `s^* A = s^* A'` at `b`, they agree at every point of the fibre over
`b`. -/
theorem apply_eq_of_mpullback_apply_eq (hA : IsConnectionForm A) (hA' : IsConnectionForm A')
    {s : B → ManifoldTotalSpace G P} {b : B} (hs : MDifferentiableAt IB (IB.prod IG) s b)
    (hsec : (fun y ↦ ((ManifoldTotalSpace.homeomorph G P).symm (s y)).proj) =ᶠ[𝓝 b] id)
    (heq : ∀ v : TangentSpace IB b, mpullback (F := EG) IB (IB.prod IG) s A.val b ![v] =
      mpullback (F := EG) IB (IB.prod IG) s A'.val b ![v])
    {x : ManifoldTotalSpace G P} (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj = b) :
    A.val x = A'.val x := by
  -- The two forms agree at `s b`, on the image of `ds` by hypothesis and on vertical vectors by
  -- reproduction.
  have hsb (w : TangentSpace (IB.prod IG) (s b)) : A.val (s b) ![w] = A'.val (s b) ![w] := by
    obtain ⟨ξ, hξ⟩ := exists_eq_mfderiv_add_rightFundamentalVectorField hs hsec w
    rw [hξ, ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_add,
      hA.apply_rightFundamentalVectorField, hA'.apply_rightFundamentalVectorField]
    congr 1
    exact (mpullback_apply_one _ _ _ _).symm.trans ((heq _).trans (mpullback_apply_one _ _ _ _))
  -- The point `x` lies in the fibre over `b`, so it is `s b · g` for some `g`.
  obtain ⟨g, rfl⟩ : ∃ g : G, op g • s b = x := by
    obtain ⟨⟨b₁, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
    obtain ⟨⟨b₂, q⟩, hq⟩ := (ManifoldTotalSpace.homeomorph G P).surjective (s b)
    have hb₂ : b₂ = b := by simpa [← hq] using hsec.self_of_nhds
    rw [Homeomorph.symm_apply_apply] at hx
    subst hx hb₂
    exact ⟨division G q p, by rw [← hq, ManifoldTotalSpace.smul_homeomorph, smul_division]⟩
  -- Equivariance carries the agreement at `s b` to `s b · g`: every tangent vector there is the
  -- right translate of a tangent vector at `s b`.
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  have hmd (h : G) (y : ManifoldTotalSpace G P) :
      MDifferentiableAt (IB.prod IG) (IB.prod IG) (fun z ↦ op h • z) y :=
    (contMDiff_const_smul (I := IB.prod IG) (n := 1) (op h) y).mdifferentiableAt one_ne_zero
  have hw : w 0 = mfderiv (IB.prod IG) (IB.prod IG) (fun z ↦ op g • z) (s b)
      (mfderiv (IB.prod IG) (IB.prod IG) (fun z ↦ op g⁻¹ • z) (op g • s b) (w 0)) := by
    rw [← mfderiv_comp_apply_of_eq _ (hmd g _) (hmd g⁻¹ _) (by simp [smul_smul])]
    have hid : ((fun z : ManifoldTotalSpace G P ↦ op g • z) ∘ fun z ↦ op g⁻¹ • z) = id := by
      funext z
      simp [smul_smul]
    rw [hid, mfderiv_id, ContinuousLinearMap.id_apply]
  have hw' : w = ![w 0] := by
    funext i
    fin_cases i
    rfl
  rw [hw', hw]
  exact (hA.apply_mfderiv_op_smul g (s b) _).trans
    ((congrArg _ (hsb _)).trans (hA'.apply_mfderiv_op_smul g (s b) _).symm)

end IsConnectionForm

end TauCeti.PrincipalBundle
