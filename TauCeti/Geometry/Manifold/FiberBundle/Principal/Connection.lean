/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.MaurerCartan
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField

/-!
# Principal connections

Let `P` be a smooth principal `G`-bundle over a manifold `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P`, on which `G` acts on the right, `x ↦ x · g`. Every element `ξ` of
the Lie algebra `𝔤 = T₁G` generates the fundamental vector field `ξ♯`
(`TauCeti.rightFundamentalVectorField`). A **connection form** on `P`
(`TauCeti.PrincipalBundle.IsConnectionForm`) is a smooth one-form `A` on the total space with
values in `𝔤` which

* reproduces the generators of the fundamental vector fields, `A(ξ♯) = ξ`, and
* is equivariant, `R_g^* A = Ad(g⁻¹) ∘ A`.

This file proves that **every smooth principal bundle over a Hausdorff σ-compact
finite-dimensional base has a connection form** (`TauCeti.PrincipalBundle.exists_isConnectionForm`).
Over the base set of a trivialization `e` of the atlas, write `x = e⁻¹(π x, g_e(x))`. The fibre
coordinate `g_e` satisfies `g_e(x · g) = g_e(x) g`, so the pullback `g_e^* θ` of the left
Maurer–Cartan form of `G` (`TauCeti.maurerCartanForm`) is a connection form over that base set: it
takes the value `ξ` on `ξ♯`, because `ξ♯` is carried to the left-invariant vector field of `ξ`, and
it transforms by `Ad(g⁻¹)` because `θ` does under right translations
(`TauCeti.maurerCartanForm_apply_mfderiv_mul_right`). A smooth partition of unity `ρ_e` on the base
subordinate to the base sets glues these local forms to

`A = ∑_e (ρ_e ∘ π) g_e^* θ`.

The weights are invariant under the action, so both laws survive the gluing: equivariance
because each term is equivariant, reproduction because the weights add up to `1`. Smoothness of
the glued form is `TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`.

A connection form splits every tangent vector `v` of the total space into the vertical vector
`A(v)♯` and the horizontal vector `v - A(v)♯`, on which `A` vanishes
(`TauCeti.PrincipalBundle.IsConnectionForm.apply_sub_rightFundamentalVectorField`), and the only
vertical vector on which `A` vanishes is zero
(`TauCeti.PrincipalBundle.IsConnectionForm.apply_rightFundamentalVectorField_eq_zero_iff`). Two
connection forms agree on vertical vectors
(`TauCeti.PrincipalBundle.IsConnectionForm.sub_apply_rightFundamentalVectorField`), and their
affine combinations are connection forms
(`TauCeti.PrincipalBundle.IsConnectionForm.smul_add_smul`).

The Lie algebra `GroupLieAlgebra IG G` is the model space `EG` of `G`, which carries the norm, so
connection forms take values in `EG`, as the Maurer–Cartan form does.

## Main definitions

* `TauCeti.PrincipalBundle.IsConnectionForm A`: the one-form `A` is a connection form.

## Main results

* `TauCeti.PrincipalBundle.exists_isConnectionForm`: existence of connection forms.
* `TauCeti.PrincipalBundle.IsConnectionForm.apply_sub_rightFundamentalVectorField`: the
  horizontal part `v - A(v)♯` of a tangent vector.
* `TauCeti.PrincipalBundle.IsConnectionForm.smul_add_smul`: affine combinations of connection
  forms.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §1 (connection forms) and Theorem II.2.1 (existence of connections).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §11.1 and Lemma 11.3 (principal connections and their existence).
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
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [IsManifold IB ∞ B] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]

/-- A **connection form** on a smooth principal bundle, or more generally on a smooth fibre bundle
with model fibre `G` whose fibres carry right actions of `G`: a smooth one-form `A` on the total
space, with values in the Lie algebra `GroupLieAlgebra IG G` (the model space `EG`), which takes
the value `ξ` on the fundamental vector field `ξ♯` of every `ξ`, and which is equivariant,
`A_{x · g}(d(R_g)_x v) = Ad(g⁻¹) (A_x v)`, that is `R_g^* A = Ad(g⁻¹) ∘ A`. -/
structure IsConnectionForm (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) : Prop where
  /-- A connection form takes the value `ξ` on the fundamental vector field of `ξ`. -/
  apply_rightFundamentalVectorField (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    A.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ
  /-- A connection form is equivariant: right translation by `g` transforms it by `Ad(g⁻¹)`. -/
  apply_mfderiv_op_smul (g : G) (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    A.val (op g • x) ![mfderiv (IB.prod IG) (IB.prod IG) (fun y ↦ op g • y) x v] =
      Lie.adjointContinuousLinearMap (I := IG) g⁻¹ (A.val x ![v])

namespace IsConnectionForm

variable {A A' : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}

/-- A connection form vanishes on the fundamental vector field of `ξ` only for `ξ = 0`. -/
theorem apply_rightFundamentalVectorField_eq_zero_iff (hA : IsConnectionForm A)
    (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    A.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = 0 ↔ ξ = 0 := by
  rw [hA.apply_rightFundamentalVectorField]
  -- The two zeros are those of the model space and of the Lie algebra, which is that space.
  exact Iff.rfl

/-- **The horizontal part of a tangent vector.** Subtracting from `v` the fundamental vector field
of `A(v)`, its vertical part, leaves a horizontal vector, one on which the connection form
vanishes. -/
theorem apply_sub_rightFundamentalVectorField (hA : IsConnectionForm A)
    (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    A.val x ![v - rightFundamentalVectorField (I := IG) (G := G) (IB.prod IG) (A.val x ![v]) x] =
      0 := by
  rw [ContinuousAlternatingMap.map_vecCons_sub, sub_eq_zero]
  exact (hA.apply_rightFundamentalVectorField x _).symm

/-- Two connection forms agree on vertical vectors: their difference vanishes on every fundamental
vector field. -/
theorem sub_apply_rightFundamentalVectorField (hA : IsConnectionForm A)
    (hA' : IsConnectionForm A') (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    (A - A').val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = 0 := by
  rw [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    hA.apply_rightFundamentalVectorField, hA'.apply_rightFundamentalVectorField]
  exact sub_self _

/-- **Affine combinations of connection forms.** A combination `c • A + c' • A'` of connection
forms with `c + c' = 1` is a connection form. -/
theorem smul_add_smul (hA : IsConnectionForm A) (hA' : IsConnectionForm A') {c c' : ℝ}
    (hc : c + c' = 1) : IsConnectionForm (c • A + c' • A') where
  apply_rightFundamentalVectorField x ξ := by
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      hA.apply_rightFundamentalVectorField, hA'.apply_rightFundamentalVectorField]
    -- The value `ξ` is read in the model space, where the weights add up to `1`.
    have key (y : EG) : c • y + c' • y = y := by rw [← add_smul, hc, one_smul]
    exact key ξ
  apply_mfderiv_op_smul g x v := by
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      hA.apply_mfderiv_op_smul, hA'.apply_mfderiv_op_smul]
    -- The adjoint action is read as a linear map of the model space.
    have key (L : EG →L[ℝ] EG) (y y' : EG) : c • L y + c' • L y' = L (c • y + c' • y') := by
      rw [map_add, map_smul, map_smul]
    exact key (Lie.adjointContinuousLinearMap (I := IG) g⁻¹) _ _

end IsConnectionForm

/-! ### Fibre coordinates of trivializations -/

variable [PrincipalBundle G P]

section FiberCoord

variable (G P) in
/-- The base point of a point of the charted total space. -/
private abbrev proj (x : ManifoldTotalSpace G P) : B :=
  ((ManifoldTotalSpace.homeomorph G P).symm x).proj

variable (P) in
/-- The fibre coordinate of a point of the charted total space in the trivialization of the atlas
at `b₀`. -/
private def fiberCoord (b₀ : B) (x : ManifoldTotalSpace G P) : G :=
  (trivializationAt G P b₀ ((ManifoldTotalSpace.homeomorph G P).symm x)).2

omit [TopologicalSpace B] [TopologicalSpace G] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [PrincipalBundle G P] in
/-- The right action preserves base points. -/
private theorem proj_op_smul (g : G) (x : ManifoldTotalSpace G P) :
    proj G P (op g • x) = proj G P x := by
  simp [proj]

/-- Over the base set, the fibre coordinate of `x · g` is the fibre coordinate of `x` times `g`. -/
private theorem fiberCoord_op_smul {b₀ : B} {x : ManifoldTotalSpace G P}
    (hx : proj G P x ∈ (trivializationAt G P b₀).baseSet) (g : G) :
    fiberCoord P b₀ (op g • x) = fiberCoord P b₀ x * g := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  simp only [proj, Homeomorph.symm_apply_apply] at hx
  simp only [fiberCoord, ManifoldTotalSpace.smul_homeomorph, Homeomorph.symm_apply_apply]
  exact (trivializationAt G P b₀).snd_apply_smul hx p g

omit [Group G] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- The points over the base set of a trivialization form an open set. -/
private theorem isOpen_setOf_proj_mem (b₀ : B) :
    IsOpen {x : ManifoldTotalSpace G P | proj G P x ∈ (trivializationAt G P b₀).baseSet} :=
  (trivializationAt G P b₀).open_baseSet.preimage
    ((FiberBundle.continuous_proj G P).comp (ManifoldTotalSpace.homeomorph G P).symm.continuous)

omit [Group G] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] [IsManifold IB ∞ B]
  [LieGroup IG ∞ G] in
/-- Over the base set, the fibre coordinate is smooth. -/
private theorem contMDiffAt_fiberCoord {b₀ : B} {x : ManifoldTotalSpace G P}
    (hx : proj G P x ∈ (trivializationAt G P b₀).baseSet) :
    ContMDiffAt (IB.prod IG) IG ∞ (fiberCoord P b₀) x :=
  (ManifoldTotalSpace.contMDiffOn_trivialization_snd_comp (n := ∞) (trivializationAt G P b₀)
    (s := {y | proj G P y ∈ (trivializationAt G P b₀).baseSet}) contMDiffOn_id
    fun _ hy ↦ hy).contMDiffAt ((isOpen_setOf_proj_mem b₀).mem_nhds hx)

omit [IsManifold IB ∞ B] in
/-- Over the base set, the fibre coordinate carries the fundamental vector field of `ξ` to the
left-invariant vector field of `ξ`. -/
private theorem mfderiv_fiberCoord_rightFundamentalVectorField {b₀ : B}
    {x : ManifoldTotalSpace G P} (hx : proj G P x ∈ (trivializationAt G P b₀).baseSet)
    (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) IG (fiberCoord P b₀) x (rightFundamentalVectorField (IB.prod IG) ξ x) =
      mulInvariantVectorField ξ (fiberCoord P b₀ x) := by
  have hfun : fiberCoord P b₀ ∘ (fun g : G ↦ op g • x) = (fiberCoord P b₀ x * ·) := by
    funext g
    exact fiberCoord_op_smul hx g
  rw [rightFundamentalVectorField_apply, ← mfderiv_comp_apply_of_eq (1 : G)
    ((contMDiffAt_fiberCoord hx).mdifferentiableAt (by simp))
    (mdifferentiableAt_orbit (n := ∞) (by simp) x 1) (by simp), hfun]
  rfl

omit [IsManifold IB ∞ B] in
/-- Over the base set, the fibre coordinate intertwines the right action with right
multiplication, also on tangent vectors. -/
private theorem mfderiv_fiberCoord_mfderiv_op_smul {b₀ : B} {x : ManifoldTotalSpace G P}
    (hx : proj G P x ∈ (trivializationAt G P b₀).baseSet) (g : G)
    (v : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) IG (fiberCoord P b₀) (op g • x)
        (mfderiv (IB.prod IG) (IB.prod IG) (fun y ↦ op g • y) x v) =
      mfderiv IG IG (· * g) (fiberCoord P b₀ x)
        (mfderiv (IB.prod IG) IG (fiberCoord P b₀) x v) := by
  have hx' : proj G P (op g • x) ∈ (trivializationAt G P b₀).baseSet := by
    rwa [proj_op_smul]
  -- Near `x`, translating by `g` and then taking the fibre coordinate is right multiplication by
  -- `g` after the fibre coordinate.
  have heq : fiberCoord P b₀ ∘ (fun y ↦ op g • y) =ᶠ[𝓝 x] (· * g) ∘ fiberCoord P b₀ :=
    Filter.eventually_of_mem ((isOpen_setOf_proj_mem b₀).mem_nhds hx)
      fun y hy ↦ fiberCoord_op_smul hy g
  have hcomp : HasMFDerivAt (IB.prod IG) IG (fiberCoord P b₀ ∘ fun y ↦ op g • y) x
      ((mfderiv IG IG (· * g) (fiberCoord P b₀ x)).comp
        (mfderiv (IB.prod IG) IG (fiberCoord P b₀) x)) :=
    ((mdifferentiableAt_mul_right (I := IG)).hasMFDerivAt.comp x
      ((contMDiffAt_fiberCoord hx).mdifferentiableAt (by simp)).hasMFDerivAt).congr_of_eventuallyEq
      heq
  rw [← mfderiv_comp_apply_of_eq x ((contMDiffAt_fiberCoord hx').mdifferentiableAt (by simp))
      ((contMDiff_const_smul (I := IB.prod IG) (n := 1) (op g) x).mdifferentiableAt one_ne_zero)
      rfl, hcomp.mfderiv]
  rfl

end FiberCoord

/-! ### Existence -/

/-- **Existence of connection forms.** A smooth principal bundle over a Hausdorff σ-compact
finite-dimensional manifold has a connection form. -/
theorem exists_isConnectionForm [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] :
    ∃ A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1, IsConnectionForm A := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun b ↦ (trivializationAt G P b).baseSet) (fun b ↦ (trivializationAt G P b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt G P b⟩
  -- The indices whose weight does not vanish at a point have that point in their base set.
  have hmem {b₀ b : B} (hb : b ∈ ρ.finsupport b₀) : b₀ ∈ (trivializationAt G P b).baseSet :=
    hρ b (subset_tsupport _ ((ρ.mem_finsupport b₀).1 hb))
  have hsmooth := isSmoothForm_sum_finsupport_smul_mpullback (F := EG) hρ
    (fun b ↦ (trivializationAt G P b).open_baseSet) (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG)
    (g := fiberCoord P) (fun _ _ hx ↦ contMDiffAt_fiberCoord hx) (maurerCartanForm IG G)
  refine ⟨⟨_, hsmooth.mem_smoothBundleForms⟩, ⟨fun x ξ ↦ ?_, fun g x v ↦ ?_⟩⟩
  -- The glued form is a subtype element whose value is the defining sum; `change` exposes that sum,
  -- which no lemma about the anonymous constructor rewrites to.
  · change (∑ b ∈ ρ.finsupport (proj G P x), ρ b (proj G P x) •
      mpullback (F := EG) (IB.prod IG) IG (fiberCoord P b) (maurerCartanForm IG G).val x)
        ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ
    rw [ContinuousAlternatingMap.sum_apply]
    have h (b : B) (hb : b ∈ ρ.finsupport (proj G P x)) :
        (ρ b (proj G P x) •
          mpullback (F := EG) (IB.prod IG) IG (fiberCoord P b) (maurerCartanForm IG G).val x)
            ![rightFundamentalVectorField (IB.prod IG) ξ x] = ρ b (proj G P x) • (ξ : EG) := by
      rw [ContinuousAlternatingMap.smul_apply, mpullback_apply_one,
        mfderiv_fiberCoord_rightFundamentalVectorField (hmem hb),
        maurerCartanForm_apply_mulInvariantVectorField]
      rfl
    have hsum (c : EG) : ∑ b ∈ ρ.finsupport (proj G P x), ρ b (proj G P x) • c = c := by
      rw [← Finset.sum_smul, ρ.sum_finsupport _ (mem_univ _), one_smul]
    exact (Finset.sum_congr rfl h).trans (hsum ξ)
  · change (∑ b ∈ ρ.finsupport (proj G P (op g • x)), ρ b (proj G P (op g • x)) •
      mpullback (F := EG) (IB.prod IG) IG (fiberCoord P b) (maurerCartanForm IG G).val (op g • x))
        ![mfderiv (IB.prod IG) (IB.prod IG) (fun y ↦ op g • y) x v] =
      Lie.adjointContinuousLinearMap (I := IG) g⁻¹ ((∑ b ∈ ρ.finsupport (proj G P x),
        ρ b (proj G P x) •
          mpullback (F := EG) (IB.prod IG) IG (fiberCoord P b) (maurerCartanForm IG G).val x)
            ![v])
    rw [proj_op_smul, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.sum_apply]
    -- The adjoint action is read as a linear map of the model space, where the sum lives.
    refine (Finset.sum_congr rfl fun b hb ↦ ?_).trans
      (map_sum (Lie.adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG) _ _).symm
    rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply]
    refine (congrArg (ρ b (proj G P x) • ·) ?_).trans
      ((Lie.adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG).map_smul _ _).symm
    rw [mpullback_apply_one, mpullback_apply_one, mfderiv_fiberCoord_mfderiv_op_smul (hmem hb),
      fiberCoord_op_smul (hmem hb), maurerCartanForm_apply_mfderiv_mul_right]

end TauCeti.PrincipalBundle
