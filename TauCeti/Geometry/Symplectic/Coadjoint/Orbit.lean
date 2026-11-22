/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Manifold.Descent

import TauCeti.Geometry.Symplectic.Coadjoint
import TauCeti.Geometry.Lie.RightInvariantVectorField

/-!
# The Kirillov–Kostant–Souriau form on a homogeneous coadjoint orbit

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, and fix `ν ∈ 𝔤*`. The coset space `G ⧸ G_ν` of its coadjoint
stabilizer `G_ν = {g | Ad*_g ν = ν}` is a smooth manifold on which `G` acts smoothly by left
multiplication (`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Orbit`). This file makes
`G ⧸ G_ν` a symplectic manifold: the coadjoint orbit of `ν` with its intrinsic homogeneous smooth
structure, whose points are cosets rather than covectors.

**The KKS form.** The left-invariant Kirillov form `σ_ν` on `G`
(`Module.Dual.leftInvariantKirillovForm`), with `σ_ν(ξ^L, η^L) = ν ⁅ξ, η⁆` for left-invariant
vector fields, is closed and invariant under right translation by `G_ν`, and its kernel at `g` is
the left translate `d(L_g)(𝔤_ν)` of the infinitesimal stabilizer `𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`.
That translate is exactly the kernel of the differential of the projection `π : G → G ⧸ G_ν`
(`Module.Dual.ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation`): the curves
`t ↦ g exp (t ξ)` with `ξ ∈ 𝔤_ν` stay in the coset `g G_ν`, and both spaces have the dimension of
`𝔤_ν`, the Lie algebra of `G_ν`. Hence `σ_ν` is basic for `π` and descends to a unique two-form
`ω_ν` on `G ⧸ G_ν` with `π^* ω_ν = σ_ν` (`Module.Dual.coadjointOrbitForm`), which is symplectic
(`Module.Dual.isSymplectic_coadjointOrbitForm`) and invariant under the action of `G`.

**The orbit map.** The injective equivariant map `[g] ↦ Ad*_g ν` (`Representation.orbitMap` of
the coadjoint representation) is a coadjoint-equivariant moment map of `ω_ν` for the action of `G`
(`Module.Dual.isEquivariantMomentMap_coadjointOrbitForm`), in the conventions
`d⟨μ, ξ⟩ = ι_(ξ_O) ω_ν` and `μ (g • x) = Ad*_g (μ x)`. Consequently `ω_ν` takes the defining
KKS values on generators,

`ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆` at the point `μ` of the orbit,

(`Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`), in particular `ν ⁅ξ, η⁆` at the
coset of the identity (`Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField_one`), and the
differential of the orbit map in the direction `ξ_O` is the infinitesimal coadjoint action. The
differential of the orbit map is injective at every point
(`Module.Dual.injective_differential_orbitMap_coadjointRepresentation`), so the orbit map is an
injective immersion into `𝔤*`. The orbit has dimension `dim 𝔤 - dim 𝔤_ν`, which is even.

## Main definitions

* `Module.Dual.coadjointOrbitForm ν`: the Kirillov–Kostant–Souriau form on `G ⧸ G_ν`.

## Main results

* `Module.Dual.isBasic_leftInvariantKirillovForm`: `σ_ν` is basic for `G → G ⧸ G_ν`.
* `Module.Dual.mpullback_quotientMk_coadjointOrbitForm`, `Module.Dual.eq_coadjointOrbitForm_iff`:
  `ω_ν` is the unique two-form pulling back to `σ_ν`.
* `Module.Dual.isSymplectic_coadjointOrbitForm`: `ω_ν` is symplectic.
* `Module.Dual.mpullback_smul_coadjointOrbitForm`: `G` acts by symplectomorphisms.
* `Module.Dual.eval₂_coadjointOrbitForm_mfderiv_smul`: the same, on tangent vectors.
* `Module.Dual.isEquivariantMomentMap_coadjointOrbitForm`: the orbit map is an equivariant moment
  map.
* `Module.Dual.eval₂_coadjointOrbitForm_mfderiv_mulInvariantVectorField`:
  `ω_ν(dπ ξ^L, dπ η^L) = ν ⁅ξ, η⁆`.
* `Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`: `ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆`.
* `Module.Dual.injective_differential_orbitMap_coadjointRepresentation`: the orbit map is an
  immersion.
* `Module.Dual.even_finrank_quotientModelSpace`: the orbit has even dimension.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22 (coadjoint orbits and their moment maps).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 14 (the KKS form and its pullback to the group).
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {ν : Module.Dual ℝ (GroupLieAlgebra I G)}

variable (ν)

/-- **A coadjoint orbit has even dimension.** Its dimension `dim 𝔤 - dim 𝔤_ν` is that of the
algebraic tangent model `𝔤 ⧸ 𝔤_ν`, which carries the nondegenerate alternating form
`[ξ], [η] ↦ ν ⁅ξ, η⁆`. -/
theorem even_finrank_quotientModelSpace :
    Even (finrank ℝ
      (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))) := by
  rw [finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator]
  exact even_finrank_quotient_lieAnnihilator ν

variable {ν}

/-- The kernel of the left-invariant Kirillov form of `ν` at `g` is the kernel of the differential
of the projection onto the coadjoint orbit `G ⧸ G_ν`. -/
theorem ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv (g : G) :
    LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) =
      (mfderiv I
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).ker := by
  rw [ker_bilinFormAt_leftInvariantKirillovForm,
    ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation]

variable (ν)

/-- **The left-invariant Kirillov form is basic** for the projection `G → G ⧸ G_ν`. -/
theorem isBasic_leftInvariantKirillovForm :
    RoughForm.IsBasic (V := ℝ)
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
      ν.leftInvariantKirillovForm.val :=
  -- Right translation by `G_ν` acts transitively on the fibres and preserves `σ_ν`, and vertical
  -- vectors lie in the kernel of `σ_ν`.
  SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le
    (τ := fun h : (coadjointRepresentation ℝ I G).stabilizer ν ↦ (· * (h : G)))
    (ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.mdifferentiable
      (by simp))
    (fun h ↦ (contMDiff_mul_right (I := I) (n := ∞)).mdifferentiable (by simp))
    (fun h ↦ funext fun g ↦ QuotientGroup.mk_mul_of_mem g h.property)
    (fun x y hxy ↦ .inr ⟨⟨x⁻¹ * y, QuotientGroup.eq.1 hxy⟩, mul_inv_cancel_left x y⟩)
    (fun x ↦ (ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv x).ge) fun h ↦ by
      simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val
        (ν.mpullback_mul_right_leftInvariantKirillovForm_of_mem_stabilizer h.property)

/-! ### The Kirillov–Kostant–Souriau form -/

/-- **The Kirillov–Kostant–Souriau form** `ω_ν` on the coadjoint orbit `G ⧸ G_ν`: the descent of
the left-invariant Kirillov form `σ_ν` along the projection `G → G ⧸ G_ν`, the unique two-form with
`π^* ω_ν = σ_ν` (`Module.Dual.eq_coadjointOrbitForm_iff`). On generators it is
`ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆` at the point `μ` of the orbit
(`Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`). -/
def coadjointOrbitForm :
    SmoothTwoForm 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  SmoothForm.descendedForm ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    QuotientGroup.mk_surjective
    ν.leftInvariantKirillovForm ν.isBasic_leftInvariantKirillovForm

/-- The KKS form pulls back to the left-invariant Kirillov form along the projection
`G → G ⧸ G_ν`. -/
@[simp]
theorem mpullback_quotientMk_coadjointOrbitForm
    (hπ : ContMDiff I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) :
    SmoothForm.mpullback QuotientGroup.mk hπ ν.coadjointOrbitForm = ν.leftInvariantKirillovForm :=
  SmoothForm.mpullback_descendedForm

/-- **Uniqueness of the KKS form**: it is the only two-form on `G ⧸ G_ν` pulling back to the
left-invariant Kirillov form along the projection. -/
theorem eq_coadjointOrbitForm_iff
    {η : SmoothTwoForm
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)}
    (hπ : ContMDiff I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) :
    η = ν.coadjointOrbitForm ↔ SmoothForm.mpullback QuotientGroup.mk hπ η =
      ν.leftInvariantKirillovForm :=
  SmoothForm.eq_descendedForm_iff

/-- The KKS form evaluates on images under the differential of the projection `G → G ⧸ G_ν` as
the left-invariant Kirillov form: `ω_ν(dπ v, dπ w) = σ_ν(v, w)`. -/
theorem eval₂_coadjointOrbitForm_mfderiv (g : G) (v w : TangentSpace I g) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm
        (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (mfderiv I
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          QuotientGroup.mk g v)
        (mfderiv I
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          QuotientGroup.mk g w) =
      SmoothBundleForm.eval₂ ν.leftInvariantKirillovForm g v w :=
  SmoothTwoForm.eval₂_descendedForm_mfderiv g v w

/-- On the images of left-invariant vector fields under the projection `G → G ⧸ G_ν`, the KKS form
is the Kirillov form: `ω_ν(dπ ξ^L(g), dπ η^L(g)) = ν ⁅ξ, η⁆` at every `g`. -/
theorem eval₂_coadjointOrbitForm_mfderiv_mulInvariantVectorField (ξ η : GroupLieAlgebra I G)
    (g : G) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm
        (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g (mulInvariantVectorField ξ g))
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g (mulInvariantVectorField η g)) =
      ν ⁅ξ, η⁆ := by
  rw [eval₂_coadjointOrbitForm_mfderiv, eval₂_leftInvariantKirillovForm_mulInvariantVectorField]

/-- **The KKS form is symplectic.** -/
theorem isSymplectic_coadjointOrbitForm : ν.coadjointOrbitForm.IsSymplectic :=
  -- `σ_ν` is closed, and its kernel is exactly the kernel of the differential of the projection.
  SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨ν.isClosed_leftInvariantKirillovForm, ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv⟩

/-- **`G` acts on its coadjoint orbit by symplectomorphisms**: left translation by `g` preserves the
KKS form. -/
@[simp]
theorem mpullback_smul_coadjointOrbitForm (g : G)
    (hg : ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      fun x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν ↦ g • x) :
    SmoothForm.mpullback (g • ·) hg ν.coadjointOrbitForm = ν.coadjointOrbitForm := by
  have hπ := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  rw [eq_coadjointOrbitForm_iff ν hπ, SmoothForm.mpullback_mpullback_of_comp_eq hπ hg
    contMDiff_mul_left hπ (funext fun h ↦ MulAction.Quotient.smul_coe _ g h),
    mpullback_quotientMk_coadjointOrbitForm, mpullback_mul_left_leftInvariantKirillovForm]

/-- **`G` acts on its coadjoint orbit by symplectomorphisms**, read on tangent vectors: the KKS
form pairs `d(g •) u` and `d(g •) v` at `g • x` as it pairs `u` and `v` at `x`. -/
theorem eval₂_coadjointOrbitForm_mfderiv_smul (g : G)
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
    (u v : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x) :
    ν.coadjointOrbitForm.eval₂ (g • x) (mfderiv _ _ (g • ·) x u) (mfderiv _ _ (g • ·) x v) =
      ν.coadjointOrbitForm.eval₂ x u v := by
  have h := congrArg (fun τ ↦ SmoothBundleForm.eval₂ τ x u v)
    (ν.mpullback_smul_coadjointOrbitForm g (ContMDiffSMul.contMDiff_const_smul (I := I) g))
  simpa only [SmoothForm.eval₂_mpullback] using h

/-! ### The orbit map as a moment map -/

/-- **The orbit map is a moment map.** For the action of `G` on its coadjoint orbit by left
multiplication, the orbit map `[g] ↦ Ad*_g ν` is a coadjoint-equivariant moment map of the KKS
form: `d⟨μ, ξ⟩ = ι_(ξ_O) ω_ν`. This is the moment map `g ↦ Ad*_g ν` of `σ_ν` on `G`
(`Module.Dual.isEquivariantMomentMap_leftInvariantKirillovForm`), descended along the projection. -/
theorem isEquivariantMomentMap_coadjointOrbitForm :
    ν.coadjointOrbitForm.IsEquivariantMomentMap
      ((coadjointRepresentation ℝ I G).orbitMap ν) where
  contMDiff := ν.contMDiff_orbitMap_coadjointRepresentation_apply
  isHamiltonianVectorField ξ := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    have : T2Space G := I.t2Space_of_lieGroup ∞
    have hπ := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, rfl⟩ := hπ.surjective_mfderiv (by simp) g v
    have hcomp : (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y ξ) ∘ QuotientGroup.mk =
        fun h : G ↦ coadjointRepresentation ℝ I G h ν ξ :=
      funext fun h ↦ by rw [comp_apply, Representation.orbitMap_mk]
    -- The generator `ξ_O([g])` is the image of the generator `ξ_G(g)` of left multiplication.
    rw [InfinitesimalAction.fundamental_apply,
      ← Subgroup.mfderiv_quotientMk_fundamentalVectorField
        (isClosed_stabilizer_coadjointRepresentation I ν) g ξ,
      eval₂_coadjointOrbitForm_mfderiv, ← mvfderiv_comp_apply g
        ((ν.contMDiff_orbitMap_coadjointRepresentation_apply ξ).mdifferentiableAt (by simp))
        (hπ.contMDiff.mdifferentiableAt (by simp)), hcomp,
      ← InfinitesimalAction.fundamental_apply]
    exact ν.isEquivariantMomentMap_leftInvariantKirillovForm.eval₂_apply ξ g u
  apply_smul := (coadjointRepresentation ℝ I G).orbitMap_smul ν

/-- **The KKS form on generators.** At a point `x` of the coadjoint orbit with image
`μ = Ad*_g ν` in `𝔤*`, the KKS form pairs the generators of `ξ` and `η` to `μ ⁅ξ, η⁆`; at the coset
of the identity this is the Kirillov form `ν ⁅ξ, η⁆`. -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ η : GroupLieAlgebra I G) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x)
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) η x) =
      (coadjointRepresentation ℝ I G).orbitMap ν x ⁅ξ, η⁆ := by
  simpa only [InfinitesimalAction.fundamental_apply] using SmoothTwoForm.momentCocycle_eq_zero_iff.1
    (ν.isEquivariantMomentMap_coadjointOrbitForm.momentCocycle_eq_zero x) ξ η

/-- **The KKS form at the base point.** At the coset of the identity, the KKS form pairs the
generators of `ξ` and `η` to `ν ⁅ξ, η⁆`. -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField_one (ξ η : GroupLieAlgebra I G) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm
        ((1 : G) : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (fundamentalVectorField _ ξ _) (fundamentalVectorField _ η _) =
      ν ⁅ξ, η⁆ := by
  rw [eval₂_coadjointOrbitForm_fundamentalVectorField, Representation.orbitMap_mk, map_one,
    one_apply_eq_self]

/-- **The derivative of the orbit map along generators**: in the direction `ξ_O`, the component
`⟨μ, η⟩` of the orbit map changes at the rate `μ ⁅η, ξ⁆`. -/
theorem mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ η : GroupLieAlgebra I G) :
    mvfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y η) x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x) =
      (coadjointRepresentation ℝ I G).orbitMap ν x ⁅η, ξ⁆ := by
  rw [← ν.isEquivariantMomentMap_coadjointOrbitForm.eval₂_apply,
    InfinitesimalAction.fundamental_apply, eval₂_coadjointOrbitForm_fundamentalVectorField]

/-- **The orbit map is an immersion.** At every point of the coadjoint orbit, the differential
`v ↦ (ξ ↦ d⟨μ, ξ⟩(v))` of the orbit map is injective. -/
theorem injective_differential_orbitMap_coadjointRepresentation
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    Function.Injective (ν.isEquivariantMomentMap_coadjointOrbitForm.differential x) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hπ := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  intro v hv
  obtain ⟨u, rfl⟩ := hπ.surjective_mfderiv (by simp) g v
  -- Pulled back to `G`, `d⟨μ, ξ⟩(dπ u) = σ_ν(ξ_G, u)` vanishes for every `ξ`, and the generators
  -- `ξ_G(g)` exhaust `T_g G`, so `u` lies in the kernel of `σ_ν`, which is the kernel of `dπ`.
  have hu : u ∈ LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) := by
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w ↦ ?_)
    -- Write `w` as the generator `ξ_G(g)`, the right-invariant field of `ξ`.
    obtain ⟨ξ, rfl⟩ := (bijective_mulRightInvariantVectorField (I := I) g).2 w
    have hξ := congr($hv ξ)
    rw [SmoothTwoForm.IsMomentMap.differential_apply_eq_eval₂,
      InfinitesimalAction.fundamental_apply,
      ← Subgroup.mfderiv_quotientMk_fundamentalVectorField
        (isClosed_stabilizer_coadjointRepresentation I ν) g ξ,
      eval₂_coadjointOrbitForm_mfderiv, fundamentalVectorField_eq_mulRightInvariantVectorField,
      SmoothBundleForm.eval₂_swap, LinearMap.zero_apply, neg_eq_zero] at hξ
    rw [SmoothForm.bilinFormAt_apply, hξ, LinearMap.zero_apply]
  rw [ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv] at hu
  exact hu

end Module.Dual
