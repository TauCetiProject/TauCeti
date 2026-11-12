/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

import TauCeti.Topology.FiberBundle.Separation

/-!
# The moment map of a cotangent-lifted Lie group action

Let a Lie group `G`, with Lie algebra `𝔤 = GroupLieAlgebra IG G`, act smoothly on the left on a
manifold `M`. Its cotangent lift `g • (x, p) = (g • x, p ∘ (dg_x)⁻¹)`
(`TauCeti.CotangentBundle.instMulAction`) is a smooth action on `T*M`
(`TauCeti.CotangentBundle.instContMDiffSMul`) preserving the Liouville form `λ` and the canonical
symplectic form `ω = -dλ`. This file proves that it is Hamiltonian, with the moment map

`⟨μ(x, p), ξ⟩ = p(ξ_M(x))` (`TauCeti.CotangentBundle.momentMap`),

the pairing of the covector `p` with the fundamental vector field `ξ_M` of `ξ` at its base point.

* The fundamental vector field `ξ_{T*M}` of the lifted action covers `ξ_M`:
  `dπ(ξ_{T*M}) = ξ_M ∘ π` (`TauCeti.CotangentBundle.mfderiv_proj_fundamentalVectorField`). Hence
  the moment map is the contraction of the Liouville form with the generating vector fields,
  `⟨μ, ξ⟩ = λ(ξ_{T*M})` (`TauCeti.CotangentBundle.liouvilleForm_apply_fundamentalVectorField`).
* Since `G` preserves `λ`, its fundamental vector fields annihilate `λ`, `L_{ξ_{T*M}} λ = 0`
  (`TauCeti.CotangentBundle.mlieDerivForm_fundamentalVectorField_liouvilleForm`), and Cartan's
  formula turns this into the moment map identity `d⟨μ, ξ⟩ = ι_{ξ_{T*M}} ω`.
* The moment map is equivariant for the coadjoint action, `μ(g • z) = Ad*_g μ(z)`
  (`TauCeti.CotangentBundle.momentMap_smul`), because `dg⁻¹` carries `ξ_M` to `(Ad_{g⁻¹} ξ)_M`.

Together these say that `μ` is a group-level moment map of the cotangent-lifted action
(`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap`). The step from invariance to
infinitesimal invariance integrates fundamental vector fields, so this theorem assumes a
finite-dimensional Hausdorff base without boundary and a Hausdorff Lie group without boundary;
the formula `⟨μ, ξ⟩ = λ(ξ_{T*M})` and the equivariance need neither.

This is the intrinsic version of the moment map `TauCeti.cotangentMomentMap` of a cotangent-lifted
linear action on a vector space, and the moment map with respect to which cotangent bundles are
reduced.

## Main definitions

* `TauCeti.CotangentBundle.momentMap IG G`: the moment map `⟨μ(x, p), ξ⟩ = p(ξ_M(x))`.

## Main results

* `TauCeti.CotangentBundle.liouvilleForm_apply_fundamentalVectorField`: `⟨μ, ξ⟩ = λ(ξ_{T*M})`.
* `TauCeti.CotangentBundle.momentMap_smul`: coadjoint equivariance.
* `TauCeti.CotangentBundle.momentMap_comp_groupLieAlgebraMap`: for an action through a
  homomorphism, the cotangent moment map is the restriction of the cotangent moment map of the
  larger group.
* `TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap`: `μ` is a coadjoint-equivariant
  moment map for the canonical symplectic form.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.1 (momentum maps of cotangent lifts).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §22.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M]

variable (IG G) in
/-- The **moment map of the cotangent-lifted action**: the covector `p` at `x` is sent to the
linear form `ξ ↦ p(ξ_M(x))` on the Lie algebra of `G`, where `ξ_M` is the fundamental vector field
of `ξ`. -/
def momentMap (z : CotangentBundle I M) : Module.Dual ℝ (GroupLieAlgebra IG G) where
  toFun ξ := z.2 (fundamentalVectorField I ξ z.proj)
  map_add' ξ η := by
    rw [fundamentalVectorField_add, Pi.add_apply, map_add]
  map_smul' c ξ := by
    rw [fundamentalVectorField_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

/-- The moment map pairs the covector with the fundamental vector field at its base point:
`⟨μ(x, p), ξ⟩ = p(ξ_M(x))`. -/
@[simp]
theorem momentMap_apply (z : CotangentBundle I M) (ξ : GroupLieAlgebra IG G) :
    momentMap IG G z ξ = z.2 (fundamentalVectorField I ξ z.proj) :=
  (rfl)

/-- **Restriction along a homomorphism.** If a Lie group `K` acts on `M` through a homomorphism
`φ : K →* G` that is differentiable at the identity, then the cotangent moment map of `K` is the
restriction along `dφ : 𝔨 → 𝔤` of that of `G`: `⟨μ_K(z), ξ⟩ = ⟨μ_G(z), dφ ξ⟩`. -/
theorem momentMap_comp_groupLieAlgebraMap {EK HK : Type*} [NormedAddCommGroup EK]
    [NormedSpace ℝ EK] [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK} {K : Type*}
    [TopologicalSpace K] [ChartedSpace HK K] [Group K] [MulAction K M] [ContMDiffSMul IG I 1 G M]
    (φ : K →* G) (hφ : MDifferentiableAt IK IG φ 1) (hsmul : ∀ (k : K) (x : M), k • x = φ k • x)
    (z : CotangentBundle I M) :
    (momentMap IG G z).comp (φ.groupLieAlgebraMap IK IG).toLinearMap = momentMap IK K z := by
  ext ξ
  rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, momentMap_apply, momentMap_apply,
    φ.fundamentalVectorField_groupLieAlgebraMap hφ hsmul]

section Smooth

variable [LieGroup IG ∞ G] [IsManifold I ∞ M] [ContMDiffSMul IG I ∞ G M]
  [ContMDiffConstSMul I ∞ G M]

/-- The fundamental vector field of the cotangent-lifted action covers the fundamental vector field
of the action on the base: `dπ(ξ_{T*M}(z)) = ξ_M(π z)`. -/
theorem mfderiv_proj_fundamentalVectorField (ξ : GroupLieAlgebra IG G) (z : CotangentBundle I M) :
    mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z
        (fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ z) =
      fundamentalVectorField I ξ z.proj :=
  mfderiv_fundamentalVectorField_of_map_smul
    ((contMDiff_proj (n := 1) _).mdifferentiableAt one_ne_zero)
    ((ContMDiffSMul.contMDiff_smul_const (n := ∞) z).mdifferentiableAt (by simp))
    (fun g ↦ proj_smul g z) ξ

/-- **The moment map is the contraction of the Liouville form with the generating vector fields**:
`⟨μ, ξ⟩ = λ(ξ_{T*M})`. -/
theorem liouvilleForm_apply_fundamentalVectorField (ξ : GroupLieAlgebra IG G)
    (z : CotangentBundle I M) :
    (liouvilleForm I M).1 z ![fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ z] =
      momentMap IG G z ξ := by
  rw [liouvilleForm_apply, Matrix.cons_val_zero, mfderiv_proj_fundamentalVectorField,
    momentMap_apply]

/-- The components of the moment map are smooth. -/
theorem contMDiff_momentMap_apply (ξ : GroupLieAlgebra IG G) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞ fun z : CotangentBundle I M ↦ momentMap IG G z ξ := by
  -- Apply the Liouville form, a smooth section of `T*(T*M)`, to the smooth field `ξ_{T*M}`.
  have h := ContMDiff.clm_bundle_apply (E₂ := Trivial (CotangentBundle I M) ℝ)
    (SmoothForm.degreeOneEquiv (liouvilleForm I M)).contMDiff
    (contMDiff_fundamentalVectorField (I' := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (m := ∞) (n := ∞)
      (by simp) ξ)
  refine fun z ↦ (contMDiffAt_totalSpace_iff.1 (h z)).2.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Trivial.eq_trivialization _ ℝ, Trivial.trivialization_apply,
    SmoothForm.degreeOneEquiv_apply_apply, ← Matrix.vec_single_eq_const,
    liouvilleForm_apply_fundamentalVectorField]

/-- **Coadjoint equivariance of the cotangent moment map**: `μ(g • z) = Ad*_g μ(z)`. -/
theorem momentMap_smul (g : G) (z : CotangentBundle I M) :
    momentMap IG G (g • z) = Lie.coadjointRepresentation ℝ IG G g (momentMap IG G z) := by
  ext ξ
  rw [momentMap_apply, Lie.coadjointRepresentation_apply, momentMap_apply]
  -- `dg⁻¹` carries `ξ_M` at `g • x` to `(Ad_{g⁻¹} ξ)_M` at `x`.
  have h := mfderiv_smul_fundamentalVectorField (I := IG) (I' := I) g⁻¹ ξ (g • z.proj)
  set η := Lie.adjointContinuousLinearMap (I := IG) g⁻¹ ξ
  exact (congrArg (fun x : M ↦ (g • z).2 (fundamentalVectorField I ξ x)) (proj_smul g z)).trans
    ((smul_snd_apply g z (fundamentalVectorField I ξ (g • z.proj))).trans ((congrArg z.2 h).trans
      (congrArg (fun x : M ↦ z.2 (fundamentalVectorField I η x)) (inv_smul_smul g z.proj))))

end Smooth

section Equivariant

variable [CompleteSpace EG] [LieGroup IG ∞ G] [T2Space G] [BoundarylessManifold IG G]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffSMul IG I ∞ G M] [ContMDiffConstSMul I ∞ G M]

/-- The fundamental vector fields and the exponential flow only need a `C³` Lie group. -/
local instance lieGroupMinSmoothness : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := IG) (G := G) (m := minSmoothness ℝ 3) (n := ∞) (by simp)

/-- **The Liouville form is infinitesimally invariant** under the cotangent-lifted action: its Lie
derivative along every fundamental vector field vanishes, `L_{ξ_{T*M}} λ = 0`. -/
theorem mlieDerivForm_fundamentalVectorField_liouvilleForm (ξ : GroupLieAlgebra IG G) :
    mlieDerivForm (fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ) (liouvilleForm I M).1 =
      0 :=
  mlieDerivForm_fundamentalVectorField_eq_zero mpullback_smul_liouvilleForm ξ

/-- **The cotangent-lifted action is Hamiltonian.** The map `⟨μ(x, p), ξ⟩ = p(ξ_M(x))` is a
coadjoint-equivariant moment map of the cotangent lift of a smooth action of a Lie group, for the
canonical symplectic form `ω = -dλ` of the cotangent bundle: `d⟨μ, ξ⟩ = ι_{ξ_{T*M}} ω`. -/
theorem isEquivariantMomentMap_momentMap :
    (symplecticForm I M).IsEquivariantMomentMap (momentMap IG G) where
  contMDiff := contMDiff_momentMap_apply
  isHamiltonianVectorField ξ := by
    set X := fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (M := CotangentBundle I M) ξ
    have hX : MDifferentiable (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent
        fun z ↦ (⟨z, X z⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M)) :=
      (contMDiff_fundamentalVectorField (m := 1) (n := ∞) (by simp) ξ).mdifferentiable one_ne_zero
    -- Cartan's formula: `0 = L_X λ = ι_X dλ + d(λ(X))`, and `ι_X dλ = -ι_X ω`.
    have hcartan := SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add hX
      (φ := liouvilleForm I M)
    rw [mlieDerivForm_fundamentalVectorField_liouvilleForm, eq_comm, add_eq_zero_iff_eq_neg']
      at hcartan
    have hlam : RoughForm.interior X (liouvilleForm I M).1 =
        RoughForm.ofFunction _ fun z ↦ momentMap IG G z ξ := by
      funext z
      ext v
      rw [RoughForm.interior_apply, Subsingleton.elim v ![], RoughForm.ofFunction_apply]
      exact liouvilleForm_apply_fundamentalVectorField ξ z
    rw [SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq,
      InfinitesimalAction.fundamental_apply, ← hlam, hcartan, symplecticForm_eq_neg_mextDeriv]
    funext z
    ext v
    simp [RoughForm.interior_apply, X]
  apply_smul := momentMap_smul

end Equivariant

end TauCeti.CotangentBundle
