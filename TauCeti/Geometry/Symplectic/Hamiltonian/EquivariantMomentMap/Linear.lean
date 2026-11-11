/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Linear
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# The moment map of a linear symplectic representation

Let a Lie group `G` act smoothly and linearly on a finite-dimensional real symplectic vector space
`(V, ω)` by linear symplectomorphisms, `ω (g • u) (g • w) = ω u w`. Each element `ξ` of the Lie
algebra `𝔤` of `G` then acts on `V` by the linear vector field `ξ_V`
(`TauCeti.fundamentalLinearMap`), which lies in the symplectic Lie algebra `sp(V, ω)`
(`TauCeti.SymplecticForm.fundamentalLinearMap_mem_skewAdjointLieSubalgebra`). The **quadratic
moment map** of the representation is

`μ(v)(ξ) = ½ ω(ξ_V v, v)`

(`TauCeti.SymplecticForm.linearActionMomentMap`). Its component `μ_ξ` is the component
`μ_{ξ_V}` of the moment map `TauCeti.SymplecticForm.linearMomentMap` of `sp(V, ω)` itself
(`TauCeti.SymplecticForm.linearActionMomentMap_apply_eq_linearMomentMap`), so
`d μ_ξ = ι_{ξ_V} ω`. Every element of `G` acts by a symplectomorphism of the constant form `ω`,
and `μ` vanishes at the fixed point `0`, so `μ` is a coadjoint-equivariant group-level moment map
(`TauCeti.SymplecticForm.isEquivariantMomentMap_linearActionMomentMap`):

`μ (g • v) = Ad*_g (μ v)`.

This is the model moment map on the symplectic slice of a Hamiltonian action: at a point `p`, the
stabilizer `G_p` acts linearly and symplectically on the symplectic normal space, and the local
normal form of the action near the orbit of `p` is built from this quadratic moment map.

## Main definitions

* `TauCeti.SymplecticForm.linearActionMomentMap I G ω`: the quadratic moment map
  `μ(v)(ξ) = ½ ω(ξ_V v, v)` of a linear action of `G` on `(V, ω)`.

## Main results

* `TauCeti.SymplecticForm.fundamentalLinearMap_mem_skewAdjointLieSubalgebra`: for an action by
  linear symplectomorphisms, each `ξ_V` lies in `sp(V, ω)`.
* `TauCeti.SymplecticForm.mpullback_smul_constSmooth`: each element of `G` preserves the constant
  two-form `ω`.
* `TauCeti.SymplecticForm.isMomentMap_linearActionMomentMap`: `μ` is a moment map of the action of
  `𝔤` by fundamental vector fields.
* `TauCeti.SymplecticForm.isEquivariantMomentMap_linearActionMomentMap`: `μ` is a
  coadjoint-equivariant group-level moment map.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the moment map of a linear symplectic action).
* E. Lerman, R. Sjamaar, *Stratified symplectic spaces and reduction*, Annals of Mathematics 134
  (1991), 375–422, Section 2 (the quadratic moment map on the symplectic slice).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace SymplecticForm

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DistribMulAction G V] [SMulCommClass G ℝ V]
  (ω : SymplecticForm V)

section Linear

variable [ContMDiffSMul I 𝓘(ℝ, V) 1 G V]

variable (I G) in
/-- The **quadratic moment map** of a linear action of a Lie group `G` on a symplectic vector space
`(V, ω)`: `μ(v)(ξ) = ½ ω(ξ_V v, v)`, where `ξ_V` is the linear fundamental vector field of `ξ`. -/
def linearActionMomentMap (v : V) : Module.Dual ℝ (GroupLieAlgebra I G) where
  toFun ξ := ω (fundamentalLinearMap I G V ξ v) v / 2
  map_add' ξ η := by simp [add_div]
  map_smul' c ξ := by simp [mul_div_assoc]

@[simp]
theorem linearActionMomentMap_apply (v : V) (ξ : GroupLieAlgebra I G) :
    linearActionMomentMap I G ω v ξ = ω (fundamentalLinearMap I G V ξ v) v / 2 :=
  (rfl)

/-- The quadratic moment map vanishes at the origin. -/
@[simp]
theorem linearActionMomentMap_zero : linearActionMomentMap I G ω 0 = 0 := by
  ext ξ
  simp

variable [FiniteDimensional ℝ V]

/-- **Linear symplectic actions act infinitesimally through `sp(V, ω)`.** If every element of `G`
acts by a linear symplectomorphism of `(V, ω)`, then the fundamental vector field `ξ_V` of every
`ξ` is skew-adjoint for `ω`. -/
theorem fundamentalLinearMap_mem_skewAdjointLieSubalgebra
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (ξ : GroupLieAlgebra I G) :
    fundamentalLinearMap I G V ξ ∈ skewAdjointLieSubalgebra ω.toBilinForm := by
  refine (LinearMap.mem_skewAdjointSubmodule _).2 fun u w ↦ ?_
  have h := ω.toBilinForm.toContinuousBilinearMap.apply_fundamentalLinearMap_left
    (fun g u w ↦ by simpa using hω g u w) ξ u w
  simp only [LinearMap.toContinuousBilinearMap_apply] at h
  rw [h, Pi.neg_apply, map_neg]

/-- The component `μ_ξ` of the quadratic moment map of a linear symplectic action is the component
`μ_{ξ_V}` of the moment map of the linear action of `sp(V, ω)`. -/
theorem linearActionMomentMap_apply_eq_linearMomentMap
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (v : V) (ξ : GroupLieAlgebra I G) :
    linearActionMomentMap I G ω v ξ =
      ω.linearMomentMap v ⟨fundamentalLinearMap I G V ξ,
        ω.fundamentalLinearMap_mem_skewAdjointLieSubalgebra hω ξ⟩ := by
  rw [linearActionMomentMap_apply, linearMomentMap_apply]

end Linear

section Smooth

variable [FiniteDimensional ℝ V] [ContMDiffSMul I 𝓘(ℝ, V) (⊤ : ℕ∞) G V]

variable (I) in
/-- **Linear symplectic actions preserve the constant symplectic form.** If `g` acts by a linear
symplectomorphism of `(V, ω)`, then it pulls the constant two-form `ω` on `V` back to itself. -/
theorem mpullback_smul_constSmooth {g : G} (hg : ∀ u w : V, ω (g • u) (g • w) = ω u w) :
    SmoothForm.mpullback (fun v : V ↦ g • v) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      ω.constSmooth = ω.constSmooth := by
  let L : V →L[ℝ] V := LinearMap.toContinuousLinearMap (DistribSMul.toLinearMap ℝ V g)
  -- `mvfderiv` sees the action of `g` in its eta-reduced form `HSMul.hSMul g`.
  have hL : (HSMul.hSMul g : V → V) = L := by
    ext v
    simp [L]
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, eval₂_constSmooth_mfderiv_eq, fromTangentSpace_constSmooth_apply,
    hL, mvfderiv_eq_fderiv, L.fderiv]
  exact hg v w

variable [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G]

/-- The fundamental vector fields only need a `C¹` action. -/
local instance contMDiffSMulOne : ContMDiffSMul I 𝓘(ℝ, V) 1 G V :=
  ContMDiffSMul.of_le (M := V) ENat.LEInfty.out

/-- **The quadratic moment map is a moment map.** For a linear action of `G` on `(V, ω)` by linear
symplectomorphisms, `μ(v)(ξ) = ½ ω(ξ_V v, v)` is a moment map of the action of the Lie algebra by
fundamental vector fields: `d μ_ξ = ι_{ξ_V} ω`. -/
theorem isMomentMap_linearActionMomentMap
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) :
    ω.constSmooth.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V)
      (linearActionMomentMap I G ω) := by
  have hlin := ω.isMomentMap_linearMomentMap
  refine ⟨fun ξ ↦ ?_, fun ξ ↦ ?_⟩
  · simpa only [linearActionMomentMap_apply_eq_linearMomentMap ω hω] using
      hlin.contMDiff ⟨_, ω.fundamentalLinearMap_mem_skewAdjointLieSubalgebra hω ξ⟩
  · -- The fundamental vector field of `ξ` is the linear vector field of `ξ_V ∈ sp(V, ω)`.
    have hX : (InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V ξ :
          (v : V) → TangentSpace 𝓘(ℝ, V) v) =
        ((InfinitesimalAction.linear V).comp (skewAdjointLieSubalgebra ω.toBilinForm).incl
          ⟨_, ω.fundamentalLinearMap_mem_skewAdjointLieSubalgebra hω ξ⟩ :
            (v : V) → TangentSpace 𝓘(ℝ, V) v) := by
      funext v
      rw [InfinitesimalAction.fundamental_apply, InfinitesimalAction.comp_apply,
        LieSubalgebra.coe_incl, InfinitesimalAction.linear_apply,
        fundamentalLinearMap_apply_eq_fundamentalVectorField, NormedSpace.fromTangentSpace_apply]
    simp only [linearActionMomentMap_apply_eq_linearMomentMap ω hω]
    rw [hX]
    exact hlin.isHamiltonianVectorField _

/-- **The quadratic moment map is equivariant.** For a linear action of a Lie group `G` on
`(V, ω)` by linear symplectomorphisms, `μ(v)(ξ) = ½ ω(ξ_V v, v)` is a coadjoint-equivariant
group-level moment map: `μ (g • v) = Ad*_g (μ v)`. -/
theorem isEquivariantMomentMap_linearActionMomentMap
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) :
    ω.constSmooth.IsEquivariantMomentMap (linearActionMomentMap I G ω) := by
  -- An action by symplectomorphisms of the connected space `V` is equivariant once it is so at
  -- one point; at the fixed point `0` both sides vanish.
  refine ((ω.isMomentMap_linearActionMomentMap hω).isEquivariantMomentMap_iff
    (fun g ↦ ω.mpullback_smul_constSmooth I (hω g)) 0).2 fun g ↦ ?_
  rw [smul_zero, linearActionMomentMap_zero, map_zero]

end Smooth

end SymplecticForm

end TauCeti
