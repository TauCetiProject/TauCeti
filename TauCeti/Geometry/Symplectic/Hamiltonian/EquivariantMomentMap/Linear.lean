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

Let a Lie group `G` act smoothly and linearly on a finite-dimensional symplectic vector space
`(V, ω)`, preserving `ω`: `ω (g • x) (g • y) = ω x y`. Each `ξ` in the Lie algebra then acts by
the skew-adjoint endomorphism `dρ(ξ) : x ↦ ξ_V(x)` of `(V, ω)`
(`TauCeti.fundamentalLieHom_mem_skewAdjointLieSubalgebra`), and

`μ(x)(ξ) = ½ ω(ξ_V(x), x)`

(`TauCeti.SymplecticForm.representationMomentMap`) is a **group-level moment map**: it satisfies
`d⟨μ, ξ⟩ = ι_{ξ_V} ω` and is coadjoint-equivariant, `μ (g • x) = Ad*_g (μ x)`
(`TauCeti.SymplecticForm.isEquivariantMomentMap_representationMomentMap`). No connectedness of
`G` is needed.

The moment map identity is the restriction, along the Lie algebra homomorphism
`dρ : 𝔤 → 𝔰𝔭(V, ω)`, of the moment map `A ↦ ½ ω(A x, x)` of the infinitesimal action of
`𝔰𝔭(V, ω)` by linear vector fields (`TauCeti.SymplecticForm.isMomentMap_linearMomentMap`).
Equivariance then holds because every `g` acts by a linear symplectomorphism
(`TauCeti.SymplecticForm.mpullback_smul_constSmooth`) and the moment map vanishes at the fixed
point `0`, so its equivariance defect, which is independent of the point, vanishes.

## Main definitions

* `TauCeti.SymplecticForm.representationMomentMap ω I G`: the map `x ↦ (ξ ↦ ½ ω(ξ_V(x), x))`.

## Main results

* `TauCeti.SymplecticForm.mpullback_smul_constSmooth`: a linear action preserving `ω` acts by
  symplectomorphisms of the constant form.
* `TauCeti.SymplecticForm.isMomentMap_representationMomentMap`: `μ` is a moment map of the
  fundamental vector fields.
* `TauCeti.SymplecticForm.isEquivariantMomentMap_representationMomentMap`: `μ` is a group-level,
  coadjoint-equivariant moment map.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.4, linear symplectic actions and their quadratic momentum maps.
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.SymplecticForm

attribute [local instance 100] LieRing.ofAssociativeRing

-- The smoothness exponent `(⊤ : ℕ∞)` is written out, as the scope providing its notation `∞`
-- also takes the name `ω` used here for the symplectic form.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [DistribMulAction G V] [SMulCommClass G ℝ V] [ContMDiffSMul I 𝓘(ℝ, V) (⊤ : ℕ∞) G V]

variable (ω : SymplecticForm V)

variable (I G) in
/-- The **moment map of a linear representation** on a symplectic vector space `(V, ω)`:
`μ(x)(ξ) = ½ ω(ξ_V(x), x)`, where `ξ_V(x) = dρ(ξ) x` is the fundamental vector field. When the
action preserves `ω` this is a coadjoint-equivariant moment map
(`TauCeti.SymplecticForm.isEquivariantMomentMap_representationMomentMap`). -/
def representationMomentMap (x : V) : Module.Dual ℝ (GroupLieAlgebra I G) where
  toFun ξ := ω (fundamentalLieHom I G V ξ x) x / 2
  map_add' ξ η := by
    simp only [map_add, LinearMap.add_apply, add_div]
  map_smul' c ξ := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]

/-- The value of the moment map of a linear representation: `μ(x)(ξ) = ½ ω(dρ(ξ) x, x)`. -/
@[simp]
theorem representationMomentMap_apply (x : V) (ξ : GroupLieAlgebra I G) :
    ω.representationMomentMap I G x ξ = ω (fundamentalLieHom I G V ξ x) x / 2 :=
  (rfl)

/-- The moment map of a linear representation vanishes at the origin. -/
@[simp]
theorem representationMomentMap_zero : ω.representationMomentMap I G (0 : V) = 0 := by
  ext ξ
  simp

/-- For a representation preserving `ω`, the moment map is the restriction of the moment map
`A ↦ ½ ω(A x, x)` of `𝔰𝔭(V, ω)` along the derivative `dρ : 𝔤 → 𝔰𝔭(V, ω)`. -/
theorem representationMomentMap_eq_comp
    (hω : ∀ (g : G) (x y : V), ω (g • x) (g • y) = ω x y) (x : V) :
    ω.representationMomentMap I G x =
      (ω.linearMomentMap x).comp (fundamentalSkewAdjointLieHom I G V hω : _ →ₗ[ℝ] _) := by
  ext ξ
  simp

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] in
/-- **A linear action preserving `ω` acts by symplectomorphisms**: each `x ↦ g • x` pulls the
constant form `ω` back to itself. -/
theorem mpullback_smul_constSmooth (hω : ∀ (g : G) (x y : V), ω (g • x) (g • y) = ω x y)
    (g : G) :
    SmoothForm.mpullback (fun x : V ↦ g • x)
        (ContMDiffSMul.contMDiff_const_smul (I := I) g) ω.constSmooth =
      ω.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback]
  refine (constSmooth_apply _ _ _ _).trans (Eq.trans ?_ (constSmooth_apply _ _ _ _).symm)
  -- The differentials are read in the fibres of the form bundle, which are `V` by definition.
  exact (congrArg₂ (fun a b : V ↦ ω a b) (mfderiv_smul_apply g p v)
    (mfderiv_smul_apply g p w)).trans (hω g v w)

/-- **The moment map identity for a linear symplectic representation**:
`d⟨μ, ξ⟩ = ι_{ξ_V} ω` for `μ(x)(ξ) = ½ ω(ξ_V(x), x)`. -/
theorem isMomentMap_representationMomentMap
    (hω : ∀ (g : G) (x y : V), ω (g • x) (g • y) = ω x y) :
    ω.constSmooth.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V)
      (ω.representationMomentMap I G) := by
  have ha : InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V =
      ((InfinitesimalAction.linear V).comp (skewAdjointLieSubalgebra ω.toBilinForm).incl).comp
        (fundamentalSkewAdjointLieHom I G V hω) := by
    rw [InfinitesimalAction.fundamental_eq_linear_comp]
    exact InfinitesimalAction.ext fun ξ ↦ funext fun x ↦ by
      simp only [InfinitesimalAction.comp_apply, InfinitesimalAction.linear_apply,
        LieSubalgebra.coe_incl, coe_fundamentalSkewAdjointLieHom]
      -- Both sides are now `dρ(ξ) x`, up to unfolding the coercion out of the subalgebra.
      rfl
  rw [ha, funext (ω.representationMomentMap_eq_comp hω)]
  exact ω.isMomentMap_linearMomentMap.comp (fundamentalSkewAdjointLieHom I G V hω)

/-- **The moment map of a linear symplectic representation is equivariant.** For a smooth linear
action of a Lie group `G` on a finite-dimensional symplectic vector space `(V, ω)` preserving `ω`,
`μ(x)(ξ) = ½ ω(ξ_V(x), x)` is a group-level moment map: `d⟨μ, ξ⟩ = ι_{ξ_V} ω` and
`μ (g • x) = Ad*_g (μ x)`. -/
theorem isEquivariantMomentMap_representationMomentMap
    (hω : ∀ (g : G) (x y : V), ω (g • x) (g • y) = ω x y) :
    ω.constSmooth.IsEquivariantMomentMap (ω.representationMomentMap I G) :=
  ((ω.isMomentMap_representationMomentMap hω).isEquivariantMomentMap_iff
    (ω.mpullback_smul_constSmooth (I := I) hω) 0).2 fun g ↦ by simp

end TauCeti.SymplecticForm
