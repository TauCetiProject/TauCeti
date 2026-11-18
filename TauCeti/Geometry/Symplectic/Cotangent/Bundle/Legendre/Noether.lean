/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone

/-!
# Noether's theorem for a Lie group symmetry of a Lagrangian

Let a Lie group `G` act smoothly on a configuration manifold `M`, and let `L : TM → ℝ` be a
Lagrangian invariant under the tangent-lifted action `g • (x, v) = (g • x, dg_x v)`
(`TangentBundle.instMulAction`), that is `L (g • v) = L v`. The **Lagrangian momentum map** is the
moment map `μ` of the cotangent-lifted action (`TauCeti.CotangentBundle.momentMap`) composed with
the Legendre map `FL : TM → T*M`. Its component along `ξ ∈ 𝔤` is

`J_ξ(v) = ⟨μ(FL v), ξ⟩ = FL(v)(ξ_M(x))`, for `v ∈ T_x M`,

the derivative of `L` along the fibre through `v` in the direction of the fundamental vector field
`ξ_M` of the action on `M`. This file proves Noether's theorem: the Lagrangian momentum map is
conserved by the Lagrangian dynamics.

* The Legendre map of an invariant Lagrangian intertwines the tangent- and cotangent-lifted
  actions, `FL (g • v) = g • FL v` (`TauCeti.legendreMap_smul`), and the energy is invariant,
  `E_L (g • v) = E_L v` (`TauCeti.lagrangianEnergy_smul`). Both are the naturality of `FL` and
  `E_L` under the diffeomorphisms `x ↦ g • x`.
* Differentiating the first identity, `dFL` carries the fundamental vector field `ξ_{TM}` of the
  tangent-lifted action to the fundamental vector field `ξ_{T*M}` of the cotangent-lifted action
  (`TauCeti.mfderiv_legendreMap_fundamentalVectorField`). Since `μ_ξ` is a Hamiltonian of
  `ξ_{T*M}` for the canonical form `ω` and the Cartan two-form is `ω_L = FL^* ω`, the component
  `J_ξ = μ_ξ ∘ FL` is a Hamiltonian of `ξ_{TM}` for `ω_L`. Together with the coadjoint equivariance
  of `μ`, this says that `μ ∘ FL` is a group-level moment map of the tangent-lifted action on
  `(TM, ω_L)` (`TauCeti.isEquivariantMomentMap_cartanTwoForm_momentMap_comp_legendreMap`).
* **Noether's theorem.** Let `X` be a Hamiltonian vector field of the energy for `ω_L`, such as
  the Lagrangian vector field `X_E` of a regular Lagrangian. Then
  `dJ_ξ(X) = ω_L(ξ_{TM}, X) = -dE_L(ξ_{TM}) = 0`, because the energy is invariant
  (`TauCeti.mvfderiv_lagrangianEnergy_fundamentalVectorField`). So `μ ∘ FL` is constant along every
  integral curve of `X` (`TauCeti.momentMap_legendreMap_eq_of_isMIntegralCurveOn`). The
  Cartan two-form need not be nondegenerate for this; regularity of `L` only provides the
  Lagrangian vector field `X_E`, for which the statement is
  `TauCeti.IsRegularLagrangian.momentMap_legendreMap_eq_of_isMIntegralCurve`.
* **The Hamiltonian side.** For a hyperregular Lagrangian, the Hamiltonian `H = E_L ∘ FL⁻¹` is
  invariant under the cotangent-lifted action (`TauCeti.IsHyperregularLagrangian.hamiltonian_smul`),
  so every component of the cotangent moment map `μ` is a first integral of `H`
  (`TauCeti.IsHyperregularLagrangian.isFirstIntegral_momentMap`). This is the conservation law of
  the Hamiltonian action on `T*M` whose pullback along `FL` is the Lagrangian momentum map.

This is the intrinsic, group-level form of the coordinate statement
`TauCeti.noetherCharge_eq_cotangentMomentMap` for linear symmetries of a Lagrangian on a vector
space.

## Main results

* `TauCeti.legendreMap_smul`, `TauCeti.lagrangianEnergy_smul`: equivariance of the Legendre map and
  invariance of the energy of an invariant Lagrangian.
* `TauCeti.isEquivariantMomentMap_cartanTwoForm_momentMap_comp_legendreMap`: `μ ∘ FL` is a
  coadjoint-equivariant moment map of the tangent-lifted action for the Cartan two-form.
* `TauCeti.momentMap_legendreMap_eq_of_isMIntegralCurveOn`: Noether's theorem, conservation of
  `μ ∘ FL` along integral curves of a Hamiltonian vector field of the energy.
* `TauCeti.IsRegularLagrangian.momentMap_legendreMap_eq_of_isMIntegralCurve`: Noether's theorem
  for the Lagrangian vector field of a regular Lagrangian.
* `TauCeti.IsHyperregularLagrangian.isFirstIntegral_momentMap`: the components of `μ` are first
  integrals of the Hamiltonian of a hyperregular invariant Lagrangian.

## References

* E. Noether, *Invariante Variationsprobleme*, Nachrichten von der Gesellschaft der Wissenschaften
  zu Göttingen, Mathematisch-Physikalische Klasse (1918), 235–257.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 4.2 (momentum maps of Lagrangian systems with symmetry).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (Noether's theorem and the momentum maps
  of tangent and cotangent lifts).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti

open CotangentBundle

/-! ### Invariant Lagrangians -/

section Invariance

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {G : Type*} [Group G] [MulAction G M]
  [ContMDiffConstSMul I ∞ G M] {L : TangentBundle I M → 𝕜} {g : G}

/-- A Lagrangian invariant under the tangent-lifted action of `g` is unchanged by composing it with
the tangent map of `x ↦ g • x`. -/
private theorem comp_tangentMap_constSmul (hL : ∀ v, L (g • v) = L v) :
    L ∘ tangentMap I I (Diffeomorph.constSmul I ∞ g) = L :=
  funext fun v ↦ by
    rw [Function.comp_apply, Diffeomorph.coe_constSmul, ← TangentBundle.smul_eq_tangentMap, hL]

/-- **The Legendre map of an invariant Lagrangian is equivariant.** If `L (g • v) = L v` for every
tangent vector `v`, then the Legendre map intertwines the tangent- and cotangent-lifted actions of
`g`: `FL (g • v) = g • FL v`. -/
theorem legendreMap_smul (hL : ∀ v, L (g • v) = L v) (v : TangentBundle I M) :
    legendreMap L (g • v) = g • legendreMap L v := by
  have h := cotangent_legendreMap_comp_tangentMap L (Diffeomorph.constSmul I ∞ g) v
  rw [comp_tangentMap_constSmul hL, Diffeomorph.cotangent_constSmul, Diffeomorph.constSmul_apply,
    Diffeomorph.coe_constSmul, ← TangentBundle.smul_eq_tangentMap] at h
  exact h.symm

/-- **The energy of an invariant Lagrangian is invariant.** If `L (g • v) = L v` for every tangent
vector `v`, then `E_L (g • v) = E_L v`. -/
theorem lagrangianEnergy_smul (hL : ∀ v, L (g • v) = L v) (v : TangentBundle I M) :
    lagrangianEnergy L (g • v) = lagrangianEnergy L v := by
  have h := congrFun (lagrangianEnergy_comp_tangentMap L (Diffeomorph.constSmul I ∞ g)
    (by simp)) v
  rw [comp_tangentMap_constSmul hL, Function.comp_apply, Diffeomorph.coe_constSmul,
    ← TangentBundle.smul_eq_tangentMap] at h
  exact h.symm

/-- **The Hamiltonian of an invariant hyperregular Lagrangian is invariant** under the
cotangent-lifted action: if `L (g • v) = L v` for every tangent vector `v`, then
`H (g • z) = H z` for the Hamiltonian `H = E_L ∘ FL⁻¹`. -/
theorem IsHyperregularLagrangian.hamiltonian_smul (h : IsHyperregularLagrangian L)
    (hL : ∀ v, L (g • v) = L v) (z : CotangentBundle I M) :
    h.hamiltonian (g • z) = h.hamiltonian z := by
  obtain ⟨v, rfl⟩ := h.bijective_legendreMap.2 z
  rw [← legendreMap_smul hL, h.hamiltonian_legendreMap, h.hamiltonian_legendreMap,
    lagrangianEnergy_smul hL]

end Invariance

/-! ### The Lagrangian momentum map -/

section Noether

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]
  [ContMDiffConstSMul I ∞ G M] {L : TangentBundle I M → ℝ}

/-- **The Legendre map relates fundamental vector fields.** For a smooth Lagrangian invariant under
the tangent-lifted action, the differential of the Legendre map carries the fundamental vector
field `ξ_{TM}` of the tangent-lifted action to the fundamental vector field `ξ_{T*M}` of the
cotangent-lifted action. -/
theorem mfderiv_legendreMap_fundamentalVectorField (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hinv : ∀ (g : G) v, L (g • v) = L v) (ξ : GroupLieAlgebra IG G) (v : TangentBundle I M) :
    mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v
        (fundamentalVectorField I.tangent ξ v) =
      fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ (legendreMap L v) :=
  mfderiv_fundamentalVectorField_of_map_smul
    ((contMDiff_legendreMap (m := ∞) hL le_rfl).mdifferentiableAt (by simp))
    (ContMDiffSMul.mdifferentiableAt_smul_const v 1) (fun g ↦ legendreMap_smul (hinv g) v) ξ

/-- **The energy of an invariant Lagrangian is infinitesimally invariant**: its derivative along
every fundamental vector field `ξ_{TM}` of the tangent-lifted action vanishes. -/
theorem mvfderiv_lagrangianEnergy_fundamentalVectorField (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hinv : ∀ (g : G) v, L (g • v) = L v) (ξ : GroupLieAlgebra IG G) (v : TangentBundle I M) :
    mvfderiv I.tangent (lagrangianEnergy L) v (fundamentalVectorField I.tangent ξ v) = 0 :=
  mvfderiv_fundamentalVectorField_eq_zero
    ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl).mdifferentiableAt (by simp))
    (ContMDiffSMul.mdifferentiableAt_smul_const v 1) (fun g ↦ lagrangianEnergy_smul (hinv g) v) ξ

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompleteSpace EG] [T2Space G]
  [BoundarylessManifold IG G]

/-- Group-level moment maps only need a `C³` Lie group. -/
local instance lieGroupMinSmoothness : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := IG) (G := G) (m := minSmoothness ℝ 3) (n := ∞) (by simp)

/-- **The Lagrangian momentum map is a moment map.** For a smooth Lagrangian invariant under the
tangent-lifted action of `G`, the composite `μ ∘ FL` of the cotangent-lift moment map with the
Legendre map is a coadjoint-equivariant moment map of the tangent-lifted action for the Cartan
two-form: `d⟨μ ∘ FL, ξ⟩ = ι_{ξ_{TM}} ω_L`. -/
theorem isEquivariantMomentMap_cartanTwoForm_momentMap_comp_legendreMap
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hinv : ∀ (g : G) v, L (g • v) = L v) :
    (cartanTwoForm L hL).IsEquivariantMomentMap (momentMap IG G ∘ legendreMap L) where
  contMDiff ξ := (contMDiff_momentMap_apply ξ).comp (contMDiff_legendreMap hL le_rfl)
  isHamiltonianVectorField ξ := by
    have hμ := (isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := M)
      ).isHamiltonianVectorField ξ
    rw [InfinitesimalAction.fundamental_apply] at hμ
    rw [← mpullback_legendreMap_symplecticForm hL, InfinitesimalAction.fundamental_apply]
    exact hμ.mpullback (contMDiff_legendreMap hL le_rfl)
      (fun v ↦ (contMDiff_momentMap_apply ξ (legendreMap L v)).mdifferentiableAt (by simp))
      (mfderiv_legendreMap_fundamentalVectorField hL hinv ξ)
  apply_smul g v := by
    rw [Function.comp_apply, Function.comp_apply, legendreMap_smul (hinv g), momentMap_smul]

/-- **Noether's theorem, pointwise.** For a smooth Lagrangian invariant under the tangent-lifted
action of `G` and a Hamiltonian vector field `X` of the energy for the Cartan two-form, every
component `J_ξ = ⟨μ ∘ FL, ξ⟩` of the Lagrangian momentum map is stationary along `X`:
`dJ_ξ(X) = -dE_L(ξ_{TM}) = 0`. -/
theorem mvfderiv_momentMap_legendreMap_eq_zero (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hinv : ∀ (g : G) v, L (g • v) = L v) {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    (ξ : GroupLieAlgebra IG G) (v : TangentBundle I M) :
    mvfderiv I.tangent (fun w ↦ momentMap IG G (legendreMap L w) ξ) v (X v) = 0 := by
  have h := (isEquivariantMomentMap_cartanTwoForm_momentMap_comp_legendreMap hL hinv
    ).toIsMomentMap.differential_apply_of_isHamiltonianVectorField hX v ξ
  rwa [SmoothTwoForm.IsMomentMap.differential_apply, InfinitesimalAction.fundamental_apply,
    mvfderiv_lagrangianEnergy_fundamentalVectorField hL hinv, neg_zero] at h

/-- **Noether's theorem.** For a smooth Lagrangian invariant under the tangent-lifted action of
`G`, the Lagrangian momentum map `μ ∘ FL` is constant along every integral curve, on a
preconnected set of times, of a Hamiltonian vector field `X` of the energy for the Cartan
two-form. -/
theorem momentMap_legendreMap_eq_of_isMIntegralCurveOn (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hinv : ∀ (g : G) v, L (g • v) = L v) {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} {s : Set ℝ} (hs : IsPreconnected s) (hγ : IsMIntegralCurveOn γ X s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    momentMap IG G (legendreMap L (γ t)) = momentMap IG G (legendreMap L (γ t₀)) := by
  have h := isEquivariantMomentMap_cartanTwoForm_momentMap_comp_legendreMap (IG := IG) hL hinv
  ext ξ
  exact hγ.apply_eq_of_mvfderiv_apply_eq_zero (f := fun w ↦ momentMap IG G (legendreMap L w) ξ)
    hs (fun u _ ↦ (h.contMDiff ξ (γ u)).mdifferentiableAt (by simp))
    (fun u _ ↦ mvfderiv_momentMap_legendreMap_eq_zero hL hinv hX ξ (γ u)) ht₀ ht

/-- **Noether's theorem for a regular Lagrangian.** For a smooth regular Lagrangian invariant under
the tangent-lifted action of `G`, the Lagrangian momentum map `μ ∘ FL` is constant along every
integral curve of the Lagrangian vector field `X_E`, the Hamiltonian vector field of the energy
for the symplectic Cartan two-form. -/
theorem IsRegularLagrangian.momentMap_legendreMap_eq_of_isMIntegralCurve
    (hreg : IsRegularLagrangian L)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hinv : ∀ (g : G) v, L (g • v) = L v)
    {γ : ℝ → TangentBundle I M}
    (hγ : IsMIntegralCurve γ ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)))
    (s t : ℝ) :
    momentMap IG G (legendreMap L (γ t)) = momentMap IG G (legendreMap L (γ s)) :=
  momentMap_legendreMap_eq_of_isMIntegralCurveOn (IG := IG) hL hinv
    ((hreg.isSymplectic_cartanTwoForm hL).isNondegenerate
      |>.isHamiltonianVectorField_hamiltonianVectorField _)
    isPreconnected_univ (hγ.isMIntegralCurveOn _) (Set.mem_univ s) (Set.mem_univ t)

/-- **Hamiltonian conservation of the cotangent moment map.** For a smooth hyperregular Lagrangian
invariant under the tangent-lifted action of `G`, every component `μ_ξ` of the cotangent-lift
moment map is a first integral of the Hamiltonian `H = E_L ∘ FL⁻¹` for the canonical symplectic
form of `T*M`. -/
theorem IsHyperregularLagrangian.isFirstIntegral_momentMap (h : IsHyperregularLagrangian L)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hinv : ∀ (g : G) v, L (g • v) = L v)
    (ξ : GroupLieAlgebra IG G) :
    (symplecticForm I M).IsFirstIntegral h.hamiltonian fun z ↦ momentMap IG G z ξ := by
  have hμ := (isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := M)).toIsMomentMap
  refine SmoothTwoForm.isFirstIntegral_iff.2 fun z ↦ congrFun
    ((hμ.poissonBracket_eq_zero_iff isSymplectic_symplecticForm.isNondegenerate h.hamiltonian
      ξ).2 fun z ↦ ?_) z
  rw [InfinitesimalAction.fundamental_apply]
  exact mvfderiv_fundamentalVectorField_eq_zero
    ((h.contMDiff_hamiltonian hL).mdifferentiableAt (by simp))
    (ContMDiffSMul.mdifferentiableAt_smul_const z 1)
    (fun g ↦ h.hamiltonian_smul (hinv g) z) ξ

end Noether

end TauCeti
