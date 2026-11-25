/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Pullback
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

/-!
# Noether's theorem for Lagrangians with a configuration symmetry

Let a Lie group `G` act smoothly on a configuration manifold `M`. Its tangent lift
`g • v = dg_x v` (`TangentBundle.instMulAction`) acts on the velocity phase space `TM`, and its
cotangent lift `g • p = p ∘ (dg_x)⁻¹` (`TauCeti.CotangentBundle.instMulAction`) acts on the momentum
phase space `T*M`, where it has the moment map `⟨μ(x, p), ξ⟩ = p(ξ_M(x))`
(`TauCeti.CotangentBundle.momentMap`).

Let `L : TM → ℝ` be a smooth Lagrangian invariant under the action, `L (g • v) = L v`. Reading `L`
through the diffeomorphism `x ↦ g • x` gives `L` back, so the naturality of Lagrangian mechanics
under changes of configuration coordinates makes the Legendre map `FL : TM → T*M` equivariant,
`FL (g • v) = g • FL v` (`TauCeti.legendreMap_smul`), and the energy `E_L` invariant
(`TauCeti.lagrangianEnergy_smul`). The **Noether charges** of the symmetry are the components of

`J = μ ∘ FL`, `⟨J(v), ξ⟩ = FL(v)(ξ_M(x))` for `v ∈ T_x M`,

the momentum `FL(v)` paired with the infinitesimal symmetry `ξ_M`. The fundamental vector field
`ξ_{TM}` of the tangent-lifted action covers `ξ_M`, so this is the Cartan form `θ_L = FL^*λ`
evaluated on `ξ_{TM}` (`TauCeti.cartanForm_apply_fundamentalVectorField`). Since `FL` is
equivariant and pulls the canonical symplectic form `ω` of `T*M` back to the Cartan two-form
`ω_L`, the moment map `μ` pulls back to a coadjoint-equivariant moment map `J` of the
tangent-lifted action for `ω_L` (`TauCeti.isEquivariantMomentMap_momentMap_comp_legendreMap`):
`d⟨J, ξ⟩ = ι_{ξ_{TM}} ω_L`.

**Noether's theorem** (`TauCeti.momentMap_legendreMap_eq_of_isMIntegralCurveOn`) follows from the
conservation law of moment maps under invariant Hamiltonians
(`TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant`): along an
integral curve of a Lagrangian vector field `X`, that is `ι_X ω_L = dE_L`, the derivative of
`⟨J, ξ⟩` is `ω_L(ξ_{TM}, X) = -dE_L(ξ_{TM})`, and this vanishes because `E_L` is invariant. So
`J` is constant along every motion of the system. Neither regularity of `L` nor nondegeneracy
of `ω_L` is used: when `L` is regular, `X` is the Lagrangian vector field and its integral curves
are the velocity curves of the motions
(`TauCeti.IsRegularLagrangian.eq_curveVelocityLift_of_isMIntegralCurve`).

For a hyperregular Lagrangian the Hamiltonian `H = E_L ∘ FL⁻¹` is invariant under the
cotangent-lifted action (`TauCeti.IsHyperregularLagrangian.hamiltonian_smul`), so the moment map
`μ` is conserved along the Hamiltonian motions in `T*M`
(`TauCeti.IsHyperregularLagrangian.momentMap_eq_of_isMIntegralCurveOn`); moreover, every
component of `μ` Poisson-commutes with `H`
(`TauCeti.IsHyperregularLagrangian.isFirstIntegral_momentMap`). This is the same conservation
law: the Legendre map carries the Lagrangian motions to the Hamiltonian ones
(`TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`), and `J = μ ∘ FL`.

The flat version, for configuration spaces that are normed spaces and symmetries with a gauge
term, is `TauCeti.noetherCharge_eq_of_eulerLagrange`; for a linear symmetry its charge is the
cotangent moment map of the Legendre image (`TauCeti.noetherCharge_eq_cotangentMomentMap`).

## Main results

* `TauCeti.legendreMap_smul`, `TauCeti.lagrangianEnergy_smul`: for an invariant Lagrangian the
  Legendre map is equivariant and the energy is invariant.
* `TauCeti.IsHyperregularLagrangian.hamiltonian_smul`: the Hamiltonian of an invariant
  hyperregular Lagrangian is invariant.
* `TauCeti.cartanForm_apply_fundamentalVectorField`: the Noether charge `⟨μ(FL v), ξ⟩` is the
  Cartan form evaluated on the fundamental vector field `ξ_{TM}`.
* `TauCeti.isEquivariantMomentMap_momentMap_comp_legendreMap`: the Noether charges `μ ∘ FL` form a
  coadjoint-equivariant moment map for the Cartan two-form.
* `TauCeti.momentMap_legendreMap_eq_of_isMIntegralCurveOn`,
  `TauCeti.momentMap_legendreMap_eq_of_isMIntegralCurve`: **Noether's theorem**, the Noether
  charges are conserved along the integral curves of a Lagrangian vector field.
* `TauCeti.IsHyperregularLagrangian.momentMap_eq_of_isMIntegralCurveOn`,
  `TauCeti.IsHyperregularLagrangian.isFirstIntegral_momentMap`: the moment map is conserved along
  the Hamiltonian motions of an invariant hyperregular Lagrangian, and its components are first
  integrals of the Hamiltonian.

## References

* E. Noether, *Invariante Variationsprobleme*, Nachrichten von der Gesellschaft der Wissenschaften
  zu Göttingen, Mathematisch-Physikalische Klasse (1918), 235–257.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 4.2 (Noether's theorem for the momentum map of a Lagrangian system).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 12.4 (momentum maps of lifted actions on tangent bundles,
  and the Lagrangian Noether theorem).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

section Invariant

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {G : Type*} [Group G] [MulAction G M]
  [ContMDiffConstSMul I ∞ G M] {L : TangentBundle I M → 𝕜} {g : G}

/-- An element `g` preserves `L` exactly when `L` read through the diffeomorphism `x ↦ g • x` is
`L` itself. -/
private theorem comp_tangentMap_constSmul (hLg : ∀ v, L (g • v) = L v) :
    L ∘ tangentMap I I (Diffeomorph.constSmul I ∞ g) = L :=
  funext fun v ↦ by
    rw [← Diffeomorph.coe_tangent, Diffeomorph.tangent_constSmul, Function.comp_apply,
      Diffeomorph.coe_constSmul, hLg]

/-- **The Legendre map of an invariant Lagrangian is equivariant.** If `g` preserves `L`, then
`FL (g • v) = g • FL v`, for the tangent-lifted action on `TM` and the cotangent-lifted action on
`T*M`. -/
theorem legendreMap_smul (hLg : ∀ v, L (g • v) = L v) (v : TangentBundle I M) :
    legendreMap L (g • v) = g • legendreMap L v := by
  have h := cotangent_legendreMap_comp_tangentMap L (Diffeomorph.constSmul I ∞ g) v
  rw [comp_tangentMap_constSmul hLg, Diffeomorph.coe_constSmul,
    ← TangentBundle.smul_eq_tangentMap, ← CotangentBundle.smul_def] at h
  exact h.symm

/-- **The energy of an invariant Lagrangian is invariant**: if `g` preserves `L`, then
`E_L (g • v) = E_L v`. -/
theorem lagrangianEnergy_smul (hLg : ∀ v, L (g • v) = L v) (v : TangentBundle I M) :
    lagrangianEnergy L (g • v) = lagrangianEnergy L v := by
  have h := congrFun (lagrangianEnergy_comp_tangentMap L (Diffeomorph.constSmul I ∞ g)
    (by simp)) v
  rw [comp_tangentMap_constSmul hLg, Function.comp_apply, Diffeomorph.coe_constSmul,
    ← TangentBundle.smul_eq_tangentMap] at h
  exact h.symm

/-- **The Hamiltonian of an invariant hyperregular Lagrangian is invariant**: if `g` preserves
`L`, then `H (g • p) = H p` for the cotangent-lifted action. -/
theorem IsHyperregularLagrangian.hamiltonian_smul (hL : IsHyperregularLagrangian L)
    (hLg : ∀ v, L (g • v) = L v) (p : CotangentBundle I M) :
    hL.hamiltonian (g • p) = hL.hamiltonian p := by
  -- `p ↦ H (g • p)` composed with `FL` is `v ↦ E_L (g • v) = E_L v`, which characterizes `H`.
  have hH : (fun p ↦ hL.hamiltonian (g • p)) = hL.hamiltonian :=
    hL.eq_hamiltonian_iff.2 <| funext fun v ↦ by
      rw [Function.comp_apply, ← legendreMap_smul hLg, hL.hamiltonian_legendreMap,
        lagrangianEnergy_smul hLg]
  exact congrFun hH p

end Invariant

section Charge

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [IsManifold IG ∞ G] {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ContMDiffConstSMul I ∞ G M]

/-- **The Noether charge is the Cartan form on the symmetry.** The Cartan one-form `θ_L = FL^*λ`
evaluated on the fundamental vector field `ξ_{TM}` of the tangent-lifted action is the Noether
charge `⟨μ(FL v), ξ⟩ = FL(v)(ξ_M(π v))`. -/
theorem cartanForm_apply_fundamentalVectorField {L : TangentBundle I M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (ξ : GroupLieAlgebra IG G) (v : TangentBundle I M) :
    (cartanForm L hL).val v ![fundamentalVectorField I.tangent ξ v] =
      CotangentBundle.momentMap IG G (legendreMap L v) ξ := by
  rw [cartanForm_apply, Matrix.cons_val_zero, TangentBundle.mfderiv_proj_fundamentalVectorField,
    CotangentBundle.momentMap_apply]
  -- The Legendre map covers the identity, `π (FL v) = π v`.
  exact congrArg (legendreMap L v).snd
    (congrArg (fundamentalVectorField I ξ) (proj_legendreMap L v).symm)

end Charge

section Noether

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [T2Space G] [BoundarylessManifold IG G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M] [ContMDiffConstSMul I ∞ G M] {L : TangentBundle I M → ℝ}

/-- The pullback of moment maps only needs a `C³` Lie group. -/
local instance lieGroupMinSmoothness : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := IG) (G := G) (m := minSmoothness ℝ 3) (n := ∞) (by simp)

/-- **The Noether charges form a moment map.** For a smooth Lagrangian `L` invariant under the
tangent lift of a smooth action of `G`, the Noether charges
`⟨μ(FL v), ξ⟩ = FL(v)(ξ_M(x))` (`TauCeti.CotangentBundle.momentMap_apply`) form a
coadjoint-equivariant moment map of the tangent-lifted action for the Cartan two-form `ω_L`:
`d⟨μ ∘ FL, ξ⟩ = ι_{ξ_{TM}} ω_L`. -/
theorem isEquivariantMomentMap_momentMap_comp_legendreMap
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hLG : ∀ (g : G) v, L (g • v) = L v) :
    (cartanTwoForm L hL).IsEquivariantMomentMap
      (CotangentBundle.momentMap IG G ∘ legendreMap L) := by
  rw [← mpullback_legendreMap_symplecticForm hL]
  exact CotangentBundle.isEquivariantMomentMap_momentMap.mpullback
    (contMDiff_legendreMap hL le_rfl) fun g ↦ legendreMap_smul (hLG g)

/-- **Noether's theorem.** Let `L` be a smooth Lagrangian invariant under the tangent lift of a
smooth action of `G`, and let `X` be a Lagrangian vector field, `ι_X ω_L = dE_L`. Along an
integral curve `γ` of `X` on a preconnected set `s` of times, the Noether charges
`⟨μ(FL v), ξ⟩ = FL(v)(ξ_M(x))` are constant. -/
theorem momentMap_legendreMap_eq_of_isMIntegralCurveOn (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hLG : ∀ (g : G) v, L (g • v) = L v)
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ X s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    CotangentBundle.momentMap IG G (legendreMap L (γ t)) =
      CotangentBundle.momentMap IG G (legendreMap L (γ t₀)) :=
  (isEquivariantMomentMap_momentMap_comp_legendreMap hL hLG).toIsMomentMap
    |>.apply_eq_of_isMIntegralCurveOn_of_smul_invariant (fun g ↦ lagrangianEnergy_smul (hLG g))
      hX hs hγ (fun t _ ↦ (contMDiff_lagrangianEnergy hL (m := 1) (by simp)).mdifferentiableAt
        one_ne_zero) ht₀ ht

/-- **Noether's theorem** along a global integral curve: for a smooth Lagrangian `L` invariant
under the tangent lift of a smooth action of `G`, the Noether charges are constant along every
integral curve of a Lagrangian vector field. -/
theorem momentMap_legendreMap_eq_of_isMIntegralCurve (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hLG : ∀ (g : G) v, L (g • v) = L v)
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} (hγ : IsMIntegralCurve γ X) (t₀ t : ℝ) :
    CotangentBundle.momentMap IG G (legendreMap L (γ t)) =
      CotangentBundle.momentMap IG G (legendreMap L (γ t₀)) :=
  momentMap_legendreMap_eq_of_isMIntegralCurveOn hL hLG hX isPreconnected_univ
    (hγ.isMIntegralCurveOn _) (Set.mem_univ t₀) (Set.mem_univ t)

/-- **Noether's theorem on the Hamiltonian side.** For a smooth hyperregular Lagrangian `L`
invariant under the tangent lift of a smooth action of `G`, the moment map `μ` of the
cotangent-lifted action is constant along every integral curve of a Hamiltonian vector field of
`H = E_L ∘ FL⁻¹` on a preconnected set of times. -/
theorem IsHyperregularLagrangian.momentMap_eq_of_isMIntegralCurveOn
    (hLh : IsHyperregularLagrangian L) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hLG : ∀ (g : G) v, L (g • v) = L v)
    {X : (p : CotangentBundle I M) → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p}
    (hX : (CotangentBundle.symplecticForm I M).IsHamiltonianVectorField hLh.hamiltonian X)
    {γ : ℝ → CotangentBundle I M} {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ X s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    CotangentBundle.momentMap IG G (γ t) = CotangentBundle.momentMap IG G (γ t₀) :=
  CotangentBundle.isEquivariantMomentMap_momentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant
    (fun g ↦ hLh.hamiltonian_smul (hLG g)) hX hs hγ
    (fun t _ ↦ (hLh.contMDiff_hamiltonian hL).mdifferentiableAt (by simp)) ht₀ ht

/-- **The moment map is a first integral of the Hamiltonian.** For a hyperregular Lagrangian `L`
invariant under the tangent lift of a smooth action of `G`, every component `μ_ξ` of the
cotangent-lift moment map Poisson-commutes with the Hamiltonian `H = E_L ∘ FL⁻¹` for the
canonical symplectic form of `T*M`. -/
theorem IsHyperregularLagrangian.isFirstIntegral_momentMap (hLh : IsHyperregularLagrangian L)
    (hLG : ∀ (g : G) v, L (g • v) = L v) (ξ : GroupLieAlgebra IG G) :
    (CotangentBundle.symplecticForm I M).IsFirstIntegral hLh.hamiltonian
      fun p ↦ CotangentBundle.momentMap IG G p ξ :=
  SmoothTwoForm.isFirstIntegral_iff.2 <| congrFun <|
    CotangentBundle.isEquivariantMomentMap_momentMap.toIsMomentMap
      |>.poissonBracket_eq_zero_of_smul_invariant
        CotangentBundle.isSymplectic_symplecticForm.isNondegenerate
        (fun g ↦ hLh.hamiltonian_smul (hLG g)) ξ

end Noether

end TauCeti
