/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Data.Bundle
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Hyperregular Lagrangians

A Lagrangian `L : TM → 𝕜` is **hyperregular** (`TauCeti.IsHyperregularLagrangian`) when it is
regular and its Legendre map `FL : TM → T*M` is a bijection. For a smooth Lagrangian on a
boundaryless manifold, regularity makes `FL` a local diffeomorphism, so a hyperregular Lagrangian
has a **global** Legendre diffeomorphism `TM ≃ T*M`
(`TauCeti.IsHyperregularLagrangian.legendreDiffeomorph`), and conversely a smooth Lagrangian
whose Legendre map is a diffeomorphism is hyperregular
(`TauCeti.isHyperregularLagrangian_iff_exists_diffeomorph`).

The **Hamiltonian** of a hyperregular Lagrangian is its energy read through the inverse Legendre
map, `H = E_L ∘ FL⁻¹` (`TauCeti.IsHyperregularLagrangian.hamiltonian`). It is the unique
function on `T*M` with `H ∘ FL = E_L` (`TauCeti.IsHyperregularLagrangian.eq_hamiltonian_iff`),
and it is smooth when `L` is.

For a smooth real regular Lagrangian on a boundaryless manifold, the Cartan two-form
`ω_L = FL^*ω` is symplectic (`TauCeti.IsRegularLagrangian.isSymplectic_cartanTwoForm`), so the
energy has a Hamiltonian vector field `X_E` for `ω_L` on `TM`: the Lagrangian vector field. On a
finite-dimensional manifold and for a hyperregular Lagrangian, the Legendre map carries `X_E` to
the Hamiltonian vector field `X_H` of `H` for the canonical symplectic form `ω` of `T*M`
(`TauCeti.IsHyperregularLagrangian.mfderiv_legendreMap_hamiltonianVectorField`). Hence a curve
`γ` in `TM` is an integral curve of `X_E` exactly when `FL ∘ γ` is an integral curve of `X_H`
(`TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`): the Lagrangian and
Hamiltonian flows are conjugate by `FL`.

Subtracting a potential `V : M → 𝕜` keeps a Lagrangian hyperregular and adds `V` to its
Hamiltonian. A mechanical Lagrangian `½ g(v, v) - V(x)` with symmetric kinetic form `g` is
hyperregular exactly when it is regular, that is when each `g x` is invertible onto the dual
(`TauCeti.isHyperregularLagrangian_mechanicalLagrangian_iff`); in finite dimensions this holds for
positive definite `g`. Its Hamiltonian is `H(p) = ½ p(g_x⁻¹ p) + V(x)` for a covector `p` at `x`
(`TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian`).

## Main declarations

* `TauCeti.IsHyperregularLagrangian`: regular Lagrangians with bijective Legendre map.
* `TauCeti.IsHyperregularLagrangian.legendreDiffeomorph`: the Legendre diffeomorphism `TM ≃ T*M`.
* `TauCeti.IsHyperregularLagrangian.hamiltonian`: the Hamiltonian `H = E_L ∘ FL⁻¹`.
* `TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`: the Legendre map
  conjugates the Lagrangian and Hamiltonian flows.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.6.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.4.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

section Hyperregular

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {L : TangentBundle I M → 𝕜}

/-- A Lagrangian `L : TM → 𝕜` is **hyperregular** when it is regular and its Legendre map
`FL : TM → T*M` is a bijection. For a smooth Lagrangian on a boundaryless manifold this says that
`FL` is a diffeomorphism (`TauCeti.isHyperregularLagrangian_iff_exists_diffeomorph`). -/
structure IsHyperregularLagrangian (L : TangentBundle I M → 𝕜) : Prop where
  /-- A hyperregular Lagrangian is regular. -/
  isRegularLagrangian : IsRegularLagrangian L
  /-- The Legendre map of a hyperregular Lagrangian is a bijection. -/
  bijective_legendreMap : Function.Bijective (legendreMap L)

namespace IsHyperregularLagrangian

variable (h : IsHyperregularLagrangian L)

/-- The **Hamiltonian** `H = E_L ∘ FL⁻¹` of a hyperregular Lagrangian `L`: the energy of the
unique tangent vector with the given Legendre transform. -/
def hamiltonian : CotangentBundle I M → 𝕜 :=
  lagrangianEnergy L ∘ (Equiv.ofBijective _ h.bijective_legendreMap).symm

/-- The Hamiltonian of a hyperregular Lagrangian takes the value `E_L(v)` at `FL(v)`. -/
@[simp]
theorem hamiltonian_legendreMap (v : TangentBundle I M) :
    h.hamiltonian (legendreMap L v) = lagrangianEnergy L v := by
  rw [hamiltonian, Function.comp_apply]
  exact congrArg (lagrangianEnergy L)
    ((Equiv.ofBijective _ h.bijective_legendreMap).symm_apply_apply v)

/-- The Hamiltonian of a hyperregular Lagrangian composed with the Legendre map is the energy. -/
theorem hamiltonian_comp_legendreMap : h.hamiltonian ∘ legendreMap L = lagrangianEnergy L :=
  funext h.hamiltonian_legendreMap

/-- **The Hamiltonian is characterized by `H ∘ FL = E_L`**: since the Legendre map of a
hyperregular Lagrangian is onto, this determines `H`. -/
theorem eq_hamiltonian_iff {K : CotangentBundle I M → 𝕜} :
    K = h.hamiltonian ↔ K ∘ legendreMap L = lagrangianEnergy L := by
  refine ⟨fun hK ↦ hK ▸ h.hamiltonian_comp_legendreMap, fun hK ↦ funext fun p ↦ ?_⟩
  obtain ⟨v, rfl⟩ := h.bijective_legendreMap.2 p
  rw [h.hamiltonian_legendreMap, ← hK, Function.comp_apply]

end IsHyperregularLagrangian

/-- Subtracting a potential, a function of the base point only, does not change whether a
Lagrangian is hyperregular. -/
@[simp]
theorem isHyperregularLagrangian_sub_comp_proj_iff {V : M → 𝕜} :
    IsHyperregularLagrangian (fun v ↦ L v - V v.proj) ↔ IsHyperregularLagrangian L := by
  refine ⟨fun h ↦ ⟨isRegularLagrangian_sub_comp_proj_iff.1 h.1, ?_⟩,
    fun h ↦ ⟨isRegularLagrangian_sub_comp_proj_iff.2 h.1, ?_⟩⟩
  · simpa only [legendreMap_sub_comp_proj] using h.2
  · simpa only [legendreMap_sub_comp_proj] using h.2

/-- Subtracting a potential `V` from a hyperregular Lagrangian adds `V` to its Hamiltonian. -/
theorem IsHyperregularLagrangian.hamiltonian_sub_comp_proj (h : IsHyperregularLagrangian L)
    {V : M → 𝕜} (hV : IsHyperregularLagrangian fun v ↦ L v - V v.proj)
    (p : CotangentBundle I M) :
    hV.hamiltonian p = h.hamiltonian p + V p.proj := by
  have hK : (fun p : CotangentBundle I M ↦ h.hamiltonian p + V p.proj) = hV.hamiltonian := by
    rw [hV.eq_hamiltonian_iff, legendreMap_sub_comp_proj]
    funext v
    simp [lagrangianEnergy_sub_comp_proj]
  exact (congrFun hK p).symm

end Hyperregular

section Diffeomorph

variable {𝕜 E H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I.tangent (TangentBundle I M)] {L : TangentBundle I M → 𝕜}

namespace IsHyperregularLagrangian

variable (h : IsHyperregularLagrangian L) (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) ∞ L)

/-- The **Legendre diffeomorphism** `TM ≃ T*M` of a smooth hyperregular Lagrangian on a
boundaryless manifold: its forward map is the Legendre map. -/
def legendreDiffeomorph :
    TangentBundle I M ≃ₘ⟮I.tangent, I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M :=
  (h.isRegularLagrangian.isLocalDiffeomorph_legendreMap hL).diffeomorphOfBijective
    h.bijective_legendreMap

/-- The Legendre diffeomorphism is the Legendre map. -/
@[simp]
theorem coe_legendreDiffeomorph : ⇑(h.legendreDiffeomorph hL) = legendreMap L :=
  coe_diffeomorphOfBijective

/-- The inverse of the Legendre diffeomorphism undoes the Legendre map. -/
@[simp]
theorem legendreDiffeomorph_symm_apply_legendreMap (v : TangentBundle I M) :
    (h.legendreDiffeomorph hL).symm (legendreMap L v) = v := by
  rw [← coe_legendreDiffeomorph h hL, Diffeomorph.symm_apply_apply]

/-- The Legendre map undoes the inverse of the Legendre diffeomorphism. -/
@[simp]
theorem legendreMap_legendreDiffeomorph_symm_apply (p : CotangentBundle I M) :
    legendreMap L ((h.legendreDiffeomorph hL).symm p) = p := by
  rw [← coe_legendreDiffeomorph h hL, Diffeomorph.apply_symm_apply]

/-- The inverse of the Legendre diffeomorphism covers the identity of the base. -/
@[simp]
theorem proj_legendreDiffeomorph_symm_apply (p : CotangentBundle I M) :
    ((h.legendreDiffeomorph hL).symm p).proj = p.proj := by
  conv_rhs => rw [← h.legendreMap_legendreDiffeomorph_symm_apply hL p]
  rw [proj_legendreMap]

/-- The Hamiltonian of a hyperregular Lagrangian is the energy composed with the inverse of the
Legendre diffeomorphism. -/
theorem hamiltonian_eq_comp_symm :
    h.hamiltonian = lagrangianEnergy L ∘ (h.legendreDiffeomorph hL).symm :=
  (h.eq_hamiltonian_iff.2 (funext fun v ↦ by
    rw [Function.comp_apply, Function.comp_apply, legendreDiffeomorph_symm_apply_legendreMap])).symm

/-- **The Hamiltonian of a smooth hyperregular Lagrangian is smooth.** -/
theorem contMDiff_hamiltonian (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) ∞ L) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) 𝓘(𝕜, 𝕜) ∞ h.hamiltonian := by
  rw [h.hamiltonian_eq_comp_symm hL]
  exact (contMDiff_lagrangianEnergy hL le_rfl).comp (h.legendreDiffeomorph hL).symm.contMDiff

end IsHyperregularLagrangian

/-- **A smooth Lagrangian is hyperregular exactly when its Legendre map is a diffeomorphism**, on
a boundaryless manifold. -/
theorem isHyperregularLagrangian_iff_exists_diffeomorph
    (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) ∞ L) :
    IsHyperregularLagrangian L ↔
      ∃ Φ : TangentBundle I M ≃ₘ⟮I.tangent, I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M,
        ⇑Φ = legendreMap L := by
  refine ⟨fun h ↦ ⟨h.legendreDiffeomorph hL, h.coe_legendreDiffeomorph hL⟩, ?_⟩
  rintro ⟨Φ, hΦ⟩
  refine ⟨(isLocalDiffeomorph_legendreMap_iff (m := ∞) hL le_rfl (by simp)).1 ?_,
    hΦ ▸ Φ.bijective⟩
  exact hΦ ▸ Φ.isLocalDiffeomorph

end Diffeomorph

section Symplectic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I.tangent (TangentBundle I M)]
  {L : TangentBundle I M → ℝ}

variable [FiniteDimensional ℝ E]

namespace IsHyperregularLagrangian

variable (h : IsHyperregularLagrangian L) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)

/-- **The Legendre map carries the Lagrangian vector field to the Hamiltonian vector field.** For
a smooth hyperregular Lagrangian `L` on a finite-dimensional boundaryless manifold, the differential
of `FL` sends the Hamiltonian vector field of the energy `E_L` for the Cartan two-form `ω_L` to the
Hamiltonian vector field of `H = E_L ∘ FL⁻¹` for the canonical symplectic form of `T*M`. -/
theorem mfderiv_legendreMap_hamiltonianVectorField (v : TangentBundle I M) :
    mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v) =
      (CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian
        (legendreMap L v) := by
  have hωL := h.isRegularLagrangian.isSymplectic_cartanTwoForm hL
  have := hωL.isNondegenerate.mfderiv_hamiltonianVectorField_comp
    (CotangentBundle.isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate
    (contMDiff_legendreMap hL le_rfl) (mpullback_legendreMap_symplecticForm hL)
    ((h.isRegularLagrangian.isLocalDiffeomorph_legendreMap hL).isInvertible_mfderiv
      (by simp) v).surjective
    ((h.contMDiff_hamiltonian hL _).mdifferentiableAt (by simp))
  rwa [h.hamiltonian_comp_legendreMap] at this

/-- **The Legendre map conjugates the Lagrangian and Hamiltonian flows.** For a smooth
hyperregular Lagrangian `L` on a finite-dimensional boundaryless manifold, a curve `γ` in `TM` is
an integral curve of the Hamiltonian vector field of the energy `E_L` for the Cartan two-form `ω_L`
exactly when `FL ∘ γ` is an integral curve of the Hamiltonian vector field of `H = E_L ∘ FL⁻¹` for
the canonical symplectic form of `T*M`. -/
theorem isMIntegralCurve_legendreMap_comp_iff {γ : ℝ → TangentBundle I M} :
    IsMIntegralCurve (legendreMap L ∘ γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian) ↔
      IsMIntegralCurve γ ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) := by
  have hω := CotangentBundle.isSymplectic_symplecticForm (I := I) (M := M)
  have hωL := h.isRegularLagrangian.isSymplectic_cartanTwoForm hL
  set Φ := h.legendreDiffeomorph hL
  have hΦ : SmoothForm.mpullback Φ Φ.contMDiff (CotangentBundle.symplecticForm I M) =
      cartanTwoForm L hL := by
    simpa only [Φ, coe_legendreDiffeomorph] using mpullback_legendreMap_symplecticForm hL
  constructor
  · intro hγ
    -- Pull back along the inverse Legendre diffeomorphism, which carries `H` to `E_L`.
    have hE : lagrangianEnergy L ∘ Φ.symm = h.hamiltonian :=
      (h.hamiltonian_eq_comp_symm hL).symm
    have := hω.isNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField hωL.isNondegenerate
      Φ.symm.contMDiff (SmoothForm.mpullback_symm_eq_of_mpullback_eq hΦ)
      (fun t ↦ (Φ.symm.isInvertible_mfderiv (by simp)).surjective)
      (fun t ↦ ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl) _).mdifferentiableAt
        (by simp))
      (hE ▸ hγ)
    have hid : ⇑Φ.symm ∘ (legendreMap L ∘ γ) = γ :=
      funext fun t ↦ h.legendreDiffeomorph_symm_apply_legendreMap hL (γ t)
    rwa [hid] at this
  · intro hγ
    exact hωL.isNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField hω.isNondegenerate
      (contMDiff_legendreMap hL le_rfl) (mpullback_legendreMap_symplecticForm hL)
      (fun t ↦ ((h.isRegularLagrangian.isLocalDiffeomorph_legendreMap hL).isInvertible_mfderiv
        (by simp) _).surjective)
      (fun t ↦ ((h.contMDiff_hamiltonian hL _).mdifferentiableAt (by simp)))
      (h.hamiltonian_comp_legendreMap ▸ hγ)

end IsHyperregularLagrangian

end Symplectic

section Mechanical

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

/-- **A mechanical Lagrangian is hyperregular exactly when it is regular**: for symmetric `g`, its
Legendre map `v ↦ g(v, ·)` is a bijection as soon as each `g x` is invertible onto the dual. -/
theorem isHyperregularLagrangian_mechanicalLagrangian_iff (hg : ∀ x v w, g x v w = g x w v)
    (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) ↔ ∀ x, (g x).IsInvertible := by
  rw [← isRegularLagrangian_mechanicalLagrangian_iff hg V]
  refine ⟨fun h ↦ h.isRegularLagrangian, fun hreg ↦ ⟨hreg, ?_⟩⟩
  have hinv := (isRegularLagrangian_mechanicalLagrangian_iff hg V).1 hreg
  rw [funext (legendreMap_mechanicalLagrangian hg V)]
  exact bijective_totalSpace_map_iff.2 fun x ↦ (hinv x).bijective

/-- **A mechanical Lagrangian with positive definite kinetic form is hyperregular**, on a
finite-dimensional manifold. -/
theorem isHyperregularLagrangian_mechanicalLagrangian [FiniteDimensional ℝ E]
    (hg : ∀ x v w, g x v w = g x w v) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff hg V).2
    ((isRegularLagrangian_mechanicalLagrangian_iff hg V).1
      (isRegularLagrangian_mechanicalLagrangian hg hpos V))

/-- **The Hamiltonian of a hyperregular mechanical Lagrangian** is the total energy in terms of
momenta: for symmetric `g` and a covector `p` at `x`, `H(p) = ½ p(g_x⁻¹ p) + V(x)`. -/
theorem IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian
    (hg : ∀ x v w, g x v w = g x w v) {V : M → ℝ}
    (h : IsHyperregularLagrangian (mechanicalLagrangian g V)) (p : CotangentBundle I M) :
    h.hamiltonian p = 2⁻¹ * p.2 ((g p.proj).inverse p.2) + V p.proj := by
  have hinv := (isHyperregularLagrangian_mechanicalLagrangian_iff hg V).1 h p.proj
  -- The covector `p` is the Legendre transform of the velocity `g_x⁻¹ p` at `x`.
  have hp : legendreMap (mechanicalLagrangian g V)
      (TotalSpace.mk' E p.proj ((g p.proj).inverse p.2)) = p :=
    (legendreMap_mechanicalLagrangian hg V _).trans
      (TotalSpace.ext rfl (heq_of_eq (hinv.self_apply_inverse p.2)))
  conv_lhs => rw [← hp, h.hamiltonian_legendreMap, lagrangianEnergy_mechanicalLagrangian]
  dsimp only
  rw [hinv.self_apply_inverse]

end Mechanical

end TauCeti
