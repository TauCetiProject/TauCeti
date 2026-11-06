/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent

/-!
# Hyperregular Lagrangians and their Hamiltonians

A Lagrangian `L : TM → 𝕜` is **hyperregular** when it is regular and its Legendre map
`FL : TM → T*M` is a bijection (`TauCeti.IsHyperregularLagrangian`). On a boundaryless manifold a
regular Lagrangian has a local diffeomorphism as Legendre map, so for a hyperregular Lagrangian the
Legendre map is a global diffeomorphism `TM ≃ T*M` (`TauCeti.legendreDiffeomorph`); conversely, a
Lagrangian whose Legendre map is a diffeomorphism is hyperregular
(`TauCeti.isHyperregularLagrangian_iff_exists_diffeomorph`).

A hyperregular Lagrangian has a **Hamiltonian** `H = E_L ∘ FL⁻¹` on the cotangent bundle
(`TauCeti.IsHyperregularLagrangian.hamiltonian`), the unique function with `H ∘ FL = E_L`
(`TauCeti.IsHyperregularLagrangian.eq_hamiltonian_iff`). It is as smooth as the energy
(`TauCeti.IsHyperregularLagrangian.contMDiff_hamiltonian`).

For a smooth real Lagrangian on a finite-dimensional boundaryless manifold, the Cartan two-form
`ω_L = FL^*ω` is nondegenerate, hence symplectic, exactly when `L` is regular
(`TauCeti.isNondegenerate_cartanTwoForm_iff`, `TauCeti.isSymplectic_cartanTwoForm_iff`). In the
hyperregular case the Legendre diffeomorphism identifies the Lagrangian vector field, the
Hamiltonian vector field of the energy `E_L` for `ω_L`, with the Hamiltonian vector field of `H` for
the canonical form `ω`
(`TauCeti.IsHyperregularLagrangian.mfderiv_legendreMap_hamiltonianVectorField`).
Hence a curve `γ` in `TM` is an integral curve of the Lagrangian vector field exactly when `FL ∘ γ`
solves Hamilton's equations for `H`
(`TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`): the Lagrangian and the
Hamiltonian dynamics are the same.

The basic example is the mechanical Lagrangian `L(v) = ½ g(v, v) - V(x)` with a symmetric kinetic
form `g`. It is hyperregular exactly when each `g x` is an isomorphism onto the dual
(`TauCeti.isHyperregularLagrangian_mechanicalLagrangian_iff`), in particular for a positive definite
`g` in finite dimensions (`TauCeti.isHyperregularLagrangian_mechanicalLagrangian`), and then its
Hamiltonian is the total energy `H(x, p) = ½ p(g_x⁻¹ p) + V(x)`
(`TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian`).

## Main declarations

* `TauCeti.IsHyperregularLagrangian`: regular Lagrangians with bijective Legendre map.
* `TauCeti.legendreDiffeomorph`: the Legendre map of a hyperregular Lagrangian as a diffeomorphism.
* `TauCeti.IsHyperregularLagrangian.hamiltonian`: the Hamiltonian `H = E_L ∘ FL⁻¹`.
* `TauCeti.isSymplectic_cartanTwoForm_iff`: `ω_L` is symplectic exactly for regular Lagrangians.
* `TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`: equivalence of the
  Lagrangian and Hamiltonian dynamics.
* `TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian`: the Hamiltonian of a
  mechanical system.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.6 (hyperregular Lagrangians and the equivalence with Hamiltonian systems).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.4.
-/

public section

noncomputable section

open Bundle Set Function
open scoped Manifold Topology ContDiff

namespace TauCeti

section Hyperregular

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {L : TangentBundle I M → 𝕜}

/-- A Lagrangian `L : TM → 𝕜` is **hyperregular** when it is regular and its Legendre map
`FL : TM → T*M` is a bijection. For a Lagrangian of class at least `C^2` on a boundaryless manifold
this means that the Legendre map is a diffeomorphism
(`TauCeti.isHyperregularLagrangian_iff_exists_diffeomorph`). Bijectivity alone does not suffice:
`L(v) = v⁴ / 4` on `ℝ` has the bijective Legendre map `v ↦ v³`, whose inverse is not smooth. -/
structure IsHyperregularLagrangian (L : TangentBundle I M → 𝕜) : Prop where
  /-- A hyperregular Lagrangian is regular. -/
  isRegularLagrangian : IsRegularLagrangian L
  /-- The Legendre map of a hyperregular Lagrangian is bijective. -/
  bijective_legendreMap : Bijective (legendreMap L)

namespace IsHyperregularLagrangian

/-- The **Hamiltonian** `H = E_L ∘ FL⁻¹` of a hyperregular Lagrangian `L`: the energy of `L`
transported to the cotangent bundle by the inverse of the Legendre map. -/
def hamiltonian (h : IsHyperregularLagrangian L) (p : CotangentBundle I M) : 𝕜 :=
  lagrangianEnergy L ((Equiv.ofBijective _ h.bijective_legendreMap).symm p)

/-- The Hamiltonian of a hyperregular Lagrangian takes the value of the energy at the Legendre
image of a tangent vector. -/
@[simp]
theorem hamiltonian_legendreMap (h : IsHyperregularLagrangian L) (v : TangentBundle I M) :
    h.hamiltonian (legendreMap L v) = lagrangianEnergy L v := by
  rw [hamiltonian, Equiv.ofBijective_symm_apply_apply]

/-- The Hamiltonian of a hyperregular Lagrangian pulls back to its energy along the Legendre map:
`H ∘ FL = E_L`. -/
theorem hamiltonian_comp_legendreMap (h : IsHyperregularLagrangian L) :
    h.hamiltonian ∘ legendreMap L = lagrangianEnergy L :=
  funext h.hamiltonian_legendreMap

/-- **The Hamiltonian is characterized by the energy**: it is the unique function `K` on the
cotangent bundle with `K ∘ FL = E_L`. -/
theorem eq_hamiltonian_iff (h : IsHyperregularLagrangian L) {K : CotangentBundle I M → 𝕜} :
    K = h.hamiltonian ↔ K ∘ legendreMap L = lagrangianEnergy L := by
  refine ⟨fun hK ↦ hK ▸ h.hamiltonian_comp_legendreMap, fun hK ↦ funext fun p ↦ ?_⟩
  obtain ⟨v, rfl⟩ := h.bijective_legendreMap.2 p
  rw [hamiltonian_legendreMap, ← hK, comp_apply]

end IsHyperregularLagrangian

end Hyperregular

section Diffeomorph

variable {𝕜 E H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {L : TangentBundle I M → 𝕜} {m n : WithTop ℕ∞}
  [IsManifold I.tangent m (TangentBundle I M)]
  [IsManifold (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m (CotangentBundle I M)]
  [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- The **Legendre diffeomorphism** `FL : TM ≃ T*M` of a hyperregular `C^n` Lagrangian: its
Legendre map, a bijective local diffeomorphism of class `C^m` for `m + 1 ≤ n` and `1 ≤ m`. -/
def legendreDiffeomorph (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n) (hm : 1 ≤ m)
    (h : IsHyperregularLagrangian L) :
    TangentBundle I M ≃ₘ^m⟮I.tangent, I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M :=
  ((isLocalDiffeomorph_legendreMap_iff hL hmn hm).2 h.isRegularLagrangian).diffeomorphOfBijective
    h.bijective_legendreMap

/-- The Legendre diffeomorphism is the Legendre map. -/
@[simp]
theorem coe_legendreDiffeomorph (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n)
    (hm : 1 ≤ m) (h : IsHyperregularLagrangian L) :
    ⇑(legendreDiffeomorph hL hmn hm h) = legendreMap L :=
  coe_diffeomorphOfBijective

/-- **A Lagrangian is hyperregular exactly when its Legendre map is a diffeomorphism.** For a `C^n`
Lagrangian on a boundaryless manifold, with `m + 1 ≤ n` and `1 ≤ m`, this holds for `C^m`
diffeomorphisms. -/
theorem isHyperregularLagrangian_iff_exists_diffeomorph (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hmn : m + 1 ≤ n) (hm : 1 ≤ m) :
    IsHyperregularLagrangian L ↔
      ∃ Φ : TangentBundle I M ≃ₘ^m⟮I.tangent, I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M,
        ⇑Φ = legendreMap L := by
  refine ⟨fun h ↦ ⟨legendreDiffeomorph hL hmn hm h, coe_legendreDiffeomorph hL hmn hm h⟩, ?_⟩
  rintro ⟨Φ, hΦ⟩
  refine ⟨(isLocalDiffeomorph_legendreMap_iff hL hmn hm).1 ?_, hΦ ▸ Φ.bijective⟩
  exact hΦ ▸ Φ.isLocalDiffeomorph

namespace IsHyperregularLagrangian

/-- The Hamiltonian of a hyperregular Lagrangian is its energy composed with the inverse of the
Legendre diffeomorphism. -/
theorem hamiltonian_eq_lagrangianEnergy_comp_symm (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hmn : m + 1 ≤ n) (hm : 1 ≤ m) (h : IsHyperregularLagrangian L) :
    h.hamiltonian = lagrangianEnergy L ∘ (legendreDiffeomorph hL hmn hm h).symm := by
  refine (h.eq_hamiltonian_iff.2 (funext fun v ↦ ?_)).symm
  rw [comp_apply, comp_apply, ← coe_legendreDiffeomorph hL hmn hm h,
    Diffeomorph.symm_apply_apply]

/-- **The Hamiltonian is smooth.** The Hamiltonian of a hyperregular `C^n` Lagrangian is `C^m`
whenever `m + 1 ≤ n` and `1 ≤ m`. -/
theorem contMDiff_hamiltonian (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n)
    (hm : 1 ≤ m) (h : IsHyperregularLagrangian L) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) 𝓘(𝕜, 𝕜) m h.hamiltonian := by
  rw [h.hamiltonian_eq_lagrangianEnergy_comp_symm hL hmn hm]
  exact (contMDiff_lagrangianEnergy hL hmn).comp (legendreDiffeomorph hL hmn hm h).symm.contMDiff

end IsHyperregularLagrangian

end Diffeomorph

section Symplectic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}
  [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The Cartan two-form is nondegenerate exactly for regular Lagrangians.** For a smooth real
Lagrangian on a finite-dimensional boundaryless manifold, `ω_L = FL^*ω` is nondegenerate exactly
when all fibre Hessians are invertible. -/
theorem isNondegenerate_cartanTwoForm_iff (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    (cartanTwoForm L hL).IsNondegenerate ↔ IsRegularLagrangian L := by
  have hω := (CotangentBundle.isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate
  rw [← mpullback_legendreMap_symplecticForm hL]
  refine ⟨fun hnd ↦ isRegularLagrangian_iff.2 fun v ↦ ?_, fun hreg ↦ ?_⟩
  · -- A nondegenerate pullback forces injective, hence invertible, differentials of `FL`.
    rw [← isInvertible_mfderiv_legendreMap_iff hL (by simp) v]
    have hinj := ((hω.isNondegenerate_mpullback_iff (contMDiff_legendreMap hL le_rfl)).1 hnd).2 v
    -- Read the differential as a map between the model spaces, of equal finite dimension.
    obtain ⟨T, hT⟩ : ∃ T : E × E →L[ℝ] E × (E →L[ℝ] ℝ),
        mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v = T := ⟨_, rfl⟩
    rw [hT] at hinj ⊢
    have hdim : Module.finrank ℝ (E × E) = Module.finrank ℝ (E × (E →L[ℝ] ℝ)) := by
      rw [Module.finrank_prod, Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq]
    have key (S : E × E →L[ℝ] E × (E →L[ℝ] ℝ)) (hS : Injective S) : S.IsInvertible :=
      ⟨((S : E × E →ₗ[ℝ] E × (E →L[ℝ] ℝ)).linearEquivOfInjective hS
        hdim).toContinuousLinearEquiv, ContinuousLinearMap.ext fun x ↦ by simp⟩
    exact key T hinj
  · exact hω.isNondegenerate_mpullback_of_isLocalDiffeomorph
      ((isLocalDiffeomorph_legendreMap_iff (m := ∞) hL le_rfl (by simp)).2 hreg)

/-- **The Cartan two-form is symplectic exactly for regular Lagrangians.** It is always closed, as
the exterior derivative of the Cartan one-form, and it is nondegenerate exactly when the
Lagrangian is regular. -/
theorem isSymplectic_cartanTwoForm_iff (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    (cartanTwoForm L hL).IsSymplectic ↔ IsRegularLagrangian L := by
  refine ⟨fun h ↦ (isNondegenerate_cartanTwoForm_iff hL).1 h.isNondegenerate, fun h ↦ ⟨?_,
    (isNondegenerate_cartanTwoForm_iff hL).2 h⟩⟩
  rw [← mpullback_legendreMap_symplecticForm hL]
  exact CotangentBundle.isSymplectic_symplecticForm.isClosed.mpullback _ _

namespace IsHyperregularLagrangian

/-- **The Legendre map carries the Lagrangian vector field to the Hamiltonian vector field.** For a
smooth hyperregular Lagrangian, the differential of the Legendre map sends the Hamiltonian vector
field of the energy `E_L` for the Cartan two-form `ω_L` to the Hamiltonian vector field of
`H = E_L ∘ FL⁻¹` for the canonical symplectic form `ω` of the cotangent bundle. -/
theorem mfderiv_legendreMap_hamiltonianVectorField (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (h : IsHyperregularLagrangian L) (v : TangentBundle I M) :
    mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v) =
      (CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian
        (legendreMap L v) := by
  have hloc :=
    (isLocalDiffeomorph_legendreMap_iff (m := ∞) hL le_rfl (by simp)).2 h.isRegularLagrangian
  rw [← h.hamiltonian_comp_legendreMap]
  exact SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp
    ((isNondegenerate_cartanTwoForm_iff hL).2 h.isRegularLagrangian)
    CotangentBundle.isSymplectic_symplecticForm.isNondegenerate (contMDiff_legendreMap hL le_rfl)
    (mpullback_legendreMap_symplecticForm hL) (hloc.isInvertible_mfderiv (by simp) v).surjective
    ((h.contMDiff_hamiltonian (m := ∞) hL le_rfl (by simp) _).mdifferentiableAt (by simp))

/-- **The Lagrangian and Hamiltonian dynamics agree.** For a smooth hyperregular Lagrangian, a
curve `γ` in the tangent bundle is an integral curve of the Lagrangian vector field, the
Hamiltonian vector field of the energy `E_L` for the Cartan two-form `ω_L`, exactly when its
Legendre image `FL ∘ γ` is an integral curve of the Hamiltonian vector field of `H = E_L ∘ FL⁻¹`
for the canonical symplectic form `ω`. -/
theorem isMIntegralCurve_legendreMap_comp_iff (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (h : IsHyperregularLagrangian L) {γ : ℝ → TangentBundle I M} :
    IsMIntegralCurve (legendreMap L ∘ γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian) ↔
      IsMIntegralCurve γ ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) := by
  set Φ := legendreDiffeomorph (m := ∞) hL le_rfl (by simp) h
  have hΦ : ⇑Φ = legendreMap L := coe_legendreDiffeomorph hL le_rfl (by simp) h
  simp only [isMIntegralCurve_iff_isMIntegralCurveOn]
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ ?_⟩
  · -- The inverse diffeomorphism pulls `ω_L = FL^* ω` back to `ω` and `E_L` to `H`, so it carries
    -- the Hamiltonian vector field of `H` to that of `E_L` and the trajectory `FL ∘ γ` to `γ`.
    have hpull : SmoothForm.mpullback Φ.symm Φ.symm.contMDiff (cartanTwoForm L hL) =
        CotangentBundle.symplecticForm I M := by
      refine SmoothForm.mpullback_symm_eq_of_mpullback_eq ?_
      -- The two pullbacks differ only in the map, and `⇑Φ = legendreMap L` is `hΦ`.
      convert mpullback_legendreMap_symplecticForm hL using 3
    have hback := hγ.map_of_mfderiv_eq (f := Φ.symm)
      (fun t _ ↦ (Φ.symm.contMDiff _).mdifferentiableAt (by simp)) fun t _ ↦ by
        rw [h.hamiltonian_eq_lagrangianEnergy_comp_symm (m := ∞) hL le_rfl (by simp)]
        exact SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp
          CotangentBundle.isSymplectic_symplecticForm.isNondegenerate
          ((isNondegenerate_cartanTwoForm_iff hL).2 h.isRegularLagrangian) Φ.symm.contMDiff hpull
          (Φ.symm.isLocalDiffeomorph.isInvertible_mfderiv (by simp) _).surjective
          ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl _).mdifferentiableAt (by simp))
    have hγ' : ⇑Φ.symm ∘ (legendreMap L ∘ γ) = γ := by
      funext t
      rw [comp_apply, comp_apply, ← hΦ, Diffeomorph.symm_apply_apply]
    rwa [hγ'] at hback
  · exact hγ.map_of_mfderiv_eq
      (fun t _ ↦ (contMDiff_legendreMap (m := ∞) hL le_rfl _).mdifferentiableAt (by simp))
      (fun t _ ↦ h.mfderiv_legendreMap_hamiltonianVectorField hL _)

end IsHyperregularLagrangian

end Symplectic

section Mechanical

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

/-- The Legendre map of a mechanical Lagrangian sends a tangent vector `v` at `x` to the covector
`g(v, ·)` at `x`, for symmetric `g`. -/
theorem legendreMap_mechanicalLagrangian_mk (hg : ∀ x v w, g x v w = g x w v) {V : M → ℝ} (x : M)
    (v : TangentSpace I x) :
    legendreMap (mechanicalLagrangian g V) (TotalSpace.mk' E x v) =
      TotalSpace.mk' (E →L[ℝ] ℝ) x (g x v) :=
  CotangentBundle.ext (proj_legendreMap _ _) fun w ↦ by
    rw [legendreMap_mechanicalLagrangian_snd hg]
    rfl

/-- **A mechanical Lagrangian is hyperregular exactly when its kinetic form is invertible**: for
symmetric `g`, the Legendre map `v ↦ g(v, ·)` is then a bijection `TM → T*M`. By
`TauCeti.isRegularLagrangian_mechanicalLagrangian_iff`, a mechanical Lagrangian is therefore
hyperregular exactly when it is regular. -/
theorem isHyperregularLagrangian_mechanicalLagrangian_iff (hg : ∀ x v w, g x v w = g x w v)
    (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) ↔ ∀ x, (g x).IsInvertible := by
  rw [← isRegularLagrangian_mechanicalLagrangian_iff hg V]
  refine ⟨IsHyperregularLagrangian.isRegularLagrangian, fun hreg ↦ ⟨hreg, ?_, ?_⟩⟩
  all_goals have hinv := (isRegularLagrangian_mechanicalLagrangian_iff hg V).1 hreg
  · rintro ⟨x, v⟩ ⟨y, w⟩ hvw
    obtain rfl : x = y := by
      simpa using congrArg TotalSpace.proj hvw
    rw [legendreMap_mechanicalLagrangian_mk hg, legendreMap_mechanicalLagrangian_mk hg] at hvw
    rw [(hinv x).injective (TotalSpace.mk_injective x hvw)]
  · rintro ⟨x, p⟩
    refine ⟨TotalSpace.mk' E x ((g x).inverse p), ?_⟩
    rw [legendreMap_mechanicalLagrangian_mk hg, (hinv x).self_apply_inverse]

/-- **A mechanical Lagrangian with positive definite kinetic form is hyperregular**, on a
finite-dimensional manifold. This covers the Lagrangian `½ |v|² - V(x)` of a Riemannian metric. -/
theorem isHyperregularLagrangian_mechanicalLagrangian [FiniteDimensional ℝ E]
    (hg : ∀ x v w, g x v w = g x w v) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff hg V).2
    ((isRegularLagrangian_mechanicalLagrangian_iff hg V).1
      (isRegularLagrangian_mechanicalLagrangian hg hpos V))

/-- **The Hamiltonian of a mechanical system** is its total energy in terms of momenta: for
symmetric `g`, the Hamiltonian of `L(v) = ½ g(v, v) - V(x)` is `H(x, p) = ½ p(g_x⁻¹ p) + V(x)`. -/
theorem IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian
    (hg : ∀ x v w, g x v w = g x w v) {V : M → ℝ}
    (h : IsHyperregularLagrangian (mechanicalLagrangian g V)) (p : CotangentBundle I M) :
    h.hamiltonian p = 2⁻¹ * p.2 ((g p.proj).inverse p.2) + V p.proj := by
  have hinv := (isHyperregularLagrangian_mechanicalLagrangian_iff hg V).1 h p.proj
  -- The momentum `p` at `x` is the Legendre image of the velocity `g_x⁻¹ p`.
  set v : TangentBundle I M := TotalSpace.mk' E p.proj ((g p.proj).inverse p.2)
  have hgv : g v.proj v.2 = p.2 := hinv.self_apply_inverse p.2
  have hv : legendreMap (mechanicalLagrangian g V) v = p := by
    rw [legendreMap_mechanicalLagrangian_mk hg, hinv.self_apply_inverse]
  calc h.hamiltonian p = h.hamiltonian (legendreMap (mechanicalLagrangian g V) v) := by rw [hv]
    _ = 2⁻¹ * p.2 ((g p.proj).inverse p.2) + V p.proj := by
      rw [h.hamiltonian_legendreMap, lagrangianEnergy_mechanicalLagrangian, hgv]

end Mechanical

end TauCeti
