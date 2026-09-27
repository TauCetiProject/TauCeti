/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Complex

/-!
# The Maslov phase of maximal totally real subspaces

Let `E` be a complex vector space of dimension `n`, and call a real subspace `L` of `E`
*maximal totally real* when it is complementary to `i L` (`TauCeti.IsMaximalTotallyReal` for the
real-linear map `J = i •`). Such an `L` is a real form of `E`: a real basis of `L` is a complex
basis of `E`. Consequently the complex-linear automorphisms of `E` act transitively on maximal
totally real subspaces, and a complex-linear automorphism `C` preserving `L` is the
complexification of its restriction to `L`, so that `det C` is real.

These two facts make the *Maslov phase*
```
ρ(L₀, A L₀) = det A / conj (det A) = det A ^ 2 / |det A| ^ 2
```
well defined: its value does not depend on the automorphism `A` taking `L₀` to `L = A L₀`,
because two choices differ by an automorphism preserving `L₀`, whose determinant is real. This is
the map `GL(n, ℂ) / GL(n, ℝ) → S¹` through which the Maslov index of a loop of totally real
subspaces is defined as a winding number, and which, for the boundary values of a
Cauchy--Riemann operator with totally real boundary conditions, enters the Riemann--Roch formula
for its Fredholm index. For Lagrangian subspaces of `ℂⁿ` one may take `A` unitary, recovering
the classical formula `ρ(Λ) = det (U) ^ 2` for `Λ = U ℝⁿ`.

The phase is taken relative to a reference subspace `L₀` rather than to a fixed `ℝⁿ ⊆ ℂⁿ`, so
it is coordinate-free; it is multiplicative along chains
(`TauCeti.IsMaximalTotallyReal.maslovPhase_mul_maslovPhase`) and invariant under simultaneous
complex-linear changes of coordinates (`TauCeti.IsMaximalTotallyReal.maslovPhase_map_map`).

## Main declarations

* `TauCeti.IsMaximalTotallyReal.maslovPhase`: the Maslov phase `ρ(L₀, L)`.
* `TauCeti.IsMaximalTotallyReal.maslovPhase_map`: `ρ(L₀, A L₀) = det A / conj (det A)`.
* `TauCeti.IsMaximalTotallyReal.norm_maslovPhase`: the Maslov phase has modulus one.
* `TauCeti.IsMaximalTotallyReal.maslovPhase_map_lsmul`: rotating by `z` has phase
  `(z / conj z) ^ n`, so `e^{iθ} L₀` has phase `e^{2inθ}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the boundary Maslov index of a bundle pair
  with totally real boundary condition).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 2.3 (the map
  `ρ(U ℝⁿ) = det (U) ^ 2` on the Lagrangian Grassmannian).
-/

public section

open Module
open scoped ComplexConjugate

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] {L : Submodule ℝ E}

namespace IsMaximalTotallyReal

variable (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- Two complex-linear automorphisms taking `L` to the same subspace have the same determinant
phase `det A / conj (det A)`: they differ by an automorphism preserving `L`, whose determinant is
real. -/
private theorem det_div_conj_eq_of_map_eq {A B : E ≃ₗ[ℂ] E}
    (h : L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ) = L.map ((B : E →ₗ[ℂ] E).restrictScalars ℝ)) :
    LinearMap.det (A : E →ₗ[ℂ] E) / conj (LinearMap.det (A : E →ₗ[ℂ] E)) =
      LinearMap.det (B : E →ₗ[ℂ] E) / conj (LinearMap.det (B : E →ₗ[ℂ] E)) := by
  let C : E ≃ₗ[ℂ] E := B.trans A.symm
  have hC : ∀ x ∈ L, (C : E →ₗ[ℂ] E) x ∈ L := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ : B x ∈ L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ) :=
      h ▸ Submodule.mem_map_of_mem hx
    have hCx : (C : E →ₗ[ℂ] E) x = y := by
      simp only [C, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
      rw [← hyx]
      exact A.symm_apply_apply y
    exact hCx ▸ hy
  have hB : (B : E →ₗ[ℂ] E) = (A : E →ₗ[ℂ] E) ∘ₗ (C : E →ₗ[ℂ] E) := by
    ext x
    simp [C]
  have hr := hL.det_eq_det_restrict (C : E →ₗ[ℂ] E) hC
  have hr0 : LinearMap.det (C : E →ₗ[ℂ] E) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact (LinearEquiv.det C).ne_zero
  rw [hB, LinearMap.det_comp, map_mul, hr, Complex.conj_ofReal]
  rw [hr] at hr0
  exact (mul_div_mul_right _ _ hr0).symm

end IsMaximalTotallyReal

end TauCeti

namespace TauCeti

namespace IsMaximalTotallyReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] {L : Submodule ℝ E}
  (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- The **Maslov phase** `ρ(L₀, L)` of two maximal totally real subspaces of a complex module.
For `L = A L₀` it is `det A / conj (det A)`; the value is independent of the choice of `A`. -/
noncomputable def maslovPhase {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') : ℂ :=
  let A := (hL.exists_linearEquiv_map_eq hL').choose
  LinearMap.det (A : E →ₗ[ℂ] E) / conj (LinearMap.det (A : E →ₗ[ℂ] E))

/-- The Maslov phase has modulus one. -/
@[simp]
theorem norm_maslovPhase {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') :
    ‖hL.maslovPhase hL'‖ = 1 := by
  unfold maslovPhase
  have h0 : LinearMap.det (((hL.exists_linearEquiv_map_eq hL').choose : E ≃ₗ[ℂ] E) :
      E →ₗ[ℂ] E) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact (LinearEquiv.det (hL.exists_linearEquiv_map_eq hL').choose).ne_zero
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

/-- The Maslov phase is nonzero. -/
@[simp]
theorem maslovPhase_ne_zero {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') :
    hL.maslovPhase hL' ≠ 0 :=
  norm_ne_zero_iff.1 (by simp)

private theorem maslovPhase_congr {L₁ L₂ : Submodule ℝ E}
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁)
    (hL₂ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₂)
    (h : L₁ = L₂) : hL.maslovPhase hL₁ = hL.maslovPhase hL₂ := by
  subst L₂
  rfl

/-- The Maslov phase of `A L` relative to a maximal totally real `L` is the determinant phase
`det A / conj (det A)` of the complex-linear automorphism `A`. -/
@[simp]
theorem maslovPhase_map (A : E ≃ₗ[ℂ] E) :
    hL.maslovPhase (hL.map_linearEquiv A) =
      LinearMap.det (A : E →ₗ[ℂ] E) / conj (LinearMap.det (A : E →ₗ[ℂ] E)) := by
  unfold maslovPhase
  exact hL.det_div_conj_eq_of_map_eq (hL.exists_linearEquiv_map_eq
    (hL.map_linearEquiv A)).choose_spec

/-- A maximal totally real subspace has Maslov phase one relative to itself. -/
@[simp]
theorem maslovPhase_self : hL.maslovPhase hL = 1 := by
  simpa [div_self] using hL.maslovPhase_map (LinearEquiv.refl ℂ E)

/-- The Maslov phase is multiplicative along chains of maximal totally real subspaces:
`ρ(L₀, L₁) ρ(L₁, L₂) = ρ(L₀, L₂)`. -/
theorem maslovPhase_mul_maslovPhase {L₁ L₂ : Submodule ℝ E}
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁)
    (hL₂ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₂) :
    hL.maslovPhase hL₁ * hL₁.maslovPhase hL₂ = hL.maslovPhase hL₂ := by
  obtain ⟨A, rfl⟩ := hL.exists_linearEquiv_map_eq hL₁
  obtain ⟨B, rfl⟩ := hL₁.exists_linearEquiv_map_eq hL₂
  have hAB : (L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ)).map ((B : E →ₗ[ℂ] E).restrictScalars ℝ) =
      L.map (((A.trans B : E ≃ₗ[ℂ] E) : E →ₗ[ℂ] E).restrictScalars ℝ) := by
    rw [← Submodule.map_comp, LinearEquiv.coe_trans, LinearMap.restrictScalars_comp]
  rw [hL.maslovPhase_map, hL₁.maslovPhase_map,
    hL.maslovPhase_congr hL₂ (hL.map_linearEquiv (A.trans B)) hAB,
    hL.maslovPhase_map, LinearEquiv.coe_trans, LinearMap.det_comp, map_mul,
    mul_div_mul_comm, mul_comm]

/-- Exchanging the two subspaces inverts the Maslov phase. -/
theorem maslovPhase_symm {L₁ : Submodule ℝ E}
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁) :
    hL₁.maslovPhase hL = (hL.maslovPhase hL₁)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm, hL.maslovPhase_mul_maslovPhase hL₁ hL, hL.maslovPhase_self]

/-- The Maslov phase is invariant under a simultaneous complex-linear change of coordinates. -/
theorem maslovPhase_map_map {L₁ : Submodule ℝ E}
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁)
    (B : E ≃ₗ[ℂ] E) :
    (hL.map_linearEquiv B).maslovPhase (hL₁.map_linearEquiv B) = hL.maslovPhase hL₁ := by
  obtain ⟨A, rfl⟩ := hL.exists_linearEquiv_map_eq hL₁
  -- `B (A L) = (B A B⁻¹) (B L)`, and conjugation does not change the determinant.
  let C : E ≃ₗ[ℂ] E := B.symm.trans (A.trans B)
  have hconj : (L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ)).map ((B : E →ₗ[ℂ] E).restrictScalars ℝ) =
      (L.map ((B : E →ₗ[ℂ] E).restrictScalars ℝ)).map ((C : E →ₗ[ℂ] E).restrictScalars ℝ) := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    ext x
    simp [C]
  have hdet : LinearMap.det (C : E →ₗ[ℂ] E) = LinearMap.det (A : E →ₗ[ℂ] E) := by
    rw [← LinearMap.det_conj (A : E →ₗ[ℂ] E) B]
    simp only [C, LinearEquiv.coe_trans, LinearMap.comp_assoc]
  rw [(hL.map_linearEquiv B).maslovPhase_congr (hL₁.map_linearEquiv B)
    ((hL.map_linearEquiv B).map_linearEquiv C) hconj,
    (hL.map_linearEquiv B).maslovPhase_map, hdet, hL.maslovPhase_map]

/-- Rotating a maximal totally real subspace `L` of an `n`-dimensional complex module by a nonzero
scalar `z` has Maslov phase `(z / conj z) ^ n`; for `z = e^{iθ}` this is `e^{2inθ}`. -/
theorem maslovPhase_map_lsmul {z : ℂ} (hz : z ≠ 0) :
    hL.maslovPhase (hL.map_linearEquiv (LinearEquiv.smulOfNeZero ℂ E z hz)) =
      (z / conj z) ^ finrank ℂ E := by
  have hA : ((LinearEquiv.smulOfNeZero ℂ E z hz : E ≃ₗ[ℂ] E) : E →ₗ[ℂ] E) =
      LinearMap.lsmul ℂ E z := by
    ext x
    simp
  have hsmul : LinearMap.lsmul ℂ E z = z • LinearMap.id := by
    ext x
    simp
  calc
    hL.maslovPhase (hL.map_linearEquiv (LinearEquiv.smulOfNeZero ℂ E z hz)) =
        LinearMap.det (LinearEquiv.smulOfNeZero ℂ E z hz : E →ₗ[ℂ] E) /
          conj (LinearMap.det (LinearEquiv.smulOfNeZero ℂ E z hz : E →ₗ[ℂ] E)) :=
      hL.maslovPhase_map _
    _ = (z / conj z) ^ finrank ℂ E := by
      rw [hA, hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, ← div_pow]

/-- The image `i L` of a maximal totally real subspace `L` of an `n`-dimensional complex module
has Maslov phase `(-1) ^ n` relative to `L`. -/
theorem maslovPhase_map_I :
    hL.maslovPhase (hL.map_linearEquiv
      (LinearEquiv.smulOfNeZero ℂ E Complex.I Complex.I_ne_zero)) =
      (-1) ^ finrank ℂ E := by
  rw [hL.maslovPhase_map_lsmul Complex.I_ne_zero, Complex.conj_I, div_neg,
    div_self Complex.I_ne_zero]

end IsMaximalTotallyReal

end TauCeti
