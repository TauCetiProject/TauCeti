/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.TotallyReal.Basic

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

* `TauCeti.IsTotallyReal.linearIndependent_complex`: real-linearly independent vectors of a
  totally real subspace are complex-linearly independent.
* `TauCeti.IsMaximalTotallyReal.complexBasis`: a real basis of a maximal totally real subspace,
  as a complex basis of the ambient space.
* `TauCeti.IsMaximalTotallyReal.det_eq_det_restrict`: a complex-linear map preserving a maximal
  totally real subspace has the same (real) determinant as its restriction.
* `TauCeti.IsMaximalTotallyReal.exists_linearEquiv_map_eq`: the complex-linear automorphisms act
  transitively on maximal totally real subspaces.
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
  {L : Submodule ℝ E}

/-- Vectors of a totally real subspace of a complex module that are linearly independent over `ℝ`
are linearly independent over `ℂ`. -/
theorem IsTotallyReal.linearIndependent_complex
    (hL : IsTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L) {ι : Type*}
    {v : ι → E} (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L) : LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  -- Split `∑ gⱼ vⱼ` into `a + i b` with `a, b ∈ L`; total reality forces `a = b = 0`.
  set a : E := ∑ j ∈ s, (g j).re • v j
  set b : E := ∑ j ∈ s, (g j).im • v j
  have hsplit : ∑ j ∈ s, g j • v j = a + Complex.I • b := by
    simp only [a, b, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
      ← add_smul, mul_comm]
    simp
  have hb : b ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hvL j)
  have hab : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left (hsplit ▸ hsum)
  have ha0 : a = 0 := by
    refine Submodule.disjoint_def.1 hL.disjoint a (L.sum_mem fun j _ => L.smul_mem _ (hvL j)) ?_
    rw [hab]
    exact Submodule.neg_mem _ ⟨b, hb, rfl⟩
  have hb0 : b = 0 := by
    rw [ha0, zero_eq_neg, smul_eq_zero] at hab
    exact hab.resolve_left Complex.I_ne_zero
  exact Complex.ext (hv s _ ha0 i hi) (hv s _ hb0 i hi)

namespace IsMaximalTotallyReal

variable (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- Vectors spanning a maximal totally real subspace over `ℝ` span the ambient complex module over
`ℂ`. -/
theorem span_complex_eq_top {ι : Type*} {v : ι → E} (hv : Submodule.span ℝ (Set.range v) = L) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  have hle : L ≤ (Submodule.span ℂ (Set.range v)).restrictScalars ℝ :=
    hv ▸ Submodule.span_le_restrictScalars ℝ ℂ _
  have hJle : L.map ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) ≤
      (Submodule.span ℂ (Set.range v)).restrictScalars ℝ := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem _ Complex.I (hle hx)
  rw [← Submodule.restrictScalars_eq_top_iff ℝ, eq_top_iff, ← hL.sup_eq_top]
  exact sup_le hle hJle

/-- A real basis of a maximal totally real subspace `L` of a complex module `E` is a complex basis
of `E`: `L` is a real form of `E`. -/
noncomputable def complexBasis {ι : Type*} (b : Basis ι ℝ L) : Basis ι ℂ E :=
  Basis.mk (v := L.subtype ∘ b)
    (hL.isTotallyReal.linearIndependent_complex
      (b.linearIndependent.map' L.subtype L.ker_subtype) fun i => (b i).2)
    (hL.span_complex_eq_top (by
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top])).ge

@[simp]
theorem complexBasis_apply {ι : Type*} (b : Basis ι ℝ L) (i : ι) :
    hL.complexBasis b i = b i :=
  Basis.mk_apply _ _ _

/-- The complex coordinates of a vector of `L` in `complexBasis b` are its real coordinates in
`b`. -/
@[simp]
theorem complexBasis_repr_coe {ι : Type*} (b : Basis ι ℝ L) (x : L) (i : ι) :
    (hL.complexBasis b).repr x i = b.repr x i := by
  have h : ((hL.complexBasis b).repr.toLinearMap.restrictScalars ℝ).comp L.subtype =
      (Finsupp.mapRange.linearMap Complex.ofRealAm.toLinearMap).comp b.repr.toLinearMap :=
    b.ext fun j => by
      have hj := (hL.complexBasis b).repr_self j
      rw [complexBasis_apply] at hj
      simp [hj]
  simpa using DFunLike.congr_fun (LinearMap.congr_fun h x) i

/-- A complex-linear automorphism maps maximal totally real subspaces to maximal totally real
subspaces. -/
theorem map_linearEquiv (A : E ≃ₗ[ℂ] E) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      (L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ)) := by
  have hcomm : ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ).comp
      ((A : E →ₗ[ℂ] E).restrictScalars ℝ) =
        ((A : E →ₗ[ℂ] E).restrictScalars ℝ).comp
          ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) :=
    LinearMap.ext fun x => (A.map_smul Complex.I x).symm
  rw [isMaximalTotallyReal_iff, ← Submodule.map_comp, hcomm, Submodule.map_comp]
  exact Submodule.isCompl_map (A.restrictScalars ℝ) hL.isCompl

variable [FiniteDimensional ℂ E]

/-- A maximal totally real subspace has real dimension equal to the complex dimension of the
ambient module. -/
theorem finrank_eq_finrank_complex : finrank ℝ L = finrank ℂ E := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  rw [finrank_eq_card_basis (hL.complexBasis (Module.finBasis ℝ L)), Fintype.card_fin]

/-- A complex-linear endomorphism `f` preserving a maximal totally real subspace `L` is the
complexification of its restriction to `L`, so its determinant is the (real) determinant of that
restriction. -/
theorem det_eq_det_restrict (f : E →ₗ[ℂ] E) (hf : ∀ x ∈ L, f x ∈ L) :
    LinearMap.det f = ((LinearMap.det ((f.restrictScalars ℝ).restrict hf) : ℝ) : ℂ) := by
  classical
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  let b := Module.finBasis ℝ L
  rw [← LinearMap.det_toMatrix (hL.complexBasis b), ← LinearMap.det_toMatrix b]
  refine ((Complex.ofRealHom.map_det _).trans (congrArg Matrix.det ?_)).symm
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, complexBasis_apply]
  exact (hL.complexBasis_repr_coe b ((f.restrictScalars ℝ).restrict hf (b j)) i).symm

/-- The complex-linear automorphisms act transitively on the maximal totally real subspaces of a
finite-dimensional complex module. -/
theorem exists_linearEquiv_map_eq {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') :
    ∃ A : E ≃ₗ[ℂ] E, L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ) = L' := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have hspan {K : Submodule ℝ E} (c : Basis (Fin (finrank ℂ E)) ℝ K) :
      Submodule.span ℝ (Set.range (K.subtype ∘ c)) = K := by
    rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
  let b := Module.finBasisOfFinrankEq ℝ L hL.finrank_eq_finrank_complex
  let b' := Module.finBasisOfFinrankEq ℝ L' hL'.finrank_eq_finrank_complex
  obtain ⟨A, hA⟩ : ∃ A : E ≃ₗ[ℂ] E, ∀ i, A (b i) = b' i :=
    ⟨(hL.complexBasis b).equiv (hL'.complexBasis b') (Equiv.refl _), fun i => by
      simpa using (hL.complexBasis b).equiv_apply i (hL'.complexBasis b') (Equiv.refl _)⟩
  refine ⟨A, ?_⟩
  rw [← hspan b, Submodule.map_span, ← Set.range_comp, ← hspan b']
  congr 2
  funext i
  exact hA i

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
theorem maslovPhase_map (A : E ≃ₗ[ℂ] E) :
    hL.maslovPhase (hL.map_linearEquiv A) =
      LinearMap.det (A : E →ₗ[ℂ] E) / conj (LinearMap.det (A : E →ₗ[ℂ] E)) := by
  unfold maslovPhase
  exact hL.det_div_conj_eq_of_map_eq (hL.exists_linearEquiv_map_eq
    (hL.map_linearEquiv A)).choose_spec

/-- A maximal totally real subspace has Maslov phase one relative to itself. -/
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
