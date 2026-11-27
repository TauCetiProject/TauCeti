/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RepresentationTheory.GKModule.Basic
public import TauCeti.RepresentationTheory.GL2.CompactCartan.Orthogonal
public import TauCeti.RepresentationTheory.GL2.CompactWeight.Module
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# The action of `O(2)` on the module of compact weights

The orthogonal group `O(2)` acts on `𝔤𝔩₂(ℂ)` by conjugation, `TauCeti.orthogonalAd`. A rotation
`g = !![a, -b; b, a]` has phase `z(g) = a - i b` (`TauCeti.orthogonalPhase`), of absolute value one,
and every reflection is a rotation followed by `A = diag(1, -1)`. This file makes
`TauCeti.CompactWeightModule k μ` a `(𝔤𝔩₂(ℂ), O(2))`-module: a rotation acts on the weight vector
`v_ℓ` by `z(g) ^ ℓ` and a reflection `g` by `v_ℓ ↦ z(g) ^ (-ℓ) v_{-ℓ}`, that is
`g • v_ℓ = z(g) ^ (ε ℓ) v_{ε ℓ}` with `ε = det g = ±1`. For the rotation `r_θ = exp(θJ)`,
`z(r_θ) = e^{iθ}`, so `r_θ` acts on `v_ℓ` by `e^{iℓθ}`, matching the derivative
`TauCeti.lie_gl2RotationGenerator_weightVector`; `A` acts by
`TauCeti.CompactWeightModule.reflection`. The action is covariant: conjugation by a rotation
multiplies the `X_c`- and `Y_c`-coordinates of a matrix by `z(g) ^ 2` and `z(g) ^ (-2)`
(`TauCeti.compactCoordX_orthogonalAd_of_det_eq_one`), and the reflection case follows from that of
`A` (`TauCeti.CompactWeightModule.reflection_lie`).

The Lie submodules `TauCeti.CompactWeightModule.weightLieSubmodule k μ S` with `-S = S` are
`O(2)`-stable, so they are `(𝔤𝔩₂(ℂ), O(2))`-modules; this applies to the discrete series
`D_k(μ)`, whose weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2` form a symmetric set.

## Main definitions

* `TauCeti.CompactWeightModule.orthogonalRep k μ`: the action of `O(2)` on the compact weights.
* `TauCeti.CompactWeightModule.gkModule k μ`: the `(𝔤𝔩₂(ℂ), O(2))`-module of all compact weights.
* `TauCeti.CompactWeightModule.weightGKSubmodule k μ S`: the `(𝔤𝔩₂(ℂ), O(2))`-submodule of the
  vectors supported on a symmetric set `S`.

## Main results

* `TauCeti.CompactWeightModule.orthogonalRep_weightVector`: `g • v_ℓ = z(g) ^ (ε ℓ) v_{ε ℓ}`.
* `TauCeti.CompactWeightModule.aeval_orthogonalRep_eq_zero_iff`: if the roots of `q` among the
  `z(g) ^ ℓ` are those with `ℓ ∈ S`, then `q(g)` kills exactly the vectors supported on `S`.
* `TauCeti.CompactWeightModule.orthogonalRep_orthogonalDiagonalReflection`: `A` acts by the
  reflection `v_ℓ ↦ v_{-ℓ}`.
* `TauCeti.CompactWeightModule.orthogonalRep_lie`: covariance,
  `g • ⁅M, v⁆ = ⁅g M g⁻¹, g • v⁆`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
* W. Casselman, *Representations of SL₂(ℝ)*, lecture notes, §§2, 5–6, pp. 9–11, 17–20.
-/

public section

noncomputable section

open Complex Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### The action of `O(2)` on the compact weights -/

namespace CompactWeightModule

variable {k μ : ℂ}

/-- A linear map built on the weight basis sends `v_ℓ` to the prescribed vector. -/
private theorem constr_weightVector (f : ℤ → CompactWeightModule k μ) (ℓ : ℤ) :
    (weightBasis k μ).constr ℂ f (weightVector k μ ℓ) = f ℓ := by
  rw [← weightBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

variable (k μ) in
/-- **The action of `O(2)` on the compact weights**: `g ∈ O(2)` sends `v_ℓ` to
`z(g) ^ (ε ℓ) v_{ε ℓ}`, where `z(g)` is the phase and `ε = det g = ±1`. A rotation `r_θ` acts on
`v_ℓ` by `e^{iℓθ}`, and `A = diag(1, -1)` acts by the reflection `v_ℓ ↦ v_{-ℓ}`. -/
def orthogonalRep : Representation ℂ (orthogonalGroup (Fin 2) ℝ) (CompactWeightModule k μ) where
  toFun g := (weightBasis k μ).constr ℂ fun ℓ ↦
    (orthogonalPhase g ^ (orthogonalSign g * ℓ)) • weightVector k μ (orthogonalSign g * ℓ)
  map_one' := (weightBasis k μ).ext fun ℓ ↦ by
    simp [constr_weightVector]
  map_mul' g h := (weightBasis k μ).ext fun ℓ ↦ by
    simp [constr_weightVector, smul_smul, orthogonalSign_mul, orthogonalPhase_mul, mul_zpow,
      ← _root_.zpow_mul, mul_assoc]
    module

/-- `g ∈ O(2)` sends `v_ℓ` to `z(g) ^ (ε ℓ) v_{ε ℓ}`, `ε = det g`. -/
@[simp]
theorem orthogonalRep_weightVector (g : orthogonalGroup (Fin 2) ℝ) (ℓ : ℤ) :
    orthogonalRep k μ g (weightVector k μ ℓ) =
      (orthogonalPhase g ^ (orthogonalSign g * ℓ)) • weightVector k μ (orthogonalSign g * ℓ) :=
  constr_weightVector _ ℓ

/-- A rotation `g` is diagonal in the weight basis, with eigenvalue `z(g) ^ ℓ` at `v_ℓ`. -/
private theorem orthogonalRep_weightBasis_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (ℓ : ℤ) :
    orthogonalRep k μ g (weightBasis k μ ℓ) = orthogonalPhase g ^ ℓ • weightBasis k μ ℓ := by
  simp [orthogonalRep_weightVector, orthogonalSign_of_det_eq_one hg]

open Polynomial in
/-- **The kernel of a polynomial in a rotation**: if the roots of `q` among the powers
`z(g) ^ ℓ` are exactly those with `ℓ ∈ S`, then `q(g)` kills exactly the vectors supported on
`S`. -/
theorem aeval_orthogonalRep_eq_zero_iff {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) {q : ℂ[X]} {S : Set ℤ}
    (hq : ∀ ℓ : ℤ, q.eval (orthogonalPhase g ^ ℓ) = 0 ↔ ℓ ∈ S) (v : CompactWeightModule k μ) :
    aeval (orthogonalRep k μ g) q v = 0 ↔ equivFinsupp k μ v ∈ Finsupp.supported ℂ ℂ S := by
  rw [← weightBasis_repr]
  exact (weightBasis k μ).aeval_apply_eq_zero_iff_repr_mem_supported
    (orthogonalRep_weightBasis_of_det_eq_one hg) hq v

/-- **The reflection `A = diag(1, -1)` acts by `TauCeti.CompactWeightModule.reflection`**,
`v_ℓ ↦ v_{-ℓ}`. -/
theorem orthogonalRep_orthogonalDiagonalReflection :
    orthogonalRep k μ (orthogonalDiagonalReflection ℝ 1) = (reflection k μ).toLinearMap :=
  (weightBasis k μ).ext fun ℓ ↦ by simp

/-- Covariance for a rotation. -/
private theorem orthogonalRep_lie_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : CompactWeightModule k μ) :
    orthogonalRep k μ g ⁅M, v⁆ = ⁅orthogonalAd (Fin 2) g M, orthogonalRep k μ g v⁆ := by
  have hz := orthogonalPhase_ne_zero g
  have h : orthogonalRep k μ g ∘ₗ LieModule.toEnd ℂ _ _ M =
      LieModule.toEnd ℂ _ _ (orthogonalAd (Fin 2) g M) ∘ₗ orthogonalRep k μ g := by
    refine (weightBasis k μ).ext fun ℓ ↦ ?_
    simp only [weightBasis_apply, LinearMap.coe_comp, Function.comp_apply,
      LieModule.toEnd_apply_apply, lie_weightVector, map_add, map_smul,
      orthogonalRep_weightVector, smul_add, smul_smul, orthogonalSign_of_det_eq_one hg, one_mul,
      compactCoordH_orthogonalAd_of_det_eq_one hg, compactCoordX_orthogonalAd_of_det_eq_one hg,
      compactCoordY_orthogonalAd_of_det_eq_one hg, compactCoordOne_orthogonalAd_of_det_eq_one hg]
    rw [zpow_add₀ hz, zpow_sub₀ hz, zpow_two, div_eq_mul_inv]
    module
  simpa using congr($h v)

/-- **Covariance of the action of `O(2)`**: `g • ⁅M, v⁆ = ⁅g M g⁻¹, g • v⁆`. A reflection `g` is
the rotation `g A` followed by `A`, which acts by `TauCeti.CompactWeightModule.reflection`. -/
theorem orthogonalRep_lie (g : orthogonalGroup (Fin 2) ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : CompactWeightModule k μ) :
    orthogonalRep k μ g ⁅M, v⁆ = ⁅orthogonalAd (Fin 2) g M, orthogonalRep k μ g v⁆ := by
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · exact orthogonalRep_lie_of_det_eq_one hg M v
  obtain ⟨r, hr, rfl⟩ : ∃ r : orthogonalGroup (Fin 2) ℝ, (r : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∧
      g = r * orthogonalDiagonalReflection ℝ 1 := by
    refine ⟨g * orthogonalDiagonalReflection ℝ 1, ?_, by
      rw [mul_assoc, orthogonalDiagonalReflection_mul_self, mul_one]⟩
    rw [Submonoid.coe_mul, det_mul, hg, det_orthogonalDiagonalReflection, neg_one_mul, neg_neg]
  simp only [map_mul, mul_apply_eq_comp, orthogonalRep_orthogonalDiagonalReflection,
    LinearEquiv.coe_coe, reflection_lie, orthogonalRep_lie_of_det_eq_one hr,
    orthogonalAd_orthogonalDiagonalReflection]

variable (k μ) in
/-- **The `(𝔤𝔩₂(ℂ), O(2))`-module of all compact weights**: `TauCeti.CompactWeightModule k μ` with
the action `TauCeti.CompactWeightModule.orthogonalRep k μ` of `O(2)`, covariant for the
conjugation action `TauCeti.orthogonalAd`. Every vector is `O(2)`-finite: the orbit of `v_ℓ` lies
in the span of `v_ℓ` and `v_{-ℓ}`. -/
def gkModule : GKModule (orthogonalAd (Fin 2)) (CompactWeightModule k μ) where
  ρ := orthogonalRep k μ
  map_lie := orthogonalRep_lie
  isGFinite v := by
    have hfin : ∀ ℓ, (orthogonalRep k μ).IsGFinite (weightVector k μ ℓ) := fun ℓ ↦ by
      have := FiniteDimensional.span_of_finite ℂ
        (Set.toFinite {weightVector k μ ℓ, weightVector k μ (-ℓ)})
      refine Representation.IsGFinite.of_forall_apply_mem
        (W := Submodule.span ℂ {weightVector k μ ℓ, weightVector k μ (-ℓ)}) fun g ↦ ?_
      rw [orthogonalRep_weightVector]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rcases orthogonalSign_eq_one_or_neg_one g with h | h <;> simp [h]
    have htop : ⊤ ≤ (orthogonalRep k μ).gFiniteSubmodule := by
      rw [← (weightBasis k μ).span_eq, Submodule.span_le]
      rintro _ ⟨ℓ, rfl⟩
      exact (Representation.mem_gFiniteSubmodule _).2 (by simpa using hfin ℓ)
    exact (Representation.mem_gFiniteSubmodule _).1 (htop Submodule.mem_top)

/-- The action of `O(2)` in `TauCeti.CompactWeightModule.gkModule`. -/
@[simp]
theorem gkModule_ρ : (gkModule k μ).ρ = orthogonalRep k μ :=
  (rfl)

/-- `O(2)` preserves the vectors supported on a symmetric set of weights `S`, `-S = S`. -/
theorem equivFinsupp_orthogonalRep_mem_supported {S : Set ℤ} (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S)
    (g : orthogonalGroup (Fin 2) ℝ) {v : CompactWeightModule k μ}
    (hv : equivFinsupp k μ v ∈ Finsupp.supported ℂ ℂ S) :
    equivFinsupp k μ (orthogonalRep k μ g v) ∈ Finsupp.supported ℂ ℂ S := by
  have hc : ∀ ℓ ∈ S, orthogonalSign g * ℓ ∉ S → orthogonalPhase g ^ (orthogonalSign g * ℓ) = 0 :=
    fun ℓ hℓ hℓ' ↦ by
      rcases orthogonalSign_eq_one_or_neg_one g with h | h <;> simp only [h, one_mul,
        neg_one_mul] at hℓ'
      · exact absurd hℓ hℓ'
      · exact absurd ((hS ℓ).2 hℓ) hℓ'
  have key := Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ
    ((equivFinsupp k μ).toLinearMap ∘ₗ orthogonalRep k μ g ∘ₗ (equivFinsupp k μ).symm.toLinearMap)
    (fun ℓ ↦ orthogonalPhase g ^ (orthogonalSign g * ℓ)) (fun ℓ ↦ orthogonalSign g * ℓ)
    (fun ℓ ↦ by
      rw [← equivFinsupp_weightVector (k := k) (μ := μ),
        ← equivFinsupp_weightVector (k := k) (μ := μ)]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply, orthogonalRep_weightVector, map_smul]) hc hv
  simpa using key

variable (k μ) in
/-- The `(𝔤𝔩₂(ℂ), O(2))`-submodule of the vectors supported on a set of weights `S` with
`-S = S` that `X_c` and `Y_c` leave only with coefficient zero: the Lie submodule
`TauCeti.CompactWeightModule.weightLieSubmodule k μ S` is `O(2)`-stable. -/
def weightGKSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S) :
    GKSubmodule (gkModule k μ) where
  toLieSubmodule := weightLieSubmodule k μ S hX hY
  apply_mem g _ hv := mem_weightLieSubmodule.2
    (equivFinsupp_orthogonalRep_mem_supported hS g (mem_weightLieSubmodule.1 hv))

/-- The underlying Lie submodule of `TauCeti.CompactWeightModule.weightGKSubmodule`. -/
@[simp]
theorem toLieSubmodule_weightGKSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S) :
    (weightGKSubmodule k μ S hX hY hS).toLieSubmodule = weightLieSubmodule k μ S hX hY :=
  (rfl)

end CompactWeightModule

end TauCeti
