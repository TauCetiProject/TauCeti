/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
import TauCeti.Geometry.RealAlgebraic.CAD.Existence

/-!
# Composition of Nash germs

A map `g : (σ → ℝ) → (τ → ℝ)` between finite-dimensional coordinate spaces is regarded as a Nash
map germ at `x` when each of its coordinates `fun y ↦ g y i` is a Nash germ at `x`
(`TauCeti.IsNashAt`). This file deduces from the map form of the local Nash graph criterion
(`TauCeti.forall_isNashAt_apply_iff_exists_isSemialgebraicOn`) that Nash germs compose.

The proof of composition goes through semialgebraic graphs rather than through polynomial
relations. Nash coordinates of `g` have semialgebraic graphs on one open semialgebraic
neighbourhood `U` of `x`, and a Nash germ `f` at `g x` has semialgebraic graph on an open
semialgebraic neighbourhood `V` of `g x`. By the Tarski–Seidenberg theorem the part of `U` mapped
into `V` is semialgebraic and `f ∘ g` has semialgebraic graph there; it is a neighbourhood of `x`
because `g` is continuous at `x`. Since `f ∘ g` is analytic at `x`, the graph criterion makes it a
Nash germ.

## Main results

* `TauCeti.IsNashAt.comp`: if `f` is a Nash germ at `g x` and the coordinates of `g` are Nash germs
  at `x`, then `f ∘ g` is a Nash germ at `x`.
* `LinearMap.isNashAt_apply`, `ContinuousLinearMap.isNashAt_apply`: every coordinate of a linear
  (or continuous linear) map on a finite-dimensional real coordinate space is a Nash germ.
* `TauCeti.IsNashAt.comp_linearMap`, `TauCeti.IsNashAt.comp_continuousLinearMap`,
  `TauCeti.isNashAt_comp_linearEquiv_iff`, `TauCeti.isNashAt_comp_continuousLinearEquiv_iff`:
  closure of Nash germs under precomposition with linear maps and linear equivalences.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter Set Topology

/-- Every coordinate of a linear map from a finite-dimensional real coordinate space is a Nash
germ. -/
theorem LinearMap.isNashAt_apply {σ τ : Type*} [Fintype σ]
    (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (j : τ) {x : σ → ℝ} :
    TauCeti.IsNashAt (fun y ↦ L y j) x := by
  classical
  have hlin : (fun y ↦ L y j) = ∑ i : σ, fun y ↦ y i * L (Pi.single i 1) j := by
    ext y
    conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [L.map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hlin]
  exact Finset.univ.isNashAt_sum fun i _ ↦
    (TauCeti.isNashAt_apply i).fun_mul (TauCeti.isNashAt_const _)

/-- Every coordinate of a continuous linear map from a finite-dimensional real coordinate space is
a Nash germ. -/
theorem ContinuousLinearMap.isNashAt_apply {σ τ : Type*} [Fintype σ]
    (L : (σ → ℝ) →L[ℝ] (τ → ℝ)) (j : τ) {x : σ → ℝ} :
    TauCeti.IsNashAt (fun y ↦ L y j) x :=
  L.toLinearMap.isNashAt_apply j

namespace TauCeti

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {g : (σ → ℝ) → (τ → ℝ)} {x : σ → ℝ}

/-- **Composition of Nash germs.** If `f` is a Nash germ at `g x` and every coordinate of `g` is a
Nash germ at `x`, then `f ∘ g` is a Nash germ at `x`. -/
theorem IsNashAt.comp {f : (τ → ℝ) → ℝ} (hf : IsNashAt f (g x))
    (hg : ∀ i, IsNashAt (fun y ↦ g y i) x) : IsNashAt (f ∘ g) x := by
  obtain ⟨hga, U, hUo, hxU, hgU⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hg
  obtain ⟨hfa, V, hVo, hgxV, hV, hfV⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  have hW : IsSemialgebraic (U ∩ g ⁻¹' V) := hgU.isSemialgebraic_inter_preimage hV
  refine (hfV.comp (hgU.mono hW inter_subset_left) fun y hy ↦ hy.2).isNashAt
    (hfa.comp hga) ?_
  exact inter_mem (hUo.mem_nhds hxU) (hga.continuousAt.preimage_mem_nhds (hVo.mem_nhds hgxV))

/-- Precomposing a Nash germ with a linear map yields a Nash germ. -/
theorem IsNashAt.comp_linearMap {f : (τ → ℝ) → ℝ} {x : σ → ℝ}
    (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (hf : IsNashAt f (L x)) : IsNashAt (f ∘ L) x :=
  hf.comp fun j ↦ L.isNashAt_apply j

/-- Precomposing a Nash germ with a continuous linear map yields a Nash germ. -/
theorem IsNashAt.comp_continuousLinearMap {f : (τ → ℝ) → ℝ} {x : σ → ℝ}
    (L : (σ → ℝ) →L[ℝ] (τ → ℝ)) (hf : IsNashAt f (L x)) : IsNashAt (f ∘ L) x :=
  hf.comp_linearMap L.toLinearMap

/-- Precomposing with a linear equivalence preserves Nash germs in both directions. -/
@[simp]
theorem isNashAt_comp_linearEquiv_iff {f : (τ → ℝ) → ℝ} {x : σ → ℝ}
    (L : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) : IsNashAt (f ∘ L) x ↔ IsNashAt f (L x) :=
  ⟨fun h ↦ by
    have hx : L.symm.toLinearMap (L x) = x := L.symm_apply_apply x
    have hcomp : (f ∘ L) ∘ L.symm.toLinearMap = f := by ext y; simp
    rw [← hcomp]
    exact (hx ▸ h).comp_linearMap L.symm.toLinearMap,
    fun h ↦ h.comp_linearMap L.toLinearMap⟩

/-- Precomposing with a continuous linear equivalence preserves Nash germs in both directions. -/
@[simp]
theorem isNashAt_comp_continuousLinearEquiv_iff {f : (τ → ℝ) → ℝ} {x : σ → ℝ}
    (L : (σ → ℝ) ≃L[ℝ] (τ → ℝ)) : IsNashAt (f ∘ L) x ↔ IsNashAt f (L x) :=
  isNashAt_comp_linearEquiv_iff L.toLinearEquiv

end TauCeti
