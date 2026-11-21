/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Tactic.Module

/-!
# The conjugate graph of a real-linear map

For a real-linear automorphism `K` and a real-linear operator `Ψ` of a complex normed space `E`,
the **conjugate graph** `conjGraph K Ψ = {(K z, Ψ z) | z ∈ E}` is a real subspace of `E × E`
(`TauCeti.conjGraph`). When `K` is a conjugation, a real-linear automorphism anticommuting with
`i`, the map `(u, w) ↦ (K u, w)` is complex linear from `(E, -i) × (E, i)` to `E × E`, and the
conjugate graph is the image of the graph of `Ψ` in `(E, -i) × (E, i)`.

For such `K`:

* the conjugate graph of the identity is maximal totally real
  (`TauCeti.isMaximalTotallyReal_conjGraph_id`);
* the conjugate graph of `Ψ` is the conjugate graph of the identity moved by the map
  `(u, w) ↦ (u, Q u + P w)`, with `P` the complex-linear part of `Ψ` and `Q` that of `Ψ ∘ K⁻¹`
  (`TauCeti.conjGraph_eq_map`).

These are used in `TauCeti.LinearAlgebra.TotallyReal.Maslov.Symplectic` to read the graph of a
linear symplectic map as a maximal totally real subspace.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (graphs of linear symplectic maps).
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **conjugate graph** `{(K z, Ψ z) | z ∈ E}` of a real-linear operator `Ψ` of a complex
normed space, for a real-linear automorphism `K`. When `K` is a conjugation, this is the graph of
`Ψ` in `(E, -i) × (E, i)`, read in `E × E` through `K` on the first factor. -/
def conjGraph (K : E ≃L[ℝ] E) (Ψ : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((K : E →ₗ[ℝ] E).prod (Ψ : E →ₗ[ℝ] E))

@[simp]
theorem mem_conjGraph {K : E ≃L[ℝ] E} {Ψ : E →L[ℝ] E} {x : E × E} :
    x ∈ conjGraph K Ψ ↔ ∃ z, (K z, Ψ z) = x := by
  simp [conjGraph]

variable {K : E ≃L[ℝ] E}

/-- **The conjugate graph of the identity is maximal totally real.** For an automorphism `K`
anticommuting with `i`, the subspace `{(K z, z)}` of `E × E` is complementary to its image under
multiplication by `i`. -/
theorem isMaximalTotallyReal_conjGraph_id (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E) Complex.I).restrictScalars ℝ)
      (conjGraph K (ContinuousLinearMap.id ℝ E)) := by
  rw [isMaximalTotallyReal_iff]
  constructor
  · -- `(K z, z) = i (K w, w)` forces `K w = -K w`, so `w = 0`.
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨z, rfl⟩ := mem_conjGraph.1 hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    obtain ⟨w, rfl⟩ := mem_conjGraph.1 hy
    simp only [ContinuousLinearMap.coe_id', id_eq, LinearMap.coe_restrictScalars,
      LinearMap.lsmul_apply, Prod.smul_mk, Prod.mk.injEq] at hyx
    obtain ⟨h₁, rfl⟩ := hyx
    rw [hK] at h₁
    have hKw : K w = 0 := by
      have h₂ : (2 : ℂ) • (Complex.I • K w) = 0 := by
        rw [two_smul]
        nth_rw 1 [h₁]
        exact neg_add_cancel _
      simpa using h₂
    have hw0 : w = 0 := K.injective (by simpa using hKw)
    simp [hw0]
  · -- `(u, w)` is `(K a, a) + i (K b, b)` with `a = (w + K⁻¹ u) / 2`, `i b = (w - K⁻¹ u) / 2`.
    rw [codisjoint_iff, eq_top_iff]
    rintro ⟨u, w⟩ -
    have hII (v : E) : Complex.I • Complex.I • v = -v := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    set a : E := (2⁻¹ : ℝ) • (w + K.symm u)
    set b : E := -(Complex.I • ((2⁻¹ : ℝ) • (w - K.symm u)))
    refine Submodule.mem_sup.2 ⟨(K a, a), ⟨a, rfl⟩, Complex.I • (K b, b),
      ⟨(K b, b), ⟨b, rfl⟩, rfl⟩, ?_⟩
    have ha : K a = (2⁻¹ : ℝ) • (K w + u) := by
      simp only [a, map_smul, map_add, K.apply_symm_apply]
    have hb : K b = (2⁻¹ : ℝ) • (Complex.I • (K w - u)) := by
      simp only [b, map_neg, hK, neg_neg, map_smul, map_sub, K.apply_symm_apply]
      rw [smul_comm]
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, ha, hb]
    constructor
    · rw [smul_comm Complex.I (2⁻¹ : ℝ), hII]
      module
    · simp only [a, b, smul_neg, smul_comm Complex.I (2⁻¹ : ℝ), hII]
      module

/-- The conjugate graph of `Ψ` is the conjugate graph of the identity moved by the real-linear map
`(u, w) ↦ (u, Q u + P w)`, where `P` is the complex-linear part of `Ψ` and `Q` that of `Ψ ∘ K⁻¹`. -/
theorem conjGraph_eq_map (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    (Ψ : E →L[ℝ] E) :
    conjGraph K Ψ = (conjGraph K (ContinuousLinearMap.id ℝ E)).map
      ((LinearMap.fst ℝ E E).prod
        (((Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart.restrictScalars ℝ :
            E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E E +
          ((Ψ.complexLinearPart.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.snd ℝ E E)) := by
  -- `Q (K z) + P z = Ψ z`.
  have key (z : E) : (Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart (K z) +
      Ψ.complexLinearPart z = Ψ z := by
    simp only [ContinuousLinearMap.complexLinearPart_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, Function.comp_apply, K.symm_apply_apply]
    -- `K⁻¹` also anticommutes with `i`.
    have hKs := (isComplexAntilinear_of_apply
      (J := (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      (J' := (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      (F := (K.toLinearEquiv : E →ₗ[ℝ] E)) hK).symm.apply (K z)
    simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv, K.symm_apply_apply] at hKs
    rw [hKs, map_neg]
    module
  have hmap (z : E) : ((LinearMap.fst ℝ E E).prod
      (((Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart.restrictScalars ℝ :
          E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E E +
        ((Ψ.complexLinearPart.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
          LinearMap.snd ℝ E E)) (K z, z) = (K z, Ψ z) :=
    Prod.ext rfl (key z)
  ext x
  rw [mem_conjGraph, Submodule.mem_map]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(K z, z), mem_conjGraph.2 ⟨z, by simp⟩, hmap z⟩
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_conjGraph.1 hy
    exact ⟨z, by simpa using (hmap z).symm⟩

end TauCeti
