/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Elementary constructions for orthonormal families

Nonemptiness of `{f : ι → E | Orthonormal 𝕜 f}` in finite dimension
(`TauCeti.nonempty_setOfPred_orthonormal_iff`), extracting orthonormal pairs (`Orthonormal.pair`),
and normalized orthogonal sums from a real orthonormal four-tuple
(`Orthonormal.inv_sqrt_two_add_pair`).
-/

public section

open scoped InnerProductSpace

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TauCeti

/-- On a finite-dimensional inner product space, an orthonormal `ι`-tuple exists iff
`Fintype.card ι ≤ Module.finrank 𝕜 E`. -/
theorem nonempty_setOfPred_orthonormal_iff [Fintype ι] [FiniteDimensional 𝕜 E] :
    {f : ι → E | Orthonormal 𝕜 f}.Nonempty ↔ Fintype.card ι ≤ Module.finrank 𝕜 E := by
  refine ⟨fun ⟨f, hf⟩ ↦ hf.linearIndependent.fintype_card_le_finrank, fun h ↦ ?_⟩
  let emb : ι ↪ Fin (Module.finrank 𝕜 E) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb h)
  exact ⟨fun i ↦ stdOrthonormalBasis 𝕜 E (emb i),
    (stdOrthonormalBasis 𝕜 E).orthonormal.comp emb emb.injective⟩

end TauCeti

namespace Orthonormal

/-- Two distinct entries of an orthonormal family form an orthonormal pair. -/
theorem pair {f : ι → E} (hf : Orthonormal 𝕜 f) {i j : ι} (hij : i ≠ j) :
    Orthonormal 𝕜 ![f i, f j] := by simp [hf.1 i, hf.1 j, hf.2 hij]

/-- For an orthonormal four-tuple `![x₁, x₂, y₁, y₂]` in a real inner product space, the
normalized sums `(√2)⁻¹ • (x₁ + x₂)` and `(√2)⁻¹ • (y₁ + y₂)` form an orthonormal pair. -/
theorem inv_sqrt_two_add_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x₁ x₂ y₁ y₂ : V} (h : Orthonormal ℝ ![x₁, x₂, y₁, y₂]) :
    Orthonormal ℝ ![(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)] := by
  have hnorm {a b : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫_ℝ = 0) :
      ‖(√2)⁻¹ • (a + b)‖ = 1 := by
    have hsq : ‖a + b‖ ^ 2 = 2 := by rw [norm_add_sq_real, ha, hb, hab]; ring
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← Real.sqrt_sq (norm_nonneg _), hsq,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 two_pos)]
  simp only [orthonormal_vecCons_iff, orthonormal_subsingleton_iff, Fin.forall_fin_succ,
    Fin.forall_fin_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, and_true] at h
  rcases h with ⟨h1, ⟨h12, h13, h14⟩, h2, ⟨h23, h24⟩, h3, h34, h4⟩
  simp [-smul_add, hnorm h1 h2 h12, hnorm h3 h4 h34, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, h13, h14, h23, h24]

end Orthonormal
