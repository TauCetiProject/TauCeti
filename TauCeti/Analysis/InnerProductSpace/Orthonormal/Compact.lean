/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Topology, compactness, and finite-tuple constructions for orthonormal families

For an inner product space `E` over `𝕜`, `{f : ι → E | Orthonormal 𝕜 f}` is closed in the product
topology, compact when `E` is finite-dimensional, and nonempty for finite `ι` iff
`Fintype.card ι ≤ Module.finrank 𝕜 E`, along with finite-tuple extraction, extension, and
normalized-sum helpers.

## Main statements

* `TauCeti.isClosed_setOfPred_orthonormal`, `TauCeti.isCompact_setOfPred_orthonormal`,
  `TauCeti.nonempty_setOfPred_orthonormal_iff`, `Orthonormal.pair`,
  `Orthonormal.exists_fin_four_extension`, `Orthonormal.inv_sqrt_two_add_pair`.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapters 1–5, Springer (1987), Chapter V, §2.
-/

public section

open Set
open scoped InnerProductSpace

namespace TauCeti

section RCLike

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The set of orthonormal `ι`-tuples is closed in the product topology. -/
theorem isClosed_setOfPred_orthonormal : IsClosed {f : ι → E | Orthonormal 𝕜 f} := by
  have heq : {f : ι → E | Orthonormal 𝕜 f} = (⋂ i : ι, {f : ι → E | ‖f i‖ = 1}) ∩
      (⋂ (i : ι) (j : ι) (_ : i ≠ j), {f : ι → E | ⟪f i, f j⟫_𝕜 = 0}) := by
    ext f; simp only [mem_ofPred_eq, Orthonormal, mem_inter_iff, mem_iInter]; rfl
  rw [heq]
  exact (isClosed_iInter fun i ↦ isClosed_eq (continuous_norm.comp (continuous_apply i))
    continuous_const).inter (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_eq (Continuous.inner (continuous_apply i) (continuous_apply j)) continuous_const)

/-- On a finite-dimensional inner product space, the set of orthonormal `ι`-tuples is compact. -/
theorem isCompact_setOfPred_orthonormal [FiniteDimensional 𝕜 E] :
    IsCompact {f : ι → E | Orthonormal 𝕜 f} := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  exact (isCompact_univ_pi fun _ : ι ↦ isCompact_closedBall (0 : E) 1).of_isClosed_subset
    isClosed_setOfPred_orthonormal fun f hf i _ ↦ by simp [(hf.1 i).le]

/-- On a finite-dimensional inner product space, an orthonormal `ι`-tuple exists iff
`Fintype.card ι ≤ Module.finrank 𝕜 E`. -/
theorem nonempty_setOfPred_orthonormal_iff [Fintype ι] [FiniteDimensional 𝕜 E] :
    {f : ι → E | Orthonormal 𝕜 f}.Nonempty ↔ Fintype.card ι ≤ Module.finrank 𝕜 E := by
  refine ⟨fun ⟨f, hf⟩ ↦ hf.linearIndependent.fintype_card_le_finrank, fun h ↦ ?_⟩
  let emb : ι ↪ Fin (Module.finrank 𝕜 E) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb h)
  exact ⟨fun i ↦ stdOrthonormalBasis 𝕜 E (emb i),
    (stdOrthonormalBasis 𝕜 E).orthonormal.comp emb emb.injective⟩

end RCLike

end TauCeti

namespace Orthonormal

section RCLike

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two distinct entries of an orthonormal family form an orthonormal pair. -/
theorem pair {f : ι → E} (hf : Orthonormal 𝕜 f) {i j : ι} (hij : i ≠ j) :
    Orthonormal 𝕜 ![f i, f j] := by simp [hf.1 i, hf.1 j, hf.2 hij]

/-- In dimension at least four, every orthonormal pair `![u, v]` extends to an orthonormal
four-frame `f` with `f 0 = u` and `f 2 = v`. -/
theorem exists_fin_four_extension {u v : E} (huv : Orthonormal 𝕜 ![u, v])
    (hn : 4 ≤ Module.finrank 𝕜 E) :
    ∃ f : Fin 4 → E, Orthonormal 𝕜 f ∧ f 0 = u ∧ f 2 = v := by
  classical
  obtain ⟨w₁, hw₁, hw₁o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v} : Finset E) (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨w₂, hw₂, hw₂o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v, w₁} : Finset E)
    (((Finset.card_insert_le u {v, w₁}).trans (Nat.succ_le_succ Finset.card_le_two)).trans_lt
      (by omega))
  simp only [orthonormal_vecCons_iff, orthonormal_subsingleton_iff, Fin.forall_fin_one,
    Matrix.cons_val_zero] at huv
  refine ⟨![u, w₁, v, w₂], ?_, rfl, rfl⟩
  simp [Fin.forall_fin_succ, huv.1, huv.2.1, huv.2.2, hw₁, hw₂, hw₁o u (by simp),
    inner_eq_zero_symm.2 (hw₁o v (by simp)), hw₂o u (by simp), hw₂o v (by simp), hw₂o w₁ (by simp)]

end RCLike

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
  have hxy : ⟪(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)⟫_ℝ = 0 := by
    simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h13, h14, h23, h24]
  simp only [orthonormal_vecCons_iff, orthonormal_subsingleton_iff, Fin.forall_fin_one,
    Matrix.cons_val_zero, hnorm h1 h2 h12, hnorm h3 h4 h34, hxy, and_self]

end Orthonormal
