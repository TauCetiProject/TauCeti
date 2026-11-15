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

For an inner product space `E` over `𝕜` (`ℝ` or `ℂ`) and any index type `ι`, the set
`{f : ι → E | Orthonormal 𝕜 f}` is closed in the product topology because each unit-norm condition
`‖f i‖ = 1` and pairwise orthogonality condition `⟪f i, f j⟫ = 0` (`i ≠ j`) is cut out by
continuous maps. When `E` is finite-dimensional, every factor lies in the compact closed unit ball,
so Tychonoff makes `{f : ι → E | Orthonormal 𝕜 f}` compact; for finite `ι` it is nonempty if and
only if `Fintype.card ι ≤ Module.finrank 𝕜 E`.

We also record finite-tuple helpers for orthonormal frames: extracting an orthonormal pair
`![f i, f j]` (`i ≠ j`), extending an orthonormal pair `![u, v]` in dimension at least four to an
orthonormal four-frame `f` with `f 0 = u` and `f 2 = v`, and forming the normalized sum pair
`![(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)]` from an orthonormal four-tuple `![x₁, x₂, y₁, y₂]`.

## Main statements

* `TauCeti.isClosed_setOfPred_orthonormal`, `TauCeti.isCompact_setOfPred_orthonormal`,
  `TauCeti.nonempty_setOfPred_orthonormal_iff`: closedness, finite-dimensional compactness, and
  dimension criterion for `{f : ι → E | Orthonormal 𝕜 f}`.
* `Orthonormal.pair`: `![f i, f j]` is orthonormal for `i ≠ j`.
* `Orthonormal.exists_fin_four_extension`: in dimension at least four, every orthonormal pair
  `![u, v]` extends to an orthonormal four-frame `f` with `f 0 = u` and `f 2 = v`.
* `Orthonormal.inv_sqrt_two_add_pair`: for an orthonormal four-tuple `![x₁, x₂, y₁, y₂]`, the pair
  `![(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)]` is orthonormal.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapters 1–5, Springer (1987), Chapter V, §2.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VII.
-/

public section

open Set
open scoped InnerProductSpace

namespace TauCeti

section RCLike

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The set of orthonormal `ι`-tuples in an inner product space is closed in the product
topology. -/
theorem isClosed_setOfPred_orthonormal : IsClosed {f : ι → E | Orthonormal 𝕜 f} := by
  have heq : {f : ι → E | Orthonormal 𝕜 f} = (⋂ i : ι, {f : ι → E | ‖f i‖ = 1}) ∩
      (⋂ (i : ι) (j : ι) (_ : i ≠ j), {f : ι → E | ⟪f i, f j⟫_𝕜 = 0}) := by
    ext f; simp only [mem_ofPred_eq, Orthonormal, mem_inter_iff, mem_iInter]; rfl
  rw [heq]
  exact (isClosed_iInter fun i ↦ isClosed_eq (continuous_norm.comp (continuous_apply i))
    continuous_const).inter (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_eq (Continuous.inner (continuous_apply i) (continuous_apply j)) continuous_const)

/-- On a finite-dimensional inner product space, the set of orthonormal `ι`-tuples is compact in the
product topology. -/
theorem isCompact_setOfPred_orthonormal [FiniteDimensional 𝕜 E] :
    IsCompact {f : ι → E | Orthonormal 𝕜 f} := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  refine (isCompact_univ_pi fun _ : ι ↦ isCompact_closedBall (0 : E) 1).of_isClosed_subset
    isClosed_setOfPred_orthonormal fun f hf i _ ↦ ?_
  simp [(hf.1 i).le]

/-- On a finite-dimensional inner product space, an orthonormal `ι`-tuple exists if and only if
`Fintype.card ι ≤ Module.finrank 𝕜 E`. -/
theorem nonempty_setOfPred_orthonormal_iff [Fintype ι] [FiniteDimensional 𝕜 E] :
    {f : ι → E | Orthonormal 𝕜 f}.Nonempty ↔ Fintype.card ι ≤ Module.finrank 𝕜 E := by
  refine ⟨fun ⟨f, hf⟩ ↦ hf.linearIndependent.fintype_card_le_finrank, fun h ↦ ?_⟩
  let emb : ι ↪ Fin (Module.finrank 𝕜 E) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb h)
  exact ⟨fun i ↦ stdOrthonormalBasis 𝕜 E (emb i),
    (stdOrthonormalBasis 𝕜 E).orthonormal.comp emb emb.injective⟩

end RCLike

end TauCeti

namespace Orthonormal

section RCLike

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two distinct entries of an orthonormal family form an orthonormal pair. -/
theorem pair {f : ι → E} (hf : Orthonormal 𝕜 f) {i j : ι} (hij : i ≠ j) :
    Orthonormal 𝕜 ![f i, f j] := by
  simp [hf.1 i, hf.1 j, hf.2 hij]

/-- In dimension at least four, every orthonormal pair `![u, v]` extends to an orthonormal
four-frame `f` with `f 0 = u` and `f 2 = v`. -/
theorem exists_fin_four_extension {u v : E} (huv : Orthonormal 𝕜 ![u, v])
    (hn : 4 ≤ Module.finrank 𝕜 E) :
    ∃ f : Fin 4 → E, Orthonormal 𝕜 f ∧ f 0 = u ∧ f 2 = v := by
  classical
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have huv0 : ⟪u, v⟫_𝕜 = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  obtain ⟨w₁, hw₁_norm, hw₁_orth⟩ :=
    TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
      (𝕜 := 𝕜) ({u, v} : Finset E) (Finset.card_le_two.trans_lt (by omega))
  have huw₁ : ⟪u, w₁⟫_𝕜 = 0 := hw₁_orth u (by simp)
  have hw₁v : ⟪w₁, v⟫_𝕜 = 0 := inner_eq_zero_symm.2 (hw₁_orth v (by simp))
  have hcard3 : ({u, v, w₁} : Finset E).card < Module.finrank 𝕜 E :=
    ((Finset.card_insert_le u {v, w₁}).trans (Nat.succ_le_succ Finset.card_le_two)).trans_lt
      (by omega)
  obtain ⟨w₂, hw₂_norm, hw₂_orth⟩ :=
    TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
      (𝕜 := 𝕜) ({u, v, w₁} : Finset E) hcard3
  have huw₂ : ⟪u, w₂⟫_𝕜 = 0 := hw₂_orth u (by simp)
  have hvw₂ : ⟪v, w₂⟫_𝕜 = 0 := hw₂_orth v (by simp)
  have hw₁w₂ : ⟪w₁, w₂⟫_𝕜 = 0 := hw₂_orth w₁ (by simp)
  refine ⟨![u, w₁, v, w₂], ?_, rfl, rfl⟩
  simp [Fin.forall_fin_succ, hu, hv, hw₁_norm, hw₂_norm, huv0, huw₁, hw₁v, huw₂, hvw₂, hw₁w₂]

end RCLike

/-- For an orthonormal four-tuple `![x₁, x₂, y₁, y₂]` in a real inner product space, the normalized
sums `(√2)⁻¹ • (x₁ + x₂)` and `(√2)⁻¹ • (y₁ + y₂)` form an orthonormal pair. -/
theorem inv_sqrt_two_add_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x₁ x₂ y₁ y₂ : V} (h : Orthonormal ℝ ![x₁, x₂, y₁, y₂]) :
    Orthonormal ℝ ![(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)] := by
  have hnorm {a b : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫_ℝ = 0) :
      ‖(√2)⁻¹ • (a + b)‖ = 1 := by
    have hsq : ‖a + b‖ ^ 2 = 2 := by rw [norm_add_sq_real, ha, hb, hab]; ring
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg 2)),
      ← Real.sqrt_sq (norm_nonneg (a + b)), hsq, inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 two_pos)]
  have hx : ‖(√2)⁻¹ • (x₁ + x₂)‖ = 1 :=
    hnorm (h.1 0) (h.1 1) (h.2 (by decide : (0 : Fin 4) ≠ 1))
  have hy : ‖(√2)⁻¹ • (y₁ + y₂)‖ = 1 :=
    hnorm (h.1 2) (h.1 3) (h.2 (by decide : (2 : Fin 4) ≠ 3))
  have h₁₁ : ⟪x₁, y₁⟫_ℝ = 0 := h.2 (by decide : (0 : Fin 4) ≠ 2)
  have h₁₂ : ⟪x₁, y₂⟫_ℝ = 0 := h.2 (by decide : (0 : Fin 4) ≠ 3)
  have h₂₁ : ⟪x₂, y₁⟫_ℝ = 0 := h.2 (by decide : (1 : Fin 4) ≠ 2)
  have h₂₂ : ⟪x₂, y₂⟫_ℝ = 0 := h.2 (by decide : (1 : Fin 4) ≠ 3)
  have hxy : ⟪(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)⟫_ℝ = 0 := by
    simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h₁₁, h₁₂, h₂₁, h₂₂]
  simp only [orthonormal_vecCons_iff, orthonormal_subsingleton_iff, Fin.forall_fin_one,
    Matrix.cons_val_zero, hx, hy, hxy, and_self]

end Orthonormal
