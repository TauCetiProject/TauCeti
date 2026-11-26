/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Bases

/-!
# Pairwise distance, countability, and elementary constructions for orthonormal families

Two distinct vectors of an orthonormal family in an inner product space sit at squared distance `2`,
hence at distance `√2` (`Orthonormal.norm_sub_sq`, `Orthonormal.norm_sub_eq_sqrt_two`,
`Orthonormal.dist_eq_sqrt_two`). Consequently the open balls of radius `√2 / 2` around the members
of an orthonormal family are pairwise disjoint, so in a separable inner product space every
orthonormal family is countable (`Orthonormal.countable_of_separableSpace`).

Independently of separability, Bessel's inequality `Orthonormal.inner_products_summable` implies
that any vector pairs nontrivially with at most countably many members of an orthonormal family
(`Orthonormal.countable_support_inner_left`, `Orthonormal.countable_support_inner_right`). Together,
these two countability properties characterize separability of inner product spaces carrying a
Hilbert basis and bound basis-overlap supports in arbitrary Hilbert spaces to prove invariance of
Hilbert-basis cardinality.

The file also records elementary constructions: nonemptiness of `{f : ι → E | Orthonormal 𝕜 f}`
in finite dimension (`TauCeti.nonempty_setOfPred_orthonormal_iff`), extracting orthonormal pairs
(`Orthonormal.pair`), normalized orthogonal sums from a real orthonormal four-tuple
(`Orthonormal.inv_sqrt_two_add_pair`), and orthonormal bases from orthonormal families of `dim E`
vectors (`Orthonormal.exists_orthonormalBasis_coe_eq`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §4.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.3.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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

variable {𝕜 : Type*} {E : Type*} {ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] {v : ι → E}

/-- Two distinct vectors of an orthonormal family have `‖v i - v j‖ ^ 2 = 2`. -/
theorem norm_sub_sq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ ^ 2 = 2 := by
  rw [@_root_.norm_sub_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
  norm_num

/-- Two distinct vectors of an orthonormal family satisfy `‖v i - v j‖ = √2`. -/
theorem norm_sub_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = √2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), hv.norm_sub_sq hij]

/-- Two distinct vectors of an orthonormal family sit at distance `√2`. -/
theorem dist_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = √2 := by
  rw [dist_eq_norm, hv.norm_sub_eq_sqrt_two hij]

/-- **Countable Fourier support.** Every vector has nonzero inner product with at most countably
many members of an orthonormal family. -/
theorem countable_support_inner_left (hv : Orthonormal 𝕜 v) (x : E) :
    (Function.support fun i ↦ ⟪v i, x⟫_𝕜).Countable := by
  refine (hv.inner_products_summable x).countable_support.mono fun i hi ↦ ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)

/-- Right-hand inner-product form of `Orthonormal.countable_support_inner_left`. -/
theorem countable_support_inner_right (hv : Orthonormal 𝕜 v) (x : E) :
    (Function.support fun i ↦ ⟪x, v i⟫_𝕜).Countable := by
  refine (hv.countable_support_inner_left x).mono fun i (hi : ⟪x, v i⟫_𝕜 ≠ 0) ↦ ?_
  intro (h0 : ⟪v i, x⟫_𝕜 = 0)
  apply hi
  rw [← inner_conj_symm, h0, map_zero]

/-- Every orthonormal family in a separable inner product space is countable. -/
theorem countable_of_separableSpace (hv : Orthonormal 𝕜 v)
    [TopologicalSpace.SeparableSpace E] : Countable ι := by
  have hr : 0 < √2 / 2 := by positivity
  have hd : Pairwise (Function.onFun Disjoint fun i ↦ Metric.ball (v i) (√2 / 2)) := fun i j hij ↦
    Metric.ball_disjoint_ball (by rw [add_halves, hv.dist_eq_sqrt_two hij])
  exact hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨v i, Metric.mem_ball_self hr⟩)

/-- Two distinct entries of an orthonormal family form an orthonormal pair. -/
theorem pair {f : ι → E} (hf : Orthonormal 𝕜 f) {i j : ι} (hij : i ≠ j) :
    Orthonormal 𝕜 ![f i, f j] := by
  simp [hf.norm_eq_one i, hf.norm_eq_one j, hf.inner_eq_zero hij]

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

/-- In a finite-dimensional inner product space, an orthonormal family with as many vectors as the
dimension is an orthonormal basis. -/
theorem exists_orthonormalBasis_coe_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [Fintype ι] (card_ι : Module.finrank 𝕜 F = Fintype.card ι)
    {b : ι → F} (hb : Orthonormal 𝕜 b) : ∃ w : OrthonormalBasis ι 𝕜 F, ⇑w = b := by
  obtain ⟨w, hw⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (s := Set.univ)
    card_ι (hb.comp _ Subtype.val_injective)
  exact ⟨w, funext fun i ↦ hw i (Set.mem_univ i)⟩

end Orthonormal
