/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Product-seminorm bounds for continuous multilinear maps

A continuous multilinear map on spaces with defining seminorm families is bounded, for each
continuous target seminorm, by a constant times a product of finite suprema of source seminorms.
This is the estimate needed to lift arbitrary continuous multilinear maps through the projective
tensor topology, rather than only maps supplied with an explicit bound. More generally, the bound
holds for a target seminorm `q` whenever `q ∘ f` is continuous at the origin.

The scaling argument reuses `MultilinearMap.bound_of_shell_of_norm_map_coord_zero` and the
seminorm-induced normed-space argument of `Seminorm.bound_of_continuous`. No separation or
completeness assumption is needed, and the main bound also covers maps of arity zero.
-/

public section

namespace TauCeti

open Function

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]

omit [Fintype ι] in
/-- If a multilinear map is bounded on a product of seminorm balls, its target seminorm
vanishes whenever one source seminorm vanishes. The source seminorms need not be norms. -/
theorem multilinearMap_seminorm_eq_zero_of_box [Finite ι]
    (p : ∀ i, Seminorm 𝕜 (E i)) (q : Seminorm 𝕜 F)
    (f : MultilinearMap (RingHom.id 𝕜) E F) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i)
    (hf : ∀ x, (∀ i, p i (x i) < ε i) → q (f x) ≤ 1)
    (x : ∀ i, E i) (i : ι) (hi : p i (x i) = 0) : q (f x) = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hscale (j) : ∃ a : 𝕜, a ≠ 0 ∧ p j (a • x j) < ε j := by
    by_cases hj : p j (x j) = 0
    · exact ⟨1, one_ne_zero, by simpa [hj] using hε j⟩
    · obtain ⟨a, ha, hlt, _, _⟩ := (p j).rescale_to_shell hc (hε j) hj
      exact ⟨a, ha, hlt⟩
  choose a ha hax using hscale
  -- Since `p i (x i) = 0`, the `i`-th scalar can be replaced by any `t`, so `q (f x)` is
  -- bounded by `1 / (‖t‖ * K)` for scalars `t` of arbitrarily large norm.
  set K := ‖∏ j ∈ Finset.univ \ {i}, a j‖
  have hK : 0 < K := norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  have hbound (t : 𝕜) : ‖t‖ * (K * q (f x)) ≤ 1 := by
    have := hf (fun j => update a i t j • x j) fun j => by
      rcases eq_or_ne j i with rfl | hji
      · simpa [map_smul_eq_mul, hi] using hε j
      · simpa [hji] using hax j
    simpa only [f.map_smul_univ, map_smul_eq_mul, RingHom.id_apply,
      Finset.prod_update_of_mem (Finset.mem_univ i), norm_mul, mul_assoc] using this
  by_contra hne
  have hpos : 0 < K * q (f x) := mul_pos hK ((apply_nonneg q _).lt_of_ne' hne)
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm 𝕜 (K * q (f x))⁻¹
  exact (hbound t).not_gt ((inv_lt_iff_one_lt_mul₀ hpos).mp ht)

/-- Boundedness on a product of seminorm balls gives a global product-seminorm bound.
The constant is explicit after choosing any scalar whose norm exceeds one. -/
theorem multilinearMap_seminorm_le_of_box
    (p : ∀ i, Seminorm 𝕜 (E i)) (q : Seminorm 𝕜 F)
    (f : MultilinearMap (RingHom.id 𝕜) E F) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i)
    (hf : ∀ x, (∀ i, p i (x i) < ε i) → q (f x) ≤ 1)
    {c : 𝕜} (hc : 1 < ‖c‖) (x : ∀ i, E i) :
    q (f x) ≤ (∏ i, ‖c‖ / ε i) * ∏ i, p i (x i) := by
  let : ∀ i, SeminormedAddCommGroup (E i) := fun i =>
    (p i).toSeminormedAddCommGroup
  let : ∀ i, NormedSpace 𝕜 (E i) := fun i =>
    { norm_smul_le := fun a b => (map_smul_eq_mul (p i) a b).le }
  let : SeminormedAddCommGroup F := q.toSeminormedAddCommGroup
  let : NormedSpace 𝕜 F :=
    { norm_smul_le := fun a b => (map_smul_eq_mul q a b).le }
  refine f.bound_of_shell_of_norm_map_coord_zero
    (fun {m i} hi => multilinearMap_seminorm_eq_zero_of_box p q f hε hf m i hi)
    hε (fun _ => hc) (fun m hm hm' => (hf m hm').trans ?_) x
  rw [← Finset.prod_mul_distrib]
  calc
    1 = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∏ i, (‖c‖ / ε i) * p i (m i) := by
      apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
      intro i _
      rw [div_mul_eq_mul_div, le_div_iff₀ (hε i), one_mul, mul_comm]
      exact (div_le_iff₀ (lt_trans zero_lt_one hc)).mp (hm i)

/-- A multilinear map `f` on spaces with defining seminorm families admits a product bound for a
target seminorm `q`, using finitely many of the defining source seminorms in each variable, as soon
as `q ∘ f` is continuous at the origin. This holds in particular when `f` is continuous and `q` is a
continuous seminorm. -/
theorem exists_multilinearMap_seminorm_bound
    {σ : ι → Type*} (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i))
    [∀ i, TopologicalSpace (E i)] (hp : ∀ i, WithSeminorms (p i))
    (q : Seminorm 𝕜 F) (f : MultilinearMap (RingHom.id 𝕜) E F)
    (hf : ContinuousAt (fun x => q (f x)) 0) :
    ∃ (s : ∀ i, Finset (σ i)) (C : NNReal),
      ∀ x, q (f x) ≤ (C : ℝ) * ∏ i, (s i).sup (p i) (x i) := by
  classical
  cases isEmpty_or_nonempty ι
  · exact ⟨fun _ => ∅, (q (f 0)).toNNReal, fun x => by simp [Subsingleton.elim x 0]⟩
  have hball : {x | q (f x) < 1} ∈ nhds (0 : ∀ i, E i) :=
    hf.preimage_mem_nhds (Iio_mem_nhds (by simp))
  rw [nhds_pi] at hball
  obtain ⟨I, _, U, hU, hsub⟩ := Filter.mem_pi.mp hball
  choose s ε hε hs using fun i => (hp i).mem_nhds_iff 0 (U i) |>.mp (hU i)
  have hbox : ∀ x, (∀ i, (s i).sup (p i) (x i) < ε i) → q (f x) ≤ 1 := by
    intro x hx
    exact (hsub (fun i _ => hs i (by simpa using hx i))).le
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  refine ⟨s, ⟨∏ i, ‖c‖ / ε i,
    Finset.prod_nonneg (fun i _ => div_nonneg (norm_nonneg c) (hε i).le)⟩, ?_⟩
  exact multilinearMap_seminorm_le_of_box (fun i => (s i).sup (p i)) q f hε hbox hc

/-- A continuous bilinear map on spaces with defining seminorm families is bounded, for each
continuous target seminorm, by a constant times a finite supremum of source seminorms in each
variable. This is the two-variable case of `exists_multilinearMap_seminorm_bound`, for variables
in two different spaces. -/
theorem exists_bilinearMap_seminorm_bound {E₁ E₂ σ₁ σ₂ : Type*} [AddCommGroup E₁] [Module 𝕜 E₁]
    [AddCommGroup E₂] [Module 𝕜 E₂] (p₁ : SeminormFamily 𝕜 E₁ σ₁) (p₂ : SeminormFamily 𝕜 E₂ σ₂)
    [TopologicalSpace E₁] [TopologicalSpace E₂] (hp₁ : WithSeminorms p₁) (hp₂ : WithSeminorms p₂)
    [TopologicalSpace F] (q : Seminorm 𝕜 F) (hq : Continuous q) (B : E₁ →ₗ[𝕜] E₂ →ₗ[𝕜] F)
    (hB : Continuous fun x : E₁ × E₂ ↦ B x.1 x.2) :
    ∃ (s₁ : Finset σ₁) (s₂ : Finset σ₂) (C : NNReal),
      ∀ x y, q (B x y) ≤ C * s₁.sup p₁ x * s₂.sup p₂ y := by
  have hball : {x : E₁ × E₂ | q (B x.1 x.2) < 1} ∈ nhds ((0 : E₁), (0 : E₂)) :=
    (hq.comp hB).continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp))
  rw [nhds_prod_eq] at hball
  obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := Filter.mem_prod_iff.mp hball
  obtain ⟨s₁, ε₁, hε₁, hs₁⟩ := (hp₁.mem_nhds_iff 0 U₁).mp hU₁
  obtain ⟨s₂, ε₂, hε₂, hs₂⟩ := (hp₂.mem_nhds_iff 0 U₂).mp hU₂
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  -- `B` as a multilinear map of two variables in `E₁ × E₂`, through the two projections.
  let f : MultilinearMap (RingHom.id 𝕜) (fun _ : Fin 2 ↦ E₁ × E₂) F :=
    { toFun v := B (v 0).1 (v 1).2
      map_update_add' v i x y := by
        fin_cases i <;> simp
      map_update_smul' v i a x := by
        fin_cases i <;> simp }
  let p : Fin 2 → Seminorm 𝕜 (E₁ × E₂) :=
    ![(s₁.sup p₁).comp (LinearMap.fst 𝕜 E₁ E₂), (s₂.sup p₂).comp (LinearMap.snd 𝕜 E₁ E₂)]
  let ε : Fin 2 → ℝ := ![ε₁, ε₂]
  have hε (i : Fin 2) : 0 < ε i := by
    fin_cases i
    exacts [hε₁, hε₂]
  have hbox (v : Fin 2 → E₁ × E₂) (hv : ∀ i, p i (v i) < ε i) : q (f v) ≤ 1 :=
    (hU (a := ((v 0).1, (v 1).2))
      ⟨hs₁ (by simpa [p, ε] using hv 0), hs₂ (by simpa [p, ε] using hv 1)⟩).le
  refine ⟨s₁, s₂, ⟨∏ i, ‖c‖ / ε i, Finset.prod_nonneg fun i _ ↦ (div_pos
    (zero_lt_one.trans hc) (hε i)).le⟩, fun x y ↦ ?_⟩
  calc q (B x y) = q (f ![(x, 0), (0, y)]) := by simp [f]
    _ ≤ (∏ i, ‖c‖ / ε i) * ∏ i, p i (![(x, 0), (0, y)] i) :=
      multilinearMap_seminorm_le_of_box p q f hε hbox hc _
    _ = (∏ i, ‖c‖ / ε i) * (s₁.sup p₁ x * s₂.sup p₂ y) := by simp [p, Fin.prod_univ_two]
    _ = _ := (mul_assoc _ _ _).symm

end TauCeti
