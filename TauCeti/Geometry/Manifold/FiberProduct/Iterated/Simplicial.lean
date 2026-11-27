/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Submersion
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Smooth simplicial structure of iterated submersion fibre products

When `π : Y → M` is a `C^n` submersion (`1 ≤ n`) between finite-dimensional boundaryless real
manifolds and each `IteratedFiberProduct π (m + 1)` carries
`TauCeti.iteratedFiberProductChartedSpace` (building on the manifold-free simplicial operations
`reindex`, `face`, `degeneracy`, and `cons` in
`TauCeti.Geometry.Manifold.FiberProduct.Iterated.Basic`):

* every reindexing map `reindex α` is `C^{m'}` (`m' ≤ n`), and a bijection `α : Fin k₁ ≃ Fin k₂`
  induces a `C^n` diffeomorphism (`TauCeti.iteratedFiberProductReindexDiffeomorph`);
* reindexing along any injective map `α : Fin (m₁ + 1) → Fin (m₂ + 1)` is a surjective `C^n`
  submersion (`TauCeti.isSubmersion_reindex_of_injective`); in particular, every face map `face i`
  is a surjective `C^n` submersion (`TauCeti.isSubmersion_face`,
  `TauCeti.IteratedFiberProduct.surjective_face`);
* reindexing along any surjective map is a `C^n` smooth embedding
  (`TauCeti.isSmoothEmbedding_reindex_of_surjective`); in particular, every degeneracy map
  `degeneracy i` is a `C^n` immersion and smooth embedding (`TauCeti.contMDiff_degeneracy`,
  `TauCeti.isImmersion_degeneracy`, `TauCeti.isSmoothEmbedding_degeneracy`);
* for a section `s` of `π`, prepending `s (baseProj y)` to `y` is `C^{m'}` at every `y` where `s`
  is `C^{m'}` at `baseProj y` (`TauCeti.contMDiffAt_cons_section`).

## References

* J.-L. Brylinski, *Loop Spaces, Characteristic Classes and Geometric Quantization*,
  Progress in Mathematics 107, Birkhäuser (1993), Chapter V (smooth Čech nerves of submersions).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) **54** (1996), 403–416.
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω}
  [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- Contravariant reindexing `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_reindex {m₁ m₂ : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n)
    (α : Fin (m₁ + 1) → Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    ContMDiff
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → IteratedFiberProduct π (m₁ + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m₂
  let := iteratedFiberProductChartedSpace hn hπ m₁
  refine (contMDiff_iteratedFiberProduct_iff hn hπ hm').2 fun i ↦ ?_
  simp only [IteratedFiberProduct.eval_reindex]
  exact contMDiff_eval hn hπ hm' (α i)

/-- Reindexing along an equivalence `α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)` induces a `C^n`
diffeomorphism `Y^[m₂ + 1] ≃ₘ^n Y^[m₁ + 1]`. In particular, permuting the factors of `Y^[k]` is a
`C^n` diffeomorphism. -/
noncomputable def iteratedFiberProductReindexDiffeomorph {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    IteratedFiberProduct π (m₂ + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π (m₁ + 1) := by
  letI := iteratedFiberProductChartedSpace hn hπ m₂
  letI := iteratedFiberProductChartedSpace hn hπ m₁
  exact
    { toFun := IteratedFiberProduct.reindex α
      invFun := IteratedFiberProduct.reindex α.symm
      left_inv := fun y ↦ IteratedFiberProduct.ext fun j ↦ by simp
      right_inv := fun x ↦ IteratedFiberProduct.ext fun i ↦ by simp
      contMDiff_toFun := contMDiff_reindex hn hπ le_rfl α
      contMDiff_invFun := contMDiff_reindex hn hπ le_rfl α.symm }

/-- `iteratedFiberProductReindexDiffeomorph` acts by `IteratedFiberProduct.reindex α`. -/
@[simp]
theorem iteratedFiberProductReindexDiffeomorph_apply {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) (y : IteratedFiberProduct π (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    iteratedFiberProductReindexDiffeomorph hn hπ α y = IteratedFiberProduct.reindex α y := (rfl)

/-- The inverse of `iteratedFiberProductReindexDiffeomorph` acts by
`IteratedFiberProduct.reindex α.symm`. -/
@[simp]
theorem iteratedFiberProductReindexDiffeomorph_symm_apply {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) (x : IteratedFiberProduct π (m₁ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    (iteratedFiberProductReindexDiffeomorph hn hπ α).symm x =
      IteratedFiberProduct.reindex α.symm x := (rfl)

/-- **Reindexing along an injective map is a submersion.** For any injective map
`α : Fin (m₁ + 1) → Fin (m₂ + 1)`, `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]` is a `C^n` submersion. -/
theorem isSubmersion_reindex_of_injective {m₁ m₂ : ℕ} {α : Fin (m₁ + 1) → Fin (m₂ + 1)}
    (hα : Injective α) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → IteratedFiberProduct π (m₁ + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m₂
  let := iteratedFiberProductChartedSpace hn hπ m₁
  have := isManifold_iteratedFiberProduct hn hπ m₂
  have := isManifold_iteratedFiberProduct hn hπ m₁
  let K₁ := 𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ)
  let PI₁ := ModelWithCorners.pi fun _ : Fin (m₁ + 1) ↦ IY
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_reindex hn hπ le_rfl α).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y η ↦ ?_).isSubmersion
  let x : IteratedFiberProduct π (m₁ + 1) := IteratedFiberProduct.reindex α y
  let u := mfderiv K₁ PI₁ Subtype.val x η
  have hu : ∀ i₁ i₂ : Fin (m₁ + 1),
      mfderiv IY IM π (y.val (α i₁)) (u i₁) =
        tangentSpaceCast IM (π (y.val (α i₂))) (π (y.val (α i₁)))
          (mfderiv IY IM π (y.val (α i₂)) (u i₂)) :=
    (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m₁ x u).1 ⟨η, rfl⟩
  let w₀ : TangentSpace IM (π (y.val (α 0))) := mfderiv IY IM π (y.val (α 0)) (u 0)
  have hsurj : ∀ j : Fin (m₂ + 1),
      ∃ v_j : TangentSpace IY (y.val j),
        (∀ i : Fin (m₁ + 1), α i = j →
          tangentSpaceCast IY (y.val j) (y.val (α i)) v_j = u i) ∧
        tangentSpaceCast IM (π (y.val j)) (π (y.val (α 0))) (mfderiv IY IM π (y.val j) v_j) = w₀
            := by
    intro j
    by_cases hj : ∃ i, α i = j
    · obtain ⟨i₀, rfl⟩ := hj
      refine ⟨u i₀, fun i hi ↦ ?_, (hu 0 i₀).symm⟩
      cases hα hi
      rfl
    · obtain ⟨v_j, hv_j⟩ :=
        ((tangentSpaceCast IM (π (y.val j)) (π (y.val (α 0)))).surjective.comp
          (hπ.surjective_mfderiv hn0 (y.val j))) w₀
      exact ⟨v_j, fun i hi ↦ (hj ⟨i, hi⟩).elim, hv_j⟩
  choose v hv_hit hv_map using hsurj
  have hcompat : ∀ j₁ j₂ : Fin (m₂ + 1),
      mfderiv IY IM π (y.val j₁) (v j₁) =
        tangentSpaceCast IM (π (y.val j₂)) (π (y.val j₁)) (mfderiv IY IM π (y.val j₂) (v j₂)) :=
    fun j₁ j₂ ↦
      (eq_tangentSpaceCast_iff_tangentSpaceCast_eq (y.property j₁ (α 0)) (y.property j₂ (α 0))).2
        ((hv_map j₁).trans (hv_map j₂).symm)
  have hemb₁ := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m₁
  have hemb₂ := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m₂
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m₂ y v).2 hcompat
  refine ⟨ξ, (hemb₁.isImmersion.isImmersionAt x).mfderiv_injective hn0 ?_⟩
  have hc_lhs := mfderiv_comp y ((hemb₁.contMDiff x).mdifferentiableAt hn0)
    (((contMDiff_reindex hn hπ le_rfl α) y).mdifferentiableAt hn0)
  rw [← ContinuousLinearMap.comp_apply, ← hc_lhs]
  funext i
  have hc₁ := mfderiv_comp y (TauCeti.hasMFDerivAt_apply i x.val).mdifferentiableAt
    (((hemb₁.contMDiff.comp (contMDiff_reindex hn hπ le_rfl α)) y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hc₁
  have hfn : ((fun f : Fin (m₁ + 1) → Y ↦ f i) ∘
      (Subtype.val ∘ IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → (Fin (m₁ + 1) → Y))) =
      (fun g : Fin (m₂ + 1) → Y ↦ g (α i)) ∘ Subtype.val := rfl
  have hc₂ := mfderiv_comp y (TauCeti.hasMFDerivAt_apply (α i) y.val).mdifferentiableAt
    ((hemb₂.contMDiff y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hc₂
  have hlhs := (DFunLike.congr_fun hc₁ ξ).symm
  rw [hfn, hc₂] at hlhs
  exact hlhs.trans ((congrFun hξ (α i)).trans (hv_hit (α i) i rfl))

/-- **Reindexing along a surjective map is a smooth embedding.** For any surjective map
`α : Fin (m₁ + 1) → Fin (m₂ + 1)`, `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]` is a `C^n` smooth
embedding. -/
theorem isSmoothEmbedding_reindex_of_surjective {m₁ m₂ : ℕ} {α : Fin (m₁ + 1) → Fin (m₂ + 1)}
    (hα : Surjective α) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → IteratedFiberProduct π (m₁ + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m₂
  let := iteratedFiberProductChartedSpace hn hπ m₁
  have := isManifold_iteratedFiberProduct hn hπ m₂
  have := isManifold_iteratedFiberProduct hn hπ m₁
  exact (contMDiff_reindex hn hπ le_rfl α).isSmoothEmbedding_of_leftInverse hn
    (contMDiff_reindex hn hπ hn (surjInv hα))
    (IteratedFiberProduct.leftInverse_reindex_surjInv hα)

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_face {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.face i :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  let := iteratedFiberProductChartedSpace hn hπ m
  exact contMDiff_reindex hn hπ hm' i.succAbove

/-- **Every face map is a surjective submersion.** On `IteratedFiberProduct π (m + 2)`, each face
map `face i : Y^[m + 2] → Y^[m + 1]` omitting the `i`-th factor is a `C^n` submersion. -/
theorem isSubmersion_face {m : ℕ} (i : Fin (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.face i :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  let := iteratedFiberProductChartedSpace hn hπ m
  exact isSubmersion_reindex_of_injective hn hπ Fin.succAbove_right_injective

/-- Every diagonal degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is `C^{m'}` for
`m' ≤ n`. -/
theorem contMDiff_degeneracy {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    ContMDiff
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  exact contMDiff_reindex hn hπ hm' i.predAbove

/-- For a section `s` of `π`, prepending `s (baseProj y)` to `y`, a map `Y^[m + 1] → Y^[m + 2]`,
is `C^{m'}` at `y` whenever `s` is `C^{m'}` at `baseProj y`. -/
theorem contMDiffAt_cons_section {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) {s : M → Y}
    (hs : ∀ x, π (s x) = x) {y : IteratedFiberProduct π (m + 1)}
    (hsy : ContMDiffAt IM IY m' s (IteratedFiberProduct.baseProj y)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    ContMDiffAt 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) m'
      (fun y ↦ IteratedFiberProduct.cons (s (IteratedFiberProduct.baseProj y)) y (hs _)) y := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  refine (contMDiffAt_iteratedFiberProduct_iff hn hπ hm').2 fun i ↦ ?_
  cases i using Fin.cases with
  | zero =>
    simp only [IteratedFiberProduct.eval_zero_cons]
    exact hsy.comp y (contMDiff_baseProj hn hπ hm' y)
  | succ j =>
    simp only [IteratedFiberProduct.eval_succ_cons]
    exact contMDiff_eval hn hπ hm' j y

/-- Every diagonal degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a `C^n` immersion,
split on the left by `face i.castSucc`. -/
theorem isImmersion_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    Manifold.IsImmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  exact (IteratedFiberProduct.degeneracy_eq_reindex i ▸
    isSmoothEmbedding_reindex_of_surjective hn hπ (Fin.predAbove_surjective i)).isImmersion

/-- **Every diagonal degeneracy map is a smooth embedding.** On `IteratedFiberProduct π (m + 1)`,
`degeneracy i : Y^[m + 1] → Y^[m + 2]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  exact IteratedFiberProduct.degeneracy_eq_reindex i ▸
    isSmoothEmbedding_reindex_of_surjective hn hπ (Fin.predAbove_surjective i)

end Manifold

end TauCeti
