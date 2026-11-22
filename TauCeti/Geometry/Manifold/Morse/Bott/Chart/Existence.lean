/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Bott.Lemma

/-!
# Existence of Morse–Bott charts

Every point of a Morse–Bott critical submanifold of a smooth function has a Morse–Bott chart
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.nonempty_morseBottChart`): it is the
normalized Morse–Bott lemma
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_normalized_morseBott_chart`,
read as a single chart of the maximal atlas of `M`, with its normal coordinates rescaled by `√2`.
So every critical point of a Morse–Bott function has one
(`TauCeti.IsMorseBottFamily.nonempty_morseBottChart`).

## Main declarations

* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.nonempty_morseBottChart`: every point
  of a Morse–Bott critical submanifold of a smooth function has a Morse–Bott chart.
* `TauCeti.IsMorseBottFamily.nonempty_morseBottChart`: every critical point of a Morse–Bott
  function has a Morse–Bott chart.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

/-! ### Existence on Morse–Bott critical submanifolds -/

section Existence

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {i : SmoothEmbedding J 𝓘(ℝ, E) ∞ S M}

/-- Coordinates `(b, y)` on `E' × ℝᵐ` in which `Σⱼ ±yⱼ²` is a diagonal quadratic form with
weights `0` on the base and `±1` on the fibre: a basis of `E'` on the base and `√2 y` on the fibre,
indexed by `Fin N` for any `N = dim E' + m`. -/
private theorem exists_linearEquiv_weight [FiniteDimensional ℝ E'] {m N : ℕ}
    (hN : N = Module.finrank ℝ E' + m) (ind : ℕ) :
    ∃ (T : (E' × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (Fin N → ℝ)) (w : Fin N → ℝ),
      (∀ j, w j = -1 ∨ w j = 0 ∨ w j = 1) ∧ ∀ v, (2 : ℝ)⁻¹ * ∑ j, w j * T v j ^ 2 =
        ∑ k, (if k.val < ind then -1 else 1) * v.2 k ^ 2 := by
  set d := Module.finrank ℝ E'
  let eN : Fin N ≃ Fin d ⊕ Fin m := (finCongr hN).trans finSumFinEquiv.symm
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  let T : (E' × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (Fin N → ℝ) :=
    (((Module.finBasis ℝ E').equivFun.prodCongr ((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).trans
      (LinearEquiv.smulOfNeZero ℝ _ _ hsqrt))).trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin m) ℝ ℝ).symm).trans
      (LinearEquiv.funCongrLeft ℝ ℝ eN)
  have hT (v : E' × EuclideanSpace ℝ (Fin m)) (j : Fin N) :
      T v j = Sum.elim ((Module.finBasis ℝ E').equivFun v.1)
        (fun k ↦ Real.sqrt 2 * v.2 k) (eN j) := by
    rcases hj : eN j with k | k <;>
      simp [T, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, hj]
  let sg : Fin m → ℝ := fun k ↦ if k.val < ind then -1 else 1
  let w : Fin N → ℝ := fun j ↦ Sum.elim (fun _ ↦ 0) sg (eN j)
  have hsum (u : Fin d → ℝ) (v : Fin m → ℝ) :
      ∑ j, w j * Sum.elim u v (eN j) ^ 2 = ∑ k, sg k * v k ^ 2 := by
    rw [eN.sum_comp (fun k ↦ Sum.elim (fun _ ↦ (0 : ℝ)) sg k * Sum.elim u v k ^ 2),
      Fintype.sum_sum_type]
    simp
  refine ⟨T, w, fun j ↦ ?_, fun v ↦ ?_⟩
  · simp only [w, sg]
    rcases eN j with k | k
    · simp
    · simp only [Sum.elim_inr]
      split_ifs <;> simp
  · simp only [hT, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    ring

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-- **The Morse–Bott lemma as a chart of the maximal atlas.** Every point `i s` of a Morse–Bott
critical submanifold of a function `f`, smooth near `i s`, has a Morse–Bott chart: a chart of the
maximal atlas of `M`, centred at `i s`, in which `f y = f (i s) + (1/2) Σⱼ wⱼ (L (ψ y))ⱼ²` with
weights `wⱼ ∈ {-1, 0, 1}`. -/
theorem nonempty_morseBottChart (hi : i.IsNondegenerateCriticalSubmanifold f) (s : S)
    (hf : ∀ᶠ y in 𝓝 (i s), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y) :
    Nonempty (MorseBottChart E f (i s)) := by
  -- Slice charts of `i` at `s`, with complement `F`.
  let F := i.isImmersion.complement
  have h : Manifold.IsImmersionAtOfComplement F J 𝓘(ℝ, E) ∞ i s :=
    i.isImmersion.isImmersionOfComplement_complement s
  set φ := h.domChart.extend J with hφ
  set c := h.codChart with hc
  set L := h.equiv with hL
  set a := φ s with ha
  obtain ⟨ψ, U, V, -, -, haU, h0V, hsource, -, hUVξ, hsec, -, hψ0, -, hψ, hψinv, hψg⟩ :=
    hi.exists_normalized_morseBott_chart h (k := ⊤) (by simp) (by simp)
      (hf.mono fun y hy ↦ hy.of_le (by simp))
  have : FiniteDimensional ℝ (E' × F) := L.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_surjective (LinearMap.fst ℝ E' F) LinearMap.fst_surjective
  have : FiniteDimensional ℝ F :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' F) LinearMap.snd_surjective
  -- The extended chart of the model `𝓘(ℝ, E)` is the chart itself.
  have hξs : ∀ w, (c.extend 𝓘(ℝ, E)).symm w = c.symm w := fun w ↦ by simp
  have hξt : (c.extend 𝓘(ℝ, E)).target = c.target := by simp
  -- The centre `i s` has slice coordinates `(a, 0)`.
  have hsa : c.symm (L (a, 0)) = i s := by
    rw [← hξs, hsec a haU, ha, hφ, (h.domChart.extend J).left_inv
      (by simpa using h.mem_domChart_source)]
  have hUVc : U ×ˢ V ⊆ L ⁻¹' c.target := hξt ▸ hUVξ
  have hca : c (i s) = L (a, 0) := by
    rw [← hsa, c.right_inv (hUVc (mk_mem_prod haU h0V))]
  -- The final linear coordinates `T`, with their weights `w`.
  have hN : Module.finrank ℝ E = Module.finrank ℝ E' + Module.finrank ℝ F := by
    rw [← L.toLinearEquiv.finrank_eq, Module.finrank_prod]
  obtain ⟨T, w, hw, hTw⟩ := exists_linearEquiv_weight hN (manifoldMorseIndex 𝓘(ℝ, E) f (i s))
  -- The chart: slice coordinates, then `ψ`, then the translation of `(a, 0)` to `0` and the
  -- coordinates `T`, read back in `E` through a basis of `E`.
  let B := (Module.finBasis ℝ E).equivFun
  let K : (E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) ≃L[ℝ] E :=
    (T.trans B.symm).toContinuousLinearEquiv
  have hBK (v : E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) : B (K v) = T v := by simp [K]
  obtain ⟨Φ, hΦ, hΦsrc, hΦmem⟩ := exists_trans_mem_maximalAtlas_of_contDiffOn
    h.codChart_mem_maximalAtlas L ψ hψ hψinv K
    ((a, 0) : E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))
  refine ⟨⟨c.trans Φ, hΦmem, ?_, ?_, B, w, hw, fun y hy ↦ ?_⟩⟩
  · -- The chart is defined at `i s`.
    refine ⟨h.mem_codChart_source, ?_⟩
    rw [mem_preimage, hΦsrc, mem_preimage, OpenPartialHomeomorph.symm_symm, hca,
      L.symm_apply_apply, hsource]
    exact mk_mem_prod haU h0V
  · -- It sends `i s` to `0`.
    rw [OpenPartialHomeomorph.coe_trans, comp_apply, hca, hΦ, L.symm_apply_apply, hψ0, sub_self,
      map_zero]
  · -- The normal form.
    rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage, hΦsrc,
      mem_preimage] at hy
    have hfy := hψg _ hy.2
    rw [comp_apply, comp_apply, ← hL, ← hc, hξs, L.apply_symm_apply, c.left_inv hy.1] at hfy
    rw [hfy, OpenPartialHomeomorph.coe_trans, comp_apply, hΦ, hBK, hTw, Prod.snd_sub,
      sub_zero]

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end Existence

section Family

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, (J a).Boundaryless] {S : ι → Type*} [∀ a, TopologicalSpace (S a)]
  [∀ a, ChartedSpace (H' a) (S a)] {i : ∀ a, SmoothEmbedding (J a) 𝓘(ℝ, E) ∞ (S a) M}

/-- **Every critical point of a Morse–Bott function has a Morse–Bott chart.** -/
theorem IsMorseBottFamily.nonempty_morseBottChart (h : IsMorseBottFamily i f)
    (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) : Nonempty (MorseBottChart E f x) := by
  obtain ⟨a, s, rfl⟩ := mem_iUnion.1 (h.criticalPoints_subset_iUnion_range hx)
  exact (h.isNondegenerateCriticalSubmanifold a).nonempty_morseBottChart s
    (.of_forall fun _ ↦ h.contMDiff.contMDiffAt)

end Family

end TauCeti
