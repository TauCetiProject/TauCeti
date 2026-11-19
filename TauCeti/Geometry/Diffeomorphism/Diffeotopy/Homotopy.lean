/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Homotopies of diffeotopies fixing both time ends

Two diffeotopies `Φ` and `Ψ` of a manifold `M` are **homotopic**
(`TauCeti.Diffeotopy.Homotopic`) when a `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins their
motions `(x, t) ↦ φ_t x` and `(x, t) ↦ ψ_t x` while fixing both time ends: `G ((x, 0), s) = x` and
`G ((x, 1), s) = φ₁ x` for every `s`. These are the hypotheses of the homotopy invariance of the
flux, `TauCeti.Diffeotopy.flux_eq_of_homotopy`. The intermediate maps `G (·, s)` need not be
diffeotopies.

Homotopic diffeotopies have the same final diffeomorphism. Homotopy is an equivalence relation
for `n ≤ ∞` (`TauCeti.Diffeotopy.homotopic_equivalence`): transitivity glues two homotopies along
a smooth transition in the homotopy parameter, constant near the joining time. It is compatible
with the pointwise operations, the composite `TauCeti.Diffeotopy.trans` with slices `ψ_t ∘ φ_t`
(`TauCeti.Diffeotopy.Homotopic.trans_congr`) and the inverse `TauCeti.Diffeotopy.symm` with slices
`φ_t⁻¹` (`TauCeti.Diffeotopy.Homotopic.symm_congr`). Compatibility with the inverse cannot invert
the maps of the homotopy, which need not be diffeomorphisms; it follows from compatibility with
the composite, since `Φ.symm` is an inverse of `Φ` for the composite.

## Main definitions

* `TauCeti.Diffeotopy.Homotopic`: homotopy of diffeotopies fixing both time ends.

## Main results

* `TauCeti.Diffeotopy.Homotopic.final_eq`: homotopic diffeotopies have the same final
  diffeomorphism.
* `TauCeti.Diffeotopy.homotopic_equivalence`: homotopy is an equivalence relation.
* `TauCeti.Diffeotopy.Homotopic.trans_congr`, `Homotopic.symm_congr`: homotopy is compatible with
  the pointwise composite and inverse.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2, for homotopy classes of symplectic isotopies with fixed
  end points.
-/

public section

noncomputable section

namespace TauCeti

namespace Diffeotopy

open unitInterval Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {Φ Φ' Ψ Ψ' Θ : Diffeotopy J n M}

/-- Two diffeotopies are **homotopic** when a `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins the
motion `(x, t) ↦ φ_t x` of `Φ` at `s = 0` to the motion of `Ψ` at `s = 1` while fixing both time
ends: `G ((x, 0), s) = x` and `G ((x, 1), s) = φ₁ x` for every `s`. The maps `G (·, s)` need not be
diffeotopies. -/
def Homotopic (Φ Ψ : Diffeotopy J n M) : Prop :=
  ∃ G : (M × I) × I → M, ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G ∧
    (∀ p, G (p, 0) = Φ.cylinderMap p) ∧ (∀ p, G (p, 1) = Ψ.cylinderMap p) ∧
    (∀ x s, G ((x, 0), s) = x) ∧ ∀ x s, G ((x, 1), s) = Φ.final x

/-- Unfold the homotopy relation: a `C^n` map joining the two motions and fixing both time ends. -/
theorem homotopic_iff : Φ.Homotopic Ψ ↔
    ∃ G : (M × I) × I → M, ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G ∧
      (∀ p, G (p, 0) = Φ.cylinderMap p) ∧ (∀ p, G (p, 1) = Ψ.cylinderMap p) ∧
      (∀ x s, G ((x, 0), s) = x) ∧ ∀ x s, G ((x, 1), s) = Φ.final x :=
  Iff.rfl

/-- Homotopic diffeotopies have the same final diffeomorphism. -/
theorem Homotopic.final_eq (h : Φ.Homotopic Ψ) : Φ.final = Ψ.final := by
  obtain ⟨G, -, -, hG₁, -, h₁⟩ := h
  exact (Φ.final_eq_of_homotopy hG₁ h₁).symm

variable (Φ) in
/-- Every diffeotopy is homotopic to itself, through the constant homotopy. -/
@[refl]
theorem Homotopic.refl : Φ.Homotopic Φ :=
  ⟨fun q ↦ Φ.cylinderMap q.1, Φ.contMDiff_cylinderMap.comp contMDiff_fst, fun _ ↦ rfl,
    fun _ ↦ rfl, fun x _ ↦ by dsimp only; rw [cylinderMap_apply, apply_zero],
    fun x _ ↦ by dsimp only; rw [cylinderMap_apply, final_apply]⟩

/-- Homotopy of diffeotopies is symmetric: run the homotopy backwards. -/
@[symm]
theorem Homotopic.symm (h : Φ.Homotopic Ψ) : Ψ.Homotopic Φ := by
  have hfinal := h.final_eq
  obtain ⟨G, hG, hG₀, hG₁, h₀, h₁⟩ := h
  refine ⟨fun q ↦ G (q.1, σ q.2), hG.comp (contMDiff_fst.prodMk
    (contMDiff_symm.comp contMDiff_snd)), fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ h₀ x _,
    fun x s ↦ by dsimp only; rw [h₁, hfinal]⟩
  · dsimp only
    rw [symm_zero, hG₁]
  · dsimp only
    rw [symm_one, hG₀]

/-- Glue two homotopies, running through the first for `s ≤ 1 / 2` and through the second for
`1 / 2 < s`, each reparametrized by a smooth transition to be stationary for `s` near `1 / 2`. -/
private def glue (G G' : (M × I) × I → M) (q : (M × I) × I) : M :=
  if (q.2 : ℝ) ≤ 1 / 2 then G (q.1, collaredSmoothTransitionUnit (2 * q.2))
  else G' (q.1, collaredSmoothTransitionUnit (2 * q.2 - 1))

/-- Gluing two `C^n` maps which agree at the joining time gives a `C^n` map: near `s = 1 / 2` both
pieces are stationary at that common value. -/
private theorem contMDiff_glue {G G' : (M × I) × I → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G)
    (hG' : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G') (hGG' : ∀ p, G (p, 1) = G' (p, 0))
    (hn : n ≤ ∞) : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n (glue G G') := by
  classical
  have hcoe : Continuous fun s : I ↦ (s : ℝ) := continuous_subtype_val
  have hfirst : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n fun s : I ↦ collaredSmoothTransitionUnit (2 * s) :=
    (contMDiff_collaredSmoothTransitionUnit hn).comp
      ((contDiff_const.mul contDiff_id).contMDiff.comp
        (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))
  have hsecond : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n fun s : I ↦ collaredSmoothTransitionUnit (2 * s - 1) :=
    (contMDiff_collaredSmoothTransitionUnit hn).comp
      (((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))
  have hpw : glue G G' = Set.piecewise {q : (M × I) × I | (q.2 : ℝ) ≤ 1 / 2}
      (fun q ↦ G (q.1, collaredSmoothTransitionUnit (2 * q.2)))
      (fun q ↦ G' (q.1, collaredSmoothTransitionUnit (2 * q.2 - 1))) := by
    funext q
    by_cases hq : (q.2 : ℝ) ≤ 1 / 2
    · rw [Set.piecewise_eq_of_mem _ _ _ (by exact hq)]
      simp only [glue, hq, ↓reduceIte]
    · rw [Set.piecewise_eq_of_notMem _ _ _ (by exact hq)]
      simp only [glue, hq, ↓reduceIte]
  rw [hpw]
  refine (hG.comp (contMDiff_fst.prodMk (hfirst.comp contMDiff_snd))).piecewise
    (hG'.comp (contMDiff_fst.prodMk (hsecond.comp contMDiff_snd))) fun q hq ↦ ?_
  have hq' : (q.2 : ℝ) = 1 / 2 :=
    frontier_le_subset_eq (hcoe.comp continuous_snd) continuous_const hq
  have hnear : {r : (M × I) × I | 3 / 8 < (r.2 : ℝ) ∧ (r.2 : ℝ) < 5 / 8} ∈ 𝓝 q :=
    (isOpen_Ioo.preimage (hcoe.comp continuous_snd)).mem_nhds
      (by simp only [mem_preimage, mem_Ioo, Function.comp_apply, hq']; norm_num)
  filter_upwards [hnear] with r hr
  simp only [Function.comp_apply]
  rw [collaredSmoothTransitionUnit_eq_one_of_ge (by linarith [hr.1]),
    collaredSmoothTransitionUnit_eq_zero_of_le (by linarith [hr.2]), hGG']

/-- **Homotopy of diffeotopies is transitive**, at finite regularity and at `C^∞`. -/
@[trans]
theorem Homotopic.trans (h : Φ.Homotopic Ψ) (h' : Ψ.Homotopic Θ) (hn : n ≤ ∞) :
    Φ.Homotopic Θ := by
  have hfinal := h.final_eq
  obtain ⟨G, hG, hG₀, hG₁, h₀, h₁⟩ := h
  obtain ⟨G', hG', hG'₀, hG'₁, h'₀, h'₁⟩ := h'
  refine ⟨glue G G', contMDiff_glue hG hG' (fun p ↦ (hG₁ p).trans (hG'₀ p).symm) hn,
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_⟩
  · have h0 : ((0 : I) : ℝ) ≤ 1 / 2 := by norm_num [Set.Icc.coe_zero]
    simp only [glue, h0, ↓reduceIte]
    rw [Set.Icc.coe_zero, mul_zero,
      collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num), hG₀]
  · have h1 : ¬((1 : I) : ℝ) ≤ 1 / 2 := by norm_num [Set.Icc.coe_one]
    simp only [glue, h1, ↓reduceIte]
    rw [Set.Icc.coe_one,
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num), hG'₁]
  · rw [glue]
    split_ifs
    exacts [h₀ x _, h'₀ x _]
  · rw [glue]
    split_ifs
    exacts [h₁ x _, by rw [h'₁, hfinal]]

/-- Homotopy of diffeotopies is an equivalence relation, at finite regularity and at `C^∞`. -/
theorem homotopic_equivalence (hn : n ≤ ∞) :
    Equivalence (Homotopic (J := J) (n := n) (M := M)) :=
  ⟨Homotopic.refl, Homotopic.symm, fun h h' ↦ h.trans h' hn⟩

/-- **Homotopy is compatible with the pointwise composite.** If `Φ` is homotopic to `Φ'` and `Ψ` to
`Ψ'`, then `ψ_t ∘ φ_t` is homotopic to `ψ'_t ∘ φ'_t`: feed the first homotopy into the second. -/
theorem Homotopic.trans_congr (h : Φ.Homotopic Φ') (h' : Ψ.Homotopic Ψ') :
    (Φ.trans Ψ).Homotopic (Φ'.trans Ψ') := by
  obtain ⟨G, hG, hG₀, hG₁, h₀, h₁⟩ := h
  obtain ⟨G', hG', hG'₀, hG'₁, h'₀, h'₁⟩ := h'
  refine ⟨fun q ↦ G' ((G q, q.1.2), q.2),
    hG'.comp ((hG.prodMk (contMDiff_snd.comp contMDiff_fst)).prodMk contMDiff_snd),
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ by dsimp only; rw [h₀, h'₀], fun x s ↦ ?_⟩
  · dsimp only
    rw [hG₀, hG'₀, cylinderMap_trans, Function.comp_apply]
  · dsimp only
    rw [hG₁, hG'₁, cylinderMap_trans, Function.comp_apply]
  · dsimp only
    rw [h₁, h'₁, final_trans, _root_.Diffeomorph.coe_trans, Function.comp_apply]

/-- **Homotopy is compatible with the pointwise inverse.** If `Φ` is homotopic to `Φ'`, then
`φ_t⁻¹` is homotopic to `φ'_t⁻¹`. -/
theorem Homotopic.symm_congr (h : Φ.Homotopic Φ') :
    Φ.symm.Homotopic Φ'.symm := by
  -- `φ_t⁻¹ = (φ_t⁻¹ ∘ φ'_t) ∘ φ'_t⁻¹`, and `φ_t⁻¹ ∘ φ'_t` is homotopic to `φ_t⁻¹ ∘ φ_t = id`.
  have hloop : (Φ'.trans Φ.symm).Homotopic (Diffeotopy.refl J n M) := by
    rw [← Φ.self_trans_symm]
    exact h.symm.trans_congr (Homotopic.refl _)
  have key := (Homotopic.refl Φ'.symm).trans_congr hloop
  rwa [← trans_assoc, symm_trans_self, refl_trans, trans_refl] at key

end Diffeotopy

end TauCeti
