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
(`TauCeti.Diffeotopy.Homotopic`) when they are joined by a smooth family of diffeotopies fixing both
time ends. That is, a `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins their motions
`(x, t) ↦ φ_t x` and `(x, t) ↦ ψ_t x` while fixing both time ends, `G ((x, 0), s) = x` and
`G ((x, 1), s) = φ₁ x` for every `s`, and `G` has a `C^n` inverse `G'` in the space variable:
`G' ((G ((x, t), s), t), s) = x` and `G ((G' ((x, t), s), t), s) = x`. So
`(s, t, x) ↦ (s, t, G ((x, t), s))` is a `C^n` diffeomorphism, and every intermediate motion
`G (·, s)` is a diffeotopy. These are paths of diffeomorphisms modulo homotopy through such paths.
The conditions on `G` alone are the hypotheses of the homotopy invariance of the flux,
`TauCeti.Diffeotopy.flux_eq_of_homotopy`.

Homotopic diffeotopies have the same final diffeomorphism. Homotopy is an equivalence relation
for `n ≤ ∞` (`TauCeti.Diffeotopy.Homotopic.equivalence`): transitivity glues two homotopies along
a smooth transition in the homotopy parameter, constant near the joining time. It is compatible
with the pointwise operations, the composite `TauCeti.Diffeotopy.trans` with slices `ψ_t ∘ φ_t`
(`TauCeti.Diffeotopy.Homotopic.trans_congr`) and the inverse `TauCeti.Diffeotopy.symm` with slices
`φ_t⁻¹` (`TauCeti.Diffeotopy.Homotopic.symm_congr`). Compatibility with the inverse follows from
compatibility with the composite, since `Φ.symm` is an inverse of `Φ` for the composite. The
constant, reversed, glued and composed homotopies behind these laws are stated for explicit
witnesses (`TauCeti.Diffeotopy.IsHomotopy.refl`, `IsHomotopy.symm`, `IsHomotopy.trans`,
`IsHomotopy.trans_congr`), so that relations adding conditions on the witnesses can reuse them.

## Main definitions

* `TauCeti.Diffeotopy.IsHomotopy`: a homotopy fixing both time ends between two diffeotopies,
  together with its inverse in the space variable.
* `TauCeti.Diffeotopy.Homotopic`: homotopy of diffeotopies fixing both time ends.

## Main results

* `TauCeti.Diffeotopy.Homotopic.final_eq`: homotopic diffeotopies have the same final
  diffeomorphism.
* `TauCeti.Diffeotopy.Homotopic.equivalence`: homotopy is an equivalence relation.
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

open unitInterval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {Φ Φ' Ψ Ψ' Θ : Diffeotopy J n M}

/-- `G` is a **homotopy from `Φ` to `Ψ` fixing both time ends, with inverse `G'` in the space
variable**. That is, the `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins the motion
`(x, t) ↦ φ_t x` of `Φ` at `s = 0` to the motion of `Ψ` at `s = 1` while fixing both time ends,
`G ((x, 0), s) = x` and `G ((x, 1), s) = φ₁ x` for every `s`, and `G'` is a `C^n` inverse of `G` in
the space variable: `G' ((G ((x, t), s), t), s) = x` and `G ((G' ((x, t), s), t), s) = x`. -/
def IsHomotopy (Φ Ψ : Diffeotopy J n M) (G G' : (M × I) × I → M) : Prop :=
  ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G ∧
    (∀ p, G (p, 0) = Φ.cylinderMap p) ∧ (∀ p, G (p, 1) = Ψ.cylinderMap p) ∧
    (∀ x s, G ((x, 0), s) = x) ∧ (∀ x s, G ((x, 1), s) = Φ.final x) ∧
    ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G' ∧
    (∀ x t s, G' ((G ((x, t), s), t), s) = x) ∧ ∀ x t s, G ((G' ((x, t), s), t), s) = x

/-- Unfold the homotopy predicate: `G` is a `C^n` map joining the two motions and fixing both time
ends, and `G'` is a `C^n` inverse of `G` in the space variable. -/
theorem isHomotopy_iff {G G' : (M × I) × I → M} : IsHomotopy Φ Ψ G G' ↔
    ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G ∧
      (∀ p, G (p, 0) = Φ.cylinderMap p) ∧ (∀ p, G (p, 1) = Ψ.cylinderMap p) ∧
      (∀ x s, G ((x, 0), s) = x) ∧ (∀ x s, G ((x, 1), s) = Φ.final x) ∧
      ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G' ∧
      (∀ x t s, G' ((G ((x, t), s), t), s) = x) ∧ ∀ x t s, G ((G' ((x, t), s), t), s) = x :=
  Iff.rfl

/-- Two diffeotopies are **homotopic** when they are joined by a smooth family of diffeotopies
fixing both time ends. That is, a `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins the motion
`(x, t) ↦ φ_t x` of `Φ` at `s = 0` to the motion of `Ψ` at `s = 1` while fixing both time ends,
`G ((x, 0), s) = x` and `G ((x, 1), s) = φ₁ x` for every `s`, and `G` has a `C^n` inverse `G'` in
the space variable: `G' ((G ((x, t), s), t), s) = x` and `G ((G' ((x, t), s), t), s) = x`
(`TauCeti.Diffeotopy.IsHomotopy`). So every intermediate motion `G (·, s)` is a diffeotopy, with
inverse `G' (·, s)`. -/
def Homotopic (Φ Ψ : Diffeotopy J n M) : Prop :=
  ∃ G G' : (M × I) × I → M, IsHomotopy Φ Ψ G G'

/-- Unfold the homotopy relation: a `C^n` map joining the two motions and fixing both time ends,
with a `C^n` inverse in the space variable. -/
theorem homotopic_iff : Φ.Homotopic Ψ ↔
    ∃ G G' : (M × I) × I → M, ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G ∧
      (∀ p, G (p, 0) = Φ.cylinderMap p) ∧ (∀ p, G (p, 1) = Ψ.cylinderMap p) ∧
      (∀ x s, G ((x, 0), s) = x) ∧ (∀ x s, G ((x, 1), s) = Φ.final x) ∧
      ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J n G' ∧
      (∀ x t s, G' ((G ((x, t), s), t), s) = x) ∧ ∀ x t s, G ((G' ((x, t), s), t), s) = x :=
  Iff.rfl

namespace IsHomotopy

variable {G K G' K' : (M × I) × I → M}

/-- Diffeotopies joined by a homotopy fixing both time ends are homotopic. -/
theorem homotopic (h : IsHomotopy Φ Ψ G K) : Φ.Homotopic Ψ :=
  ⟨G, K, h⟩

/-- The two ends of a homotopy fixing both time ends have the same final diffeomorphism. -/
theorem final_eq (h : IsHomotopy Φ Ψ G K) : Φ.final = Ψ.final := by
  obtain ⟨-, -, hG₁, -, h₁, -⟩ := h
  exact (Φ.final_eq_of_homotopy hG₁ h₁).symm

variable (Φ) in
/-- The **constant homotopy** of a diffeotopy. -/
theorem refl :
    IsHomotopy Φ Φ (fun q ↦ Φ.cylinderMap q.1) (fun q ↦ Φ.symm.cylinderMap q.1) :=
  ⟨Φ.contMDiff_cylinderMap.comp contMDiff_fst, fun _ ↦ rfl,
    fun _ ↦ rfl, fun x _ ↦ by dsimp only; rw [cylinderMap_apply, apply_zero],
    fun x _ ↦ by dsimp only; rw [cylinderMap_apply, final_apply],
    Φ.symm.contMDiff_cylinderMap.comp contMDiff_fst,
    fun x t _ ↦ by dsimp only; rw [cylinderMap_apply, cylinderMap_apply, symm_apply_apply_mk],
    fun x t _ ↦ by dsimp only; rw [cylinderMap_apply, cylinderMap_apply, apply_symm_apply_mk]⟩

/-- The **reversed homotopy**: run a homotopy backwards in the homotopy parameter. -/
theorem symm (h : IsHomotopy Φ Ψ G K) :
    IsHomotopy Ψ Φ (fun q ↦ G (q.1, σ q.2)) (fun q ↦ K (q.1, σ q.2)) := by
  have hfinal := h.final_eq
  obtain ⟨hG, hG₀, hG₁, h₀, h₁, hK, hl, hr⟩ := h
  have hσ : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) n
      fun q : (M × I) × I ↦ (q.1, σ q.2) :=
    contMDiff_fst.prodMk (contMDiff_symm.comp contMDiff_snd)
  refine ⟨hG.comp hσ, fun p ↦ ?_, fun p ↦ ?_,
    fun x s ↦ h₀ x _, fun x s ↦ by dsimp only; rw [h₁, hfinal], hK.comp hσ,
    fun x t s ↦ hl x t _, fun x t s ↦ hr x t _⟩
  · dsimp only
    rw [symm_zero, hG₁]
  · dsimp only
    rw [symm_one, hG₀]

/-- The **glued homotopy**, at finite regularity and at `C^∞`: run through `G` and then through
`G'`, each reparametrized to be stationary near `s = 1 / 2`. -/
theorem trans (h : IsHomotopy Φ Ψ G K) (h' : IsHomotopy Ψ Θ G' K') (hn : n ≤ ∞) :
    IsHomotopy Φ Θ
      (fun q ↦ if (q.2 : ℝ) ≤ 1 / 2 then G (q.1, collaredFirstHalf hn q.2)
        else G' (q.1, collaredSecondHalf hn q.2))
      (fun q ↦ if (q.2 : ℝ) ≤ 1 / 2 then K (q.1, collaredFirstHalf hn q.2)
        else K' (q.1, collaredSecondHalf hn q.2)) := by
  have hfinal := h.final_eq
  obtain ⟨hG, hG₀, hG₁, h₀, h₁, hK, hl, hr⟩ := h
  obtain ⟨hG', hG'₀, hG'₁, h'₀, h'₁, hK', hl', hr'⟩ := h'
  -- At the seam both inverses invert the motion of `Ψ`, so they agree there.
  have hseam (p : M × I) : K (p, 1) = K' (p, 0) := by
    rw [← hl' (K (p, 1)) p.2 0, hG'₀, ← hG₁, hr]
  refine ⟨hG.glue_collaredHalves hG' (fun p ↦ (hG₁ p).trans (hG'₀ p).symm) hn,
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_, hK.glue_collaredHalves hK' hseam hn,
    fun x t s ↦ ?_, fun x t s ↦ ?_⟩
  all_goals dsimp only
  · rw [ite_eq_left (by norm_num [Set.Icc.coe_zero]), collaredFirstHalf_zero, hG₀]
  · rw [ite_eq_right (by norm_num [Set.Icc.coe_one]), collaredSecondHalf_one, hG'₁]
  · split_ifs
    exacts [h₀ x _, h'₀ x _]
  · split_ifs
    exacts [h₁ x _, by rw [h'₁, hfinal]]
  · split_ifs
    exacts [hl x t _, hl' x t _]
  · split_ifs
    exacts [hr x t _, hr' x t _]

/-- The **composed homotopy** of the pointwise composites: feed the first homotopy into the
second. -/
theorem trans_congr (h : IsHomotopy Φ Φ' G K) (h' : IsHomotopy Ψ Ψ' G' K') :
    IsHomotopy (Φ.trans Ψ) (Φ'.trans Ψ') (fun q ↦ G' ((G q, q.1.2), q.2))
      (fun q ↦ K ((K' q, q.1.2), q.2)) := by
  obtain ⟨hG, hG₀, hG₁, h₀, h₁, hK, hl, hr⟩ := h
  obtain ⟨hG', hG'₀, hG'₁, h'₀, h'₁, hK', hl', hr'⟩ := h'
  refine ⟨hG'.comp ((hG.prodMk (contMDiff_snd.comp contMDiff_fst)).prodMk contMDiff_snd),
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ by dsimp only; rw [h₀, h'₀], fun x s ↦ ?_,
    hK.comp ((hK'.prodMk (contMDiff_snd.comp contMDiff_fst)).prodMk contMDiff_snd),
    fun x t s ↦ by dsimp only; rw [hl', hl], fun x t s ↦ by dsimp only; rw [hr, hr']⟩
  · dsimp only
    rw [hG₀, hG'₀, cylinderMap_trans, Function.comp_apply]
  · dsimp only
    rw [hG₁, hG'₁, cylinderMap_trans, Function.comp_apply]
  · dsimp only
    rw [h₁, h'₁, final_trans, _root_.Diffeomorph.coe_trans, Function.comp_apply]

end IsHomotopy

/-- Homotopic diffeotopies have the same final diffeomorphism. -/
theorem Homotopic.final_eq (h : Φ.Homotopic Ψ) : Φ.final = Ψ.final :=
  let ⟨_, _, h⟩ := h
  h.final_eq

variable (Φ) in
/-- Every diffeotopy is homotopic to itself, through the constant homotopy. -/
@[refl]
theorem Homotopic.refl : Φ.Homotopic Φ :=
  ⟨_, _, IsHomotopy.refl Φ⟩

/-- Homotopy of diffeotopies is symmetric: run the homotopy backwards. -/
@[symm]
theorem Homotopic.symm (h : Φ.Homotopic Ψ) : Ψ.Homotopic Φ :=
  let ⟨_, _, h⟩ := h
  ⟨_, _, h.symm⟩

/-- **Homotopy of diffeotopies is transitive**, at finite regularity and at `C^∞`. -/
@[trans]
theorem Homotopic.trans (h : Φ.Homotopic Ψ) (h' : Ψ.Homotopic Θ) (hn : n ≤ ∞) :
    Φ.Homotopic Θ :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, h'⟩ := h'
  ⟨_, _, h.trans h' hn⟩

/-- Homotopy of diffeotopies is an equivalence relation, at finite regularity and at `C^∞`. -/
theorem Homotopic.equivalence (hn : n ≤ ∞) :
    Equivalence (Homotopic (J := J) (n := n) (M := M)) :=
  ⟨Homotopic.refl, Homotopic.symm, fun h h' ↦ h.trans h' hn⟩

/-- **Homotopy is compatible with the pointwise composite.** If `Φ` is homotopic to `Φ'` and `Ψ` to
`Ψ'`, then `ψ_t ∘ φ_t` is homotopic to `ψ'_t ∘ φ'_t`: feed the first homotopy into the second. -/
theorem Homotopic.trans_congr (h : Φ.Homotopic Φ') (h' : Ψ.Homotopic Ψ') :
    (Φ.trans Ψ).Homotopic (Φ'.trans Ψ') :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, h'⟩ := h'
  ⟨_, _, h.trans_congr h'⟩

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
