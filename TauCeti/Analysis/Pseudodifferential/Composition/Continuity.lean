/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion

/-!
# Continuity of the composition symbol and of its remainders

Let `a` be a symbol of order `m'` and `b` a symbol of order `m` that vanishes at positions outside
a fixed compact set `K`. This file proves that the composition symbol `a # b`
(`TauCeti.Symbol.sharp`), whose quantization is `Op(a) ∘ Op(b)`, depends continuously on `a` and
`b` in the seminorm topologies of the symbol classes (`TauCeti.Symbol.instTopologicalSpace`), and
that so does every remainder

`R_N(a, b) = a # b - ∑_{k < N} sharpTerm a b k`

of its asymptotic expansion (`TauCeti.Symbol.sharpRemainder`), in the class of order `m' + m - N`.
The continuity of `a # b` in the class of order `m' + m` says nothing about `R_N(a, b)` in the
smaller class of order `m' + m - N`: it needs the remainder estimates themselves.

The quantitative form is a bilinear seminorm estimate: for compact sets `K` and `L` of positions
and words `α`, `β` of coordinate indices, there are finitely many seminorms of `a` on `L` and of
`b` on `K`, and a constant `C`, with

`p_{L,α,β}(a # b) ≤ C (∑ᵢ p_{L,αᵢ,βᵢ}(a)) (∑ⱼ p_{K,γⱼ,δⱼ}(b))`

for all `a` and all `b` vanishing outside `K` (`TauCeti.Symbol.exists_seminorm_sharp_le`), and
likewise for `R_N(a, b)` with its seminorms of order `m' + m - N`
(`TauCeti.Symbol.exists_seminorm_sharpRemainder_le`).
Consequently the composition of two continuous families of symbols, the right factors vanishing
outside one compact set, is a continuous family (`Continuous.symbol_sharp`), and so are the
remainders of the expansion (`Continuous.symbol_sharpRemainder`). For a fixed right factor,
`a ↦ a # b` and `a ↦ R_N(a, b)` are continuous linear maps (`TauCeti.Symbol.sharpRightCLM`,
`TauCeti.Symbol.sharpRemainderRightCLM`). Continuous families of symbols arise as homotopies of
symbols and as parameter-dependent symbols; this file lets them pass through the composition of
pseudodifferential operators together with its expansion: every truncation of the expansion has
a remainder of the claimed order depending continuously on the two factors.

## Proof outline

Without derivatives, `(a # b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη` is bounded
by `p_{L,[],[]}(a)` times the decay constant of the Fourier transform `b̂` of the position slices
of `b`, which is itself a finite sum of seminorms of `b` on `K`
(`TauCeti.Symbol.exists_norm_integral_sharpIntegrand_le_seminorm`). The Leibniz rules
`∂(a # b) = (∂a) # b + a # (∂b)` for position and frequency derivatives
(`TauCeti.Symbol.spatialDeriv_sharp`, `TauCeti.Symbol.coefficient_frequencyDeriv_sharp`) and the
identities `p_{L,α,β}(∂_{x_j} a) = p_{L,α ++ [j],β}(a)` and
`p_{L,α,β}(∂_{ξ_j} a) = p_{L,α,β ++ [j]}(a)` then give the estimate for every mixed derivative by
induction on the number of derivatives (`TauCeti.Symbol.exists_seminorm_le_of_leibniz`). The
remainders satisfy the same Leibniz rules, and their estimate without derivatives is proved with
the expansion in `TauCeti.Analysis.Pseudodifferential.Composition.Expansion`. Continuity follows
from the bilinear estimates by writing
`B(a, b) - B(a₀, b₀) = B(a - a₀, b - b₀) + B(a - a₀, b₀) + B(a₀, b - b₀)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open Filter MeasureTheory Real Topology FourierTransform
open TopologicalSpace (Compacts)
open scoped RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The seminorm estimate -/

section Seminorm

/-- The estimate without derivatives: `p_{L,[],[]}(a # b)` is at most `C p_{L,[],[]}(a)` times a
finite sum of seminorms `p_{K,γ,[]}(b)`, for all `b` vanishing outside `K`. -/
private theorem exists_seminorm_nil_nil_sharp_le (K L : Compacts (CoordinateSpace n)) :
    ∃ (t : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) →
          Symbol.seminorm L [] [] (a.sharp b hb) ≤
            C * Symbol.seminorm L [] [] a * ∑ γ ∈ t, Symbol.seminorm K γ [] b := by
  obtain ⟨t, C, hC0, hC⟩ := exists_norm_integral_sharpIntegrand_le_seminorm (U := U) (V := V)
    (W := W) (m := m) (m' := m') K L (R := 2 * π) (by linarith [Real.two_le_pi])
  refine ⟨t, C, hC0, fun a b hb hbK ↦ seminorm_le_bound L [] [] _
    (mul_nonneg (mul_nonneg hC0 (apply_nonneg _ _)) (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _))
    fun x hx ξ ↦ ?_⟩
  rw [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero, coefficient_sharp]
  simpa only [sharpIntegrand_apply] using hC a b hbK (2 * π) (abs_of_pos Real.two_pi_pos).le x hx ξ

/-- **Seminorm estimate for the composition symbol.** For compact sets `K` and `L` of positions
and words `α`, `β` of coordinate indices, there are finitely many pairs of words and a constant `C`
such that

`p_{L,α,β}(a # b) ≤ C (∑ᵢ p_{L,αᵢ,βᵢ}(a)) (∑ⱼ p_{K,γⱼ,δⱼ}(b))`

for every symbol `a` of order `m'` and every symbol `b` of order `m` vanishing at positions outside
`K`. -/
theorem exists_seminorm_sharp_le (K L : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ (s t : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β (a.sharp b hb) ≤
            C * (∑ i ∈ s, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t, Symbol.seminorm K i.1 i.2 b :=
  exists_seminorm_le_of_leibniz (fun m' m ↦ m' + m) (fun _ _ ↦ by linarith)
    (fun _ _ ↦ by linarith) (fun a b hb ↦ a.sharp b hb) (fun _ _ hb j ↦ spatialDeriv_sharp hb j)
    (fun _ _ hb j ↦ funext fun p ↦ coefficient_frequencyDeriv_sharp hb j p.1 p.2) K L
    (fun {m m'} ↦ by
      obtain ⟨t, C, hC0, hC⟩ := exists_seminorm_nil_nil_sharp_le (U := U) (V := V) (W := W)
        (m := m) (m' := m') K L
      refine ⟨{([], [])}, t.image fun γ ↦ (γ, []), C, hC0, fun a b hb hbK ↦ ?_⟩
      rw [Finset.sum_singleton, Finset.sum_image fun _ _ _ _ h ↦ congrArg Prod.fst h]
      exact hC a b hb hbK)
    α β

end Seminorm

/-! ### Continuity -/

section Continuity

variable {μ : ℝ}
  (B : Symbol n W U m' → (b : Symbol n V W m) → b.HasCompactSpatialSupport → Symbol n V U μ)
  (hsub_left : ∀ (a₁ a₂ : Symbol n W U m') (b : Symbol n V W m)
    (hb : b.HasCompactSpatialSupport), B (a₁ - a₂) b hb = B a₁ b hb - B a₂ b hb)
  (hsub_right : ∀ (a : Symbol n W U m') (b₁ b₂ : Symbol n V W m)
    (hb₁ : b₁.HasCompactSpatialSupport) (hb₂ : b₂.HasCompactSpatialSupport),
      B a (b₁ - b₂) (hb₁.sub hb₂) = B a b₁ hb₁ - B a b₂ hb₂)
  (hB : ∀ (K L : Compacts (CoordinateSpace n)) (α β : List (Fin n)),
    ∃ (s t : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) → Symbol.seminorm L α β (B a b hb) ≤
          C * (∑ i ∈ s, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t, Symbol.seminorm K i.1 i.2 b)

include hsub_left hsub_right hB in
/-- Let `B a b` be a symbol depending on a symbol `a` and a symbol `b` with compact spatial
support, subtractive in each argument, with a bilinear seminorm estimate as in
`exists_seminorm_sharp_le`. If the seminorms of `a i - a₀` on `L` and those of `b i - b₀` on `K`
tend to zero, then so does `p_{L,α,β}(B (a i) (b i) - B a₀ b₀)`. -/
private theorem tendsto_seminorm_sub {ι : Type*} {l : Filter ι}
    {K L : Compacts (CoordinateSpace n)} (α β : List (Fin n)) {a : ι → Symbol n W U m'}
    {a₀ : Symbol n W U m'} {b : ι → Symbol n V W m} {b₀ : Symbol n V W m}
    (hb : ∀ i, (b i).HasCompactSpatialSupport) (hb₀ : b₀.HasCompactSpatialSupport)
    (hbK : ∀ i, ∀ x ∉ K, ∀ ξ, (b i).coefficient (x, ξ) = 0)
    (hb₀K : ∀ x ∉ K, ∀ ξ, b₀.coefficient (x, ξ) = 0)
    (ha : ∀ γ δ, Tendsto (fun i ↦ Symbol.seminorm L γ δ (a i - a₀)) l (𝓝 0))
    (hbt : ∀ γ δ, Tendsto (fun i ↦ Symbol.seminorm K γ δ (b i - b₀)) l (𝓝 0)) :
    Tendsto (fun i ↦ Symbol.seminorm L α β (B (a i) (b i) (hb i) - B a₀ b₀ hb₀)) l (𝓝 0) := by
  obtain ⟨s, t, C, -, hC⟩ := hB K L α β
  have hsub : ∀ i, ∀ x ∉ K, ∀ ξ, (b i - b₀).coefficient (x, ξ) = 0 := fun i x hx ξ ↦ by
    rw [coefficient_sub, Pi.sub_apply, hbK i x hx ξ, hb₀K x hx ξ, sub_zero]
  have hP : Tendsto (fun i ↦ ∑ k ∈ s, Symbol.seminorm L k.1 k.2 (a i - a₀)) l (𝓝 0) := by
    simpa using tendsto_finsetSum s fun k _ ↦ ha k.1 k.2
  have hQ : Tendsto (fun i ↦ ∑ k ∈ t, Symbol.seminorm K k.1 k.2 (b i - b₀)) l (𝓝 0) := by
    simpa using tendsto_finsetSum t fun k _ ↦ hbt k.1 k.2
  set P₀ := ∑ k ∈ s, Symbol.seminorm L k.1 k.2 a₀
  set Q₀ := ∑ k ∈ t, Symbol.seminorm K k.1 k.2 b₀
  -- `B a b - B a₀ b₀ = B (a - a₀) (b - b₀) + B (a - a₀) b₀ + B a₀ (b - b₀)`
  have hdecomp : ∀ i, B (a i) (b i) (hb i) - B a₀ b₀ hb₀ =
      B (a i - a₀) (b i - b₀) ((hb i).sub hb₀) + B (a i - a₀) b₀ hb₀ +
        B a₀ (b i - b₀) ((hb i).sub hb₀) := fun i ↦ by
    rw [hsub_right _ _ _ (hb i) hb₀, hsub_right _ _ _ (hb i) hb₀, hsub_left, hsub_left]
    abel
  refine squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun i ↦ ?_)
    (show Tendsto (fun i ↦ C * (∑ k ∈ s, Symbol.seminorm L k.1 k.2 (a i - a₀)) *
        (∑ k ∈ t, Symbol.seminorm K k.1 k.2 (b i - b₀)) +
      C * (∑ k ∈ s, Symbol.seminorm L k.1 k.2 (a i - a₀)) * Q₀ +
      C * P₀ * (∑ k ∈ t, Symbol.seminorm K k.1 k.2 (b i - b₀))) l (𝓝 0) by
      simpa using (((hP.const_mul C).mul hQ).add ((hP.const_mul C).mul_const Q₀)).add
        ((hQ.const_mul (C * P₀))))
  rw [hdecomp]
  refine (map_add_le_add _ _ _).trans (add_le_add ((map_add_le_add _ _ _).trans
    (add_le_add (hC _ _ _ (hsub i)) (hC _ _ _ hb₀K))) (hC _ _ _ (hsub i)))

include hsub_left hsub_right hB in
/-- **Continuity from a bilinear seminorm estimate.** For `B` as in `tendsto_seminorm_sub`, if
`t ↦ a t` and `t ↦ b t` are continuous families of symbols, and all `b t` vanish at positions
outside one compact set `K`, then `t ↦ B (a t) (b t)` is a continuous family of symbols. -/
private theorem continuous_of_exists_seminorm_le {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n W U m'} {b : X → Symbol n V W m} (ha : Continuous a) (hb : Continuous b)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hbK : ∀ t, ∀ x ∉ K, ∀ ξ, (b t).coefficient (x, ξ) = 0) :
    Continuous fun t ↦ B (a t) (b t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t⟩) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  rw [ContinuousAt, withSeminorms.tendsto_nhds]
  rintro ⟨L, α, β⟩ ε hε
  have key := tendsto_seminorm_sub B hsub_left hsub_right hB (K := ⟨K, hK⟩) (L := L) (a := a)
    (a₀ := a t₀) (b := b) (b₀ := b t₀) α β
    (fun t ↦ hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t⟩)
    (hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t₀⟩) hbK (hbK t₀)
    (fun γ δ ↦ by
      simpa only [Function.comp_def, seminormFamily_apply] using
        ((withSeminorms.continuous_seminorm (L, γ, δ)).comp
          (show Continuous fun t ↦ a t - a t₀ from ha.sub continuous_const)).tendsto' t₀ 0
          (by simp))
    (fun γ δ ↦ by
      simpa only [Function.comp_def, seminormFamily_apply] using
        ((withSeminorms.continuous_seminorm (⟨K, hK⟩, γ, δ)).comp
          (show Continuous fun t ↦ b t - b t₀ from hb.sub continuous_const)).tendsto' t₀ 0
          (by simp))
  simpa only [seminormFamily_apply] using (tendsto_order.1 key).2 ε hε

/-- **Continuity of the composition symbol.** If `t ↦ a t` and `t ↦ b t` are continuous families
of symbols of orders `m'` and `m`, and all `b t` vanish at positions outside one compact set `K`,
then `t ↦ a t # b t` is a continuous family of symbols of order `m' + m`. -/
theorem _root_.Continuous.symbol_sharp {X : Type*} [TopologicalSpace X] {a : X → Symbol n W U m'}
    {b : X → Symbol n V W m} (ha : Continuous a) (hb : Continuous b)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hbK : ∀ t, ∀ x ∉ K, ∀ ξ, (b t).coefficient (x, ξ) = 0) :
    Continuous fun t ↦ (a t).sharp (b t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t⟩) :=
  continuous_of_exists_seminorm_le (fun a b hb ↦ a.sharp b hb)
    (fun a₁ a₂ _ hb ↦ sub_sharp a₁ a₂ hb) (fun a _ _ hb₁ hb₂ ↦ sharp_sub a hb₁ hb₂)
    exists_seminorm_sharp_le ha hb hK hbK

/-- Composition with a fixed right factor `b` with compact spatial support, `a ↦ a # b`, as a
continuous linear map from the symbols of order `m'` to those of order `m' + m`. -/
def sharpRightCLM (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport) :
    Symbol n W U m' →L[ℂ] Symbol n V U (m' + m) where
  toFun a := a.sharp b hb
  map_add' a₁ a₂ := add_sharp a₁ a₂ hb
  map_smul' c a := smul_sharp c a hb
  cont := by
    obtain ⟨K, hK, hbK⟩ := hasCompactSpatialSupport_iff.1 hb
    exact continuous_id.symbol_sharp continuous_const hK fun _ ↦ hbK

@[simp]
theorem sharpRightCLM_apply (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport)
    (a : Symbol n W U m') : sharpRightCLM b hb a = a.sharp b hb := (rfl)

variable [CompleteSpace W] [CompleteSpace U]

/-- **Continuity of the remainders of the composition expansion.** If `t ↦ a t` and `t ↦ b t` are
continuous families of symbols of orders `m'` and `m`, and all `b t` vanish at positions outside one
compact set `K`, then for every `N` the remainders `a t # b t - ∑_{k < N} sharpTerm (a t) (b t) k`
form a continuous family of symbols of order `m' + m - N`. -/
theorem _root_.Continuous.symbol_sharpRemainder {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n W U m'} {b : X → Symbol n V W m} (ha : Continuous a) (hb : Continuous b)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hbK : ∀ t, ∀ x ∉ K, ∀ ξ, (b t).coefficient (x, ξ) = 0) (N : ℕ) :
    Continuous fun t ↦
      (a t).sharpRemainder (b t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t⟩) N :=
  continuous_of_exists_seminorm_le (fun a b hb ↦ a.sharpRemainder b hb N)
    (fun a₁ a₂ _ hb ↦ sub_sharpRemainder a₁ a₂ hb N)
    (fun a _ _ hb₁ hb₂ ↦ sharpRemainder_sub a hb₁ hb₂ N)
    (fun K L α β ↦ exists_seminorm_sharpRemainder_le K L N α β) ha hb hK hbK

/-- The remainder of the composition expansion after `N` terms with a fixed right factor `b` with
compact spatial support, `a ↦ a # b - ∑_{k < N} sharpTerm a b k`, as a continuous linear map from
the symbols of order `m'` to those of order `m' + m - N`. -/
def sharpRemainderRightCLM (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    Symbol n W U m' →L[ℂ] Symbol n V U (m' + m - N) where
  toFun a := a.sharpRemainder b hb N
  map_add' a₁ a₂ := add_sharpRemainder a₁ a₂ hb N
  map_smul' c a := smul_sharpRemainder c a hb N
  cont := by
    obtain ⟨K, hK, hbK⟩ := hasCompactSpatialSupport_iff.1 hb
    exact continuous_id.symbol_sharpRemainder continuous_const hK (fun _ ↦ hbK) N

@[simp]
theorem sharpRemainderRightCLM_apply (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport)
    (N : ℕ) (a : Symbol n W U m') : sharpRemainderRightCLM b hb N a = a.sharpRemainder b hb N :=
  (rfl)

end Continuity

end Symbol

end TauCeti
