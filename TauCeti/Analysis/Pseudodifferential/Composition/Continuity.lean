/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# Continuity of the composition symbol

Let `a` be a symbol of order `m'` and `b` a symbol of order `m` that vanishes at positions outside
a fixed compact set `K`. This file proves that the composition symbol `a # b`
(`TauCeti.Symbol.sharp`), whose quantization is `Op(a) ∘ Op(b)`, depends continuously on `a` and
`b` in the seminorm topologies of the symbol classes (`TauCeti.Symbol.instTopologicalSpace`).

The quantitative form is a bilinear seminorm estimate: for compact sets `K` and `L` of positions
and words `α`, `β` of coordinate indices, there are finitely many seminorms of `a` on `L` and of
`b` on `K`, and a constant `C`, with

`p_{L,α,β}(a # b) ≤ C (∑ᵢ p_{L,αᵢ,βᵢ}(a)) (∑ⱼ p_{K,γⱼ,δⱼ}(b))`

for all `a` and all `b` vanishing outside `K` (`TauCeti.Symbol.exists_seminorm_sharp_le`).
Consequently the composition of two continuous families of symbols, the right factors vanishing
outside one compact set, is a continuous family (`Continuous.symbol_sharp`), and composition
with a fixed right factor is a continuous linear map (`TauCeti.Symbol.sharpRightCLM`). Continuous
families of symbols arise as homotopies of symbols and as parameter-dependent symbols; this file
lets them pass through the composition of pseudodifferential operators.

## Proof outline

Without derivatives, `(a # b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη` is bounded
by `p_{L,[],[]}(a)` times the decay constant of the Fourier transform `b̂` of the position slices
of `b`, which is itself a finite sum of seminorms of `b` on `K`
(`TauCeti.Symbol.exists_norm_fourier_slice_le_sum_seminorm`), together with Peetre's inequality
(`TauCeti.Symbol.norm_comp_fourier_slice_le`). The Leibniz rules
`∂(a # b) = (∂a) # b + a # (∂b)` for position and frequency derivatives
(`TauCeti.Symbol.spatialDeriv_sharp`, `TauCeti.Symbol.coefficient_frequencyDeriv_sharp`) and the
identities `p_{L,α,β}(∂_{x_j} a) = p_{L,α ++ [j],β}(a)` and
`p_{L,α,β}(∂_{ξ_j} a) = p_{L,α,β ++ [j]}(a)` then give the estimate for every mixed derivative by
induction on the number of derivatives.

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

/-- Two bilinear bounds `x ≤ C₁ P₁ Q₁` and `y ≤ C₂ P₂ Q₂` combine to `x + y ≤ (C₁ + C₂) P Q` for
`P ≥ P₁, P₂` and `Q ≥ Q₁, Q₂`. -/
private theorem add_le_add_mul_mul {x y C₁ C₂ P₁ P₂ Q₁ Q₂ P Q : ℝ}
    (hx : x ≤ C₁ * P₁ * Q₁) (hy : y ≤ C₂ * P₂ * Q₂) (h₁ : P₁ ≤ P) (h₂ : P₂ ≤ P) (h₃ : Q₁ ≤ Q)
    (h₄ : Q₂ ≤ Q) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hQ₁ : 0 ≤ Q₁)
    (hQ₂ : 0 ≤ Q₂) : x + y ≤ (C₁ + C₂) * P * Q := by
  have e₁ : C₁ * P₁ * Q₁ ≤ C₁ * P * Q :=
    mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC₁) h₃ hQ₁ (mul_nonneg hC₁ (hP₁.trans h₁))
  have e₂ : C₂ * P₂ * Q₂ ≤ C₂ * P * Q :=
    mul_le_mul (mul_le_mul_of_nonneg_left h₂ hC₂) h₄ hQ₂ (mul_nonneg hC₂ (hP₂.trans h₂))
  linarith

/-- The estimate without derivatives: `p_{L,[],[]}(a # b)` is at most `C p_{L,[],[]}(a)` times a
finite sum of seminorms `p_{K,γ,[]}(b)`, for all `b` vanishing outside `K`. -/
private theorem exists_seminorm_nil_nil_sharp_le (K L : Compacts (CoordinateSpace n)) :
    ∃ (t : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) →
          Symbol.seminorm L [] [] (a.sharp b hb) ≤
            C * Symbol.seminorm L [] [] a * ∑ γ ∈ t, Symbol.seminorm K γ [] b := by
  obtain ⟨t, CF, hCF0, hCF⟩ := exists_norm_fourier_slice_le_sum_seminorm (V := V) (W := W)
    (m := m) K ((n : ℝ) + 1 + |m'|)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  set D := 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * CF * I
  refine ⟨t, D, by positivity, fun a b hb hbK ↦ ?_⟩
  set A := Symbol.seminorm L [] [] a
  set Q := ∑ γ ∈ t, Symbol.seminorm K γ [] b
  have hA : 0 ≤ A := apply_nonneg _ _
  refine seminorm_le_bound L [] [] _ (by positivity) fun x hx ξ ↦ ?_
  -- the pointwise bound on the integrand, with the integrable weight `⟨η⟩ ^ (-(n + 1))`
  have hpt : ∀ η, ‖(𝐞 ⟪η, x⟫ : ℂ) •
      (a.coefficient (x, ξ + (2 * π) • η)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)‖ ≤
        A * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * (CF * Q) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := fun η ↦ by
    rw [norm_smul, Circle.norm_coe, one_mul]
    refine norm_comp_fourier_slice_le hA (by linarith [Real.two_le_pi])
      (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
      (norm_coefficient_le_seminorm L a hx _) ?_
    simpa only [add_assoc] using hCF b hbK η ξ
  have hint : Integrable fun η : CoordinateSpace n ↦
      A * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * (CF * Q) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) *
        (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _
  rw [mixedDeriv_nil_nil, coefficient_sharp, List.length_nil, Nat.cast_zero, sub_zero]
  refine (norm_integral_le_of_norm_le hint (.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- **The step of a position derivative.** A bilinear bound for `p_{L,α,β}(a # b)` gives one for
`p_{L,α ++ [j],β}(a # b)`, by the Leibniz rule `∂_{x_j} (a # b) = (∂_{x_j} a) # b + a # (∂_{x_j} b)`
and `p_{L,α,β}(∂_{x_j} a) = p_{L,α ++ [j],β}(a)`. -/
private theorem seminorm_append_sharp_le [DecidableEq (List (Fin n))]
    {K L : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {s t : Finset (List (Fin n) × List (Fin n))} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
      (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) → Symbol.seminorm L α β (a.sharp b hb) ≤
        C * (∑ i ∈ s, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t, Symbol.seminorm K i.1 i.2 b)
    (j : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport)
    (hbK : ∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) :
    Symbol.seminorm L (α ++ [j]) β (a.sharp b hb) ≤
      (C + C) * (∑ i ∈ s ∪ s.image (Prod.map (· ++ [j]) id), Symbol.seminorm L i.1 i.2 a) *
        ∑ i ∈ t ∪ t.image (Prod.map (· ++ [j]) id), Symbol.seminorm K i.1 i.2 b := by
  have hf : Function.Injective (Prod.map (· ++ [j]) id : List (Fin n) × List (Fin n) → _) :=
    (List.append_left_injective [j]).prodMap Function.injective_id
  rw [← seminorm_spatialDeriv, spatialDeriv_sharp]
  refine (map_add_le_add _ _ _).trans (add_le_add_mul_mul (hC _ b hb hbK)
    (hC a _ _ fun x hx ↦ coefficient_spatialDeriv_eq_zero K.isCompact.isClosed hbK j hx) ?_ ?_ ?_ ?_
    hC0 hC0 (by positivity) (by positivity) (by positivity) (by positivity))
  · exact Finset.sum_le_sum_of_injOn _ hf.injOn Finset.subset_union_right
      (fun i _ ↦ (seminorm_spatialDeriv j L i.1 i.2 a).le) fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_injOn _ hf.injOn Finset.subset_union_right
      (fun i _ ↦ (seminorm_spatialDeriv j K i.1 i.2 b).le) fun _ _ _ ↦ apply_nonneg _ _

/-- **The step of a frequency derivative.** Bilinear bounds for `p_{L,α,β}((∂a) # b)` and
`p_{L,α,β}(a # (∂b))` at the orders of `∂_{ξ_j} a` and `∂_{ξ_j} b` give one for
`p_{L,α,β ++ [j]}(a # b)`, by the Leibniz rule
`∂_{ξ_j} (a # b) = (∂_{ξ_j} a) # b + a # (∂_{ξ_j} b)` and
`p_{L,α,β}(∂_{ξ_j} a) = p_{L,α,β ++ [j]}(a)`. -/
private theorem seminorm_sharp_append_le [DecidableEq (List (Fin n))]
    {K L : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {s₁ t₁ s₂ t₂ : Finset (List (Fin n) × List (Fin n))} {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ (a : Symbol n W U (m' - 1)) (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
      (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) → Symbol.seminorm L α β (a.sharp b hb) ≤
        C₁ * (∑ i ∈ s₁, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t₁, Symbol.seminorm K i.1 i.2 b)
    (hC₂ : ∀ (a : Symbol n W U m') (b : Symbol n V W (m - 1)) (hb : b.HasCompactSpatialSupport),
      (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) → Symbol.seminorm L α β (a.sharp b hb) ≤
        C₂ * (∑ i ∈ s₂, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t₂, Symbol.seminorm K i.1 i.2 b)
    (j : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport)
    (hbK : ∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) :
    Symbol.seminorm L α (β ++ [j]) (a.sharp b hb) ≤
      (C₁ + C₂) * (∑ i ∈ s₁.image (Prod.map id (· ++ [j])) ∪ s₂, Symbol.seminorm L i.1 i.2 a) *
        ∑ i ∈ t₁ ∪ t₂.image (Prod.map id (· ++ [j])), Symbol.seminorm K i.1 i.2 b := by
  have hg : Function.Injective (Prod.map id (· ++ [j]) : List (Fin n) × List (Fin n) → _) :=
    Function.injective_id.prodMap (List.append_left_injective [j])
  -- the two terms of the Leibniz rule have the orders `(m' - 1) + m` and `m' + (m - 1)`
  have h₁ : m' - 1 + m ≤ m' + m - 1 := by linarith
  have h₂ : m' + (m - 1) ≤ m' + m - 1 := by linarith
  have hsplit : frequencyDeriv j (a.sharp b hb) =
      inclusion h₁ ((frequencyDeriv j a).sharp b hb) +
        inclusion h₂ (a.sharp (frequencyDeriv j b) (hb.frequencyDeriv j)) := by
    ext1
    funext ⟨x, ξ⟩
    rw [coefficient_add, Pi.add_apply, coefficient_inclusion, coefficient_inclusion,
      coefficient_frequencyDeriv_sharp]
  rw [← seminorm_frequencyDeriv, hsplit]
  refine (map_add_le_add _ _ _).trans (add_le_add_mul_mul
    ((seminorm_inclusion_le h₁ L α β _).trans (hC₁ _ b hb hbK))
    ((seminorm_inclusion_le h₂ L α β _).trans
      (hC₂ a _ _ fun x hx ↦ coefficient_frequencyDeriv_eq_zero (hbK x hx) j)) ?_ ?_ ?_ ?_
    hC₁0 hC₂0 (by positivity) (by positivity) (by positivity) (by positivity))
  · exact Finset.sum_le_sum_of_injOn _ hg.injOn Finset.subset_union_left
      (fun i _ ↦ (seminorm_frequencyDeriv j L i.1 i.2 a).le) fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ ↦ apply_nonneg _ _
  · exact Finset.sum_le_sum_of_injOn _ hg.injOn Finset.subset_union_right
      (fun i _ ↦ (seminorm_frequencyDeriv j K i.1 i.2 b).le) fun _ _ _ ↦ apply_nonneg _ _

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
            C * (∑ i ∈ s, Symbol.seminorm L i.1 i.2 a) * ∑ i ∈ t, Symbol.seminorm K i.1 i.2 b := by
  classical
  -- induction on the number of derivatives, removing the last letter of `β`, or of `α` if `β = []`
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m m' α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    obtain ⟨t, C, hC0, hC⟩ := exists_seminorm_nil_nil_sharp_le (U := U) (V := V) (W := W)
      (m := m) (m' := m') K L
    refine ⟨{([], [])}, t.image fun γ ↦ (γ, []), C, hC0, fun a b hb hbK ↦ ?_⟩
    rw [Finset.sum_singleton, Finset.sum_image fun _ _ _ _ h ↦ congrArg Prod.fst h]
    exact hC a b hb hbK
  | succ D ih =>
    rcases List.eq_nil_or_concat' β with rfl | ⟨β, j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α, j, rfl⟩
      · simp at hD
      obtain ⟨s, t, C, hC0, hC⟩ := ih (m := m) (m' := m') α [] (by simpa using hD)
      exact ⟨_, _, C + C, by positivity, seminorm_append_sharp_le hC0 hC j⟩
    · have hlen : α.length + β.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨s₁, t₁, C₁, hC₁0, hC₁⟩ := ih (m := m) (m' := m' - 1) α β hlen
      obtain ⟨s₂, t₂, C₂, hC₂0, hC₂⟩ := ih (m := m - 1) (m' := m') α β hlen
      exact ⟨_, _, C₁ + C₂, by positivity, seminorm_sharp_append_le hC₁0 hC₂0 hC₁ hC₂ j⟩

end Seminorm

/-! ### Continuity -/

section Continuity

/-- If the seminorms of `a i - a₀` on `L` and those of `b i - b₀` on `K` tend to zero, then so does
`p_{L,α,β}(a i # b i - a₀ # b₀)`, by the bilinear estimate `exists_seminorm_sharp_le`. -/
private theorem tendsto_seminorm_sharp_sub {ι : Type*} {l : Filter ι}
    {K L : Compacts (CoordinateSpace n)} (α β : List (Fin n)) {a : ι → Symbol n W U m'}
    {a₀ : Symbol n W U m'} {b : ι → Symbol n V W m} {b₀ : Symbol n V W m}
    (hb : ∀ i, (b i).HasCompactSpatialSupport) (hb₀ : b₀.HasCompactSpatialSupport)
    (hbK : ∀ i, ∀ x ∉ K, ∀ ξ, (b i).coefficient (x, ξ) = 0)
    (hb₀K : ∀ x ∉ K, ∀ ξ, b₀.coefficient (x, ξ) = 0)
    (ha : ∀ γ δ, Tendsto (fun i ↦ Symbol.seminorm L γ δ (a i - a₀)) l (𝓝 0))
    (hbt : ∀ γ δ, Tendsto (fun i ↦ Symbol.seminorm K γ δ (b i - b₀)) l (𝓝 0)) :
    Tendsto (fun i ↦ Symbol.seminorm L α β ((a i).sharp (b i) (hb i) - a₀.sharp b₀ hb₀)) l
      (𝓝 0) := by
  obtain ⟨s, t, C, -, hC⟩ :=
    exists_seminorm_sharp_le (U := U) (V := V) (W := W) (m := m) (m' := m') K L α β
  have hsub : ∀ i, ∀ x ∉ K, ∀ ξ, (b i - b₀).coefficient (x, ξ) = 0 := fun i x hx ξ ↦ by
    rw [coefficient_sub, Pi.sub_apply, hbK i x hx ξ, hb₀K x hx ξ, sub_zero]
  have hP : Tendsto (fun i ↦ ∑ k ∈ s, Symbol.seminorm L k.1 k.2 (a i - a₀)) l (𝓝 0) := by
    simpa using tendsto_finsetSum s fun k _ ↦ ha k.1 k.2
  have hQ : Tendsto (fun i ↦ ∑ k ∈ t, Symbol.seminorm K k.1 k.2 (b i - b₀)) l (𝓝 0) := by
    simpa using tendsto_finsetSum t fun k _ ↦ hbt k.1 k.2
  set P₀ := ∑ k ∈ s, Symbol.seminorm L k.1 k.2 a₀
  set Q₀ := ∑ k ∈ t, Symbol.seminorm K k.1 k.2 b₀
  -- `a # b - a₀ # b₀ = (a - a₀) # (b - b₀) + (a - a₀) # b₀ + a₀ # (b - b₀)`
  have hdecomp : ∀ i, (a i).sharp (b i) (hb i) - a₀.sharp b₀ hb₀ =
      (a i - a₀).sharp (b i - b₀) ((hb i).sub hb₀) + (a i - a₀).sharp b₀ hb₀ +
        a₀.sharp (b i - b₀) ((hb i).sub hb₀) := fun i ↦ by
    rw [sharp_sub _ (hb i) hb₀, sharp_sub _ (hb i) hb₀, sub_sharp, sub_sharp]
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

/-- **Continuity of the composition symbol.** If `t ↦ a t` and `t ↦ b t` are continuous families
of symbols of orders `m'` and `m`, and all `b t` vanish at positions outside one compact set `K`,
then `t ↦ a t # b t` is a continuous family of symbols of order `m' + m`. -/
theorem _root_.Continuous.symbol_sharp {X : Type*} [TopologicalSpace X] {a : X → Symbol n W U m'}
    {b : X → Symbol n V W m} (ha : Continuous a) (hb : Continuous b)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hbK : ∀ t, ∀ x ∉ K, ∀ ξ, (b t).coefficient (x, ξ) = 0) :
    Continuous fun t ↦ (a t).sharp (b t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK t⟩) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  rw [ContinuousAt, withSeminorms.tendsto_nhds]
  rintro ⟨L, α, β⟩ ε hε
  have key := tendsto_seminorm_sharp_sub (K := ⟨K, hK⟩) (L := L) (a := a) (a₀ := a t₀) (b := b)
    (b₀ := b t₀) α β
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

end Continuity

end Symbol

end TauCeti
