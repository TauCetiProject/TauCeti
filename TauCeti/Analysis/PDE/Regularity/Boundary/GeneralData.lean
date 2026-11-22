/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.BoundaryValues
public import TauCeti.Analysis.PDE.Regularity.Boundary.DirichletHolder

/-!
# The global Hölder estimate for the Dirichlet problem with general data

Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a bounded Lipschitz domain and let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ`. Consider the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` in `Ω`, `u = G` on `∂Ω`,

with a scalar datum `f ∈ Lʳ(Ω)`, `r > 1`, `r > n/2`, a vector datum `F ∈ L^q(Ω; ℝⁿ)`, `q > 2`,
`q > n`, and boundary values `G` bounded by `K₀` and `K₁`-Lipschitz on `Ω`. A weak solution is a
`u ∈ H¹(Ω)` with

`a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`,

and `u - g ∈ H¹₀(Ω)` for some `g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. This file
proves that every such `u` is Hölder continuous up to the boundary: it agrees almost everywhere on
`Ω` with a function that is `α`-Hölder on `Ω` with constant

`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`,

where `α ∈ (0, 1]` and `C` depend only on `Ω`, `λ`, `Λ`, `r`, `q` and the normalization of the
Haar measure (`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_add_divergence`). A function
that is Hölder on `Ω` extends uniquely to a Hölder function on the closure of `Ω`, with the same
exponent and constant. No regularity of the coefficients beyond measurability is assumed, and the
constants do not depend on `a` beyond `λ` and `Λ`. This is Gilbarg–Trudinger's global Hölder
estimate, Theorem 8.29, for a uniformly elliptic operator in divergence form without lower-order
terms, with Lipschitz boundary values. The uniformity in the coefficient is what the compact-map
existence theory of quasilinear equations consumes.

## The argument

The two special cases are already proved: a scalar datum with zero boundary values
(`Set.IsLipschitzDomain.exists_holderWith_preciseRepresentative_indicator`), and a divergence
datum with Lipschitz boundary values
(`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_divergence`).
Let `w ∈ H¹₀(Ω)` be the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼw) = f`, given by Lax–Milgram
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp`;
`v ↦ ∫_Ω f v` is continuous on `H¹₀(Ω)` because `r > 2n/(n + 2)`). Then `u - w` solves
`-∂ᵢ(aⁱʲ ∂ⱼ(u - w)) = ∂ᵢFⁱ` with the boundary values `G`, and `u = (u - w) + w`. The two Hölder
exponents are lowered to their minimum on the bounded set `Ω` (`HolderOnWith.of_le`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.3 and 8.29.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- Splitting off the scalar datum. If `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` weakly, then the weak
solution `w ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = f` leaves `u - w` solving `-∂ᵢ(aⁱʲ ∂ⱼ(u - w)) = ∂ᵢFⁱ`. -/
private theorem exists_mem_w1p0Submodule_forall_energyFormH1_eq_and_sub_eq [Nonempty ι]
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    {r : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : W1p mu Omega 2} (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hfin : mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞) (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) (hf : MemLp f r (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) :
    ∃ w : W1p mu Omega 2, w ∈ w1p0Submodule mu Omega 2 ∧
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 w (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u - w) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨w, hw, -⟩ := h.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp ha (c := 0)
    aestronglyMeasurable_const (gamma := 0) (fun _ _ => by simp) (fun _ _ => le_rfl) hfin hr
    (by nlinarith [mul_pos hn (sub_pos.2 hr1)]) hf
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨w, (ClosedSubmodule.mem_toSubmodule_iff _ _).1 w.property, hw, fun v => ?_⟩
  rw [energyFormH1_sub_left hcoeff, hu v, hw v]
  ring

end TauCeti.PDE

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE TauCeti.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The arithmetic of the constant: the sum of the two Hölder constants is at most the combined
constant times the sum of the data. -/
private theorem mul_add_mul_le {C₁ C₂ d₁ d₂ P Q K₀ K₁ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) :
    C₂ * (Q + K₀ + K₁) * d₂ + C₁ * P * d₁ ≤ (C₁ * d₁ + C₂ * d₂) * (P + Q + K₀ + K₁) := by
  have h₁ : 0 ≤ C₁ * d₁ * (Q + K₀ + K₁) := by positivity
  have h₂ : 0 ≤ C₂ * d₂ * P := by positivity
  nlinarith

/-- **The global Hölder estimate for the Dirichlet problem with a scalar datum, a divergence datum
and Lipschitz boundary values on a bounded Lipschitz domain.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a bounded
Lipschitz domain, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are `α ∈ (0, 1]`
and `C > 0`, depending only on `Ω`, `λ`, `Λ`, `r`, `q` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, let `f ∈ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `G` be bounded by `K₀` and
`K₁`-Lipschitz on `Ω`. Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with
boundary values `G`: `a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`, and `u - g ∈ H¹₀(Ω)`
for some `g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. Then `u` agrees almost everywhere
on `Ω` with a function that is `α`-Hölder on `Ω` with constant
`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`.

No regularity of the coefficients beyond measurability is assumed. -/
theorem exists_ae_eq_and_holderOnWith_add_divergence [Nonempty ι]
    {Omega : Opens (EuclideanSpace ℝ ι)}
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {lam Lam : ℝ} {r q : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u g : W1p mu Omega 2} {G : EuclideanSpace ℝ ι → ℝ} {K₀ K₁ : ℝ≥0},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) →
      MemLp F q (mu.restrict Omega) →
      u - g ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.value g =ᵐ[mu.restrict Omega] G →
      LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |G x| ≤ K₀) →
      ∃ v : EuclideanSpace ℝ ι → ℝ, W1p.value u =ᵐ[mu.restrict Omega] v ∧
        HolderOnWith (C * ((eLpNorm f r (mu.restrict Omega)).toReal / lam +
          (eLpNorm F q (mu.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal α v Omega := by
  obtain ⟨α₁, C₁, hα₁, hC₁, hscalar⟩ :=
    exists_holderWith_preciseRepresentative_indicator (mu := mu) hΩ hb (lam := lam)
      (Lam := Lam) hr hrn
  obtain ⟨α₂, C₂, hα₂, hα₂1, hC₂, hdiv⟩ :=
    exists_ae_eq_and_holderOnWith_divergence (mu := mu) hΩ hb (lam := lam) (Lam := Lam) hq hqn
  -- A bound `D ≥ 1` for the distances in `Ω`, to lower both exponents to `min α₁ α₂`.
  obtain ⟨D₀, hD₀⟩ := isBounded_iff.1 hb
  set D : ℝ≥0 := max D₀.toNNReal 1
  have hD : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ∀ y ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      edist x y ≤ D := fun x hx y hy => by
    rw [edist_nndist, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nndist]
    exact (hD₀ hx hy).trans ((Real.le_coe_toNNReal D₀).trans (by simp [D]))
  set α := min α₁ α₂
  refine ⟨α, C₁ * (D : ℝ) ^ ((α₁ : ℝ) - α) + C₂ * (D : ℝ) ^ ((α₂ : ℝ) - α), lt_min hα₁ hα₂,
    (NNReal.coe_le_coe.2 (min_le_right _ _)).trans hα₂1, by positivity, ?_⟩
  intro a f F u g G K₀ K₁ h ha hf hF hug hu hgG hG hG0
  have hlam := h.pos
  -- `u = (u - w) + w`, where `w ∈ H¹₀(Ω)` carries the scalar datum and `u - w` the rest.
  obtain ⟨w, hw0, hw, huw⟩ := exists_mem_w1p0Submodule_forall_energyFormH1_eq_and_sub_eq h ha
    hb.measure_lt_top.ne hr hrn hf hu
  have huwg : u - w - g ∈ w1p0Submodule mu Omega 2 := by
    rw [sub_right_comm]
    exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1
      ((w1p0Submodule mu Omega 2).toSubmodule.sub_mem
        ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hug)
        ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hw0))
  obtain ⟨v₂, hv₂, hv₂H⟩ := hdiv h ha hF huwg huw hgG hG hG0
  refine ⟨v₂ + preciseRepresentative mu ((Omega : Set (EuclideanSpace ℝ ι)).indicator
    (W1p.value w)), ?_, ?_⟩
  · filter_upwards [W1p.ae_eq_preciseRepresentative_indicator w, W1p.value_sub_ae u w, hv₂]
      with x h₁ h₂ h₃
    rw [Pi.add_apply, ← h₁, ← h₃, h₂, Pi.sub_apply, sub_add_cancel]
  -- Both Hölder bounds at the common exponent `α`, added.
  have hsum := (hv₂H.of_le hD (min_le_right α₁ α₂)).add
    (((hscalar h ha hf hw0 hw).holderOnWith (Omega : Set (EuclideanSpace ℝ ι))).of_le hD
      (min_le_left α₁ α₂))
  refine hsum.mono_const ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  have hP : 0 ≤ (eLpNorm f r (mu.restrict Omega)).toReal / lam := by positivity
  have hQ : 0 ≤ (eLpNorm F q (mu.restrict Omega)).toReal / lam := by positivity
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity), mul_div_assoc]
  exact mul_add_mul_le hC₁.le hC₂.le (by positivity) (by positivity) hP hQ K₀.coe_nonneg
    K₁.coe_nonneg

end Set.IsLipschitzDomain
