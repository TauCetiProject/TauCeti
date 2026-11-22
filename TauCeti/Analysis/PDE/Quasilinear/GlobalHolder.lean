/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.Existence
public import TauCeti.Analysis.PDE.Regularity.Boundary.GeneralData
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Instances.Matrix

/-!
# Hölder continuous solutions of quasilinear Dirichlet problems

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded Lipschitz domain and let `A : Ω × ℝ → Mat(n + 1, ℝ)` be a
Carathéodory coefficient: `x ↦ A(x, s)` is measurable for every `s`, and `s ↦ A(x, s)` is
continuous for almost every `x`. Suppose that every `A(·, s)` is uniformly elliptic and bounded
with the same constants `0 < λ ≤ Λ`. Consider the quasilinear Dirichlet problem

`-div (A(x, u) ∇u) = f + div F` in `Ω`, `u = G` on `∂Ω`,

with `f ∈ Lʳ(Ω)`, `r > 1`, `r > (n + 1)/2`, `F ∈ L^q(Ω; ℝⁿ⁺¹)`, `q > 2`, `q > n + 1`, and boundary
values `G` bounded by `K₀` and `K₁`-Lipschitz on `Ω`, attained in the sense that `u - g ∈ H¹₀(Ω)`
for some `g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. Its weak form is

`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω f φ - ∫_Ω ⟨F, ∇φ⟩` for every `φ ∈ H¹₀(Ω)`.

This file proves that the problem has a weak solution that is Hölder continuous up to the
boundary, with a bound that does not depend on `A` beyond `λ` and `Λ` (in the
`Set.IsLipschitzDomain` namespace,
`exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_holderOnWith`):
there are `α ∈ (0, 1]` and `C`, depending only on `Ω`, `λ`, `Λ`, `r` and `q`, such that the
solution agrees almost everywhere on `Ω` with a function that is `α`-Hölder on `Ω` with constant

`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`.

Such a function extends uniquely to a Hölder function on the closure of `Ω`. No uniqueness is
claimed.

The estimate holds for every weak solution, in every dimension `n ≥ 1` and for every additive
Haar measure (`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_quasilinear`), whether or not
the problem has only one solution.

## The argument

The data define the functional `φ ↦ ∫_Ω f φ - ∫_Ω ⟨F, ∇φ⟩` on `H¹₀(Ω)`, continuous because
`r > 2 (n + 1)/(n + 3)` (`TauCeti.W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp`) and
`q ≥ 2` (`TauCeti.PDE.divergenceForcing`). Schauder's theorem gives a weak solution `u`
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`). It solves the
linear problem with the frozen coefficient `a(x) = A(x, u(x))`, which is measurable and uniformly
elliptic with the constants `λ, Λ`, so the global Hölder estimate for linear equations with
measurable coefficients
(`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_add_divergence`) applies to it. Its
exponent and constant were chosen before the coefficient, which is why the bound is uniform in
`A`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.29 (the global Hölder estimate) and Section 11.3 (quasilinear equations by
  Schauder's theorem, with Hölder estimates uniform in the frozen coefficient).
* M. Chipot, *Elliptic Equations: An Introductory Course*, Birkhäuser, 2009, Section 11.2.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Hölder continuity up to the boundary of weak solutions of quasilinear Dirichlet problems.**
Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a bounded Lipschitz domain, let `r > 1` with `r > n/2`, and let `q > 2`
with `q > n`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `Ω`, `λ`, `Λ`, `r`, `q` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `A` be a
Carathéodory coefficient on `Ω` with every `A(·, s)` uniformly elliptic with constants `λ, Λ`, let
`f ∈ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `G` be bounded by `K₀` and `K₁`-Lipschitz on `Ω`. Let
`u ∈ H¹(Ω)` be a weak solution of `-div (A(x, u) ∇u) = f + div F` with boundary values `G`:
`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω f φ - ∫_Ω F · ∇φ` for every `φ ∈ H¹₀(Ω)`, and `u - g ∈ H¹₀(Ω)` for some
`g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. Then `u` agrees almost everywhere on `Ω`
with a function that is `α`-Hölder on `Ω` with constant

`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`. -/
theorem exists_ae_eq_and_holderOnWith_quasilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {Omega : Opens (EuclideanSpace ℝ ι)}
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {lam Lam : ℝ} {r q : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧
      ∀ {A : EuclideanSpace ℝ ι → ℝ → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
        {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u g : W1p mu Omega 2}
        {G : EuclideanSpace ℝ ι → ℝ} {K₀ K₁ : ℝ≥0},
        (∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x => A x s) lam Lam) →
        (∀ s, AEStronglyMeasurable (fun x => A x s) (mu.restrict Omega)) →
        (∀ᵐ x ∂mu.restrict Omega, Continuous (A x)) →
        MemLp f r (mu.restrict Omega) →
        MemLp F q (mu.restrict Omega) →
        u - g ∈ w1p0Submodule mu Omega 2 →
        (∀ φ : W1p0 mu Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u (φ : W1p mu Omega 2) =
            ∫ x in Omega, f x * W1p.value (φ : W1p mu Omega 2) x ∂mu -
              ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu) →
        W1p.value g =ᵐ[mu.restrict Omega] G →
        LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι)) →
        (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |G x| ≤ K₀) →
        ∃ v : EuclideanSpace ℝ ι → ℝ, W1p.value u =ᵐ[mu.restrict Omega] v ∧
          HolderOnWith (C * ((eLpNorm f r (mu.restrict Omega)).toReal / lam +
            (eLpNorm F q (mu.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal α v Omega := by
  obtain ⟨α, C, hα, hα1, hC, hlin⟩ :=
    exists_ae_eq_and_holderOnWith_add_divergence (mu := mu) hΩ hb (lam := lam) (Lam := Lam) hr
      hrn hq hqn
  refine ⟨α, C, hα, hα1, hC, fun hA hAm hAc hf hF hug hu hgG hG hG0 => ?_⟩
  -- The coefficient frozen at `u` is measurable and uniformly elliptic with the constants `λ, Λ`.
  exact hlin (UniformlyEllipticOn.apply_of_forall hA _)
    ((Lp.aestronglyMeasurable _).apply_of_forall_of_continuousAt hAm
      (hAc.mono fun _ hx => hx.continuousAt)) hf hF hug hu hgG hG hG0

/-- **Hölder continuous solutions of the quasilinear Dirichlet problem.** Let `Ω ⊆ ℝⁿ⁺¹` be a
bounded Lipschitz domain, let `r > 1` with `r > (n + 1)/2`, and let `q > 2` with `q > n + 1`.
There are `α ∈ (0, 1]` and `C > 0`, depending only on `Ω`, `λ`, `Λ`, `r` and `q`, such that the
following holds. Let `A : ℝⁿ⁺¹ × ℝ → Mat(n + 1, ℝ)` be a Carathéodory coefficient on `Ω` with every
`A(·, s)` uniformly elliptic and bounded on `Ω` with the constants `λ, Λ`, let `f ∈ Lʳ(Ω)` and
`F ∈ L^q(Ω; ℝⁿ⁺¹)`, and let `G` be bounded by `K₀` and `K₁`-Lipschitz on `Ω`, with `g ∈ H¹(Ω)`
whose value is `G` almost everywhere on `Ω`. Then there is `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)`
solving `-div (A(x, u) ∇u) = f + div F` weakly,

`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω f φ - ∫_Ω ⟨F, ∇φ⟩` for every `φ ∈ H¹₀(Ω)`,

and agreeing almost everywhere on `Ω` with a function that is `α`-Hölder on `Ω` with constant
`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`.

No uniqueness is claimed. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_holderOnWith {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) {lam Lam : ℝ}
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (n : ℝ) + 1 < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (n : ℝ) + 1 < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧
      ∀ {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {g : W1p volume Omega 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {K₀ K₁ : ℝ≥0},
      (∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
        (fun x => A x s) lam Lam) →
      (∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega)) →
      (∀ᵐ x ∂volume.restrict Omega, Continuous (A x)) →
      MemLp f r (volume.restrict Omega) →
      MemLp F q (volume.restrict Omega) →
      W1p.value g =ᵐ[volume.restrict Omega] G →
      LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) →
      ∃ u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
        (∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ =
            (∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x) -
              ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫) ∧
        ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, W1p.value u =ᵐ[volume.restrict Omega] v ∧
          HolderOnWith (C * ((eLpNorm f r (volume.restrict Omega)).toReal / lam +
            (eLpNorm F q (volume.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal α v Omega := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  obtain ⟨α, C, hα, hα1, hC, hreg⟩ :=
    exists_ae_eq_and_holderOnWith_quasilinear (mu := volume) hΩ hb (lam := lam) (Lam := Lam) hr
      (by rwa [hcard]) hq (by rwa [hcard])
  refine ⟨α, C, hα, hα1, hC, fun {A f F g G K₀ K₁} hA hAm hAc hf hF hgG hG hG0 => ?_⟩
  have hfin : volume (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≠ ∞ := hb.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hfin
  -- The forcing `φ ↦ ∫_Ω f φ - ∫_Ω ⟨F, ∇φ⟩` is a continuous linear functional on `H¹₀(Ω)`.
  have hrn' : (Fintype.card (Fin (n + 1)) : ℝ) * (2 - r) < 2 * r :=
    mul_two_sub_lt_two_mul_of_lt_two_mul (Nat.cast_nonneg _) (by exact_mod_cast hr)
      (by rwa [hcard])
  obtain ⟨ℓ, hℓ⟩ := W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp hfin hr
    (by rwa [finrank_euclideanSpace]) hf
  have hF2 : MemLp F 2 (volume.restrict Omega) := hF.mono_exponent (by exact_mod_cast hq.le)
  obtain ⟨u, hug, hu⟩ := exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq hA hAm
    hAc hb g (ℓ + divergenceForcing (hF2.toLp F))
  have hu' : ∀ φ : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ =
        (∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x) -
          ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ := fun φ => by
    rw [hu φ, add_apply, hℓ φ, divergenceForcing_toLp_apply, ← sub_eq_add_neg]
  exact ⟨u, hug, hu', hreg hA hAm hAc hf hF hug hu' hgG hG hG0⟩

end Set.IsLipschitzDomain
