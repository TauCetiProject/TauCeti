/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Coboundary
import Mathlib.Algebra.DualNumber
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Linearised square-zero deformation cocycles and Lubin–Tate cocycles

Let `F(X, Y)` be a commutative formal group law over a commutative ring `A` with normalised
invariant differential `ω = P(T) dT` (`P(T) = F_X(0, T)⁻¹`), and let `I ⊆ A` be an ideal of square
zero (`I * I = ⊥`). Following §1 of Lubin and Tate, *Formal moduli for one-parameter formal Lie
groups* (1966), this file connects deformations of `F` modulo `I` to symmetric 2-cocycles of `F`
(`FormalGroup.IsSymmetricCocycle`) and constructs canonical symmetric 2-cocycles with prescribed
leading Lazard cocycle over every commutative ring.

## Main definitions

* `FormalGroup.deformationCocycle`: the linearised difference
  `Φ(X, Y) = P(F(X, Y)) · (G(X, Y) - F(X, Y))` of two formal group laws `F, G` over `A`.
* `FormalGroup.deformByCocycle`: the formal group law `F(X, Y) + F_X(0, F(X, Y)) · Φ(X, Y)`
  attached to a symmetric 2-cocycle `Φ` without constant term whose coefficients lie in a
  square-zero ideal `I`.
* `FormalGroup.deformationCocycleEquiv`: the equivalence (Lubin–Tate, Lemma 1.2) between
  commutative formal group laws congruent to `F` modulo `I` and symmetric 2-cocycles of `F` without
  constant term and with coefficients in `I`.
* `FormalGroup.lubinTateCocycle`: for any commutative formal group law `F` over a commutative ring
  `R` and `n : ℕ+`, the canonical symmetric 2-cocycle of `F` obtained by shifting the `n`-th
  polynomial generator of `TauCeti.LazardRing` by `ε` in `DualNumber LazardRing` and pushing
  forward along `LazardRing.lift` (Lubin–Tate, Lemma 1.3).

## Main results

* `FormalGroup.isSymmetricCocycle_deformationCocycle`: when `G ≡ F (mod I)` with `I * I = ⊥` and
  `F, G` are commutative, `F.deformationCocycle G` is a symmetric 2-cocycle of `F`.
* `FormalGroup.deformationCocycle_trans`: additivity of `deformationCocycle` across square-zero
  congruences.
* `FormalGroup.deformationCocycle_smul_eq_homDefect_𝔾ₐ` and
  `FormalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ`: an infinitesimal
  coordinate change `φ ≡ X (mod I)` shifts the deformation cocycle by the coboundary
  `F.homDefect 𝔾ₐ (P · (φ - X))`, characterising `I`-congruent coordinate equivalence
  (Lubin–Tate, Lemma 1.1).
* `FormalGroup.homogeneousComponent_lubinTateCocycle`: `F.lubinTateCocycle n` vanishes below total
  degree `n + 1` and has degree-`(n + 1)` homogeneous component equal to `C_(n + 1)`.
* `FormalGroup.IsSymmetricCocycle.existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ`: over a
  characteristic-`p` ring where `[p]_F` has order `pʰ` with unit leading coefficient, every
  symmetric 2-cocycle without constant term decomposes uniquely in the Lubin–Tate cocycle basis in
  degrees `p, p², …, p^(h - 1)` modulo coboundaries.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1.
* M. Hazewinkel, *Formal Groups and Applications*, Academic Press (1978), §22.
-/

public section

noncomputable section

open MvPowerSeries TauCeti

section IdealHelpers

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- Two multivariate power series with coefficients in a square-zero ideal multiply to zero. -/
private theorem mvPowerSeries_mul_eq_zero_of_coeff_mem {σ : Type*} (hI : I * I = ⊥)
    {f g : MvPowerSeries σ A} (hf : ∀ d, coeff d f ∈ I) (hg : ∀ d, coeff d g ∈ I) :
    f * g = 0 := by
  classical
  ext d
  rw [coeff_mul, map_zero]
  refine Finset.sum_eq_zero fun pq _ ↦ ?_
  rw [← Ideal.mem_bot, ← hI]
  exact Ideal.mul_mem_mul (hf pq.1) (hg pq.2)

/-- Multiplying by any series preserves having all coefficients in an ideal `I`. -/
private theorem coeff_mul_mem_of_right {σ : Type*} (P : MvPowerSeries σ A)
    {f : MvPowerSeries σ A} (hf : ∀ d, coeff d f ∈ I) (d : σ →₀ ℕ) :
    coeff d (P * f) ∈ I := by
  classical
  rw [coeff_mul]
  exact Ideal.sum_mem I fun pq _ ↦ I.mul_mem_left _ (hf pq.2)

/-- One-variable version of `coeff_mul_mem_of_right`. -/
private theorem powerSeries_coeff_mul_mem_of_right (P : PowerSeries A)
    {f : PowerSeries A} (hf : ∀ n, PowerSeries.coeff n f ∈ I) (n : ℕ) :
    PowerSeries.coeff n (P * f) ∈ I := by
  rw [PowerSeries.coeff_mul]
  exact Ideal.sum_mem I fun pq _ ↦ I.mul_mem_left _ (hf pq.2)

/-- Substituting into a series with coefficients in `I` keeps all coefficients in `I`. -/
private theorem coeff_subst_mem_of_coeff_mem {σ τ : Type*} {a : σ → MvPowerSeries τ A}
    (ha : HasSubst a) {f : MvPowerSeries σ A} (hf : ∀ d, coeff d f ∈ I) (d : τ →₀ ℕ) :
    coeff d (f.subst a) ∈ I :=
  Ideal.span_le.mpr (Set.range_subset_iff.mpr hf) (coeff_subst_mem_span ha d)

private theorem coeff_powerSeries_subst_mem_of_coeff_mem {τ : Type*} {a : MvPowerSeries τ A}
    (ha : PowerSeries.HasSubst a) {f : PowerSeries A} (hf : ∀ n, PowerSeries.coeff n f ∈ I)
    (d : τ →₀ ℕ) : coeff d (PowerSeries.subst a f) ∈ I := by
  refine Ideal.span_le.mpr (Set.range_subset_iff.mpr fun e ↦ ?_) (coeff_subst_mem_span ha.const d)
  rw [← PowerSeries.coeff_def rfl]
  exact hf (e ())

end IdealHelpers

namespace FormalGroup

/-! ### 1. The linearised deformation cocycle -/

section DeformationCocycle

variable {A B : Type*} [CommRing A] [CommRing B]

/-- `F_X(0, T)`, the inverse of `F.invariantDifferential` in `PowerSeries A`. -/
private noncomputable abbrev invInvariantDifferential (F : FormalGroup A) : PowerSeries A :=
  subst ![(0 : PowerSeries A), PowerSeries.X] (pderiv 0 F.toPowerSeries)

private theorem subst_invariantDifferential_mul_inv {σ : Type*} (F : FormalGroup A)
    {x : MvPowerSeries σ A} (hx : PowerSeries.HasSubst x) :
    PowerSeries.subst x F.invariantDifferential *
      PowerSeries.subst x F.invInvariantDifferential = 1 := by
  rw [← PowerSeries.subst_mul hx, F.invariantDifferential_mul_subst_pderiv,
    ← PowerSeries.coe_substAlgHom hx, map_one]

private theorem subst_invInvariantDifferential_mul {σ : Type*} (F : FormalGroup A)
    {x : MvPowerSeries σ A} (hx : PowerSeries.HasSubst x) :
    PowerSeries.subst x F.invInvariantDifferential *
      PowerSeries.subst x F.invariantDifferential = 1 := by
  rw [mul_comm, F.subst_invariantDifferential_mul_inv hx]

/-- **The linearised deformation cocycle** of a pair of formal group laws `F, G` over `A`:
`Φ(X, Y) = P(F(X, Y)) · (G(X, Y) - F(X, Y))`, where `ω = P(T) dT` is the normalised invariant
differential of `F` (`FormalGroup.invariantDifferential`). When `G - F` has coefficients in a
square-zero ideal and `F, G` are commutative, `Φ` is a symmetric 2-cocycle of `F`. -/
noncomputable def deformationCocycle (F G : FormalGroup A) : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst F.toPowerSeries F.invariantDifferential *
    (G.toPowerSeries - F.toPowerSeries)

/-- The deformation cocycle of `F` with itself vanishes. -/
@[simp]
theorem deformationCocycle_self (F : FormalGroup A) : F.deformationCocycle F = 0 := by
  simp [deformationCocycle]

/-- The deformation cocycle has zero constant coefficient. -/
@[simp]
theorem constantCoeff_deformationCocycle (F G : FormalGroup A) :
    constantCoeff (F.deformationCocycle G) = 0 := by
  simp [deformationCocycle, F.zero_constantCoeff, G.zero_constantCoeff]

/-- Over the additive formal group law `𝔾ₐ`, whose invariant differential is `dT`, the deformation
cocycle of `G` is the nonlinear difference `G(X, Y) - (X + Y)`. -/
@[simp]
theorem deformationCocycle_𝔾ₐ (G : FormalGroup A) :
    (𝔾ₐ : FormalGroup A).deformationCocycle G = G.toPowerSeries - (X 0 + X 1) := by
  have h0 : constantCoeff (𝔾ₐ : FormalGroup A).toPowerSeries = 0 := 𝔾ₐ.zero_constantCoeff
  rw [deformationCocycle, invariantDifferential_𝔾ₐ,
    ← PowerSeries.coe_substAlgHom (.of_constantCoeff_zero h0), map_one, one_mul, 𝔾ₐ_toPowerSeries]

/-- The deformation cocycle commutes with change of coefficient ring. -/
@[simp]
theorem map_deformationCocycle (f : A →+* B) (F G : FormalGroup A) :
    MvPowerSeries.map f (F.deformationCocycle G) =
      (F.map f).deformationCocycle (G.map f) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  rw [deformationCocycle, deformationCocycle, map_mul, map_sub,
    PowerSeries.map_subst hF, F.map_invariantDifferential, F.map_toPowerSeries, G.map_toPowerSeries]

/-- Recovering `G - F` from `F.deformationCocycle G` via `F_X(0, F(X, Y))`. -/
private theorem sub_toPowerSeries_eq_mul_deformationCocycle (F G : FormalGroup A) :
    G.toPowerSeries - F.toPowerSeries =
      PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * F.deformationCocycle G := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  rw [deformationCocycle, ← mul_assoc, F.subst_invInvariantDifferential_mul hF, one_mul]

/-- For a fixed base law `F`, `G ↦ F.deformationCocycle G` is injective over any commutative ring,
since `P(F(X, Y))` is a unit in `A⟦X, Y⟧`. -/
theorem deformationCocycle_injective (F : FormalGroup A) :
    Function.Injective F.deformationCocycle := by
  intro G₁ G₂ h
  ext d
  have hsub : G₁.toPowerSeries - F.toPowerSeries = G₂.toPowerSeries - F.toPowerSeries := by
    rw [F.sub_toPowerSeries_eq_mul_deformationCocycle G₁,
      F.sub_toPowerSeries_eq_mul_deformationCocycle G₂, h]
  exact sub_left_inj.mp hsub ▸ rfl

/-- The deformation cocycle `F.deformationCocycle G` has coefficients in an ideal `I` if and only
if `G - F` has coefficients in `I`. -/
theorem coeff_deformationCocycle_mem_iff {F G : FormalGroup A} {I : Ideal A} :
    (∀ d, coeff d (F.deformationCocycle G) ∈ I) ↔
      ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I := by
  refine ⟨fun h d ↦ ?_, fun h d ↦ coeff_mul_mem_of_right _ h d⟩
  rw [F.sub_toPowerSeries_eq_mul_deformationCocycle G]
  exact coeff_mul_mem_of_right _ h d

/-- The deformation cocycle vanishes below total degree `2`. -/
theorem two_le_order_deformationCocycle (F G : FormalGroup A) :
    ((2 : ℕ) : ℕ∞) ≤ (F.deformationCocycle G).order := by
  have hsub : G.toPowerSeries - F.toPowerSeries = -(F.homDefect G PowerSeries.X) := by
    rw [homDefect_X, neg_sub]
  have hord : ((2 : ℕ) : ℕ∞) ≤ (G.toPowerSeries - F.toPowerSeries).order := by
    rw [hsub, order_neg]
    exact F.two_le_order_homDefect_X (G := G)
  rw [deformationCocycle]
  exact (_root_.zero_add _).symm.le.trans ((add_le_add zero_le hord).trans le_order_mul)

/-- **Additivity of the deformation cocycle across square-zero steps.** If `G ≡ F (mod I)` and
`H ≡ G (mod I)` for an ideal `I` with `I * I = ⊥`, then
`F.deformationCocycle H = F.deformationCocycle G + G.deformationCocycle H`. -/
theorem deformationCocycle_trans {F G H : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I)
    (hGH : ∀ d, coeff d (H.toPowerSeries - G.toPowerSeries) ∈ I) :
    F.deformationCocycle H = F.deformationCocycle G + G.deformationCocycle H := by
  set π := Ideal.Quotient.mk I
  have hmap : G.map π = F.map π := by
    ext d
    rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, coeff_map, coeff_map,
      ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hFG d
  have hP : ∀ d, coeff d (PowerSeries.subst G.toPowerSeries G.invariantDifferential -
      PowerSeries.subst F.toPowerSeries F.invariantDifferential) ∈ I := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub,
      PowerSeries.map_subst (.of_constantCoeff_zero G.zero_constantCoeff),
      PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
      G.map_invariantDifferential, F.map_invariantDifferential,
      ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries, hmap, sub_self, map_zero]
  have hzero := mvPowerSeries_mul_eq_zero_of_coeff_mem hI hP hGH
  simp only [deformationCocycle]
  linear_combination -hzero

/-- Reversing the roles of `F` and `G` negates the deformation cocycle when `G ≡ F (mod I)` and
`I * I = ⊥`. -/
theorem deformationCocycle_symm {F G : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    G.deformationCocycle F = -F.deformationCocycle G := by
  have hGF : ∀ d, coeff d (F.toPowerSeries - G.toPowerSeries) ∈ I := fun d ↦ by
    rw [← neg_sub, map_neg]
    exact I.neg_mem (hFG d)
  have h := deformationCocycle_trans hI hFG hGF
  rw [deformationCocycle_self] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- First-order expansion of `(F + Δ)((F + Δ)(X₀, X₁), X₂) - (F + Δ)(X₀, (F + Δ)(X₁, X₂))` when `Δ`
has coefficients in a square-zero ideal `I`. -/
private theorem assocDefect_add_eq {I : Ideal A} (hI : I * I = ⊥) (F : FormalGroup A)
    (Δ : MvPowerSeries (Fin 2) A) (hΔI : ∀ d, coeff d Δ ∈ I) :
    let S := F.toPowerSeries + Δ
    let F₀₁ := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
    let F₁₂ := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
    S.subst ![S.subst ![X 0, X 1], X 2] - S.subst ![X 0, S.subst ![X 1, X 2]] =
      Δ.subst ![X 0, X 1] * (pderiv 0 F.toPowerSeries).subst ![F₀₁, X 2] + Δ.subst ![F₀₁, X 2] -
        Δ.subst ![X 0, F₁₂] -
        Δ.subst ![X 1, X 2] * (pderiv 1 F.toPowerSeries).subst ![X 0, F₁₂] := by
  intro S F₀₁ F₁₂
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := A) i
  have h01 := hasSubst_finTwo (hX 0) (hX 1)
  have h12 := hasSubst_finTwo (hX 1) (hX 2)
  have haL := hasSubst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2)
  have haR := hasSubst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2))
  set δL : Fin 2 → MvPowerSeries (Fin 3) A := ![Δ.subst ![X 0, X 1], 0]
  set δR : Fin 2 → MvPowerSeries (Fin 3) A := ![0, Δ.subst ![X 1, X 2]]
  have hδLI (s : Fin 2) (d : Fin 3 →₀ ℕ) : coeff d (δL s) ∈ I := by
    fin_cases s
    · exact coeff_subst_mem_of_coeff_mem h01 hΔI d
    · simp [δL]
  have hδRI (s : Fin 2) (d : Fin 3 →₀ ℕ) : coeff d (δR s) ∈ I := by
    fin_cases s
    · simp [δR]
    · exact coeff_subst_mem_of_coeff_mem h12 hΔI d
  have hhL (i j : Fin 2) : δL i * δL j = 0 :=
    mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδLI i) (hδLI j)
  have hhR (i j : Fin 2) : δR i * δR j = 0 :=
    mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδRI i) (hδRI j)
  have heqL : (![S.subst ![X 0, X 1], X 2] : Fin 2 → MvPowerSeries (Fin 3) A) =
      ![F₀₁, X 2] + δL := by funext s; fin_cases s <;> simp [S, F₀₁, δL, subst_add h01]
  have heqR : (![X 0, S.subst ![X 1, X 2]] : Fin 2 → MvPowerSeries (Fin 3) A) =
      ![X 0, F₁₂] + δR := by funext s; fin_cases s <;> simp [S, F₁₂, δR, subst_add h12]
  have h2L : ∑ i, δL i * (pderiv i Δ).subst ![F₀₁, X 2] = 0 :=
    Finset.sum_eq_zero fun i _ ↦ mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδLI i) fun d ↦
      coeff_subst_mem_of_coeff_mem haL
        (fun e ↦ by rw [coeff_pderiv]; exact I.mul_mem_right _ (hΔI _)) d
  have h2R : ∑ i, δR i * (pderiv i Δ).subst ![X 0, F₁₂] = 0 :=
    Finset.sum_eq_zero fun i _ ↦ mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδRI i) fun d ↦
      coeff_subst_mem_of_coeff_mem haR
        (fun e ↦ by rw [coeff_pderiv]; exact I.mul_mem_right _ (hΔI _)) d
  rw [heqL, heqR, subst_add (haL.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhL])),
    subst_add (haR.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhR])),
    subst_add_of_mul_eq_zero haL hhL F.toPowerSeries, subst_add_of_mul_eq_zero haL hhL Δ, h2L,
    subst_add_of_mul_eq_zero haR hhR F.toPowerSeries, subst_add_of_mul_eq_zero haR hhR Δ, h2R,
    Fin.sum_univ_two, Fin.sum_univ_two, ← F.assoc]
  simp only [δL, δR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zero_mul, _root_.add_zero]
  ring

/-- Multiplying the associativity defect of `S = F + F_X(0, F) · Φ` by `P(F(F(X₀, X₁), X₂))`
recovers the 2-cocycle defect `Φ(X₀, X₁) + Φ(F(X₀, X₁), X₂) - Φ(X₀, F(X₁, X₂)) - Φ(X₁, X₂)`. -/
private theorem mul_assocDefect_add_eq_cocycle {I : Ideal A} (hI : I * I = ⊥)
    (F : FormalGroup A) [F.IsComm] {Φ : MvPowerSeries (Fin 2) A} (hΦI : ∀ d, coeff d Φ ∈ I) :
    let Δ := PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * Φ
    let S := F.toPowerSeries + Δ
    let F₀₁ := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
    let F₁₂ := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
    PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
        (S.subst ![S.subst ![X 0, X 1], X 2] - S.subst ![X 0, S.subst ![X 1, X 2]]) =
      Φ.subst ![X 0, X 1] + Φ.subst ![F₀₁, X 2] - Φ.subst ![X 0, F₁₂] - Φ.subst ![X 1, X 2] := by
  intro Δ S F₀₁ F₁₂
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := A) i
  have h01 := hasSubst_finTwo (hX 0) (hX 1)
  have h12 := hasSubst_finTwo (hX 1) (hX 2)
  have haL := hasSubst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2)
  have haR := hasSubst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2))
  have hPΔ : PowerSeries.subst F.toPowerSeries F.invariantDifferential * Δ = Φ := by
    dsimp only [Δ]
    rw [← mul_assoc, F.subst_invariantDifferential_mul_inv
      (.of_constantCoeff_zero F.zero_constantCoeff), one_mul]
  -- After any valid substitution `b`, multiplying `Δ(b)` by `P(F(b))` recovers `Φ(b)`.
  have hPΔ_sub {b : Fin 2 → MvPowerSeries (Fin 3) A} (hb : HasSubst b) :
      PowerSeries.subst (F.toPowerSeries.subst b) F.invariantDifferential * Δ.subst b =
        Φ.subst b := by
    rw [← subst_powerSeriesSubst hb (.of_constantCoeff_zero F.zero_constantCoeff),
      ← subst_mul hb, hPΔ]
  -- Evaluate `P(F(U, V)) · ∂₀F(U, V) = P(U)` and its ∂₁ analogue at `(F₀₁, X₂)` and `(X₀, F₁₂)`.
  have inv0 := congrArg (subst ![F₀₁, X 2]) F.subst_invariantDifferential_mul_pderiv
  rw [subst_mul haL, subst_powerSeriesSubst haL (.of_constantCoeff_zero F.zero_constantCoeff),
    subst_powerSeriesSubst haL (PowerSeries.HasSubst.X 0), subst_X haL,
    Matrix.cons_val_zero] at inv0
  have inv1 := congrArg (subst ![X 0, F₁₂]) F.subst_invariantDifferential_mul_pderiv_one
  rw [subst_mul haR, subst_powerSeriesSubst haR (.of_constantCoeff_zero F.zero_constantCoeff),
    subst_powerSeriesSubst haR (PowerSeries.HasSubst.X 1), subst_X haR,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ← F.assoc] at inv1
  -- Expand the associativity defect to first order and simplify using `inv0` and `inv1`.
  have had := assocDefect_add_eq hI F Δ (coeff_mul_mem_of_right _ hΦI)
  dsimp only at had
  rw [had]
  calc PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
        (Δ.subst ![X 0, X 1] * (pderiv 0 F.toPowerSeries).subst ![F₀₁, X 2] +
          Δ.subst ![F₀₁, X 2] - Δ.subst ![X 0, F₁₂] -
          Δ.subst ![X 1, X 2] * (pderiv 1 F.toPowerSeries).subst ![X 0, F₁₂])
      = (PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
          (pderiv 0 F.toPowerSeries).subst ![F₀₁, X 2]) * Δ.subst ![X 0, X 1] +
        PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
          Δ.subst ![F₀₁, X 2] -
        PowerSeries.subst (F.toPowerSeries.subst ![X 0, F₁₂]) F.invariantDifferential *
          Δ.subst ![X 0, F₁₂] -
        (PowerSeries.subst (F.toPowerSeries.subst ![F₀₁, X 2]) F.invariantDifferential *
          (pderiv 1 F.toPowerSeries).subst ![X 0, F₁₂]) * Δ.subst ![X 1, X 2] := by
        rw [F.assoc]
        ring
    _ = _ := by rw [inv0, inv1, hPΔ_sub h01, hPΔ_sub haL, hPΔ_sub haR, hPΔ_sub h12]

/-- **Lubin–Tate, Lemma 1.2 (forward direction).** If `F` and `G` are commutative formal group laws
over `A` that agree modulo a square-zero ideal `I` (`I * I = ⊥`), then `F.deformationCocycle G` is
a symmetric 2-cocycle of `F`. -/
theorem isSymmetricCocycle_deformationCocycle (F G : FormalGroup A) [F.IsComm] [G.IsComm]
    {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    F.IsSymmetricCocycle (F.deformationCocycle G) where
  subst_swap := by
    have hsw : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) A) := HasSubst.X_X
    rw [deformationCocycle, subst_mul hsw, subst_sub hsw,
      subst_powerSeriesSubst hsw (.of_constantCoeff_zero F.zero_constantCoeff),
      ← IsComm.comm (F := F), ← IsComm.comm (F := G)]
  subst_add_subst_eq := by
    have hΦI : ∀ d, coeff d (F.deformationCocycle G) ∈ I :=
      coeff_deformationCocycle_mem_iff.mpr hFG
    have hG : G.toPowerSeries = F.toPowerSeries +
        PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * F.deformationCocycle G := by
      rw [← F.sub_toPowerSeries_eq_mul_deformationCocycle G, add_sub_cancel]
    have h := mul_assocDefect_add_eq_cocycle hI F hΦI
    dsimp only at h
    rw [← hG, G.assoc, sub_self, mul_zero] at h
    linear_combination -h

/-- **Lubin–Tate, Lemma 1.2 (inverse construction).** Given a commutative formal group law `F` over
`A`, an ideal `I` with `I * I = ⊥`, and a symmetric 2-cocycle `Φ` of `F` without constant term whose
coefficients lie in `I`, `F(X, Y) + F_X(0, F(X, Y)) · Φ(X, Y)` is a formal group law over `A`. -/
noncomputable def deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : FormalGroup A where
  toPowerSeries := F.toPowerSeries +
    PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * Φ
  zero_constantCoeff := by simp [F.zero_constantCoeff, hΦ₀]
  lin_coeff_X := by
    have hord : ((2 : ℕ) : ℕ∞) ≤
        (PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * Φ).order :=
      (_root_.zero_add _).symm.le.trans
        ((add_le_add zero_le (hΦ.two_le_order hΦ₀)).trans le_order_mul)
    rw [map_add, F.lin_coeff_X, coeff_of_lt_order (lt_of_lt_of_le (by simp) hord), _root_.add_zero]
  lin_coeff_Y := by
    have hord : ((2 : ℕ) : ℕ∞) ≤
        (PowerSeries.subst F.toPowerSeries F.invInvariantDifferential * Φ).order :=
      (_root_.zero_add _).symm.le.trans
        ((add_le_add zero_le (hΦ.two_le_order hΦ₀)).trans le_order_mul)
    rw [map_add, F.lin_coeff_Y, coeff_of_lt_order (lt_of_lt_of_le (by simp) hord), _root_.add_zero]
  assoc := by
    have h := mul_assocDefect_add_eq_cocycle hI F hΦI
    dsimp only at h
    have hcoc : Φ.subst ![X 0, X 1] +
        Φ.subst ![F.toPowerSeries.subst ![X 0, X 1], (X 2 : MvPowerSeries (Fin 3) A)] -
        Φ.subst ![X 0, F.toPowerSeries.subst ![X 1, X 2]] - Φ.subst ![X 1, X 2] = 0 := by
      rw [hΦ.subst_add_subst_eq]
      abel
    rw [hcoc] at h
    have hF3 : PowerSeries.HasSubst
        (F.toPowerSeries.subst ![F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1],
          X 2]) :=
      F.hasSubst_subst_pair (F.hasSubst_subst_pair (PowerSeries.HasSubst.X 0)
        (PowerSeries.HasSubst.X 1)) (PowerSeries.HasSubst.X 2)
    have hzero := congrArg
      (PowerSeries.subst (F.toPowerSeries.subst
        ![F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2])
        F.invInvariantDifferential * ·) h
    rw [mul_zero, ← mul_assoc, F.subst_invInvariantDifferential_mul hF3, one_mul] at hzero
    exact sub_eq_zero.mp hzero

/-- The underlying power series of `F.deformByCocycle hI hΦ hΦ₀ hΦI`. -/
@[simp]
theorem toPowerSeries_deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ)
    (hΦ₀ : constantCoeff Φ = 0) (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hΦ hΦ₀ hΦI).toPowerSeries =
      F.toPowerSeries +
        PowerSeries.subst F.toPowerSeries
          (subst ![(0 : PowerSeries A), PowerSeries.X] (pderiv 0 F.toPowerSeries)) * Φ :=
  (rfl)

/-- A formal group law constructed from a symmetric 2-cocycle is commutative. -/
instance instIsCommDeformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : (F.deformByCocycle hI hΦ hΦ₀ hΦI).IsComm where
  comm := by
    have hsw : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) A) := HasSubst.X_X
    rw [toPowerSeries_deformByCocycle, subst_add hsw, subst_mul hsw,
      subst_powerSeriesSubst hsw (.of_constantCoeff_zero F.zero_constantCoeff),
      ← IsComm.comm (F := F), hΦ.subst_swap]

/-- The deformation cocycle of `F.deformByCocycle hI hΦ hΦ₀ hΦI` relative to `F` is `Φ`. -/
@[simp]
theorem deformationCocycle_deformByCocycle (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.IsSymmetricCocycle Φ)
    (hΦ₀ : constantCoeff Φ = 0) (hΦI : ∀ d, coeff d Φ ∈ I) :
    F.deformationCocycle (F.deformByCocycle hI hΦ hΦ₀ hΦI) = Φ := by
  rw [deformationCocycle, toPowerSeries_deformByCocycle, add_sub_cancel_left, ← mul_assoc,
    F.subst_invariantDifferential_mul_inv (.of_constantCoeff_zero F.zero_constantCoeff), one_mul]

/-- Deforming `F` by `F.deformationCocycle G` recovers `G`. -/
theorem deformByCocycle_deformationCocycle (F G : FormalGroup A) [F.IsComm] [G.IsComm]
    {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I) :
    F.deformByCocycle hI (F.isSymmetricCocycle_deformationCocycle G hI hFG)
      (F.constantCoeff_deformationCocycle G)
      (coeff_deformationCocycle_mem_iff.mpr hFG) = G := by
  ext d
  rw [toPowerSeries_deformByCocycle, ← invInvariantDifferential,
    ← F.sub_toPowerSeries_eq_mul_deformationCocycle G, add_sub_cancel]

/-- **Lubin–Tate, Lemma 1.2.** Over a ring `A` with a square-zero ideal `I` (`I * I = ⊥`),
commutative formal group laws `G` congruent to `F` modulo `I` correspond bijectively to symmetric
2-cocycles `Φ` of `F` without constant term whose coefficients lie in `I`. -/
noncomputable def deformationCocycleEquiv (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) :
    {G : FormalGroup A // G.IsComm ∧ ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I} ≃
      {Φ : MvPowerSeries (Fin 2) A //
        F.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧ ∀ d, coeff d Φ ∈ I} where
  toFun G :=
    have := G.2.1
    ⟨F.deformationCocycle G.1, F.isSymmetricCocycle_deformationCocycle G.1 hI G.2.2,
      F.constantCoeff_deformationCocycle G.1, coeff_deformationCocycle_mem_iff.mpr G.2.2⟩
  invFun Φ :=
    ⟨F.deformByCocycle hI Φ.2.1 Φ.2.2.1 Φ.2.2.2, inferInstance, fun d ↦ by
      rw [toPowerSeries_deformByCocycle, add_sub_cancel_left]
      exact coeff_mul_mem_of_right _ Φ.2.2.2 d⟩
  left_inv G := by
    have := G.2.1
    exact Subtype.ext (F.deformByCocycle_deformationCocycle G.1 hI G.2.2)
  right_inv Φ := Subtype.ext (F.deformationCocycle_deformByCocycle hI Φ.2.1 Φ.2.2.1 Φ.2.2.2)

/-- Evaluating `deformationCocycleEquiv` on `G` computes `F.deformationCocycle G`. -/
@[simp]
theorem deformationCocycleEquiv_apply_coe (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥)
    (G : {G : FormalGroup A // G.IsComm ∧ ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I}) :
    (F.deformationCocycleEquiv hI G).val = F.deformationCocycle G.val :=
  (rfl)

/-- Evaluating the inverse of `deformationCocycleEquiv` on `Φ` constructs `deformByCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_symm_apply_coe (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥)
    (Φ : {Φ : MvPowerSeries (Fin 2) A //
      F.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧ ∀ d, coeff d Φ ∈ I}) :
    ((F.deformationCocycleEquiv hI).symm Φ).val =
      F.deformByCocycle hI Φ.2.1 Φ.2.2.1 Φ.2.2.2 :=
  (rfl)

end DeformationCocycle

/-! ### 2. Infinitesimal coordinate changes and coboundaries -/

section CoordinateChange

variable {A : Type*} [CommRing A]

/-- If `G ≡ F (mod I)` and `g` has coefficients in `I` with `I * I = ⊥`, then the coboundaries of
`g` along `G` and `F` coincide. -/
theorem homDefect_𝔾ₐ_eq_of_coeff_mem {F G : FormalGroup A} {I : Ideal A} (hI : I * I = ⊥)
    (hFG : ∀ d, coeff d (G.toPowerSeries - F.toPowerSeries) ∈ I)
    {g : PowerSeries A} (hgI : ∀ n, PowerSeries.coeff n g ∈ I) :
    G.homDefect 𝔾ₐ g = F.homDefect 𝔾ₐ g := by
  have hG := (PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff).const
  have hF := (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff).const
  rw [homDefect_𝔾ₐ, homDefect_𝔾ₐ, PowerSeries.subst_def G.toPowerSeries,
    PowerSeries.subst_def F.toPowerSeries,
    subst_eq_subst_of_coeff_mem hG hF (fun _ ↦ hFG) fun e x hx ↦ ?_]
  rw [← PowerSeries.coeff_def rfl, ← Ideal.mem_bot, ← hI]
  exact Ideal.mul_mem_mul (hgI (e ())) hx

/-- If `φ - X` has coefficients in an ideal `I`, then `(φ • F) - F` also has coefficients in `I`. -/
private theorem coeff_smul_sub_mem {I : Ideal A} (F : FormalGroup A) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I)
    (d : Fin 2 →₀ ℕ) : coeff d ((φ • F).toPowerSeries - F.toPowerSeries) ∈ I := by
  set π := Ideal.Quotient.mk I
  have hφ1 : FormalCoordinate.map π φ = 1 := by
    ext n
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      PowerSeries.coeff_map, ← PowerSeries.map_X π, PowerSeries.coeff_map, ← sub_eq_zero,
      ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hφ n
  have hmap : (φ • F).map π = F.map π := by rw [map_smul, hφ1, one_smul]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, ← FormalGroup.map_toPowerSeries,
    ← FormalGroup.map_toPowerSeries, hmap, sub_self, map_zero]

/-- **Lubin–Tate, Lemma 1.1 (coboundary of an infinitesimal coordinate change).** Let `I` be an
ideal of `A` with `I * I = ⊥`, let `F` be a commutative formal group law over `A`, and let `φ` be a
formal coordinate with `φ(T) ≡ T (mod I)`. Then the deformation cocycle of `φ • F` relative to `F`
is the coboundary `F.homDefect 𝔾ₐ (P · (φ - X))`, where `P` is `F.invariantDifferential`. -/
theorem deformationCocycle_smul_eq_homDefect_𝔾ₐ (F : FormalGroup A) [F.IsComm] {I : Ideal A}
    (hI : I * I = ⊥) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) :
    F.deformationCocycle (φ • F) =
      F.homDefect 𝔾ₐ (F.invariantDifferential * (φ.toPowerSeries - PowerSeries.X)) := by
  set δ := φ.toPowerSeries - PowerSeries.X
  set Δ := (φ • F).toPowerSeries - F.toPowerSeries
  have hΔ_def : (φ • F).toPowerSeries - F.toPowerSeries = Δ := rfl
  have hΔI : ∀ d, coeff d Δ ∈ I := F.coeff_smul_sub_mem hφ
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := A) i
  have hhom := subst_toPowerSeries_eq_subst_smul_toPowerSeries φ F
  -- Write `φ(X) = X + δ(X)` and `(φ • F)(X, Y) = F(X, Y) + Δ(X, Y)` with `δ, Δ ≡ 0 (mod I)`.
  have hφeq : φ.toPowerSeries = PowerSeries.X + δ := by simp [δ]
  have hFsmul : (φ • F).toPowerSeries = F.toPowerSeries + Δ := by simp [Δ]
  set δv : Fin 2 → MvPowerSeries (Fin 2) A :=
    ![PowerSeries.subst (X 0) δ, PowerSeries.subst (X 1) δ]
  have hδvI (i : Fin 2) (d : Fin 2 →₀ ℕ) : coeff d (δv i) ∈ I := by
    fin_cases i <;> exact coeff_powerSeries_subst_mem_of_coeff_mem (hX _) hφ d
  have hh (i j : Fin 2) : δv i * δv j = 0 :=
    mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδvI i) (hδvI j)
  have harg : (![PowerSeries.subst (X 0) φ.toPowerSeries,
      PowerSeries.subst (X 1) φ.toPowerSeries] : Fin 2 → MvPowerSeries (Fin 2) A) = X + δv := by
    funext i
    fin_cases i <;>
      simp [hφeq, δv, PowerSeries.subst_add (hX _), PowerSeries.subst_X (hX _)]
  -- Since `I * I = ⊥`, `Δ(X + δv) = Δ` and `F(X + δv) = F + δ(X₀) ∂₀F + δ(X₁) ∂₁F`.
  have hΔsub : Δ.subst (X + δv) = Δ := by
    rw [subst_X_add_of_mul_eq_zero hh]
    suffices ∑ i, δv i * pderiv i Δ = 0 by rw [this, _root_.add_zero]
    refine Finset.sum_eq_zero fun i _ ↦
      mvPowerSeries_mul_eq_zero_of_coeff_mem hI (hδvI i) fun d ↦ ?_
    rw [coeff_pderiv]
    exact I.mul_mem_right _ (hΔI _)
  rw [harg, hFsmul, hφeq, PowerSeries.subst_add hF, PowerSeries.subst_X hF,
    subst_add (HasSubst.X.add (.of_sq_eq_zero fun i ↦ by rw [sq, hh])),
    subst_X_add_of_mul_eq_zero hh, hΔsub, Fin.sum_univ_two] at hhom
  have hΔeq : Δ = PowerSeries.subst F.toPowerSeries δ -
      PowerSeries.subst (X 0) δ * pderiv 0 F.toPowerSeries -
      PowerSeries.subst (X 1) δ * pderiv 1 F.toPowerSeries := by
    simp only [δv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hhom
    linear_combination -hhom
  -- Multiply by `P(F(X₀, X₁))` and apply the invariance of `ω` to obtain `homDefect 𝔾ₐ (P · δ)`.
  rw [deformationCocycle, hΔ_def, hΔeq, homDefect_𝔾ₐ, PowerSeries.subst_mul hF,
    PowerSeries.subst_mul (hX 0), PowerSeries.subst_mul (hX 1)]
  calc PowerSeries.subst F.toPowerSeries F.invariantDifferential *
        (PowerSeries.subst F.toPowerSeries δ -
          PowerSeries.subst (X 0) δ * pderiv 0 F.toPowerSeries -
          PowerSeries.subst (X 1) δ * pderiv 1 F.toPowerSeries)
      = PowerSeries.subst F.toPowerSeries F.invariantDifferential *
          PowerSeries.subst F.toPowerSeries δ -
        (PowerSeries.subst F.toPowerSeries F.invariantDifferential * pderiv 0 F.toPowerSeries) *
          PowerSeries.subst (X 0) δ -
        (PowerSeries.subst F.toPowerSeries F.invariantDifferential * pderiv 1 F.toPowerSeries) *
          PowerSeries.subst (X 1) δ := by ring
    _ = _ := by
        rw [F.subst_invariantDifferential_mul_pderiv, F.subst_invariantDifferential_mul_pderiv_one]

/-- For an infinitesimal coordinate `φ` (`φ ≡ X (mod I)` with `I * I = ⊥`), `φ • F = G` if and only
if `F.deformationCocycle G` is the coboundary of `F.invariantDifferential * (φ - X)`. -/
theorem smul_eq_iff_deformationCocycle_eq_homDefect_𝔾ₐ (F G : FormalGroup A) [F.IsComm]
    {I : Ideal A} (hI : I * I = ⊥) {φ : FormalCoordinate A}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) :
    φ • F = G ↔
      F.deformationCocycle G =
        F.homDefect 𝔾ₐ (F.invariantDifferential * (φ.toPowerSeries - PowerSeries.X)) := by
  rw [← F.deformationCocycle_smul_eq_homDefect_𝔾ₐ hI hφ]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ F.deformationCocycle_injective h.symm⟩

/-- **Lubin–Tate, Lemma 1.1.** Over a commutative ring `A` with an ideal `I` satisfying `I * I = ⊥`,
a commutative formal group law `F` and a formal group law `G` are related by a coordinate `φ`
congruent to `X` modulo `I` if and only if `F.deformationCocycle G` is the coboundary of a power
series without constant term whose coefficients lie in `I`. -/
theorem exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
    (F G : FormalGroup A) [F.IsComm] {I : Ideal A} (hI : I * I = ⊥) :
    (∃ φ : FormalCoordinate A,
        (∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) ∧ φ • F = G) ↔
      ∃ g : PowerSeries A, PowerSeries.constantCoeff g = 0 ∧
        (∀ n, PowerSeries.coeff n g ∈ I) ∧ F.deformationCocycle G = F.homDefect 𝔾ₐ g := by
  constructor
  · rintro ⟨φ, hφI, rfl⟩
    refine ⟨F.invariantDifferential * (φ.toPowerSeries - PowerSeries.X), ?_,
      powerSeries_coeff_mul_mem_of_right _ hφI,
      F.deformationCocycle_smul_eq_homDefect_𝔾ₐ hI hφI⟩
    simp [φ.constantCoeff_toPowerSeries]
  · rintro ⟨g, hg₀, hgI, hcoc⟩
    set δ := F.invInvariantDifferential * g
    have hδ₀ : PowerSeries.constantCoeff δ = 0 := by simp [δ, hg₀]
    have hδI : ∀ n, PowerSeries.coeff n δ ∈ I := powerSeries_coeff_mul_mem_of_right _ hgI
    have hnil : IsNilpotent (PowerSeries.coeff 1 δ) :=
      ⟨2, by
        rw [pow_two, ← Ideal.mem_bot, ← hI]
        exact Ideal.mul_mem_mul (hδI 1) (hδI 1)⟩
    let φ : FormalCoordinate A :=
      { toPowerSeries := PowerSeries.X + δ
        constantCoeff_toPowerSeries := by simp [hδ₀]
        isUnit_coeff_one := by simpa using hnil.isUnit_one_add }
    have hφX : φ.toPowerSeries - PowerSeries.X = δ := by simp [φ]
    have hPδ : F.invariantDifferential * δ = g := by
      dsimp only [δ]
      rw [← mul_assoc, F.invariantDifferential_mul_subst_pderiv, one_mul]
    refine ⟨φ, fun n ↦ hφX ▸ hδI n, ?_⟩
    rw [F.smul_eq_iff_deformationCocycle_eq_homDefect_𝔾ₐ G hI (fun n ↦ hφX ▸ hδI n), hφX, hPδ]
    exact hcoc

end CoordinateChange

/-! ### 3. Canonical Lubin–Tate symmetric 2-cocycles -/

section LubinTateCocycle

open TauCeti.LazardRing

/-- Evaluating `ℤ[x₁, x₂, …]` in `DualNumber LazardRing` with `xₙ` shifted by `ε`. -/
private noncomputable def evalShift (n : ℕ+) : MvPolynomial ℕ+ ℤ →ₐ[ℤ] DualNumber LazardRing :=
  MvPolynomial.aeval fun m : ℕ+ ↦
    algebraMap LazardRing (DualNumber LazardRing) (generator m) +
      if m = n then DualNumber.eps else 0

/-- Shifting the `n`-th polynomial generator of `LazardRing` by `ε` in `DualNumber LazardRing`. -/
private noncomputable def shiftGeneratorHom (n : ℕ+) :
    LazardRing →+* DualNumber LazardRing :=
  ((evalShift n).comp (mvPolynomialEquiv.symm : LazardRing →ₐ[ℤ] MvPolynomial ℕ+ ℤ)).toRingHom

private theorem fst_evalShift (n : ℕ+) (p : MvPolynomial ℕ+ ℤ) :
    (evalShift n p).fst = mvPolynomialEquiv p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [evalShift]
  | add p q hp hq => rw [map_add, map_add, TrivSqZeroExt.fst_add, hp, hq]
  | mul_X p m hp =>
    rw [map_mul, map_mul, TrivSqZeroExt.fst_mul, hp, mvPolynomialEquiv_X, evalShift,
      MvPolynomial.aeval_X]
    split_ifs <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private theorem fst_shiftGeneratorHom (n : ℕ+) (x : LazardRing) :
    (shiftGeneratorHom n x).fst = x := by
  simp [shiftGeneratorHom, fst_evalShift]

/-- The `ε`-component of `evalShift n` acts via the `n`-th polynomial partial derivative. -/
private theorem snd_evalShift (n : ℕ+) (p : MvPolynomial ℕ+ ℤ) :
    (evalShift n p).snd = mvPolynomialEquiv (MvPolynomial.pderiv n p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [evalShift]
  | add p q hp hq => rw [map_add, map_add, map_add, TrivSqZeroExt.snd_add, hp, hq]
  | mul_X p m hp =>
    have hXm : evalShift n (MvPolynomial.X m) =
        algebraMap LazardRing (DualNumber LazardRing) (generator m) +
          if m = n then DualNumber.eps else 0 := MvPolynomial.aeval_X _ m
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, mvPolynomialEquiv_X, TrivSqZeroExt.snd_mul,
      fst_evalShift, hp, hXm, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hmn : m = n
    · subst hmn
      simp [TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
    · simp [hmn, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

private theorem snd_shiftGeneratorHom (n : ℕ+) (x : LazardRing) :
    (shiftGeneratorHom n x).snd =
      mvPolynomialEquiv (MvPolynomial.pderiv n (mvPolynomialEquiv.symm x)) :=
  snd_evalShift n (mvPolynomialEquiv.symm x)

private theorem snd_shiftGeneratorHom_eq_zero_of_mem_grading_lt {n : ℕ+} {m : ℕ}
    (hm : m < 2 * (n : ℕ)) {x : LazardRing} (hx : x ∈ grading m) :
    (shiftGeneratorHom n x).snd = 0 := by
  have hx' : mvPolynomialEquiv (mvPolynomialEquiv.symm x) ∈ grading m := by simpa using hx
  have hp := mvPolynomialEquiv_mem_grading_iff.mp hx'
  rw [snd_shiftGeneratorHom]
  suffices MvPolynomial.pderiv n (mvPolynomialEquiv.symm x) = 0 by simp [this]
  ext d
  by_cases hc : (mvPolynomialEquiv.symm x).coeff (d + Finsupp.single n 1) = 0
  · simp [MvPolynomial.coeff_pderiv, hc]
  · exfalso
    have hw := hp hc
    rw [map_add, Finsupp.weight_single, one_smul] at hw
    omega

private theorem snd_shiftGeneratorHom_mem_grading_zero (n : ℕ+) {x : LazardRing}
    (hx : x ∈ grading (2 * (n : ℕ))) : (shiftGeneratorHom n x).snd ∈ grading 0 := by
  have hx' : mvPolynomialEquiv (mvPolynomialEquiv.symm x) ∈ grading (2 * (n : ℕ)) := by
    simpa using hx
  have hp := mvPolynomialEquiv_mem_grading_iff.mp hx'
  rw [snd_shiftGeneratorHom, mvPolynomialEquiv_mem_grading_iff]
  intro d hd
  rw [MvPolynomial.coeff_pderiv] at hd
  have hc : (mvPolynomialEquiv.symm x).coeff (d + Finsupp.single n 1) ≠ 0 := fun h ↦
    hd (by simp [h])
  have hw := hp hc
  rw [map_add, Finsupp.weight_single, one_smul] at hw
  omega

private theorem snd_shiftGeneratorHom_mem_augmentationIdeal_of_mem_sq (n : ℕ+) {x : LazardRing}
    (hx : x ∈ augmentationIdeal ^ 2) : (shiftGeneratorHom n x).snd ∈ augmentationIdeal := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) fun y z hy hz ↦ by
    rw [map_add, TrivSqZeroExt.snd_add]
    exact augmentationIdeal.add_mem hy hz
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_shiftGeneratorHom, fst_shiftGeneratorHom]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  exact augmentationIdeal.add_mem (augmentationIdeal.mul_mem_right _ hy)
    (augmentationIdeal.mul_mem_left _ hz)

/-- The `ε`-coefficient series of the universal formal group law under `shiftGeneratorHom n`. -/
private noncomputable def universalShiftSeries (n : ℕ+) : MvPowerSeries (Fin 2) LazardRing :=
  fun d ↦ (shiftGeneratorHom n (coeff d formalGroup.toPowerSeries)).snd

@[simp]
private theorem coeff_universalShiftSeries (n : ℕ+) (d : Fin 2 →₀ ℕ) :
    coeff d (universalShiftSeries n) =
      (shiftGeneratorHom n (coeff d formalGroup.toPowerSeries)).snd :=
  (rfl)

private theorem le_order_universalShiftSeries (n : ℕ+) :
    (((n : ℕ) + 1 : ℕ) : ℕ∞) ≤ (universalShiftSeries n).order := by
  refine le_order fun d hd ↦ ?_
  have hd' : d.degree < (n : ℕ) + 1 := by exact_mod_cast hd
  have hn := n.pos
  exact snd_shiftGeneratorHom_eq_zero_of_mem_grading_lt (by omega) (coeff_formalGroup_mem_grading d)

private theorem coeff_formalGroup_eq_zero_of_axis {d : Fin 2 →₀ ℕ} (hd : 2 ≤ d.degree)
    (haxis : d 0 = 0 ∨ d 1 = 0) : coeff d formalGroup.toPowerSeries = 0 := by
  have hdeg : d 0 + d 1 = d.degree := by simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hd_eq : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    ext s; fin_cases s <;> simp
  rcases haxis with h0 | h1
  · rw [hd_eq, h0, Finsupp.single_zero, _root_.zero_add, ← coeff_subst_zero_X,
      formalGroup.zero_add PowerSeries.HasSubst.X', PowerSeries.coeff_X, ite_eq_right (by omega)]
  · rw [hd_eq, h1, Finsupp.single_zero, _root_.add_zero, ← coeff_subst_X_zero,
      formalGroup.add_zero PowerSeries.HasSubst.X', PowerSeries.coeff_X, ite_eq_right (by omega)]

/-- The degree-`(n + 1)` homogeneous part of `universalShiftSeries n` is `C_(n + 1)`. -/
private theorem homogeneousComponent_universalShiftSeries (n : ℕ+) :
    homogeneousComponent ((n : ℕ) + 1) (universalShiftSeries n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) LazardRing) := by
  have hn := n.pos
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe]
  have hdeg_sum : d.degree = d 0 + d 1 := by simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  by_cases hd : d.degree = (n : ℕ) + 1
  · rw [ite_eq_left hd]
    by_cases haxis : d 0 = 0 ∨ d 1 = 0
    · have hFG := coeff_formalGroup_eq_zero_of_axis (by omega) haxis
      rw [coeff_universalShiftSeries, hFG, map_zero, TrivSqZeroExt.snd_zero,
        TauCeti.coeff_lazardCocycle, ite_eq_right (by omega)]
    · push Not at haxis
      obtain ⟨h0, h1⟩ := haxis
      have hi0 : 0 < d 0 := Nat.pos_of_ne_zero h0
      have hin : d 0 ≤ (n : ℕ) := by omega
      have hd1 : d 1 = (n : ℕ) + 1 - d 0 := by omega
      have hd_eq : d = Finsupp.single 0 (d 0) + Finsupp.single 1 ((n : ℕ) + 1 - d 0) := by
        ext s; fin_cases s <;> simp [hd1]
      -- Modulo `augmentationIdeal ^ 2`, `coeff d F` equals `(C(n+1, d₀) / d_{n+1}) • generator n`.
      let z := coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 ((n : ℕ) + 1 - d 0))
          formalGroup.toPowerSeries -
        (((n : ℕ) + 1).choose (d 0) / TauCeti.lazardGcd ((n : ℕ) + 1)) • generator n
      have hz_def : z = coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 ((n : ℕ) + 1 - d 0))
          formalGroup.toPowerSeries -
        (((n : ℕ) + 1).choose (d 0) / TauCeti.lazardGcd ((n : ℕ) + 1)) • generator n := rfl
      have hz_sq : z ∈ augmentationIdeal ^ 2 :=
        coeff_formalGroup_sub_nsmul_generator_mem_sq n hi0 hin
      have hz_gr : z ∈ grading (2 * (n : ℕ)) := by
        refine sub_mem ?_ (Submodule.smul_of_tower_mem _ _ (generator_mem_grading n))
        have hmem := coeff_formalGroup_mem_grading
          (Finsupp.single 0 (d 0) + Finsupp.single 1 ((n : ℕ) + 1 - d 0))
        have hsub : (Finsupp.single (0 : Fin 2) (d 0) +
            Finsupp.single 1 ((n : ℕ) + 1 - d 0)).degree - 1 = (n : ℕ) := by
          rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
          omega
        rwa [hsub] at hmem
      -- `(shiftGeneratorHom n z).snd` lies in `grading 0 ∩ augmentationIdeal`, so it vanishes.
      have hz0 : (shiftGeneratorHom n z).snd = 0 := by
        have haug : augmentation ((shiftGeneratorHom n z).snd) = 0 :=
          mem_augmentationIdeal.mp (snd_shiftGeneratorHom_mem_augmentationIdeal_of_mem_sq n hz_sq)
        rw [← intCast_augmentation_of_mem_grading_zero
          (snd_shiftGeneratorHom_mem_grading_zero n hz_gr), haug, Int.cast_zero]
      have hgen : (shiftGeneratorHom n (generator n)).snd = 1 := by
        rw [snd_shiftGeneratorHom, mvPolynomialEquiv_symm_generator, MvPolynomial.pderiv_X_self,
          map_one]
      have hval : (shiftGeneratorHom n (coeff d formalGroup.toPowerSeries)).snd =
          (((n : ℕ) + 1).choose (d 0) / TauCeti.lazardGcd ((n : ℕ) + 1) : ℕ) := by
        rw [hz_def, ← Nat.cast_smul_eq_nsmul ℤ, map_sub, map_zsmul, TrivSqZeroExt.snd_sub,
          TrivSqZeroExt.snd_smul, hgen, zsmul_eq_mul, mul_one, Int.cast_natCast, sub_eq_zero] at hz0
        rwa [← hd_eq] at hz0
      rw [coeff_universalShiftSeries, hval, hd_eq,
        TauCeti.coeff_single_add_single_lazardCocycle hi0 (by omega)]
      simp
  · rw [ite_eq_right hd, TauCeti.coeff_lazardCocycle, ite_eq_right (by omega)]

/-- The universal Lubin–Tate symmetric 2-cocycle in degree `n + 1` over `LazardRing`. -/
private noncomputable def universalLubinTateCocycle (n : ℕ+) :
    MvPowerSeries (Fin 2) LazardRing :=
  PowerSeries.subst formalGroup.toPowerSeries formalGroup.invariantDifferential *
    universalShiftSeries n

/-- Over `DualNumber LazardRing`, the deformation cocycle between `formalGroup` and its shift along
`shiftGeneratorHom n` is `ε • universalLubinTateCocycle n`. -/
private theorem deformationCocycle_universal_shiftGeneratorHom (n : ℕ+) :
    (formalGroup.map (algebraMap LazardRing (DualNumber LazardRing))).deformationCocycle
        (formalGroup.map (shiftGeneratorHom n)) =
      (DualNumber.eps : DualNumber LazardRing) •
        MvPowerSeries.map (algebraMap LazardRing (DualNumber LazardRing))
          (universalLubinTateCocycle n) := by
  let inlR := algebraMap LazardRing (DualNumber LazardRing)
  have hsub : (formalGroup.map (shiftGeneratorHom n)).toPowerSeries -
      (formalGroup.map inlR).toPowerSeries =
      (DualNumber.eps : DualNumber LazardRing) •
        MvPowerSeries.map inlR (universalShiftSeries n) :=
    MvPowerSeries.ext fun d ↦ TrivSqZeroExt.ext
      (by simp [inlR, FormalGroup.map_toPowerSeries, fst_shiftGeneratorHom,
        TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [inlR, FormalGroup.map_toPowerSeries, TrivSqZeroExt.algebraMap_eq_inl])
  rw [deformationCocycle, hsub, universalLubinTateCocycle, map_mul,
    PowerSeries.map_subst (.of_constantCoeff_zero formalGroup.zero_constantCoeff),
    formalGroup.map_invariantDifferential, ← FormalGroup.map_toPowerSeries, mul_smul_comm]

/-- `universalLubinTateCocycle n` is a symmetric 2-cocycle of the universal formal group law. -/
private theorem isSymmetricCocycle_universalLubinTateCocycle (n : ℕ+) :
    formalGroup.IsSymmetricCocycle (universalLubinTateCocycle n) := by
  let inlR := algebraMap LazardRing (DualNumber LazardRing)
  let F_L := formalGroup.map inlR
  let G_L := formalGroup.map (shiftGeneratorHom n)
  -- Apply `isSymmetricCocycle_deformationCocycle` over `DualNumber LazardRing` modulo `(ε)`.
  let I : Ideal (DualNumber LazardRing) :=
    RingHom.ker (TrivSqZeroExt.fstHom ℤ LazardRing LazardRing).toRingHom
  have hI : I * I = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply] at hx hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  have hFG : ∀ d, coeff d (G_L.toPowerSeries - F_L.toPowerSeries) ∈ I := fun d ↦ by
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply,
      map_sub, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, coeff_map, coeff_map,
      TrivSqZeroExt.fst_sub, fst_shiftGeneratorHom]
    simp [inlR, TrivSqZeroExt.algebraMap_eq_inl]
  have hcoc := F_L.isSymmetricCocycle_deformationCocycle G_L hI hFG
  rw [deformationCocycle_universal_shiftGeneratorHom] at hcoc
  -- Read off the `ε`-component to descend symmetry and the 2-cocycle identity to `LazardRing`.
  have hinj {σ : Type} {U V : MvPowerSeries σ LazardRing}
      (h : (DualNumber.eps : DualNumber LazardRing) • MvPowerSeries.map inlR U =
        (DualNumber.eps : DualNumber LazardRing) • MvPowerSeries.map inlR V) : U = V := by
    ext d
    have hd := congrArg (fun S ↦ (coeff d S).snd) h
    simpa [inlR, TrivSqZeroExt.algebraMap_eq_inl] using hd
  have hmap_sub {τ : Type} {b : Fin 2 → MvPowerSeries τ LazardRing} (hb : HasSubst b) :
      ((DualNumber.eps : DualNumber LazardRing) •
          MvPowerSeries.map inlR (universalLubinTateCocycle n)).subst
        (fun i ↦ MvPowerSeries.map inlR (b i)) =
        (DualNumber.eps : DualNumber LazardRing) •
          MvPowerSeries.map inlR ((universalLubinTateCocycle n).subst b) := by
    rw [subst_smul (hb.map inlR), ← map_subst hb]
  refine { subst_swap := hinj ?_, subst_add_subst_eq := hinj ?_ }
  · have h2 := hcoc.subst_swap
    have hbsw : (fun i ↦ MvPowerSeries.map inlR (![X 1, X 0] i)) =
        (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) (DualNumber LazardRing)) := by
      funext i; fin_cases i <;> simp
    rw [← hbsw, hmap_sub HasSubst.X_X] at h2
    exact h2
  · have h1 := hcoc.subst_add_subst_eq
    have hb1 : (fun i ↦ MvPowerSeries.map inlR
        (![(X 0 : MvPowerSeries (Fin 3) LazardRing), X 1] i)) = ![X 0, X 1] := by
      funext i; fin_cases i <;> simp
    have hb3 : (fun i ↦ MvPowerSeries.map inlR
        (![(X 1 : MvPowerSeries (Fin 3) LazardRing), X 2] i)) = ![X 1, X 2] := by
      funext i; fin_cases i <;> simp
    have hb2 : (fun i ↦ MvPowerSeries.map inlR
        (![formalGroup.toPowerSeries.subst
          ![(X 0 : MvPowerSeries (Fin 3) LazardRing), X 1], X 2] i)) =
        ![F_L.toPowerSeries.subst ![X 0, X 1], X 2] := by
      refine funext <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp [F_L, FormalGroup.map_toPowerSeries, map_subst HasSubst.X_X, hb1]
      · simp
    have hb4 : (fun i ↦ MvPowerSeries.map inlR
        (![X 0, formalGroup.toPowerSeries.subst
          ![(X 1 : MvPowerSeries (Fin 3) LazardRing), X 2]] i)) =
        ![X 0, F_L.toPowerSeries.subst ![X 1, X 2]] := by
      refine funext <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp
      · simp [F_L, FormalGroup.map_toPowerSeries, map_subst HasSubst.X_X, hb3]
    have eq1 := hmap_sub (b := ![(X 0 : MvPowerSeries (Fin 3) LazardRing), X 1]) HasSubst.X_X
    have eq2 := hmap_sub (τ := Fin 3) (hasSubst_finTwo (formalGroup.hasSubst_subst_pair
      (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 1)) (PowerSeries.HasSubst.X 2))
    have eq3 := hmap_sub (b := ![(X 1 : MvPowerSeries (Fin 3) LazardRing), X 2]) HasSubst.X_X
    have eq4 := hmap_sub (τ := Fin 3) (hasSubst_finTwo (PowerSeries.HasSubst.X 0)
      (formalGroup.hasSubst_subst_pair (PowerSeries.HasSubst.X 1) (PowerSeries.HasSubst.X 2)))
    rw [hb1] at eq1
    rw [hb2] at eq2
    rw [hb3] at eq3
    rw [hb4] at eq4
    rw [eq1, eq2, eq4, eq3, ← smul_add, ← smul_add, ← map_add, ← map_add] at h1
    exact h1

/-- **Lubin–Tate, Lemma 1.3 (canonical symmetric 2-cocycle in degree `n + 1`).** For every
commutative formal group law `F` over a commutative ring `R` and every `n : ℕ+`,
`F.lubinTateCocycle n` is a symmetric 2-cocycle of `F` without constant term, vanishing below total
degree `n + 1`, with degree-`(n + 1)` homogeneous part equal to the Lazard cocycle `C_(n + 1)`. -/
noncomputable def lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.map (LazardRing.lift ⟨F, inferInstance⟩) (universalLubinTateCocycle n)

/-- `F.lubinTateCocycle n` is a symmetric 2-cocycle of `F`. -/
theorem isSymmetricCocycle_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R)
    [F.IsComm] (n : ℕ+) : F.IsSymmetricCocycle (F.lubinTateCocycle n) := by
  simpa [lubinTateCocycle, LazardRing.map_lift] using
    (isSymmetricCocycle_universalLubinTateCocycle n).map (LazardRing.lift ⟨F, inferInstance⟩)

/-- `F.lubinTateCocycle n` has zero constant coefficient. -/
@[simp]
theorem constantCoeff_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : constantCoeff (F.lubinTateCocycle n) = 0 := by
  have h0 : constantCoeff (universalShiftSeries n) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_of_lt_order (lt_of_lt_of_le (by simp) (le_order_universalShiftSeries n))
  rw [lubinTateCocycle, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, universalLubinTateCocycle, map_mul, h0, mul_zero, map_zero]

/-- `F.lubinTateCocycle n` vanishes below total degree `n + 1`. -/
theorem le_order_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]
    (n : ℕ+) : (((n : ℕ) + 1 : ℕ) : ℕ∞) ≤ (F.lubinTateCocycle n).order := by
  have hu : (((n : ℕ) + 1 : ℕ) : ℕ∞) ≤ (universalLubinTateCocycle n).order :=
    (_root_.zero_add _).symm.le.trans
      ((add_le_add zero_le (le_order_universalShiftSeries n)).trans le_order_mul)
  refine le_order fun d hd ↦ ?_
  rw [lubinTateCocycle, coeff_map, coeff_of_lt_order (hd.trans_le hu), map_zero]

/-- The degree-`(n + 1)` homogeneous component of `F.lubinTateCocycle n` is the Lazard cocycle
`C_(n + 1)`. -/
@[simp]
theorem homogeneousComponent_lubinTateCocycle {R : Type*} [CommRing R] (F : FormalGroup R)
    [F.IsComm] (n : ℕ+) :
    homogeneousComponent ((n : ℕ) + 1) (F.lubinTateCocycle n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) R) := by
  have hP0 : constantCoeff (PowerSeries.subst formalGroup.toPowerSeries
      formalGroup.invariantDifferential - 1) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      formalGroup.zero_constantCoeff, formalGroup.constantCoeff_invariantDifferential]
    simp
  have hrem : (((n : ℕ) + 1 : ℕ) : ℕ∞) <
      ((PowerSeries.subst formalGroup.toPowerSeries formalGroup.invariantDifferential - 1) *
        universalShiftSeries n).order := by
    refine lt_of_lt_of_le ?_ le_order_mul
    calc (((n : ℕ) + 1 : ℕ) : ℕ∞) < ((1 + ((n : ℕ) + 1) : ℕ) : ℕ∞) :=
          Nat.cast_lt.mpr (by omega)
      _ = 1 + (((n : ℕ) + 1 : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ _ := add_le_add (one_le_order_iff_constCoeff_eq_zero.mpr hP0)
          (le_order_universalShiftSeries n)
  have huniv : homogeneousComponent ((n : ℕ) + 1) (universalLubinTateCocycle n) =
      ↑(TauCeti.lazardCocycle ((n : ℕ) + 1) LazardRing) := by
    have heq : universalLubinTateCocycle n = universalShiftSeries n +
        (PowerSeries.subst formalGroup.toPowerSeries formalGroup.invariantDifferential - 1) *
          universalShiftSeries n := by
      dsimp only [universalLubinTateCocycle]
      ring
    rw [heq, map_add, homogeneousComponent_of_lt_order_eq_zero hrem, _root_.add_zero,
      homogeneousComponent_universalShiftSeries]
  ext d
  rw [coeff_homogeneousComponent, lubinTateCocycle, coeff_map, MvPolynomial.coeff_coe]
  have hd := congrArg (coeff d) huniv
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe] at hd
  by_cases hdeg : d.degree = (n : ℕ) + 1
  · rw [ite_eq_left hdeg] at hd ⊢
    rw [hd, ← TauCeti.map_lazardCocycle (LazardRing.lift ⟨F, inferInstance⟩),
      MvPolynomial.coeff_map]
  · have hdeg' : d 0 + d 1 ≠ (n : ℕ) + 1 := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdeg
    rw [ite_eq_right hdeg, TauCeti.coeff_lazardCocycle, ite_eq_right (by tauto)]

/-- `FormalGroup.lubinTateCocycle` commutes with base change of the coefficient ring. -/
@[simp]
theorem map_lubinTateCocycle {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (F : FormalGroup R) [F.IsComm] (n : ℕ+) :
    MvPowerSeries.map f (F.lubinTateCocycle n) = (F.map f).lubinTateCocycle n := by
  rw [lubinTateCocycle, lubinTateCocycle, ← RingHom.comp_apply, ← MvPowerSeries.map_comp,
    LazardRing.lift_map]

/-- The index `p^(j + 1) - 1 : ℕ+` of the `j`-th Lubin–Tate cocycle in degree `p^(j + 1)`. -/
private def primePowPred (p : ℕ) (hp : p.Prime) (j : ℕ) : ℕ+ :=
  ⟨p ^ (j + 1) - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow j.succ_ne_zero hp.one_lt)⟩

@[simp]
private theorem coe_primePowPred_add_one (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (primePowPred p hp j : ℕ) + 1 = p ^ (j + 1) :=
  Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)

/-- **Canonical Lubin–Tate decomposition of symmetric 2-cocycles.** Let `p` be a prime with `p = 0`
in `R`, and let `F` be a commutative formal group law over `R` whose `p`-series has order at least
`pʰ` and a unit coefficient of `X^(pʰ)`. Then every symmetric 2-cocycle `Φ` of `F` without constant
term decomposes as
`∑ j : Fin (h - 1), c j • F.lubinTateCocycle ⟨p^(j + 1) - 1, _⟩ + F.homDefect 𝔾ₐ g`
for a *unique* tuple `c : Fin (h - 1) → R` and some power series `g` without constant term. -/
theorem IsSymmetricCocycle.existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ
    {R : Type*} [CommRing R] {F : FormalGroup R} [F.IsComm] {p h : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Φ : MvPowerSeries (Fin 2) R} (hΦ : F.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0) :
    ∃! c : Fin (h - 1) → R, ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧
      Φ = ∑ j : Fin (h - 1),
        c j • F.lubinTateCocycle ⟨p ^ (j.1 + 1) - 1,
          Nat.sub_pos_of_lt (Nat.one_lt_pow j.1.succ_ne_zero hp.one_lt)⟩ +
        F.homDefect 𝔾ₐ g :=
  hΦ.existsUnique_sum_smul_add_homDefect_𝔾ₐ hp hpR hF hv (u := fun _ ↦ 1)
    (fun j ↦ F.isSymmetricCocycle_lubinTateCocycle (primePowPred p hp j.1))
    (fun j ↦ by simpa [coe_primePowPred_add_one] using
      F.le_order_lubinTateCocycle (primePowPred p hp j.1))
    (fun j ↦ by
      have := F.homogeneousComponent_lubinTateCocycle (primePowPred p hp j.1)
      rwa [coe_primePowPred_add_one, ← one_smul R (TauCeti.lazardCocycle _ R)] at this)
    (fun _ ↦ isUnit_one) hΦ₀

end LubinTateCocycle

end FormalGroup
