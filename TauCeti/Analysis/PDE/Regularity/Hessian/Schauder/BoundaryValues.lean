/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain
import TauCeti.Analysis.Holder.BoundaryInterpolation
import TauCeti.Analysis.Holder.LipschitzDomain
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate with `C^{2,α}` boundary values

Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary Ω α`), and let

`𝓛 u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`

have coefficients `α`-Hölder and bounded on `Ω`, with `a` uniformly elliptic on `closure Ω`. The
global estimates of `TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain` are stated for
`u` vanishing on `∂Ω`. This file proves them for arbitrary boundary values `u = φ` on `∂Ω`, given by
a function `φ` that is `C²` near `closure Ω` with `|φ| ≤ P` and `D²φ` `α`-Hölder with constant `Q`
on `closure Ω`. This is Gilbarg–Trudinger's Theorem 6.6 in full:

`[D²u]_{α; closure Ω} + sup ‖Du‖ + sup ‖D²u‖ ≤ C ([𝓛 u]_{α; Ω} + sup |u| + P + Q)`

(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_eqOn_frontier`), with
`C` depending only on `Ω`, `α` and the bounds on the coefficients. With `c ≤ 0` the maximum
principle removes `sup |u|`, and the `C^{2,α}(closure Ω)` norm of `u` is bounded by the
`C^{0,α}(Ω)` norm of `𝓛 u` and the norm `P + Q` of the boundary values
(`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_eqOn_frontier_of_nonpos`). This is
the a priori estimate of the method of continuity for the Dirichlet problem with `C^{2,α}`
boundary values (Gilbarg–Trudinger, proof of Theorem 6.8).

The estimates come from the zero-boundary ones applied to `w = u - φ`, which vanishes on `∂Ω` and
solves `𝓛 w = 𝓛 u - 𝓛 φ` (`TauCeti.PDE.sum_smul_fderiv_fderiv_add_fderiv_add_mul_sub`). What this
needs is that `𝓛` is bounded from `C^{2,α}(closure Ω)` to `C^{0,α}(Ω)`
(`TauCeti.PDE.exists_norm_le_and_holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul`): the
interpolation inequalities on `closure Ω` at a fixed scale
(`TauCeti.exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_mul_add_of_isBounded`) bound
`‖Dφ‖` and `‖D²φ‖` by a multiple of `P + Q`; on the Lipschitz domain `Ω` bounded functions with
bounded derivatives are `α`-Hölder
(`Set.HasLipschitzGraphBoundary.exists_holderOnWith_and_holderOnWith_fderiv_of_norm_le`);
and products of bounded Hölder functions are Hölder
(`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul`, in
`TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.LowerOrder`). So `𝓛 φ` is `α`-Hölder on
`Ω` and bounded there (`TauCeti.PDE.abs_sum_smul_fderiv_fderiv_add_fderiv_add_mul_le`), both with
constant a multiple of `P + Q`.

## Main declarations

* `TauCeti.PDE.exists_norm_le_and_holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul`:
  `‖Dφ‖`, `‖D²φ‖`, the Hölder constant of `𝓛 φ` and `sup |𝓛 φ|` are bounded by a multiple of
  `P + Q`.
* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_eqOn_frontier`: the
  global Schauder estimate for `u = φ` on `∂Ω`, in terms of `[𝓛 u]_α`, `sup |u|`, `P` and `Q`.
* `exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_eqOn_frontier_of_nonpos`, in the
  `TauCeti.PDE` namespace: for `c ≤ 0`, the bound of `u` in `C^{2,α}(closure Ω)` by `𝓛 u` in
  `C^{0,α}(Ω)` and the boundary values.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, Theorem 6.6 (the global estimate with boundary values `φ ∈ C^{2,α}(closure Ω)`)
  and the proof of Theorem 6.8 (the a priori estimate for `c ≤ 0`); Section 3.3, Theorem 3.7.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The operator is bounded from `C^{2,α}` to `C^{0,α}`.** Let `α ≤ 1` and let `Ω ⊆ ℝ^{n+1}` be
a bounded set with Lipschitz graph boundary (`Set.HasLipschitzGraphBoundary`), for instance a
bounded set with `C^{2,α}` boundary (`Set.HasC2HolderBoundary`). Let `L`, `M`
and `B` be given. Then there is a constant `C` with the following property. Let `a` have entries
`α`-Hölder with constant `L` and bounded by `M` on `Ω`, and let `b` and `c` be `α`-Hölder
with constant `B` and bounded by `B` on `Ω`. Let `φ` be `C²` on an open set containing
`closure Ω`, with `|φ| ≤ P` on `closure Ω` and `D²φ` `α`-Hölder with constant `Q` there. Then
`‖Dφ‖` and `‖D²φ‖` are bounded by `C (P + Q)` on `closure Ω`, and
`𝓛 φ = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼφ + b · ∇φ + c φ` is `α`-Hölder on `Ω` with constant `C (P + Q)` and bounded
there by `C (P + Q)`. No ellipticity is needed. -/
theorem exists_norm_le_and_holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul {α : ℝ≥0}
    (hα1 : α ≤ 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω) (hbdry : Ω.HasLipschitzGraphBoundary)
    (L M B : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ i j, HolderOnWith L α (fun z => a z i j) Ω) → (∀ z ∈ Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) →
      ∀ {U : Set E} {φ : E → ℝ} {P Q : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 φ U → (∀ z ∈ closure Ω, |φ z| ≤ P) →
        HolderOnWith Q α (iteratedFDeriv ℝ 2 φ) (closure Ω) →
        (∀ z ∈ closure Ω, ‖fderiv ℝ φ z‖ ≤ C * (P + Q)) ∧
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 φ z‖ ≤ C * (P + Q)) ∧
        HolderOnWith (C * (P + Q)) α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ φ) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ φ z (b z) +
            c z * φ z) Ω ∧
        ∀ z ∈ Ω, |∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ φ) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ φ z (b z) + c z * φ z| ≤ C * (P + Q) := by
  -- `‖Dφ‖, ‖D²φ‖ ≤ A (P + Q)` by interpolation on `closure Ω`.
  obtain ⟨A, hA⟩ := exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_mul_add_of_isBounded
    (F := ℝ) (Set.hasLipschitzGraphBoundary_iff.1 hbdry) hΩ α
  obtain ⟨C₃, hC₃⟩ := hbdry.exists_holderOnWith_and_holderOnWith_fderiv_of_norm_le
    finrank_euclideanSpace_fin hΩ hα1
  set m : ℝ≥0 := (n + 1 : ℝ≥0) ^ 2
  set D : ℝ≥0 := (1 + A) * (2 * B + 2 * B * C₃ + m * L) + m * M
  set G : ℝ≥0 := (1 + A) * (m * M + 2 * B)
  refine ⟨A + D + G, fun {a b c} hL hM hHb hb hHc hc {U φ P Q} hU hΩU hφ hP hQ => ?_⟩
  have hΩcl : Ω ⊆ closure Ω := subset_closure
  have hAD (z : E) (hz : z ∈ closure Ω) :=
    hA hU hΩU hφ (fun z hz => by simpa only [Real.norm_eq_abs] using hP z hz) hQ z hz
  -- A common bound `N₁ = (1 + A) (P + Q)` for `|φ|`, `‖Dφ‖` and `‖D²φ‖` on `closure Ω`.
  set N₁ : ℝ≥0 := (1 + A) * (P + Q)
  have hN₁ : (P : ℝ) ≤ N₁ ∧ (A * (P + Q) : ℝ) ≤ N₁ := by
    simp only [N₁]; push_cast
    constructor <;> nlinarith [A.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]
  have hφN : ∀ z ∈ closure Ω, |φ z| ≤ N₁ := fun z hz => (hP z hz).trans hN₁.1
  have hDN : ∀ z ∈ closure Ω, ‖fderiv ℝ φ z‖ ≤ N₁ := fun z hz => (hAD z hz).1.trans hN₁.2
  have hD2N : ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 φ z‖ ≤ N₁ := fun z hz =>
    (hAD z hz).2.trans hN₁.2
  -- `φ` and `Dφ` are `α`-Hölder on `Ω` with constant `C₃ N₁`.
  obtain ⟨hHφ, hHDφ⟩ := hC₃ (fun z hz => hφ.contDiffAt (hU.mem_nhds (hΩU (hΩcl hz))))
    (fun z hz => by rw [Real.norm_eq_abs]; exact hφN z (hΩcl hz)) (fun z hz => hDN z (hΩcl hz))
    fun z hz => hD2N z (hΩcl hz)
  refine ⟨fun z hz => (hAD z hz).1.trans ?_, fun z hz => (hAD z hz).2.trans ?_,
    (holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul hL hM hHb hb hHc hc hHφ hHDφ
      (hQ.mono hΩcl) (fun z hz => hφN z (hΩcl hz)) (fun z hz => hDN z (hΩcl hz))
      (fun z hz => hD2N z (hΩcl hz))).mono_const ?_,
    fun z hz => (abs_sum_smul_fderiv_fderiv_add_fderiv_add_mul_le (hM z hz) (hb z hz)
      (hc z hz) (hφN z (hΩcl hz)) (hDN z (hΩcl hz)) (hD2N z (hΩcl hz))).trans ?_⟩
  · gcongr; exact le_self_add.trans le_self_add
  · gcongr; exact le_self_add.trans le_self_add
  · -- `m (M Q + N₁ L) + 2 B (N₁ + C₃ N₁) ≤ D (P + Q) ≤ C (P + Q)`.
    refine le_trans ?_ (mul_le_mul_left (le_add_self.trans le_self_add) _)
    rw [← NNReal.coe_le_coe]
    simp only [D, N₁, m, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, NNReal.coe_ofNat,
      NNReal.coe_pow, NNReal.coe_natCast]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ((n : ℝ) + 1)) M.coe_nonneg) P.coe_nonneg]
  · -- `N₁ ((n + 1)² M + 2 B) = G (P + Q) ≤ C (P + Q)`.
    have hG : (N₁ * ((n + 1) ^ 2 * M + 2 * B) : ℝ) = G * (P + Q) := by
      simp only [G, N₁, m, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, NNReal.coe_ofNat,
        NNReal.coe_pow, NNReal.coe_natCast]
      ring
    rw [hG]
    gcongr
    exact_mod_cast (le_add_self : G ≤ A + D + G)

/-- Adding back the boundary values: on a set `S` inside the open set `U` on which `u` and `φ`
are `C²`, bounds for `D²(u - φ)` and `D(u - φ)` and for `D²φ` and `Dφ` give bounds for `D²u` and
`Du`. -/
private theorem holderOnWith_iteratedFDeriv_two_and_norm_le_of_sub {α X' Q : ℝ≥0} {X Y : ℝ}
    {S U : Set E} (hU : IsOpen U) (hSU : S ⊆ U) {u φ : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hφ : ContDiffOn ℝ 2 φ U) (hw2 : HolderOnWith X' α (iteratedFDeriv ℝ 2 (u - φ)) S)
    (hw1 : ∀ z ∈ S, ‖fderiv ℝ (u - φ) z‖ ≤ X)
    (hw2' : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 (u - φ) z‖ ≤ X)
    (hQ : HolderOnWith Q α (iteratedFDeriv ℝ 2 φ) S) (hφ1 : ∀ z ∈ S, ‖fderiv ℝ φ z‖ ≤ Y)
    (hφ2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 φ z‖ ≤ Y) :
    HolderOnWith (X' + Q) α (iteratedFDeriv ℝ 2 u) S ∧ (∀ z ∈ S, ‖fderiv ℝ u z‖ ≤ X + Y) ∧
      ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 u z‖ ≤ X + Y := by
  have hcd (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) (z : E) (hz : z ∈ S) : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt (hU.mem_nhds (hSU hz))
  have h2 (z : E) (hz : z ∈ S) :
      iteratedFDeriv ℝ 2 u z = iteratedFDeriv ℝ 2 (u - φ) z + iteratedFDeriv ℝ 2 φ z := by
    rw [iteratedFDeriv_sub_apply (hcd u hu z hz) (hcd φ hφ z hz), sub_add_cancel]
  have h1 (z : E) (hz : z ∈ S) : fderiv ℝ u z = fderiv ℝ (u - φ) z + fderiv ℝ φ z := by
    rw [fderiv_sub ((hcd u hu z hz).differentiableAt (by norm_num))
      ((hcd φ hφ z hz).differentiableAt (by norm_num)), sub_add_cancel]
  refine ⟨(hw2.add hQ).congr fun z hz => (h2 z hz).symm, fun z hz => ?_, fun z hz => ?_⟩
  · rw [h1 z hz]
    exact (norm_add_le _ _).trans (add_le_add (hw1 z hz) (hφ1 z hz))
  · rw [h2 z hz]
    exact (norm_add_le _ _).trans (add_le_add (hw2' z hz) (hφ2 z hz))

/-- **The global Schauder estimate with `C^{2,α}` boundary values.** Let `0 < α < 1` and let
`Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary (`Set.HasC2HolderBoundary`). Let `0 < λ`,
`Λ`, `L`, `M` and `B` be given. Then there is a constant `C` with the following property. Let `a`
have ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with constant
`L` and bounded by `M` on `closure Ω`; let the drift `b` and the potential `c` be `α`-Hölder with
constant `B` and bounded by `B` on `Ω`. Put `𝓛 u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`. Let `u` and `φ` be
`C²` on an open set containing `closure Ω`, with `u = φ` on the frontier of `Ω`, `|u| ≤ N` and
`|φ| ≤ P` on `closure Ω`, `D²φ` `α`-Hölder with constant `Q` on `closure Ω`, and `D²u` `α`-Hölder
there (with any constant). If `𝓛 u` is `α`-Hölder on `Ω` with constant `K`, then `D²u` is
`α`-Hölder on `closure Ω` with constant `C (K + N + P + Q)`, and `‖Du‖` and `‖D²u‖` are bounded by
`C (K + N + P + Q)` on `closure Ω`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L`, `M` and `B`, not on the coefficients beyond
these bounds, nor on `u` or `φ`; no sign condition on `c` is needed. Since `P + Q` is equivalent to
the `C^{2,α}(closure Ω)` norm of `φ`, this is Gilbarg–Trudinger, Theorem 6.6. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_eqOn_frontier
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) →
      ∀ {U : Set E} {u φ : E → ℝ} {N P Q K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 φ U → (∀ z ∈ frontier Ω, u z = φ z) →
        (∀ z ∈ closure Ω, |u z| ≤ N) → (∀ z ∈ closure Ω, |φ z| ≤ P) →
        HolderOnWith Q α (iteratedFDeriv ℝ 2 φ) (closure Ω) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) +
            c z * u z) Ω →
        HolderOnWith (C * (K + N + P + Q)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + N + P + Q)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + N + P + Q) := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul hα hα1 hΩ
      hbdry Lam L M B hlam
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_and_holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    hα1.le hΩ hbdry.hasLipschitzGraphBoundary L M B
  refine ⟨C₀ * (1 + C₁) + C₁ + 1, fun {a b c} hEll hEll' hL hM hHb hb hHc hc {U u φ N P Q K V}
    hU hΩU hu hφ hbd hN hP hQ hV hK => ?_⟩
  obtain ⟨hφ1, hφ2, hLφ, -⟩ := hC₁ (fun i j => (hL i j).mono subset_closure)
    (fun z hz => hM z (subset_closure hz)) hHb hb hHc hc hU hΩU hφ hP hQ
  have hcd (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) (z : E) (hz : z ∈ closure Ω) :
      ContDiffAt ℝ 2 f z := hf.contDiffAt (hU.mem_nhds (hΩU hz))
  -- The zero-boundary estimate for `w = u - φ`, with `𝓛 w = 𝓛 u - 𝓛 φ`.
  obtain ⟨hw2, hw1, hw2'⟩ := hC₀ (u := u - φ) (N := N + P) (K := K + C₁ * (P + Q))
    hEll hEll' hL hM hHb hb hHc hc hU hΩU (hu.sub hφ) (fun z hz => sub_eq_zero.2 (hbd z hz))
    (fun z hz => (abs_sub _ _).trans (by push_cast; exact add_le_add (hN z hz) (hP z hz)))
    ((hV.sub hQ).congr fun z hz =>
      (iteratedFDeriv_sub_apply (hcd u hu z hz) (hcd φ hφ z hz)).symm)
    ((hK.sub hLφ).congr fun z hz => (sum_smul_fderiv_fderiv_add_fderiv_add_mul_sub
      (hcd u hu z (subset_closure hz)) (hcd φ hφ z (subset_closure hz))).symm)
  obtain ⟨h2, h1, h2'⟩ := holderOnWith_iteratedFDeriv_two_and_norm_le_of_sub hU hΩU hu hφ hw2 hw1
    hw2' hQ hφ1 hφ2
  -- Comparison of constants; `nlinarith` multiplies the nonnegativity facts.
  have hle : ((C₀ * (K + C₁ * (P + Q) + (N + P)) + Q : ℝ≥0) : ℝ) ≤
      (C₀ * (1 + C₁) + C₁ + 1) * (K + N + P + Q) := by
    push_cast
    nlinarith [C₀.coe_nonneg, C₁.coe_nonneg, mul_nonneg C₀.coe_nonneg C₁.coe_nonneg,
      K.coe_nonneg, N.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]
  have hle' : (C₀ * ((K + C₁ * (P + Q) : ℝ≥0) + (N + P : ℝ≥0)) : ℝ) + C₁ * (P + Q) ≤
      (C₀ * (1 + C₁) + C₁ + 1 : ℝ≥0) * (K + N + P + Q) := by
    push_cast
    nlinarith [C₀.coe_nonneg, C₁.coe_nonneg, mul_nonneg C₀.coe_nonneg C₁.coe_nonneg,
      K.coe_nonneg, N.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]
  exact ⟨h2.mono_const (by exact_mod_cast hle), fun z hz => (h1 z hz).trans hle',
    fun z hz => (h2' z hz).trans hle'⟩

/-- **The global Schauder a priori estimate with `C^{2,α}` boundary values for a nonpositive
potential.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`). Let `0 < λ`, `Λ`, `L`, `M` and `B` be given. Then there is a constant
`C` with the following property. Let `a` have ellipticity bounds `λ, Λ` at every point of
`closure Ω`, and entries `α`-Hölder with constant `L` and bounded by `M` on `closure Ω`; let the
drift `b` and the potential `c` be `α`-Hölder with constant `B` and bounded by `B` on `Ω`, and let
`c ≤ 0` on `Ω`. Put `𝓛 u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`. Let `u` and `φ` be `C²` on an open set
containing `closure Ω`, with `u = φ` on the frontier of `Ω`, `|φ| ≤ P` on `closure Ω`, `D²φ`
`α`-Hölder with constant `Q` on `closure Ω`, and `D²u` `α`-Hölder there (with any constant). If
`𝓛 u` is `α`-Hölder on `Ω` with constant `K` and bounded there by `F`, then on `closure Ω`

* `|u| ≤ C (F + P + Q)`,
* `D²u` is `α`-Hölder with constant `C (K + F + P + Q)`,
* `‖Du‖` and `‖D²u‖` are bounded by `C (K + F + P + Q)`.

So the `C^{2,α}(closure Ω)` norm of `u` is bounded by `C` times the sum of the `C^{0,α}(Ω)` norm of
`𝓛 u` and the `C^{2,α}(closure Ω)` norm of the boundary values, with `C` depending only on `Ω`, `α`,
`λ`, `Λ`, `L`, `M` and `B`. This is the a priori estimate of the method of continuity for the
Dirichlet problem with boundary values `φ` (Gilbarg–Trudinger, Theorem 6.6 with `sup |u|` bounded
by Theorem 3.7, as in the proof of Theorem 6.8). -/
theorem exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_eqOn_frontier_of_nonpos
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) → (∀ z ∈ Ω, c z ≤ 0) →
      ∀ {U : Set E} {u φ : E → ℝ} {P Q K F V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 φ U → (∀ z ∈ frontier Ω, u z = φ z) →
        (∀ z ∈ closure Ω, |φ z| ≤ P) → HolderOnWith Q α (iteratedFDeriv ℝ 2 φ) (closure Ω) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) +
            c z * u z) Ω →
        (∀ z ∈ Ω, |∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) + c z * u z| ≤ F) →
        (∀ z ∈ closure Ω, |u z| ≤ C * (F + P + Q)) ∧
          HolderOnWith (C * (K + F + P + Q)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + F + P + Q)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + F + P + Q) := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos hα
      hα1 hΩ hbdry Lam L M B hlam
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_and_holderOnWith_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    hα1.le hΩ hbdry.hasLipschitzGraphBoundary L M B
  refine ⟨C₀ * (1 + 2 * C₁) + C₁ + 1, fun {a b c} hEll hEll' hL hM hHb hb hHc hc hc0
    {U u φ P Q K F V} hU hΩU hu hφ hbd hP hQ hV hK hF => ?_⟩
  obtain ⟨hφ1, hφ2, hLφ, hLφF⟩ := hC₁ (fun i j => (hL i j).mono subset_closure)
    (fun z hz => hM z (subset_closure hz)) hHb hb hHc hc hU hΩU hφ hP hQ
  have hcd (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) (z : E) (hz : z ∈ closure Ω) :
      ContDiffAt ℝ 2 f z := hf.contDiffAt (hU.mem_nhds (hΩU hz))
  have hLw (z : E) (hz : z ∈ Ω) := sum_smul_fderiv_fderiv_add_fderiv_add_mul_sub (a := a) (b := b)
    (c := c) (hcd u hu z (subset_closure hz)) (hcd φ hφ z (subset_closure hz))
  -- The zero-boundary estimate for `w = u - φ`, with `𝓛 w = 𝓛 u - 𝓛 φ`.
  obtain ⟨hw0, hw2, hw1, hw2'⟩ := hC₀ (u := u - φ) (K := K + C₁ * (P + Q))
    (F := F + C₁ * (P + Q)) hEll hEll' hL hM hHb hb hHc hc hc0 hU hΩU (hu.sub hφ)
    (fun z hz => sub_eq_zero.2 (hbd z hz))
    ((hV.sub hQ).congr fun z hz =>
      (iteratedFDeriv_sub_apply (hcd u hu z hz) (hcd φ hφ z hz)).symm)
    ((hK.sub hLφ).congr fun z hz => (hLw z hz).symm)
    (fun z hz => by
      rw [hLw z hz]
      exact (abs_sub _ _).trans (by push_cast; exact add_le_add (hF z hz) (hLφF z hz)))
  obtain ⟨h2, h1, h2'⟩ := holderOnWith_iteratedFDeriv_two_and_norm_le_of_sub hU hΩU hu hφ hw2 hw1
    hw2' hQ hφ1 hφ2
  -- Comparison of constants; `nlinarith` multiplies the nonnegativity facts.
  have hle : ((C₀ * (K + C₁ * (P + Q) + (F + C₁ * (P + Q))) + Q : ℝ≥0) : ℝ) ≤
      (C₀ * (1 + 2 * C₁) + C₁ + 1) * (K + F + P + Q) := by
    push_cast
    nlinarith [C₀.coe_nonneg, C₁.coe_nonneg, mul_nonneg C₀.coe_nonneg C₁.coe_nonneg,
      K.coe_nonneg, F.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]
  have hle' : (C₀ * ((K + C₁ * (P + Q) : ℝ≥0) + (F + C₁ * (P + Q) : ℝ≥0)) : ℝ) + C₁ * (P + Q) ≤
      (C₀ * (1 + 2 * C₁) + C₁ + 1 : ℝ≥0) * (K + F + P + Q) := by
    push_cast
    nlinarith [C₀.coe_nonneg, C₁.coe_nonneg, mul_nonneg C₀.coe_nonneg C₁.coe_nonneg,
      K.coe_nonneg, F.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]
  refine ⟨fun z hz => ?_, h2.mono_const (by exact_mod_cast hle),
    fun z hz => (h1 z hz).trans hle', fun z hz => (h2' z hz).trans hle'⟩
  -- `|u| ≤ |w| + |φ| ≤ C₀ (F + C₁ (P + Q)) + P`.
  rw [show u z = (u - φ) z + φ z by simp]
  refine (abs_add_le _ _).trans ((add_le_add (hw0 z hz) (hP z hz)).trans ?_)
  push_cast
  nlinarith [C₀.coe_nonneg, C₁.coe_nonneg, mul_nonneg C₀.coe_nonneg C₁.coe_nonneg,
    F.coe_nonneg, P.coe_nonneg, Q.coe_nonneg]

end TauCeti.PDE
