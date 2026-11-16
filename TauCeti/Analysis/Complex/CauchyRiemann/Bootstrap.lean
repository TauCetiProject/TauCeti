/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher

/-!
# Interior elliptic bootstrapping for planar nonlinear Cauchy–Riemann equations

Let `V` be a finite-dimensional real normed space, `U ⊆ ℂ` be open, and `u : ℂ → V` be a weak
solution of the nonlinear Cauchy–Riemann equation `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `U` in the
sense of `TauCeti.IsWeakCauchyRiemannOn p U J η u`, with `2 < p ≤ ∞`. Suppose `J(z, u z)² = -1`
on `U` and `J`, `η` are `C^ℓ` on an open neighbourhood `W ⊆ ℂ × V` of the graph of `u` over `U`.

This file proves the interior elliptic bootstrapping theorem (McDuff–Salamon, Theorem B.4.1):

* If `2 < p < ∞` and `J`, `η` are `C^ℓ` on `W`, then `u ∈ W^{ℓ + 1, p}_loc(U)`
  (`TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn`).
* For any `2 < p ≤ ∞` and any smoothness order `n : ℕ∞` (both finite orders `ℓ : ℕ` and `∞`), if
  `J` and `η` are `C^n` on `W`, then `u` is `C^n` on `U`
  (`TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn`). In particular, when `n ≥ 1`, `u`
  solves the classical pointwise Cauchy–Riemann equation on `U` by
  `TauCeti.isWeakCauchyRiemannOn_iff_of_contDiffOn`, and when `2 < p < ∞` and `n = ℓ` is finite,
  the `ℓ`-th derivative of `u` is locally Hölder continuous with exponent `1 - 2 / p` by
  `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact`.

## Proof

Induction on `ℓ : ℕ` for `2 < p < ∞`. At `ℓ = 0`, `u ∈ W^{1,p}_loc(U)` is immediate from
`TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_one`. At `ℓ = k + 1`, the induction hypothesis gives
`u ∈ W^{k + 1, p}_loc(U)`. Because `p > 2` and `u` is continuous on `U`, the higher-order Sobolev
chain rule (`TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ`) places `z ↦ J z (u z)` and
`z ↦ η z (u z)` in `W^{k + 1, p}_loc(U)`. Viewing the nonlinear equation as a linear equation with
frozen coefficients `z ↦ J z (u z)` and right-hand side `z ↦ η z (u z)`, higher-order linear
regularity (`TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`) boosts `u` to `W^{k + 2, p}_loc(U)`.

For `C^n` regularity (`n : ℕ∞`, `2 < p ≤ ∞`), dropping to the finite exponent `q = min p 3 ∈ (2, ∞)`
gives `u ∈ W^{ℓ + 1, q}_loc(U)` for every finite `ℓ ≤ n`; Morrey's embedding
(`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`) yields a `C^ℓ` representative agreeing almost
everywhere with `u`, which agrees with `u` everywhere on `U` by continuity of `u`.

## Main declarations

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn`: `W^{ℓ + 1, p}_loc` bootstrapping for
  `C^ℓ` coefficients on an open neighbourhood of the graph (`2 < p < ∞`).
* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiff`: the global `ContDiff` specialisation.
* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn_target`: the domain-independent form
  `∂ₛu + J(u) ∂ₜu = η(u)` on an open subset of `V`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn`: `C^n` bootstrapping (`n : ℕ∞`,
  including `∞`) for any `2 < p ≤ ∞`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_contDiff`: the global `ContDiff` specialisation.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn_target`: the domain-independent form
  on an open subset of `V`.
* `TauCeti.contDiffOn_of_contDiffOn_one_cauchyRiemann`: classical `C¹` solutions with `C^n`
  coefficients are `C^n`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem B.4.1 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} {U : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-! ### Sobolev bootstrapping -/

/-- **Interior Sobolev bootstrapping for planar nonlinear Cauchy–Riemann equations.**
Let `2 < p < ∞` and `ℓ : ℕ`. If `u` is a weak solution of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on an
open set `U ⊆ ℂ` (`TauCeti.IsWeakCauchyRiemannOn p U J η u`), `J` and `η` are `C^ℓ` on an open
neighbourhood `W ⊆ ℂ × V` of the graph of `u` over `U`, and `J(z, u z)² = -1` on `U`, then
`u ∈ W^{ℓ + 1, p}_loc(U)`. -/
theorem IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn
    (hu : IsWeakCauchyRiemannOn p U J η u) (hU : IsOpen U) (hp : 2 < p) (hp_top : p ≠ ⊤)
    {ℓ : ℕ} {W : Set (ℂ × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ (Function.uncurry J) W) (hη : ContDiffOn ℝ ℓ (Function.uncurry η) W)
    (hgraph : ∀ z ∈ U, (z, u z) ∈ W) (hJsq : ∀ z ∈ U, J z (u z) * J z (u z) = -1) :
    MemWkpLoc p U (ℓ + 1) u := by
  let Ω : Opens ℂ := ⟨U, hU⟩
  have hp_inv : p⁻¹ + p⁻¹ < 1 := by
    have hlt : p⁻¹ < (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hp
    exact (ENNReal.add_lt_add hlt hlt).trans_eq ENNReal.inv_two_add_inv_two
  obtain ⟨-, -, D, hD, -, hae⟩ := (isWeakCauchyRiemannOn_iff_of_isOpen (Ω := Ω)).1 hu
  have heq : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ),
      D z 1 + J z (u z) (D z I) + (0 : V →L[ℝ] V) (u z) = η z (u z) := by
    filter_upwards [hae] with z hz
    simpa using hz
  have hJsq_ae : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), J z (u z) * J z (u z) = -1 :=
    (ae_restrict_iff' hU.measurableSet).2 (.of_forall hJsq)
  lift p to ℝ≥0 using hp_top
  have hp' : (2 : ℝ≥0) < p := by exact_mod_cast hp
  induction ℓ with
  | zero => exact hu.memWkpLoc_one
  | succ k ih =>
    have hu_prev : MemWkpLoc p Ω (k + 1) u :=
      ih (hJ.of_le (by exact_mod_cast Nat.le_succ k)) (hη.of_le (by exact_mod_cast Nat.le_succ k))
    have hJu : MemWkpLoc p Ω (k + 1) (fun z => J z (u z)) :=
      hu_prev.contDiffOn_comp_graph_succ hp' hu.continuousOn hW (by exact_mod_cast hJ) hgraph
    have hηu : MemWkpLoc p Ω (k + 1) (fun z => η z (u z)) :=
      hu_prev.contDiffOn_comp_graph_succ hp' hu.continuousOn hW (by exact_mod_cast hη) hgraph
    have hmax : max 1 (k + 1) = k + 1 := max_eq_right (Nat.succ_le_succ (Nat.zero_le k))
    exact memWkpLoc_succ_of_ae_cauchyRiemann (Ω := Ω) hp ENNReal.coe_ne_top hp_inv le_rfl
      (S := fun _ => 0) (hmax ▸ hJu) memWkpLoc_zero_fun hJsq_ae hu.memWkpLoc_one hD hηu heq

/-- **Interior Sobolev bootstrapping for globally `C^ℓ` coefficients.** Specialisation of
`TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn` with `W = Set.univ`. -/
theorem IsWeakCauchyRiemannOn.memWkpLoc_of_contDiff
    (hu : IsWeakCauchyRiemannOn p U J η u) (hU : IsOpen U) (hp : 2 < p) (hp_top : p ≠ ⊤)
    {ℓ : ℕ} (hJ : ContDiff ℝ ℓ (Function.uncurry J)) (hη : ContDiff ℝ ℓ (Function.uncurry η))
    (hJsq : ∀ z ∈ U, J z (u z) * J z (u z) = -1) :
    MemWkpLoc p U (ℓ + 1) u :=
  hu.memWkpLoc_of_contDiffOn hU hp hp_top isOpen_univ hJ.contDiffOn hη.contDiffOn
    (fun _ _ => trivial) hJsq

/-- **Interior Sobolev bootstrapping for domain-independent equations `∂ₛu + J(u) ∂ₜu = η(u)`.**
If `J` and `η` are `C^ℓ` on an open set `W ⊆ V` containing `u '' U` and `J(u z)² = -1` on `U`,
then any weak solution with `2 < p < ∞` belongs to `W^{ℓ + 1, p}_loc(U)`. -/
theorem IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn_target
    {J : V → V →L[ℝ] V} {η : V → V}
    (hu : IsWeakCauchyRiemannOn p U (fun _ => J) (fun _ => η) u) (hU : IsOpen U)
    (hp : 2 < p) (hp_top : p ≠ ⊤) {ℓ : ℕ} {W : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ J W) (hη : ContDiffOn ℝ ℓ η W)
    (huW : MapsTo u U W) (hJsq : ∀ z ∈ U, J (u z) * J (u z) = -1) :
    MemWkpLoc p U (ℓ + 1) u :=
  hu.memWkpLoc_of_contDiffOn hU hp hp_top (isOpen_univ.prod hW)
    (hJ.comp contDiffOn_snd fun _ hx => hx.2) (hη.comp contDiffOn_snd fun _ hx => hx.2)
    (fun _ hz => ⟨trivial, huW hz⟩) hJsq

/-! ### Classical `C^n` and `C^∞` bootstrapping -/

/-- **Interior `C^n` and `C^∞` bootstrapping for planar nonlinear Cauchy–Riemann equations.**
Let `2 < p ≤ ∞` and `n : ℕ∞` (either a finite order `ℓ : ℕ` or `∞`). If `u` is a weak solution of
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` on an open set `U ⊆ ℂ`, `J` and `η` are `C^n` on an open
neighbourhood `W ⊆ ℂ × V` of the graph of `u` over `U`, and `J(z, u z)² = -1` on `U`, then `u` is
`C^n` on `U`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn
    (hu : IsWeakCauchyRiemannOn p U J η u) (hU : IsOpen U) (hp : 2 < p) {n : ℕ∞}
    {W : Set (ℂ × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (Function.uncurry J) W) (hη : ContDiffOn ℝ n (Function.uncurry η) W)
    (hgraph : ∀ z ∈ U, (z, u z) ∈ W) (hJsq : ∀ z ∈ U, J z (u z) * J z (u z) = -1) :
    ContDiffOn ℝ n u U := by
  have hnat (ℓ : ℕ) (hJℓ : ContDiffOn ℝ ℓ (Function.uncurry J) W)
      (hηℓ : ContDiffOn ℝ ℓ (Function.uncurry η) W) : ContDiffOn ℝ ℓ u U := by
    let q : ℝ≥0∞ := min p 3
    have hq2 : 2 < q := lt_min hp (by norm_num)
    have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
    have hw : MemWkpLoc q U (ℓ + 1) u :=
      (hu.mono_exponent (min_le_left _ _)).memWkpLoc_of_contDiffOn hU hq2 hq_top hW hJℓ hηℓ
        hgraph hJsq
    obtain ⟨g, hg, hug⟩ := hw.exists_contDiffOn_ae_eq (Ω := ⟨U, hU⟩) hq2
    have heq : EqOn u g U := Measure.eqOn_open_of_ae_eq hug hU hu.continuousOn hg.continuousOn
    exact hg.congr heq
  cases n with
  | top => exact contDiffOn_infty.2 fun ℓ => hnat ℓ (hJ.of_le (by simp)) (hη.of_le (by simp))
  | coe ℓ => exact hnat ℓ (by exact_mod_cast hJ) (by exact_mod_cast hη)

/-- **Interior `C^n` and `C^∞` bootstrapping for globally `C^n` coefficients.** Specialisation of
`TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn` with `W = Set.univ`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn_of_contDiff
    (hu : IsWeakCauchyRiemannOn p U J η u) (hU : IsOpen U) (hp : 2 < p) {n : ℕ∞}
    (hJ : ContDiff ℝ n (Function.uncurry J)) (hη : ContDiff ℝ n (Function.uncurry η))
    (hJsq : ∀ z ∈ U, J z (u z) * J z (u z) = -1) :
    ContDiffOn ℝ n u U :=
  hu.contDiffOn_of_contDiffOn hU hp isOpen_univ hJ.contDiffOn hη.contDiffOn
    (fun _ _ => trivial) hJsq

/-- **Interior `C^n` and `C^∞` bootstrapping for domain-independent equations
`∂ₛu + J(u) ∂ₜu = η(u)`.** If `J` and `η` are `C^n` (`n : ℕ∞`) on an open set `W ⊆ V` containing
`u '' U` and `J(u z)² = -1` on `U`, then any weak solution with `2 < p ≤ ∞` is `C^n` on `U`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn_of_contDiffOn_target
    {J : V → V →L[ℝ] V} {η : V → V}
    (hu : IsWeakCauchyRiemannOn p U (fun _ => J) (fun _ => η) u) (hU : IsOpen U) (hp : 2 < p)
    {n : ℕ∞} {W : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n J W) (hη : ContDiffOn ℝ n η W)
    (huW : MapsTo u U W) (hJsq : ∀ z ∈ U, J (u z) * J (u z) = -1) :
    ContDiffOn ℝ n u U :=
  hu.contDiffOn_of_contDiffOn hU hp (isOpen_univ.prod hW)
    (hJ.comp contDiffOn_snd fun _ hx => hx.2) (hη.comp contDiffOn_snd fun _ hx => hx.2)
    (fun _ hz => ⟨trivial, huW hz⟩) hJsq

/-- **Classical `C¹` bootstrapping.** A `C¹` solution of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on an open
set `U ⊆ ℂ` with `C^n` coefficients (`n : ℕ∞`) on an open neighbourhood `W ⊆ ℂ × V` of its graph
and `J(z, u z)² = -1` on `U` is `C^n` on `U`. -/
theorem contDiffOn_of_contDiffOn_one_cauchyRiemann (hU : IsOpen U) {n : ℕ∞}
    {W : Set (ℂ × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (Function.uncurry J) W) (hη : ContDiffOn ℝ n (Function.uncurry η) W)
    (hu : ContDiffOn ℝ 1 u U) (hgraph : ∀ z ∈ U, (z, u z) ∈ W)
    (hJsq : ∀ z ∈ U, J z (u z) * J z (u z) = -1)
    (heq : ∀ z ∈ U, fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z)) :
    ContDiffOn ℝ n u U := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hw := isWeakCauchyRiemannOn_of_contDiffOn (p := 3) (Ω := ⟨U, hU⟩) hu heq
  exact hw.contDiffOn_of_contDiffOn hU (by norm_num) hW hJ hη hgraph hJsq

/-! ### Non-vacuity checks -/

section Examples

-- Check that `memWkpLoc_of_contDiffOn` and `contDiffOn_of_contDiffOn` instantiate cleanly on the
-- standard structure `J = i` on `ℂ` for finite orders, `∞`, and `p = ⊤`.
example (Ω : Opens ℂ) (ℓ : ℕ) : MemWkpLoc 3 Ω (ℓ + 1) (id : ℂ → ℂ) :=
  (isWeakCauchyRiemannOn_id (p := 3) (Ω := Ω)).memWkpLoc_of_contDiff Ω.isOpen (by norm_num)
    (by norm_num) contDiff_const contDiff_const fun _ _ => by
      ext x
      simp [← mul_assoc]

example (Ω : Opens ℂ) : ContDiffOn ℝ ∞ (id : ℂ → ℂ) Ω :=
  (isWeakCauchyRiemannOn_id (p := ⊤) (Ω := Ω)).contDiffOn_of_contDiff Ω.isOpen (by simp)
    contDiff_const contDiff_const fun _ _ => by
      ext x
      simp [← mul_assoc]

example (Ω : Opens ℂ) (ℓ : ℕ) : ContDiffOn ℝ ℓ (id : ℂ → ℂ) Ω :=
  (isWeakCauchyRiemannOn_id (p := ⊤) (Ω := Ω)).contDiffOn_of_contDiff Ω.isOpen (by simp)
    contDiff_const contDiff_const fun _ _ => by
      ext x
      simp [← mul_assoc]

example : ContDiffOn ℝ ∞ (id : ℂ → ℂ) (Metric.ball 0 1) :=
  let h := isWeakCauchyRiemannOn_id (p := ⊤) (Ω := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩)
  h.contDiffOn_of_contDiffOn_target Metric.isOpen_ball (by simp) Metric.isOpen_ball
    contDiffOn_const contDiffOn_const (fun _ hz => hz) fun _ _ => by
      ext x
      simp [← mul_assoc]

example : ContDiffOn ℝ ∞ (id : ℂ → ℂ) (Metric.ball 0 1) :=
  contDiffOn_of_contDiffOn_one_cauchyRiemann Metric.isOpen_ball isOpen_univ
    (J := fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (η := fun _ _ => 0) contDiffOn_const
    contDiffOn_const contDiff_id.contDiffOn (fun _ _ => trivial)
    (fun _ _ => by ext x; simp [← mul_assoc])
    fun _ _ => by simp

end Examples

end TauCeti
