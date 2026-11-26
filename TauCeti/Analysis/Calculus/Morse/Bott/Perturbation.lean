/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Bott
public import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# Perturbing a Morse–Bott function by a function on its critical submanifold

Let `f (b, v)` be a function on a product `P × F` of finite-dimensional real normed spaces whose
zero section `P × {0}` is a nondegenerate (Morse–Bott) critical submanifold, as in
`TauCeti.Analysis.Calculus.Morse.Bott`. A function `h` on the critical submanifold `P` extends to
`P × F` by making it constant in the normal directions, `(b, v) ↦ h b`, and cut off away from the
zero section by a function `ρ` of the normal coordinate equal to `1` near `0`. This file studies
the small perturbation

`f_ε (b, v) = f (b, v) + ε ρ(v) h(b)`.

Over a compact set `K ⊆ P` of Morse–Bott points, in a tube `‖v‖ ≤ r` of fixed radius and for small
`ε ≠ 0`, the critical points `(b, v)` of `f_ε` with `b ∈ K` are exactly the points `(b, 0)` of the
zero section with `b` critical for `h`. Each of them is nondegenerate for `f_ε` exactly when `b`
is nondegenerate for `h`, and for `ε > 0` its Morse index is `ind_h(b) + ind_f(b, 0)`, the index
of `h` plus the index of the normal Hessian. This is the perturbation through which the cascade
complex of a Morse–Bott function, built from auxiliary Morse functions on the critical components,
is compared with the Morse complex of a Morse function.

**Near the zero section.** Where `ρ = 1` the perturbation is `f + h ∘ Prod.fst`, after absorbing
`ε` into `h`, and no smallness is needed. The derivative of `h ∘ Prod.fst` vanishes in the fibre
directions, while near a Morse–Bott point the fibre derivative of `f` grows linearly with the
distance to the zero section (`TauCeti.exists_mul_norm_snd_le_norm_fderiv_comp_inr`): the vertical
Hessian is invertible. So a critical point of `f + h ∘ Prod.fst` lies on the zero section, where
`f` is critical, and is therefore a critical point of `h`
(`TauCeti.eventually_forall_fderiv_add_comp_fst_eq_zero_iff`). The neighbourhood depends only on
`f`, not on `h`. At such a point the Hessian is block-diagonal: the Hessian of `f` at `(b, 0)`
involves only the fibre directions, and that of `h ∘ Prod.fst` only the base directions
(`TauCeti.hessianQuadraticForm_add_comp_fst`). Hence the Morse index is additive
(`TauCeti.morseIndex_add_comp_fst`), and the critical point is nondegenerate exactly when it is
nondegenerate for `h` (`TauCeti.isNondegenerateCriticalPoint_add_comp_fst_iff`).

**The cutoff region.** Over a compact set `K ⊆ P` of Morse–Bott points the fibre derivative of `f`
vanishes only on the zero section, uniformly in a tube `K × closedBall 0 r` whose radius depends
only on `f` and `K`. On the compact shell of that tube where `ρ` may differ from `1`, the fibre
derivative of `f` is therefore bounded below, while the fibre derivative `ε h(b) Dρ(v)` of the
perturbation is at most `|ε|` times a bound. So for small `ε ≠ 0` the shell contains no critical
point, and the critical points of `f_ε` in the tube are exactly the points `(b, 0)` with `b ∈ K`
critical for `h` (`TauCeti.exists_forall_fderiv_add_mul_mul_eq_zero_iff`). For `ε > 0` their Morse
indices are `ind_h(b) + ind_f(b, 0)` (`TauCeti.morseIndex_add_mul_mul`).

## Main results

* `TauCeti.eventually_forall_fderiv_add_comp_fst_eq_zero_iff`: near a Morse–Bott point, the
  critical points of `f + h ∘ Prod.fst` are the critical points of `h` on the zero section, for
  every `h`.
* `TauCeti.hessianQuadraticForm_add_comp_fst`, `TauCeti.morseIndex_add_comp_fst`,
  `TauCeti.isNondegenerateCriticalPoint_add_comp_fst_iff`: the Hessian, Morse index and
  nondegeneracy of `f + h ∘ Prod.fst` at a point of the zero section.
* `TauCeti.exists_forall_fderiv_add_mul_mul_eq_zero_iff`: over a compact set of Morse–Bott points,
  the critical points of the small cutoff perturbation `f + ε ρ h` near the zero section.
* `TauCeti.morseIndex_add_mul_mul`, `TauCeti.isNondegenerateCriticalPoint_add_mul_mul_iff`: their
  Morse indices and nondegeneracy.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott homology and the comparison with a
  perturbation).
* A. Banyaga and D. E. Hurtubise, *Morse–Bott homology*, Transactions of the American
  Mathematical Society 362 (2010), 3997–4043 (perturbing a Morse–Bott function by Morse functions
  on its critical submanifolds).
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P × F → ℝ} {a : P}

/-! ### Perturbing by a function on the base -/

/-- Near a Morse–Bott point of the zero section, `f` is `C²`, critical along the zero section, and
its fibre derivative vanishes only on the zero section. -/
private theorem eventually_fderiv_comp_inr_eq_zero_imp [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f (a, 0)) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F)) :
    ∀ᶠ z in 𝓝 (a, (0 : F)), ContDiffAt ℝ 2 f z ∧ fderiv ℝ f (z.1, 0) = 0 ∧
      (fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F = 0 → z.2 = 0) := by
  obtain ⟨c, hc, hcz⟩ := exists_mul_norm_snd_le_norm_fderiv_comp_inr hf hcrit hker
  filter_upwards [hf.eventually (by simp), (continuous_fst.tendsto' _ _ rfl).eventually hcrit, hcz]
    with z hz hz0 hzc
  refine ⟨hz, hz0, fun hv ↦ ?_⟩
  rw [hv, norm_zero] at hzc
  exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hzc hc)

/-- The critical points of `f + h ∘ Prod.fst` at a point `z` where `f` is critical on the zero
section through `z`, and where the fibre derivative of `f` vanishes only on the zero section. -/
private theorem fderiv_add_comp_fst_eq_zero_iff {h : P → ℝ} {z : P × F}
    (hzf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z.1)
    (hz0 : fderiv ℝ f (z.1, 0) = 0)
    (hzv : fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F = 0 → z.2 = 0) :
    fderiv ℝ (fun y ↦ f y + h y.1) z = 0 ↔ z.2 = 0 ∧ fderiv ℝ h z.1 = 0 := by
  have hz : z.2 = 0 → fderiv ℝ f z = 0 := fun h2 ↦ by rwa [← Prod.mk.eta (p := z), h2]
  rw [fderiv_add_comp_fst hzf hh]
  constructor
  · intro h0
    have h2 : z.2 = 0 := hzv <| by
      ext w
      simpa using congr($h0 (0, w))
    rw [hz h2, zero_add] at h0
    exact ⟨h2, ContinuousLinearMap.comp_fst_eq_zero_iff.1 h0⟩
  · rintro ⟨h2, hh0⟩
    simp [hz h2, hh0]

/-- **Critical points of a perturbation by a function on the critical submanifold.** If `f` is
`C²` at `(a, 0)`, every point `(b, 0)` with `b` near `a` is critical, and the kernel of the Hessian
at `(a, 0)` consists of base directions, then near `(a, 0)`, for every function `h` on the base
differentiable at `z.1`, the point `z` is critical for `z ↦ f z + h z.1` exactly when it lies on
the zero section and `z.1` is critical for `h`. The neighbourhood depends only on `f`. -/
theorem eventually_forall_fderiv_add_comp_fst_eq_zero_iff [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f (a, 0)) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F)) :
    ∀ᶠ z in 𝓝 (a, (0 : F)), ∀ h : P → ℝ, DifferentiableAt ℝ h z.1 →
      (fderiv ℝ (fun y ↦ f y + h y.1) z = 0 ↔ z.2 = 0 ∧ fderiv ℝ h z.1 = 0) := by
  filter_upwards [eventually_fderiv_comp_inr_eq_zero_imp hf hcrit hker]
    with z ⟨hzf, hz0, hzv⟩ h hh
  exact fderiv_add_comp_fst_eq_zero_iff (hzf.differentiableAt two_ne_zero) hh hz0 hzv

variable {h : P → ℝ}

/-- **The Hessian of a perturbation by a function on the critical submanifold.** If `f` is `C²`
at `(a, 0)`, every point `(b, 0)` with `b` near `a` is critical, and `h` is `C²` at `a`, then the
Hessian quadratic form of `z ↦ f z + h z.1` at `(a, 0)` is the orthogonal product of the Hessian
of `h` at `a` and the vertical Hessian of `f`, that of `v ↦ f (a, v)` at `0`. -/
theorem hessianQuadraticForm_add_comp_fst (hf : ContDiffAt ℝ 2 f (a, 0))
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0) (hh : ContDiffAt ℝ 2 h a) :
    hessianQuadraticForm (fun z ↦ f z + h z.1) (a, 0) =
      (hessianQuadraticForm h a).prod (hessianQuadraticForm (fun v ↦ f (a, v)) 0) := by
  have hfst : hessianQuadraticForm (fun z : P × F ↦ h z.1) (a, 0) =
      (hessianQuadraticForm h a).comp (LinearMap.fst ℝ P F) :=
    (ContinuousLinearMap.fst ℝ P F).hessianQuadraticForm_comp hh
  rw [← Pi.add_def f (fun z ↦ h z.1),
    hessianQuadraticForm_add (g := fun z : P × F ↦ h z.1) hf (hh.comp (a, 0) contDiffAt_fst), hfst,
    hessianQuadraticForm_eq_prod_slice_right hf hcrit]
  ext ⟨u, v⟩
  simp [add_comm]

/-- **The Morse index of a perturbation by a function on the critical submanifold is additive.**
If `f` is `C²` at `(a, 0)`, every point `(b, 0)` with `b` near `a` is critical, and `h` is `C²` at
`a`, then the Morse index of `z ↦ f z + h z.1` at `(a, 0)` is the index of `h` at `a` plus the
index of `f` at `(a, 0)`. -/
theorem morseIndex_add_comp_fst [FiniteDimensional ℝ P] [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f (a, 0)) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hh : ContDiffAt ℝ 2 h a) :
    morseIndex (fun z ↦ f z + h z.1) (a, 0) = morseIndex h a + morseIndex f (a, 0) := by
  rw [← morseIndex_slice_right hf hcrit]
  simp only [morseIndex_def, hessianQuadraticForm_add_comp_fst hf hcrit hh,
    QuadraticForm.sigNeg_prod]

/-- **Nondegenerate critical points of a perturbation by a function on the critical
submanifold.** If `f` is `C²` at `(a, 0)`, every point `(b, 0)` with `b` near `a` is critical, the
kernel of the Hessian at `(a, 0)` consists of base directions, and `h` is `C²` at `a`, then
`(a, 0)` is a nondegenerate critical point of `z ↦ f z + h z.1` exactly when `a` is a
nondegenerate critical point of `h`. -/
theorem isNondegenerateCriticalPoint_add_comp_fst_iff [FiniteDimensional ℝ P]
    [FiniteDimensional ℝ F] (hf : ContDiffAt ℝ 2 f (a, 0))
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F))
    (hh : ContDiffAt ℝ 2 h a) :
    IsNondegenerateCriticalPoint (fun z ↦ f z + h z.1) (a, 0) ↔
      IsNondegenerateCriticalPoint h a := by
  have hψ := isNondegenerateCriticalPoint_slice_right_of_ker_le hf hcrit hker
  -- The Hessian is that of the separated sum of `h` and the normal restriction of `f`.
  have hQ : hessianQuadraticForm (fun z ↦ f z + h z.1) (a, 0) =
      hessianQuadraticForm (h ∘ Prod.fst + (fun v ↦ f (a, v)) ∘ Prod.snd) (a, 0) := by
    rw [hessianQuadraticForm_add_comp_fst hf hcrit hh,
      hessianQuadraticForm_comp_fst_add_comp_snd hh hψ.contDiffAt]
  have hD : fderiv ℝ (fun z ↦ f z + h z.1) (a, 0) =
      fderiv ℝ h a ∘L ContinuousLinearMap.fst ℝ P F := by
    rw [fderiv_add_comp_fst (hf.differentiableAt two_ne_zero) (hh.differentiableAt two_ne_zero),
      hcrit.self_of_nhds, zero_add]
  rw [isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate, hQ, hD]
  constructor
  · rintro ⟨-, hD0, hnd⟩
    have hh0 : fderiv ℝ h a = 0 := ContinuousLinearMap.comp_fst_eq_zero_iff.1 hD0
    refine (isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff.1 <|
      isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate.2
        ⟨(hh.comp (a, 0) contDiffAt_fst).add (hψ.contDiffAt.comp (a, 0) contDiffAt_snd),
          (fderiv_comp_fst_add_comp_snd_eq_zero_iff (hh.differentiableAt two_ne_zero)
            (hψ.contDiffAt.differentiableAt two_ne_zero)).2 ⟨hh0, hψ.fderiv_eq_zero⟩,
          hnd⟩).1
  · intro hha
    exact ⟨hf.add (hh.comp (a, 0) contDiffAt_fst), by simp [hha.fderiv_eq_zero],
      (hha.comp_fst_add_comp_snd hψ).hessianQuadraticForm_nondegenerate⟩

/-! ### Small cutoff perturbations -/

/-- Over a compact set of Morse–Bott points, the fibre derivative of `f` vanishes only on the zero
section, uniformly in a tube around it, in which `f` is `C²` and critical along the zero
section. -/
private theorem exists_pos_forall_fderiv_comp_inr_eq_zero_imp [FiniteDimensional ℝ F]
    {K : Set P} (hK : IsCompact K) (hf : ∀ a ∈ K, ContDiffAt ℝ 2 f (a, 0))
    (hcrit : ∀ a ∈ K, ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : ∀ a ∈ K,
      (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F)) :
    ∃ r > 0, ∀ b ∈ K, ∀ v : F, ‖v‖ < r → ContDiffAt ℝ 2 f (b, v) ∧ fderiv ℝ f (b, 0) = 0 ∧
      (fderiv ℝ f (b, v) ∘L ContinuousLinearMap.inr ℝ P F = 0 → v = 0) := by
  have hloc : ∀ a ∈ K, ∀ᶠ w : F × P in 𝓝 ((0 : F), a), ContDiffAt ℝ 2 f (w.2, w.1) ∧
      fderiv ℝ f (w.2, 0) = 0 ∧
        (fderiv ℝ f (w.2, w.1) ∘L ContinuousLinearMap.inr ℝ P F = 0 → w.1 = 0) := fun a ha ↦
    (continuous_swap.tendsto' ((0 : F), a) (a, 0) rfl).eventually
      (eventually_fderiv_comp_inr_eq_zero_imp (hf a ha) (hcrit a ha) (hker a ha))
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (hK.eventually_forall_of_forall_eventually
      (P := fun (v : F) (b : P) ↦ ContDiffAt ℝ 2 f (b, v) ∧ fderiv ℝ f (b, 0) = 0 ∧
        (fderiv ℝ f (b, v) ∘L ContinuousLinearMap.inr ℝ P F = 0 → v = 0)) hloc)
  exact ⟨r, hr, fun b hb v hv ↦ hball v (by simpa using hv) b hb⟩

/-- On a compact set of points at which `f` is `C¹` and its fibre derivative does not vanish, the
fibre derivative is bounded below by a positive constant. -/
private theorem exists_pos_forall_le_norm_fderiv_comp_inr {T : Set (P × F)} (hT : IsCompact T)
    (hf : ∀ z ∈ T, ContDiffAt ℝ 1 f z)
    (hne : ∀ z ∈ T, fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F ≠ 0) :
    ∃ m > 0, ∀ z ∈ T, m ≤ ‖fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F‖ := by
  refine hT.exists_forall_le' (fun z hz ↦ ?_) fun z hz ↦ norm_pos_iff.2 (hne z hz)
  have hc := ((hf z hz).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ((ContinuousLinearMap.precomp ℝ
    (ContinuousLinearMap.inr ℝ P F)).continuous.continuousAt.comp hc).norm.continuousWithinAt

/-- A point at which the fibre derivative of `f` is larger than that of the perturbation
`ε ρ(v) h(b)` is not a critical point of `f + ε ρ h`. -/
private theorem fderiv_add_mul_mul_ne_zero {ρ : F → ℝ} {h : P → ℝ} {z : P × F} {ε m : ℝ}
    (hzf : DifferentiableAt ℝ f z) (hρ : DifferentiableAt ℝ ρ z.2)
    (hh : DifferentiableAt ℝ h z.1)
    (hm : m ≤ ‖fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F‖)
    (hε : |ε| * ‖h z.1 • fderiv ℝ ρ z.2‖ < m) :
    fderiv ℝ (fun y ↦ f y + ε * (ρ y.2 * h y.1)) z ≠ 0 := by
  intro h0
  have hd : HasFDerivAt (fun y : P × F ↦ f y + ε * (ρ y.2 * h y.1))
      (fderiv ℝ f z + ε • (ρ z.2 • (fderiv ℝ h z.1 ∘L ContinuousLinearMap.fst ℝ P F) +
        h z.1 • (fderiv ℝ ρ z.2 ∘L ContinuousLinearMap.snd ℝ P F))) z :=
    hzf.hasFDerivAt.add (((hρ.hasFDerivAt.comp z hasFDerivAt_snd).mul
      (hh.hasFDerivAt.comp z hasFDerivAt_fst)).const_mul ε)
  -- The fibre derivative of `f` would cancel that of the perturbation.
  have hcancel : fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ P F =
      -(ε • (h z.1 • fderiv ℝ ρ z.2)) := by
    refine eq_neg_of_add_eq_zero_left ?_
    simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc] using
      congr($(hd.fderiv.symm.trans h0) ∘L ContinuousLinearMap.inr ℝ P F)
  rw [hcancel, norm_neg, norm_smul, Real.norm_eq_abs] at hm
  linarith

/-- **Critical points of a small cutoff perturbation of a Morse–Bott function.** Let `K ⊆ P` be a
compact set of Morse–Bott points of the zero section: at each `a ∈ K`, `f` is `C²` at `(a, 0)`,
every point `(b, 0)` with `b` near `a` is critical, and the kernel of the Hessian at `(a, 0)`
consists of base directions. Then there is a radius `r > 0`, depending only on `f` and `K`, with
the following property. For every `C¹` cutoff `ρ` on the fibre equal to `1` near `0` and every
function `h` on the base differentiable at the points of `K`, there is `ε₀ > 0` such that for
`0 < |ε| < ε₀` the critical points `z` of `f_ε (b, v) = f (b, v) + ε ρ(v) h(b)` with `z.1 ∈ K`
and `‖z.2‖ ≤ r` are exactly the points `(b, 0)` of the zero section at which `h` is critical. -/
theorem exists_forall_fderiv_add_mul_mul_eq_zero_iff [FiniteDimensional ℝ F] {K : Set P}
    (hK : IsCompact K)
    (hf : ∀ a ∈ K, ContDiffAt ℝ 2 f (a, 0))
    (hcrit : ∀ a ∈ K, ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : ∀ a ∈ K,
      (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F)) :
    ∃ r > 0, ∀ {ρ : F → ℝ} {h : P → ℝ}, ContDiff ℝ 1 ρ → (∀ᶠ v in 𝓝 0, ρ v = 1) →
      (∀ b ∈ K, DifferentiableAt ℝ h b) → ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| < ε₀ →
        ∀ z : P × F, z.1 ∈ K → ‖z.2‖ ≤ r →
          (fderiv ℝ (fun y ↦ f y + ε * (ρ y.2 * h y.1)) z = 0 ↔
            z.2 = 0 ∧ fderiv ℝ h z.1 = 0) := by
  obtain ⟨r₀, hr₀, htube⟩ := exists_pos_forall_fderiv_comp_inr_eq_zero_imp hK hf hcrit hker
  refine ⟨r₀ / 2, by positivity, fun {ρ h} hρ hρ1 hh ↦ ?_⟩
  obtain ⟨δ, hδ, hδρ⟩ := Metric.eventually_nhds_iff_ball.1 hρ1
  -- The shell of the tube in which `ρ` may differ from `1`.
  set T : Set (P × F) := K ×ˢ (closedBall 0 (r₀ / 2) \ ball 0 δ)
  have hTc : IsCompact T := hK.prod ((isCompact_closedBall _ _).diff isOpen_ball)
  have hTtube : ∀ z ∈ T, z.1 ∈ K ∧ ‖z.2‖ < r₀ ∧ z.2 ≠ 0 := by
    rintro z ⟨hz1, hz2, hz2'⟩
    rw [mem_closedBall_zero_iff] at hz2
    rw [mem_ball_zero_iff, not_lt] at hz2'
    exact ⟨hz1, by linarith, norm_ne_zero_iff.1 (by linarith)⟩
  -- On the shell the fibre derivative of `f` is bounded below by some `m > 0` ...
  obtain ⟨m, hm, hmT⟩ := exists_pos_forall_le_norm_fderiv_comp_inr hTc
    (fun z hz ↦ ((htube z.1 (hTtube z hz).1 z.2 (hTtube z hz).2.1).1.of_le (by norm_num)))
    fun z hz hv ↦ (hTtube z hz).2.2 ((htube z.1 (hTtube z hz).1 z.2 (hTtube z hz).2.1).2.2 hv)
  -- ... while the fibre derivative of the perturbation is at most `|ε| M`.
  have hcont' : ContinuousOn (fun z : P × F ↦ h z.1 • fderiv ℝ ρ z.2) T :=
    ((continuousOn_of_forall_continuousAt fun b hb ↦ (hh b hb).continuousAt).comp continuousOn_fst
      fun z hz ↦ (hTtube z hz).1).smul ((hρ.continuous_fderiv one_ne_zero).comp_continuousOn
        continuousOn_snd)
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn hcont'
  have hM' : 0 < max M 0 + 1 := by positivity
  refine ⟨m / (max M 0 + 1), by positivity, fun ε hε hεm z hz1 hz2 ↦ ?_⟩
  have hz2' : ‖z.2‖ < r₀ := by linarith
  obtain ⟨hzf, hz0, hzv⟩ := htube z.1 hz1 z.2 hz2'
  have hzf' : DifferentiableAt ℝ f z := hzf.differentiableAt two_ne_zero
  by_cases hzδ : ‖z.2‖ < δ
  · -- Near the zero section `ρ = 1`, so the perturbation is `f + (ε h) ∘ Prod.fst`.
    have heq : (fun y : P × F ↦ f y + ε * (ρ y.2 * h y.1)) =ᶠ[𝓝 z]
        fun y ↦ f y + ε * h y.1 := by
      have hopen : IsOpen {y : P × F | ‖y.2‖ < δ} :=
        isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
      filter_upwards [hopen.mem_nhds hzδ] with y hy
      rw [hδρ y.2 (mem_ball_zero_iff.2 hy), one_mul]
    rw [heq.fderiv_eq, fderiv_add_comp_fst_eq_zero_iff (h := fun b ↦ ε * h b) hzf'
      (((hh z.1 hz1).const_mul ε)) hz0 (by simpa using hzv),
      fderiv_const_mul (hh z.1 hz1), smul_eq_zero, or_iff_right hε]
  · -- On the shell neither side holds.
    have hzT : z ∈ T := ⟨hz1, by simpa using hz2, by simpa using hzδ⟩
    refine iff_of_false (fderiv_add_mul_mul_ne_zero hzf' (hρ.differentiable one_ne_zero z.2)
      (hh z.1 hz1) (hmT z hzT) ?_) fun h2 ↦ (hTtube z hzT).2.2 h2.1
    calc |ε| * ‖h z.1 • fderiv ℝ ρ z.2‖ ≤ |ε| * (max M 0 + 1) := by
          gcongr
          linarith [hM z hzT, le_max_left M 0]
      _ < m / (max M 0 + 1) * (max M 0 + 1) := by gcongr
      _ = m := div_mul_cancel₀ m hM'.ne'

omit [NormedSpace ℝ P] [NormedSpace ℝ F] in
/-- The small cutoff perturbation agrees near a point of the zero section with the perturbation
by the rescaled base function. -/
private theorem add_mul_mul_eventuallyEq {ρ : F → ℝ} (hρ1 : ∀ᶠ v in 𝓝 0, ρ v = 1) (ε : ℝ)
    (b : P) :
    (fun y : P × F ↦ f y + ε * (ρ y.2 * h y.1)) =ᶠ[𝓝 (b, 0)]
      fun y ↦ f y + (ε • h) y.1 := by
  filter_upwards [(continuous_snd.tendsto' (b, (0 : F)) 0 rfl).eventually hρ1] with y hy
  simp [hy]

/-- **The Morse index of a small cutoff perturbation of a Morse–Bott function.** If `f` is `C²`
at `(b, 0)` and every point `(c, 0)` with `c` near `b` is critical, `ρ` is equal to `1` near `0`,
`h` is `C²` at `b`, and `ε > 0`, then the Morse index of
`f_ε (c, v) = f (c, v) + ε ρ(v) h(c)` at `(b, 0)` is the index of `h` at `b` plus the index of `f`
at `(b, 0)`, the index of the normal Hessian. -/
theorem morseIndex_add_mul_mul [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] {b : P}
    {ρ : F → ℝ} (hf : ContDiffAt ℝ 2 f (b, 0)) (hcrit : ∀ᶠ c in 𝓝 b, fderiv ℝ f (c, 0) = 0)
    (hρ1 : ∀ᶠ v in 𝓝 0, ρ v = 1) (hh : ContDiffAt ℝ 2 h b) {ε : ℝ} (hε : 0 < ε) :
    morseIndex (fun y ↦ f y + ε * (ρ y.2 * h y.1)) (b, 0) =
      morseIndex h b + morseIndex f (b, 0) := by
  rw [morseIndex_congr_of_eventuallyEq (add_mul_mul_eventuallyEq hρ1 ε b),
    morseIndex_add_comp_fst (h := ε • h) hf hcrit (hh.const_smul ε)]
  simp only [morseIndex_def, hessianQuadraticForm_smul, QuadraticForm.sigNeg_smul_of_pos _ hε]

/-- **Nondegenerate critical points of a small cutoff perturbation of a Morse–Bott function.** If
`f` is `C²` at `(b, 0)`, every point `(c, 0)` with `c` near `b` is critical, the kernel of the
Hessian at `(b, 0)` consists of base directions, `ρ` is equal to `1` near `0`, `h` is `C²` at
`b`, and `ε ≠ 0`, then `(b, 0)` is a nondegenerate critical point of
`f_ε (c, v) = f (c, v) + ε ρ(v) h(c)` exactly when `b` is a nondegenerate critical point of `h`. -/
theorem isNondegenerateCriticalPoint_add_mul_mul_iff [FiniteDimensional ℝ P]
    [FiniteDimensional ℝ F] {b : P} {ρ : F → ℝ} (hf : ContDiffAt ℝ 2 f (b, 0))
    (hcrit : ∀ᶠ c in 𝓝 b, fderiv ℝ f (c, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (b, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F))
    (hρ1 : ∀ᶠ v in 𝓝 0, ρ v = 1) (hh : ContDiffAt ℝ 2 h b) {ε : ℝ} (hε : ε ≠ 0) :
    IsNondegenerateCriticalPoint (fun y ↦ f y + ε * (ρ y.2 * h y.1)) (b, 0) ↔
      IsNondegenerateCriticalPoint h b := by
  rw [← isNondegenerateCriticalPoint_const_smul_iff hε (f := h),
    ← isNondegenerateCriticalPoint_add_comp_fst_iff (h := ε • h) hf hcrit hker (hh.const_smul ε)]
  exact ⟨fun h' ↦ h'.congr_of_eventuallyEq (add_mul_mul_eventuallyEq hρ1 ε b),
    fun h' ↦ h'.congr_of_eventuallyEq (add_mul_mul_eventuallyEq hρ1 ε b).symm⟩

end TauCeti
