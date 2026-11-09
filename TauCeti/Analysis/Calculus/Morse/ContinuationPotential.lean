/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.IntervalBase
public import TauCeti.Analysis.Calculus.Morse.Prod
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The large-constant product continuation potential

A path `f_t` between two Morse functions `f₀` and `f₁` on `X` is realized as a single function on
the product `X × ℝ`,

`F(x, t) = C h(t) + f_t(x)`, with `h(t) = (t² - 1)² / 4`,

whose critical points and negative gradient trajectories in the slab `X × [0, 1]` define the
continuation map from the Morse complex of `f₀` to that of `f₁`. Here the path is extended
constantly across `t = 0` and `t = 1`, so that `f_t` is independent of `t` near the two ends. The
base factor `C h` is `TauCeti.intervalBasePotential`; this file studies the total function
`TauCeti.continuationPotential C f`, for `f : E × ℝ → ℝ` on a normed space `E`, and the time
component of its trajectories.

**Critical points.** The `t`-derivative of `F` is `-C t (1 - t²) + ∂ₜ f`. Where
`∂ₜ f < C t (1 - t²)` it is negative, so `F` has no critical point in the open slab `0 < t < 1`
once `C` dominates `∂ₜ f` there. Near the two ends `F` is the separated sum of `f₀` (or `f₁`) and
the base potential, whose Hessians in the time direction are `-C` at `0` and `2 C` at `1`. Hence,
for `C > 0`, the critical points of `F` in the slab are the points `(p, 0)` and `(q, 1)` for
critical points `p` of `f₀` and `q` of `f₁`; they are nondegenerate exactly when `p` and `q` are,
and their Morse indices are `ind p + 1` and `ind q`. These are the index shifts of a continuation:
a continuation trajectory runs from `(p, 0)` to `(q, 1)` and preserves the original index.

**The constant.** Suppose `∂ₜ f ≤ M` on the inner slab `δ ≤ t ≤ 1 - δ` and `∂ₜ f ≤ 0` (for
instance `= 0`, in the constant end germs) for the other `t ∈ (0, 1)`. Since `t (1 - t²) ≥ δ²` on
`[δ, 1 - δ]`, this gives `∂ₜ f ≤ K t (1 - t²)` on the whole open slab with `K = max M 0 / δ²`,
and every `C > K` works. On a compact set of `x` a bound `M` exists by continuity.

**The time component.** For every metric of the form `dt² + g_t`, the `t`-component of the negative
gradient of `F` is `-∂ₜ F = C t (1 - t²) - ∂ₜ f`. The results on trajectories therefore concern a
real function `τ` with `τ' = C τ (1 - τ²) - b`, where `b(s)` stands for `∂ₜ f` along the trajectory
and vanishes whenever `τ(s)` lies within `δ` of `0` or of `1`. This formulation applies verbatim to
the time component of a trajectory on `X × ℝ` for a manifold `X`. Near `τ = 0` and `τ = 1` the
equation is then the base equation `τ' = C τ (1 - τ²)`, whose solutions are unique, so:

* a trajectory meeting the level `t = 0` (or `t = 1`) stays in it;
* a trajectory meeting the open slab `0 < t < 1` stays in it, so the slab `X × [0, 1]` and its three
  strata are invariant under the flow, although nothing is asserted outside the slab;
* if moreover `b ≤ K τ (1 - τ²)` with `K < C`, a trajectory in the open slab runs from `t = 0` at
  `-∞` to `t = 1` at `+∞`, because the time coordinate `U(τ) = log τ - (1 / 2) log (1 - τ²)` of the
  base flow (`TauCeti.intervalBaseTimeCoordinate`) increases at rate at least `C - K`.

## Main declarations

* `TauCeti.continuationPotential`: the function `F(x, t) = C h(t) + f(x, t)`.
* `TauCeti.fderiv_continuationPotential_apply_zero_one`: its `t`-derivative.
* `TauCeti.fderiv_continuationPotential_eq_zero_iff_of_mem_Icc`: in the slab, the critical points
  lie at `t = 0` and `t = 1`, over critical points of `f₀` and `f₁`.
* `TauCeti.isNondegenerateCriticalPoint_continuationPotential_zero_iff`,
  `TauCeti.morseIndex_continuationPotential_zero` and their analogues at `1`: nondegeneracy and
  the index shifts `+1` and `0`.
* `TauCeti.exists_forall_le_mul_one_sub_sq` and `IsCompact.exists_forall_le_mul_one_sub_sq`: the
  choice of the constant.
* `TauCeti.eqOn_const_of_hasDerivAt_intervalBase` and
  `TauCeti.mapsTo_Ioo_of_hasDerivAt_intervalBase`: invariance of the levels `t = 0`, `t = 1` and
  of the open slab.
* `TauCeti.tendsto_atTop_of_hasDerivAt_intervalBase` and
  `TauCeti.tendsto_atBot_of_hasDerivAt_intervalBase`: the limits of the time component.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (continuation maps).
-/

public section

open Set Filter Topology

namespace TauCeti

/-! ### The potential and its derivative -/

section Potential

variable {E : Type*} {C : ℝ} {f : E × ℝ → ℝ}

/-- The **continuation potential** `F(x, t) = C h(t) + f(x, t)` on `E × ℝ`, with the double-well
`h(t) = (t² - 1)² / 4` of `TauCeti.intervalBasePotential`. For a path `f_t = f (·, t)` of
functions constant near `t = 0` and `t = 1` and a large constant `C`, it realizes the continuation
from `f₀` to `f₁` as one function on the product. -/
noncomputable def continuationPotential (C : ℝ) (f : E × ℝ → ℝ) (z : E × ℝ) : ℝ :=
  intervalBasePotential C z.2 + f z

theorem continuationPotential_apply (C : ℝ) (f : E × ℝ → ℝ) (z : E × ℝ) :
    continuationPotential C f z = intervalBasePotential C z.2 + f z := (rfl)

theorem continuationPotential_eq_add (C : ℝ) (f : E × ℝ → ℝ) :
    continuationPotential C f = intervalBasePotential C ∘ Prod.snd + f := (rfl)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.ContDiff.continuationPotential {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (continuationPotential C f) :=
  ((contDiff_intervalBasePotential C).comp contDiff_snd).add hf

/-- The derivative of the continuation potential adds the time derivative `C t (t² - 1)` of the
base potential to that of `f`. -/
theorem hasFDerivAt_continuationPotential {z : E × ℝ} {f' : E × ℝ →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' z) :
    HasFDerivAt (continuationPotential C f)
      ((C * z.2 * (z.2 ^ 2 - 1)) • ContinuousLinearMap.snd ℝ E ℝ + f') z :=
  ((hasDerivAt_intervalBasePotential C z.2).comp_hasFDerivAt z (hasFDerivAt_snd)).add hf

theorem fderiv_continuationPotential {z : E × ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (continuationPotential C f) z =
      (C * z.2 * (z.2 ^ 2 - 1)) • ContinuousLinearMap.snd ℝ E ℝ + fderiv ℝ f z :=
  (hasFDerivAt_continuationPotential hf.hasFDerivAt).fderiv

/-- **The time derivative of the continuation potential** is `-C t (1 - t²) + ∂ₜ f`. So the time
component of its negative gradient, for any metric `dt² + g_t`, is `C t (1 - t²) - ∂ₜ f`. -/
theorem fderiv_continuationPotential_apply_zero_one {z : E × ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (continuationPotential C f) z (0, 1) =
      -(C * z.2 * (1 - z.2 ^ 2)) + fderiv ℝ f z (0, 1) := by
  rw [fderiv_continuationPotential hf]
  simp
  ring

/-- Where `∂ₜ f < C t (1 - t²)`, the continuation potential strictly decreases in `t`. -/
theorem fderiv_continuationPotential_apply_zero_one_neg {z : E × ℝ}
    (hf : DifferentiableAt ℝ f z) (h : fderiv ℝ f z (0, 1) < C * z.2 * (1 - z.2 ^ 2)) :
    fderiv ℝ (continuationPotential C f) z (0, 1) < 0 := by
  rw [fderiv_continuationPotential_apply_zero_one hf]
  linarith

/-- The differential of the continuation potential vanishes exactly when the differential of the
slice `f (·, t)` vanishes and `∂ₜ f = C t (1 - t²)`. -/
theorem fderiv_continuationPotential_eq_zero_iff {z : E × ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (continuationPotential C f) z = 0 ↔
      fderiv ℝ (fun x ↦ f (x, z.2)) z.1 = 0 ∧
        fderiv ℝ f z (0, 1) = C * z.2 * (1 - z.2 ^ 2) := by
  have hslice : HasFDerivAt (fun x ↦ f (x, z.2))
      (fderiv ℝ f z ∘L ContinuousLinearMap.inl ℝ E ℝ) z.1 :=
    hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  rw [hslice.fderiv, fderiv_continuationPotential hf]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext v
      simpa using congrArg (fun L : E × ℝ →L[ℝ] ℝ ↦ L (v, 0)) h
    · have := congrArg (fun L : E × ℝ →L[ℝ] ℝ ↦ L (0, 1)) h
      simp at this
      linarith
  · rintro ⟨h₁, h₂⟩
    refine ContinuousLinearMap.ext fun ⟨v, s⟩ ↦ ?_
    have hv : fderiv ℝ f z (v, 0) = 0 := by
      simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h₁
    have hvs : fderiv ℝ f z (v, s) = fderiv ℝ f z (v, 0) + s * fderiv ℝ f z (0, 1) := by
      rw [← smul_eq_mul, ← map_smul, ← map_add]
      simp
    have happly : ((C * z.2 * (z.2 ^ 2 - 1)) • ContinuousLinearMap.snd ℝ E ℝ + fderiv ℝ f z)
        (v, s) = C * z.2 * (z.2 ^ 2 - 1) * s + fderiv ℝ f z (v, s) := by simp
    rw [happly, hvs, hv, h₂, zero_apply]
    ring

/-- **The critical points of the continuation potential in the slab** `0 ≤ t ≤ 1` lie over
critical points of `f₀` at `t = 0` and of `f₁` at `t = 1`, provided `∂ₜ f < C t (1 - t²)` in the
open slab and `∂ₜ f = 0` at its two ends. -/
theorem fderiv_continuationPotential_eq_zero_iff_of_mem_Icc {z : E × ℝ}
    (hf : DifferentiableAt ℝ f z) (hz : z.2 ∈ Icc 0 1)
    (hlt : z.2 ∈ Ioo 0 1 → fderiv ℝ f z (0, 1) < C * z.2 * (1 - z.2 ^ 2))
    (hend : z.2 ∉ Ioo 0 1 → fderiv ℝ f z (0, 1) = 0) :
    fderiv ℝ (continuationPotential C f) z = 0 ↔
      (z.2 = 0 ∨ z.2 = 1) ∧ fderiv ℝ (fun x ↦ f (x, z.2)) z.1 = 0 := by
  rw [fderiv_continuationPotential_eq_zero_iff hf]
  by_cases ht : z.2 ∈ Ioo 0 1
  · have h := hlt ht
    have h0 : z.2 ≠ 0 := ht.1.ne'
    have h1 : z.2 ≠ 1 := ht.2.ne
    simp only [h0, h1, or_self, false_and, iff_false, not_and]
    exact fun _ ↦ h.ne
  · have h0 : z.2 = 0 ∨ z.2 = 1 := by
      rcases hz with ⟨h₀, h₁⟩
      rcases h₀.lt_or_eq with h₀ | h₀
      · rcases h₁.lt_or_eq with h₁ | h₁
        · exact absurd ⟨h₀, h₁⟩ ht
        · exact Or.inr h₁
      · exact Or.inl h₀.symm
    have hzero : C * z.2 * (1 - z.2 ^ 2) = 0 := by
      rcases h0 with h0 | h0 <;> simp [h0]
    simp [h0, hend ht, hzero]

/-! ### Critical points at the two ends -/

omit [NormedSpace ℝ E] in
/-- Where `f` is independent of `t` near `(p, t₀)`, the continuation potential is there the
separated sum of the slice `f (·, t₀)` and the base potential. -/
theorem continuationPotential_eventuallyEq {p : E} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀)) :
    continuationPotential C f =ᶠ[𝓝 (p, t₀)]
      (fun x ↦ f (x, t₀)) ∘ Prod.fst + intervalBasePotential C ∘ Prod.snd := by
  filter_upwards [hf] with z hz
  simp only [continuationPotential_apply, Pi.add_apply, Function.comp_apply, hz]
  ring

/-- Where `f` is independent of `t` near `(p, t₀)`, the point `(p, t₀)` is a nondegenerate
critical point of the continuation potential exactly when `p` is one of the slice `f (·, t₀)` and
`t₀` is one of the base potential. -/
theorem isNondegenerateCriticalPoint_continuationPotential_iff {p : E} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀)) :
    IsNondegenerateCriticalPoint (continuationPotential C f) (p, t₀) ↔
      IsNondegenerateCriticalPoint (fun x ↦ f (x, t₀)) p ∧
        IsNondegenerateCriticalPoint (intervalBasePotential C) t₀ := by
  have hE := continuationPotential_eventuallyEq (C := C) hf
  have hh : ContDiffAt ℝ 2 (intervalBasePotential C) t₀ :=
    (contDiff_intervalBasePotential C).contDiffAt
  constructor
  · intro h
    have h' := h.congr_of_eventuallyEq hE
    -- The slice is the restriction of the separated sum to `t = t₀`, up to a constant.
    have hslice : ContDiffAt ℝ 2 (fun x ↦ f (x, t₀) + intervalBasePotential C t₀) p :=
      h'.contDiffAt.comp (f := fun x : E ↦ (x, t₀)) p (by fun_prop)
    have hp : ContDiffAt ℝ 2 (fun x ↦ f (x, t₀)) p := by
      simpa using hslice.sub (contDiffAt_const (c := intervalBasePotential C t₀))
    exact (isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff hp hh).1 h'
  · rintro ⟨h₁, h₂⟩
    exact (h₁.comp_fst_add_comp_snd h₂).congr_of_eventuallyEq hE.symm

/-- **The source end.** For `C ≠ 0`, if `f` is independent of `t` near `(p, 0)`, then `(p, 0)` is a
nondegenerate critical point of the continuation potential exactly when `p` is one of `f₀`. -/
theorem isNondegenerateCriticalPoint_continuationPotential_zero_iff {p : E} (hC : C ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (p, 0), f z = f (z.1, 0)) :
    IsNondegenerateCriticalPoint (continuationPotential C f) (p, 0) ↔
      IsNondegenerateCriticalPoint (fun x ↦ f (x, 0)) p := by
  simp [isNondegenerateCriticalPoint_continuationPotential_iff hf,
    isNondegenerateCriticalPoint_intervalBasePotential_zero hC]

/-- **The target end.** For `C ≠ 0`, if `f` is independent of `t` near `(q, 1)`, then `(q, 1)` is a
nondegenerate critical point of the continuation potential exactly when `q` is one of `f₁`. -/
theorem isNondegenerateCriticalPoint_continuationPotential_one_iff {q : E} (hC : C ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (q, 1), f z = f (z.1, 1)) :
    IsNondegenerateCriticalPoint (continuationPotential C f) (q, 1) ↔
      IsNondegenerateCriticalPoint (fun x ↦ f (x, 1)) q := by
  simp [isNondegenerateCriticalPoint_continuationPotential_iff hf,
    isNondegenerateCriticalPoint_intervalBasePotential_one hC]

variable [FiniteDimensional ℝ E]

/-- Where `f` is independent of `t` near `(p, t₀)`, the Morse index of the continuation potential
at `(p, t₀)` is the sum of the indices of the slice `f (·, t₀)` at `p` and of the base potential
at `t₀`. -/
theorem morseIndex_continuationPotential {p : E} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀))
    (hp : ContDiffAt ℝ 2 (fun x ↦ f (x, t₀)) p) :
    morseIndex (continuationPotential C f) (p, t₀) =
      morseIndex (fun x ↦ f (x, t₀)) p + morseIndex (intervalBasePotential C) t₀ := by
  rw [morseIndex_congr_of_eventuallyEq (continuationPotential_eventuallyEq hf),
    morseIndex_comp_fst_add_comp_snd hp (contDiff_intervalBasePotential C).contDiffAt]

/-- **The index shift at the source end is `1`.** -/
theorem morseIndex_continuationPotential_zero {p : E} (hC : 0 < C)
    (hf : ∀ᶠ z in 𝓝 (p, 0), f z = f (z.1, 0)) (hp : ContDiffAt ℝ 2 (fun x ↦ f (x, 0)) p) :
    morseIndex (continuationPotential C f) (p, 0) = morseIndex (fun x ↦ f (x, 0)) p + 1 := by
  rw [morseIndex_continuationPotential hf hp, morseIndex_intervalBasePotential_zero hC]

/-- **The index shift at the target end is `0`.** -/
theorem morseIndex_continuationPotential_one {q : E} (hC : 0 < C)
    (hf : ∀ᶠ z in 𝓝 (q, 1), f z = f (z.1, 1)) (hq : ContDiffAt ℝ 2 (fun x ↦ f (x, 1)) q) :
    morseIndex (continuationPotential C f) (q, 1) = morseIndex (fun x ↦ f (x, 1)) q := by
  rw [morseIndex_continuationPotential hf hq, morseIndex_intervalBasePotential_one hC, add_zero]

end Potential

/-! ### The choice of the constant -/

section Constant

/-- On the inner interval `[δ, 1 - δ]` the base field `t (1 - t²)` is at least `δ²`. -/
private theorem sq_le_mul_one_sub_sq {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc δ (1 - δ)) :
    δ ^ 2 ≤ t * (1 - t ^ 2) := by
  obtain ⟨h₁, h₂⟩ := ht
  have h₃ : δ * δ ≤ t * (1 - t) := mul_le_mul h₁ (by linarith) hδ.le (by linarith)
  have h₄ : 0 ≤ t * (1 - t) := by nlinarith
  nlinarith

variable {X : Type*} {g : X → ℝ → ℝ} {s : Set X} {δ : ℝ}

/-- **Choice of the constant.** If `g ≤ M` on the inner slab `δ ≤ t ≤ 1 - δ` and `g ≤ 0` on the
rest of the open slab `0 < t < 1`, then `g ≤ K t (1 - t²)` on the whole open slab for some
`K ≥ 0`. Applied to `g x t = ∂ₜ f (x, t)`, every `C > K` makes the time derivative
`-C t (1 - t²) + ∂ₜ f` of the continuation potential negative for `0 < t < 1`. -/
theorem exists_forall_le_mul_one_sub_sq {M : ℝ} (hδ : 0 < δ)
    (hM : ∀ x ∈ s, ∀ t ∈ Icc δ (1 - δ), g x t ≤ M)
    (h₀ : ∀ x ∈ s, ∀ t ∈ Ioo 0 1, t ∉ Icc δ (1 - δ) → g x t ≤ 0) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ s, ∀ t ∈ Ioo 0 1, g x t ≤ K * t * (1 - t ^ 2) := by
  refine ⟨max M 0 / δ ^ 2, by positivity, fun x hx t ht ↦ ?_⟩
  have hpos : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
  rw [mul_assoc]
  by_cases hti : t ∈ Icc δ (1 - δ)
  · calc g x t ≤ max M 0 := (hM x hx t hti).trans (le_max_left _ _)
      _ = max M 0 / δ ^ 2 * δ ^ 2 := by field_simp
      _ ≤ max M 0 / δ ^ 2 * (t * (1 - t ^ 2)) :=
        mul_le_mul_of_nonneg_left (sq_le_mul_one_sub_sq hδ hti) (by positivity)
  · exact (h₀ x hx t ht hti).trans (by positivity)

/-- **Choice of the constant on a compact set.** If `g` is continuous on `K × [δ, 1 - δ]` for a
compact set `K` and `g ≤ 0` on the rest of the open slab, then `g ≤ K' t (1 - t²)` on `K × (0, 1)`
for some `K' ≥ 0`. -/
theorem _root_.IsCompact.exists_forall_le_mul_one_sub_sq [TopologicalSpace X] (hs : IsCompact s)
    (hδ : 0 < δ) (hg : ContinuousOn (Function.uncurry g) (s ×ˢ Icc δ (1 - δ)))
    (h₀ : ∀ x ∈ s, ∀ t ∈ Ioo 0 1, t ∉ Icc δ (1 - δ) → g x t ≤ 0) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ s, ∀ t ∈ Ioo 0 1, g x t ≤ K * t * (1 - t ^ 2) := by
  obtain ⟨M, hM⟩ := (hs.prod isCompact_Icc).bddAbove_image hg
  exact TauCeti.exists_forall_le_mul_one_sub_sq hδ
    (fun x hx t ht ↦ hM (mem_image_of_mem _ (mk_mem_prod hx ht))) h₀

end Constant

/-! ### The time component of a trajectory -/

section Trajectory

variable {C δ c : ℝ} {τ b : ℝ → ℝ} {I : Set ℝ}

/-- Near a point where `τ` takes a zero `c` of the base field, with `b` vanishing while `τ` is
within `δ` of `c`, the equation `τ' = C τ (1 - τ²) - b` is the base equation, whose solutions are
unique; so `τ` is locally constant there. -/
private theorem eventuallyEq_const_of_hasDerivAt (hc : c * (1 - c ^ 2) = 0) (hδ : 0 < δ)
    (hIo : IsOpen I) (hτ : ∀ s ∈ I, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s)
    (hb : ∀ s ∈ I, |τ s - c| < δ → b s = 0) {s₀ : ℝ} (hs₀ : s₀ ∈ I) (hτs₀ : τ s₀ = c) :
    τ =ᶠ[𝓝 s₀] fun _ ↦ c := by
  have hv : ContDiff ℝ 1 fun x : ℝ ↦ C * x * (1 - x ^ 2) := by fun_prop
  obtain ⟨K, U, hU, hK⟩ := hv.locallyLipschitz c
  have hcont : ContinuousAt τ s₀ := (hτ s₀ hs₀).continuousAt
  have hnear : ∀ᶠ s in 𝓝 s₀, τ s ∈ U ∩ Metric.ball c δ :=
    hcont.preimage_mem_nhds (by rw [hτs₀]; exact inter_mem hU (Metric.ball_mem_nhds c hδ))
  refine ODE_solution_unique_of_eventually (v := fun _ x ↦ C * x * (1 - x ^ 2)) (s := fun _ ↦ U)
    (Eventually.of_forall fun _ ↦ hK) ?_ (Eventually.of_forall fun _ ↦ ?_) hτs₀
  · filter_upwards [hnear, hIo.mem_nhds hs₀] with s hs hsI
    refine ⟨?_, hs.1⟩
    have hbs : b s = 0 := hb s hsI (by simpa [Real.dist_eq] using hs.2)
    simpa [hbs] using hτ s hsI
  · refine ⟨?_, mem_of_mem_nhds hU⟩
    have : C * c * (1 - c ^ 2) = 0 := by rw [mul_assoc, hc, mul_zero]
    rw [this]
    exact hasDerivAt_const _ _

/-- **Invariance of the levels `t = 0` and `t = 1`.** Let `τ' = C τ (1 - τ²) - b` on an open
preconnected set `I`, where `b` vanishes whenever `τ` lies within `δ` of a zero `c` of the base
field `t (1 - t²)`, for instance `c = 0` or `c = 1`. If `τ` takes the value `c` somewhere on `I`,
then it is constantly `c` on `I`. -/
theorem eqOn_const_of_hasDerivAt_intervalBase (hc : c * (1 - c ^ 2) = 0) (hδ : 0 < δ)
    (hIo : IsOpen I) (hI : IsPreconnected I)
    (hτ : ∀ s ∈ I, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s)
    (hb : ∀ s ∈ I, |τ s - c| < δ → b s = 0) {s₀ : ℝ} (hs₀ : s₀ ∈ I) (hτs₀ : τ s₀ = c) :
    EqOn τ (fun _ ↦ c) I := by
  classical
  -- Whether `τ = c` is locally constant along `I`, hence constant on the preconnected set `I`.
  have hloc : ∀ s ∈ I, ∀ᶠ r in 𝓝 s, (τ r = c ↔ τ s = c) := fun s hs ↦ by
    by_cases h : τ s = c
    · exact (eventuallyEq_const_of_hasDerivAt hc hδ hIo hτ hb hs h).mono fun r hr ↦ by simp [hr, h]
    · exact ((hτ s hs).continuousAt.eventually_ne h).mono fun r hr ↦ by simp [hr, h]
  have hcont : ContinuousOn (fun s ↦ decide (τ s = c)) I := fun s hs ↦
    ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ decide (τ s = c)) s).congr
      ((hloc s hs).mono fun r hr ↦ decide_eq_decide.2 hr.symm)).continuousWithinAt
  intro s hs
  simpa [hτs₀] using (hI.constant hcont hs₀ hs).symm

/-- **Invariance of the open slab.** Let `τ' = C τ (1 - τ²) - b` on an open preconnected set `I`,
where `b` vanishes whenever `τ` lies within `δ` of `0` or of `1`. If `τ` takes a value in `(0, 1)`
somewhere on `I`, then it takes values in `(0, 1)` everywhere on `I`. -/
theorem mapsTo_Ioo_of_hasDerivAt_intervalBase (hδ : 0 < δ) (hIo : IsOpen I) (hI : IsPreconnected I)
    (hτ : ∀ s ∈ I, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s)
    (hb₀ : ∀ s ∈ I, |τ s| < δ → b s = 0) (hb₁ : ∀ s ∈ I, |τ s - 1| < δ → b s = 0) {s₀ : ℝ}
    (hs₀ : s₀ ∈ I) (hτs₀ : τ s₀ ∈ Ioo 0 1) :
    MapsTo τ I (Ioo 0 1) := by
  classical
  -- Whether `τ ∈ (0, 1)` is locally constant along `I`, hence constant on the preconnected set `I`.
  suffices hloc : ∀ s ∈ I, ∀ᶠ r in 𝓝 s, (τ r ∈ Ioo 0 1 ↔ τ s ∈ Ioo 0 1) by
    have hcont : ContinuousOn (fun s ↦ decide (τ s ∈ Ioo 0 1)) I := fun s hs ↦
      ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ decide (τ s ∈ Ioo 0 1)) s).congr
        ((hloc s hs).mono fun r hr ↦ decide_eq_decide.2 hr.symm)).continuousWithinAt
    intro s hs
    simpa [hτs₀] using (hI.constant hcont hs₀ hs).symm
  intro s hs
  have hcont := (hτ s hs).continuousAt
  by_cases h : τ s ∈ Ioo 0 1
  · exact (hcont.eventually_mem (isOpen_Ioo.mem_nhds h)).mono fun r hr ↦ by simp [hr, h]
  -- Outside the open slab `τ` stays outside near `s`: by continuity where `τ s < 0` or `τ s > 1`,
  -- and by uniqueness for the base equation where `τ s = 0` or `τ s = 1`.
  suffices hout : ∀ᶠ r in 𝓝 s, τ r ∉ Ioo 0 1 by
    exact hout.mono fun r hr ↦ by simp [hr, h]
  rcases not_and_or.1 h with h₀ | h₁
  · rcases (not_lt.1 h₀).lt_or_eq with h₀ | h₀
    · exact (hcont.eventually_lt continuousAt_const h₀).mono fun r hr hr' ↦ hr'.1.not_gt hr
    · exact (eventuallyEq_const_of_hasDerivAt (c := 0) (by simp) hδ hIo hτ (by simpa using hb₀)
        hs h₀).mono fun r hr hr' ↦ hr'.1.ne' hr
  · rcases (not_lt.1 h₁).lt_or_eq with h₁ | h₁
    · exact (continuousAt_const.eventually_lt hcont h₁).mono fun r hr hr' ↦ hr'.2.not_gt hr
    · exact (eventuallyEq_const_of_hasDerivAt (c := 1) (by simp) hδ hIo hτ hb₁ hs
        h₁.symm).mono fun r hr hr' ↦ hr'.2.ne hr

/-- Along a solution of `τ' = C τ (1 - τ²) - b` in the open slab with `b ≤ K τ (1 - τ²)`, the time
coordinate `U(τ) = log τ - (1 / 2) log (1 - τ²)` advances at rate at least `C - K`. -/
private theorem le_intervalBaseTimeCoordinate_sub {K : ℝ}
    (hτ : ∀ s, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s) (hτI : ∀ s, τ s ∈ Ioo 0 1)
    (hb : ∀ s, b s ≤ K * τ s * (1 - τ s ^ 2)) {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) :
    (C - K) * (s₂ - s₁) ≤
      intervalBaseTimeCoordinate (τ s₂) - intervalBaseTimeCoordinate (τ s₁) := by
  set w : ℝ → ℝ := fun s ↦ intervalBaseTimeCoordinate (τ s) - (C - K) * s
  have hw : ∀ s, HasDerivAt w ((C * τ s * (1 - τ s ^ 2) - b s) * (τ s * (1 - τ s ^ 2))⁻¹ -
      (C - K)) s := fun s ↦
    (((hasDerivAt_intervalBaseTimeCoordinate (hτI s)).comp s (hτ s)).congr_deriv
      (mul_comm _ _)).sub (((hasDerivAt_id s).const_mul (C - K)).congr_deriv (mul_one _))
  have hmono : Monotone w := by
    refine monotone_of_deriv_nonneg (fun s ↦ (hw s).differentiableAt) fun s ↦ ?_
    rw [(hw s).deriv]
    have hpos : 0 < τ s * (1 - τ s ^ 2) := mul_pos (hτI s).1 (by nlinarith [(hτI s).1, (hτI s).2])
    rw [sub_nonneg, le_mul_inv_iff₀ hpos]
    nlinarith [hb s]
  have := hmono hs
  simp only [w] at this
  linarith

/-- **The time component tends to `1` at `+∞`.** Let `τ' = C τ (1 - τ²) - b` on the whole line,
with values in `(0, 1)`. If `b ≤ K τ (1 - τ²)` for some `K < C`, then `τ → 1` at `+∞`: a
trajectory in the open slab ends at the target level `t = 1`. -/
theorem tendsto_atTop_of_hasDerivAt_intervalBase {K : ℝ}
    (hτ : ∀ s, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s) (hτI : ∀ s, τ s ∈ Ioo 0 1)
    (hb : ∀ s, b s ≤ K * τ s * (1 - τ s ^ 2)) (hKC : K < C) :
    Tendsto τ atTop (𝓝 1) := by
  -- `1 - τ² ≤ exp (-2 U(τ))`, and `U(τ s) ≥ U(τ 0) + (C - K) s`.
  have hbound : ∀ s, 0 ≤ s → 1 - τ s ≤
      Real.exp (-(2 * (intervalBaseTimeCoordinate (τ 0) + (C - K) * s))) := by
    intro s hs
    have hU := le_intervalBaseTimeCoordinate_sub hτ hτI hb hs
    obtain ⟨h₀, h₁⟩ := hτI s
    have h1 : 0 < 1 - τ s ^ 2 := by nlinarith
    have hlog : Real.log (1 - τ s ^ 2) ≤ -(2 * intervalBaseTimeCoordinate (τ s)) := by
      have := Real.log_nonpos h₀.le h₁.le
      rw [intervalBaseTimeCoordinate_apply]
      linarith
    calc 1 - τ s ≤ 1 - τ s ^ 2 := by nlinarith
      _ = Real.exp (Real.log (1 - τ s ^ 2)) := (Real.exp_log h1).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have hlim : Tendsto (fun s ↦
      Real.exp (-(2 * (intervalBaseTimeCoordinate (τ 0) + (C - K) * s)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((tendsto_atTop_add_const_left _ _
      (tendsto_id.const_mul_atTop (sub_pos.2 hKC))).const_mul_atTop two_pos))
  have h1 : Tendsto (fun s ↦ 1 - τ s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun s ↦ sub_nonneg.2 (hτI s).2.le)
      (eventually_ge_atTop 0 |>.mono hbound)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-- **The time component tends to `0` at `-∞`.** Let `τ' = C τ (1 - τ²) - b` on the whole line,
with values in `(0, 1)`. If `b ≤ K τ (1 - τ²)` for some `K < C`, then `τ → 0` at `-∞`: a
trajectory in the open slab starts at the source level `t = 0`. -/
theorem tendsto_atBot_of_hasDerivAt_intervalBase {K : ℝ}
    (hτ : ∀ s, HasDerivAt τ (C * τ s * (1 - τ s ^ 2) - b s) s) (hτI : ∀ s, τ s ∈ Ioo 0 1)
    (hb : ∀ s, b s ≤ K * τ s * (1 - τ s ^ 2)) (hKC : K < C) :
    Tendsto τ atBot (𝓝 0) := by
  -- `τ ≤ exp U(τ)`, and `U(τ s) ≤ U(τ 0) + (C - K) s` for `s ≤ 0`.
  have hbound : ∀ s, s ≤ 0 → τ s ≤
      Real.exp (intervalBaseTimeCoordinate (τ 0) + (C - K) * s) := by
    intro s hs
    have hU := le_intervalBaseTimeCoordinate_sub hτ hτI hb hs
    obtain ⟨h₀, h₁⟩ := hτI s
    have h1 : 0 < 1 - τ s ^ 2 := by nlinarith
    have hlog : Real.log (τ s) ≤ intervalBaseTimeCoordinate (τ s) := by
      have := Real.log_nonpos h1.le (by nlinarith)
      rw [intervalBaseTimeCoordinate_apply]
      linarith
    calc τ s = Real.exp (Real.log (τ s)) := (Real.exp_log h₀).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have hlim : Tendsto (fun s ↦
      Real.exp (intervalBaseTimeCoordinate (τ 0) + (C - K) * s)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atBot (sub_pos.2 hKC)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun s ↦ (hτI s).1.le) (eventually_le_atBot 0 |>.mono hbound)

end Trajectory

end TauCeti
