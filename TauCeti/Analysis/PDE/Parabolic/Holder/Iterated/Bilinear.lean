/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.LeibnizJet
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation
import TauCeti.Topology.MetricSpace.Holder

/-!
# Products in the parabolic Hölder spaces of every order

Let `B : F →L[ℝ] G →L[ℝ] H` be a continuous bilinear map and `α ≤ 1`. This file proves that `B`
acts pointwise on the bounded parabolic Hölder spaces `C_{par,b}^{k+α}` of every order `k` on a
slab `E × [a, b]`: for `u ∈ C_{par,b}^{k+α}(F)` and `v ∈ C_{par,b}^{k+α}(G)` the map
`(x, t) ↦ B (u (x, t)) (v (x, t))` lies in `C_{par,b}^{k+α}(H)`, and

`‖B u v‖ ≤ 21 (k + 1)² 2ᵏ ‖B‖ ‖u‖ ‖v‖`

(`ContinuousLinearMap.norm_compParabolicCkHolder₂_le`). With `B` the multiplication of `ℝ`, the
scalar multiplication `ℝ × F → F` or the application of operator-valued coefficients, this is the
product and bounded multiplication estimate of these spaces: it bounds the terms `aⁱʲ ∂ᵢ∂ⱼu`,
`bⁱ ∂ᵢu` and `c u` of a parabolic operator with coefficients in `C_{par,b}^{k+α}` acting on
`C_{par,b}^{k+2+α}`, and the localization of a solution by a smooth space-time cutoff.

The fields of `B u v` are given by the Leibniz rule in time and in space,

`D_t^r D_x^m (B u v) = ∑_{r₁ + r₂ = r} (r choose r₁) Λₘ (J^{r₁} u, J^{r₂} v)`, where
`J^{r'} u = (D_t^{r'} D_x^i u)_{i ≤ m}`

(`ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`), where
`Λₘ = ContinuousLinearMap.leibnizJet B E m` is the continuous bilinear map computing the `m`-th
spatial derivative of a product from the jets of its factors. Because `Λₘ` is bilinear and
continuous, the time derivatives of the jets pass through it by the product rule, and the binomial
recursion of `Finset.sum_antidiagonal_choose_succ_nsmul` reassembles them.

The Hölder conditions of `B u v` come from those of the fields of `u` and `v` of every order, not
only the top one. For `α ≤ 1`, every field `D_t^r D_x^m u` of order `2 r + m ≤ k` is parabolically
`α`-Hölder with constant `6 ‖u‖` (`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL`): at the
top order by definition, and below it because the field is Lipschitz in space, with the next
spatial field as derivative, and Lipschitz or `(1 + α) / 2`-Hölder in time. Likewise every field of
order `2 r + m ≤ k - 1` has `(1 + α) / 2`-Hölder time slices with constant `3 ‖u‖`
(`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk`). Products of bounded Hölder maps
through a bilinear map are Hölder, which gives the Hölder field and the Hölder time slices of
`B u v` at the top two orders.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL`: every field of order at most `k` is
  parabolically `α`-Hölder with constant `6 ‖u‖`.
* `TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk`: every field of order at most
  `k - 1` has `(1 + α) / 2`-Hölder time slices with constant `3 ‖u‖`.
* `ContinuousLinearMap.compParabolicCkHolder₂`: pointwise application of `B` as a continuous
  bilinear map of the parabolic Hölder spaces of order `k`.
* `ContinuousLinearMap.compParabolicCkHolder₂_apply` and
  `ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`: its values and its fields.
* `ContinuousLinearMap.norm_compParabolicCkHolder₂_le`: the operator-norm bound
  `21 (k + 1)² 2ᵏ ‖B‖`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}

variable (E) in
/-- Shortcut instance for jets of multilinear maps, keeping instance search on the spaces of
continuous linear maps between them shallow. -/
local instance instNormedAddCommGroupJet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ) : NormedAddCommGroup ((i : Fin m) → E [×i]→L[ℝ] X) :=
  inferInstance

variable (E) in
/-- Shortcut instance for scalar operations on jets of multilinear maps. -/
local instance instNormedSpaceJet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ) : NormedSpace ℝ ((i : Fin m) → E [×i]→L[ℝ] X) :=
  inferInstance

variable (E) in
/-- Shortcut instance for continuous linear maps from jets to multilinear maps. -/
local instance instNormedAddCommGroupJetCLM (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (m n : ℕ) :
    NormedAddCommGroup (((i : Fin m) → E [×i]→L[ℝ] X) →L[ℝ] E [×n]→L[ℝ] Y) :=
  inferInstance

variable (E) in
/-- Shortcut instance for scalar operations on continuous linear maps from jets to multilinear
maps. -/
local instance instNormedSpaceJetCLM (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (m n : ℕ) :
    NormedSpace ℝ (((i : Fin m) → E [×i]→L[ℝ] X) →L[ℝ] E [×n]→L[ℝ] Y) :=
  inferInstance

namespace ParabolicCkHolderSpace

/-! ### Hölder bounds for the fields of every order -/

/-- A field of order at most `k - 2` is Lipschitz in time, with constant `‖u‖`. -/
private theorem timeEHolderNorm_one_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) :
    timeEHolderNorm 1 (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖u‖₊ := by
  have key := timeEHolderNorm_one_le_of_hasDerivWithinAt (a := a) (b := b)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m u))
    (wₜ := fun y t ↦ mixedDerivL (r + 1) m u (slabMk y (projIcc a b hab.le t))) (C := ‖u‖₊)
    (fun y t ht ↦ by
      simpa only [projIcc_of_mem hab.le ht] using hasDerivWithinAt_mixedDerivL u h y ⟨t, ht⟩)
    (fun y t _ ↦ by
      rw [coe_nnNorm]
      exact ((mixedDerivL (r + 1) m u).norm_coe_le_norm _).trans (norm_mixedDerivL_le u _ _))
  rwa [ParabolicC2HolderSpace.timeExtension_space_slabTime] at key

/-- A field of order at most `k - 1` is Lipschitz in space, with constant `‖u‖`. -/
private theorem spaceEHolderNorm_one_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) :
    spaceEHolderNorm 1 (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖u‖₊ := by
  have key := spaceEHolderNorm_one_le_of_hasFDerivAt (a := a) (b := b)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m u))
    (w' := fun y t ↦ (mixedDerivL r (m + 1) u (slabMk y (projIcc a b hab.le t))).curryLeft)
    (C := ‖u‖₊)
    (fun t ht y ↦ by
      simpa only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le ht] using
        hasFDerivAt_mixedDerivL u h ⟨t, ht⟩ y)
    (fun y t _ ↦ by
      rw [coe_nnNorm, ContinuousMultilinearMap.curryLeft_norm]
      exact ((mixedDerivL r (m + 1) u).norm_coe_le_norm _).trans (norm_mixedDerivL_le u _ _))
  rwa [ParabolicC2HolderSpace.timeExtension_space_slabTime] at key

/-- The time slices of a field of order exactly `k - 1` are `(1 + α) / 2`-Hölder with constant
`‖u‖`. -/
private theorem timeEHolderNorm_mixedDerivL_le_of_add_one_eq
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m + 1 = k) :
    timeEHolderNorm ((1 + α) / 2) (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤
      ‖u‖₊ := by
  refine timeEHolderNorm_le_iff.2 fun x t s ↦ ?_
  have hx := (timeSliceL r m u x).holderWith_nnnorm t s
  rw [coe_timeSliceL u h x] at hx
  refine hx.trans ?_
  gcongr
  rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x).trans (norm_timeSliceL_le u r m)

/-- Values of a field lie within distance `2 ‖u‖` of each other. -/
private theorem dist_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p q : slab (E := E) a b) :
    dist (mixedDerivL r m u p) (mixedDerivL r m u q) ≤ ((2 * ‖u‖₊ : ℝ≥0) : ℝ) := by
  push_cast
  rw [two_mul]
  exact (dist_le_norm_add_norm _ _).trans (add_le_add
    (((mixedDerivL r m u).norm_coe_le_norm p).trans (norm_mixedDerivL_le u r m))
    (((mixedDerivL r m u).norm_coe_le_norm q).trans (norm_mixedDerivL_le u r m)))

/-- **Every field is parabolically Hölder.** For `α ≤ 1`, each field `D_t^r D_x^m u` of order
`2 r + m ≤ k` is parabolically `α`-Hölder with constant `6 ‖u‖`. -/
theorem holderWith_mixedDerivL (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) :
    HolderWith (6 * ‖u‖₊) α (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  rcases h.eq_or_lt with h | h
  · intro p q
    have hp := (mixedDerivHolderL r m u).holderWith_nnnorm p q
    rw [mixedDerivHolderL_apply u h, mixedDerivHolderL_apply u h] at hp
    refine hp.trans ?_
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, coe_nnNorm]
    have := norm_mixedDerivHolderL_le u r m
    push_cast
    linarith [norm_nonneg u]
  · have hspace := spaceEHolderNorm_one_mixedDerivL_le u (r := r) (m := m) (by omega)
    have hD := dist_mixedDerivL_le u r m
    have hbound : eHolderNorm α (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤
        ↑(6 * ‖u‖₊) := by
      by_cases h2 : 2 * r + m + 2 ≤ k
      · refine (eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le hspace
          (timeEHolderNorm_one_mixedDerivL_le u h2) hD hα (by
            rw [← NNReal.coe_le_coe]
            push_cast
            have : (α : ℝ) ≤ 1 := by exact_mod_cast hα
            linarith) one_pos one_pos).trans (le_of_eq ?_)
        simp only [NNReal.one_rpow, mul_one]
        congr 1
        ring
      · refine (eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le hspace
          (timeEHolderNorm_mixedDerivL_le_of_add_one_eq u (by omega)) hD hα (by
            rw [← NNReal.coe_le_coe]
            push_cast
            linarith) one_pos one_pos).trans (le_of_eq ?_)
        simp only [NNReal.one_rpow, mul_one]
        congr 1
        ring
    exact eHolderNorm_le_iff.1 hbound

/-- **Every field below the top order has Hölder time slices.** For `α ≤ 1`, each field
`D_t^r D_x^m u` of order `2 r + m ≤ k - 1` has `(1 + α) / 2`-Hölder time slices with constant
`3 ‖u‖`. -/
theorem holderWith_mixedDerivL_slabMk (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (3 * ‖u‖₊) ((1 + α) / 2) fun t : Icc a b ↦ mixedDerivL r m u (slabMk x t) := by
  have hbound : timeEHolderNorm ((1 + α) / 2)
      (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ↑(3 * ‖u‖₊) := by
    rcases h.eq_or_lt with h | h
    · refine (timeEHolderNorm_mixedDerivL_le_of_add_one_eq u h).trans (ENNReal.coe_le_coe.2 ?_)
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith [norm_nonneg u]
    · refine (timeEHolderNorm_le_of_timeEHolderNorm_le
        (timeEHolderNorm_one_mixedDerivL_le u (r := r) (m := m) (by omega))
        (dist_mixedDerivL_le u r m) (by
          rw [← NNReal.coe_le_coe]
          push_cast
          have : (α : ℝ) ≤ 1 := by exact_mod_cast hα
          linarith) one_pos).trans (le_of_eq ?_)
      simp only [NNReal.one_rpow, mul_one]
      congr 1
      ring
  exact fun t s ↦ timeEHolderNorm_le_iff.1 hbound x t s

/-! ### Jets of the fields -/

/-- The spatial jet `(D_t^r D_x^i u (p))_{i ≤ m}` of the `r`-th time derivative at `p`. -/
private def jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (p : slab (E := E) a b) :
    (i : Fin (m + 1)) → E [×i]→L[ℝ] F :=
  fun i ↦ mixedDerivL r i u p

private theorem jetInit_jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) : jetInit ℝ E F m (jet u r (m + 1) p) = jet u r m p :=
  funext fun i ↦ by
    rw [jetInit_apply]
    rfl

private theorem norm_jet_le (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) : ‖jet u r m p‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i ↦
    ((mixedDerivL r i u).norm_coe_le_norm p).trans (norm_mixedDerivL_le u r i)

private theorem continuous_jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    Continuous (jet u r m) :=
  continuous_pi fun i ↦ (mixedDerivL r i u).continuous

private theorem holderWith_jet (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) : HolderWith (6 * ‖u‖₊) α (jet u r m) := fun p q ↦
  edist_pi_le_iff.2 fun i ↦ holderWith_mixedDerivL hα u (by omega) p q

private theorem holderWith_jet_slabMk (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (3 * ‖u‖₊) ((1 + α) / 2) fun t : Icc a b ↦ jet u r m (slabMk x t) := fun t s ↦
  edist_pi_le_iff.2 fun i ↦ holderWith_mixedDerivL_slabMk hα u (by omega) x t s

/-- The jet of the `r`-th time derivative is differentiable in time within `[a, b]`, with the jet
of the `(r + 1)`-th time derivative as derivative. -/
private theorem hasDerivWithinAt_jet (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (fun s ↦ jet u r m (slabMk x (projIcc a b hab.le s)))
      (jet u (r + 1) m (slabMk x t)) (Icc a b) t :=
  hasDerivWithinAt_pi.2 fun i ↦ by
    have hi := hasDerivWithinAt_mixedDerivL u (r := r) (m := i) (by omega) x t
    rwa [ParabolicC2HolderSpace.timeExtension_def] at hi

/-! ### Finite sums of Hölder maps -/

/-- A sum of `cᵢ` copies of maps `fᵢ` which are `r`-Hölder with a common constant `K` is
`r`-Hölder with constant `(∑ cᵢ) K`. -/
private theorem holderWith_sum_nsmul {X Y ι : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] {r K : ℝ≥0} (s : Finset ι) (c : ι → ℕ)
    {f : ι → X → Y} (hf : ∀ i ∈ s, HolderWith K r (f i)) :
    HolderWith ((∑ i ∈ s, c i) * K) r fun x ↦ ∑ i ∈ s, c i • f i x := by
  have h := HolderWith.sum (s := s) (C := fun i ↦ K * ‖(c i : ℝ)‖₊)
    (f := fun i x ↦ (c i : ℝ) • f i x) fun i hi ↦ (hf i hi).smul (c i : ℝ)
  simp only [Real.nnNorm_natCast, Nat.cast_smul_eq_nsmul] at h
  rwa [Nat.cast_sum, Finset.sum_mul, Finset.sum_congr rfl fun i _ ↦ mul_comm (c i : ℝ≥0) K]

/-! ### The fields of the product -/

variable (B : F →L[ℝ] G →L[ℝ] H)

/-- The field `D_t^r D_x^m (B u v)` given by the Leibniz rule. -/
private def productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) : E [×m]→L[ℝ] H :=
  ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m p) (jet v ij.2 m p)

private theorem sum_antidiagonal_choose (r : ℕ) :
    ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 = 2 ^ r := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Nat.sum_range_choose r

private theorem continuous_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) : Continuous (productField B u v r m) :=
  continuous_finsetSum _ fun ij _ ↦
    (((B.leibnizJet E m).continuous₂.comp
      ((continuous_jet u ij.1 m).prodMk (continuous_jet v ij.2 m)))).const_smul _

/-- The Leibniz map of order `m` applied to two jets, bounded by `2ᵐ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_leibnizJet_jet_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r₁ r₂ m : ℕ) (p : slab (E := E) a b) :
    ‖B.leibnizJet E m (jet u r₁ m p) (jet v r₂ m p)‖ ≤ 2 ^ m * ‖B‖ * ‖u‖ * ‖v‖ :=
  ((B.leibnizJet E m).le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul (B.norm_leibnizJet_le m)
    (norm_jet_le u r₁ m p) (norm_nonneg _) (by positivity)) (norm_jet_le v r₂ m p)
    (norm_nonneg _) (by positivity))

private theorem norm_productField_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) :
    ‖productField B u v r m p‖ ≤ 2 ^ (r + m) * ‖B‖ * ‖u‖ * ‖v‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun ij _ ↦ norm_nsmul_le.trans
    (mul_le_mul_of_nonneg_left (norm_leibnizJet_jet_le B u v ij.1 ij.2 m p)
      (Nat.cast_nonneg _))).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_antidiagonal_choose, pow_add]
  push_cast
  ring

/-- The field `D_t^r D_x^m (B u v)` as a bounded continuous map. -/
private def productFieldBCF (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) : slab (E := E) a b →ᵇ (E [×m]→L[ℝ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (productField B u v r m)
    (continuous_productField B u v r m) (2 ^ (r + m) * ‖B‖ * ‖u‖ * ‖v‖)
    (norm_productField_le B u v r m)

private theorem productFieldBCF_apply (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) :
    productFieldBCF B u v r m p = productField B u v r m p := by
  simp [productFieldBCF]

/-- **The spatial Leibniz rule for the product fields.** -/
private theorem hasFDerivAt_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (t : Icc a b)
    (x : E) :
    HasFDerivAt (fun y ↦ productField B u v r m (slabMk y t))
      (productField B u v r (m + 1) (slabMk x t)).curryLeft x := by
  have hterm : ∀ ij ∈ Finset.antidiagonal r, HasFDerivAt
      (fun y ↦ r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m (slabMk y t))
        (jet v ij.2 m (slabMk y t)))
      (r.choose ij.1 • (B.leibnizJet E (m + 1) (jet u ij.1 (m + 1) (slabMk x t))
        (jet v ij.2 (m + 1) (slabMk x t))).curryLeft) x := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hD := B.hasFDerivAt_leibnizJet (n := m) (x := x)
      (f := fun y ↦ jet u ij.1 (m + 1) (slabMk y t))
      (g := fun y ↦ jet v ij.2 (m + 1) (slabMk y t))
      (fun i ↦ hasFDerivAt_mixedDerivL u (r := ij.1) (m := i) (by omega) t x)
      (fun i ↦ hasFDerivAt_mixedDerivL v (r := ij.2) (m := i) (by omega) t x)
    simp only [jetInit_jet] at hD
    exact hD.const_smul _
  have hsum := HasFDerivAt.fun_sum hterm
  refine hsum.congr_fderiv ?_
  ext h v
  simp [productField, -ContinuousLinearMap.curryLeft_leibnizJet_succ]

/-- **The time Leibniz rule for the product fields.** -/
private theorem hasDerivWithinAt_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (productFieldBCF B u v r m) x)
      (productField B u v (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hterm : ∀ ij ∈ Finset.antidiagonal r, HasDerivWithinAt
      (fun s ↦ r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m (slabMk x (projIcc a b hab.le s)))
        (jet v ij.2 m (slabMk x (projIcc a b hab.le s))))
      (r.choose ij.1 • (B.leibnizJet E m (jet u ij.1 m (slabMk x t))
        (jet v (ij.2 + 1) m (slabMk x t)) + B.leibnizJet E m (jet u (ij.1 + 1) m (slabMk x t))
          (jet v ij.2 m (slabMk x t)))) (Icc a b) t := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hu := hasDerivWithinAt_jet u (r := ij.1) (m := m) (by omega) x t
    have hv := hasDerivWithinAt_jet v (r := ij.2) (m := m) (by omega) x t
    have hB := (B.leibnizJet E m).hasDerivWithinAt_of_bilinear hu hv
    rw [projIcc_val] at hB
    exact hB.const_smul _
  have hsum := HasDerivWithinAt.fun_sum hterm
  have hfun : ParabolicC2HolderSpace.timeExtension hab.le (productFieldBCF B u v r m) x =
      fun s ↦ ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m
        (jet u ij.1 m (slabMk x (projIcc a b hab.le s)))
        (jet v ij.2 m (slabMk x (projIcc a b hab.le s))) := by
    funext s
    simp only [ParabolicC2HolderSpace.timeExtension_def, productFieldBCF_apply]
    rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  unfold productField
  rw [Finset.sum_antidiagonal_choose_succ_nsmul
    (fun i j ↦ B.leibnizJet E m (jet u i m (slabMk x t)) (jet v j m (slabMk x t))) r]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm]

/-- The Hölder constant of the product fields of top order. -/
private theorem holderWith_productField (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    HolderWith (2 ^ r * (2 ^ m * ‖B‖₊ * (12 * ‖u‖₊ * ‖v‖₊))) α (productField B u v r m) := by
  have hK : ∀ ij ∈ Finset.antidiagonal r, HolderWith (2 ^ m * ‖B‖₊ * (12 * ‖u‖₊ * ‖v‖₊)) α
      fun p ↦ B.leibnizJet E m (jet u ij.1 m p) (jet v ij.2 m p) := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hP := (B.leibnizJet E m).holderWith_comp₂ (holderWith_jet hα u (r := ij.1) (m := m)
      (by omega)) (holderWith_jet hα v (r := ij.2) (m := m) (by omega))
      (Mf := ‖u‖₊) (Mg := ‖v‖₊) (norm_jet_le u ij.1 m) (norm_jet_le v ij.2 m)
    refine fun p q ↦ (hP p q).trans ?_
    gcongr
    · rw [← NNReal.coe_le_coe]
      push_cast
      exact B.norm_leibnizJet_le m
    · exact le_of_eq (by ring)
  have hsum := holderWith_sum_nsmul (Finset.antidiagonal r) (fun ij ↦ r.choose ij.1) hK
  rwa [sum_antidiagonal_choose, Nat.cast_pow, Nat.cast_ofNat] at hsum

/-- The Hölder constant of the time slices of the product fields one order below the top. -/
private theorem holderWith_productField_slabMk (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace k α E F hab) (v : ParabolicCkHolderSpace k α E G hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (2 ^ r * (2 ^ m * ‖B‖₊ * (6 * ‖u‖₊ * ‖v‖₊))) ((1 + α) / 2)
      fun t : Icc a b ↦ productField B u v r m (slabMk x t) := by
  have hK : ∀ ij ∈ Finset.antidiagonal r, HolderWith (2 ^ m * ‖B‖₊ * (6 * ‖u‖₊ * ‖v‖₊))
      ((1 + α) / 2) fun t : Icc a b ↦
        B.leibnizJet E m (jet u ij.1 m (slabMk x t)) (jet v ij.2 m (slabMk x t)) :=
      fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hP := (B.leibnizJet E m).holderWith_comp₂
      (holderWith_jet_slabMk hα u (r := ij.1) (m := m) (by omega) x)
      (holderWith_jet_slabMk hα v (r := ij.2) (m := m) (by omega) x)
      (Mf := ‖u‖₊) (Mg := ‖v‖₊) (fun t ↦ norm_jet_le u ij.1 m _) (fun t ↦ norm_jet_le v ij.2 m _)
    refine fun t s ↦ (hP t s).trans ?_
    gcongr
    · rw [← NNReal.coe_le_coe]
      push_cast
      exact B.norm_leibnizJet_le m
    · exact le_of_eq (by ring)
  have hsum := holderWith_sum_nsmul (Finset.antidiagonal r) (fun ij ↦ r.choose ij.1) hK
  rwa [sum_antidiagonal_choose, Nat.cast_pow, Nat.cast_ofNat] at hsum

private theorem coe_productFieldBCF (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) :
    ⇑(productFieldBCF B u v r m) = productField B u v r m :=
  funext (productFieldBCF_apply B u v r m)

/-- The norm of a product field is at most `2ᵏ ‖B‖ ‖u‖ ‖v‖` at every order `2 r + m ≤ k`. -/
private theorem norm_productFieldBCF_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖productFieldBCF B u v r m‖ ≤ 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ :=
  (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _).trans (by
    gcongr
    · norm_num
    · omega)

/-- The pointwise product `B u v`, before bundling. -/
private def compAux (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) : ParabolicCkHolderSpace k α E H hab :=
  mk (productFieldBCF B u v)
    (fun _ _ h t x ↦ by
      simpa only [productFieldBCF_apply] using hasFDerivAt_productField B u v h t x)
    (fun _ _ h x t ↦ by
      rw [productFieldBCF_apply]
      exact hasDerivWithinAt_productField B u v h x t)
    (fun _ _ h ↦ ⟨_, fun x ↦ by
      simpa only [productFieldBCF_apply] using holderWith_productField_slabMk B hα u v h.le x⟩)
    (fun _ _ h ↦ by
      rw [coe_productFieldBCF]
      exact (holderWith_productField B hα u v h.le).memHolder)

private theorem mixedDerivL_compAux (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (compAux B hα u v) = productFieldBCF B u v r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem compAux_apply (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (p : slab (E := E) a b) :
    compAux B hα u v p = B (u p) (v p) := by
  rw [compAux, mk_apply, productFieldBCF_apply, productField]
  simp [jet]

/-- The real value of the Hölder constants of the product fields at order `2 r + m ≤ k` is at most
`c 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem coe_two_pow_mul_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) (c : ℝ≥0) :
    ((2 ^ r * (2 ^ m * ‖B‖₊ * (c * ‖u‖₊ * ‖v‖₊)) : ℝ≥0) : ℝ) ≤
      c * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  have h2 : (2 : ℝ) ^ r * 2 ^ m ≤ 2 ^ k := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ c * ‖B‖ * ‖u‖ * ‖v‖)
  push_cast
  nlinarith

/-- The time slices of the product one order below the top have norm at most
`7 · 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_timeSliceL_compAux_le (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖timeSliceL r m (compAux B hα u v)‖ ≤ 7 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  by_cases h1 : 2 * r + m + 1 = k
  · refine (norm_timeSliceL_le_of_holderWith _ h1
      (C := 2 ^ r * (2 ^ m * ‖B‖₊ * (6 * ‖u‖₊ * ‖v‖₊))) fun x ↦ ?_).trans ?_
    · rw [mixedDerivL_compAux B hα u v h]
      simpa only [productFieldBCF_apply] using holderWith_productField_slabMk B hα u v h1.le x
    · have h6 : ((2 ^ r * (2 ^ m * ‖B‖₊ * (6 * ‖u‖₊ * ‖v‖₊)) : ℝ≥0) : ℝ) ≤
          6 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
        exact_mod_cast coe_two_pow_mul_le B u v h 6
      rw [mixedDerivL_compAux B hα u v h]
      linarith [norm_productFieldBCF_le B u v h]
  · rw [timeSliceL_of_ne h1, zero_apply, norm_zero]
    positivity

/-- The Hölder field of the product at the top order has norm at most
`13 · 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_mixedDerivHolderL_compAux_le (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace k α E F hab) (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) :
    ‖mixedDerivHolderL r m (compAux B hα u v)‖ ≤ 13 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  by_cases h0 : 2 * r + m = k
  · have hcoe : ⇑(mixedDerivHolderL r m (compAux B hα u v)) = productField B u v r m := by
      funext q
      rw [mixedDerivHolderL_apply _ h0, mixedDerivL_compAux B hα u v h, productFieldBCF_apply]
    refine (HolderSpace.norm_le_of_norm_le_of_holderWith (M := 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖)
      (by positivity) (fun q ↦ ?_)
      (hcoe ▸ holderWith_productField B hα u v h)).trans ?_
    · rw [hcoe, ← productFieldBCF_apply]
      exact ((productFieldBCF B u v r m).norm_coe_le_norm q).trans
        (norm_productFieldBCF_le B u v h)
    · have h12 : ((2 ^ r * (2 ^ m * ‖B‖₊ * (12 * ‖u‖₊ * ‖v‖₊)) : ℝ≥0) : ℝ) ≤
          12 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
        exact_mod_cast coe_two_pow_mul_le B u v h 12
      linarith
  · rw [mixedDerivHolderL_of_ne h0, zero_apply, norm_zero]
    positivity

/-- At most `(k + 1)²` pairs `(r, m)` have parabolic order `2 r + m ≤ k`. -/
private theorem card_parabolicDerivPairs_le (k : ℕ) :
    ((parabolicDerivPairs k).card : ℝ) ≤ (k + 1) ^ 2 := by
  have : (parabolicDerivPairs k).card ≤ (k + 1) ^ 2 := by
    refine (Finset.card_le_card (t := Finset.range (k + 1) ×ˢ Finset.range (k + 1))
      fun q hq ↦ ?_).trans ?_
    · have := mem_parabolicDerivPairs.1 hq
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    · rw [Finset.card_product, Finset.card_range, sq]
  exact_mod_cast this

private theorem norm_compAux_le (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖compAux B hα u v‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  set M := 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ with hM
  -- Each pair `(r, m)` contributes at most `M + 7 M + 13 M`.
  have hterm : ∀ q ∈ parabolicDerivPairs k, ‖mixedDerivL q.1 q.2 (compAux B hα u v)‖ +
      (‖timeSliceL q.1 q.2 (compAux B hα u v)‖ + ‖mixedDerivHolderL q.1 q.2 (compAux B hα u v)‖) ≤
        21 * M := by
    rintro ⟨r, m⟩ hq
    have hq : 2 * r + m ≤ k := mem_parabolicDerivPairs.1 hq
    have hfield := norm_productFieldBCF_le B u v hq
    rw [← mixedDerivL_compAux B hα u v hq] at hfield
    linarith [norm_timeSliceL_compAux_le B hα u v hq, norm_mixedDerivHolderL_compAux_le B hα u v hq]
  rw [norm_eq]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  calc ((parabolicDerivPairs k).card : ℝ) * (21 * M) ≤ (k + 1) ^ 2 * (21 * M) := by
        gcongr
        exact card_parabolicDerivPairs_le k
    _ = 21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by rw [hM]; ring

end ParabolicCkHolderSpace

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.ParabolicCkHolderSpace TauCeti.ParabolicSpaceTime
open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}
  (B : F →L[ℝ] G →L[ℝ] H) (hα : α ≤ 1)

/-- For `α ≤ 1`, pointwise application `(u, v) ↦ B u v` of a continuous bilinear map, as a
continuous bilinear map of the bounded parabolic Hölder spaces `C_{par,b}^{k+α}` of order `k` on a
slab. -/
def compParabolicCkHolder₂ :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E G hab →L[ℝ]
      ParabolicCkHolderSpace k α E H hab :=
  (LinearMap.mk₂ ℝ (compAux B hα)
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])).mkContinuous₂
    (21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖) (norm_compAux_le B hα)

/- `LinearMap.mkContinuous₂_apply` and `LinearMap.mk₂_apply` do not fire here, as for the order-two
space `TauCeti.ParabolicC2HolderSpace`, whose definition as a submodule is not exposed either; the
equation is closed by `rfl` directly. -/
private theorem compParabolicCkHolder₂_eq (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    B.compParabolicCkHolder₂ hα u v = compAux B hα u v := (rfl)

@[simp]
theorem compParabolicCkHolder₂_apply (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (p : slab (E := E) a b) :
    B.compParabolicCkHolder₂ hα u v p = B (u p) (v p) := by
  rw [compParabolicCkHolder₂_eq, compAux_apply]

/-- **The Leibniz rule for the fields.** For `2 r + m ≤ k`, the field `D_t^r D_x^m (B u v)` is
`∑_{r₁ + r₂ = r} (r choose r₁) Λₘ (J^{r₁} u, J^{r₂} v)`, where `Λₘ = B.leibnizJet E m` and
`J^{r'} u = (D_t^{r'} D_x^i u)_{i ≤ m}` is the spatial jet of the `r'`-th time derivative. -/
theorem mixedDerivL_compParabolicCkHolder₂ (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k)
    (p : slab (E := E) a b) :
    mixedDerivL r m (B.compParabolicCkHolder₂ hα u v) p =
      ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m
        (fun i ↦ mixedDerivL ij.1 i u p) (fun i ↦ mixedDerivL ij.2 i v p) := by
  rw [compParabolicCkHolder₂_eq, mixedDerivL_compAux B hα u v h, productFieldBCF_apply]
  rfl

/-- **The product estimate.** Pointwise application of `B` to parabolic Hölder maps of order `k`
has operator norm at most `21 (k + 1)² 2ᵏ ‖B‖`, uniformly over the exponent, the spaces and the
slab. -/
theorem norm_compParabolicCkHolder₂_le :
    ‖B.compParabolicCkHolder₂ (k := k) (E := E) (hab := hab) hα‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ :=
  opNorm_le_bound₂ _ (by positivity) fun u v ↦ by
    rw [compParabolicCkHolder₂_eq]
    exact norm_compAux_le B hα u v

/-- The norm of `B u v` is at most `21 (k + 1)² 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
theorem norm_compParabolicCkHolder₂_apply_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖B.compParabolicCkHolder₂ hα u v‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [compParabolicCkHolder₂_eq]
  exact norm_compAux_le B hα u v

end ContinuousLinearMap
