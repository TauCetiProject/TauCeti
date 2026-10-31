/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Functional-equation pairs with a level

Mathlib's `WeakFEPair` packages the Mellin-transform argument behind the functional equations of
zeta and L-functions for a transformation law `f (1 / x) = ε x ^ k g x`. Theta kernels attached to
a lattice or an ideal satisfy this law only after a rescaling: the natural law reads
`f (1 / (N t)) = ε t ^ k g t` for a level `N > 0`. This file adds that level by transport and
develops no second Mellin theory. It adapts the wrapper proposed in the note in Mathlib's
`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`: that note writes the law as
`f (N' / x) = (const) • x ^ k • g x`, so its `N'` corresponds to `1 / N` here, and where the note
rescales both `f` and `g`, the transport here rescales only `g`.

A `TauCeti.FEPairWithLevel` carries the hypotheses of `WeakFEPair` together with a level `N > 0`.
Its transport `TauCeti.FEPairWithLevel.toWeakFEPair` replaces `g` by `g (· / N)` and `ε` by
`ε N ^ (-k)` and leaves `f` alone, so the completed function `TauCeti.FEPairWithLevel.Λ` of `f` is
Mathlib's `WeakFEPair.Λ` of the transported pair. Unlike Mathlib's carrier, `f` and `g` vanish
on `(-∞, 0]`, so a pair is determined by the values its laws actually use (`ext`). Conversely
`WeakFEPair.toFEPairWithLevel` presents any weak pair at any level, extending its functions by zero
off `(0, ∞)`. The round trip from a pair is the identity, and the round trip from a weak pair
changes only values at nonpositive inputs, so it keeps the completed function.

The one fact the level adds is that the continued Mellin transform of `g (· / N)` is `N ^ s` times
that of `g`. Combined with Mathlib's functional equation it gives the Mellin principle at level `N`
(Neukirch, *Algebraic Number Theory*, VII (1.4), with a level):
`Λ(f, s) = ε N ^ (-s) Λ(g, k - s)`.

## Main declarations

* `TauCeti.FEPairWithLevel`: a functional-equation pair with a level.
* `TauCeti.FEPairWithLevel.ext`: a pair is determined by its functions on `(0, ∞)` and its
  constants.
* `TauCeti.FEPairWithLevel.toWeakFEPair`: its transport to Mathlib's `WeakFEPair`.
* `WeakFEPair.toFEPairWithLevel`: a weak pair presented at a given level.
* `TauCeti.FEPairWithLevel.symm`: the pair read backwards at the same level.
* `WeakFEPair.Λ_congr`: the completed function of a weak pair depends only on `f` on `(0, ∞)` and
  the constants.
* `TauCeti.FEPairWithLevel.Λ`: the completed function, the continued Mellin transform of `f - f₀`.
* `TauCeti.FEPairWithLevel.hasMellin`, `differentiableAt_Λ`, `Λ_residue_zero`, `Λ_residue_k`:
  its Mellin representation, regularity and residues.
* `TauCeti.FEPairWithLevel.toWeakFEPair_symm_Λ`: the dual side of the transport is `N ^ s` times
  the completed function of `g`.
* `TauCeti.FEPairWithLevel.Λ_eq` and `Λ_eventuallyEq`: the functional equation at level `N`, off
  the poles and as an equality of punctured germs at every point.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §1.
* The carrier and its main theorems are Mathlib's `WeakFEPair`, `WeakFEPair.functional_equation`
  and `WeakFEPair.hasMellin` (D. Loeffler); the dual-side comparison uses `mellin_comp_mul_right`
  and the identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/

public section

noncomputable section

open Real Complex Filter Asymptotics Set MeasureTheory

open scoped Topology

namespace TauCeti

/-- A functional-equation pair with a level. The fields are those of Mathlib's `WeakFEPair`:
functions `f` and `g` locally integrable on `(0, ∞)`, equal to the constants `f₀` and `g₀` at `∞` up
to an error decaying faster than every power, a weight `k > 0` and a root number `ε ≠ 0`. The
transformation law is taken at a level `N > 0`: `f (1 / (N t)) = ε t ^ k g t`. At `N = 1` it is
Mathlib's law. Only the values of `f` and `g` on `(0, ∞)` enter the laws, so both are required to
vanish elsewhere. -/
structure FEPairWithLevel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  /-- The function whose completed Mellin transform is studied. -/
  f : ℝ → E
  /-- The dual function. -/
  g : ℝ → E
  /-- The weight, the exponent in the transformation law. -/
  k : ℝ
  /-- The root number. -/
  ε : ℂ
  /-- The constant term of `f` at `∞`. -/
  f₀ : E
  /-- The constant term of `g` at `∞`. -/
  g₀ : E
  /-- The level. -/
  N : ℝ
  hN : 0 < N
  hf_int : LocallyIntegrableOn f (Ioi 0)
  hg_int : LocallyIntegrableOn g (Ioi 0)
  hf_nonpos : ∀ t ≤ 0, f t = 0
  hg_nonpos : ∀ t ≤ 0, g t = 0
  hk : 0 < k
  hε : ε ≠ 0
  h_feq : ∀ t ∈ Ioi (0 : ℝ), f (1 / (N * t)) = (ε * ↑(t ^ k)) • g t
  hf_top (r : ℝ) : (f · - f₀) =O[atTop] (· ^ r)
  hg_top (r : ℝ) : (g · - g₀) =O[atTop] (· ^ r)

namespace FEPairWithLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A pair is determined by the values of its functions on `(0, ∞)`, its weight, root number,
constant terms and level. -/
theorem ext {P Q : FEPairWithLevel E} (hf : EqOn P.f Q.f (Ioi 0)) (hg : EqOn P.g Q.g (Ioi 0))
    (hk : P.k = Q.k) (hε : P.ε = Q.ε) (hf₀ : P.f₀ = Q.f₀) (hg₀ : P.g₀ = Q.g₀) (hN : P.N = Q.N) :
    P = Q := by
  have key {u v : ℝ → E} (huv : EqOn u v (Ioi 0)) (hu : ∀ t ≤ 0, u t = 0)
      (hv : ∀ t ≤ 0, v t = 0) : u = v := by
    funext t
    rcases le_or_gt t 0 with ht | ht
    · rw [hu t ht, hv t ht]
    · exact huv ht
  have hf' := key hf P.hf_nonpos Q.hf_nonpos
  have hg' := key hg P.hg_nonpos Q.hg_nonpos
  cases P
  cases Q
  dsimp only at hf' hg' hk hε hf₀ hg₀ hN
  subst hf' hg' hk hε hf₀ hg₀ hN
  rfl

end FEPairWithLevel

end TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A weak functional-equation pair presented at level `N > 0`: `g` is replaced by `g (N ·)` and
`ε` by `ε N ^ k`, so that `f (1 / (N t)) = (ε N ^ k) t ^ k g (N t)`. Both functions are extended by
zero off `(0, ∞)`, where the laws do not see them. -/
def WeakFEPair.toFEPairWithLevel (Q : WeakFEPair E) (N : ℝ) (hN : 0 < N) :
    TauCeti.FEPairWithLevel E where
  f := (Ioi 0).indicator Q.f
  g := (Ioi 0).indicator fun t ↦ Q.g (N * t)
  k := Q.k
  ε := Q.ε * ↑(N ^ Q.k)
  f₀ := Q.f₀
  g₀ := Q.g₀
  N := N
  hN := hN
  hf_int := Q.hf_int.congr <| (ae_restrict_mem measurableSet_Ioi).mono fun _ ht ↦
    (indicator_of_mem ht _).symm
  hg_int := (Q.hg_int.comp_smul_of_mapsTo hN.ne' fun _ ht ↦ mul_pos hN ht).congr <|
    (ae_restrict_mem measurableSet_Ioi).mono fun _ ht ↦ (indicator_of_mem ht _).symm
  hf_nonpos _ ht := indicator_of_notMem (notMem_Ioi.mpr ht) _
  hg_nonpos _ ht := indicator_of_notMem (notMem_Ioi.mpr ht) _
  hk := Q.hk
  hε := mul_ne_zero Q.hε (ofReal_ne_zero.mpr (rpow_pos_of_pos hN _).ne')
  h_feq t ht := by
    have ht' : (0 : ℝ) < t := ht
    rw [indicator_of_mem (mem_Ioi.mpr (one_div_pos.mpr (mul_pos hN ht'))), indicator_of_mem ht,
      Q.h_feq _ (mul_pos hN ht'), Real.mul_rpow hN.le ht'.le]
    congr 1
    push_cast
    ring
  hf_top r := (Q.hf_top r).congr' ((eventually_gt_atTop 0).mono fun _ ht ↦ by
    simp only [indicator_of_mem (mem_Ioi.mpr ht)]) EventuallyEq.rfl
  hg_top r := ((Q.hg_top r).comp_const_mul_rpow hN).congr' ((eventually_gt_atTop 0).mono
    fun _ ht ↦ by simp only [indicator_of_mem (mem_Ioi.mpr ht)]) EventuallyEq.rfl

namespace WeakFEPair

variable (Q : WeakFEPair E) (N : ℝ) (hN : 0 < N)

@[simp] theorem toFEPairWithLevel_f : (Q.toFEPairWithLevel N hN).f = (Ioi 0).indicator Q.f := (rfl)

@[simp] theorem toFEPairWithLevel_g :
    (Q.toFEPairWithLevel N hN).g = (Ioi 0).indicator fun t ↦ Q.g (N * t) := (rfl)

@[simp] theorem toFEPairWithLevel_k : (Q.toFEPairWithLevel N hN).k = Q.k := (rfl)

@[simp] theorem toFEPairWithLevel_ε : (Q.toFEPairWithLevel N hN).ε = Q.ε * ↑(N ^ Q.k) := (rfl)

@[simp] theorem toFEPairWithLevel_f₀ : (Q.toFEPairWithLevel N hN).f₀ = Q.f₀ := (rfl)

@[simp] theorem toFEPairWithLevel_g₀ : (Q.toFEPairWithLevel N hN).g₀ = Q.g₀ := (rfl)

@[simp] theorem toFEPairWithLevel_N : (Q.toFEPairWithLevel N hN).N = N := (rfl)

/-- Two weak pairs whose functions `f` agree on `(0, ∞)`, with the same weight, root number and
constants, have the same completed function: `Λ` sees `f` only through a Mellin transform. -/
theorem Λ_congr {P P' : WeakFEPair E} (hf : EqOn P.f P'.f (Ioi 0)) (hk : P.k = P'.k)
    (hε : P.ε = P'.ε) (hf₀ : P.f₀ = P'.f₀) (hg₀ : P.g₀ = P'.g₀) : P.Λ = P'.Λ := by
  have hmod : EqOn P.f_modif P'.f_modif (Ioi 0) := fun t ht ↦ by
    simp only [f_modif, Pi.add_apply, indicator_apply, hf ht, hk, hε, hf₀, hg₀]
  funext s
  simp only [Λ, Λ₀, mellin, hk, hε, hf₀, hg₀]
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by rw [hmod ht]]

end WeakFEPair

namespace TauCeti.FEPairWithLevel

variable (P : FEPairWithLevel E)

/-- The level transport to Mathlib's pair: `g` becomes `g (· / N)` and `ε` becomes `ε N ^ (-k)`.
The law at `t = x / N` reads `f (1 / x) = (ε N ^ (-k)) x ^ k g (x / N)`, which is Mathlib's law.
The transport moves neither `f`, `k`, `f₀` nor `g₀`. -/
def toWeakFEPair : WeakFEPair E where
  f := P.f
  g x := P.g (x / P.N)
  k := P.k
  ε := P.ε * ↑(P.N ^ (-P.k))
  f₀ := P.f₀
  g₀ := P.g₀
  hf_int := P.hf_int
  hg_int := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      P.hg_int.comp_smul_of_mapsTo (inv_ne_zero P.hN.ne') fun _ hx ↦ mul_pos (inv_pos.2 P.hN) hx
  hk := P.hk
  hε := mul_ne_zero P.hε (ofReal_ne_zero.mpr (rpow_pos_of_pos P.hN _).ne')
  h_feq x hx := by
    have hx' : (0 : ℝ) < x := hx
    have h := P.h_feq (x / P.N) (div_pos hx' P.hN)
    rw [mul_div_cancel₀ x P.hN.ne'] at h
    rw [h, Real.div_rpow hx'.le P.hN.le, Real.rpow_neg P.hN.le]
    congr 1
    push_cast
    ring
  hf_top := P.hf_top
  hg_top r := by
    simpa only [div_eq_inv_mul] using (P.hg_top r).comp_const_mul_rpow (inv_pos.2 P.hN)

@[simp] theorem toWeakFEPair_f : P.toWeakFEPair.f = P.f := (rfl)

@[simp] theorem toWeakFEPair_g : P.toWeakFEPair.g = fun x ↦ P.g (x / P.N) := (rfl)

@[simp] theorem toWeakFEPair_k : P.toWeakFEPair.k = P.k := (rfl)

@[simp] theorem toWeakFEPair_ε : P.toWeakFEPair.ε = P.ε * ↑(P.N ^ (-P.k)) := (rfl)

@[simp] theorem toWeakFEPair_f₀ : P.toWeakFEPair.f₀ = P.f₀ := (rfl)

@[simp] theorem toWeakFEPair_g₀ : P.toWeakFEPair.g₀ = P.g₀ := (rfl)

/-- Transporting a weak pair presented at level `N` returns its functions on `(0, ∞)`. -/
theorem _root_.WeakFEPair.toWeakFEPair_toFEPairWithLevel_f (Q : WeakFEPair E) {N : ℝ}
    (hN : 0 < N) : EqOn (Q.toFEPairWithLevel N hN).toWeakFEPair.f Q.f (Ioi 0) :=
  fun _ ht ↦ indicator_of_mem ht _

/-- Transporting a weak pair presented at level `N` returns its dual function on `(0, ∞)`. -/
theorem _root_.WeakFEPair.toWeakFEPair_toFEPairWithLevel_g (Q : WeakFEPair E) {N : ℝ}
    (hN : 0 < N) : EqOn (Q.toFEPairWithLevel N hN).toWeakFEPair.g Q.g (Ioi 0) := fun x hx ↦ by
  simp [indicator_of_mem (mem_Ioi.mpr (div_pos hx hN)), mul_div_cancel₀ _ hN.ne']

/-- Transporting a weak pair presented at level `N` returns its root number. -/
theorem _root_.WeakFEPair.toWeakFEPair_toFEPairWithLevel_ε (Q : WeakFEPair E) {N : ℝ}
    (hN : 0 < N) : (Q.toFEPairWithLevel N hN).toWeakFEPair.ε = Q.ε := by
  simp only [toWeakFEPair_ε, WeakFEPair.toFEPairWithLevel_ε, WeakFEPair.toFEPairWithLevel_k,
    WeakFEPair.toFEPairWithLevel_N]
  rw [Real.rpow_neg hN.le, ofReal_inv,
    mul_inv_cancel_right₀ (ofReal_ne_zero.mpr (rpow_pos_of_pos hN _).ne')]

/-- Presenting the transport of a pair at its own level returns the pair. -/
@[simp]
theorem toFEPairWithLevel_toWeakFEPair :
    P.toWeakFEPair.toFEPairWithLevel P.N P.hN = P := by
  refine ext (fun t ht ↦ ?_) (fun t ht ↦ ?_) rfl ?_ rfl rfl rfl
  · exact indicator_of_mem ht _
  · simp [indicator_of_mem ht, mul_div_cancel_left₀ _ P.hN.ne']
  · simp only [WeakFEPair.toFEPairWithLevel_ε, toWeakFEPair_ε, toWeakFEPair_k]
    rw [Real.rpow_neg P.hN.le, ofReal_inv,
      inv_mul_cancel_right₀ (ofReal_ne_zero.mpr (rpow_pos_of_pos P.hN _).ne')]

/-- The pair read backwards at the same level: `g (1 / (N t)) = (ε⁻¹ N ^ k) t ^ k f t`. -/
def symm : FEPairWithLevel E where
  f := P.g
  g := P.f
  k := P.k
  ε := P.ε⁻¹ * ↑(P.N ^ P.k)
  f₀ := P.g₀
  g₀ := P.f₀
  N := P.N
  hN := P.hN
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_nonpos := P.hg_nonpos
  hg_nonpos := P.hf_nonpos
  hk := P.hk
  hε := mul_ne_zero (inv_ne_zero P.hε) (ofReal_ne_zero.mpr (rpow_pos_of_pos P.hN _).ne')
  h_feq t ht := by
    have ht' : (0 : ℝ) < t := ht
    have hN := P.hN
    have h := P.h_feq (1 / (P.N * t)) (one_div_pos.2 (mul_pos hN ht'))
    have hinv : 1 / (P.N * (1 / (P.N * t))) = t := by field_simp
    rw [hinv] at h
    rw [h, smul_smul, Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
      Real.mul_rpow hN.le ht'.le]
    have h1 : ((P.N ^ P.k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (rpow_pos_of_pos hN _).ne'
    have h2 : ((t ^ P.k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (rpow_pos_of_pos ht' _).ne'
    push_cast
    field_simp [P.hε]
    simp
  hf_top := P.hg_top
  hg_top := P.hf_top

@[simp] theorem symm_f : P.symm.f = P.g := (rfl)

@[simp] theorem symm_g : P.symm.g = P.f := (rfl)

@[simp] theorem symm_k : P.symm.k = P.k := (rfl)

@[simp] theorem symm_ε : P.symm.ε = P.ε⁻¹ * ↑(P.N ^ P.k) := (rfl)

@[simp] theorem symm_f₀ : P.symm.f₀ = P.g₀ := (rfl)

@[simp] theorem symm_g₀ : P.symm.g₀ = P.f₀ := (rfl)

@[simp] theorem symm_N : P.symm.N = P.N := (rfl)

/-- Reading a pair backwards twice returns the pair. -/
@[simp]
theorem symm_symm : P.symm.symm = P := by
  have h : ((P.N ^ P.k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (rpow_pos_of_pos P.hN _).ne'
  refine ext (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl ?_ rfl rfl rfl
  simp only [symm_ε, symm_k, symm_N, mul_inv, inv_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]

/-- The completed function `Λ(f, s)`: Mathlib's `WeakFEPair.Λ` of the transported pair, which
agrees with the Mellin transform of `f - f₀` on `Re s > k` (`hasMellin`) and continues it
meromorphically to `ℂ` with poles at most at `0` and `k`. -/
def Λ : ℂ → E := P.toWeakFEPair.Λ

@[simp]
theorem toWeakFEPair_Λ : P.toWeakFEPair.Λ = P.Λ := (rfl)

/-- A weak pair presented at any level keeps its completed function: presentation followed by
transport changes both functions only at nonpositive inputs, which the Mellin transform does not
see. -/
@[simp]
theorem _root_.WeakFEPair.toFEPairWithLevel_Λ (Q : WeakFEPair E) {N : ℝ} (hN : 0 < N) :
    (Q.toFEPairWithLevel N hN).Λ = Q.Λ := by
  rw [← toWeakFEPair_Λ]
  exact WeakFEPair.Λ_congr (Q.toWeakFEPair_toFEPairWithLevel_f hN) rfl
    (Q.toWeakFEPair_toFEPairWithLevel_ε hN) rfl rfl

/-- On `Re s > k`, `Λ s` is the Mellin transform of `f - f₀`. -/
theorem hasMellin [CompleteSpace E] {s : ℂ} (hs : P.k < s.re) :
    HasMellin (P.f · - P.f₀) s (P.Λ s) :=
  P.toWeakFEPair.hasMellin hs

/-- `Λ` is differentiable away from `0` and `k`; the point `0` is regular when `f₀ = 0`, and `k`
when `g₀ = 0`. -/
theorem differentiableAt_Λ {s : ℂ} (hs : s ≠ 0 ∨ P.f₀ = 0) (hs' : s ≠ P.k ∨ P.g₀ = 0) :
    DifferentiableAt ℂ P.Λ s :=
  P.toWeakFEPair.differentiableAt_Λ hs hs'

/-- The residue of `Λ` at `s = 0` is `-f₀`. -/
theorem Λ_residue_zero : Tendsto (fun s ↦ s • P.Λ s) (𝓝[≠] 0) (𝓝 (-P.f₀)) :=
  P.toWeakFEPair.Λ_residue_zero

/-- The residue of `Λ` at `s = k` is `ε N ^ (-k) g₀`. -/
theorem Λ_residue_k :
    Tendsto (fun s : ℂ ↦ (s - P.k) • P.Λ s) (𝓝[≠] (P.k : ℂ))
      (𝓝 ((P.ε * (P.N : ℂ) ^ (-(P.k : ℂ))) • P.g₀)) := by
  have h := P.toWeakFEPair.Λ_residue_k
  rwa [toWeakFEPair_ε, ofReal_cpow P.hN.le, ofReal_neg] at h

/-- The dual side of the transported pair is the continued Mellin transform of `g (· / N)`, which
is `N ^ s` times that of `g`. Stated off `0` and `k`, where both sides are values of continued
functions rather than junk values at poles. -/
theorem toWeakFEPair_symm_Λ [CompleteSpace E] {s : ℂ} (h0 : s ≠ 0) (hk : s ≠ P.k) :
    P.toWeakFEPair.symm.Λ s = (P.N : ℂ) ^ s • P.symm.Λ s := by
  have hfin : ({0, (P.k : ℂ)} : Set ℂ).Finite := (Set.finite_singleton _).insert _
  set U : Set ℂ := ({0, (P.k : ℂ)} : Set ℂ)ᶜ with hU
  have memU {z : ℂ} : z ∈ U ↔ z ≠ 0 ∧ z ≠ (P.k : ℂ) := by simp [hU, not_or]
  have hUo : IsOpen U := hfin.isClosed.isOpen_compl
  have hUc : IsPreconnected U := (Set.Countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) hfin.countable).isPreconnected
  have hN0 : (P.N : ℂ) ≠ 0 := ofReal_ne_zero.mpr P.hN.ne'
  -- Both sides are analytic on the connected set `ℂ ∖ {0, k}`.
  have hL : AnalyticOnNhd ℂ P.toWeakFEPair.symm.Λ U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hUo
    obtain ⟨hz0, hzk⟩ := memU.mp hz
    exact (P.toWeakFEPair.symm.differentiableAt_Λ (.inl hz0) (.inl hzk)).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ (fun z ↦ (P.N : ℂ) ^ z • P.symm.Λ z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hUo
    obtain ⟨hz0, hzk⟩ := memU.mp hz
    exact ((differentiableAt_id.const_cpow (.inl hN0)).smul
      (P.symm.differentiableAt_Λ (.inl hz0) (.inl hzk))).differentiableWithinAt
  have hmem : (P.k : ℂ) + 1 ∈ U := by
    refine memU.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have := congrArg Complex.re h
      simp only [add_re, ofReal_re, one_re, zero_re] at this
      linarith [P.hk]
    · simpa using congrArg Complex.re h
  -- They agree on `Re s > k`, where both are Mellin transforms.
  have hev : P.toWeakFEPair.symm.Λ =ᶠ[𝓝 ((P.k : ℂ) + 1)]
      fun z ↦ (P.N : ℂ) ^ z • P.symm.Λ z := by
    have hre : ∀ᶠ z in 𝓝 ((P.k : ℂ) + 1), P.k < z.re :=
      (continuous_re.tendsto _).eventually (lt_mem_nhds (by simp))
    filter_upwards [hre] with z hz
    rw [← (P.toWeakFEPair.symm.hasMellin hz).2, ← (P.symm.hasMellin hz).2]
    simp only [WeakFEPair.symm_f, WeakFEPair.symm_f₀, toWeakFEPair_g, toWeakFEPair_g₀, symm_f,
      symm_f₀]
    have h := mellin_comp_mul_right (fun t ↦ P.g t - P.g₀) z (inv_pos.mpr P.hN)
    simp only [← div_eq_mul_inv] at h
    refine h.trans ?_
    rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg P.hN.le]; exact pi_ne_zero.symm),
      cpow_neg, inv_inv]
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hmem hev (memU.mpr ⟨h0, hk⟩)

/-- The Mellin principle at level `N`: `Λ(f, s) = ε N ^ (-s) Λ(g, k - s)` off the poles `0`
and `k`. -/
theorem Λ_eq [CompleteSpace E] {s : ℂ} (h0 : s ≠ 0) (hk : s ≠ P.k) :
    P.Λ s = (P.ε * (P.N : ℂ) ^ (-s)) • P.symm.Λ (P.k - s) := by
  have h := P.toWeakFEPair.functional_equation (P.k - s)
  rw [toWeakFEPair_k, sub_sub_cancel, toWeakFEPair_Λ,
    P.toWeakFEPair_symm_Λ (sub_ne_zero.mpr hk.symm) (fun h' ↦ h0 (sub_eq_self.mp h')),
    smul_smul] at h
  rw [h, toWeakFEPair_ε, ofReal_cpow P.hN.le, mul_assoc,
    ← cpow_add _ _ (ofReal_ne_zero.mpr P.hN.ne')]
  congr 3
  push_cast
  ring

/-- The Mellin principle at level `N` as an equality of punctured germs at every point, the poles
included. -/
theorem Λ_eventuallyEq [CompleteSpace E] (s : ℂ) :
    P.Λ =ᶠ[𝓝[≠] s] fun z ↦ (P.ε * (P.N : ℂ) ^ (-z)) • P.symm.Λ (P.k - z) := by
  have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
    rcases eq_or_ne s a with rfl | h
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h)
  filter_upwards [hne 0, hne P.k] with z hz0 hzk
  exact P.Λ_eq hz0 hzk

end TauCeti.FEPairWithLevel
