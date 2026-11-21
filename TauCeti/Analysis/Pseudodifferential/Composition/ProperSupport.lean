/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Classical
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic
import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Basic
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic

/-!
# Composition with a properly supported operator

The composition symbol `a # b` of `TauCeti.Symbol.sharp` is built from the Fourier transforms of
the position slices of `b`, so it needs `b` to have compact spatial support. This file removes that
condition when the left factor is properly supported: let `a` be a symbol of order `m'` of
propagation at most `ε` (`TauCeti.Symbol.HasPropagationLE`), so that `Op(a) w (x)` only depends on
`w` on the ball of radius `ε` about `x`, and let `b` be any symbol of order `m`, with no condition
on its spatial support. Then `Op(a) ∘ Op(b)` is the quantization of a symbol of order `m' + m`,
`a.properSharp ha b`, which is computed near every position by the composition symbol of a
localization of `b`:

`(a.properSharp ha b)(x, ξ) = (a # b')(x, ξ)`

for every symbol `b'` with compact spatial support that agrees with `b` on the ball of radius `ε`
about `x` (`TauCeti.Symbol.coefficient_properSharp_eq_sharp`), for instance `ψ(y) b(y, ξ)` for a
cutoff `ψ` equal to `1` on that ball. This value does not depend on `b'`
(`TauCeti.Symbol.HasPropagationLE.coefficient_sharp_congr`): `Op(a # b') u (x)` only involves
`Op(b') u` near `x`, where it equals `Op(b) u`.

## Main results

* `TauCeti.Symbol.properSharp`: the composition symbol of a symbol `a` of finite propagation with
  an arbitrary symbol `b`. It is `a # b` when `b` has compact spatial support
  (`TauCeti.Symbol.properSharp_eq_sharp`).
* `TauCeti.Symbol.quantizeSchwartzValue_properSharp`: **composition of quantizations**.
  `Op(a.properSharp ha b) u (x) = Op(a) w (x)` for every Schwartz function `w` that agrees with
  `Op(b) u` on the ball of radius `ε` about `x`. In particular
  `Op(a.properSharp ha b) u = Op(a) (Op(b) u)` whenever `Op(b) u` has compact support
  (`TauCeti.Symbol.quantizeSchwartzValue_properSharp_of_hasCompactSupport`), for instance when `u`
  has compact support and `b` has finite propagation.
* `TauCeti.Symbol.HasPropagationLE.properSharp`: if `b` has propagation at most `ε'`, then the
  composition has propagation at most `ε + ε'`, so properly supported operators compose to
  properly supported operators.
* `TauCeti.Symbol.isAsymptoticSum_properSharp`: the **composition expansion**
  `a.properSharp ha b ∼ ∑ₖ sharpTerm a b k`, with remainders of order `m' + m - N`.
* `TauCeti.Symbol.properSharp_add`, `TauCeti.Symbol.add_properSharp` and their companions: the
  composition symbol is linear in each factor.
* `TauCeti.ClassicalSymbol.properSharp`: **the composition of classical symbols with a properly
  supported left factor is classical**, with the homogeneous terms `sharpTerms a.term b.term`, the
  formal composition of the expansions, and principal symbol `a_{m'} ∘ b_m`
  (`TauCeti.ClassicalSymbol.principal_properSharp`). It agrees with the composition
  `TauCeti.ClassicalSymbol.sharp` when `b` has compact spatial support
  (`TauCeti.ClassicalSymbol.properSharp_eq_sharp`), and is elliptic when `a` and `b` are
  (`TauCeti.ClassicalSymbol.IsElliptic.properSharp`).
* `TauCeti.ClassicalSymbol.exists_isSmoothing_sub_and_hasPropagationLE`: every classical symbol is,
  up to a smoothing symbol, a classical symbol of finite propagation with the same homogeneous
  terms.

Together with `TauCeti.Symbol.exists_isSmoothing_sub_and_hasPropagationLE`, which replaces every
symbol by one of finite propagation up to a smoothing symbol, this gives the composition calculus
of properly supported operators without any compact support condition on the symbols, both for
general symbols and within the classical symbols.

## Implementation notes

The coefficient of `a.properSharp ha b` at `x` is the coefficient of `a # b'` for the localization
`b'(y, ξ) = ψ_x(y) b(y, ξ)` by a bump function `ψ_x` about `x`. Near every position it agrees
with the single symbol `a # b''`, where `b''` is cut off by a bump function equal to `1` on a
larger ball, so it is a symbol of order `m' + m` (`TauCeti.Symbol.ofEventuallyEq`). The
remainders of the expansion are built in the same way from the remainders
`TauCeti.Symbol.sharpRemainder` of `a # b''`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28) and (2.5)–(2.7).
-/

public section

noncomputable section

open Filter Finset Metric
open scoped ContDiff SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' μ ε : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### Auxiliary constructions -/

section Auxiliary

/-- A bump function about `x`, equal to `1` on the closed ball of radius `max r 1`. -/
private def bump (r : ℝ) (x : CoordinateSpace n) : ContDiffBump x :=
  ⟨max r 1, max r 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩

/-- The localization `ψ(y) b(y, ξ)` of `b` by the bump function `ψ = bump r x`. -/
private def localize (r : ℝ) (x : CoordinateSpace n) (b : Symbol n V W m) : Symbol n V W m :=
  smulLeft (Complex.ofRealCLM.contDiff.comp (bump r x).contDiff) b

private theorem hasCompactSpatialSupport_localize (r : ℝ) (x : CoordinateSpace n)
    (b : Symbol n V W m) : (localize r x b).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_smulLeft _ ((bump r x).hasCompactSupport.comp_left Complex.ofReal_zero) b

private theorem coefficient_localize {r : ℝ} {x y : CoordinateSpace n} (hy : dist y x ≤ max r 1)
    (b : Symbol n V W m) (ξ : CoordinateSpace n) :
    (localize r x b).coefficient (y, ξ) = b.coefficient (y, ξ) := by
  simp [localize, (bump r x).one_of_mem_closedBall hy]

private theorem coefficient_localize_of_mem_ball {r : ℝ} {x y : CoordinateSpace n}
    (hy : y ∈ ball x r) (b : Symbol n V W m) (ξ : CoordinateSpace n) :
    (localize r x b).coefficient (y, ξ) = b.coefficient (y, ξ) :=
  coefficient_localize (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (le_max_left _ _)) hy) b ξ

/-- The localization to the ball of radius `r + 1` about `x` agrees with `b` on the ball of
radius `r` about every point of the ball of radius `1` about `x`. -/
private theorem coefficient_localize_add_one {r : ℝ} {x y z : CoordinateSpace n}
    (hy : y ∈ ball x 1) (hz : z ∈ ball y r) (b : Symbol n V W m) (ξ : CoordinateSpace n) :
    (localize (r + 1) x b).coefficient (z, ξ) = b.coefficient (z, ξ) :=
  coefficient_localize_of_mem_ball (ball_subset_ball' (add_le_add_right (mem_ball.1 hy).le r) hz)
    b ξ

end Auxiliary

/-! ### Locality of the composition symbol -/

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] {a : Symbol n W U m'}

/-- **Locality of the composition symbol.** If `a` has propagation at most `ε`, the composition
symbol `a # b` at the position `x` only depends on the right factor `b` on the ball of radius `ε`
about `x`. -/
theorem HasPropagationLE.coefficient_sharp_congr (ha : a.HasPropagationLE ε)
    {b : Symbol n V W m} {b' : Symbol n V W μ} (hb : b.HasCompactSpatialSupport)
    (hb' : b'.HasCompactSpatialSupport) {x : CoordinateSpace n}
    (h : ∀ y ∈ ball x ε, ∀ ξ, b.coefficient (y, ξ) = b'.coefficient (y, ξ))
    (ξ : CoordinateSpace n) :
    (a.sharp b hb).coefficient (x, ξ) = (a.sharp b' hb').coefficient (x, ξ) := by
  obtain ⟨C, -, hC⟩ := (a.sharp b hb).exists_bound_coefficient_slice x
  obtain ⟨C', -, hC'⟩ := (a.sharp b' hb').exists_bound_coefficient_slice x
  refine eq_of_forall_quantizeSchwartzValue_eq ((a.sharp b hb).continuous_coefficient_slice x)
    ((a.sharp b' hb').continuous_coefficient_slice x) hC hC' (fun u _ ↦ ?_) ξ
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  refine ha.quantizeSchwartzValue_congr fun y hy ↦ ?_
  rw [HasCompactSupport.toSchwartzMap_toFun, HasCompactSupport.toSchwartzMap_toFun]
  exact quantizeSchwartzValue_congr_left (h y hy) u

/-! ### The composition symbol -/

/-- **The composition symbol with a properly supported left factor.** For a symbol `a` of order
`m'` of propagation at most `ε` and an arbitrary symbol `b` of order `m`, the symbol of order
`m' + m` whose quantization is `Op(a) ∘ Op(b)`
(`TauCeti.Symbol.quantizeSchwartzValue_properSharp`). At every position `x` it is the composition
symbol `a # b'` of any localization `b'` of `b` that agrees with `b` on the ball of radius `ε`
about `x` (`TauCeti.Symbol.coefficient_properSharp_eq_sharp`). -/
def properSharp (a : Symbol n W U m') (ha : a.HasPropagationLE ε) (b : Symbol n V W m) :
    Symbol n V U (m' + m) :=
  ofEventuallyEq
    (fun p ↦ (a.sharp (localize ε p.1 b) (hasCompactSpatialSupport_localize ε p.1 b)).coefficient p)
    fun x ↦ ⟨a.sharp (localize (ε + 1) x b) (hasCompactSpatialSupport_localize (ε + 1) x b), by
      filter_upwards [ball_mem_nhds x one_pos] with y hy η
      refine ha.coefficient_sharp_congr _ _ (fun z hz ξ ↦ ?_) η
      rw [coefficient_localize_add_one hy hz, coefficient_localize_of_mem_ball hz]⟩

variable (ha : a.HasPropagationLE ε)
include ha

/-- **The composition symbol is computed by localizations.** At the position `x`, the
composition symbol of `a` and `b` is the composition symbol `a # b'` of any symbol `b'` with
compact spatial support that agrees with `b` on the ball of radius `ε` about `x`. -/
theorem coefficient_properSharp_eq_sharp {b : Symbol n V W m} {b' : Symbol n V W μ}
    (hb' : b'.HasCompactSpatialSupport) {x : CoordinateSpace n}
    (h : ∀ y ∈ ball x ε, ∀ ξ, b'.coefficient (y, ξ) = b.coefficient (y, ξ))
    (ξ : CoordinateSpace n) :
    (a.properSharp ha b).coefficient (x, ξ) = (a.sharp b' hb').coefficient (x, ξ) := by
  rw [properSharp, coefficient_ofEventuallyEq]
  refine ha.coefficient_sharp_congr _ hb' (fun y hy η ↦ ?_) ξ
  rw [h y hy, coefficient_localize_of_mem_ball hy]

/-- The composition symbol does not depend on the propagation bound of `a` used to build it. -/
theorem properSharp_congr {ε' : ℝ} (ha' : a.HasPropagationLE ε') {b : Symbol n V W m} :
    a.properSharp ha b = a.properSharp ha' b :=
  Symbol.ext <| funext fun ⟨x, ξ⟩ ↦ by
    have hb := hasCompactSpatialSupport_localize (max ε ε') x b
    rw [coefficient_properSharp_eq_sharp ha hb fun y hy ↦
        coefficient_localize_of_mem_ball (ball_subset_ball (le_max_left _ _) hy) b,
      coefficient_properSharp_eq_sharp ha' hb fun y hy ↦
        coefficient_localize_of_mem_ball (ball_subset_ball (le_max_right _ _) hy) b]

/-- For a right factor with compact spatial support, the composition symbol is `a # b`. -/
theorem properSharp_eq_sharp {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) :
    a.properSharp ha b = a.sharp b hb :=
  Symbol.ext <| funext fun ⟨_, ξ⟩ ↦ coefficient_properSharp_eq_sharp ha hb (fun _ _ _ ↦ rfl) ξ

/-- **Composition of quantizations.** `Op(a.properSharp ha b) u (x) = Op(a) w (x)` for every
Schwartz function `w` that agrees with `Op(b) u` on the ball of radius `ε` about `x`. -/
theorem quantizeSchwartzValue_properSharp (b : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    {x : CoordinateSpace n} {w : 𝓢(CoordinateSpace n, W)}
    (hw : ∀ y ∈ ball x ε, w y = quantizeSchwartzValue b.coefficient u y) :
    quantizeSchwartzValue (a.properSharp ha b).coefficient u x =
      quantizeSchwartzValue a.coefficient w x := by
  have hb := hasCompactSpatialSupport_localize ε x b
  rw [quantizeSchwartzValue_congr_left (coefficient_properSharp_eq_sharp ha hb
      fun y hy ↦ coefficient_localize_of_mem_ball hy b),
    quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  refine ha.quantizeSchwartzValue_congr fun y hy ↦ ?_
  rw [HasCompactSupport.toSchwartzMap_toFun, hw y hy]
  exact quantizeSchwartzValue_congr_left (coefficient_localize_of_mem_ball hy b) u

/-- **Composition of quantizations.** If `Op(b) u` has compact support, for instance when `u` has
compact support and `b` has finite propagation
(`TauCeti.Symbol.HasPropagationLE.hasCompactSupport_quantizeSchwartzValue`), then
`Op(a.properSharp ha b) u = Op(a) (Op(b) u)`. -/
theorem quantizeSchwartzValue_properSharp_of_hasCompactSupport (b : Symbol n V W m)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport (quantizeSchwartzValue b.coefficient u))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.properSharp ha b).coefficient u x =
      quantizeSchwartzValue a.coefficient (hu.toSchwartzMap (b.contDiff_quantizeSchwartzValue u))
        x :=
  quantizeSchwartzValue_properSharp ha b u fun y _ ↦ HasCompactSupport.toSchwartzMap_toFun _ _ y

/-- **Properly supported operators compose to properly supported operators.** If `a` has
propagation at most `ε` and `b` has propagation at most `ε'`, then their composition has
propagation at most `ε + ε'`. -/
theorem HasPropagationLE.properSharp {b : Symbol n V W m} {ε' : ℝ} (hb : b.HasPropagationLE ε') :
    (a.properSharp ha b).HasPropagationLE (ε + ε') := hasPropagationLE_iff.2 fun u x hu ↦ by
  rw [quantizeSchwartzValue_properSharp ha b u (w := 0) fun y hy ↦ ?_,
    quantizeSchwartzValue_zero_right]
  refine (hasPropagationLE_iff.1 hb u y fun z hz ↦ hu z (ball_subset_ball' ?_ hz)).symm
  linarith [mem_ball.1 hy]

/-- If `a` also has compact spatial support, then so does the composition symbol. -/
theorem HasCompactSpatialSupport.properSharp (ha' : a.HasCompactSpatialSupport)
    (b : Symbol n V W m) : (a.properSharp ha b).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha'
  refine hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ ↦ ?_⟩
  rw [Symbol.properSharp, coefficient_ofEventuallyEq]
  simp [hKa x hx]

/-! ### The composition expansion -/

/-- **The composition expansion.** The composition symbol is an asymptotic sum
`a.properSharp ha b ∼ ∑ₖ sharpTerm a b k` of the terms of the expansion, of orders `m' + m - k`:
for every `N`, the remainder `a.properSharp ha b - ∑_{k < N} sharpTerm a b k` is a symbol of
order `m' + m - N`. -/
theorem isAsymptoticSum_properSharp (b : Symbol n V W m) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) (inclusion (by simp) (a.properSharp ha b))
      (a.sharpTerm b) := by
  refine isAsymptoticSum_iff.2 fun N ↦ ⟨ofEventuallyEq ((a.properSharp ha b).coefficient -
    ∑ k ∈ range N, (a.sharpTerm b k).coefficient) fun x ↦ ?_, by
      rw [coefficient_ofEventuallyEq, coefficient_inclusion]⟩
  -- Near `x`, the right factor `b` agrees with its localization `b'` to a ball of radius
  -- `max (ε + 1) 1` about `x`, and the remainder is that of `a # b'`.
  have hb := hasCompactSpatialSupport_localize (ε + 1) x b
  refine ⟨a.sharpRemainder _ hb N, ?_⟩
  filter_upwards [ball_mem_nhds x one_pos] with y hy η
  rw [coefficient_sharpRemainder, Pi.sub_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_apply,
    coefficient_properSharp_eq_sharp ha hb (fun z hz ξ ↦ coefficient_localize_add_one hy hz b ξ)]
  -- The terms of the expansion at `y` only involve the derivatives of `b` at `y`.
  have hev : ∀ᶠ z in 𝓝 y, ∀ ξ, (localize (ε + 1) x b).coefficient (z, ξ) = b.coefficient (z, ξ) :=
    by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz ξ
    exact coefficient_localize ((mem_ball.1 hz).le.trans (le_max_right _ _)) b ξ
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact coefficient_sharpTerm_congr_of_eventually hev a k η

/-! ### Linearity -/

/-- At the position `x`, the composition symbol is computed by the localization of `b` to the ball
of radius `ε` about `x`. -/
private theorem coefficient_properSharp_eq_sharp_localize (b : Symbol n V W m)
    (x ξ : CoordinateSpace n) :
    (a.properSharp ha b).coefficient (x, ξ) =
      (a.sharp (localize ε x b) (hasCompactSpatialSupport_localize ε x b)).coefficient (x, ξ) :=
  coefficient_properSharp_eq_sharp ha _ (fun _ hy ↦ coefficient_localize_of_mem_ball hy b) ξ

theorem properSharp_add (b₁ b₂ : Symbol n V W m) :
    a.properSharp ha (b₁ + b₂) = a.properSharp ha b₁ + a.properSharp ha b₂ := by
  ext1
  funext ⟨x, ξ⟩
  have hb₁ := hasCompactSpatialSupport_localize ε x b₁
  have hb₂ := hasCompactSpatialSupport_localize ε x b₂
  rw [coefficient_properSharp_eq_sharp ha (hb₁.add hb₂) fun y hy η ↦ by
      simp [coefficient_localize_of_mem_ball hy], sharp_add a hb₁ hb₂]
  simp [coefficient_properSharp_eq_sharp_localize ha]

@[simp]
theorem properSharp_smul (b : Symbol n V W m) (c : ℂ) :
    a.properSharp ha (c • b) = c • a.properSharp ha b := by
  ext1
  funext ⟨x, ξ⟩
  have hb := hasCompactSpatialSupport_localize ε x b
  rw [coefficient_properSharp_eq_sharp ha (hb.smul c) fun y hy η ↦ by
      simp [coefficient_localize_of_mem_ball hy], sharp_smul a hb]
  simp [coefficient_properSharp_eq_sharp_localize ha]

@[simp]
theorem properSharp_zero : a.properSharp ha (0 : Symbol n V W m) = 0 := by
  simpa using properSharp_smul ha (0 : Symbol n V W m) 0

@[simp]
theorem properSharp_neg (b : Symbol n V W m) : a.properSharp ha (-b) = -a.properSharp ha b := by
  simpa using properSharp_smul ha b (-1)

theorem properSharp_sub (b₁ b₂ : Symbol n V W m) :
    a.properSharp ha (b₁ - b₂) = a.properSharp ha b₁ - a.properSharp ha b₂ := by
  rw [sub_eq_add_neg, properSharp_add, properSharp_neg, ← sub_eq_add_neg]

omit ha in
theorem add_properSharp {a₁ a₂ : Symbol n W U m'} (ha₁ : a₁.HasPropagationLE ε)
    (ha₂ : a₂.HasPropagationLE ε) (b : Symbol n V W m) :
    (a₁ + a₂).properSharp (ha₁.add ha₂) b = a₁.properSharp ha₁ b + a₂.properSharp ha₂ b := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_properSharp_eq_sharp_localize, add_sharp]

@[simp]
theorem smul_properSharp (c : ℂ) (b : Symbol n V W m) :
    (c • a).properSharp (ha.smul c) b = c • a.properSharp ha b := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_properSharp_eq_sharp_localize]

omit ha in
@[simp]
theorem zero_properSharp (b : Symbol n V W m) :
    (0 : Symbol n W U m').properSharp (hasPropagationLE_zero ε) b = 0 := by
  simpa using smul_properSharp (hasPropagationLE_zero ε) (0 : ℂ) b

@[simp]
theorem neg_properSharp (b : Symbol n V W m) :
    (-a).properSharp ha.neg b = -a.properSharp ha b := by
  simpa using smul_properSharp ha (-1 : ℂ) b

omit ha in
theorem sub_properSharp {a₁ a₂ : Symbol n W U m'} (ha₁ : a₁.HasPropagationLE ε)
    (ha₂ : a₂.HasPropagationLE ε) (b : Symbol n V W m) :
    (a₁ - a₂).properSharp (ha₁.sub ha₂) b = a₁.properSharp ha₁ b - a₂.properSharp ha₂ b := by
  simpa [sub_eq_add_neg, neg_properSharp ha₂] using add_properSharp ha₁ ha₂.neg b

end Symbol

/-! ### Classical symbols -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {m m' ε : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **Every classical pseudodifferential operator is properly supported up to a smoothing
operator**, within the classical symbols. For every `ε > 0`, every classical symbol `b` differs by a
smoothing symbol from a classical symbol `c` of propagation at most `ε`. The two have the same
homogeneous terms (`TauCeti.ClassicalSymbol.isSmoothing_toSymbol_sub_iff`). -/
theorem exists_isSmoothing_sub_and_hasPropagationLE [CompleteSpace V] [CompleteSpace W]
    (b : ClassicalSymbol n V W m) (hε : 0 < ε) :
    ∃ c : ClassicalSymbol n V W m,
      (c - b).toSymbol.IsSmoothing ∧ c.toSymbol.HasPropagationLE ε := by
  obtain ⟨c, hc, hcε⟩ := b.toSymbol.exists_isSmoothing_sub_and_hasPropagationLE hε
  refine ⟨b + ofIsSmoothing _ hc, ?_, ?_⟩
  · simpa [toSymbol_sub, toSymbol_add] using hc
  · simpa [toSymbol_add] using hcε

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]

/-- **The composition of classical symbols with a properly supported left factor is classical.**
For a classical symbol `a` of order `m'` of propagation at most `ε` and a classical symbol `b` of
order `m`, with no condition on the spatial support of `b`, the composition symbol
`a.toSymbol.properSharp ha b.toSymbol`, whose quantization is `Op(a) ∘ Op(b)`
(`TauCeti.Symbol.quantizeSchwartzValue_properSharp`), is a classical symbol of order `m' + m`. As
for `TauCeti.ClassicalSymbol.sharp`, its homogeneous terms are the formal composition
`sharpTerms a.term b.term` of the expansions of `a` and `b`. -/
def properSharp (a : ClassicalSymbol n W U m') (ha : a.toSymbol.HasPropagationLE ε)
    (b : ClassicalSymbol n V W m) : ClassicalSymbol n V U (m' + m) where
  toSymbol := a.toSymbol.properSharp ha b.toSymbol
  term := sharpTerms a.term b.term
  exists_remainder' := ⟨default, exists_remainder_sharpTerms_of_isAsymptoticSum a b
    (Symbol.isAsymptoticSum_properSharp ha b.toSymbol) default⟩

variable (a : ClassicalSymbol n W U m') (ha : a.toSymbol.HasPropagationLE ε)
  (b : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_properSharp :
    (a.properSharp ha b).toSymbol = a.toSymbol.properSharp ha b.toSymbol :=
  (rfl)

@[simp]
theorem term_properSharp (j : ℕ) : (a.properSharp ha b).term j = sharpTerms a.term b.term j :=
  (rfl)

/-- **The principal symbol of a composition** is the composition of the principal symbols. -/
@[simp]
theorem principal_properSharp :
    (a.properSharp ha b).principal = a.principal.comp b.principal := by
  ext1
  funext z
  simp

/-- The term of degree `m' + m - 1` of the composition of classical symbols with a properly
supported left factor is `a_{m'} ∘ b_{m-1} + a_{m'-1} ∘ b_m - i ∑ⱼ ∂_{ξⱼ} a_{m'} ∘ ∂_{xⱼ} b_m`. -/
theorem coefficient_term_one_properSharp (z : CoordinateSpace n × CoordinateSpace n) :
    ((a.properSharp ha b).term 1).coefficient z =
      (a.principal.coefficient z).comp ((b.term 1).coefficient z) +
        ((a.term 1).coefficient z).comp (b.principal.coefficient z) -
        Complex.I • ∑ j, ((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient
          z).comp ((b.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z) := by
  rw [term_properSharp, coefficient_sharpTerms_one, principal_def, principal_def]
  simp

/-- For a right factor with compact spatial support, the composition is `a # b`. -/
theorem properSharp_eq_sharp (hb : b.toSymbol.HasCompactSpatialSupport) :
    a.properSharp ha b = a.sharp b hb :=
  ext (by rw [toSymbol_properSharp, toSymbol_sharp, Symbol.properSharp_eq_sharp ha hb])

/-- The composition does not depend on the propagation bound of `a` used to build it. -/
theorem properSharp_congr {ε' : ℝ} (ha' : a.toSymbol.HasPropagationLE ε') :
    a.properSharp ha b = a.properSharp ha' b :=
  ext (Symbol.properSharp_congr ha ha')

@[simp]
theorem properSharp_zero : a.properSharp ha (0 : ClassicalSymbol n V W m) = 0 :=
  ext (by simp)

theorem properSharp_add (b₁ b₂ : ClassicalSymbol n V W m) :
    a.properSharp ha (b₁ + b₂) = a.properSharp ha b₁ + a.properSharp ha b₂ :=
  ext (by simp [Symbol.properSharp_add])

@[simp]
theorem properSharp_smul (c : ℂ) : a.properSharp ha (c • b) = c • a.properSharp ha b :=
  ext (by simp)

@[simp]
theorem properSharp_neg : a.properSharp ha (-b) = -a.properSharp ha b :=
  ext (by simp)

theorem properSharp_sub (b₁ b₂ : ClassicalSymbol n V W m) :
    a.properSharp ha (b₁ - b₂) = a.properSharp ha b₁ - a.properSharp ha b₂ :=
  ext (by simp [Symbol.properSharp_sub])

omit ha in
@[simp]
theorem zero_properSharp (ha : (0 : ClassicalSymbol n W U m').toSymbol.HasPropagationLE ε) :
    (0 : ClassicalSymbol n W U m').properSharp ha b = 0 :=
  ext (by simp)

omit ha in
theorem add_properSharp {a₁ a₂ : ClassicalSymbol n W U m'} (ha₁ : a₁.toSymbol.HasPropagationLE ε)
    (ha₂ : a₂.toSymbol.HasPropagationLE ε) (ha : (a₁ + a₂).toSymbol.HasPropagationLE ε) :
    (a₁ + a₂).properSharp ha b = a₁.properSharp ha₁ b + a₂.properSharp ha₂ b :=
  ext (by simp [Symbol.add_properSharp ha₁ ha₂])

theorem smul_properSharp (c : ℂ) (hca : (c • a).toSymbol.HasPropagationLE ε) :
    (c • a).properSharp hca b = c • a.properSharp ha b :=
  ext (by simp [Symbol.smul_properSharp ha])

theorem neg_properSharp (hna : (-a).toSymbol.HasPropagationLE ε) :
    (-a).properSharp hna b = -a.properSharp ha b :=
  ext (by simp [Symbol.neg_properSharp ha])

omit ha in
theorem sub_properSharp {a₁ a₂ : ClassicalSymbol n W U m'} (ha₁ : a₁.toSymbol.HasPropagationLE ε)
    (ha₂ : a₂.toSymbol.HasPropagationLE ε) (ha : (a₁ - a₂).toSymbol.HasPropagationLE ε) :
    (a₁ - a₂).properSharp ha b = a₁.properSharp ha₁ b - a₂.properSharp ha₂ b :=
  ext (by simp [Symbol.sub_properSharp ha₁ ha₂])

variable {a b} in
/-- **The composition of elliptic classical symbols is elliptic.** -/
theorem IsElliptic.properSharp (ha' : a.IsElliptic) (hb' : b.IsElliptic) :
    (a.properSharp ha b).IsElliptic := by
  rw [isElliptic_def, principal_properSharp]
  exact (isElliptic_def.1 ha').comp (isElliptic_def.1 hb')

end ClassicalSymbol

end TauCeti
