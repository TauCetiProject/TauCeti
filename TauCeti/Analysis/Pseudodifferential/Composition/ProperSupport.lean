/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
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
* `TauCeti.Symbol.properSharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero`: the expansion is exact,
  `a.properSharp ha b = ∑_{k < N} sharpTerm a b k`, when `a(x, ξ)` is a polynomial of degree less
  than `N` in `ξ`, as for the symbol of a differential operator.

Together with `TauCeti.Symbol.exists_isSmoothing_sub_and_hasPropagationLE`, which replaces every
symbol by one of finite propagation up to a smoothing symbol, this gives the composition calculus
of properly supported operators without any compact support condition on the symbols.

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

/-- The localization about `x` agrees with `b` near every point of the ball of radius `1` about
`x`. -/
private theorem eventually_coefficient_localize {r : ℝ} {x y : CoordinateSpace n}
    (hy : y ∈ ball x 1) (b : Symbol n V W m) :
    ∀ᶠ z in 𝓝 y, ∀ ξ, (localize r x b).coefficient (z, ξ) = b.coefficient (z, ξ) := by
  filter_upwards [isOpen_ball.mem_nhds hy] with z hz ξ
  exact coefficient_localize ((mem_ball.1 hz).le.trans (le_max_right _ _)) b ξ

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
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact coefficient_sharpTerm_congr_of_eventually (eventually_coefficient_localize hy b) a k η

/-- **Exact composition with a symbol polynomial in the frequency.** If the frequency derivatives
of `a` of order `N` vanish, so that `a(x, ξ)` is a polynomial of degree less than `N` in `ξ`, as
for the symbol of a differential operator of order less than `N`, then the composition expansion
is exact after `N` terms: `a.properSharp ha b = ∑_{k < N} sharpTerm a b k`, for every symbol `b`,
with no compact support condition on `b`. -/
theorem properSharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero {N : ℕ}
    (hpoly : ∀ β : List (Fin n), β.length = N → ∀ x ξ, mixedDeriv [] β a.coefficient x ξ = 0)
    (b : Symbol n V W m) :
    a.properSharp ha b =
      ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k) := by
  ext1
  funext ⟨x, ξ⟩
  -- At `x`, the composition is `a # b'` for the localization `b'` of `b` to a ball about `x`,
  -- whose expansion is exact; its terms at `x` only involve `b` near `x`.
  have hb := hasCompactSpatialSupport_localize (ε + 1) x b
  rw [coefficient_properSharp_eq_sharp ha hb (fun z hz ξ ↦
      coefficient_localize_add_one (mem_ball_self one_pos) hz b ξ),
    sharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero hpoly hb]
  simp only [coefficient_sum, coefficient_inclusion, Finset.sum_apply, coefficient_sharpTerm,
    mixedDeriv_congr_of_eventually (eventually_coefficient_localize (mem_ball_self one_pos) b)]

end Symbol

end TauCeti
