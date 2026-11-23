/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedDeriv.Indicator
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Complex.SectorBounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Weakly parameter-dependent symbols

The resolvent `(A - λ)⁻¹` of a classical elliptic operator `A` of order `d` is approximated by
pseudodifferential operators whose symbols depend holomorphically on the spectral parameter `λ`.
For second-order differential operators the strongly parameter-dependent class
`TauCeti.ParameterSymbol`, in which `λ` counts as two frequency orders, is available. For a general
classical operator it is not: the homogeneous terms of its symbol are only smooth away from
`ξ = 0`, so the resolvent symbol is not jointly smooth in `ξ` and the rescaled parameter at
`ξ = 0`. Grubb and Seeley replaced the joint estimates by a weaker condition, phrased in the
reciprocal parameter `r = 1 / λ`: the symbol must be holomorphic in `r`, and each derivative in `r`
may cost `d` frequency orders, uniformly as `r` ranges over a sector (including `r → 0`, that is
`λ → ∞`).

For an open set `R ⊆ ℂ` of reciprocal parameters, an anisotropy `d` and a frequency order `m`,
`TauCeti.WeakParameterSymbol n R V W d m` is the class of maps `a(x, ξ, r)` with values in
`V →L[ℂ] W`, infinitely complex differentiable (holomorphic) in `r ∈ R`, such that for every `j`
the `j`-th complex derivative `∂_r^j a(·, ·, r)` is a symbol of order `m + d j`, with estimates
uniform in `r ∈ R`:

`‖∂ₓ^α ∂_ξ^β ∂_r^j a(x, ξ, r)‖ ≤ C ⟨ξ⟩ ^ (m + d j - |β|)` for `x` in a compact set, all `ξ` and
all `r ∈ R`.

The symbol at the spectral parameter `λ` is `a(x, ξ, λ⁻¹)`. This is the class of parameter order
`0`; Grubb and Seeley obtain the classes of other parameter orders `δ` from it by multiplying with
`λ ^ δ`, which this file does not do.

## Main results

* `TauCeti.WeakParameterSymbol.toSymbol`, `TauCeti.WeakParameterSymbol.iteratedDerivSymbol`: the
  value at `r ∈ R` is a symbol of order `m`, and its `j`-th derivative in `r` one of order
  `m + d j`, both `ℂ`-linear in the weakly parameter-dependent symbol;
  `TauCeti.WeakParameterSymbol.bddAbove_seminorm_iteratedDerivSymbol` and
  `TauCeti.WeakParameterSymbol.exists_bound_iteratedDerivSymbol` say that the seminorms and the
  estimates on compact sets of the latter are bounded uniformly in `r`.
* `TauCeti.WeakParameterSymbol.inclusion`: the class grows with `m` and with `d`, and it is a
  complex vector space.
* `TauCeti.WeakParameterSymbol.ofSymbol`: a symbol independent of the parameter is weakly
  parameter-dependent for every anisotropy; its higher parameter derivatives vanish.
* `TauCeti.WeakParameterSymbol.ofIteratedDerivSymbol`,
  `TauCeti.WeakParameterSymbol.ofIteratedDerivSymbolOn`: conversely, a family holomorphic on `R`
  whose parameter derivatives are symbols of order `m + d j` with seminorms bounded uniformly in
  `r` is weakly parameter-dependent (the second extends a family on `R` by zero).
* `TauCeti.WeakParameterSymbol.ofParameter`: for `d ≥ 0`, an operator-valued function of the
  parameter alone, holomorphic with bounded derivatives on `R`, is a symbol of order `0`.
* `TauCeti.WeakParameterSymbol.comp`: the pointwise composition `b ∘ a` of symbols `b` of order
  `m'` and `a` of order `m` has order `m' + m`. Its parameter derivatives are given by Leibniz's
  rule in `r` (`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_comp`, from
  `ContinuousLinearMap.iteratedDeriv_of_bilinear` applied to `ContinuousLinearMap.compL`), each
  term `∂_r^i b ∘ ∂_r^(j - i) a` having order `m' + d i + m + d (j - i) = m' + m + d j`.
  Composition is bilinear, commutes with the order inclusions and is associative.
* `TauCeti.WeakParameterSymbol.shiftedLaplacianNormalizedResolvent`: on a sector
  `Re r ≤ c ‖r‖`, `c < 1`, of reciprocal parameters, the normalized resolvent symbol
  `(1 - r (1 + ‖ξ‖²))⁻¹` of `1 - Δ` has frequency order `0` and anisotropy `2`. Its `j`-th
  derivative in `r` is `j! (1 + ‖ξ‖²) ^ j (1 - r (1 + ‖ξ‖²)) ^ (-(j + 1))`
  (`TauCeti.WeakParameterSymbol.iteratedDeriv_coefficient_shiftedLaplacianNormalizedResolvent`).
  At the spectral parameter `λ` it is `-λ` times the resolvent symbol `((1 + ‖ξ‖²) - λ)⁻¹` of the
  strongly parameter-dependent calculus
  (`TauCeti.WeakParameterSymbol.coefficient_shiftedLaplacianNormalizedResolvent_inv_eq_neg_smul`).

## Implementation notes

The coefficient is set to `0` outside `R`, so a symbol is determined by its values on `R`
(`TauCeti.WeakParameterSymbol.ext_of_mem`). Holomorphy is stated as infinite complex
differentiability on the open set `R`, which is what the algebraic operations use; for complete
coefficient spaces it is equivalent to complex differentiability on `R`.

The order-zero estimates for `(1 - r (1 + ‖ξ‖²))⁻¹` are proved at one frequency `ξ` at a time.
With `t = ⟨ξ⟩`, the function `v ↦ 1 - r (1 + ‖ξ + t v‖²)` has derivatives at `0` bounded by a
multiple of `1 + ‖r‖ t²`, while on the sector its modulus is at least a multiple of that
quantity; the uniform estimate for reciprocals `TauCeti.exists_norm_iteratedFDeriv_inv_le_div`
then bounds the derivatives of its inverse at `0` independently of `r` and `ξ`. Undoing the dilation
by `t` gives the symbol estimates of order `0`.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
* G. Grubb and L. Hansen, *Complex powers of resolvents of pseudodifferential operators*,
  Comm. Partial Differential Equations 27 (2002), Definition 2.1.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology Nat

namespace TauCeti

variable (n : ℕ)

/-- The class of weakly parameter-dependent symbols of frequency order `m` and anisotropy `d` on
an open set `R` of reciprocal spectral parameters `r = 1 / λ`: maps `a(x, ξ, r)` with values in
`V →L[ℂ] W`, infinitely complex differentiable in `r ∈ R` and set to `0` for `r ∉ R`, such that
for every `j` the `j`-th complex derivative in `r` is smooth in `(x, ξ)` and satisfies, on every
compact set `K` of positions, the symbol estimates of order `m + d j` uniformly in `r ∈ R`:
`‖∂ₓ^α ∂_ξ^β ∂_r^j a(x, ξ, r)‖ ≤ C ⟨ξ⟩ ^ (m + d j - |β|)` for `x ∈ K`, all `ξ` and all `r ∈ R`. -/
@[ext]
structure WeakParameterSymbol (R : TopologicalSpace.Opens ℂ) (V W : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (d m : ℝ) where
  /-- The coefficient `a(x, ξ, r)` at the position `x`, the frequency `ξ` and the reciprocal
  spectral parameter `r`, set to `0` for `r ∉ R`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W
  contDiffOn_coefficient : ∀ p, ContDiffOn ℂ ∞ (coefficient p) R
  coefficient_of_notMem : ∀ p, ∀ r ∉ R, coefficient p r = 0
  contDiff_iteratedDeriv : ∀ j : ℕ, ∀ r ∈ R,
    ContDiff ℝ ∞ fun p => iteratedDeriv j (coefficient p) r
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ (j : ℕ) (α β : List (Fin n)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R,
      ‖mixedDeriv α β (fun p => iteratedDeriv j (coefficient p) r) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m + d * j - β.length) / 2)

namespace WeakParameterSymbol

variable {n} {R : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {d d' m m' : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : WeakParameterSymbol n R V W d m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => WeakParameterSymbol.ext h

/-- A weakly parameter-dependent symbol is determined by its values at parameters in `R`. -/
theorem ext_of_mem {a b : WeakParameterSymbol n R V W d m}
    (h : ∀ p, ∀ r ∈ R, a.coefficient p r = b.coefficient p r) : a = b := by
  ext1
  funext p r
  by_cases hr : r ∈ R
  · exact h p r hr
  · rw [a.coefficient_of_notMem p r hr, b.coefficient_of_notMem p r hr]

/-- The coefficient is infinitely complex differentiable in the parameter at every point of `R`. -/
theorem contDiffAt_coefficient (a : WeakParameterSymbol n R V W d m) (p) {r : ℂ} (hr : r ∈ R)
    {N : ℕ} : ContDiffAt ℂ N (a.coefficient p) r :=
  ((a.contDiffOn_coefficient p).contDiffAt (R.isOpen.mem_nhds hr)).of_le (mod_cast le_top)

/-- The coefficient is holomorphic in the parameter on `R`. -/
theorem differentiableOn_coefficient (a : WeakParameterSymbol n R V W d m) (p) :
    DifferentiableOn ℂ (a.coefficient p) R :=
  (a.contDiffOn_coefficient p).differentiableOn (by simp)

/-- At every parameter `r ∈ R`, the coefficient is smooth in the point `(x, ξ)`. -/
theorem contDiff_coefficient_apply (a : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) :
    ContDiff ℝ ∞ fun p ↦ a.coefficient p r := by
  simpa using a.contDiff_iteratedDeriv 0 r hr

section Module

instance : Zero (WeakParameterSymbol n R V W d m) where
  zero :=
    { coefficient := 0
      contDiffOn_coefficient := fun _ => contDiffOn_const
      coefficient_of_notMem := fun _ _ _ => rfl
      contDiff_iteratedDeriv := fun j _ _ => by
        simpa [iteratedDeriv_const] using contDiff_const (c := (0 : V →L[ℂ] W))
      exists_bound := fun _ _ j α β => ⟨0, le_rfl, fun x _ ξ r _ => by
        simp only [Pi.zero_apply, iteratedDeriv_const_zero, zero_mul, norm_le_zero_iff]
        exact mixedDeriv_zero (A := V →L[ℂ] W) α β x ξ⟩ }

instance : Add (WeakParameterSymbol n R V W d m) where
  add a b :=
    { coefficient := fun p r => a.coefficient p r + b.coefficient p r
      contDiffOn_coefficient := fun p =>
        (a.contDiffOn_coefficient p).add (b.contDiffOn_coefficient p)
      coefficient_of_notMem := fun p r hr => by
        rw [a.coefficient_of_notMem p r hr, b.coefficient_of_notMem p r hr, add_zero]
      contDiff_iteratedDeriv := fun j r hr => by
        simp only [iteratedDeriv_fun_add (a.contDiffAt_coefficient _ hr)
          (b.contDiffAt_coefficient _ hr)]
        exact (a.contDiff_iteratedDeriv j r hr).add (b.contDiff_iteratedDeriv j r hr)
      exists_bound := fun K hK j α β => by
        obtain ⟨C, hC, hCb⟩ := a.exists_bound K hK j α β
        obtain ⟨D, hD, hDb⟩ := b.exists_bound K hK j α β
        refine ⟨C + D, add_nonneg hC hD, fun x hx ξ r hr => ?_⟩
        have hfun : (fun p => iteratedDeriv j (fun r => a.coefficient p r + b.coefficient p r) r) =
            (fun p => iteratedDeriv j (a.coefficient p) r) +
              fun p => iteratedDeriv j (b.coefficient p) r := by
          funext p
          exact iteratedDeriv_fun_add (a.contDiffAt_coefficient _ hr)
            (b.contDiffAt_coefficient _ hr)
        rw [hfun]
        exact norm_mixedDeriv_add_le (a.contDiff_iteratedDeriv j r hr)
          (b.contDiff_iteratedDeriv j r hr) (hCb x hx ξ r hr) (hDb x hx ξ r hr) }

instance : SMul ℂ (WeakParameterSymbol n R V W d m) where
  smul c a :=
    { coefficient := fun p r => c • a.coefficient p r
      contDiffOn_coefficient := fun p => (a.contDiffOn_coefficient p).const_smul c
      coefficient_of_notMem := fun p r hr => by rw [a.coefficient_of_notMem p r hr, smul_zero]
      contDiff_iteratedDeriv := fun j r hr => by
        simp only [iteratedDeriv_fun_const_smul (a.contDiffAt_coefficient _ hr)]
        exact (a.contDiff_iteratedDeriv j r hr).const_smul c
      exists_bound := fun K hK j α β => by
        obtain ⟨C, hC, hCb⟩ := a.exists_bound K hK j α β
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x hx ξ r hr => ?_⟩
        have hfun : (fun p => iteratedDeriv j (fun r => c • a.coefficient p r) r) =
            c • fun p => iteratedDeriv j (a.coefficient p) r := by
          funext p
          exact iteratedDeriv_fun_const_smul (a.contDiffAt_coefficient _ hr) c
        rw [hfun]
        exact norm_mixedDeriv_smul_le c (hCb x hx ξ r hr) }

instance : Neg (WeakParameterSymbol n R V W d m) where
  neg a := (-1 : ℂ) • a

instance : Sub (WeakParameterSymbol n R V W d m) where
  sub a b := a + -b

instance : SMul ℕ (WeakParameterSymbol n R V W d m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (WeakParameterSymbol n R V W d m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : WeakParameterSymbol n R V W d m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : WeakParameterSymbol n R V W d m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : WeakParameterSymbol n R V W d m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : WeakParameterSymbol n R V W d m) :
    (-a).coefficient = -a.coefficient :=
  neg_one_smul ℂ a.coefficient

@[simp]
theorem coefficient_sub (a b : WeakParameterSymbol n R V W d m) :
    (a - b).coefficient = a.coefficient - b.coefficient := by
  rw [sub_eq_add_neg a.coefficient]
  exact congrArg (a.coefficient + ·) (coefficient_neg b)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : WeakParameterSymbol n R V W d m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : WeakParameterSymbol n R V W d m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (WeakParameterSymbol n R V W d m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (WeakParameterSymbol n R V W d m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

@[simp]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (a : ι → WeakParameterSymbol n R V W d m) :
    (∑ i ∈ s, a i).coefficient = ∑ i ∈ s, (a i).coefficient :=
  map_sum (⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩ :
    WeakParameterSymbol n R V W d m →+ _) a s

end Module

/-! ### Values and parameter derivatives as ordinary symbols -/

/-- The `j`-th derivative in the parameter at `r ∈ R`, a symbol of order `m + d j`. -/
def iteratedDerivSymbol (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    Symbol n V W (m + d * j) where
  coefficient p := iteratedDeriv j (a.coefficient p) r
  contDiff_coefficient := a.contDiff_iteratedDeriv j r hr
  exists_bound K hK α β :=
    (a.exists_bound K hK j α β).imp fun _ hC => ⟨hC.1, fun x hx ξ => hC.2 x hx ξ r hr⟩

@[simp]
theorem coefficient_iteratedDerivSymbol (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.iteratedDerivSymbol j hr).coefficient p = iteratedDeriv j (a.coefficient p) r := (rfl)

@[simp]
theorem iteratedDerivSymbol_zero (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (0 : WeakParameterSymbol n R V W d m).iteratedDerivSymbol j hr = 0 :=
  Symbol.ext (funext fun _ => iteratedDeriv_const_zero)

@[simp]
theorem iteratedDerivSymbol_add (a b : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) :
    (a + b).iteratedDerivSymbol j hr = a.iteratedDerivSymbol j hr + b.iteratedDerivSymbol j hr :=
  Symbol.ext (funext fun _ => iteratedDeriv_fun_add (a.contDiffAt_coefficient _ hr)
    (b.contDiffAt_coefficient _ hr))

@[simp]
theorem iteratedDerivSymbol_smul (c : ℂ) (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) : (c • a).iteratedDerivSymbol j hr = c • a.iteratedDerivSymbol j hr :=
  Symbol.ext (funext fun _ => iteratedDeriv_fun_const_smul (a.contDiffAt_coefficient _ hr) c)

@[simp]
theorem iteratedDerivSymbol_neg (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) : (-a).iteratedDerivSymbol j hr = -a.iteratedDerivSymbol j hr := by
  rw [← neg_one_smul ℂ a, iteratedDerivSymbol_smul, neg_one_smul]

@[simp]
theorem iteratedDerivSymbol_sub (a b : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) :
    (a - b).iteratedDerivSymbol j hr = a.iteratedDerivSymbol j hr - b.iteratedDerivSymbol j hr := by
  rw [sub_eq_add_neg, iteratedDerivSymbol_add, iteratedDerivSymbol_neg, ← sub_eq_add_neg]

/-- The value at `r ∈ R`, a symbol of order `m`. -/
def toSymbol (a : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) : Symbol n V W m where
  coefficient p := a.coefficient p r
  contDiff_coefficient := a.contDiff_coefficient_apply hr
  exists_bound K hK α β := (a.exists_bound K hK 0 α β).imp fun _ hC =>
    ⟨hC.1, fun x hx ξ => by simpa using hC.2 x hx ξ r hr⟩

@[simp]
theorem coefficient_toSymbol (a : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.toSymbol hr).coefficient p = a.coefficient p r := (rfl)

@[simp]
theorem toSymbol_zero {r : ℂ} (hr : r ∈ R) :
    (0 : WeakParameterSymbol n R V W d m).toSymbol hr = 0 := (rfl)

@[simp]
theorem toSymbol_add (a b : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) :
    (a + b).toSymbol hr = a.toSymbol hr + b.toSymbol hr := (rfl)

@[simp]
theorem toSymbol_smul (c : ℂ) (a : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) :
    (c • a).toSymbol hr = c • a.toSymbol hr := (rfl)

@[simp]
theorem toSymbol_neg (a : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) :
    (-a).toSymbol hr = -a.toSymbol hr := by
  rw [← neg_one_smul ℂ a, toSymbol_smul, neg_one_smul]

@[simp]
theorem toSymbol_sub (a b : WeakParameterSymbol n R V W d m) {r : ℂ} (hr : r ∈ R) :
    (a - b).toSymbol hr = a.toSymbol hr - b.toSymbol hr := by
  rw [sub_eq_add_neg, toSymbol_add, toSymbol_neg, ← sub_eq_add_neg]

@[simp]
theorem iteratedDerivSymbol_sum {ι : Type*} (s : Finset ι)
    (a : ι → WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (∑ i ∈ s, a i).iteratedDerivSymbol j hr = ∑ i ∈ s, (a i).iteratedDerivSymbol j hr :=
  map_sum (⟨⟨fun a ↦ a.iteratedDerivSymbol j hr, iteratedDerivSymbol_zero j hr⟩,
    fun a b ↦ iteratedDerivSymbol_add a b j hr⟩ : WeakParameterSymbol n R V W d m →+ _) a s

@[simp]
theorem toSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → WeakParameterSymbol n R V W d m)
    {r : ℂ} (hr : r ∈ R) : (∑ i ∈ s, a i).toSymbol hr = ∑ i ∈ s, (a i).toSymbol hr :=
  map_sum (⟨⟨fun a ↦ a.toSymbol hr, toSymbol_zero hr⟩, fun a b ↦ toSymbol_add a b hr⟩ :
    WeakParameterSymbol n R V W d m →+ _) a s

/-- **Uniform estimates.** Every seminorm of the `j`-th parameter derivative is bounded uniformly
in the parameter `r ∈ R`. -/
theorem bddAbove_seminorm_iteratedDerivSymbol (a : WeakParameterSymbol n R V W d m) (j : ℕ)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    BddAbove (range fun r : R => Symbol.seminorm K α β (a.iteratedDerivSymbol j r.property)) := by
  obtain ⟨C, hC, hCb⟩ := a.exists_bound K K.isCompact j α β
  refine ⟨C, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact Symbol.seminorm_le_bound K α β _ hC fun x hx ξ => hCb x hx ξ r r.property

/-- **Uniform estimates on compact sets.** The `j`-th parameter derivatives
`∂_r^j a(·, ·, r)`, `r ∈ R`, form a family of symbols of order `m + d j` whose estimates on a
compact set `K` of positions hold with constants independent of `r`. -/
theorem exists_bound_iteratedDerivSymbol (a : WeakParameterSymbol n R V W d m) (j : ℕ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ r : R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (a.iteratedDerivSymbol j r.property).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m + d * j - β.length) / 2) :=
  (a.exists_bound K hK j α β).imp fun _ hC => ⟨hC.1, fun r x hx ξ => by
    simpa only [← funext (coefficient_iteratedDerivSymbol a j r.property)] using
      hC.2 x hx ξ r r.property⟩

/-- **Uniform estimates for the values.** Every seminorm of the value at `r` is bounded uniformly
in the parameter `r ∈ R`. -/
theorem bddAbove_seminorm_toSymbol (a : WeakParameterSymbol n R V W d m)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    BddAbove (range fun r : R => Symbol.seminorm K α β (a.toSymbol r.property)) := by
  obtain ⟨C, hC, hCb⟩ := a.exists_bound K K.isCompact 0 α β
  refine ⟨C, ?_⟩
  rintro _ ⟨r, rfl⟩
  have hcoef : (a.toSymbol r.property).coefficient = fun p => a.coefficient p r := rfl
  exact Symbol.seminorm_le_bound K α β _ hC fun x hx ξ => by
    simpa [hcoef] using hCb x hx ξ r r.property

/-! ### Order inclusions -/

/-- A weakly parameter-dependent symbol of frequency order `m` and anisotropy `d` has every
frequency order `m' ≥ m` and every anisotropy `d' ≥ d`, since the parameter derivatives have
nonnegative order. -/
def inclusion (hm : m ≤ m') (hd : d ≤ d') :
    WeakParameterSymbol n R V W d m →ₗ[ℂ] WeakParameterSymbol n R V W d' m' where
  toFun a :=
    { coefficient := a.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient
      coefficient_of_notMem := a.coefficient_of_notMem
      contDiff_iteratedDeriv := a.contDiff_iteratedDeriv
      exists_bound := fun K hK j α β =>
        (a.exists_bound K hK j α β).imp fun C hC => ⟨hC.1, fun x hx ξ r hr =>
          (hC.2 x hx ξ r hr).trans (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ
            (by nlinarith [mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (α := ℝ) j)])) hC.1)⟩ }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_inclusion (hm : m ≤ m') (hd : d ≤ d') (a : WeakParameterSymbol n R V W d m) :
    (inclusion hm hd a).coefficient = a.coefficient := (rfl)

@[simp]
theorem toSymbol_inclusion (hm : m ≤ m') (hd : d ≤ d') (a : WeakParameterSymbol n R V W d m)
    {r : ℂ} (hr : r ∈ R) : (inclusion hm hd a).toSymbol hr = Symbol.inclusion hm (a.toSymbol hr) :=
  Symbol.ext (Symbol.coefficient_inclusion hm (a.toSymbol hr)).symm

@[simp]
theorem iteratedDerivSymbol_inclusion (hm : m ≤ m') (hd : d ≤ d')
    (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (inclusion hm hd a).iteratedDerivSymbol j hr =
      Symbol.inclusion (add_le_add hm (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg j)))
        (a.iteratedDerivSymbol j hr) :=
  Symbol.ext (Symbol.coefficient_inclusion _ (a.iteratedDerivSymbol j hr)).symm

theorem inclusion_injective (hm : m ≤ m') (hd : d ≤ d') :
    Function.Injective (inclusion (n := n) (R := R) (V := V) (W := W) hm hd) :=
  fun _ _ hab => WeakParameterSymbol.ext (by simpa using congrArg coefficient hab)

/-! ### Parameter-independent symbols -/

/-- A symbol `b` of order `m` that does not depend on the parameter is weakly parameter-dependent
of frequency order `m`, for every anisotropy `d`: its parameter derivatives vanish. -/
def ofSymbol (b : Symbol n V W m) : WeakParameterSymbol n R V W d m where
  coefficient p := (R : Set ℂ).indicator fun _ => b.coefficient p
  contDiffOn_coefficient p :=
    (contDiffOn_const (c := b.coefficient p)).congr fun _ hr => indicator_of_mem hr _
  coefficient_of_notMem p r hr := indicator_of_notMem hr _
  contDiff_iteratedDeriv j r hr := by
    simp only [iteratedDeriv_indicator_of_mem R.isOpen hr, iteratedDeriv_const]
    split_ifs
    · exact b.contDiff_coefficient
    · exact contDiff_const
  exists_bound K hK j α β := by
    rcases eq_or_ne j 0 with rfl | hj
    · obtain ⟨C, hC, hCb⟩ := b.exists_bound K hK α β
      exact ⟨C, hC, fun x hx ξ r hr => by
        simpa [iteratedDeriv_indicator_of_mem R.isOpen hr] using hCb x hx ξ⟩
    · exact ⟨0, le_rfl, fun x _ ξ r hr => by
        simp only [iteratedDeriv_indicator_of_mem R.isOpen hr, iteratedDeriv_const, hj, ↓reduceIte,
          zero_mul, norm_le_zero_iff]
        exact mixedDeriv_zero (A := V →L[ℂ] W) α β x ξ⟩

@[simp]
theorem coefficient_ofSymbol (b : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n)
    {r : ℂ} (hr : r ∈ R) :
    (ofSymbol b : WeakParameterSymbol n R V W d m).coefficient p r = b.coefficient p :=
  indicator_of_mem (s := (R : Set ℂ)) hr fun _ => b.coefficient p

@[simp]
theorem toSymbol_ofSymbol (b : Symbol n V W m) {r : ℂ} (hr : r ∈ R) :
    (ofSymbol b : WeakParameterSymbol n R V W d m).toSymbol hr = b :=
  Symbol.ext (funext fun p => coefficient_ofSymbol (d := d) b p hr)

@[simp]
theorem iteratedDerivSymbol_ofSymbol_zero (b : Symbol n V W m) {r : ℂ} (hr : r ∈ R) :
    (ofSymbol b : WeakParameterSymbol n R V W d m).iteratedDerivSymbol 0 hr =
      Symbol.inclusion (by simp) b :=
  Symbol.ext (funext fun p => by simp [hr])

/-- The parameter derivatives of a parameter-independent symbol vanish. -/
@[simp]
theorem iteratedDerivSymbol_ofSymbol_succ (b : Symbol n V W m) (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (ofSymbol b : WeakParameterSymbol n R V W d m).iteratedDerivSymbol (j + 1) hr = 0 :=
  Symbol.ext (funext fun p => by
    simp [ofSymbol, iteratedDeriv_indicator_of_mem R.isOpen hr, iteratedDeriv_const])

/-! ### Symbols from their parameter derivatives -/

section OfIteratedDerivSymbol

variable (b : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W)
  (hb : ∀ p, ContDiffOn ℂ ∞ (b p) R) (hb₀ : ∀ p, ∀ r ∉ R, b p r = 0)
  (s : (j : ℕ) → (r : ℂ) → r ∈ R → Symbol n V W (m + d * j))
  (hs : ∀ j r (hr : r ∈ R) p, (s j r hr).coefficient p = iteratedDeriv j (b p) r)
  (hbound : ∀ (j : ℕ) (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)),
    ∃ C, ∀ r (hr : r ∈ R), Symbol.seminorm K α β (s j r hr) ≤ C)

/-- A family `b`, holomorphic in the parameter on `R` and vanishing outside `R`, whose derivatives
`∂_r^j b(·, ·, r)` are the coefficients of symbols `s j r` of order `m + d j` with seminorms bounded
uniformly in `r ∈ R`, is a weakly parameter-dependent symbol. -/
def ofIteratedDerivSymbol : WeakParameterSymbol n R V W d m where
  coefficient := b
  contDiffOn_coefficient := hb
  coefficient_of_notMem := hb₀
  contDiff_iteratedDeriv j r hr := by
    rw [show (fun p ↦ iteratedDeriv j (b p) r) = (s j r hr).coefficient from
      funext fun p ↦ (hs j r hr p).symm]
    exact (s j r hr).contDiff_coefficient
  exists_bound K hK j α β := by
    obtain ⟨C, hC⟩ := hbound j ⟨K, hK⟩ α β
    refine ⟨max C 0, le_max_right C 0, fun x hx ξ r hr ↦ ?_⟩
    have h := Symbol.le_seminorm ⟨K, hK⟩ α β (s j r hr) hx ξ
    simp only [funext (hs j r hr)] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((hC r hr).trans (le_max_left C 0))
      (rpow_weight_pos ξ _).le)

@[simp]
theorem coefficient_ofIteratedDerivSymbol :
    (ofIteratedDerivSymbol b hb hb₀ s hs hbound).coefficient = b := (rfl)

@[simp]
theorem iteratedDerivSymbol_ofIteratedDerivSymbol (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (ofIteratedDerivSymbol b hb hb₀ s hs hbound).iteratedDerivSymbol j hr = s j r hr :=
  Symbol.ext (funext fun p ↦ (hs j r hr p).symm)

end OfIteratedDerivSymbol

section OfIteratedDerivSymbolOn

variable (g : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W)
  (hg : ∀ p, ContDiffOn ℂ ∞ (g p) R)
  (s : (j : ℕ) → (r : ℂ) → r ∈ R → Symbol n V W (m + d * j))
  (hs : ∀ j r (hr : r ∈ R) p, (s j r hr).coefficient p = iteratedDeriv j (g p) r)
  (hbound : ∀ (j : ℕ) (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)),
    ∃ C, ∀ r (hr : r ∈ R), Symbol.seminorm K α β (s j r hr) ≤ C)

/-- A family `g`, holomorphic in the parameter on `R`, whose derivatives `∂_r^j g(·, ·, r)` are
the coefficients of symbols `s j r` of order `m + d j` with seminorms bounded uniformly in `r ∈ R`,
gives a weakly parameter-dependent symbol, equal to `g` on `R` and extended by zero outside `R`.
Unlike `TauCeti.WeakParameterSymbol.ofIteratedDerivSymbol`, `g` need not vanish outside `R`. -/
def ofIteratedDerivSymbolOn : WeakParameterSymbol n R V W d m :=
  ofIteratedDerivSymbol (fun p ↦ (R : Set ℂ).indicator (g p))
    (fun p ↦ (hg p).congr fun _ hr ↦ indicator_of_mem hr _)
    (fun _ _ hr ↦ indicator_of_notMem hr _) s
    (fun j r hr p ↦ by rw [hs, iteratedDeriv_indicator_of_mem R.isOpen hr])
    hbound

@[simp]
theorem coefficient_ofIteratedDerivSymbolOn (p : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) : (ofIteratedDerivSymbolOn g hg s hs hbound).coefficient p r = g p r :=
  indicator_of_mem hr _

@[simp]
theorem iteratedDerivSymbol_ofIteratedDerivSymbolOn (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (ofIteratedDerivSymbolOn g hg s hs hbound).iteratedDerivSymbol j hr = s j r hr :=
  iteratedDerivSymbol_ofIteratedDerivSymbol ..

end OfIteratedDerivSymbolOn

/-! ### Functions of the parameter alone -/

section OfParameter

/-- A function `g` of the parameter alone, holomorphic on `R` with every derivative bounded on
`R`, as a weakly parameter-dependent symbol of frequency order `0`, for an anisotropy `d ≥ 0`:
its coefficient is `g(r)` for every position and frequency. Its parameter derivatives are the
constant symbols `∂_r^j g(r)` of order `0 ≤ d j`. -/
def ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W) (hg : ContDiffOn ℂ ∞ g R)
    (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C) :
    WeakParameterSymbol n R V W d 0 :=
  ofIteratedDerivSymbolOn (fun _ ↦ g) (fun _ ↦ hg)
    (fun j r _ ↦ Symbol.inclusion (by positivity) (Symbol.const (iteratedDeriv j g r)))
    (fun j r _ p ↦ by simp)
    (fun j K α β ↦ (hbound j).imp fun _ hC r hr ↦ (Symbol.seminorm_inclusion_le _ K α β _).trans
      ((Symbol.seminorm_const_le K α β _).trans (hC r hr)))

@[simp]
theorem coefficient_ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W) (hg : ContDiffOn ℂ ∞ g R)
    (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C)
    (p : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    (ofParameter hd g hg hbound).coefficient p r = g r :=
  coefficient_ofIteratedDerivSymbolOn _ _ _ _ _ p hr

@[simp]
theorem iteratedDerivSymbol_ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W)
    (hg : ContDiffOn ℂ ∞ g R) (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C) (j : ℕ)
    {r : ℂ} (hr : r ∈ R) :
    (ofParameter (n := n) hd g hg hbound).iteratedDerivSymbol j hr =
      Symbol.inclusion (by positivity) (Symbol.const (iteratedDeriv j g r)) :=
  iteratedDerivSymbol_ofIteratedDerivSymbolOn ..

end OfParameter

/-! ### Composition -/

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- For `i ≤ j`, `m' + d i + (m + d (j - i)) = m' + m + d j`: the order of the term
`∂_r^i b ∘ ∂_r^(j - i) a` of Leibniz's rule is `m' + m + d j`. -/
theorem add_mul_add_add_mul_sub_eq {j : ℕ} (i : Fin (j + 1)) :
    m' + d * i + (m + d * ↑(j - i : ℕ)) = m' + m + d * j := by
  rw [Nat.cast_sub i.is_le]
  ring

/-- Every seminorm of the parameter derivatives is bounded uniformly in `r ∈ R`, in the form used
by `TauCeti.Symbol.exists_seminorm_comp_le`. -/
private theorem exists_seminorm_iteratedDerivSymbol_le (a : WeakParameterSymbol n R V W d m)
    (j : ℕ) (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ C, ∀ r : R, Symbol.seminorm K α β (a.iteratedDerivSymbol j r.property) ≤ C := by
  obtain ⟨C, hC⟩ := a.bddAbove_seminorm_iteratedDerivSymbol j K α β
  exact ⟨C, fun r ↦ hC ⟨r, rfl⟩⟩

/-- **Composition.** The pointwise composition `(x, ξ, r) ↦ b(x, ξ, r) ∘ a(x, ξ, r)` of weakly
parameter-dependent symbols `b` of frequency order `m'` and `a` of frequency order `m` has
frequency order `m' + m`. By Leibniz's rule in `r`
(`ContinuousLinearMap.iteratedDeriv_of_bilinear`,
`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_comp`) its `j`-th parameter derivative is a sum
of the compositions `∂_r^i b ∘ ∂_r^(j - i) a`, each of order
`m' + d i + m + d (j - i) = m' + m + d j`. -/
def comp (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    WeakParameterSymbol n R V U d (m' + m) :=
  ofIteratedDerivSymbol (fun p r ↦ (b.coefficient p r).comp (a.coefficient p r))
    (fun p ↦ (b.contDiffOn_coefficient p).clm_comp (a.contDiffOn_coefficient p))
    (fun p r hr ↦ by simp [b.coefficient_of_notMem p r hr])
    (fun j r hr ↦ ∑ i : Fin (j + 1),
      (j.choose i : ℂ) •
        Symbol.inclusion (add_mul_add_add_mul_sub_eq i).le
          ((b.iteratedDerivSymbol i hr).comp (a.iteratedDerivSymbol (j - i) hr)))
    (fun j r hr p ↦ by
      have hL := (ContinuousLinearMap.compL ℂ V W U).iteratedDeriv_of_bilinear
        (b.contDiffAt_coefficient p hr) (a.contDiffAt_coefficient p hr) (n := j)
      simp only [ContinuousLinearMap.compL_apply] at hL
      rw [hL, Symbol.coefficient_sum, Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun i ↦ j.choose i •
          (iteratedDeriv i (b.coefficient p) r).comp (iteratedDeriv (j - i) (a.coefficient p) r))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [Nat.cast_smul_eq_nsmul])
    (fun j K α β ↦ by
      choose C hC using fun i : Fin (j + 1) ↦ Symbol.exists_seminorm_comp_le K
        (b := fun r : R ↦ b.iteratedDerivSymbol i r.property)
        (a := fun r : R ↦ a.iteratedDerivSymbol (j - i) r.property)
        (b.exists_seminorm_iteratedDerivSymbol_le i K)
        (a.exists_seminorm_iteratedDerivSymbol_le (j - i) K) α β
      refine ⟨∑ i : Fin (j + 1), ‖(j.choose i : ℂ)‖ * C i, fun r hr ↦ ?_⟩
      refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
        (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left
        ((Symbol.seminorm_inclusion_le _ K α β _).trans (hC i ⟨r, hr⟩)) (norm_nonneg _))

@[simp]
theorem coefficient_comp (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (b.comp a).coefficient p r = (b.coefficient p r).comp (a.coefficient p r) := (rfl)

/-- The value of a composition at a parameter is the composition of the values. -/
@[simp]
theorem toSymbol_comp (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m)
    {r : ℂ} (hr : r ∈ R) : (b.comp a).toSymbol hr = (b.toSymbol hr).comp (a.toSymbol hr) :=
  Symbol.ext (funext fun _ ↦ by simp)

/-- **Leibniz's rule for the parameter derivatives of a composition**, as symbols: the `j`-th
parameter derivative of `b ∘ a` is the sum of the compositions
`(j choose i) ∂_r^i b ∘ ∂_r^(j - i) a`, each of order `m' + m + d j`. -/
@[simp]
theorem iteratedDerivSymbol_comp (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (b.comp a).iteratedDerivSymbol j hr = ∑ i : Fin (j + 1), (j.choose i : ℂ) •
      Symbol.inclusion (add_mul_add_add_mul_sub_eq i).le
        ((b.iteratedDerivSymbol i hr).comp (a.iteratedDerivSymbol (j - i) hr)) :=
  iteratedDerivSymbol_ofIteratedDerivSymbol ..

theorem comp_add (b : WeakParameterSymbol n R W U d m') (a₁ a₂ : WeakParameterSymbol n R V W d m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ := by
  ext p r
  simp

theorem add_comp (b₁ b₂ : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a := by
  ext p r
  simp

@[simp]
theorem comp_smul (c : ℂ) (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) : b.comp (c • a) = c • b.comp a := by
  ext p r
  simp

@[simp]
theorem smul_comp (c : ℂ) (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) : (c • b).comp a = c • b.comp a := by
  ext p r
  simp

@[simp]
theorem comp_zero (b : WeakParameterSymbol n R W U d m') :
    b.comp (0 : WeakParameterSymbol n R V W d m) = 0 := by
  ext p r
  simp

@[simp]
theorem zero_comp (a : WeakParameterSymbol n R V W d m) :
    (0 : WeakParameterSymbol n R W U d m').comp a = 0 := by
  ext p r
  simp

@[simp]
theorem comp_neg (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    b.comp (-a) = -b.comp a := by
  ext p r
  simp

@[simp]
theorem neg_comp (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    (-b).comp a = -b.comp a := by
  ext p r
  simp

theorem comp_sub (b : WeakParameterSymbol n R W U d m') (a₁ a₂ : WeakParameterSymbol n R V W d m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ := by
  ext p r
  simp [ContinuousLinearMap.comp_sub]

theorem sub_comp (b₁ b₂ : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a := by
  ext p r
  simp [ContinuousLinearMap.sub_comp]

variable {m'' : ℝ}

/-- Composing after raising the order of the outer symbol raises the order of the composition. -/
theorem inclusion_comp (h : m' ≤ m'') (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    (inclusion h le_rfl b).comp a = inclusion (by linarith) le_rfl (b.comp a) := by
  ext p r
  simp

/-- Composing after raising the order of the inner symbol raises the order of the composition. -/
theorem comp_inclusion (h : m ≤ m'') (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    b.comp (inclusion h le_rfl a) = inclusion (by linarith) le_rfl (b.comp a) := by
  ext p r
  simp

/-- Composition of weakly parameter-dependent symbols is associative, up to the identification of
the orders `(m'' + m') + m = m'' + (m' + m)`. -/
theorem comp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U']
    (c : WeakParameterSymbol n R U U' d m'') (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    (c.comp b).comp a = inclusion (add_assoc m'' m' m).ge le_rfl (c.comp (b.comp a)) := by
  ext p r
  simp [ContinuousLinearMap.comp_assoc]

end Comp

/-! ### The normalized resolvent of `1 - Δ` -/

private theorem one_sub_mul_ne_zero {c : ℝ} (hc : c < 1) {r : ℂ} (hr : r.re ≤ c * ‖r‖) {t : ℝ}
    (ht : 0 ≤ t) : 1 - r * t ≠ 0 := by
  intro h
  have h' := Complex.mul_one_add_le_norm_one_sub_mul hr ht
  rw [h, norm_zero] at h'
  have : 0 < (1 - max c (-1)) / 2 * (1 + ‖r‖ * t) :=
    mul_pos (by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]) (by positivity)
  linarith

/-- The complex weight `1 + ‖ξ‖²`, the symbol of `1 - Δ`, satisfies the symbol estimates of
order `2`. -/
private theorem exists_norm_iteratedFDeriv_weight_le (i : ℕ) : ∃ C, ∀ ξ : CoordinateSpace n,
    ‖iteratedFDeriv ℝ i (fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((2 - i : ℝ) / 2) := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le (E := CoordinateSpace n) 2 i
  refine ⟨C, fun ξ => ?_⟩
  have h : (fun ξ : CoordinateSpace n => (((1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    norm_num
  have hξ := hC ξ
  rw [h] at hξ
  exact hξ

private theorem contDiff_weight :
    ContDiff ℝ ∞ fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.add (contDiff_norm_sq ℝ))

/-- **The dilated symbol of `1 - r (1 - Δ)`.** With `t = ⟨ξ⟩`, the derivatives at `0` of
`v ↦ 1 - r (1 + ‖ξ + t v‖²)` are at most `(1 + |C|) (1 + ‖r‖ (1 + ‖ξ‖²))`, where `C` is a
constant in the symbol estimate of order `2` for `1 + ‖ξ‖²`: dilating by `t` turns each frequency
derivative into a factor `t`, which the gain of `1 + ‖ξ‖²` in that derivative compensates. -/
private theorem norm_iteratedFDeriv_one_sub_mul_weight_dilate_le (j : ℕ) {C : ℝ}
    (hC : ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ j (fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((2 - j : ℝ) / 2))
    (r : ℂ) (ξ : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ j (fun v : CoordinateSpace n =>
        1 - r * ((1 + ‖ξ + (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) • v‖ ^ 2 : ℝ) : ℂ)) 0‖ ≤
      (1 + |C|) * (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2)) := by
  set t : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
  have hu : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hwd : ContDiff ℝ ∞ fun v : CoordinateSpace n => ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ) :=
    (contDiff_weight (n := n)).comp (contDiff_const.add (contDiff_id.const_smul t))
  -- The constant contributes at most `1`, the dilated weight at most `|C| (1 + ‖ξ‖²)`.
  have hsplit : iteratedFDeriv ℝ j (fun v : CoordinateSpace n =>
      1 - r * ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ)) 0 =
      iteratedFDeriv ℝ j (fun _ : CoordinateSpace n => (1 : ℂ)) 0 -
        r • iteratedFDeriv ℝ j
          (fun v : CoordinateSpace n => ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ)) 0 := by
    rw [fun_iteratedFDeriv_sub_apply (contDiff_const.contDiffAt.of_le (mod_cast le_top))
      ((contDiff_const.mul hwd).contDiffAt.of_le (mod_cast le_top))]
    congr 1
    exact iteratedFDeriv_const_smul_apply' (a := r) (hwd.of_le (mod_cast le_top)).contDiffAt
  have hconst : ‖iteratedFDeriv ℝ j (fun _ : CoordinateSpace n => (1 : ℂ)) 0‖ ≤ 1 := by
    rcases eq_or_ne j 0 with rfl | hj0
    · simp
    · simp [iteratedFDeriv_const_of_ne hj0]
  have hdil : ‖iteratedFDeriv ℝ j (fun v : CoordinateSpace n =>
      ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ)) 0‖ ≤ |C| * (1 + ‖ξ‖ ^ 2) := by
    rw [norm_iteratedFDeriv_comp_add_const_smul (fun ξ : CoordinateSpace n =>
      ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) ξ t 0 j, smul_zero, add_zero, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hu _), one_add_norm_sq_rpow_one_div_two_pow]
    calc (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) * ‖iteratedFDeriv ℝ j
          (fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) ξ‖
        ≤ (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) * (|C| * (1 + ‖ξ‖ ^ 2) ^ ((2 - j : ℝ) / 2)) := by
          gcongr
          exact (hC ξ).trans (by gcongr; exact le_abs_self _)
      _ = |C| * (1 + ‖ξ‖ ^ 2) := by
          rw [mul_left_comm, ← Real.rpow_add hu,
            show (j : ℝ) / 2 + (2 - j) / 2 = 1 by ring, Real.rpow_one]
  have hr : ‖r • iteratedFDeriv ℝ j
      (fun v : CoordinateSpace n => ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ)) 0‖ ≤
      ‖r‖ * (|C| * (1 + ‖ξ‖ ^ 2)) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hdil (norm_nonneg r)
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add hconst hr).trans ?_)
  have : 0 ≤ ‖r‖ * (1 + ‖ξ‖ ^ 2) := by positivity
  nlinarith [abs_nonneg C]

/-- **Order-zero estimates for the normalized resolvent, uniformly on the sector.** The
derivatives of `ξ ↦ (1 - r (1 + ‖ξ‖²))⁻¹` satisfy the symbol estimates of order `0` with
constants independent of `r` in the sector `Re r ≤ c ‖r‖`. At a frequency `ξ`, dilating by
`t = ⟨ξ⟩` gives a function whose derivatives at `0` are of the size `σ = 1 + ‖r‖ ⟨ξ⟩²` of the
function itself there, so its inverse has derivatives of size `1 / σ ≤ 1`
(`TauCeti.exists_norm_iteratedFDeriv_inv_le_div`); undoing the dilation costs `t ^ (-k)`. -/
private theorem exists_norm_iteratedFDeriv_inv_one_sub_mul_weight_le {c : ℝ} (hc : c < 1)
    (k : ℕ) : ∃ C, ∀ r : {r : ℂ // r.re ≤ c * ‖r‖}, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k
          (fun ξ : CoordinateSpace n => (1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((0 - k : ℝ) / 2) := by
  have hκ : 0 < (1 - max c (-1)) / 2 := by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]
  choose Cw hCw using exists_norm_iteratedFDeriv_weight_le (n := n)
  set A := 1 + ∑ j ∈ Finset.range (k + 1), |Cw j|
  obtain ⟨Q, hQ, hQb⟩ := exists_norm_iteratedFDeriv_inv_le_div (E := CoordinateSpace n)
    (𝕜 := ℂ) k A hκ
  refine ⟨Q, fun ⟨r, hr⟩ ξ => ?_⟩
  set u : ℝ := 1 + ‖ξ‖ ^ 2 with hudef
  have hu : 0 < u := by positivity
  set t : ℝ := u ^ ((1 : ℝ) / 2) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hu _
  set σ : ℝ := 1 + ‖r‖ * u
  have hσ : 1 ≤ σ := le_add_of_nonneg_right (by positivity)
  set h : CoordinateSpace n → ℂ := fun v => 1 - r * ((1 + ‖ξ + t • v‖ ^ 2 : ℝ) : ℂ) with hhdef
  have hh : ContDiff ℝ ∞ h := contDiff_const.sub (contDiff_const.mul
    ((contDiff_weight (n := n)).comp (contDiff_const.add (contDiff_id.const_smul t))))
  have hder : ∀ j ≤ k, ‖iteratedFDeriv ℝ j h 0‖ ≤ A * σ := fun j hj =>
    (norm_iteratedFDeriv_one_sub_mul_weight_dilate_le j (hCw j) r ξ).trans <|
      mul_le_mul_of_nonneg_right (add_le_add le_rfl (Finset.single_le_sum
        (f := fun j => |Cw j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))) (by positivity)
  have hlow : (1 - max c (-1)) / 2 * σ ≤ ‖h 0‖ := by
    have h0 : h 0 = 1 - r * (u : ℂ) := by simp [hhdef, hudef]
    rw [h0]
    exact Complex.mul_one_add_le_norm_one_sub_mul hr hu.le
  have hinv := hQb h σ 0 (by positivity) (hh.of_le (mod_cast le_top)) hder hlow k le_rfl
  -- Undo the dilation: `‖D^k (h⁻¹) 0‖ = t ^ k ‖D^k (1 - r (1 + ‖·‖²))⁻¹ ξ‖`.
  have hundil : ‖iteratedFDeriv ℝ k (fun v => (h v)⁻¹) 0‖ = ‖t‖ ^ k * ‖iteratedFDeriv ℝ k
      (fun ξ : CoordinateSpace n => (1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) (ξ + t • 0)‖ :=
    norm_iteratedFDeriv_comp_add_const_smul
      (fun ξ : CoordinateSpace n => (1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ξ t 0 k
  rw [hundil, smul_zero, add_zero, Real.norm_eq_abs, abs_of_pos ht, htdef,
    one_add_norm_sq_rpow_one_div_two_pow] at hinv
  have hpow : 0 < u ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  calc _ ≤ Q / u ^ ((k : ℝ) / 2) := by
        rw [le_div_iff₀ hpow, mul_comm]
        exact hinv.trans (div_le_self hQ hσ)
    _ = Q * u ^ ((0 - k : ℝ) / 2) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hu.le]
        ring_nf

/-- The `j`-th parameter derivative of `(1 - r u)⁻¹ • id` on an open set of parameters:
`∂_r^j (1 - r u)⁻¹ = j! u ^ j ((1 - r u)⁻¹) ^ (j + 1)` (Mathlib's `iter_deriv_inv_linear`). -/
private theorem iteratedDeriv_indicator_inv_one_sub_mul_smul (u : ℂ) (j : ℕ) {r : ℂ} (hr : r ∈ R)
    (hu : 1 - r * u ≠ 0) :
    iteratedDeriv j ((R : Set ℂ).indicator fun r => (1 - r * u)⁻¹ • ContinuousLinearMap.id ℂ V)
        r = (j ! * (u ^ j * ((1 - r * u)⁻¹) ^ (j + 1))) • ContinuousLinearMap.id ℂ V := by
  have hf : (fun r : ℂ => (1 - r * u)⁻¹) = fun r => (-u * r + 1)⁻¹ := by
    funext s
    ring_nf
  have hd : ContDiffAt ℂ j (fun s : ℂ => (1 - s * u)⁻¹) r :=
    (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const)).inv hu
  rw [iteratedDeriv_indicator_of_mem R.isOpen hr, iteratedDeriv_smul_const hd, hf,
    iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  congr 1
  beta_reduce
  have h1 : ((-1 : ℂ)) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  rw [show (-1 - j : ℤ) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    ← inv_pow, show -u * r + 1 = 1 - r * u by ring, neg_pow u j]
  linear_combination (j ! * u ^ j * ((1 - r * u)⁻¹) ^ (j + 1) : ℂ) * h1

/-- The `j`-th parameter derivative of the normalized resolvent of `1 - Δ`, at a parameter `r ∈ R`
in the sector `Re r ≤ c ‖r‖`, as a function of `(x, ξ)`. -/
private theorem iteratedDeriv_indicator_inv_one_sub_mul_weight_smul {c : ℝ} (hc : c < 1) (j : ℕ)
    {r : ℂ} (hr : r ∈ R) (hrc : r.re ≤ c * ‖r‖) :
    (fun p : CoordinateSpace n × CoordinateSpace n => iteratedDeriv j ((R : Set ℂ).indicator
      fun r => (1 - r * ((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹ • ContinuousLinearMap.id ℂ V) r) =
      fun p => ((j ! : ℂ) * (((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ) ^ j *
        ((1 - r * ((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))) • ContinuousLinearMap.id ℂ V :=
  funext fun p => iteratedDeriv_indicator_inv_one_sub_mul_smul _ j hr
    (one_sub_mul_ne_zero hc hrc (by positivity : (0 : ℝ) ≤ 1 + ‖p.2‖ ^ 2))

/-- The `j`-th parameter derivative `j! (1 + ‖ξ‖²) ^ j ((1 - r (1 + ‖ξ‖²))⁻¹) ^ (j + 1)` of the
normalized resolvent is smooth in `ξ` for `r` in the sector. -/
private theorem contDiff_resolventDeriv {c : ℝ} (hc : c < 1) {r : ℂ} (hr : r.re ≤ c * ‖r‖)
    (j : ℕ) : ContDiff ℝ ∞ fun ξ : CoordinateSpace n => (j ! : ℂ) *
      (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1)) :=
  contDiff_const.mul (((contDiff_weight (n := n)).pow j).mul
    (((contDiff_const.sub (contDiff_const.mul (contDiff_weight (n := n)))).inv fun ξ =>
      one_sub_mul_ne_zero hc hr (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)).pow (j + 1)))

/-- **Symbol estimates for the parameter derivatives of the normalized resolvent.** The function
`ξ ↦ j! (1 + ‖ξ‖²) ^ j ((1 - r (1 + ‖ξ‖²))⁻¹) ^ (j + 1)` satisfies the symbol estimates of order
`2 j`, uniformly in `r` in the sector `Re r ≤ c ‖r‖`. -/
private theorem exists_norm_iteratedFDeriv_resolventDeriv_le {c : ℝ} (hc : c < 1) (j k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ r : {r : ℂ // r.re ≤ c * ‖r‖}, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n => (j ! : ℂ) *
          (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1)))
          ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((0 + 2 * j - k : ℝ) / 2) := by
  have hG (r : {r : ℂ // r.re ≤ c * ‖r‖}) : ContDiff ℝ ∞
      fun ξ : CoordinateSpace n => (1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ :=
    (contDiff_const.sub (contDiff_const.mul (contDiff_weight (n := n)))).inv fun ξ =>
      one_sub_mul_ne_zero hc r.property (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)
  have hW : ∀ i : ℕ, ∃ C, ∀ (_ : {r : ℂ // r.re ≤ c * ‖r‖}) (ξ : CoordinateSpace n),
      ‖iteratedFDeriv ℝ i (fun ξ : CoordinateSpace n => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((2 - i : ℝ) / 2) := fun i =>
    (exists_norm_iteratedFDeriv_weight_le (n := n) i).imp fun _ h _ => h
  -- The product of the weight power, of order `2 j`, and the resolvent power, of order `0`.
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_mul_le_one_add_norm_sq_rpow
    (f := fun (_ : {r : ℂ // r.re ≤ c * ‖r‖}) (ξ : CoordinateSpace n) =>
      ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j)
    (g := fun (r : {r : ℂ // r.re ≤ c * ‖r‖}) (ξ : CoordinateSpace n) =>
      ((1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))
    (fun _ => ((contDiff_weight (n := n)).pow j).of_le (mod_cast le_top))
    (fun r => ((hG r).pow (j + 1)).of_le (mod_cast le_top)) (k := k)
    (fun i _ => exists_norm_iteratedFDeriv_pow_le_one_add_norm_sq_rpow (k := i)
      (fun _ => (contDiff_weight (n := n)).of_le (mod_cast le_top)) (fun i' _ => hW i') j)
    (fun i _ => exists_norm_iteratedFDeriv_pow_le_one_add_norm_sq_rpow (k := i)
      (fun r => (hG r).of_le (mod_cast le_top))
      (fun i' _ => exists_norm_iteratedFDeriv_inv_one_sub_mul_weight_le hc i') (j + 1))
  refine ⟨j ! * |C|, by positivity, fun r ξ => ?_⟩
  have hsmul : (fun ξ : CoordinateSpace n => (j ! : ℂ) *
      (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))) =
      (j ! : ℂ) • fun ξ : CoordinateSpace n =>
        ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - (r : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1) :=
    funext fun _ => (smul_eq_mul _ _).symm
  rw [hsmul, iteratedFDeriv_const_smul_apply ((((contDiff_weight (n := n)).pow j).mul
    ((hG r).pow (j + 1))).of_le (mod_cast le_top)).contDiffAt, norm_smul, Complex.norm_natCast,
    mul_assoc]
  gcongr
  refine (hC r ξ).trans ?_
  rw [show ((j * 2 + (j + 1 : ℕ) * 0 - k : ℝ) / 2) = (0 + 2 * j - k : ℝ) / 2 by push_cast; ring]
  gcongr
  exact le_abs_self _

/-- **Mixed derivatives of the parameter derivatives of the normalized resolvent.** The
position-independent coefficient `(x, ξ) ↦ j! (1 + ‖ξ‖²) ^ j ((1 - r (1 + ‖ξ‖²))⁻¹) ^ (j + 1) • id`
satisfies the symbol estimates of order `2 j`, uniformly in `r` in the sector. -/
private theorem exists_norm_mixedDeriv_resolventDeriv_le {c : ℝ} (hc : c < 1) (j : ℕ)
    (β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℂ, r.re ≤ c * ‖r‖ → ∀ (α : List (Fin n)) (x ξ : CoordinateSpace n),
      ‖mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n => ((j ! : ℂ) *
          (((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - r * ((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))) •
            ContinuousLinearMap.id ℂ V) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((0 + 2 * j - β.length : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_resolventDeriv_le (n := n) hc j β.length
  refine ⟨C, hC0, fun r hr α x ξ => ?_⟩
  have hs := contDiff_resolventDeriv (n := n) hc hr j
  set F : CoordinateSpace n → V →L[ℂ] V := fun ξ => ((j ! : ℂ) *
    (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j * ((1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))) •
      ContinuousLinearMap.id ℂ V
  rcases eq_or_ne α [] with rfl | hα
  · rw [mixedDeriv_nil_comp_snd F]
    refine (norm_coordinateDeriv_le β ((hs.smul contDiff_const).of_le (mod_cast le_top)) ξ).trans ?_
    refine ((hs.of_le (mod_cast le_top)).contDiffAt.norm_iteratedFDeriv_smul_const_le _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans ?_
    exact hC ⟨r, hr⟩ ξ
  · rw [mixedDeriv_comp_snd F hα, norm_zero]
    positivity

variable (V) in
/-- The **normalized resolvent symbol of `1 - Δ`**, `(1 - r (1 + ‖ξ‖²))⁻¹ • id`, on an open set `R`
of reciprocal parameters inside a sector `Re r ≤ c ‖r‖`, `c < 1`. At the spectral parameter
`λ = r⁻¹` it is `λ (λ - (1 + ‖ξ‖²))⁻¹`. It is weakly parameter-dependent of frequency order `0`
and anisotropy `2`: its `j`-th derivative in `r` is
`j! (1 + ‖ξ‖²) ^ j (1 - r (1 + ‖ξ‖²)) ^ (-(j + 1))`, of order `2 j` uniformly in `r`. -/
def shiftedLaplacianNormalizedResolvent {c : ℝ} (hc : c < 1) (hR : ∀ r ∈ R, r.re ≤ c * ‖r‖) :
    WeakParameterSymbol n R V V 2 0 where
  coefficient p := (R : Set ℂ).indicator fun r =>
    (1 - r * ((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹ • ContinuousLinearMap.id ℂ V
  contDiffOn_coefficient p := by
    refine ContDiffOn.congr (f := fun r =>
      (1 - r * ((1 + ‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹ • ContinuousLinearMap.id ℂ V) ?_
      fun _ hr => indicator_of_mem hr _
    exact ((contDiffOn_const.sub (contDiffOn_id.mul contDiffOn_const)).inv fun r hr =>
      one_sub_mul_ne_zero hc (hR r hr) (by positivity)).smul contDiffOn_const
  coefficient_of_notMem p r hr := indicator_of_notMem hr _
  contDiff_iteratedDeriv j r hr := by
    rw [iteratedDeriv_indicator_inv_one_sub_mul_weight_smul hc j hr (hR r hr)]
    exact ((contDiff_resolventDeriv hc (hR r hr) j).smul contDiff_const).comp contDiff_snd
  exists_bound K _ j α β := by
    obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_resolventDeriv_le (n := n) (V := V) hc j β
    refine ⟨C, hC0, fun x _ ξ r hr => ?_⟩
    rw [iteratedDeriv_indicator_inv_one_sub_mul_weight_smul hc j hr (hR r hr)]
    exact hC r (hR r hr) α x ξ

variable {c : ℝ} {hc : c < 1} {hR : ∀ r ∈ R, r.re ≤ c * ‖r‖}

@[simp]
theorem coefficient_shiftedLaplacianNormalizedResolvent (x ξ : CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (shiftedLaplacianNormalizedResolvent V hc hR).coefficient (x, ξ) r =
      (1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ • ContinuousLinearMap.id ℂ V :=
  indicator_of_mem (s := (R : Set ℂ)) hr fun r =>
    (1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ • ContinuousLinearMap.id ℂ V

/-- The parameter derivatives of the normalized resolvent symbol:
`∂_r^j (1 - r (1 + ‖ξ‖²))⁻¹ = j! (1 + ‖ξ‖²) ^ j ((1 - r (1 + ‖ξ‖²))⁻¹) ^ (j + 1)`. -/
theorem iteratedDeriv_coefficient_shiftedLaplacianNormalizedResolvent (j : ℕ)
    (x ξ : CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    iteratedDeriv j ((shiftedLaplacianNormalizedResolvent V hc hR).coefficient (x, ξ)) r =
      ((j ! : ℂ) * (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ j *
        ((1 - r * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) ^ (j + 1))) • ContinuousLinearMap.id ℂ V :=
  congrFun (iteratedDeriv_indicator_inv_one_sub_mul_weight_smul hc j hr (hR r hr)) (x, ξ)

/-- At the spectral parameter `λ ≠ 0` with `λ⁻¹ ∈ R`, the normalized resolvent symbol is
`-λ ((1 + ‖ξ‖²) - λ)⁻¹`, that is `-λ` times the resolvent symbol of `1 - Δ`. -/
theorem coefficient_shiftedLaplacianNormalizedResolvent_inv (x ξ : CoordinateSpace n) {μ : ℂ}
    (hμ : μ⁻¹ ∈ R) (hμ0 : μ ≠ 0) :
    (shiftedLaplacianNormalizedResolvent V hc hR).coefficient (x, ξ) μ⁻¹ =
      (-μ * (((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) - μ)⁻¹) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_shiftedLaplacianNormalizedResolvent x ξ hμ]
  have h1 : 1 - μ⁻¹ * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) = -(((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) - μ) * μ⁻¹ := by
    field_simp
    ring
  rw [h1, mul_inv, inv_inv, inv_neg]
  congr 1
  ring

/-- **Comparison with the strongly parameter-dependent calculus.** At a spectral parameter
`λ ∈ Λ` with `λ⁻¹ ∈ R`, the normalized resolvent symbol is `-λ` times the resolvent symbol
`((1 + ‖ξ‖²) - λ)⁻¹`, the inverse of the strongly parameter-dependent symbol of `1 - Δ - λ`. -/
theorem coefficient_shiftedLaplacianNormalizedResolvent_inv_eq_neg_smul [CompleteSpace V]
    {Λ : TopologicalSpace.Opens ℂ}
    (h : (ParameterSymbol.shiftedLaplacian V 1 : ParameterSymbol n Λ V V 2).IsElliptic)
    (x ξ : CoordinateSpace n) {μ : ℂ} (hμΛ : μ ∈ Λ) (hμ : μ⁻¹ ∈ R) (hμ0 : μ ≠ 0) :
    (shiftedLaplacianNormalizedResolvent V hc hR).coefficient (x, ξ) μ⁻¹ =
      (-μ) • ((ParameterSymbol.shiftedLaplacian V 1).inverse h).coefficient ((x, ξ), μ) := by
  rw [coefficient_shiftedLaplacianNormalizedResolvent_inv x ξ hμ hμ0,
    ParameterSymbol.coefficient_inverse_shiftedLaplacian h x ξ hμΛ, smul_smul]

end WeakParameterSymbol

end TauCeti
