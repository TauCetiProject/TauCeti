/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

/-!
# Weakly parameter-dependent symbols

The resolvent `(A - λ)⁻¹` of a classical elliptic pseudodifferential operator `A` of order `d > 0`
is not a strongly parameter-dependent operator (`TauCeti.ParameterSymbol`) unless `A` is a
differential operator: its symbol is not jointly homogeneous in `(ξ, λ^{1/d})`. Grubb and Seeley
showed that it belongs instead to a calculus of *weakly* parameter-dependent symbols, defined
through the inverse parameter `r = 1 / λ`. A symbol `a(x, ξ, λ)` of this calculus, of frequency
order `m`, is described by `b(x, ξ, r) = a(x, ξ, 1 / r)`, holomorphic in `r`, such that each
derivative `∂_r^j b` is an ordinary symbol of order `m + d j`, with estimates uniform in `r`:

`‖∂ₓ^α ∂_ξ^β ∂_r^j b(x, ξ, r)‖ ≤ C ⟨ξ⟩ ^ (m + d j - |β|)`

for `x` in a compact set, all frequencies `ξ` and all `r` in the parameter set. Each derivative
in `r` may cost `d` frequency orders, the anisotropy `d` being the order of `A`. Grubb and Seeley
also use the classes of the products `λ ^ δ a` with such `a`; this file treats `δ = 0`.

This file defines the class `TauCeti.WeakParameterSymbol n R V W d m` of such `b`, on an open set
`R ⊆ ℂ` of inverse parameters (typically the image under `λ ↦ 1 / λ` of a sector of spectral
parameters with `|λ| ≥ 1`, a bounded set of inverse parameters `r ≠ 0`), with values in
`V →L[ℂ] W`. Its `j`-th slice at `r ∈ R`,
`TauCeti.WeakParameterSymbol.slice b j r`, is the ordinary symbol `(x, ξ) ↦ ∂_r^j b(x, ξ, r)` of
order `m + d j`, and the defining estimates say that every seminorm of the slices is bounded
uniformly in `r` (`TauCeti.WeakParameterSymbol.exists_seminorm_slice_le`); a holomorphic family
with such slices is a weakly parameter-dependent symbol
(`TauCeti.WeakParameterSymbol.ofSlices`; `TauCeti.WeakParameterSymbol.ofSlicesOn` extends a family
holomorphic on `R` by zero).

## Main definitions and results

* `TauCeti.WeakParameterSymbol`: the class, with its complex vector space structure.
* `TauCeti.WeakParameterSymbol.slice`, `TauCeti.WeakParameterSymbol.exists_seminorm_slice_le`:
  the slices `∂_r^j b(·, ·, r)` and their seminorm bounds, uniform in `r`.
* `TauCeti.WeakParameterSymbol.inclusion`: the order inclusions, as linear maps.
* `TauCeti.WeakParameterSymbol.ofSymbol`: a symbol of order `m` independent of the parameter.
* `TauCeti.WeakParameterSymbol.ofParameter`: for `d ≥ 0`, a function of the parameter alone,
  holomorphic with bounded derivatives on `R`, is a symbol of order `0`.
* `TauCeti.WeakParameterSymbol.comp`: the pointwise composition `b ∘ a` of symbols `b` of order
  `m'` and `a` of order `m` has order `m' + m`. Its slices are given by Leibniz's rule in `r`
  (`TauCeti.WeakParameterSymbol.slice_comp`, from `ContinuousLinearMap.iteratedDeriv_of_bilinear`
  applied to `ContinuousLinearMap.compL`), and each term
  `∂_r^i b ∘ ∂_r^(j - i) a` has order `m' + d i + m + d (j - i) = m' + m + d j`.

## References

* G. Grubb, R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–Singer
  boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
* G. Grubb, L. Hansen, *Complex powers of resolvents of pseudodifferential operators*,
  Comm. Partial Differential Equations 27 (2002), 2333–2361, Definition 2.1.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

variable (n) in
/-- The class of weakly parameter-dependent symbols of frequency order `m` and anisotropy `d`, in
the inverse parameter `r` ranging over an open set `R ⊆ ℂ`, with values in `V →L[ℂ] W`: maps
`b(x, ξ, r)`, holomorphic in `r ∈ R`, such that for every `j` the derivative `∂_r^j b(·, ·, r)` is
smooth in `(x, ξ)` and, on every compact set `K` of positions,

`‖∂ₓ^α ∂_ξ^β ∂_r^j b(x, ξ, r)‖ ≤ C ⟨ξ⟩ ^ (m + d j - |β|)`

for some `C`, all `x ∈ K`, all frequencies `ξ` and all `r ∈ R`. A symbol `a(x, ξ, λ)` in the
spectral parameter `λ` is weakly parametric when `b(x, ξ, r) = a(x, ξ, 1 / r)` is in this class.
By convention the coefficient vanishes for `r ∉ R`. -/
@[ext]
structure WeakParameterSymbol (R : Opens ℂ) (V W : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (d m : ℝ) where
  /-- The coefficient `b(x, ξ, r)` at the position and frequency `p = (x, ξ)` and the inverse
  parameter `r`, set to `0` for `r ∉ R`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W
  differentiableOn_coefficient : ∀ p, DifferentiableOn ℂ (coefficient p) R
  coefficient_of_notMem : ∀ p, ∀ r ∉ R, coefficient p r = 0
  contDiff_iteratedDeriv : ∀ j : ℕ, ∀ r ∈ R,
    ContDiff ℝ ∞ fun p ↦ iteratedDeriv j (coefficient p) r
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ (α β : List (Fin n)) (j : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ iteratedDeriv j (coefficient p) r) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m + d * j - β.length) / 2)

namespace WeakParameterSymbol

variable {R : Opens ℂ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]
  {d m m' : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : WeakParameterSymbol n R V W d m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => WeakParameterSymbol.ext h

/-- A weakly parameter-dependent symbol is determined by its values at parameters in `R`. -/
theorem ext_of_mem {a b : WeakParameterSymbol n R V W d m}
    (h : ∀ p, ∀ r ∈ R, a.coefficient p r = b.coefficient p r) : a = b := by
  ext p r
  by_cases hr : r ∈ R
  · rw [h p r hr]
  · rw [a.coefficient_of_notMem p r hr, b.coefficient_of_notMem p r hr]

section Slice

variable (a : WeakParameterSymbol n R V W d m)

/-- The coefficient is smooth in the parameter on `R`, being holomorphic there. -/
theorem contDiffOn_coefficient [CompleteSpace W] (p : CoordinateSpace n × CoordinateSpace n)
    {k : WithTop ℕ∞} : ContDiffOn ℂ k (a.coefficient p) R :=
  (a.differentiableOn_coefficient p).contDiffOn R.isOpen

/-- The `j`-th slice of `b` at `r ∈ R`: the ordinary symbol `(x, ξ) ↦ ∂_r^j b(x, ξ, r)` of order
`m + d j`. -/
def slice (j : ℕ) (r : R) : Symbol n V W (m + d * j) where
  coefficient p := iteratedDeriv j (a.coefficient p) r
  contDiff_coefficient := a.contDiff_iteratedDeriv j r r.property
  exists_bound K hK α β := (a.exists_bound K hK α β j).imp fun _ hC ↦ ⟨hC.1, hC.2 r r.property⟩

@[simp]
theorem coefficient_slice (j : ℕ) (r : R) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.slice j r).coefficient p = iteratedDeriv j (a.coefficient p) r := (rfl)

/-- **The defining estimates.** Every seminorm of the slices `∂_r^j b(·, ·, r)` is bounded
uniformly in `r ∈ R`. -/
theorem exists_seminorm_slice_le (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (j : ℕ) : ∃ C, ∀ r : R, Symbol.seminorm K α β (a.slice j r) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := a.exists_bound K K.isCompact α β j
  exact ⟨C, fun r ↦ Symbol.seminorm_le_bound K α β _ hC0 fun x hx ξ ↦ hC r r.property x hx ξ⟩

end Slice

section OfSlices

variable (b : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W)
  (hb : ∀ p, DifferentiableOn ℂ (b p) R) (hb₀ : ∀ p, ∀ r ∉ R, b p r = 0)
  (s : (j : ℕ) → R → Symbol n V W (m + d * j))
  (hs : ∀ j r p, (s j r).coefficient p = iteratedDeriv j (b p) r)
  (hbound : ∀ (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) (j : ℕ),
    ∃ C, ∀ r : R, Symbol.seminorm K α β (s j r) ≤ C)

/-- A family `b`, holomorphic in the parameter on `R` and vanishing outside `R`, whose derivatives
`∂_r^j b(·, ·, r)` are the coefficients of symbols `s j r` of order `m + d j` with seminorms bounded
uniformly in `r`, is a weakly parameter-dependent symbol. -/
def ofSlices : WeakParameterSymbol n R V W d m where
  coefficient := b
  differentiableOn_coefficient := hb
  coefficient_of_notMem := hb₀
  contDiff_iteratedDeriv j r hr := by
    rw [show (fun p ↦ iteratedDeriv j (b p) r) = (s j ⟨r, hr⟩).coefficient from
      funext fun p ↦ (hs j ⟨r, hr⟩ p).symm]
    exact (s j ⟨r, hr⟩).contDiff_coefficient
  exists_bound K hK α β j := by
    obtain ⟨C, hC⟩ := hbound ⟨K, hK⟩ α β j
    refine ⟨max C 0, le_max_right C 0, fun r hr x hx ξ ↦ ?_⟩
    have h := Symbol.le_seminorm ⟨K, hK⟩ α β (s j ⟨r, hr⟩) hx ξ
    simp only [funext (hs j ⟨r, hr⟩)] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((hC ⟨r, hr⟩).trans (le_max_left C 0))
      (rpow_weight_pos ξ _).le)

@[simp]
theorem coefficient_ofSlices : (ofSlices b hb hb₀ s hs hbound).coefficient = b := (rfl)

@[simp]
theorem slice_ofSlices (j : ℕ) (r : R) : (ofSlices b hb hb₀ s hs hbound).slice j r = s j r :=
  Symbol.ext (funext fun p ↦ (hs j r p).symm)

end OfSlices

section OfSlicesOn

variable (g : CoordinateSpace n × CoordinateSpace n → ℂ → V →L[ℂ] W)
  (hg : ∀ p, DifferentiableOn ℂ (g p) R)
  (s : (j : ℕ) → R → Symbol n V W (m + d * j))
  (hs : ∀ j r p, (s j r).coefficient p = iteratedDeriv j (g p) r)
  (hbound : ∀ (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) (j : ℕ),
    ∃ C, ∀ r : R, Symbol.seminorm K α β (s j r) ≤ C)

/-- A family `g`, holomorphic in the parameter on `R`, whose derivatives `∂_r^j g(·, ·, r)` are
the coefficients of symbols `s j r` of order `m + d j` with seminorms bounded uniformly in `r`,
gives a weakly parameter-dependent symbol, equal to `g` on `R` and extended by zero outside `R`.
Unlike `TauCeti.WeakParameterSymbol.ofSlices`, `g` need not vanish outside `R`. -/
def ofSlicesOn : WeakParameterSymbol n R V W d m :=
  ofSlices (fun p ↦ (R : Set ℂ).indicator (g p))
    (fun p ↦ (hg p).congr fun _ hr ↦ indicator_of_mem hr _)
    (fun _ _ hr ↦ indicator_of_notMem hr _) s
    (fun j r p ↦ by
      have h : (R : Set ℂ).EqOn ((R : Set ℂ).indicator (g p)) (g p) :=
        fun _ hr ↦ indicator_of_mem hr _
      rw [hs, h.iteratedDeriv_of_isOpen R.isOpen j r.property])
    hbound

@[simp]
theorem coefficient_ofSlicesOn (p : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    (ofSlicesOn g hg s hs hbound).coefficient p r = g p r :=
  indicator_of_mem hr _

@[simp]
theorem slice_ofSlicesOn (j : ℕ) (r : R) : (ofSlicesOn g hg s hs hbound).slice j r = s j r :=
  slice_ofSlices ..

end OfSlicesOn

section Module

instance : Zero (WeakParameterSymbol n R V W d m) where
  zero := ofSlices (fun _ _ ↦ 0) (fun _ ↦ differentiableOn_const 0) (fun _ _ _ ↦ rfl)
    (fun _ _ ↦ 0) (fun j r p ↦ by simp)
    (fun _ _ _ _ ↦ ⟨0, fun _ ↦ by simp⟩)

instance : SMul ℂ (WeakParameterSymbol n R V W d m) where
  smul c a := ofSlices (c • a.coefficient)
    (fun p ↦ (a.differentiableOn_coefficient p).const_smul c)
    (fun p r hr ↦ by simp [a.coefficient_of_notMem p r hr])
    (fun j r ↦ c • a.slice j r)
    (fun j r p ↦ by
      rw [Pi.smul_apply, iteratedDeriv_const_smul_field]
      simp)
    (fun K α β j ↦ by
      obtain ⟨C, hC⟩ := a.exists_seminorm_slice_le K α β j
      exact ⟨‖c‖ * C, fun r ↦ by
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg c)⟩)

instance : Neg (WeakParameterSymbol n R V W d m) where
  neg a := ofSlices (-a.coefficient)
    (fun p ↦ (a.differentiableOn_coefficient p).neg)
    (fun p r hr ↦ by simp [a.coefficient_of_notMem p r hr])
    (fun j r ↦ -a.slice j r)
    (fun j r p ↦ by
      rw [Pi.neg_apply, iteratedDeriv_neg]
      simp)
    (fun K α β j ↦ by
      obtain ⟨C, hC⟩ := a.exists_seminorm_slice_le K α β j
      exact ⟨C, fun r ↦ by simpa only [map_neg_eq_map] using hC r⟩)

instance : SMul ℕ (WeakParameterSymbol n R V W d m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (WeakParameterSymbol n R V W d m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : WeakParameterSymbol n R V W d m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : WeakParameterSymbol n R V W d m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : WeakParameterSymbol n R V W d m) :
    (-a).coefficient = -a.coefficient := (rfl)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : WeakParameterSymbol n R V W d m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : WeakParameterSymbol n R V W d m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

@[simp]
theorem slice_zero (j : ℕ) (r : R) : (0 : WeakParameterSymbol n R V W d m).slice j r = 0 :=
  slice_ofSlices ..

@[simp]
theorem slice_smul (c : ℂ) (a : WeakParameterSymbol n R V W d m) (j : ℕ) (r : R) :
    (c • a).slice j r = c • a.slice j r :=
  slice_ofSlices ..

@[simp]
theorem slice_neg (a : WeakParameterSymbol n R V W d m) (j : ℕ) (r : R) :
    (-a).slice j r = -a.slice j r :=
  slice_ofSlices ..

variable [CompleteSpace W]

/-- On `R`, the derivatives of a coefficient are those of a smooth function. -/
private theorem contDiffAt_coefficient (a : WeakParameterSymbol n R V W d m)
    (p : CoordinateSpace n × CoordinateSpace n) (r : R) {k : WithTop ℕ∞} :
    ContDiffAt ℂ k (a.coefficient p) r :=
  (a.contDiffOn_coefficient p).contDiffAt (R.isOpen.mem_nhds r.property)

instance : Add (WeakParameterSymbol n R V W d m) where
  add a b := ofSlices (a.coefficient + b.coefficient)
    (fun p ↦ (a.differentiableOn_coefficient p).add (b.differentiableOn_coefficient p))
    (fun p r hr ↦ by simp [a.coefficient_of_notMem p r hr, b.coefficient_of_notMem p r hr])
    (fun j r ↦ a.slice j r + b.slice j r)
    (fun j r p ↦ by
      rw [Pi.add_apply, iteratedDeriv_add (a.contDiffAt_coefficient p r)
        (b.contDiffAt_coefficient p r)]
      simp)
    (fun K α β j ↦ by
      obtain ⟨C, hC⟩ := a.exists_seminorm_slice_le K α β j
      obtain ⟨D, hD⟩ := b.exists_seminorm_slice_le K α β j
      exact ⟨C + D, fun r ↦ (map_add_le_add _ _ _).trans (add_le_add (hC r) (hD r))⟩)

instance : Sub (WeakParameterSymbol n R V W d m) where
  sub a b := a + -b

@[simp]
theorem coefficient_add (a b : WeakParameterSymbol n R V W d m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_sub (a b : WeakParameterSymbol n R V W d m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (WeakParameterSymbol n R V W d m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (WeakParameterSymbol n R V W d m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

@[simp]
theorem slice_add (a b : WeakParameterSymbol n R V W d m) (j : ℕ) (r : R) :
    (a + b).slice j r = a.slice j r + b.slice j r :=
  slice_ofSlices ..

@[simp]
theorem slice_sub (a b : WeakParameterSymbol n R V W d m) (j : ℕ) (r : R) :
    (a - b).slice j r = a.slice j r - b.slice j r := by
  rw [sub_eq_add_neg, slice_add, slice_neg, ← sub_eq_add_neg]

end Module

section Inclusion

variable [CompleteSpace W]

/-- A weakly parameter-dependent symbol of frequency order `m` has every frequency order
`m' ≥ m`. -/
def inclusion (h : m ≤ m') :
    WeakParameterSymbol n R V W d m →ₗ[ℂ] WeakParameterSymbol n R V W d m' where
  toFun a := ofSlices a.coefficient a.differentiableOn_coefficient a.coefficient_of_notMem
    (fun j r ↦ Symbol.inclusion (by linarith) (a.slice j r)) (fun _ _ _ ↦ by simp)
    (fun K α β j ↦ (a.exists_seminorm_slice_le K α β j).imp fun _ hC r ↦
      (Symbol.seminorm_inclusion_le _ K α β _).trans (hC r))
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : WeakParameterSymbol n R V W d m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

@[simp]
theorem slice_inclusion (h : m ≤ m') (a : WeakParameterSymbol n R V W d m) (j : ℕ) (r : R) :
    (inclusion h a).slice j r =
      Symbol.inclusion (by linarith : m + d * j ≤ m' + d * j) (a.slice j r) := by
  ext p
  simp

theorem inclusion_injective (h : m ≤ m') :
    Function.Injective (inclusion (n := n) (R := R) (V := V) (W := W) (d := d) h) :=
  fun _ _ hab ↦ coefficient_injective (by simpa using congrArg coefficient hab)

end Inclusion

section OfSymbol

/-- The slices of a symbol independent of the parameter: the symbol itself, then zero. -/
private def ofSymbolSlice (b : Symbol n V W m) : (j : ℕ) → Symbol n V W (m + d * j)
  | 0 => Symbol.inclusion (by simp) b
  | _ + 1 => 0

/-- A symbol `b` of order `m` that does not depend on the parameter, as a weakly
parameter-dependent symbol of frequency order `m`: its coefficient is `b(x, ξ)` for every `r ∈ R`.
All its derivatives in the parameter vanish. -/
def ofSymbol (b : Symbol n V W m) : WeakParameterSymbol n R V W d m :=
  ofSlicesOn (fun p _ ↦ b.coefficient p) (fun p ↦ differentiableOn_const (b.coefficient p))
    (fun j _ ↦ ofSymbolSlice b j)
    (fun j r p ↦ by
      rw [iteratedDeriv_const]
      cases j <;> simp [ofSymbolSlice])
    (fun K α β j ↦ by
      cases j with
      | zero => exact ⟨Symbol.seminorm K α β b, fun _ ↦ Symbol.seminorm_inclusion_le _ K α β b⟩
      | succ j => exact ⟨0, fun _ ↦ by simp [ofSymbolSlice]⟩)

@[simp]
theorem coefficient_ofSymbol (b : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n)
    {r : ℂ} (hr : r ∈ R) : (ofSymbol (R := R) (d := d) b).coefficient p r = b.coefficient p :=
  coefficient_ofSlicesOn _ _ _ _ _ p hr

@[simp]
theorem slice_ofSymbol_zero (b : Symbol n V W m) (r : R) :
    (ofSymbol (R := R) (d := d) b).slice 0 r = Symbol.inclusion (by simp) b :=
  slice_ofSlicesOn ..

@[simp]
theorem slice_ofSymbol_succ (b : Symbol n V W m) (j : ℕ) (r : R) :
    (ofSymbol (R := R) (d := d) b).slice (j + 1) r = 0 := by
  simp [ofSymbol, ofSymbolSlice]

end OfSymbol

section OfParameter

/-- A function `g` of the parameter alone, holomorphic on `R` with every derivative bounded on
`R`, as a weakly parameter-dependent symbol of frequency order `0`, for an anisotropy `d ≥ 0`:
its coefficient is `g(r)` for every position and frequency. Its slices are the constant symbols
`∂_r^j g(r)` of order `0 ≤ d j`. -/
def ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W) (hg : DifferentiableOn ℂ g R)
    (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C) :
    WeakParameterSymbol n R V W d 0 :=
  ofSlicesOn (fun _ ↦ g) (fun _ ↦ hg)
    (fun j r ↦ Symbol.inclusion (by positivity) (Symbol.const (iteratedDeriv j g r)))
    (fun j r p ↦ by simp)
    (fun K α β j ↦ (hbound j).imp fun _ hC r ↦ (Symbol.seminorm_inclusion_le _ K α β _).trans
      ((Symbol.seminorm_const_le K α β _).trans (hC r r.property)))

@[simp]
theorem coefficient_ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W) (hg : DifferentiableOn ℂ g R)
    (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C)
    (p : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    (ofParameter hd g hg hbound).coefficient p r = g r :=
  coefficient_ofSlicesOn _ _ _ _ _ p hr

@[simp]
theorem slice_ofParameter (hd : 0 ≤ d) (g : ℂ → V →L[ℂ] W) (hg : DifferentiableOn ℂ g R)
    (hbound : ∀ j : ℕ, ∃ C, ∀ r ∈ R, ‖iteratedDeriv j g r‖ ≤ C) (j : ℕ) (r : R) :
    (ofParameter (n := n) hd g hg hbound).slice j r =
      Symbol.inclusion (by positivity) (Symbol.const (iteratedDeriv j g r)) :=
  slice_ofSlicesOn ..

end OfParameter

section Comp

variable [CompleteSpace W] [CompleteSpace U]

/-- For `i ≤ j`, `m' + d i + (m + d (j - i)) = m' + m + d j`: the order of the term
`∂_r^i b ∘ ∂_r^(j - i) a` of Leibniz's rule is `m' + m + d j`. -/
theorem add_mul_add_add_mul_sub_eq {j : ℕ} (i : Fin (j + 1)) :
    m' + d * i + (m + d * ↑(j - i : ℕ)) = m' + m + d * j := by
  rw [Nat.cast_sub i.is_le]
  ring

/-- **Composition.** The pointwise composition `(x, ξ, r) ↦ b(x, ξ, r) ∘ a(x, ξ, r)` of weakly
parameter-dependent symbols `b` of frequency order `m'` and `a` of frequency order `m` has
frequency order `m' + m`. By Leibniz's rule in `r`
(`ContinuousLinearMap.iteratedDeriv_of_bilinear`, `TauCeti.WeakParameterSymbol.slice_comp`) its
`j`-th slice is a sum of the compositions `∂_r^i b ∘ ∂_r^(j - i) a` of slices, each of order
`m' + d i + m + d (j - i) = m' + m + d j`. -/
def comp (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m) :
    WeakParameterSymbol n R V U d (m' + m) :=
  ofSlices (fun p r ↦ (b.coefficient p r).comp (a.coefficient p r))
    (fun p ↦ (b.differentiableOn_coefficient p).clm_comp (a.differentiableOn_coefficient p))
    (fun p r hr ↦ by simp [b.coefficient_of_notMem p r hr])
    (fun j r ↦ ∑ i : Fin (j + 1),
      (j.choose i : ℂ) •
        Symbol.inclusion (add_mul_add_add_mul_sub_eq i).le
          ((b.slice i r).comp (a.slice (j - i) r)))
    (fun j r p ↦ by
      have hL := (ContinuousLinearMap.compL ℂ V W U).iteratedDeriv_of_bilinear
        (b.contDiffAt_coefficient p r) (a.contDiffAt_coefficient p r) (n := j)
      simp only [ContinuousLinearMap.compL_apply] at hL
      rw [hL, Symbol.coefficient_sum, Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun i ↦ j.choose i •
          (iteratedDeriv i (b.coefficient p) r).comp (iteratedDeriv (j - i) (a.coefficient p) r))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [Nat.cast_smul_eq_nsmul])
    (fun K α β j ↦ by
      choose C hC using fun i : Fin (j + 1) ↦ Symbol.exists_seminorm_comp_le K
        (b := fun r : R ↦ b.slice i r) (a := fun r ↦ a.slice (j - i) r)
        (fun α β ↦ b.exists_seminorm_slice_le K α β i)
        (fun α β ↦ a.exists_seminorm_slice_le K α β (j - i)) α β
      refine ⟨∑ i : Fin (j + 1), ‖(j.choose i : ℂ)‖ * C i, fun r ↦ ?_⟩
      refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
        (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left
        ((Symbol.seminorm_inclusion_le _ K α β _).trans (hC i r)) (norm_nonneg _))

@[simp]
theorem coefficient_comp (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (b.comp a).coefficient p r = (b.coefficient p r).comp (a.coefficient p r) := (rfl)

/-- **Leibniz's rule for the slices of a composition**, as symbols: the `j`-th slice of `b ∘ a`
is the sum of the compositions `(j choose i) ∂_r^i b ∘ ∂_r^(j - i) a` of slices, each of order
`m' + m + d j`. -/
@[simp]
theorem slice_comp (b : WeakParameterSymbol n R W U d m') (a : WeakParameterSymbol n R V W d m)
    (j : ℕ) (r : R) :
    (b.comp a).slice j r = ∑ i : Fin (j + 1), (j.choose i : ℂ) •
      Symbol.inclusion (add_mul_add_add_mul_sub_eq i).le
        ((b.slice i r).comp (a.slice (j - i) r)) :=
  slice_ofSlices ..

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
    (inclusion h b).comp a = inclusion (by linarith) (b.comp a) := by
  ext p r
  simp

/-- Composing after raising the order of the inner symbol raises the order of the composition. -/
theorem comp_inclusion (h : m ≤ m'') (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    b.comp (inclusion h a) = inclusion (by linarith) (b.comp a) := by
  ext p r
  simp

/-- Composition of weakly parameter-dependent symbols is associative, up to the identification of
the orders `(m'' + m') + m = m'' + (m' + m)`. -/
theorem comp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U'] [CompleteSpace U']
    (c : WeakParameterSymbol n R U U' d m'') (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    (c.comp b).comp a = inclusion (add_assoc m'' m' m).ge (c.comp (b.comp a)) := by
  ext p r
  simp [ContinuousLinearMap.comp_assoc]

end Comp

end WeakParameterSymbol

end TauCeti
