/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.RingOfDefinition
public import TauCeti.RingTheory.WittVector.IntervalRing

/-!
# The window subring of `𝕎 O[1/(p [ϖ])]` is a ring of definition for the interval norm

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser, `0 < v(ϖ) < 1`. In a localisation `B`
of `𝕎 O` away from `p [ϖ]`, for nonnegative rationals `q = a / b` and `q' = a' / b'` in lowest
terms, consider the fractions

```text
[ϖ] ^ b / p ^ a,      p ^ a' / [ϖ] ^ b'
```

(`TauCeti.WittVector.radiusLowerFrac`, `TauCeti.WittVector.radiusUpperFrac`) and the subring

```text
𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']
```

of `B` they generate over `𝕎 O` (`TauCeti.WittVector.windowSubring`). A valuation `w` on `B` is
at most `1` at the first fraction exactly when `w([ϖ]) ^ b ≤ w(p) ^ a`, the lower radius bound
`q ≤ κ(w)`, and at the second exactly when `w(p) ^ a' ≤ w([ϖ]) ^ b'`, the upper radius bound
`κ(w) ≤ q'`. So the window subring is the ring of definition `A₀[T / s]`, for `A₀ = 𝕎 O`, of the
rational localisation of `𝕎 O` at the window `{q ≤ κ ≤ q'}` of the Fargues–Fontaine curve,
presented by these two fractions.

The interval ring `B^I` is instead the completion of `𝕎 O[1/(p [ϖ])]` for the interval norm
`λ_I = max(λ_{ρ₁}, λ_{ρ₂})` (`TauCeti.WittVector.IntervalLocalization`). The main theorem compares
the two topologies. If the radii are the ones matching the window,

```text
ρ₁ ^ a = v(ϖ) ^ b,      ρ₂ ^ a' = v(ϖ) ^ b',      ρ₁ ≤ ρ₂,
```

that is `ρ₁ = v(ϖ) ^ (1 / q)` and `ρ₂ = v(ϖ) ^ (1 / q')`, then the window subring is open and
bounded for `λ_I`, hence a ring of definition of `𝕎 O[1/(p [ϖ])]` with the interval norm (Wedhorn,
Lemma 6.2). This is the analytic input for identifying `B^I` with the completed coordinate ring of
the window.

## Proof outline

Boundedness holds because both fractions have interval norm at most `1`. Openness comes from the
unit ball: every `x` with `λ_I(x) ≤ 1` lies in the window subring after multiplication by
`[ϖ] ^ (b + b')`. Write `x = y / (p [ϖ]) ^ m` and expand `y = ∑ₙ [yₙ] pⁿ` in Teichmüller
coordinates. The bound `λ_{ρ₁}(x) ≤ 1` controls the terms with `n < m`, which carry a negative
power of `p` and are reached through `[ϖ] ^ b / p ^ a`. The bound `λ_{ρ₂}(x) ≤ 1` controls the
terms with `n ≥ m`, which carry a negative power of `[ϖ]` and are reached through
`p ^ a' / [ϖ] ^ b'`. In each case the valuation inequality makes a power of `ϖ` divide `yₙ` in
`O`. The tail `p ^ (M + 1) z` of the expansion is absorbed by a power of `p ^ a' / [ϖ] ^ b'`.

## Main definitions

* `TauCeti.WittVector.radiusLowerFrac` : the fraction `[ϖ] ^ b / p ^ a` for `q = a / b`.
* `TauCeti.WittVector.radiusUpperFrac` : the fraction `p ^ a' / [ϖ] ^ b'` for `q' = a' / b'`.
* `TauCeti.WittVector.windowSubring` : the subring `𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']`.

## Main results

* `TauCeti.WittVector.radiusLowerFrac_mul_algebraMap` and
  `TauCeti.WittVector.radiusUpperFrac_mul_algebraMap` : the defining equations of the fractions.
* `TauCeti.WittVector.windowSubring_le_iff` : the universal property of the window subring.
* `TauCeti.WittVector.algebraMap_teichmuller_pow_mul_mem_windowSubring_of_norm_le_one` : the
  unit ball of `λ_I` lies in `[ϖ] ^ -(b + b')` times the window subring.
* `TauCeti.WittVector.isOpen_windowSubring` : the window subring is open for `λ_I`.
* `TauCeti.WittVector.isBounded_windowSubring` : the window subring is bounded for `λ_I`.
* `TauCeti.WittVector.exists_pairOfDefinition_ringOfDefinition_eq_windowSubring` : for the radii
  of the window, the window subring is a ring of definition of `𝕎 O[1/(p [ϖ])]` with the interval
  norm.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the interval rings `B^I` and the windows.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 6.2 and
  Proposition and Definition 5.51.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O] (ϖ : O)

local notation "𝕎" => _root_.WittVector p

section Away

variable (B : Type*) [CommRing B] [Algebra (_root_.WittVector p O) B]
  [IsLocalization.Away ((p : _root_.WittVector p O) * teichmuller p ϖ) B]

include ϖ in
private theorem isUnit_algebraMap_natCast : IsUnit (algebraMap (𝕎 O) B p) :=
  IsLocalization.Away.isUnit_of_dvd ((p : 𝕎 O) * teichmuller p ϖ) (dvd_mul_right _ _)

private theorem isUnit_algebraMap_teichmuller :
    IsUnit (algebraMap (𝕎 O) B (teichmuller p ϖ)) :=
  IsLocalization.Away.isUnit_of_dvd ((p : 𝕎 O) * teichmuller p ϖ) (dvd_mul_left _ _)

/-- The Laurent monomial `[ϖ] ^ α p ^ β` of `B`, for integers `α` and `β`. -/
private noncomputable def mono (α β : ℤ) : B :=
  ((isUnit_algebraMap_teichmuller p ϖ B).unit ^ α *
    (isUnit_algebraMap_natCast p ϖ B).unit ^ β : Bˣ)

variable {p ϖ B}

private theorem mono_add (α β γ δ : ℤ) :
    mono p ϖ B (α + γ) (β + δ) = mono p ϖ B α β * mono p ϖ B γ δ := by
  simp only [mono, zpow_add, ← Units.val_mul, mul_mul_mul_comm]

private theorem mono_pow (α β : ℤ) (n : ℕ) :
    mono p ϖ B α β ^ n = mono p ϖ B (n * α) (n * β) := by
  rw [mono, mono, ← Units.val_pow_eq_pow_val, mul_pow, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, mul_comm α, mul_comm β]

private theorem mono_natCast (α β : ℕ) :
    mono p ϖ B α β = algebraMap (𝕎 O) B (teichmuller p ϖ ^ α * (p : 𝕎 O) ^ β) := by
  simp [mono, map_mul, map_pow]

private theorem mono_zero : mono p ϖ B 0 0 = 1 := by
  simp [mono]

variable (p ϖ B) in
/-- **The fraction `[ϖ] ^ b / p ^ a`** of a localisation `B` of `𝕎 O` away from `p [ϖ]`, for
`q = a / b` in lowest terms. Since `p` is a unit of `B`, a valuation `w` on `B` has `w(x) ≤ 1` at
this fraction `x` exactly when `w([ϖ]) ^ b ≤ w(p) ^ a`, the lower radius bound `q ≤ κ(w)`. -/
noncomputable def radiusLowerFrac (q : ℚ≥0) : B :=
  mono p ϖ B q.den (-q.num)

variable (p ϖ B) in
/-- **The fraction `p ^ a' / [ϖ] ^ b'`** of a localisation `B` of `𝕎 O` away from `p [ϖ]`, for
`q' = a' / b'` in lowest terms. Since `[ϖ]` is a unit of `B`, a valuation `w` on `B` has
`w(x) ≤ 1` at this fraction `x` exactly when `w(p) ^ a' ≤ w([ϖ]) ^ b'`, the upper radius bound
`κ(w) ≤ q'`. -/
noncomputable def radiusUpperFrac (q' : ℚ≥0) : B :=
  mono p ϖ B (-q'.den) q'.num

/-- **The defining equation of `[ϖ] ^ b / p ^ a`**: its product with `p ^ a` is `[ϖ] ^ b`. It
determines the fraction, since `p` is a unit of `B`. -/
theorem radiusLowerFrac_mul_algebraMap (q : ℚ≥0) :
    radiusLowerFrac p ϖ B q * algebraMap (𝕎 O) B ((p : 𝕎 O) ^ q.num) =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ q.den) := by
  have h₁ := mono_natCast (p := p) (ϖ := ϖ) (B := B) 0 q.num
  have h₂ := mono_natCast (p := p) (ϖ := ϖ) (B := B) q.den 0
  simp only [pow_zero, one_mul, mul_one, Nat.cast_zero] at h₁ h₂
  rw [radiusLowerFrac, ← h₁, ← h₂, ← mono_add]
  simp

/-- **The defining equation of `p ^ a' / [ϖ] ^ b'`**: its product with `[ϖ] ^ b'` is `p ^ a'`. It
determines the fraction, since `[ϖ]` is a unit of `B`. -/
theorem radiusUpperFrac_mul_algebraMap (q' : ℚ≥0) :
    radiusUpperFrac p ϖ B q' * algebraMap (𝕎 O) B (teichmuller p ϖ ^ q'.den) =
      algebraMap (𝕎 O) B ((p : 𝕎 O) ^ q'.num) := by
  have h₁ := mono_natCast (p := p) (ϖ := ϖ) (B := B) q'.den 0
  have h₂ := mono_natCast (p := p) (ϖ := ϖ) (B := B) 0 q'.num
  simp only [pow_zero, one_mul, mul_one, Nat.cast_zero] at h₁ h₂
  rw [radiusUpperFrac, ← h₁, ← h₂, ← mono_add]
  simp

variable (p ϖ B) in
/-- **The window subring `𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']`** of a localisation `B` of
`𝕎 O` away from `p [ϖ]`, for `q = a / b` and `q' = a' / b'` in lowest terms: the subring generated
over `𝕎 O` by `radiusLowerFrac p ϖ B q` and `radiusUpperFrac p ϖ B q'`. This is the ring
`A₀[T / s]`, for `A₀ = 𝕎 O`, that the rational localisation of `𝕎 O` at the window
`{q ≤ κ ≤ q'}`, presented by these two fractions, carries as its ring of definition. -/
noncomputable def windowSubring (q q' : ℚ≥0) : Subring B :=
  (Algebra.adjoin (𝕎 O) {radiusLowerFrac p ϖ B q, radiusUpperFrac p ϖ B q'}).toSubring

variable {q q' : ℚ≥0}

/-- The window subring is the subring generated by the two fractions over `𝕎 O`. -/
theorem windowSubring_def :
    windowSubring p ϖ B q q' =
      (Algebra.adjoin (𝕎 O) {radiusLowerFrac p ϖ B q, radiusUpperFrac p ϖ B q'}).toSubring :=
  (rfl)

/-- The image of `𝕎 O` lies in the window subring. -/
@[simp]
theorem algebraMap_mem_windowSubring (x : 𝕎 O) :
    algebraMap (𝕎 O) B x ∈ windowSubring p ϖ B q q' :=
  Subalgebra.algebraMap_mem _ x

/-- The fraction `[ϖ] ^ b / p ^ a` lies in the window subring. -/
@[simp]
theorem radiusLowerFrac_mem_windowSubring :
    radiusLowerFrac p ϖ B q ∈ windowSubring p ϖ B q q' :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

/-- The fraction `p ^ a' / [ϖ] ^ b'` lies in the window subring. -/
@[simp]
theorem radiusUpperFrac_mem_windowSubring :
    radiusUpperFrac p ϖ B q' ∈ windowSubring p ϖ B q q' :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

/-- **The universal property of the window subring**: it lies in a subring `S` of `B` exactly
when `S` contains the image of `𝕎 O` and the two fractions. -/
theorem windowSubring_le_iff {S : Subring B} :
    windowSubring p ϖ B q q' ≤ S ↔ (∀ x, algebraMap (𝕎 O) B x ∈ S) ∧
      radiusLowerFrac p ϖ B q ∈ S ∧ radiusUpperFrac p ϖ B q' ∈ S := by
  refine ⟨fun h ↦ ⟨fun x ↦ h (algebraMap_mem_windowSubring x),
    h radiusLowerFrac_mem_windowSubring, h radiusUpperFrac_mem_windowSubring⟩,
    fun ⟨h₀, hf, hg⟩ ↦ ?_⟩
  -- `S` is a `𝕎 O`-subalgebra, since it contains the image of `𝕎 O`
  let S' : Subalgebra (𝕎 O) B := { S with algebraMap_mem' := h₀ }
  have hle : Algebra.adjoin (𝕎 O) {radiusLowerFrac p ϖ B q, radiusUpperFrac p ϖ B q'} ≤ S' :=
    Algebra.adjoin_le (Set.insert_subset_iff.mpr ⟨hf, Set.singleton_subset_iff.mpr hg⟩)
  exact fun x hx ↦ hle hx

/-- A Laurent monomial `[ϖ] ^ α p ^ β` with `(α, β) = i (b, -a) + j (-b', a') + (k, l)`,
`i, j, k, l ≥ 0`, times an element of `𝕎 O`, lies in the window subring: it is
`u (radiusLowerFrac q) ^ i (radiusUpperFrac q') ^ j [ϖ] ^ k p ^ l`. -/
private theorem algebraMap_mul_mono_mem_windowSubring (u : 𝕎 O) (i j k l : ℕ) {α β : ℤ}
    (hα : α = i * q.den - j * q'.den + k) (hβ : β = -(i * q.num) + j * q'.num + l) :
    algebraMap (𝕎 O) B u * mono p ϖ B α β ∈ windowSubring p ϖ B q q' := by
  have h : mono p ϖ B α β =
      radiusLowerFrac p ϖ B q ^ i * radiusUpperFrac p ϖ B q' ^ j * mono p ϖ B k l := by
    rw [radiusLowerFrac, radiusUpperFrac, mono_pow, mono_pow, ← mono_add, ← mono_add, hα, hβ]
    congr 1 <;> ring
  rw [h, mono_natCast]
  exact Subring.mul_mem _ (algebraMap_mem_windowSubring u) (Subring.mul_mem _
    (Subring.mul_mem _ (Subring.pow_mem _ radiusLowerFrac_mem_windowSubring i)
      (Subring.pow_mem _ radiusUpperFrac_mem_windowSubring j)) (algebraMap_mem_windowSubring _))

/-- Every element of `B` is `y / (p [ϖ]) ^ m` for some `y ∈ 𝕎 O`. -/
private theorem exists_eq_algebraMap_mul_mono (x : B) :
    ∃ (m : ℕ) (y : 𝕎 O), x * algebraMap (𝕎 O) B (((p : 𝕎 O) * teichmuller p ϖ) ^ m) =
      algebraMap (𝕎 O) B y ∧ x = algebraMap (𝕎 O) B y * mono p ϖ B (-m) (-m) := by
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj ((p : 𝕎 O) * teichmuller p ϖ) x
  rw [← map_pow] at hy
  refine ⟨m, y, hy, ?_⟩
  have hm : algebraMap (𝕎 O) B (((p : 𝕎 O) * teichmuller p ϖ) ^ m) = mono p ϖ B m m := by
    rw [mono_natCast, mul_pow, mul_comm]
  rw [← hy, hm, mul_assoc, ← mono_add]
  simp [mono_zero]

private theorem mono_natCast_zero_left (β : ℕ) :
    mono p ϖ B 0 β = algebraMap (𝕎 O) B ((p : 𝕎 O) ^ β) := by
  simpa using mono_natCast (p := p) (ϖ := ϖ) (B := B) 0 β

private theorem mono_natCast_zero_right (α : ℕ) :
    mono p ϖ B α 0 = algebraMap (𝕎 O) B (teichmuller p ϖ ^ α) := by
  simpa using mono_natCast (p := p) (ϖ := ϖ) (B := B) α 0

/-- If `ϖ ^ e` divides `y ϖ ^ c` in `O`, then `[y] = [u] [ϖ] ^ (e - c)` in `B` for some `u ∈ O`. -/
private theorem exists_algebraMap_teichmuller_eq {y : O} {e c : ℕ}
    (h : ϖ ^ e ∣ y * ϖ ^ c) :
    ∃ u : O, algebraMap (𝕎 O) B (teichmuller p y) =
      algebraMap (𝕎 O) B (teichmuller p u) * mono p ϖ B ((e : ℤ) - c) 0 := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have hc := mono_natCast (p := p) (ϖ := ϖ) (B := B) c 0
  have he := mono_natCast (p := p) (ϖ := ϖ) (B := B) e 0
  simp only [pow_zero, mul_one, Nat.cast_zero] at hc he
  -- `[y] [ϖ] ^ c = [u] [ϖ] ^ e`, and `[ϖ] ^ c` is a unit
  have hyu : algebraMap (𝕎 O) B (teichmuller p y) * mono p ϖ B c 0 =
      algebraMap (𝕎 O) B (teichmuller p u) * mono p ϖ B e 0 := by
    rw [hc, he, ← map_mul, ← map_mul, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hu, mul_comm]
  calc algebraMap (𝕎 O) B (teichmuller p y)
      = algebraMap (𝕎 O) B (teichmuller p y) * mono p ϖ B c 0 * mono p ϖ B (-c) 0 := by
        rw [mul_assoc, ← mono_add]; simp [mono_zero]
    _ = _ := by rw [hyu, mul_assoc, ← mono_add]; simp [sub_eq_add_neg]

/-- `[ϖ] ^ N` times `u [ϖ] ^ γ p ^ δ / (p [ϖ]) ^ m` is `u [ϖ] ^ (N + γ - m) p ^ (δ - m)`. -/
private theorem mono_mul_algebraMap_mul_mono_mul_mono (N : ℕ) (u : 𝕎 O) (γ δ : ℤ) (m : ℕ) :
    mono p ϖ B N 0 * (algebraMap (𝕎 O) B u * mono p ϖ B γ δ * mono p ϖ B (-m) (-m)) =
      algebraMap (𝕎 O) B u * mono p ϖ B (N + γ - m) (δ - m) := by
  rw [mul_left_comm, mul_assoc, ← mono_add, ← mono_add]
  congr 2 <;> ring

end Away

section Interval

variable {p ϖ} {K : Type*} [Field K] [Algebra O K] {v : Valuation K ℝ≥0}
  [CharP O p] [PerfectRing O p] {q q' : ℚ≥0}

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

/-- A bound `λ_ρ(x) ≤ 1` on `x = y / (p [ϖ]) ^ m` bounds the Teichmüller coordinates of `y`:
`v(yₙ) ρ ^ n ≤ (ρ v(ϖ)) ^ m`. -/
private theorem valuation_teichmullerCoeff_mul_pow_le {B : Type*} [CommRing B]
    [Algebra (𝕎 O) B] [IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ) B] {ρ : ℝ≥0}
    (hρ : ρ ∈ Set.Ioo 0 1) {x : B} (hx : gaussValuationAway p hv hϖ ρ hρ B x ≤ 1) {m : ℕ}
    {y : 𝕎 O}
    (hy : x * algebraMap (𝕎 O) B (((p : 𝕎 O) * teichmuller p ϖ) ^ m) = algebraMap (𝕎 O) B y)
    (n : ℕ) :
    v (algebraMap O K (y.teichmullerCoeff n)) * ρ ^ n ≤ (ρ * v (algebraMap O K ϖ)) ^ m := by
  have h := congrArg (gaussValuationAway p hv hϖ ρ hρ B) hy
  rw [map_mul, gaussValuationAway_algebraMap, gaussValuationAway_algebraMap, map_pow, map_mul,
    gaussValuation_p, gaussValuation_teichmuller] at h
  calc v (algebraMap O K (y.teichmullerCoeff n)) * ρ ^ n ≤ gaussValuation p hv ρ hρ.2 y :=
        le_gaussValuation hv hρ.2 y n
    _ = _ := h.symm
    _ ≤ (ρ * v (algebraMap O K ϖ)) ^ m := mul_le_of_le_one_left zero_le hx

omit [CharP O p] [PerfectRing O p] in
/-- Rewriting `[c] = [u] [ϖ] ^ e` in a term `[c] pⁱ / (p [ϖ]) ^ m`. -/
private theorem algebraMap_teichmuller_mul_pow_mul_mono_eq {B : Type*} [CommRing B]
    [Algebra (𝕎 O) B] [IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ) B] {c u : O} {e : ℤ}
    (hu : algebraMap (𝕎 O) B (teichmuller p c) =
      algebraMap (𝕎 O) B (teichmuller p u) * mono p ϖ B e 0) (i m : ℕ) :
    algebraMap (𝕎 O) B (teichmuller p c * (p : 𝕎 O) ^ i) * mono p ϖ B (-m) (-m) =
      algebraMap (𝕎 O) B (teichmuller p u) * mono p ϖ B e i * mono p ϖ B (-m) (-m) := by
  rw [map_mul, hu, ← mono_natCast_zero_left (ϖ := ϖ), mul_assoc _ (mono p ϖ B e 0),
    ← mono_add]
  simp

omit [CharP O p] [PerfectRing O p] in
include hv hρ₁ in
/-- **A term with a negative power of `p` lies in the window subring, up to `[ϖ] ^ (b + b')`.**
If `i < m` and `v(c) ρ₁ ^ i ≤ (ρ₁ v(ϖ)) ^ m`, then writing `m - i = j a + r` with `r < a`, the
bound makes `ϖ ^ (m + j b)` divide `c = ϖ ^ (m + j b) u`, and
`[ϖ] ^ (b + b') [c] pⁱ / (p [ϖ]) ^ m = [u] ([ϖ] ^ b / p ^ a) ^ (j + 1) [ϖ] ^ b' p ^ (a - r)`. -/
private theorem mono_mul_algebraMap_teichmuller_mul_pow_mem_windowSubring_of_lt {B : Type*}
    [CommRing B] [Algebra (𝕎 O) B] [IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ) B]
    (h₁ : ρ₁ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den) (ha : 0 < q.num) {c : O} {i m : ℕ}
    (hi : i < m) (hb₁ : v (algebraMap O K c) * ρ₁ ^ i ≤ (ρ₁ * v (algebraMap O K ϖ)) ^ m) :
    mono p ϖ B (q.den + q'.den : ℕ) 0 * (algebraMap (𝕎 O) B (teichmuller p c * (p : 𝕎 O) ^ i) *
      mono p ϖ B (-m) (-m)) ∈ windowSubring p ϖ B q q' := by
  obtain ⟨j, r, hr, hm⟩ : ∃ j r, r < q.num ∧ m = i + (q.num * j + r) :=
    ⟨(m - i) / q.num, (m - i) % q.num, Nat.mod_lt _ ha, by rw [Nat.div_add_mod]; omega⟩
  have hle : v (algebraMap O K c) ≤ v (algebraMap O K ϖ) ^ (m + j * q.den) := by
    have h' : v (algebraMap O K c) * ρ₁ ^ i ≤
        ρ₁ ^ (q.num * j + r) * v (algebraMap O K ϖ) ^ m * ρ₁ ^ i := by
      calc _ ≤ _ := hb₁
        _ = _ := by rw [mul_pow, hm, pow_add]; ring
    calc v (algebraMap O K c) ≤ ρ₁ ^ (q.num * j + r) * v (algebraMap O K ϖ) ^ m :=
          le_of_mul_le_mul_right h' (pow_pos hρ₁.1 i)
      _ ≤ ρ₁ ^ (q.num * j) * v (algebraMap O K ϖ) ^ m :=
          mul_le_mul_left (pow_le_pow_of_le_one zero_le hρ₁.2.le (Nat.le_add_right _ _)) _
      _ ≤ (v (algebraMap O K ϖ) ^ q.den) ^ j * v (algebraMap O K ϖ) ^ m := by
          rw [pow_mul]; gcongr
      _ = _ := by ring
  obtain ⟨u, hu⟩ := exists_algebraMap_teichmuller_eq (p := p) (B := B)
    (hv.dvd_of_le (x := c * ϖ ^ 0) (y := ϖ ^ (m + j * q.den)) (by simpa using hle))
  rw [algebraMap_teichmuller_mul_pow_mul_mono_eq hu, mono_mul_algebraMap_mul_mono_mul_mono]
  have hm' : (m : ℤ) = i + (q.num * j + r) := by exact_mod_cast hm
  refine algebraMap_mul_mono_mem_windowSubring _ (j + 1) 0 q'.den (q.num - r) ?_ ?_
  · push_cast; ring
  · push_cast [Nat.cast_sub hr.le]; linear_combination -hm'

omit [CharP O p] [PerfectRing O p] in
include hv hρ₂ in
/-- **A term with a nonnegative power of `p` lies in the window subring, up to
`[ϖ] ^ (b + b')`.** If `m ≤ i` and `v(c) ρ₂ ^ i ≤ (ρ₂ v(ϖ)) ^ m`, then writing `i - m = j a' + r`
with `r < a'`, the bound makes `ϖ ^ m` divide `c ϖ ^ ((j + 1) b') = ϖ ^ m u`, and
`[ϖ] ^ (b + b') [c] pⁱ / (p [ϖ]) ^ m = [u] (p ^ a' / [ϖ] ^ b') ^ j [ϖ] ^ b p ^ r`. -/
private theorem mono_mul_algebraMap_teichmuller_mul_pow_mem_windowSubring_of_le {B : Type*}
    [CommRing B] [Algebra (𝕎 O) B] [IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ) B]
    (h₂ : v (algebraMap O K ϖ) ^ q'.den ≤ ρ₂ ^ q'.num) (ha' : 0 < q'.num) {c : O} {i m : ℕ}
    (hi : m ≤ i) (hb₂ : v (algebraMap O K c) * ρ₂ ^ i ≤ (ρ₂ * v (algebraMap O K ϖ)) ^ m) :
    mono p ϖ B (q.den + q'.den : ℕ) 0 * (algebraMap (𝕎 O) B (teichmuller p c * (p : 𝕎 O) ^ i) *
      mono p ϖ B (-m) (-m)) ∈ windowSubring p ϖ B q q' := by
  obtain ⟨j, r, hr, hi'⟩ : ∃ j r, r < q'.num ∧ i = m + (q'.num * j + r) :=
    ⟨(i - m) / q'.num, (i - m) % q'.num, Nat.mod_lt _ ha', by rw [Nat.div_add_mod]; omega⟩
  have hle : v (algebraMap O K c) * v (algebraMap O K ϖ) ^ ((j + 1) * q'.den) ≤
      v (algebraMap O K ϖ) ^ m := by
    have h' : v (algebraMap O K c) * ρ₂ ^ (q'.num * j + r) * ρ₂ ^ m ≤
        v (algebraMap O K ϖ) ^ m * ρ₂ ^ m := by
      calc _ = v (algebraMap O K c) * ρ₂ ^ i := by rw [hi', pow_add]; ring
        _ ≤ _ := hb₂
        _ = _ := by rw [mul_pow]; ring
    have hpow : v (algebraMap O K ϖ) ^ ((j + 1) * q'.den) ≤ ρ₂ ^ (q'.num * j + r) := by
      calc v (algebraMap O K ϖ) ^ ((j + 1) * q'.den)
          = (v (algebraMap O K ϖ) ^ q'.den) ^ j * v (algebraMap O K ϖ) ^ q'.den := by ring
        _ ≤ (ρ₂ ^ q'.num) ^ j * ρ₂ ^ q'.num := by gcongr
        _ ≤ ρ₂ ^ (q'.num * j) * ρ₂ ^ r := by
            rw [← pow_mul, mul_comm q'.num j]
            exact mul_le_mul_right (pow_le_pow_of_le_one zero_le hρ₂.2.le hr.le) _
        _ = _ := by rw [pow_add]
    calc _ ≤ v (algebraMap O K c) * ρ₂ ^ (q'.num * j + r) := by gcongr
      _ ≤ _ := le_of_mul_le_mul_right h' (pow_pos hρ₂.1 m)
  obtain ⟨u, hu⟩ := exists_algebraMap_teichmuller_eq (p := p) (B := B)
    (hv.dvd_of_le (x := c * ϖ ^ ((j + 1) * q'.den)) (y := ϖ ^ m) (by simpa using hle))
  rw [algebraMap_teichmuller_mul_pow_mul_mono_eq hu, mono_mul_algebraMap_mul_mono_mul_mono]
  have hi'' : (i : ℤ) = m + (q'.num * j + r) := by exact_mod_cast hi'
  refine algebraMap_mul_mono_mem_windowSubring _ 0 j q.den r ?_ ?_
  · push_cast; ring
  · push_cast; linear_combination hi''

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

/-- **The unit ball of the interval norm lies in the window subring, up to `[ϖ] ^ (b + b')`.**
If `ρ₁ ^ a ≤ v(ϖ) ^ b` and `v(ϖ) ^ b' ≤ ρ₂ ^ a'` for `q = a / b` and `q' = a' / b' ≠ 0` in lowest
terms, then `[ϖ] ^ (b + b') x ∈ 𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']` for every `x` with
`λ_I(x) ≤ 1`. -/
theorem algebraMap_teichmuller_pow_mul_mem_windowSubring_of_norm_le_one
    (h₁ : ρ₁ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den)
    (h₂ : v (algebraMap O K ϖ) ^ q'.den ≤ ρ₂ ^ q'.num) (hq' : q' ≠ 0) {x : L} (hx : ‖x‖ ≤ 1) :
    algebraMap (𝕎 O) L (teichmuller p ϖ ^ (q.den + q'.den)) * x ∈ windowSubring p ϖ L q q' := by
  have ha : 0 < q.num := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    rw [h, pow_zero] at h₁
    exact (pow_lt_one₀ zero_le hϖ' q.den_ne_zero).not_ge h₁
  have ha' : 0 < q'.num := NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hq')
  -- the two Gauss valuations of `x` are at most `1`
  rw [IntervalLocalization.norm_def] at hx
  have hx₁ : gaussValuationAway p hv hϖ ρ₁ hρ₁ L x ≤ 1 := by
    exact_mod_cast (le_max_left _ _).trans hx
  have hx₂ : gaussValuationAway p hv hϖ ρ₂ hρ₂ L x ≤ 1 := by
    exact_mod_cast (le_max_right _ _).trans hx
  obtain ⟨m, y, hy, rfl⟩ := exists_eq_algebraMap_mul_mono (p := p) (ϖ := ϖ) x
  -- the Teichmüller expansion `y = ∑_{i ≤ M} [yᵢ] pⁱ + p ^ (M + 1) z`, with `M = m a' + m`
  obtain ⟨z, hz⟩ := pow_dvd_sub_sum_teichmullerCoeff y (m * q'.num + m)
  have hy' : y = ∑ i ≤ m * q'.num + m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i +
      (p : 𝕎 O) ^ (m * q'.num + m + 1) * z := by
    rw [← hz]; ring
  rw [← mono_natCast_zero_right, hy', map_add, map_sum, add_mul, Finset.sum_mul, mul_add,
    Finset.mul_sum]
  refine Subring.add_mem _ (Subring.sum_mem _ fun i _ ↦ ?_) ?_
  · rcases lt_or_ge i m with hi | hi
    · exact mono_mul_algebraMap_teichmuller_mul_pow_mem_windowSubring_of_lt hv hρ₁ h₁ ha hi
        (valuation_teichmullerCoeff_mul_pow_le hv hϖ hρ₁ hx₁ hy i)
    · exact mono_mul_algebraMap_teichmuller_mul_pow_mem_windowSubring_of_le hv hρ₂ h₂ ha' hi
        (valuation_teichmullerCoeff_mul_pow_le hv hϖ hρ₂ hx₂ hy i)
  · -- the tail `p ^ (M + 1) z / (p [ϖ]) ^ m` is
    -- `z (p ^ a' / [ϖ] ^ b') ^ m [ϖ] ^ (b + b' + m (b' - 1)) p`
    have htail : algebraMap (𝕎 O) L ((p : 𝕎 O) ^ (m * q'.num + m + 1) * z) =
        algebraMap (𝕎 O) L z * mono p ϖ L 0 (m * q'.num + m + 1 : ℕ) := by
      rw [mono_natCast_zero_left, ← map_mul, mul_comm]
    rw [htail, mono_mul_algebraMap_mul_mono_mul_mono]
    refine algebraMap_mul_mono_mem_windowSubring _ 0 m (q.den + q'.den + m * (q'.den - 1)) 1 ?_ ?_
    · push_cast [Nat.cast_sub q'.den_pos]; ring
    · push_cast; ring

/-- **The window subring is open for the interval norm**, if `ρ₁ ^ a ≤ v(ϖ) ^ b` and
`v(ϖ) ^ b' ≤ ρ₂ ^ a'` for `q = a / b` and `q' = a' / b' ≠ 0` in lowest terms: it contains every `x`
with `λ_I(x)` small. -/
theorem isOpen_windowSubring (h₁ : ρ₁ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den)
    (h₂ : v (algebraMap O K ϖ) ^ q'.den ≤ ρ₂ ^ q'.num) (hq' : q' ≠ 0) :
    IsOpen (windowSubring p ϖ L q q' : Set L) := by
  set N := q.den + q'.den
  set k := N * q'.num
  -- `x = ([ϖ] ^ N x') ([ϖ] ^ -N p ^ k)` with `x' = x / p ^ k`, and `[ϖ] ^ -N p ^ k` is
  -- `(p ^ a' / [ϖ] ^ b') ^ N [ϖ] ^ (N (b' - 1))`
  have hmem : ∀ x : L, ‖x‖ < min ((ρ₁ : ℝ) ^ k) ((ρ₂ : ℝ) ^ k) →
      x ∈ windowSubring p ϖ L q q' := by
    intro x hx
    set x' := x * mono p ϖ L 0 (-k)
    have hxx' : x = x' * algebraMap (𝕎 O) L ((p : 𝕎 O) ^ k) := by
      rw [← mono_natCast_zero_left (ϖ := ϖ), mul_assoc, ← mono_add]
      simp [mono_zero]
    have hlam {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1)
        (hlt : (gaussValuationAway p hv hϖ ρ hρ L x : ℝ) < ρ ^ k) :
        gaussValuationAway p hv hϖ ρ hρ L x' ≤ 1 := by
      have e := congrArg (gaussValuationAway p hv hϖ ρ hρ L) hxx'
      rw [map_mul, gaussValuationAway_algebraMap, map_pow, gaussValuation_p] at e
      rw [e] at hlt
      exact_mod_cast ((mul_lt_iff_lt_one_left (pow_pos (by exact_mod_cast hρ.1) k)).mp
        (by exact_mod_cast hlt)).le
    have hx' : ‖x'‖ ≤ 1 := by
      rw [IntervalLocalization.norm_def] at hx ⊢
      rw [lt_min_iff, max_lt_iff, max_lt_iff] at hx
      exact max_le (by exact_mod_cast hlam hρ₁ hx.1.1) (by exact_mod_cast hlam hρ₂ hx.2.2)
    have hN := algebraMap_teichmuller_pow_mul_mem_windowSubring_of_norm_le_one hv hϖ hϖ' hρ₁ hρ₂
      h₁ h₂ hq' hx'
    have hx_eq : x = algebraMap (𝕎 O) L (teichmuller p ϖ ^ N) * x' *
        (algebraMap (𝕎 O) L 1 * mono p ϖ L (-N) k) := by
      rw [map_one, one_mul, ← mono_natCast_zero_right (p := p), mul_comm _ x', mul_assoc,
        ← mono_add]
      simp [x', mul_assoc, ← mono_add, mono_zero]
    rw [hx_eq]
    refine Subring.mul_mem _ hN (algebraMap_mul_mono_mem_windowSubring 1 0 N (N * (q'.den - 1)) 0
      ?_ ?_)
    · push_cast [Nat.cast_sub q'.den_pos]; ring
    · simp [k]
  refine AddSubgroup.isOpen_of_mem_nhds (windowSubring p ϖ L q q').toAddSubgroup
    (g := 0) (Filter.mem_of_superset (Metric.ball_mem_nhds 0 (lt_min ?_ ?_)) fun x hx ↦
      hmem x (by simpa using hx))
  · exact pow_pos (by exact_mod_cast hρ₁.1) k
  · exact pow_pos (by exact_mod_cast hρ₂.1) k

/-- The interval norm of a fraction `x` with `x y' = y` is at most `1` when `λ_{ρᵢ}(y) ≤ λ_{ρᵢ}(y')`
at both radii. -/
private theorem norm_le_one_of_mul_algebraMap_eq {x : L} {y y' : 𝕎 O}
    (h : x * algebraMap (𝕎 O) L y' = algebraMap (𝕎 O) L y)
    (hy₁ : gaussValuation p hv ρ₁ hρ₁.2 y ≤ gaussValuation p hv ρ₁ hρ₁.2 y')
    (hy₂ : gaussValuation p hv ρ₂ hρ₂.2 y ≤ gaussValuation p hv ρ₂ hρ₂.2 y')
    (hy' : y' ≠ 0) : ‖x‖ ≤ 1 := by
  have hlam {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1)
      (hy : gaussValuation p hv ρ hρ.2 y ≤ gaussValuation p hv ρ hρ.2 y') :
      gaussValuationAway p hv hϖ ρ hρ L x ≤ 1 := by
    have e := congrArg (gaussValuationAway p hv hϖ ρ hρ L) h
    rw [map_mul, gaussValuationAway_algebraMap, gaussValuationAway_algebraMap] at e
    have hpos : 0 < gaussValuation p hv ρ hρ.2 y' :=
      pos_iff_ne_zero.mpr ((gaussValuation_eq_zero_iff hv hρ.1 hρ.2).not.mpr hy')
    exact (mul_le_iff_le_one_left hpos).mp (e ▸ hy)
  rw [IntervalLocalization.norm_def]
  exact max_le (by exact_mod_cast hlam hρ₁ hy₁) (by exact_mod_cast hlam hρ₂ hy₂)

/-- **The window subring is bounded for the interval norm**, if `v(ϖ) ^ b ≤ ρᵢ ^ a` and
`ρᵢ ^ a' ≤ v(ϖ) ^ b'` at both radii, for `q = a / b` and `q' = a' / b'` in lowest terms: then both
fractions, and so the whole window subring, lie in the unit ball of `λ_I`. -/
theorem isBounded_windowSubring (hf₁ : v (algebraMap O K ϖ) ^ q.den ≤ ρ₁ ^ q.num)
    (hf₂ : v (algebraMap O K ϖ) ^ q.den ≤ ρ₂ ^ q.num)
    (hg₁ : ρ₁ ^ q'.num ≤ v (algebraMap O K ϖ) ^ q'.den)
    (hg₂ : ρ₂ ^ q'.num ≤ v (algebraMap O K ϖ) ^ q'.den) :
    IsBounded (windowSubring p ϖ L q q' : Set L) := by
  -- the unit ball of `λ_I` is the power-bounded subring, since `λ_I` is power-multiplicative
  have hball : (powerBoundedSubring L : Set L) = Metric.closedBall 0 1 :=
    IsPseudoUniformizer.coe_powerBoundedSubring_eq_closedBall
      (IsPseudoUniformizer.of_norm_lt_one (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂)
        (IntervalLocalization.norm_natCast_lt_one p hv hϖ hϖ' hρ₁ hρ₂))
      (IntervalLocalization.isPowMul_norm p hv hϖ hϖ' hρ₁ hρ₂)
  have hmem {x : L} (hx : ‖x‖ ≤ 1) : x ∈ powerBoundedSubring L := by
    rw [← SetLike.mem_coe, hball, mem_closedBall_zero_iff]
    exact hx
  refine (isBounded_closedBall_zero 1).subset (hball ▸ ?_)
  refine windowSubring_le_iff.mpr ⟨fun x ↦ hmem ?_, hmem ?_, hmem ?_⟩
  · rw [IntervalLocalization.norm_algebraMap]
    exact max_le (by exact_mod_cast gaussValuation_le_one hv hρ₁.2 x)
      (by exact_mod_cast gaussValuation_le_one hv hρ₂.2 x)
  · refine norm_le_one_of_mul_algebraMap_eq hv hϖ hϖ' hρ₁ hρ₂
      (radiusLowerFrac_mul_algebraMap q) ?_ ?_ fun h ↦ ?_
    · simpa using hf₁
    · simpa using hf₂
    · simpa [hρ₁.1.ne'] using congrArg (gaussValuation p hv ρ₁ hρ₁.2) h
  · refine norm_le_one_of_mul_algebraMap_eq hv hϖ hϖ' hρ₁ hρ₂
      (radiusUpperFrac_mul_algebraMap q') ?_ ?_ fun h ↦ ?_
    · simpa using hg₁
    · simpa using hg₂
    · simpa [map_eq_zero_iff _ hv.hom_inj, hϖ] using congrArg (gaussValuation p hv ρ₁ hρ₁.2) h

/-- **The window subring is a ring of definition for the interval norm.** If the radii are those
of the window `{q ≤ κ ≤ q'}`, that is `ρ₁ ^ a = v(ϖ) ^ b`, `ρ₂ ^ a' = v(ϖ) ^ b'` and `ρ₁ ≤ ρ₂` for
`q = a / b` and `q' = a' / b'` in lowest terms, then `𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']` is
a ring of definition of `𝕎 O[1/(p [ϖ])]` with the interval norm `λ_I`. So `λ_I` defines the
topology of the rational localisation of `𝕎 O` at the window. -/
theorem exists_pairOfDefinition_ringOfDefinition_eq_windowSubring
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    ∃ P : PairOfDefinition L, P.ringOfDefinition = windowSubring p ϖ L q q' := by
  have hq' : q' ≠ 0 := by
    rintro rfl
    simp only [NNRat.num_zero, pow_zero, NNRat.den_zero, pow_one] at h₂
    exact hϖ'.ne' h₂
  exact exists_pairOfDefinition_ringOfDefinition_eq _
    (isOpen_windowSubring hv hϖ hϖ' hρ₁ hρ₂ h₁.le h₂.ge hq')
    (isBounded_windowSubring hv hϖ hϖ' hρ₁ hρ₂ h₁.ge (h₁ ▸ pow_le_pow_left₀ zero_le h₁₂ _)
      (h₂ ▸ pow_le_pow_left₀ zero_le h₁₂ _) h₂.le)

end Interval

end TauCeti.WittVector
