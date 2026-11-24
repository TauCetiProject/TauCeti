/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.WittVector.Isocrystal

/-!
# The standard Frobenius blocks `D(s, r)`

Let `L` be a field with a field automorphism `σ`, and let `π ∈ L`. For `s : ℤ` and `r : ℕ`, the
standard block `D(s, r)` is the `L`-vector space `L^r` with the `σ`-semilinear Frobenius which
cycles through the standard basis and multiplies the wraparound by `π ^ s`:
`Φ(e_i) = e_(i+1)` for `i < r - 1` and `Φ(e_(r-1)) = π ^ s • e_0`. This file defines that
Frobenius, `TauCeti.standardBlockFrobenius σ π s r`, and proves its basic properties.

In the motivating case `L` is the completion of the maximal unramified extension of a
nonarchimedean local field `E` with uniformizer `π`, or `k((π))` in equal characteristic, and `σ`
is the arithmetic `q`-Frobenius, which fixes `π`. The block `D(s, r)` is then an isocrystal of
slope `s / r`, and the Dieudonné–Manin classification says that over an algebraically closed
residue field every finite isocrystal is a direct sum of blocks `D(s, r)` with `s` and `r`
coprime. Under the functor from isocrystals to vector bundles on the Fargues–Fontaine curve,
`D(-d, h)` goes to the standard bundle `𝒪(d / h)`.

## Main definitions

* `TauCeti.standardBlockFrobenius σ π s r`: the `σ`-semilinear Frobenius of `D(s, r)` on
  `Fin r → L`.

## Main results

* `TauCeti.standardBlockFrobenius_single_castSucc`, `TauCeti.standardBlockFrobenius_single_last`:
  the Frobenius on the standard basis, including the `π ^ s` wraparound.
* `TauCeti.standardBlockFrobenius_bijective`: the Frobenius is bijective when `π ≠ 0`, so `D(s, r)`
  is an isocrystal.
* `TauCeti.standardBlockFrobenius_iterate_rank_apply`: if `σ` fixes `π`, then
  `Φ ^ r = π ^ s • σ ^ r`, with `σ ^ r` acting on coordinates.
* `TauCeti.eq_zero_of_intertwines_standardBlock`: if `σ` fixes `π ≠ 0` and preserves a valuation
  `v` with `v π ≠ 1`, there is no nonzero Frobenius-equivariant `L`-linear map `D(s, r) → D(s', r')`
  between blocks of different slopes `s / r ≠ s' / r'`.
* `TauCeti.standardBlockFrobenius_one_apply_zero_eq_frobenius`: for Witt vectors, the rank-one block
  `D(m, 1)` with `π = p` is Mathlib's `WittVector.StandardOneDimIsocrystal p k m`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, before Proposition 8.2.6.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), Definition 4.1.1
  and Lemma 4.1.2.
-/

public section

open Finset Function

namespace TauCeti

variable {L : Type*} [Field L] (σ : L ≃+* L) (π : L) (s : ℤ) (r : ℕ)

/-- The Frobenius of the standard block `D(s, r)`: the `σ`-semilinear map on `L^r` sending the
standard basis vector `e_i` to `e_(i+1)` for `i < r - 1` and `e_(r-1)` to `π ^ s • e_0`. In
coordinates, `(Φ x)_0 = π ^ s * σ (x_(r-1))` and `(Φ x)_i = σ (x_(i-1))` for `0 < i`. -/
def standardBlockFrobenius : (Fin r → L) →ₛₗ[(σ : L →+* L)] (Fin r → L) where
  toFun x i := (if (i : ℕ) = 0 then π ^ s else 1) * σ (x ((finRotate r).symm i))
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.coe_coe]
    ring

variable {σ π s r}

theorem standardBlockFrobenius_apply (x : Fin r → L) (i : Fin r) :
    standardBlockFrobenius σ π s r x i =
      (if (i : ℕ) = 0 then π ^ s else 1) * σ (x ((finRotate r).symm i)) := (rfl)

@[simp]
theorem standardBlockFrobenius_apply_zero {n : ℕ} (x : Fin (n + 1) → L) :
    standardBlockFrobenius σ π s (n + 1) x 0 = π ^ s * σ (x (Fin.last n)) := by
  rw [standardBlockFrobenius_apply, (finRotate _).symm_apply_eq.2 finRotate_last.symm]
  simp

@[simp]
theorem standardBlockFrobenius_apply_succ {n : ℕ} (x : Fin (n + 1) → L) (i : Fin n) :
    standardBlockFrobenius σ π s (n + 1) x i.succ = σ (x i.castSucc) := by
  have hi : (finRotate (n + 1)).symm i.succ = i.castSucc :=
    (finRotate _).symm_apply_eq.2 (by rw [finRotate_apply, Fin.coeSucc_eq_succ])
  simp [standardBlockFrobenius_apply, hi]

/-- The Frobenius of `D(s, r)` moves the basis vector `e_i` to `e_(i+1)` below the last index. -/
@[simp]
theorem standardBlockFrobenius_single_castSucc {n : ℕ} (i : Fin n) (c : L) :
    standardBlockFrobenius σ π s (n + 1) (Pi.single i.castSucc c) = Pi.single i.succ (σ c) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.castSucc_ne_last, (Fin.succ_ne_zero i).symm]
  · simp [Pi.single_apply, Fin.castSucc_inj, Fin.succ_inj, apply_ite σ]

/-- The Frobenius of `D(s, r)` sends the last basis vector to `π ^ s` times the first one. -/
@[simp]
theorem standardBlockFrobenius_single_last {n : ℕ} (c : L) :
    standardBlockFrobenius σ π s (n + 1) (Pi.single (Fin.last n) c) =
      Pi.single 0 (π ^ s * σ c) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.castSucc_ne_last, Fin.succ_ne_zero]

/-- For `π ≠ 0` the Frobenius of `D(s, r)` is bijective, so `D(s, r)` is an isocrystal. -/
theorem standardBlockFrobenius_bijective (hπ : π ≠ 0) :
    Bijective (standardBlockFrobenius σ π s r) := by
  have hw (i : Fin r) : (if (i : ℕ) = 0 then π ^ s else 1) ≠ 0 := by
    split_ifs
    exacts [zpow_ne_zero s hπ, one_ne_zero]
  refine bijective_iff_has_inverse.2 ⟨fun y j => σ.symm
    ((if (finRotate r j : ℕ) = 0 then π ^ s else 1)⁻¹ * y (finRotate r j)), ?_, ?_⟩
  · intro x
    ext j
    simp only [standardBlockFrobenius_apply, Equiv.symm_apply_apply, inv_mul_cancel_left₀ (hw _),
      RingEquiv.symm_apply_apply]
  · intro y
    ext i
    simp only [standardBlockFrobenius_apply, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      mul_inv_cancel_left₀ (hw _)]

/-! ### Powers of the Frobenius -/

section Iterate

open Fin.NatCast

/-- The `k`-th power of the Frobenius of `D(s, r)` in coordinates: its `i`-th coordinate is
`σ ^ k` of the `(i - k)`-th one, times `π ^ s` for each wraparound. -/
private theorem standardBlockFrobenius_iterate_apply [NeZero r] (hσπ : σ π = π) (k : ℕ)
    (x : Fin r → L) (i : Fin r) :
    (standardBlockFrobenius σ π s r)^[k] x i =
      (∏ t ∈ range k, if ((i - t : Fin r) : ℕ) = 0 then π ^ s else 1) *
        σ^[k] (x (i - k)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hσw (j : Fin r) :
        σ (if (j : ℕ) = 0 then π ^ s else 1) = if (j : ℕ) = 0 then π ^ s else 1 := by
      split_ifs <;> simp [hσπ]
    have hidx (t : ℕ) : i - 1 - (t : Fin r) = i - ((t + 1 : ℕ) : Fin r) := by
      push_cast
      abel
    rw [iterate_succ_apply', standardBlockFrobenius_apply, finRotate_symm_apply, ih, map_mul,
      map_prod, prod_range_succ', ← iterate_succ_apply' σ]
    simp only [hσw, hidx, Nat.cast_zero, sub_zero]
    ring

/-- If `σ` fixes `π`, then the `r`-th power of the Frobenius of `D(s, r)` is `π ^ s • σ ^ r`,
with `σ ^ r` acting on coordinates. -/
theorem standardBlockFrobenius_iterate_rank_apply (hσπ : σ π = π) (x : Fin r → L)
    (i : Fin r) :
    (standardBlockFrobenius σ π s r)^[r] x i = π ^ s * σ^[r] (x i) := by
  have := i.neZero
  rw [standardBlockFrobenius_iterate_apply hσπ, Fin.natCast_self, sub_zero]
  -- Over a full cycle only the step `t = i` wraps around, so the product of factors is `π ^ s`.
  rw [prod_eq_single (i : ℕ)]
  · simp
  · intro t ht hti
    rw [ite_eq_right_iff]
    intro h
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h
    exact (hti (by rw [h, Fin.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ht)])).elim
  · simp

/-- If `σ` fixes `π`, then the `(r * m)`-th power of the Frobenius of `D(s, r)` is
`π ^ (s * m) • σ ^ (r * m)`, with `σ ^ (r * m)` acting on coordinates. -/
theorem standardBlockFrobenius_iterate_rank_mul_apply (hσπ : σ π = π) (m : ℕ) (x : Fin r → L)
    (i : Fin r) :
    (standardBlockFrobenius σ π s r)^[r * m] x i = π ^ (s * m) * σ^[r * m] (x i) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hσs : σ (π ^ s) = π ^ s := by rw [map_zpow₀, hσπ]
    rw [Nat.mul_succ, iterate_add_apply, ih, standardBlockFrobenius_iterate_rank_apply hσπ,
      iterate_map_mul, iterate_fixed hσs, ← iterate_add_apply σ]
    simp only [zpow_mul, zpow_natCast, pow_succ]
    ring

end Iterate

/-! ### Morphisms between blocks of different slopes -/

/-- **Morphisms between blocks of different slopes vanish.** Suppose `σ` fixes `π ≠ 0` and
preserves a valuation `v` with `v π ≠ 1`. If `s / r ≠ s' / r'`, then every `L`-linear map
`D(s, r) → D(s', r')` intertwining the Frobenii is zero. -/
theorem eq_zero_of_intertwines_standardBlock {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation L Γ₀} (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1)
    (hσπ : σ π = π) {s' : ℤ} {r' : ℕ} (hslope : (s : ℚ) / r ≠ (s' : ℚ) / r')
    {f : (Fin r → L) →ₗ[L] (Fin r' → L)}
    (hf : ∀ x, f (standardBlockFrobenius σ π s r x) = standardBlockFrobenius σ π s' r' (f x)) :
    f = 0 := by
  refine (Pi.basisFun L (Fin r)).ext fun j => funext fun i => ?_
  have := j.neZero
  have := i.neZero
  have hexp : s * (r' : ℤ) ≠ s' * r := by
    intro h
    apply hslope
    rw [div_eq_div_iff (by exact_mod_cast NeZero.ne r) (by exact_mod_cast NeZero.ne r')]
    exact_mod_cast h
  set y := f (Pi.basisFun L (Fin r) j)
  -- Compare the `(r * r')`-th powers of the two Frobenii on `e_j`: they are `π ^ (s * r')` and
  -- `π ^ (s' * r)` times the coordinatewise action of `σ ^ (r * r')`, which fixes `e_j`.
  have hx : (standardBlockFrobenius σ π s r)^[r * r'] (Pi.basisFun L (Fin r) j) =
      π ^ (s * r') • Pi.basisFun L (Fin r) j := by
    ext l
    rw [standardBlockFrobenius_iterate_rank_mul_apply hσπ, Pi.smul_apply, smul_eq_mul,
      Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp
  have hsc : Semiconj f (standardBlockFrobenius σ π s r) (standardBlockFrobenius σ π s' r') := hf
  have hy : π ^ (s * r') * y i = π ^ (s' * r) * σ^[r * r'] (y i) := by
    have := congrFun (hsc.iterate_right (r * r') (Pi.basisFun L (Fin r) j)) i
    rw [hx, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm r r',
      standardBlockFrobenius_iterate_rank_mul_apply hσπ] at this
    rwa [mul_comm r' r] at this
  -- Taking valuations, a nonzero coordinate of `y` would force `s * r' = s' * r`.
  by_contra hyi
  apply hexp
  have hv' := congrArg v hy
  have hvσ : v (σ^[r * r'] (y i)) = v (y i) := congrFun (iterate_invariant (funext hv) _) _
  rw [map_mul, map_mul, hvσ, map_zpow₀, map_zpow₀] at hv'
  have hvπ0 : 0 < v π := pos_iff_ne_zero.2 ((map_ne_zero v).2 hπ)
  exact (zpow_right_injective₀ hvπ0 hvπ) (mul_right_cancel₀ ((map_ne_zero v).2 hyi) hv')

/-! ### Comparison with Mathlib's rank-one Witt isocrystals -/

open WittVector Isocrystal

/-- Over the fraction field of the Witt vectors of a perfect field `k` of characteristic `p`,
with `σ` the Witt vector Frobenius and `π = p`, the rank-one block `D(m, 1)` is Mathlib's standard
one-dimensional isocrystal `StandardOneDimIsocrystal p k m`: the identification `L^1 ≅ L` given by
the only coordinate intertwines the two Frobenii. -/
theorem standardBlockFrobenius_one_apply_zero_eq_frobenius (p : ℕ) [Fact p.Prime] (k : Type*)
    [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p] (m : ℤ) (x : Fin 1 → K(p, k)) :
    standardBlockFrobenius (FractionRing.frobenius p k) (p : K(p, k)) m 1 x 0 =
      Isocrystal.frobenius p k (V := StandardOneDimIsocrystal p k m) (x 0) := by
  -- `StandardOneDimIsocrystal p k m` is a type synonym for `K(p, k)`, and its scalar action is
  -- multiplication in `K(p, k)`.
  rw [standardBlockFrobenius_apply_zero]
  exact (StandardOneDimIsocrystal.frobenius_apply p k m (x 0)).symm

end TauCeti
