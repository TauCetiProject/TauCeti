/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.WittVector.Isocrystal
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear
import TauCeti.LinearAlgebra.Matrix.Rank

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
* `TauCeti.cyclicShift φ c`: coordinatewise `φ` composed with cyclic rotation and scaling of
  coordinate `0` by `c`.

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
* `TauCeti.eq_bot_or_eq_top_of_standardBlockFrobenius_stable`: over a field `L` with an
  automorphism `σ` preserving a valuation `v` and fixing a nonzero element `π` whose valuation
  generates `v(Lˣ)`, `D(s, r)` has no proper nontrivial `standardBlockFrobenius σ π s r`-stable
  subspaces when `Nat.Coprime s.natAbs r`.
* `TauCeti.standardBlockFrobenius_one_apply_zero_eq_frobenius`: for Witt vectors, the rank-one block
  `D(m, 1)` with `π = p` is Mathlib's `WittVector.StandardOneDimIsocrystal p k m`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, before Proposition 8.2.6.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), Definition 4.1.1
  and Lemma 4.1.2.
* K. S. Kedlaya, *Slope filtrations revisited*, Doc. Math. 10 (2005), 447–525, §4.5
  (4.5.3–4.5.8, pp. 497–499).
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

/-- The Frobenius of `D(s, r)` sends `Pi.single j c` to `Pi.single (finRotate r j) (σ c)`
before the last index. -/
theorem standardBlockFrobenius_single_of_val_add_one_ne {r : ℕ} {j : Fin r}
    (hj : j.val + 1 ≠ r) (c : L) :
    standardBlockFrobenius σ π s r (Pi.single j c) = Pi.single (finRotate r j) (σ c) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (j.neZero).out
  induction j using Fin.lastCases with
  | last => exact (hj (by simp)).elim
  | cast j =>
    rw [Fin.finRotate_castSucc]
    exact standardBlockFrobenius_single_castSucc j c

/-- The Frobenius of `D(s, r)` sends `Pi.single j c` at the last index to
`Pi.single (finRotate r j) (π ^ s * σ c)`. -/
theorem standardBlockFrobenius_single_of_val_add_one_eq {r : ℕ} {j : Fin r}
    (hj : j.val + 1 = r) (c : L) :
    standardBlockFrobenius σ π s r (Pi.single j c) =
      Pi.single (finRotate r j) (π ^ s * σ c) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (j.neZero).out
  induction j using Fin.lastCases with
  | last =>
    rw [finRotate_last]
    exact standardBlockFrobenius_single_last c
  | cast j => exact absurd hj (by simp; omega)

/-- An `L`-linear map from `L^r` whose values on the standard basis `Pi.single j 1` satisfy
the cyclic Frobenius recurrence intertwines `standardBlockFrobenius σ π s r` with `Φ`. -/
theorem intertwines_standardBlockFrobenius_of_single {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module L V] {Φ : V →ₛₗ[(σ : L →+* L)] V} (g : (Fin r → L) →ₗ[L] V)
    (hg : ∀ j : Fin r, Φ (g (Pi.single j 1)) =
      (if j.val + 1 = r then π ^ s else 1) • g (Pi.single (finRotate r j) 1))
    (x : Fin r → L) :
    g (standardBlockFrobenius σ π s r x) = Φ (g x) := by
  have heq : g.comp (standardBlockFrobenius σ π s r) = Φ.comp g :=
    (Pi.basisFun L (Fin r)).ext fun j ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Pi.basisFun_apply]
      by_cases hj : j.val + 1 = r
      · rw [standardBlockFrobenius_single_of_val_add_one_eq hj, map_one, mul_one, hg j]
        simp only [hj, ↓reduceIte]
        rw [← map_smul]
        congr 1
        ext l
        simp [Pi.single_apply]
      · rw [standardBlockFrobenius_single_of_val_add_one_ne hj, map_one, hg j]
        simp only [hj, ↓reduceIte, one_smul]
  exact LinearMap.congr_fun heq x

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

/-- Cyclic shift on `Fin r → M` applying `φ` coordinatewise and scaling coordinate `0` by `c`. -/
def cyclicShift {R M : Type*} [SMul R M] [One R] {r : ℕ}
    (φ : M → M) (c : R) (x : Fin r → M) (i : Fin r) : M :=
  (if (i : ℕ) = 0 then c else 1) • φ (x ((finRotate r).symm i))

/-- Coordinate formula for `TauCeti.cyclicShift`. -/
@[simp]
theorem cyclicShift_apply {R M : Type*} [SMul R M] [One R] {r : ℕ}
    (φ : M → M) (c : R) (x : Fin r → M) (i : Fin r) :
    cyclicShift φ c x i = (if (i : ℕ) = 0 then c else 1) • φ (x ((finRotate r).symm i)) := by
  rfl

/-- The `k`-th iterate of a cyclic shift with wraparound scalar `c` and coordinate map `φ`
satisfying `φ (a • m) = σ a • φ m` and `σ c = c`. -/
theorem cyclicShift_iterate_apply {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {σ : R →+* R} (φ : M → M) (hφ_smul : ∀ (a : R) (m : M), φ (a • m) = σ a • φ m)
    (c : R) (hφc : σ c = c) {r : ℕ} [NeZero r] (k : ℕ) (x : Fin r → M) (i : Fin r) :
    (cyclicShift φ c)^[k] x i =
      (∏ t ∈ range k, if ((i - (t : Fin r) : Fin r) : ℕ) = 0 then c else 1) •
        φ^[k] (x (i - (k : Fin r))) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hσw (j : Fin r) :
        σ (if (j : ℕ) = 0 then c else 1) = if (j : ℕ) = 0 then c else 1 := by
      split_ifs <;> simp [hφc]
    have hidx (t : ℕ) : i - 1 - (t : Fin r) = i - ((t + 1 : ℕ) : Fin r) := by
      push_cast
      abel
    rw [iterate_succ_apply', cyclicShift_apply, finRotate_symm_apply, ih, hφ_smul, map_prod,
      prod_range_succ', ← iterate_succ_apply' φ, ← smul_assoc, smul_eq_mul, mul_comm]
    simp only [hσw, hidx, Nat.cast_zero, sub_zero]

/-- After a full cycle of length `r`, a cyclic shift with wraparound scalar `c` and coordinate map
`φ` acts as `c • φ^[r]` on each coordinate. -/
theorem cyclicShift_iterate_rank_apply {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {σ : R →+* R} (φ : M → M)
    (hφ_smul : ∀ (a : R) (m : M), φ (a • m) = σ a • φ m)
    (c : R) (hφc : σ c = c) {r : ℕ} (x : Fin r → M) (i : Fin r) :
    (cyclicShift φ c)^[r] x i = c • φ^[r] (x i) := by
  have := i.neZero
  rw [cyclicShift_iterate_apply φ hφ_smul c hφc, Fin.natCast_self, sub_zero,
    prod_eq_single (i : ℕ)]
  · simp
  · intro t ht hti
    rw [ite_eq_right_iff]
    intro h
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h
    exact (hti (by rw [h, Fin.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ht)])).elim
  · simp

/-- If `σ` fixes `π`, then the `r`-th power of the Frobenius of `D(s, r)` is `π ^ s • σ ^ r`,
with `σ ^ r` acting on coordinates. -/
theorem standardBlockFrobenius_iterate_rank_apply (hσπ : σ π = π) (x : Fin r → L)
    (i : Fin r) :
    (standardBlockFrobenius σ π s r)^[r] x i = π ^ s * σ^[r] (x i) := by
  have hcoe : (standardBlockFrobenius σ π s r : (Fin r → L) → (Fin r → L)) =
      cyclicShift (σ : L →+* L) (π ^ s) := by
    ext y j
    simp [standardBlockFrobenius_apply]
  rw [hcoe]
  exact cyclicShift_iterate_rank_apply (σ := (σ : L →+* L)) (σ : L →+* L)
    (fun a m ↦ map_mul σ a m) (π ^ s) (by rw [RingHom.coe_coe, map_zpow₀, hσπ]) x i

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

/-! ### Simplicity of coprime standard blocks -/

section Simplicity

private noncomputable def basisIterMatrix {L : Type*} [Field L] (σ : L ≃+* L) {d : ℕ}
    (B : Matrix (Fin d) (Fin d) L) : ℕ → Matrix (Fin d) (Fin d) L
  | 0 => 1
  | m + 1 => (basisIterMatrix σ B m).map (σ : L →+* L) * B

private theorem basisIterMatrix_mul_basis {L : Type*} [Field L] (σ : L ≃+* L) (π : L) {s : ℤ}
    {r d : ℕ} {U : Submodule L (Fin r → L)}
    (hU : ∀ x ∈ U, standardBlockFrobenius σ π s r x ∈ U) (b : Module.Basis (Fin d) L U) (m : ℕ)
    (i : Fin d) :
    let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦
      b.repr ⟨standardBlockFrobenius σ π s r (b i).val, hU (b i).val (b i).property⟩ k
    (standardBlockFrobenius σ π s r)^[m] (b i).val =
      ∑ k, basisIterMatrix σ B m i k • (b k).val := by
  intro B
  have hΦ_b (l : Fin d) :
      standardBlockFrobenius σ π s r (b l).val = ∑ k, B l k • (b k).val := by
    have hrep := congrArg Subtype.val
      (b.sum_repr ⟨standardBlockFrobenius σ π s r (b l).val, hU (b l).val (b l).property⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    exact hrep.symm
  induction m generalizing i with
  | zero => simp [basisIterMatrix, Matrix.one_apply]
  | succ m ih =>
    rw [iterate_succ_apply', ih, map_sum]
    simp only [map_smulₛₗ, RingHom.coe_coe, hΦ_b, smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← Finset.sum_smul]
    simp [basisIterMatrix, Matrix.mul_apply]

private theorem valuation_basisIterMatrix_det {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (σ : L ≃+* L) (v : Valuation L Γ₀)
    (hv : ∀ x, v (σ x) = v x) {d : ℕ} (B : Matrix (Fin d) (Fin d) L) (m : ℕ) :
    v (basisIterMatrix σ B m).det = v B.det ^ m := by
  induction m with
  | zero => simp [basisIterMatrix]
  | succ m ih =>
    rw [basisIterMatrix, Matrix.det_mul, map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      RingHom.coe_coe, hv, ih, pow_succ]

private theorem basis_matrix_iterate_det_val {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (σ : L ≃+* L) (π : L) (hσπ : σ π = π)
    (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x) {s : ℤ} {r d : ℕ}
    {U : Submodule L (Fin r → L)} (hU : ∀ x ∈ U, standardBlockFrobenius σ π s r x ∈ U)
    (b : Module.Basis (Fin d) L U) :
    let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦
      b.repr ⟨standardBlockFrobenius σ π s r (b i).val, hU (b i).val (b i).property⟩ k
    v B.det ^ r = v π ^ (s * (d : ℤ)) := by
  intro B
  let M : Matrix (Fin d) (Fin r) L := Matrix.of fun i j ↦ (b i).val j
  obtain ⟨c, hc⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.1
    (b.linearIndependent.map' U.subtype (Submodule.ker_subtype U))
  let M₀ : Matrix (Fin d) (Fin d) L := M.submatrix id c
  -- Compare `Φ^[r]` via `basisIterMatrix σ B r` against `π ^ s • σ^[r]` on coordinates.
  have hCrM : basisIterMatrix σ B r * M₀ = π ^ s • M₀.map (σ^[r] : L → L) := by
    ext i j
    have h1 : (standardBlockFrobenius σ π s r)^[r] (b i).val (c j) =
        (basisIterMatrix σ B r * M₀) i j := by
      rw [basisIterMatrix_mul_basis σ π hU b r i]
      simp [B, M₀, M, Matrix.mul_apply]
    have h2 := standardBlockFrobenius_iterate_rank_apply (s := s) hσπ (b i).val (c j)
    rw [← h1, h2]
    simp [M₀, M]
  have hdet_eq := congrArg (fun X ↦ v X.det) hCrM
  have hv_iter (x : L) : v (σ^[r] x) = v x := congrFun (iterate_invariant (funext hv) r) x
  have hdet_map : v (M₀.map (σ^[r] : L → L)).det = v M₀.det := by
    let σr : L ≃+* L := σ ^ r
    have hσr : (σ^[r] : L → L) = (σr : L →+* L) := by ext x; simp [σr]
    rw [hσr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingHom.coe_coe]
    simpa [σr] using hv_iter M₀.det
  rw [Matrix.det_mul, Matrix.det_smul, map_mul, map_mul, valuation_basisIterMatrix_det σ v hv,
    map_pow, map_zpow₀, hdet_map] at hdet_eq
  have hmul := mul_right_cancel₀ ((map_ne_zero v).2 hc) hdet_eq
  simpa [← zpow_natCast, ← zpow_mul] using hmul

/-- **Simplicity of coprime standard blocks.** Let `σ` be an automorphism of a field `L` fixing a
nonzero element `π` and preserving a valuation `v` with `v π ≠ 1` whose values on `Lˣ` lie in
`⟨v π⟩`. Then for coprime `s` and `r`, the standard block `D(s, r)` has no proper nontrivial
`standardBlockFrobenius σ π s r`-stable `L`-subspaces (Kedlaya 2005, §4.5, 4.5.3–4.5.8). -/
theorem eq_bot_or_eq_top_of_standardBlockFrobenius_stable
    {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    (σ : L ≃+* L) (π : L) (hπ : π ≠ 0) (hσπ : σ π = π)
    (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x) (hvπ : v π ≠ 1)
    (hgen : ∀ x : L, x ≠ 0 → ∃ n : ℤ, v x = v π ^ n)
    {s : ℤ} {r : ℕ} (hcop : s.natAbs.Coprime r)
    {U : Submodule L (Fin r → L)}
    (hU : ∀ x ∈ U, standardBlockFrobenius σ π s r x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  rw [or_iff_not_imp_left]
  intro hU0
  set d := Module.finrank L U
  have hd_pos : 0 < d := Nat.pos_of_ne_zero fun hd ↦ hU0 (Submodule.finrank_eq_zero.1 hd)
  have hd_le : d ≤ r := by simpa [d] using Submodule.finrank_le U
  let b : Module.Basis (Fin d) L U := Module.finBasis L U
  let Φ_U := (standardBlockFrobenius σ π s r).restrict hU
  have hΦ_U_inj : Injective Φ_U := fun x y hxy ↦ Subtype.ext <|
    (standardBlockFrobenius_bijective hπ).injective (congrArg Subtype.val hxy)
  have hΦ_U_surj : Surjective Φ_U := LinearMap.surjective_of_injectiveₛₗ hΦ_U_inj
  let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦ b.repr (Φ_U (b i)) k
  have hB_det : B.det ≠ 0 :=
    (LinearMap.isUnit_det_basis_matrix_of_surjectiveₛₗ b hΦ_U_surj).ne_zero
  have hvB_pow : v B.det ^ r = v π ^ (s * (d : ℤ)) :=
    basis_matrix_iterate_det_val σ π hσπ v hv hU b
  obtain ⟨k, hk⟩ := hgen B.det hB_det
  have hk_exp : v π ^ (k * (r : ℤ)) = v π ^ (s * (d : ℤ)) := by
    rw [zpow_mul, zpow_natCast, ← hk, hvB_pow]
  have hvπ0 : 0 < v π := pos_iff_ne_zero.2 ((map_ne_zero v).2 hπ)
  have hkr : k * (r : ℤ) = s * (d : ℤ) := zpow_right_injective₀ hvπ0 hvπ hk_exp
  have hdvd : r ∣ s.natAbs * d := by
    have h1 : (r : ℤ) ∣ s * (d : ℤ) := ⟨k, hkr.symm.trans (mul_comm k (r : ℤ))⟩
    exact Int.ofNat_dvd.1 (by simpa [Int.natAbs_mul] using Int.dvd_natAbs.2 h1)
  exact Submodule.eq_top_of_finrank_eq <| by
    simpa [d] using le_antisymm hd_le (Nat.le_of_dvd hd_pos (hcop.symm.dvd_of_dvd_mul_left hdvd))

end Simplicity

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
