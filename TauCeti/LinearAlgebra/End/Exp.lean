/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
import Mathlib.Algebra.Module.BigOperators

/-!
# The exponential of a locally nilpotent endomorphism

Let `f` be an endomorphism of a module `M` over a semiring `R`, where `M` is also a `ℚ`-vector
space. Call `f` *locally nilpotent* when every vector is killed by some power of `f`, the power
depending on the vector. Then the exponential series

`exp f x = ∑ i, (fⁱ x) / i!`

is a finite sum at every vector, and `Module.End.locallyNilpotentExp f hf` is the resulting
`R`-linear automorphism of `M`. Its inverse is the exponential of `-f`.

Mathlib's `IsNilpotent.exp` exponentiates an element of a `ℚ`-algebra that is nilpotent, so for an
endomorphism it needs a power of `f` killing every vector at once. For nilpotent `f` the two
exponentials agree (`Module.End.locallyNilpotentExp_eq_exp`). Local nilpotence without a uniform
bound is the situation of the adjoint action of a Chevalley generator on a Lie algebra presented by
generators and relations, such as Mathlib's Serre construction `Matrix.ToLieAlgebra`, which is not
known to be finite-dimensional in advance.

## Main definitions

* `Module.End.locallyNilpotentExp`: the exponential of a locally nilpotent endomorphism, as a
  linear automorphism.

## Main results

* `Module.End.locallyNilpotentExp_apply_eq_sum`: at a vector killed by `f ^ k`, the exponential is
  the exponential series truncated at length `k`.
* `Module.End.locallyNilpotentExp_apply_eq_exp_restrict`: on an `f`-stable subspace where `f` is
  nilpotent, the exponential is Mathlib's `IsNilpotent.exp` of the restriction.
* `Module.End.locallyNilpotentExp_symm_apply_eq_sum`: the inverse is the exponential series of
  `-f`.
* `Module.End.locallyNilpotentExp_symm`: the inverse is the exponential of `-f`.
* `Module.End.map_locallyNilpotentExp`: an additive map intertwining two locally nilpotent
  endomorphisms intertwines their exponentials.
* `Module.End.locallyNilpotentExp_apply_of_lie_eq_zero`,
  `Module.End.locallyNilpotentExp_apply_of_lie_lie_eq_zero`,
  `Module.End.locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero`: pushing an endomorphism past a
  locally nilpotent exponential when their iterated commutator vanishes in one, two or three steps.
* `Module.End.locallyNilpotentExp_eq_exp`: for nilpotent `f` the exponential is
  `IsNilpotent.exp f`.
-/

public section

open Finset

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module ℚ M]
  (f : Module.End R M)

variable (hf : ∀ x, ∃ n, (f ^ n) x = 0)

/-- The exponential series of `f` at `x`, truncated at some power of `f` that kills `x`. -/
private noncomputable def expFun (x : M) : M :=
  ∑ i ∈ range (hf x).choose, (i.factorial : ℚ)⁻¹ • (f ^ i) x

private theorem expFun_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    expFun f hf x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x := by
  rw [expFun, ← sum_range_smul_pow_apply_eq_of_le f _ (hf x).choose_spec (le_max_left _ k),
    sum_range_smul_pow_apply_eq_of_le f _ hk (le_max_right _ k)]

/-- The truncated exponential series is `R`-linear. -/
private noncomputable def expLinearMap : M →ₗ[R] M where
  toFun := expFun f hf
  map_add' x y := by
    obtain ⟨k, hx⟩ := hf x
    obtain ⟨l, hy⟩ := hf y
    have hx' := pow_map_zero_of_le (le_max_left k l) hx
    have hy' := pow_map_zero_of_le (le_max_right k l) hy
    have hxy : (f ^ max k l) (x + y) = 0 := by rw [map_add, hx', hy', add_zero]
    rw [expFun_eq_sum f hf hx', expFun_eq_sum f hf hy', expFun_eq_sum f hf hxy,
      ← sum_add_distrib]
    simp only [map_add, smul_add]
  map_smul' c x := by
    obtain ⟨k, hx⟩ := hf x
    have hcx : (f ^ k) (c • x) = 0 := by rw [map_smul, hx, smul_zero]
    rw [expFun_eq_sum f hf hx, expFun_eq_sum f hf hcx, RingHom.id_apply, smul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [map_smul, smul_comm]

/-- Viewing `f` as a `ℚ`-linear map does not change its values. -/
private theorem toRatLinearMap_apply (v : M) : f.toAddMonoidHom.toRatLinearMap v = f v := by
  rw [AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe]

/-- Viewing `f` as a `ℚ`-linear map does not change its powers. -/
private theorem toRatLinearMap_pow_apply (n : ℕ) (v : M) :
    (f.toAddMonoidHom.toRatLinearMap ^ n) v = (f ^ n) v := by
  rw [_root_.pow_apply_eq_iterate, _root_.pow_apply_eq_iterate, AddMonoidHom.coe_toRatLinearMap,
    LinearMap.toAddMonoidHom_coe]

/-- On an `f`-stable `ℚ`-subspace `V` on which `f` is nilpotent, the exponential series of `f` at
a vector of `V` is Mathlib's `IsNilpotent.exp` of the restriction of `f` to `V`. -/
private theorem coe_exp_restrict_apply {V : Submodule ℚ M}
    (hV : ∀ v ∈ V, f.toAddMonoidHom.toRatLinearMap v ∈ V) {n : ℕ}
    (hn : f.toAddMonoidHom.toRatLinearMap.restrict hV ^ n = 0) (v : V) :
    (IsNilpotent.exp (f.toAddMonoidHom.toRatLinearMap.restrict hV) v : M) = expFun f hf v := by
  have hpow (i : ℕ) :
      ((f.toAddMonoidHom.toRatLinearMap.restrict hV ^ i) v : M) = (f ^ i) v := by
    rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, toRatLinearMap_pow_apply]
  have hv : (f ^ n) v = 0 := by rw [← hpow, hn, LinearMap.zero_apply, Submodule.coe_zero]
  rw [IsNilpotent.exp_eq_sum hn, expFun_eq_sum f hf hv, LinearMap.sum_apply, Submodule.coe_sum]
  exact sum_congr rfl fun i _ ↦ by rw [LinearMap.smul_apply, Submodule.coe_smul, hpow]

/-- The exponential series of `-f` inverts that of `f`. At a vector killed by `f ^ n`, this is
Mathlib's `IsNilpotent.exp_neg_mul_exp_self` for the restriction of `f` to the `f`-stable
`ℚ`-subspace `ker (f ^ n)`, where `f` is nilpotent. The endomorphism `-f` is passed as any `g`
equal to it, so that both composites of the two series are instances. -/
private theorem expFun_expFun_of_eq_neg {g : Module.End R M} (hfg : g = -f)
    (hg : ∀ x, ∃ n, (g ^ n) x = 0) (x : M) : expFun g hg (expFun f hf x) = x := by
  subst hfg
  obtain ⟨n, hn⟩ := hf x
  set V := LinearMap.ker (f.toAddMonoidHom.toRatLinearMap ^ n)
  have hV : ∀ v ∈ V, f.toAddMonoidHom.toRatLinearMap v ∈ V := fun v hv ↦ by
    rw [LinearMap.mem_ker, ← _root_.mul_apply_eq_comp, ← pow_succ, pow_succ',
      _root_.mul_apply_eq_comp,
      LinearMap.mem_ker.1 hv, map_zero]
  have hV' : ∀ v ∈ V, (-f).toAddMonoidHom.toRatLinearMap v ∈ V := fun v hv ↦ V.neg_mem (hV v hv)
  have hneg : (-f).toAddMonoidHom.toRatLinearMap.restrict hV' =
      -f.toAddMonoidHom.toRatLinearMap.restrict hV := by
    ext v
    simp only [LinearMap.coe_restrict_apply, LinearMap.neg_apply, Submodule.coe_neg,
      toRatLinearMap_apply]
  have hnil : f.toAddMonoidHom.toRatLinearMap.restrict hV ^ n = 0 := by
    ext v
    rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, LinearMap.zero_apply,
      Submodule.coe_zero]
    exact v.2
  have hnil' : (-f).toAddMonoidHom.toRatLinearMap.restrict hV' ^ n = 0 := by
    rw [hneg, neg_pow (R := Module.End ℚ V), hnil, mul_zero]
  have hx : x ∈ V := by rwa [LinearMap.mem_ker, toRatLinearMap_pow_apply]
  rw [← coe_exp_restrict_apply f hf hV hnil ⟨x, hx⟩, ← coe_exp_restrict_apply (-f) hg hV' hnil',
    hneg, ← _root_.mul_apply_eq_comp, IsNilpotent.exp_neg_mul_exp_self ⟨n, hnil⟩,
    _root_.one_apply_eq_self]

/-- **The exponential of a locally nilpotent endomorphism.** If every vector of `M` is killed by
some power of `f`, the exponential series `∑ (fⁱ x) / i!` is a finite sum at every vector `x`, and
it defines an `R`-linear automorphism of `M` whose inverse is the exponential series of `-f`. -/
noncomputable def locallyNilpotentExp : M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (expLinearMap f hf)
    (expLinearMap (-f) (by simpa only [neg_pow_apply_eq_zero_iff] using hf))
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg (-f) (by simpa only [neg_pow_apply_eq_zero_iff] using hf)
        (neg_neg f).symm hf x)
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg f hf rfl (by simpa only [neg_pow_apply_eq_zero_iff] using hf) x)

/-- **The exponential as a truncated series.** At a vector killed by `f ^ k`, the exponential of
`f` is its exponential series truncated at length `k`. -/
theorem locallyNilpotentExp_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    locallyNilpotentExp f hf x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x :=
  expFun_eq_sum f hf hk

/-- **The exponential on a nilpotent piece.** On an `f`-stable `ℚ`-subspace `V` on which `f` is
nilpotent, the exponential of `f` at a vector of `V` is Mathlib's `IsNilpotent.exp` of the
restriction of `f` to `V`. -/
theorem locallyNilpotentExp_apply_eq_exp_restrict {V : Submodule ℚ M}
    (hV : ∀ v ∈ V, f.toAddMonoidHom.toRatLinearMap v ∈ V) {n : ℕ}
    (hn : f.toAddMonoidHom.toRatLinearMap.restrict hV ^ n = 0) (v : V) :
    locallyNilpotentExp f hf v =
      (IsNilpotent.exp (f.toAddMonoidHom.toRatLinearMap.restrict hV) v : M) :=
  (coe_exp_restrict_apply f hf hV hn v).symm

/-- **The inverse of the exponential.** At a vector killed by `f ^ k`, the inverse of the
exponential of `f` is the exponential series of `-f` truncated at length `k`. -/
theorem locallyNilpotentExp_symm_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    (locallyNilpotentExp f hf).symm x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • ((-f) ^ i) x :=
  expFun_eq_sum (-f) (by simpa only [neg_pow_apply_eq_zero_iff] using hf)
    ((neg_pow_apply_eq_zero_iff f k x).2 hk)

/-- **The inverse of the exponential is the exponential of `-f`.** -/
@[simp]
theorem locallyNilpotentExp_symm :
    (locallyNilpotentExp f hf).symm =
      locallyNilpotentExp (-f) (by simpa only [neg_pow_apply_eq_zero_iff] using hf) := by
  ext x
  obtain ⟨k, hk⟩ := hf x
  rw [locallyNilpotentExp_symm_apply_eq_sum f hf hk,
    locallyNilpotentExp_apply_eq_sum (-f) _ ((neg_pow_apply_eq_zero_iff f k x).2 hk)]

/-- **Naturality of the exponential.** An additive map `g` with `g ∘ f = f' ∘ g` carries the
exponential of `f` to that of `f'`. The two endomorphisms may be linear over different semirings. -/
theorem map_locallyNilpotentExp {S N F : Type*} [Semiring S] [AddCommGroup N] [Module S N]
    [Module ℚ N] [FunLike F M N] [AddMonoidHomClass F M N] {f' : Module.End S N}
    (hf' : ∀ y, ∃ n, (f' ^ n) y = 0) (g : F) (hg : Function.Semiconj g f f') (x : M) :
    g (locallyNilpotentExp f hf x) = locallyNilpotentExp f' hf' (g x) := by
  have hpow (i : ℕ) : (f' ^ i) (g x) = g ((f ^ i) x) := by
    rw [_root_.pow_apply_eq_iterate, _root_.pow_apply_eq_iterate]
    exact (hg.iterate_right i x).symm
  obtain ⟨k, hk⟩ := hf x
  rw [locallyNilpotentExp_apply_eq_sum f hf hk,
    locallyNilpotentExp_apply_eq_sum f' hf' (k := k) (by rw [hpow, hk, map_zero]), map_sum]
  exact sum_congr rfl fun i _ ↦ by rw [hpow, map_rat_smul]

/-- For a nilpotent endomorphism, the exponential is Mathlib's `IsNilpotent.exp`. -/
theorem locallyNilpotentExp_eq_exp (hnil : IsNilpotent f) :
    (locallyNilpotentExp f hnil.exists_pow_apply_eq_zero : Module.End R M) = IsNilpotent.exp f := by
  obtain ⟨k, hk⟩ := hnil
  ext x
  rw [LinearEquiv.coe_coe,
    locallyNilpotentExp_apply_eq_sum f _ (by rw [hk, LinearMap.zero_apply]),
    IsNilpotent.exp_eq_sum hk, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-! ### Pushing an endomorphism past a locally nilpotent exponential -/

omit [Module ℚ M] in
private theorem pow_add_two_mul_of_lie_lie_lie_eq_zero {a b : Module.End R M}
    (hab : ⁅a, ⁅a, ⁅a, b⁆⁆⁆ = 0) (n : ℕ) :
    a ^ (n + 2) * b = b * a ^ (n + 2) + (n + 2) • (⁅a, b⁆ * a ^ (n + 1)) +
      (n + 2).choose 2 • (⁅a, ⁅a, b⁆⁆ * a ^ n) := by
  set d₁ := ⁅a, b⁆
  set d₂ := ⁅a, d₁⁆
  have hstep₀ : a * b = b * a + d₁ := by simp only [d₁, Ring.lie_def]; abel
  have hstep₁ : a * d₁ = d₁ * a + d₂ := by simp only [d₂, Ring.lie_def]; abel
  have hcomm₂ : a * d₂ = d₂ * a := sub_eq_zero.1 (Ring.lie_def a d₂ ▸ hab)
  induction n with
  | zero =>
    change a ^ 2 * b = b * a ^ 2 + 2 • (d₁ * a) + 1 • (d₂ * 1)
    rw [sq, mul_assoc a a b, hstep₀, mul_add, ← mul_assoc a b a, hstep₀, add_mul, hstep₁,
      mul_assoc b a a, mul_one, one_nsmul, two_nsmul]
    simp only [add_assoc (G := Module.End R M)]
  | succ n ih =>
    have hch : (n + 3).choose 2 = (n + 2) + (n + 2).choose 2 := by
      rw [Nat.choose_succ_succ (n + 2) 1, Nat.choose_one_right]
    calc a ^ (n + 3) * b
        = a * (b * a ^ (n + 2) + (n + 2) • (d₁ * a ^ (n + 1)) +
            (n + 2).choose 2 • (d₂ * a ^ n)) := by
          rw [pow_succ' a (n + 2), mul_assoc, ih]
      _ = (a * b) * a ^ (n + 2) + (n + 2) • ((a * d₁) * a ^ (n + 1)) +
            (n + 2).choose 2 • ((a * d₂) * a ^ n) := by
          simp only [mul_add, mul_smul_comm, mul_assoc]
      _ = b * a ^ (n + 3) + (n + 3) • (d₁ * a ^ (n + 2)) +
            (n + 3).choose 2 • (d₂ * a ^ (n + 1)) := by
          rw [hstep₀, hstep₁, hcomm₂, add_mul, add_mul, nsmul_add, hch,
            add_nsmul (d₂ * a ^ (n + 1)) (n + 2) ((n + 2).choose 2),
            succ_nsmul' _ (n + 2), mul_assoc b a (a ^ (n + 2)), ← pow_succ' a (n + 2),
            mul_assoc d₁ a (a ^ (n + 1)), ← pow_succ' a (n + 1),
            mul_assoc d₂ a (a ^ n), ← pow_succ' a n]
          simp only [add_assoc (G := Module.End R M)]

/-- **Commuting with a locally nilpotent exponential.** An endomorphism whose commutator with `f`
vanishes commutes with `locallyNilpotentExp f hf`. -/
theorem locallyNilpotentExp_apply_of_lie_eq_zero {g : Module.End R M} (hfg : ⁅f, g⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) = g (locallyNilpotentExp f hf x) := by
  have hcomm : g * f = f * g := (sub_eq_zero.1 (Ring.lie_def f g ▸ hfg)).symm
  exact (map_locallyNilpotentExp f hf hf g (fun z ↦ LinearMap.congr_fun hcomm z) x).symm

private theorem inv_factorial_add_two_mul_choose_two (i : ℕ) :
    ((i + 2).factorial : ℚ)⁻¹ * ((i + 2).choose 2 : ℚ) = (2⁻¹ : ℚ) * (i.factorial : ℚ)⁻¹ := by
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hf0 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hf2 : ((i + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (i + 2).factorial_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero h2 hf2)
  calc (2 * ((i + 2).factorial : ℚ)) * (((i + 2).factorial : ℚ)⁻¹ * ((i + 2).choose 2 : ℚ))
      = 2 * ((i + 2).choose 2 : ℚ) := by
        rw [mul_assoc, ← mul_assoc ((i + 2).factorial : ℚ), mul_inv_cancel₀ hf2, one_mul]
    _ = (((i + 2).choose 2 * 2 : ℕ) : ℚ) := by push_cast; ring
    _ = (((i + 2) * (i + 1) : ℕ) : ℚ) := by
        rw [← Nat.add_one_mul_choose_eq (i + 1) 1, Nat.choose_one_right]
    _ = (2 * ((i + 2).factorial : ℚ)) * ((2⁻¹ : ℚ) * (i.factorial : ℚ)⁻¹) := by
        rw [Nat.factorial_succ (i + 1), Nat.factorial_succ i]
        push_cast
        rw [mul_comm (2 : ℚ), mul_assoc, ← mul_assoc (2 : ℚ) (2⁻¹ : ℚ), mul_inv_cancel₀ h2,
          one_mul, ← mul_assoc ((i : ℚ) + 1 + 1), mul_assoc _ (i.factorial : ℚ),
          mul_inv_cancel₀ hf0, mul_one, add_assoc (i : ℚ) 1 1, one_add_one_eq_two]

/-- **Pushing an endomorphism past a locally nilpotent exponential (three-step truncation).** If
the threefold commutator `⁅f, ⁅f, ⁅f, g⁆⁆⁆` vanishes in `Module.End R M`, then
`exp f (g x) = (g + ⁅f, g⁆ + (1/2) ⁅f, ⁅f, g⁆⁆) (exp f x)`. -/
theorem locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero {g : Module.End R M}
    (hfg : ⁅f, ⁅f, ⁅f, g⁆⁆⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) =
      (g + ⁅f, g⁆ + (2⁻¹ : ℚ) • ⁅f, ⁅f, g⁆⁆) (locallyNilpotentExp f hf x) := by
  obtain ⟨k, hk⟩ := hf x
  have hk₁ : (f ^ (k + 1)) x = 0 := pow_map_zero_of_le (Nat.le_succ k) hk
  have hk₂ : (f ^ (k + 2)) x = 0 := pow_map_zero_of_le (Nat.le_add_right k 2) hk
  have hgx : (f ^ (k + 2)) (g x) = 0 := by
    have h := LinearMap.congr_fun (pow_add_two_mul_of_lie_lie_lie_eq_zero hfg k) x
    simpa [_root_.mul_apply_eq_comp, hk, hk₁, hk₂] using h
  have hc₁ (i : ℕ) : ((i + 1).factorial : ℚ)⁻¹ * (i + 1 : ℚ) = (i.factorial : ℚ)⁻¹ := by
    rw [← Nat.cast_add_one, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev,
      inv_mul_cancel_right₀ (by positivity)]
  have hsum :
      ∑ i ∈ range k, ((i + 2).factorial : ℚ)⁻¹ • (f ^ (i + 2)) (g x) =
        (∑ i ∈ range k, ((i + 2).factorial : ℚ)⁻¹ • g ((f ^ (i + 2)) x)) +
          (∑ i ∈ range k, ((i + 1).factorial : ℚ)⁻¹ • ⁅f, g⁆ ((f ^ (i + 1)) x)) +
          ∑ i ∈ range k, ((2⁻¹ : ℚ) * (i.factorial : ℚ)⁻¹) • ⁅f, ⁅f, g⁆⁆ ((f ^ i) x) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    have hp := LinearMap.congr_fun (pow_add_two_mul_of_lie_lie_lie_eq_zero hfg i) x
    simp only [_root_.mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply] at hp
    rw [hp, smul_add, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul, Nat.cast_add_one, hc₁, inv_factorial_add_two_mul_choose_two]
  have hf1 : f (g x) = g (f x) + ⁅f, g⁆ x := by
    simp [Ring.lie_def, _root_.mul_apply_eq_comp]
  have hg0 : g (locallyNilpotentExp f hf x) =
      (∑ i ∈ range k, ((i + 2).factorial : ℚ)⁻¹ • g ((f ^ (i + 2)) x)) + g (f x) + g x := by
    rw [locallyNilpotentExp_apply_eq_sum f hf hk₂, sum_range_succ', sum_range_succ']
    simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      pow_zero, pow_one, _root_.one_apply_eq_self, map_add, map_sum, map_rat_smul]
  have hg1 : ⁅f, g⁆ (locallyNilpotentExp f hf x) =
      (∑ i ∈ range k, ((i + 1).factorial : ℚ)⁻¹ • ⁅f, g⁆ ((f ^ (i + 1)) x)) + ⁅f, g⁆ x := by
    rw [locallyNilpotentExp_apply_eq_sum f hf hk₁, sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
      _root_.one_apply_eq_self, map_add, map_sum, map_rat_smul]
  have hg2 : (2⁻¹ : ℚ) • ⁅f, ⁅f, g⁆⁆ (locallyNilpotentExp f hf x) =
      ∑ i ∈ range k, ((2⁻¹ : ℚ) * (i.factorial : ℚ)⁻¹) • ⁅f, ⁅f, g⁆⁆ ((f ^ i) x) := by
    rw [locallyNilpotentExp_apply_eq_sum f hf hk, map_sum, smul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [map_rat_smul, smul_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, hg0, hg1, hg2]
  rw [locallyNilpotentExp_apply_eq_sum f hf hgx, sum_range_succ', sum_range_succ', hsum]
  simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_zero, pow_one, _root_.one_apply_eq_self, hf1]
  abel

/-- **Pushing an endomorphism past a locally nilpotent exponential (two-step truncation).** If the
iterated commutator `⁅f, ⁅f, g⁆⁆` vanishes in `Module.End R M`, then
`exp f (g x) = (g + ⁅f, g⁆) (exp f x)`. -/
theorem locallyNilpotentExp_apply_of_lie_lie_eq_zero {g : Module.End R M}
    (hfg : ⁅f, ⁅f, g⁆⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) = (g + ⁅f, g⁆) (locallyNilpotentExp f hf x) := by
  have h3 : ⁅f, ⁅f, ⁅f, g⁆⁆⁆ = 0 := by rw [hfg, Ring.lie_def, mul_zero, zero_mul, sub_self]
  simpa [hfg] using locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero f hf h3 x

end Module.End
