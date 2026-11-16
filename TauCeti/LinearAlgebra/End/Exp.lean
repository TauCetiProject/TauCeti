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
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.BigOperators
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Nat.Choose.Cast

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
* `Module.End.locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero` (with specializations
  `Module.End.locallyNilpotentExp_apply_of_lie_eq_zero`,
  `Module.End.locallyNilpotentExp_apply_of_lie_lie_eq_zero`, and
  `Module.End.locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero`): pushing an endomorphism past a
  locally nilpotent exponential when their iterated commutator vanishes in `m` steps.
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

/-- **Pushing an endomorphism past a locally nilpotent exponential.** If the `m`-fold iterated
commutator `(fun h ↦ ⁅f, h⁆)^[m] g` vanishes in `Module.End R M`, then
`exp f (g x) = (∑ j ∈ range m, (j ! : ℚ)⁻¹ • (fun h ↦ ⁅f, h⁆)^[j] g) (exp f x)`. -/
theorem locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero {g : Module.End R M} {m : ℕ}
    (hfg : (fun h ↦ ⁅f, h⁆)^[m] g = 0) (x : M) :
    locallyNilpotentExp f hf (g x) =
      (∑ j ∈ range m, (j.factorial : ℚ)⁻¹ • (fun h ↦ ⁅f, h⁆)^[j] g)
        (locallyNilpotentExp f hf x) := by
  let : LieRing (Module.End R M) := LieRing.ofAssociativeRing
  let : LieAlgebra ℤ (Module.End R M) := LieAlgebra.ofAssociativeAlgebra
  let : LieRingModule (Module.End R M) M := LieRingModule.ofAssociativeModule
  let : LieModule ℤ (Module.End R M) M := LieModule.ofAssociativeModule
  set d : ℕ → Module.End R M := fun j ↦ (fun h ↦ ⁅f, h⁆)^[j] g
  have hd_zero (j : ℕ) (hj : m ≤ j) : d j = 0 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj
    induction t with
    | zero => exact hfg
    | succ t ih =>
      simpa [d, ← add_assoc, Function.iterate_succ_apply', Ring.lie_def] using
        congrArg (fun h ↦ ⁅f, h⁆) ih
  have had (j : ℕ) : (LieAlgebra.ad ℤ (Module.End R M) f ^ j) g = d j := by
    rw [_root_.pow_apply_eq_iterate]
    rfl
  have htoEnd (j : ℕ) (z : M) :
      (LieModule.toEnd ℤ (Module.End R M) M f ^ j) z = (f ^ j) z := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, ih, pow_succ', _root_.mul_apply_eq_comp]
      rfl
  have hpow (n : ℕ) :
      (f ^ n) (g x) = ∑ ij ∈ antidiagonal n, n.choose ij.1 • d ij.1 ((f ^ ij.2) x) := by
    have h := LieModule.toEnd_pow_lie ℤ (L := Module.End R M) (M := M) f g x n
    simpa [htoEnd, had, lie_eq_smul, Module.End.smul_def] using h
  obtain ⟨k, hk⟩ := hf x
  have hgx : (f ^ (m + k)) (g x) = 0 := by
    rw [hpow]
    refine sum_eq_zero fun ij hij ↦ ?_
    have hsum := mem_antidiagonal.mp hij
    rcases le_or_gt m ij.1 with hi | hi
    · rw [hd_zero _ hi, LinearMap.zero_apply, smul_zero]
    · rw [pow_map_zero_of_le (by omega) hk, map_zero, smul_zero]
  rw [locallyNilpotentExp_apply_eq_sum f hf hgx,
    locallyNilpotentExp_apply_eq_sum f hf hk, LinearMap.sum_apply]
  simp_rw [hpow, smul_sum, LinearMap.smul_apply, map_sum, smul_sum, map_rat_smul, smul_smul]
  have hterm (n : ℕ) :
      ∑ ij ∈ antidiagonal n,
        (n.factorial : ℚ)⁻¹ • n.choose ij.1 • d ij.1 ((f ^ ij.2) x) =
        ∑ ij ∈ antidiagonal n,
          ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • d ij.1 ((f ^ ij.2) x) := by
    refine sum_congr rfl fun ij hij ↦ ?_
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      Nat.inv_factorial_mul_choose (K := ℚ) n ij.1 ij.2 (mem_antidiagonal.mp hij)]
  simp_rw [hterm]
  exact TauCeti.sum_range_add_antidiagonal_of_support m k
    (fun ij ↦ ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • d ij.1 ((f ^ ij.2) x))
    fun i j hij ↦ by
      rcases hij with hi | hj
      · rw [hd_zero _ hi, LinearMap.zero_apply, smul_zero]
      · rw [pow_map_zero_of_le hj hk, map_zero, smul_zero]

/-- **Commuting with a locally nilpotent exponential.** An endomorphism whose commutator with `f`
vanishes commutes with `locallyNilpotentExp f hf`. -/
theorem locallyNilpotentExp_apply_of_lie_eq_zero {g : Module.End R M} (hfg : ⁅f, g⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) = g (locallyNilpotentExp f hf x) := by
  simpa [sum_range_one] using
    locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero f hf (m := 1) hfg x

/-- **Pushing an endomorphism past a locally nilpotent exponential (two-step truncation).** If the
iterated commutator `⁅f, ⁅f, g⁆⁆` vanishes in `Module.End R M`, then
`exp f (g x) = (g + ⁅f, g⁆) (exp f x)`. -/
theorem locallyNilpotentExp_apply_of_lie_lie_eq_zero {g : Module.End R M}
    (hfg : ⁅f, ⁅f, g⁆⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) = (g + ⁅f, g⁆) (locallyNilpotentExp f hf x) := by
  simpa [sum_range_succ, Nat.factorial] using
    locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero f hf (m := 2) hfg x

/-- **Pushing an endomorphism past a locally nilpotent exponential (three-step truncation).** If
the threefold commutator `⁅f, ⁅f, ⁅f, g⁆⁆⁆` vanishes in `Module.End R M`, then
`exp f (g x) = (g + ⁅f, g⁆ + (1/2) ⁅f, ⁅f, g⁆⁆) (exp f x)`. -/
theorem locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero {g : Module.End R M}
    (hfg : ⁅f, ⁅f, ⁅f, g⁆⁆⁆ = 0) (x : M) :
    locallyNilpotentExp f hf (g x) =
      (g + ⁅f, g⁆ + (2⁻¹ : ℚ) • ⁅f, ⁅f, g⁆⁆) (locallyNilpotentExp f hf x) := by
  simpa [sum_range_succ, Nat.factorial] using
    locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero f hf (m := 3) hfg x

end Module.End
