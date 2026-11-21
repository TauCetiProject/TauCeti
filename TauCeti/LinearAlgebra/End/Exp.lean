/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.LinearAlgebra.End.Basic
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.BigOperators
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# The exponential of a nilpotent or locally nilpotent endomorphism

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

The section on nilpotent exponentials and algebra automorphisms is adapted from
`Mei/LinearAlgebra/End/Exp.lean` in [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).

## Main definitions

* `Module.End.locallyNilpotentExp`: the exponential of a locally nilpotent endomorphism, as a
  linear automorphism.
* `Module.End.expAlgEquiv`: the exponential of a nilpotent derivation, as an algebra automorphism.

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
* `Module.End.map_exp`: an additive map intertwining two nilpotent endomorphisms intertwines
  their exponentials `IsNilpotent.exp`.
* `Module.End.restrictScalars_exp`: scalar restriction commutes with `IsNilpotent.exp`.
* `Module.End.exp_apply_mem_of_forall_mem`: `IsNilpotent.exp` of an endomorphism preserves every
  submodule stable under it whose coefficient semiring carries a compatible `ℚ`-action.
* `Module.End.exp_apply_of_apply_eq_zero`: the exponential of a nilpotent endomorphism fixes the
  vectors in its kernel.
* `LinearMap.exp_bilinear_of_leibniz`: a Leibniz-compatible bilinear pairing intertwines the
  exponentials of nilpotent endomorphisms.
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
    exact v.property
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
private theorem pow_apply_apply_eq_sum_antidiagonal (f g : Module.End R M) (x : M) (n : ℕ) :
    (f ^ n) (g x) =
      ∑ ij ∈ antidiagonal n, n.choose ij.fst • ((fun h ↦ ⁅f, h⁆)^[ij.fst] g) ((f ^ ij.snd) x) := by
  let : LieRing (Module.End R M) := LieRing.ofAssociativeRing
  let : LieAlgebra ℤ (Module.End R M) := LieAlgebra.ofAssociativeAlgebra
  let : LieRingModule (Module.End R M) M := LieRingModule.ofAssociativeModule
  let : LieModule ℤ (Module.End R M) M := LieModule.ofAssociativeModule
  have had (j : ℕ) : (LieAlgebra.ad ℤ (Module.End R M) f ^ j) g = (fun h ↦ ⁅f, h⁆)^[j] g := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, LieAlgebra.ad_apply, ih,
        Function.iterate_succ_apply']
  have htoEnd (j : ℕ) (z : M) :
      (LieModule.toEnd ℤ (Module.End R M) M f ^ j) z = (f ^ j) z := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, ih, pow_succ', _root_.mul_apply_eq_comp,
        LieModule.toEnd_apply_apply, lie_eq_smul, Module.End.smul_def]
  have h := LieModule.toEnd_pow_lie ℤ (L := Module.End R M) (M := M) f g x n
  simpa only [htoEnd, lie_eq_smul, Module.End.smul_def, had] using h

/-- **Pushing an endomorphism past a locally nilpotent exponential.** If the `m`-fold iterated
commutator `(fun h ↦ ⁅f, h⁆)^[m] g` vanishes in `Module.End R M`, then
`exp f (g x) = (∑ j ∈ range m, (j ! : ℚ)⁻¹ • (fun h ↦ ⁅f, h⁆)^[j] g) (exp f x)`. -/
theorem locallyNilpotentExp_apply_eq_sum_of_iterate_lie_eq_zero {g : Module.End R M} {m : ℕ}
    (hfg : (fun h ↦ ⁅f, h⁆)^[m] g = 0) (x : M) :
    locallyNilpotentExp f hf (g x) =
      (∑ j ∈ range m, (j.factorial : ℚ)⁻¹ • (fun h ↦ ⁅f, h⁆)^[j] g)
        (locallyNilpotentExp f hf x) := by
  let : LieRing (Module.End R M) := LieRing.ofAssociativeRing
  let d : ℕ → Module.End R M := fun j ↦ (fun h ↦ ⁅f, h⁆)^[j] g
  have hd_zero (j : ℕ) (hj : m ≤ j) : d j = 0 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj
    induction t with
    | zero => exact hfg
    | succ t ih =>
      simpa [d, ← add_assoc, Function.iterate_succ_apply', Ring.lie_def] using
        congrArg (fun h ↦ ⁅f, h⁆) ih
  obtain ⟨k, hk⟩ := hf x
  have hterm_zero (i j : ℕ) (hij : m ≤ i ∨ k ≤ j) : d i ((f ^ j) x) = 0 := by
    rcases hij with hi | hj
    · rw [hd_zero _ hi, LinearMap.zero_apply]
    · rw [pow_map_zero_of_le hj hk, map_zero]
  have hgx : (f ^ (m + k)) (g x) = 0 := by
    rw [pow_apply_apply_eq_sum_antidiagonal]
    refine sum_eq_zero fun ij hij ↦ ?_
    have hsum := mem_antidiagonal.mp hij
    rw [hterm_zero ij.fst ij.snd (by omega), smul_zero]
  rw [locallyNilpotentExp_apply_eq_sum f hf hgx,
    locallyNilpotentExp_apply_eq_sum f hf hk, LinearMap.sum_apply]
  simp_rw [pow_apply_apply_eq_sum_antidiagonal, smul_sum, LinearMap.smul_apply, map_sum,
    smul_sum, map_rat_smul, smul_smul]
  have hterm (n : ℕ) :
      ∑ ij ∈ antidiagonal n,
        (n.factorial : ℚ)⁻¹ • n.choose ij.fst •
          ((fun h ↦ ⁅f, h⁆)^[ij.fst] g) ((f ^ ij.snd) x) =
        ∑ ij ∈ antidiagonal n,
          ((ij.fst.factorial : ℚ)⁻¹ * (ij.snd.factorial : ℚ)⁻¹) •
            ((fun h ↦ ⁅f, h⁆)^[ij.fst] g) ((f ^ ij.snd) x) := by
    refine sum_congr rfl fun ij hij ↦ ?_
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      Nat.inv_factorial_mul_choose (K := ℚ) n ij.fst ij.snd (mem_antidiagonal.mp hij)]
  simp_rw [hterm]
  exact TauCeti.sum_range_add_antidiagonal_of_support m k
    (fun ij ↦ ((ij.fst.factorial : ℚ)⁻¹ * (ij.snd.factorial : ℚ)⁻¹) •
      ((fun h ↦ ⁅f, h⁆)^[ij.fst] g) ((f ^ ij.snd) x))
    fun i j hij ↦ by rw [hterm_zero i j hij, smul_zero]

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

/-- **Naturality of Mathlib's exponential.** An additive map `g` with `g ∘ f = f' ∘ g` carries
`IsNilpotent.exp f` to `IsNilpotent.exp f'` for nilpotent `f` and `f'`. The two endomorphisms may
be linear over different semirings. -/
theorem map_exp {S N F : Type*} [Semiring S] [AddCommGroup N] [Module S N] [Module ℚ N]
    [FunLike F M N] [AddMonoidHomClass F M N] {f' : Module.End S N} (hnil : IsNilpotent f)
    (hnil' : IsNilpotent f') (g : F) (hg : Function.Semiconj g f f') (x : M) :
    g (IsNilpotent.exp f x) = IsNilpotent.exp f' (g x) := by
  rw [← LinearMap.congr_fun (locallyNilpotentExp_eq_exp f hnil) x,
    ← LinearMap.congr_fun (locallyNilpotentExp_eq_exp f' hnil') (g x), LinearEquiv.coe_coe,
    LinearEquiv.coe_coe]
  exact map_locallyNilpotentExp f _ _ g hg x

end Module.End

/-!
### Nilpotent exponentials and algebra automorphisms

This section studies Mathlib's `IsNilpotent.exp` of an endomorphism. It commutes with scalar
restriction and preserves stable submodules whose coefficient semiring carries a compatible
`ℚ`-action. For a nilpotent endomorphism it fixes the vectors in the kernel, and a
Leibniz-compatible bilinear pairing intertwines the exponentials of nilpotent endomorphisms.
Consequently, a nilpotent derivation of an algebra exponentiates to an algebra automorphism.
-/

section BilinearPairings

namespace LinearMap

open IsNilpotent TensorProduct

variable {R M N P : Type*} [CommSemiring R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

/-- A Leibniz-compatible bilinear pairing intertwines nilpotent exponentials.

This generalizes `Module.End.exp_mul_of_derivation` from algebra multiplication to an `R`-bilinear
pairing. -/
theorem exp_bilinear_of_leibniz
    (f : M →ₗ[R] N →ₗ[R] P)
    (D₁ : Module.End R M) (D₂ : Module.End R N) (D₃ : Module.End R P)
    (h : ∀ x y, D₃ (f x y) = f x (D₂ y) + f (D₁ x) y)
    (h₁ : IsNilpotent D₁) (h₂ : IsNilpotent D₂) (h₃ : IsNilpotent D₃)
    (x : M) (y : N) :
    exp D₃ (f x y) = f (exp D₁ x) (exp D₂ y) := by
  -- The tensor-product argument follows `Module.End.exp_mul_of_derivation`.
  let DL : Module.End R (M ⊗[R] N) := D₂.lTensor M
  let DR : Module.End R (M ⊗[R] N) := D₁.rTensor N
  have h_nilL : IsNilpotent DL := h₂.map <| Module.End.lTensorAlgHom R N M
  have h_nilR : IsNilpotent DR := h₁.map <| Module.End.rTensorAlgHom R M N
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift f
  have h_nil : IsNilpotent (DL + DR) := h_comm.isNilpotent_add h_nilL h_nilR
  have hm : D₃ ∘ₗ m = m ∘ₗ (DL + DR) := by
    ext
    simp [DL, DR, m, h]
  -- Over a commutative semiring, `Module.End.map_exp` replaces Mathlib's
  -- `Module.End.commute_exp_left_of_commute`, which needs a commutative ring.
  have he := Module.End.map_exp (DL + DR) h_nil h₃ m
    (fun w ↦ (LinearMap.congr_fun hm w).symm) (x ⊗ₜ[R] y)
  have hl : exp DL = (exp D₂).lTensor M :=
    (h₂.map_exp (Module.End.lTensorAlgHom R N M)).symm
  have hr : exp DR = (exp D₁).rTensor N :=
    (h₁.map_exp (Module.End.rTensorAlgHom R M N)).symm
  simpa [exp_add_of_commute h_comm h_nilL h_nilR, hl, hr, m] using he.symm

end LinearMap

end BilinearPairings

namespace Module.End

section RestrictScalars

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommGroup M]
  [Module R M] [Module S M] [Module ℚ M] [LinearMap.CompatibleSMul M M R S]

/-- Restricting the scalars of an endomorphism commutes with Mathlib's exponential. For a
non-nilpotent endomorphism both sides are the junk value `0`, since scalar restriction preserves
and reflects nilpotence. -/
@[simp]
theorem restrictScalars_exp (D : Module.End S M) :
    (IsNilpotent.exp D).restrictScalars R = IsNilpotent.exp (D.restrictScalars R) := by
  by_cases hD : IsNilpotent D
  · simpa only [restrictScalarsRingHom_apply] using hD.map_exp (restrictScalarsRingHom R S M)
  · rw [IsNilpotent.exp_eq_zero_of_not_isNilpotent hD,
      IsNilpotent.exp_eq_zero_of_not_isNilpotent (isNilpotent_restrictScalars_iff.not.2 hD),
      LinearMap.restrictScalars_zero]

end RestrictScalars

/-! ### Invariant submodules

Mathlib's exponential of an endomorphism preserves every submodule stable under it whose
coefficient semiring carries a compatible `ℚ`-action. The compatibility is expressed by
`SMul ℚ K`, `Module ℚ M`, and `IsScalarTower ℚ K M`; the endomorphism may use a different
semiring.
-/

/-- With compatible `ℚ`-actions on the semiring and the module, Mathlib's exponential preserves
every submodule stable under its endomorphism. -/
theorem exp_apply_mem_of_forall_mem {R K M : Type*} [Semiring R] [Semiring K] [AddCommGroup M]
    [Module R M] [Module K M] [Module ℚ M] [SMul ℚ K] [IsScalarTower ℚ K M]
    (D : Module.End R M) (S : Submodule K M)
    (hS : ∀ x ∈ S, D x ∈ S) {x : M} (hx : x ∈ S) :
    IsNilpotent.exp D x ∈ S := by
  have hpow : ∀ n : ℕ, (D ^ n) x ∈ S := by
    intro n
    induction n generalizing x with
    | zero => simpa
    | succ n ih =>
      rw [pow_succ, _root_.mul_apply_eq_comp]
      exact ih (hS x hx)
  rw [IsNilpotent.exp, LinearMap.sum_apply]
  exact S.sum_mem fun n _ => S.smul_of_tower_mem _ (hpow n)

/-- Exponentiating a nilpotent endomorphism fixes every vector in its kernel. -/
theorem exp_apply_of_apply_eq_zero {R M : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] [Module ℚ M] (D : Module.End R M) (hD : IsNilpotent D) {m : M}
    (hm : D m = 0) : IsNilpotent.exp D m = m := by
  have h : (D ^ 1) • m = 0 := by simpa using hm
  simpa using IsNilpotent.exp_smul_eq_sum h hD

section AlgebraAutomorphisms

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Module ℚ A]

/-- The exponential of a nilpotent associative derivation is an algebra automorphism. -/
noncomputable def expAlgEquiv (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    A ≃ₐ[R] A :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (IsNilpotent.exp D)
      (exp_apply_of_apply_eq_zero D hD (by simpa using hder 1 1))
      (LinearMap.exp_bilinear_of_leibniz (LinearMap.mul R A) D D D hder hD hD hD))
    ((Module.End.isUnit_iff _).mp hD.isUnit_exp)

/-- The automorphism acts by Mathlib's exponential. -/
theorem expAlgEquiv_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    D.expAlgEquiv hder hD a = IsNilpotent.exp D a :=
  -- By definition. `AlgEquiv.ofBijective_apply` cannot rewrite it: the `map_mul` field is the
  -- `LinearMap.mul` form of `LinearMap.exp_bilinear_of_leibniz`, equal to `f (x * y) = f x * f y`
  -- only after unfolding `LinearMap.mul`.
  (rfl)

/-- The underlying map of the automorphism is Mathlib's exponential. -/
@[simp]
theorem expAlgEquiv_toLinearMap (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    (D.expAlgEquiv hder hD : A →ₗ[R] A) = IsNilpotent.exp D :=
  LinearMap.ext (expAlgEquiv_apply D hder hD)

/-- The inverse acts by the exponential of the negative endomorphism. -/
theorem expAlgEquiv_symm_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    (D.expAlgEquiv hder hD).symm a = IsNilpotent.exp (-D) a := by
  apply (D.expAlgEquiv hder hD).injective
  simp only [AlgEquiv.apply_symm_apply, expAlgEquiv_apply]
  exact (LinearMap.congr_fun hD.exp_mul_exp_neg_self a).symm

/-- The zero derivation exponentiates to the identity algebra automorphism. -/
@[simp]
theorem expAlgEquiv_zero (hder : ∀ a b, (0 : Module.End R A) (a * b) =
    a * (0 : Module.End R A) b + (0 : Module.End R A) a * b)
    (hD : IsNilpotent (0 : Module.End R A)) :
    (0 : Module.End R A).expAlgEquiv hder hD = AlgEquiv.refl := by
  ext
  simp [expAlgEquiv_apply]

/-- The inverse of a derivation's exponential automorphism is the exponential of its negation. -/
@[simp]
theorem expAlgEquiv_symm (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    (D.expAlgEquiv hder hD).symm = (-D).expAlgEquiv
      (fun a b => by simp [hder a b, add_comm]) hD.neg := by
  ext
  simp [expAlgEquiv_apply, expAlgEquiv_symm_apply]

end AlgebraAutomorphisms

section RestrictScalars

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Ring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [Module ℚ A]

/-- Scalar restriction commutes with exponentiating a nilpotent derivation. -/
@[simp]
theorem restrictScalars_expAlgEquiv (D : Module.End S A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    (D.expAlgEquiv hder hD).restrictScalars R =
      Module.End.expAlgEquiv (D.restrictScalars R) (fun a b => hder a b)
        ((isNilpotent_restrictScalars_iff (R := R) (D := D)).2 hD) := by
  ext a
  rw [AlgEquiv.restrictScalars_apply, expAlgEquiv_apply, ← LinearMap.restrictScalars_apply R,
    restrictScalars_exp]
  exact (expAlgEquiv_apply _ _ _ a).symm

end RestrictScalars

end Module.End
