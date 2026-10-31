/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Submodule.LinearMap

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
* `Module.End.locallyNilpotentExp_symm_apply_eq_sum`: the inverse is the exponential series of
  `-f`.
* `Module.End.locallyNilpotentExp_symm`: the inverse is the exponential of `-f`.
* `Module.End.map_locallyNilpotentExp`: an additive map intertwining two locally nilpotent
  endomorphisms intertwines their exponentials.
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

/-- On an `f`-stable `ℚ`-subspace `V` on which `f` is nilpotent, the exponential series of `f` at
a vector of `V` is Mathlib's `IsNilpotent.exp` of the restriction of `f` to `V`. -/
private theorem coe_exp_restrict_apply {V : Submodule ℚ M}
    (hV : ∀ v ∈ V, f.toAddMonoidHom.toRatLinearMap v ∈ V) {n : ℕ}
    (hn : f.toAddMonoidHom.toRatLinearMap.restrict hV ^ n = 0) (v : V) :
    (IsNilpotent.exp (f.toAddMonoidHom.toRatLinearMap.restrict hV) v : M) = expFun f hf v := by
  have hpow (i : ℕ) :
      ((f.toAddMonoidHom.toRatLinearMap.restrict hV ^ i) v : M) = (f ^ i) v := by
    rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, Module.End.pow_apply,
      Module.End.pow_apply, AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe]
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
  have hmem (v : M) : v ∈ V ↔ (f ^ n) v = 0 := by
    rw [LinearMap.mem_ker, Module.End.pow_apply, Module.End.pow_apply,
      AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe]
  have hV : ∀ v ∈ V, f.toAddMonoidHom.toRatLinearMap v ∈ V := fun v hv ↦ by
    rw [AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe, hmem,
      ← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, (hmem v).1 hv, map_zero]
  have hV' : ∀ v ∈ V, (-f).toAddMonoidHom.toRatLinearMap v ∈ V := fun v hv ↦ V.neg_mem (hV v hv)
  have hneg : (-f).toAddMonoidHom.toRatLinearMap.restrict hV' =
      -f.toAddMonoidHom.toRatLinearMap.restrict hV := by
    ext v
    simp only [LinearMap.coe_restrict_apply, LinearMap.neg_apply, Submodule.coe_neg,
      AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe]
  have hnil : f.toAddMonoidHom.toRatLinearMap.restrict hV ^ n = 0 := by
    ext v
    rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, LinearMap.zero_apply,
      Submodule.coe_zero]
    exact v.2
  have hnil' : (-f).toAddMonoidHom.toRatLinearMap.restrict hV' ^ n = 0 := by
    rw [hneg, neg_pow (R := Module.End ℚ V), hnil, mul_zero]
  have hx : x ∈ V := (hmem x).2 hn
  rw [← coe_exp_restrict_apply f hf hV hnil ⟨x, hx⟩, ← coe_exp_restrict_apply (-f) hg hV' hnil',
    hneg, ← Module.End.mul_apply, IsNilpotent.exp_neg_mul_exp_self ⟨n, hnil⟩,
    Module.End.one_apply]

/-- **The exponential of a locally nilpotent endomorphism.** If every vector of `M` is killed by
some power of `f`, the exponential series `∑ (fⁱ x) / i!` is a finite sum at every vector `x`, and
it defines an `R`-linear automorphism of `M` whose inverse is the exponential series of `-f`. -/
noncomputable def locallyNilpotentExp : M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (expLinearMap f hf)
    (expLinearMap (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf))
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf)
        (neg_neg f).symm hf x)
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg f hf rfl ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf) x)

/-- **The exponential as a truncated series.** At a vector killed by `f ^ k`, the exponential of
`f` is its exponential series truncated at length `k`. -/
theorem locallyNilpotentExp_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    locallyNilpotentExp f hf x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x :=
  expFun_eq_sum f hf hk

/-- **The inverse of the exponential.** At a vector killed by `f ^ k`, the inverse of the
exponential of `f` is the exponential series of `-f` truncated at length `k`. -/
theorem locallyNilpotentExp_symm_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    (locallyNilpotentExp f hf).symm x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • ((-f) ^ i) x :=
  expFun_eq_sum (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf)
    ((neg_pow_apply_eq_zero_iff f k x).2 hk)

/-- **The inverse of the exponential is the exponential of `-f`.** -/
@[simp]
theorem locallyNilpotentExp_symm :
    (locallyNilpotentExp f hf).symm =
      locallyNilpotentExp (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf) := by
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
    rw [Module.End.pow_apply, Module.End.pow_apply]
    exact (hg.iterate_right i x).symm
  obtain ⟨k, hk⟩ := hf x
  rw [locallyNilpotentExp_apply_eq_sum f hf hk,
    locallyNilpotentExp_apply_eq_sum f' hf' (k := k) (by rw [hpow, hk, map_zero]), map_sum]
  exact sum_congr rfl fun i _ ↦ by rw [hpow, map_rat_smul]

/-- For a nilpotent endomorphism, the exponential is Mathlib's `IsNilpotent.exp`. -/
theorem locallyNilpotentExp_eq_exp (hnil : IsNilpotent f) :
    (locallyNilpotentExp f hf : Module.End R M) = IsNilpotent.exp f := by
  obtain ⟨k, hk⟩ := hnil
  ext x
  rw [LinearEquiv.coe_coe, locallyNilpotentExp_apply_eq_sum f hf (by rw [hk]; rfl),
    IsNilpotent.exp_eq_sum hk, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

end Module.End
