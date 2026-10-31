/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Primary.Decomposition
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Scalar extension to `ℤ_p` of a group of finite exponent

Let `A` be an abelian group killed by some positive integer, for instance a finite abelian group,
and let `p` be a prime. Extending scalars from `ℤ` to `ℤ_p` keeps exactly the `p`-primary
component of `A`: the map `x ↦ 1 ⊗ x` restricts to an additive equivalence

```text
A[p^∞] ≃ ℤ_p ⊗[ℤ] A.
```

Write the exponent of `A` as `p ^ N * m` with `p ∤ m`. An integer `m` prime to `p` is a unit of
`ℤ_p`, so `a ⊗ y = 0` whenever `m • y = 0`, and the prime-to-`p` part of `A` dies in the tensor
product. On the `p`-primary part, which is killed by `p ^ N`, a `p`-adic scalar acts through its
truncation modulo `p ^ N`. The inverse uses an integer `c` with `c ≡ 1 (mod p ^ N)` and `m ∣ c`,
so that `x ↦ c • x` is the projection of `A` onto its `p`-primary component.

This is how the discriminant group of a lattice over `ℤ` is compared with the discriminant group
of its localization at `p`.

## Main declarations

* `TauCeti.AddCommGroup.primaryComponentEquivPadicIntTensor`: the `p`-primary component of a
  group of finite exponent is additively equivalent to its scalar extension to `ℤ_p`.
* `TauCeti.AddCommGroup.primaryComponentEquivPadicIntTensor_apply`: the equivalence is
  `x ↦ 1 ⊗ x`.
* `TauCeti.AddCommGroup.tmul_eq_zero_of_nsmul_eq_zero`: an element killed by an integer prime to
  `p` vanishes in `ℤ_p ⊗[ℤ] A`.
* `TauCeti.AddCommGroup.tmul_eq_one_tmul_appr`: on an element killed by `p ^ N`, a `p`-adic
  scalar acts through its truncation modulo `p ^ N`.

This is the case of finite `ℤ`-modules of the comparison `Â ⊗ M ≅ M̂` between scalar extension
to a completion and completion, since the `p`-adic completion of `A` is its `p`-primary component.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 10.13.
-/

public section

open TensorProduct

namespace TauCeti.AddCommGroup

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [AddCommGroup A]

/-- The decomposition data of an exponent: `p ^ N * m` with `p ∤ m`, and an integer `c` that is
`1` modulo `p ^ N` and divisible by `m`. -/
private theorem exists_idempotent_data (hA : AddMonoid.ExponentExists A) :
    ∃ (N m : ℕ) (c : ℤ), ¬p ∣ m ∧ (∀ x : A, (p ^ N * m) • x = 0) ∧
      ((p : ℤ) ^ N ∣ c - 1) ∧ (m : ℤ) ∣ c := by
  obtain ⟨N, m, hm, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (AddMonoid.exponent_ne_zero.mpr hA) p hp.out.ne_one
  have hcop : IsCoprime ((p : ℤ) ^ N) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm).pow_left N
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨N, m, v * m, hm, fun x ↦ hd ▸ AddMonoid.exponent_nsmul_eq_zero x, ⟨-u, ?_⟩,
    dvd_mul_left _ _⟩
  linear_combination huv

/-- An element killed by a natural number prime to `p` vanishes after scalar extension to
`ℤ_p`, because that number is a unit of `ℤ_p`. -/
theorem tmul_eq_zero_of_nsmul_eq_zero {m : ℕ} (hm : ¬p ∣ m) {y : A} (hy : m • y = 0)
    (a : ℤ_[p]) : a ⊗ₜ[ℤ] y = 0 := by
  obtain ⟨u, hu⟩ :=
    PadicInt.isUnit_natCast_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  have ha : a = (m : ℤ) • (a * ↑u⁻¹) := by
    rw [zsmul_eq_mul, Int.cast_natCast, ← hu, mul_left_comm, Units.mul_inv, mul_one]
  rw [ha, smul_tmul, natCast_zsmul, hy, tmul_zero]

/-- On an element killed by `p ^ N`, a `p`-adic scalar acts through its truncation modulo
`p ^ N`. -/
theorem tmul_eq_one_tmul_appr {N : ℕ} {y : A} (hy : ((p : ℤ) ^ N) • y = 0) (a : ℤ_[p]) :
    a ⊗ₜ[ℤ] y = 1 ⊗ₜ[ℤ] ((a.appr N : ℤ) • y) := by
  obtain ⟨t, ht⟩ := PadicInt.dvd_sub_appr a N
  have ha : a = (a.appr N : ℤ) • (1 : ℤ_[p]) + ((p : ℤ) ^ N) • t := by
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
    push_cast
    linear_combination ht
  conv_lhs => rw [ha]
  rw [add_tmul, smul_tmul, smul_tmul, hy, tmul_zero, add_zero]

section IdempotentData

/-! Throughout, `A` is killed by `p ^ N * m` with `p ∤ m`, and `c` is `1` modulo `p ^ N` and
divisible by `m`, so that `x ↦ c • x` projects `A` onto its `p`-primary component. -/

variable {N m : ℕ} {c : ℤ} (hA : ∀ x : A, (p ^ N * m) • x = 0) (hmc : (m : ℤ) ∣ c)
include hA hmc

omit hp in
/-- `(k * c) • x = 0` whenever `p ^ N ∣ k`. -/
private theorem mul_zsmul_eq_zero {k : ℤ} (hk : (p : ℤ) ^ N ∣ k) (x : A) : (k * c) • x = 0 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨l, rfl⟩ := hmc
  have hk : (p : ℤ) ^ N * j * (m * l) = (j * l) * ((p ^ N * m : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hk, mul_zsmul, natCast_zsmul, hA, zsmul_zero]

omit hp in
/-- `c • x` is killed by `p ^ N`. -/
private theorem pow_zsmul_zsmul_eq_zero (x : A) : ((p : ℤ) ^ N) • c • x = 0 := by
  rw [smul_smul]
  exact mul_zsmul_eq_zero hA hmc dvd_rfl x

/-- The left inverse `a ⊗ x ↦ (appr a N * c) • x` of `x ↦ 1 ⊗ x` on the `p`-primary
component. -/
private noncomputable def tensorRetraction : ℤ_[p] ⊗[ℤ] A →+ A :=
  liftAddHom
    { toFun := fun a ↦ zsmulAddGroupHom ((a.appr N : ℤ) * c)
      map_zero' := by
        ext x
        simpa using congrArg (fun k : ℕ ↦ ((k : ℤ) * c) • x) (PadicInt.appr_natCast (p := p) 0 N)
      map_add' := fun a b ↦ by
        ext x
        simp only [zsmulAddGroupHom_apply, AddMonoidHom.add_apply, ← add_zsmul, ← add_mul]
        have hdvd := (PadicInt.appr_add_modEq a b N).dvd
        push_cast at hdvd
        have h := mul_zsmul_eq_zero hA hmc (dvd_sub_comm.mp hdvd) x
        rwa [sub_mul, sub_zsmul, ← sub_eq_add_neg, sub_eq_zero] at h }
    fun r a x ↦ by
      rw [map_zsmul, map_zsmul]
      rfl

/-- The retraction on pure tensors. -/
private theorem tensorRetraction_tmul (a : ℤ_[p]) (x : A) :
    tensorRetraction hA hmc (a ⊗ₜ x) = ((a.appr N : ℤ) * c) • x :=
  liftAddHom_tmul _ _ _ _

variable (hm : ¬p ∣ m) (hc : (p : ℤ) ^ N ∣ c - 1)
include hm hc

/-- The retraction recovers every `p`-primary element from `1 ⊗ x`. -/
private theorem tensorRetraction_one_tmul {x : A} (hx : x ∈ AddCommGroup.primaryComponent A p) :
    tensorRetraction hA hmc ((1 : ℤ_[p]) ⊗ₜ x) = x := by
  have hpow : ((p : ℤ) ^ N) • x = 0 := by
    rw [← Nat.cast_pow, natCast_zsmul]
    exact pow_nsmul_eq_zero_of_mem_primaryComponent hm hA hx
  -- Mathlib's `zsmul_eq_zsmul_iff_modEq`: congruent integers act alike on `x`.
  have hcong {a b : ℤ} (h : (p : ℤ) ^ N ∣ b - a) : a • x = b • x :=
    zsmul_eq_zsmul_iff_modEq.mpr
      (Int.modEq_iff_dvd.mpr ((addOrderOf_dvd_iff_zsmul_eq_zero.mpr hpow).trans h))
  have h1 : (1 : ℤ_[p]).appr N = 1 % p ^ N := by
    simpa using PadicInt.appr_natCast (p := p) 1 N
  rw [tensorRetraction_tmul, mul_zsmul, hcong (dvd_sub_comm.mp hc), one_zsmul, h1]
  nth_rw 2 [← one_zsmul x]
  exact hcong (by exact_mod_cast (Nat.mod_modEq 1 (p ^ N)).dvd)

/-- Every element of `ℤ_p ⊗[ℤ] A` is `1 ⊗ x` for a `p`-primary `x`. -/
private theorem exists_mem_primaryComponent_one_tmul_eq (t : ℤ_[p] ⊗[ℤ] A) :
    ∃ x ∈ AddCommGroup.primaryComponent A p, (1 : ℤ_[p]) ⊗ₜ[ℤ] x = t := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨x₁, hx₁, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, rfl⟩ := h₂
    exact ⟨x₁ + x₂, add_mem hx₁ hx₂, tmul_add _ _ _⟩
  | tmul a x =>
    have hpow := pow_zsmul_zsmul_eq_zero hA hmc x
    refine ⟨(a.appr N : ℤ) • c • x, zsmul_mem (AddCommGroup.mem_primaryComponent.mpr
      ⟨N, by rwa [← natCast_zsmul, Nat.cast_pow]⟩) _, ?_⟩
    -- The prime-to-`p` part `x - c • x` is killed by `m`, a unit of `ℤ_p`.
    have hrest : a ⊗ₜ[ℤ] (x - c • x) = 0 := by
      refine tmul_eq_zero_of_nsmul_eq_zero hm ?_ a
      obtain ⟨j, hj⟩ := hc
      have hA' : ((p : ℤ) ^ N * m) • x = 0 := by exact_mod_cast hA x
      have hc' : c = (p : ℤ) ^ N * j + 1 := by linear_combination hj
      rw [← natCast_zsmul, hc']
      linear_combination (norm := module) (-j) • hA'
    rw [← tmul_eq_one_tmul_appr hpow, ← add_zero (a ⊗ₜ[ℤ] (c • x)), ← hrest, ← tmul_add,
      add_sub_cancel]

end IdempotentData

variable (p A) in
/-- **The `p`-primary component is the scalar extension to `ℤ_p`.** For an abelian group `A` of
finite exponent, `x ↦ 1 ⊗ x` is an additive equivalence from the `p`-primary component of `A`
onto `ℤ_p ⊗[ℤ] A`. -/
noncomputable def primaryComponentEquivPadicIntTensor (hA : AddMonoid.ExponentExists A) :
    AddCommGroup.primaryComponent A p ≃+ ℤ_[p] ⊗[ℤ] A :=
  AddEquiv.ofBijective
    (((TensorProduct.mk ℤ ℤ_[p] A 1).toAddMonoidHom).comp
      (AddCommGroup.primaryComponent A p).subtype) <| by
    obtain ⟨N, m, c, hm, hA, hc, hmc⟩ := exists_idempotent_data (p := p) hA
    refine ⟨fun x y hxy ↦ Subtype.ext ?_, fun t ↦ ?_⟩
    · rw [← tensorRetraction_one_tmul hA hmc hm hc x.property,
        ← tensorRetraction_one_tmul hA hmc hm hc y.property]
      exact congrArg _ hxy
    · obtain ⟨x, hx, rfl⟩ := exists_mem_primaryComponent_one_tmul_eq hA hmc hm hc t
      exact ⟨⟨x, hx⟩, rfl⟩

/-- The equivalence `A[p^∞] ≃ ℤ_p ⊗[ℤ] A` is `x ↦ 1 ⊗ x`. -/
@[simp]
theorem primaryComponentEquivPadicIntTensor_apply (hA : AddMonoid.ExponentExists A)
    (x : AddCommGroup.primaryComponent A p) :
    primaryComponentEquivPadicIntTensor p A hA x = (1 : ℤ_[p]) ⊗ₜ[ℤ] (x : A) := by
  simp only [primaryComponentEquivPadicIntTensor, AddEquiv.ofBijective_apply,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply,
    AddSubgroup.coe_subtype]

end TauCeti.AddCommGroup
