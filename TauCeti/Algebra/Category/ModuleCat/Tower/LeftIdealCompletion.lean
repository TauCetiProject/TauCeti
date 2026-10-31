/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient

/-!
# Completion of a ring along a decreasing family of left ideals

Let `A` be a ring, which need not be commutative, and `J₀ ⊇ J₁ ⊇ J₂ ⊇ ⋯` a decreasing family of
left ideals of `A`. The completion `Â = lim A ⧸ Jₙ` of `A` along the `Jₙ`
(`TauCeti.ModuleTower.quotients`) is a left `A`-module, but the quotients `A ⧸ Jₙ` are not rings,
so `Â` is not a priori a ring. It becomes one when the family has *right shifts*: for every
`b ∈ A` and every `n` there is `m` with `Jₘ b ⊆ Jₙ`. This is the situation of the left ideals
`I_N = U · (𝔤 ⊗ tᴺ ℂ[[t]])` of the enveloping algebra `U` of an affine Kac--Moody algebra at a
fixed level, whose completion `lim_N U / I_N` is the completed enveloping algebra.

The right shifts say exactly that every quotient `A ⧸ Jₙ` is *smooth*: each of its vectors is
killed by some `Jₘ`. On a vector `v` of any `A`-module killed by `Jₙ`, a point `x ∈ Â` acts as
any representative `b ∈ A` of its `n`-th coordinate, and this does not depend on the choices. The
product of `Â` is this action on the coordinates, `(x y)ₙ = x · yₙ`. Concretely, if `b` represents
`xₘ`, `c` represents `yₙ` and `Jₘ c ⊆ Jₙ`, then `(x y)ₙ` is the class of `b c`
(`TauCeti.ModuleTower.limπ_mul_eq`). The ring axioms follow from the laws of this action, in
particular `(x y) · v = x · (y · v)`.

With this product the canonical map `A → Â` is a ring homomorphism
(`TauCeti.ModuleTower.toLimQuotientsRingHom`) whose left multiplications are the `A`-action on
`Â`, the kernels of the projections `Â → A ⧸ Jₙ` are left ideals of `Â` which again have right
shifts, and multiplication is continuous for the inverse limit topology, so `Â` is a topological
ring. Every smooth `A`-module is a module over `Â`
(`TauCeti.ModuleTower.limModuleOfSmooth`): these are the discrete modules of the completed ring.

## Main definitions

* `TauCeti.ModuleTower.instRingLimQuotients`: the ring structure on `lim A ⧸ Jₙ`, for a family
  `Jₙ` with right shifts.
* `TauCeti.ModuleTower.toLimQuotientsRingHom`: the canonical map `A → lim A ⧸ Jₙ`, as a ring
  homomorphism.
* `TauCeti.ModuleTower.limModuleOfSmooth`: the module structure over `lim A ⧸ Jₙ` of an
  `A`-module every vector of which is killed by some `Jₙ`.

## Main results

* `TauCeti.ModuleTower.map_limSMul`: `A`-linear maps commute with the action of the completion.
* `TauCeti.ModuleTower.limπ_mul_eq`: the coordinates of a product are computed by
  representatives.
* `TauCeti.ModuleTower.smul_eq_toLimQuotients_mul`: the `A`-action on the completion is left
  multiplication by the image of `A`.
* `TauCeti.ModuleTower.limπ_mul_eq_zero`: the kernels of the projections are left ideals.
* `TauCeti.ModuleTower.exists_forall_limπ_mul_eq_zero`: these kernels have right shifts.
* `TauCeti.ModuleTower.instIsTopologicalRingLimQuotients`: the completion is a topological ring.
* `TauCeti.ModuleTower.limModuleOfSmooth_smul_eq`: on a smooth module, a point of the completion
  acts as a representative of a coordinate.
* `TauCeti.ModuleTower.isLocallyConstant_limSMul`,
  `TauCeti.ModuleTower.eq_limSMul_of_isLocallyConstant`: the orbit maps of this action are locally
  constant, and it is the only extension of the action of `A` with locally constant orbit maps.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1.2 and §3.2.1, for the completion
  `lim_N U / I_N` of the enveloping algebra of an affine Kac--Moody algebra along left ideals and
  its multiplication.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite Filter Topology

universe u

variable {A : Type u} [Ring A] {J : ℕ → Submodule A A} {hJ : Antitone J}

/-! ### The action on vectors killed by some `Jₙ` -/

section Action

variable {V : Type*} [AddCommGroup V] [Module A V]

/-- Representatives of two coordinates of a point of the completion act equally on a vector
killed by both corresponding left ideals. -/
private theorem smul_eq_smul_of_quotientsπ_eq {x : (quotients J hJ).lim} {v : V} {m n : ℕ}
    (hm : ∀ a ∈ J m, a • v = 0) (hn : ∀ a ∈ J n, a • v = 0) {b c : A}
    (hb : quotientsπ J hJ m b = (quotients J hJ).limπ m x)
    (hc : quotientsπ J hJ n c = (quotients J hJ).limπ n x) : b • v = c • v := by
  wlog hmn : m ≤ n generalizing m n b c
  · exact (this hn hm hc hb (le_of_not_ge hmn)).symm
  have hc' : quotientsπ J hJ m c = (quotients J hJ).limπ m x := by
    rw [← transitionOfLE_quotientsπ J hJ hmn, hc]
    exact LinearMap.congr_fun ((quotients J hJ).transitionOfLE_comp_limπ hmn) x
  rw [← sub_eq_zero, ← sub_smul]
  exact hm _ (by rw [← quotientsπ_eq_zero_iff J hJ, map_sub, hb, hc', sub_self])

open Classical in
/-- The action of a point `x` of the completion on a vector `v` of an `A`-module killed by some
`Jₙ`: a representative in `A` of the `n`-th coordinate of `x` acting on `v`
(`TauCeti.ModuleTower.limSMul_eq`). On the vectors killed by no `Jₙ` it is zero. On a smooth module
it is the action of `TauCeti.ModuleTower.limModuleOfSmooth`, and it defines the product of the
completion. -/
def limSMul (x : (quotients J hJ).lim) (v : V) : V :=
  if h : ∃ n, ∀ a ∈ J n, a • v = 0 then
    (quotientsπ_surjective J hJ h.choose ((quotients J hJ).limπ h.choose x)).choose • v
  else 0

/-- On a vector killed by `Jₙ`, a point of the completion acts as any representative of its
`n`-th coordinate. -/
theorem limSMul_eq {x : (quotients J hJ).lim} {v : V} {n : ℕ} (hv : ∀ a ∈ J n, a • v = 0) {b : A}
    (hb : quotientsπ J hJ n b = (quotients J hJ).limπ n x) : limSMul x v = b • v := by
  have h : ∃ n, ∀ a ∈ J n, a • v = 0 := ⟨n, hv⟩
  simp only [limSMul, h, ↓reduceDIte]
  exact smul_eq_smul_of_quotientsπ_eq h.choose_spec hv
    (quotientsπ_surjective J hJ _ ((quotients J hJ).limπ _ x)).choose_spec hb

/-- Every point of the completion acts on a vector killed by `Jₙ` through a representative of
its `n`-th coordinate. -/
private theorem exists_limSMul_eq (x : (quotients J hJ).lim) {v : V} {n : ℕ}
    (hv : ∀ a ∈ J n, a • v = 0) :
    ∃ b : A, quotientsπ J hJ n b = (quotients J hJ).limπ n x ∧ limSMul x v = b • v := by
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n x)
  exact ⟨b, hb, limSMul_eq hv hb⟩

private theorem limSMul_toLimQuotients (b : A) {v : V} (hv : ∃ n, ∀ a ∈ J n, a • v = 0) :
    limSMul (toLimQuotients J hJ b) v = b • v := by
  obtain ⟨n, hn⟩ := hv
  exact limSMul_eq hn (by rw [limπ_apply, coe_toLimQuotients_apply])

/-- On the vectors killed by no `Jₙ`, the action of the completion is zero. -/
theorem limSMul_of_not_exists {x : (quotients J hJ).lim} {v : V}
    (hv : ¬∃ n, ∀ a ∈ J n, a • v = 0) : limSMul x v = 0 := by
  simp only [limSMul, hv, ↓reduceDIte]

private theorem limSMul_zero_left (v : V) : limSMul (0 : (quotients J hJ).lim) v = 0 := by
  by_cases hv : ∃ n, ∀ a ∈ J n, a • v = 0
  · obtain ⟨n, hn⟩ := hv
    rw [limSMul_eq hn (b := 0) (by simp), zero_smul]
  · exact limSMul_of_not_exists hv

private theorem limSMul_zero_right (x : (quotients J hJ).lim) : limSMul x (0 : V) = 0 := by
  obtain ⟨b, -, hb⟩ := exists_limSMul_eq x (v := (0 : V)) (n := 0) (fun _ _ ↦ smul_zero _)
  rw [hb, smul_zero]

private theorem limSMul_add_left (x y : (quotients J hJ).lim) {v : V}
    (hv : ∃ n, ∀ a ∈ J n, a • v = 0) :
    limSMul (x + y) v = limSMul x v + limSMul y v := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨b, hb, hxb⟩ := exists_limSMul_eq x hn
  obtain ⟨c, hc, hyc⟩ := exists_limSMul_eq y hn
  rw [hxb, hyc, ← add_smul, limSMul_eq hn (b := b + c) (by rw [map_add, hb, hc, map_add])]

private theorem limSMul_add_right (x : (quotients J hJ).lim) {v w : V}
    (hv : ∃ n, ∀ a ∈ J n, a • v = 0) (hw : ∃ n, ∀ a ∈ J n, a • w = 0) :
    limSMul x (v + w) = limSMul x v + limSMul x w := by
  obtain ⟨m, hm⟩ := hv
  obtain ⟨n, hn⟩ := hw
  have hm' : ∀ a ∈ J (max m n), a • v = 0 := fun a ha ↦ hm a (hJ (le_max_left m n) ha)
  have hn' : ∀ a ∈ J (max m n), a • w = 0 := fun a ha ↦ hn a (hJ (le_max_right m n) ha)
  obtain ⟨b, hb, hvb⟩ := exists_limSMul_eq x hm'
  rw [hvb, limSMul_eq hn' hb, limSMul_eq (fun a ha ↦ by rw [smul_add, hm' a ha, hn' a ha,
    add_zero]) hb, smul_add]

/-- `A`-linear maps commute with the action of the completion on vectors killed by some `Jₙ`. -/
theorem map_limSMul {W : Type*} [AddCommGroup W] [Module A W] (f : V →ₗ[A] W)
    (x : (quotients J hJ).lim) {v : V} (hv : ∃ n, ∀ a ∈ J n, a • v = 0) :
    f (limSMul x v) = limSMul x (f v) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨b, hb, hvb⟩ := exists_limSMul_eq x hn
  rw [hvb, map_smul, limSMul_eq (fun a ha ↦ by rw [← map_smul, hn a ha, map_zero]) hb]

/-- The orbit map `x ↦ x · v` of a vector killed by some `Jₙ` is locally constant: it only
depends on the `n`-th coordinate. -/
theorem isLocallyConstant_limSMul {v : V} (hv : ∃ n, ∀ a ∈ J n, a • v = 0) :
    IsLocallyConstant fun x : (quotients J hJ).lim ↦ limSMul x v := by
  obtain ⟨n, hn⟩ := hv
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_
  filter_upwards [((quotients J hJ).hasBasis_nhds x).mem_of_mem (i := n) trivial] with y hy
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n x)
  rw [limSMul_eq hn (hb.trans hy.symm), limSMul_eq hn hb]

/-- **Uniqueness of the extended action.** A locally constant map `f` on the completion with
`f b = b • v` for `b ∈ A` is the orbit map `x ↦ x · v`, for a vector `v` killed by some `Jₙ`. -/
theorem eq_limSMul_of_isLocallyConstant {v : V} (hv : ∃ n, ∀ a ∈ J n, a • v = 0)
    {f : (quotients J hJ).lim → V} (hf : IsLocallyConstant f)
    (hfv : ∀ b : A, f (toLimQuotients J hJ b) = b • v) (x : (quotients J hJ).lim) :
    f x = limSMul x v := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨k, -, hk⟩ := ((quotients J hJ).hasBasis_nhds x).eventually_iff.1 (hf.eventually_eq x)
  -- A representative of the coordinate of index `max k n` serves both the local constancy of `f`,
  -- through the coordinate of index `k`, and the action on `v`, which `Jₙ` kills.
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ (max k n) ((quotients J hJ).limπ (max k n) x)
  have hbk : (quotients J hJ).limπ k (toLimQuotients J hJ b) = (quotients J hJ).limπ k x := by
    rw [← (quotients J hJ).transitionOfLE_comp_limπ (le_max_left k n), LinearMap.comp_apply,
      LinearMap.comp_apply, limπ_apply, coe_toLimQuotients_apply, hb]
  rw [← hk hbk, hfv, limSMul_eq (fun a ha ↦ hn a (hJ (le_max_right k n) ha)) hb]

end Action

/-! ### The ring structure -/

section Ring

/-- The unit of the completion is the image of `1 ∈ A`. -/
instance : One (quotients J hJ).lim where
  one := toLimQuotients J hJ 1

@[simp]
theorem toLimQuotients_one : toLimQuotients J hJ 1 = 1 :=
  (rfl)

/-- The `n`-th coordinate of `1` is the class of `1 ∈ A`. -/
@[simp]
theorem coe_one_apply (n : ℕ) :
    ((1 : (quotients J hJ).lim) : (quotients J hJ).Product) n = quotientsπ J hJ n 1 :=
  coe_toLimQuotients_apply J hJ 1 n

/-- The `n`-th coordinate of `1` is the class of `1 ∈ A`. -/
theorem limπ_one (n : ℕ) : (quotients J hJ).limπ n 1 = quotientsπ J hJ n 1 :=
  (limπ_apply _ n 1).trans (coe_one_apply n)

variable {V : Type*} [AddCommGroup V] [Module A V]

private theorem limSMul_one {v : V}
    (hv : ∃ n, ∀ a ∈ J n, a • v = 0) : limSMul (1 : (quotients J hJ).lim) v = v := by
  rw [← toLimQuotients_one, limSMul_toLimQuotients 1 hv, one_smul]

variable [hmul : Fact (∀ (b : A) (n : ℕ), ∃ m, ∀ x ∈ J m, x * b ∈ J n)]

variable (hJ) in
/-- With right shifts, every vector of a quotient `A ⧸ Jₙ` is killed by some `Jₘ`. -/
private theorem exists_smul_quotients_eq_zero {n : ℕ} (q : (quotients J hJ).obj (op n)) :
    ∃ m, ∀ a ∈ J m, a • q = 0 := by
  obtain ⟨c, rfl⟩ := quotientsπ_surjective J hJ n q
  obtain ⟨m, hm⟩ := hmul.out c n
  exact ⟨m, fun a ha ↦ by rw [← map_smul, smul_eq_mul, quotientsπ_eq_zero_iff]; exact hm a ha⟩

include hmul in
/-- The product of the completion: `(x y)ₙ = x · yₙ`. -/
instance : Mul (quotients J hJ).lim where
  mul x y := ⟨fun n ↦ limSMul x ((quotients J hJ).limπ n y), (quotients J hJ).mem_lim.2 fun n ↦ by
    rw [map_limSMul _ _ (exists_smul_quotients_eq_zero hJ _), ← LinearMap.comp_apply,
      transition_comp_limπ]⟩

/-- The `n`-th coordinate of `x y` is `x · yₙ`. -/
theorem limπ_mul (x y : (quotients J hJ).lim) (n : ℕ) :
    (quotients J hJ).limπ n (x * y) = limSMul x ((quotients J hJ).limπ n y) := by
  rw [limπ_apply]
  -- The coordinates of `x * y` are `limSMul x yₙ` by definition of the product.
  rfl

/-- **The product is computed by representatives.** If `b` represents the `m`-th coordinate of
`x`, `c` represents the `n`-th coordinate of `y` and `Jₘ c ⊆ Jₙ`, then the `n`-th coordinate of
`x y` is the class of `b c`. -/
theorem limπ_mul_eq {x y : (quotients J hJ).lim} {m n : ℕ} {b c : A}
    (hb : quotientsπ J hJ m b = (quotients J hJ).limπ m x)
    (hc : quotientsπ J hJ n c = (quotients J hJ).limπ n y) (hmn : ∀ a ∈ J m, a * c ∈ J n) :
    (quotients J hJ).limπ n (x * y) = quotientsπ J hJ n (b * c) := by
  rw [limπ_mul, ← hc, limSMul_eq (fun a ha ↦ ?_) hb, ← map_smul, smul_eq_mul]
  rw [← map_smul, smul_eq_mul, quotientsπ_eq_zero_iff]
  exact hmn a ha

private theorem limSMul_mul (x y : (quotients J hJ).lim) {v : V} (hv : ∃ n, ∀ a ∈ J n, a • v = 0) :
    limSMul (x * y) v = limSMul x (limSMul y v) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨c, hc, hyc⟩ := exists_limSMul_eq y hn
  obtain ⟨m, hm⟩ := hmul.out c n
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ m ((quotients J hJ).limπ m x)
  -- `Jₘ` kills `c • v`, because `Jₘ c ⊆ Jₙ` kills `v`.
  have hcv : ∀ a ∈ J m, a • c • v = 0 := fun a ha ↦ by rw [← mul_smul, hn _ (hm a ha)]
  rw [hyc, limSMul_eq hcv hb, ← mul_smul, limSMul_eq hn (limπ_mul_eq hb hc hm).symm]

include hmul in
/-- **The completion of `A` along a decreasing family of left ideals with right shifts is a
ring**, with product `(x y)ₙ = x · yₙ` and unit the image of `1`. -/
instance instRingLimQuotients : Ring (quotients J hJ).lim :=
  { (inferInstance : AddCommGroup (quotients J hJ).lim) with
    mul_assoc x y z := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, limπ_mul, limπ_mul, limSMul_mul _ _ (exists_smul_quotients_eq_zero hJ _)]
    one_mul x := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, limSMul_one (exists_smul_quotients_eq_zero hJ _)]
    mul_one x := (quotients J hJ).lim_ext fun n ↦ by
      obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n x)
      rw [limπ_mul_eq hb (limπ_one n).symm (fun a ha ↦ by rwa [mul_one]), mul_one, hb]
    left_distrib x y z := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, map_add, map_add, limπ_mul, limπ_mul,
        limSMul_add_right _ (exists_smul_quotients_eq_zero hJ _)
          (exists_smul_quotients_eq_zero hJ _)]
    right_distrib x y z := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, map_add, limπ_mul, limπ_mul,
        limSMul_add_left _ _ (exists_smul_quotients_eq_zero hJ _)]
    zero_mul x := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, limSMul_zero_left, map_zero]
    mul_zero x := (quotients J hJ).lim_ext fun n ↦ by
      rw [limπ_mul, map_zero, limSMul_zero_right] }

/-- The `A`-action on the completion is left multiplication by the image of `A`. -/
theorem smul_eq_toLimQuotients_mul (b : A) (x : (quotients J hJ).lim) :
    b • x = toLimQuotients J hJ b * x :=
  (quotients J hJ).lim_ext fun n ↦ by
    rw [map_smul, limπ_mul, limSMul_toLimQuotients b (exists_smul_quotients_eq_zero hJ _)]

@[simp]
theorem toLimQuotients_mul (b c : A) :
    toLimQuotients J hJ (b * c) = toLimQuotients J hJ b * toLimQuotients J hJ c := by
  rw [← smul_eq_toLimQuotients_mul, ← map_smul, smul_eq_mul]

variable (J hJ) in
/-- **The canonical map `A → lim A ⧸ Jₙ` is a ring homomorphism.** -/
def toLimQuotientsRingHom : A →+* (quotients J hJ).lim where
  toFun := toLimQuotients J hJ
  map_one' := toLimQuotients_one
  map_mul' := toLimQuotients_mul
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem coe_toLimQuotientsRingHom :
    ⇑(toLimQuotientsRingHom J hJ) = toLimQuotients J hJ :=
  (rfl)

/-- **The kernels of the projections are left ideals** of the completion. -/
theorem limπ_mul_eq_zero (x : (quotients J hJ).lim) {y : (quotients J hJ).lim} {n : ℕ}
    (hy : (quotients J hJ).limπ n y = 0) :
    (quotients J hJ).limπ n (x * y) = 0 := by
  rw [limπ_mul, hy, limSMul_zero_right]

/-- **The kernels of the projections have right shifts:** for every `y` and `n` there is `m` such
that `x y` lies in the kernel of the `n`-th projection whenever `x` lies in that of the `m`-th. -/
theorem exists_forall_limπ_mul_eq_zero (y : (quotients J hJ).lim) (n : ℕ) :
    ∃ m, ∀ x : (quotients J hJ).lim,
      (quotients J hJ).limπ m x = 0 → (quotients J hJ).limπ n (x * y) = 0 := by
  obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n y)
  obtain ⟨m, hm⟩ := hmul.out c n
  refine ⟨m, fun x hx ↦ ?_⟩
  rw [limπ_mul_eq (b := 0) (by rw [map_zero, hx]) hc hm, zero_mul, map_zero]

/-- **The completion is a topological ring:** the `n`-th coordinate of `x y` only depends on
the `m`-th coordinate of `x` and the `n`-th coordinate of `y`, for some `m`. -/
instance instIsTopologicalRingLimQuotients : IsTopologicalRing (quotients J hJ).lim where
  continuous_mul := continuous_iff_continuousAt.2 fun p ↦ by
    refine tendsto_nhds_iff.2 fun n ↦ ?_
    obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n p.2)
    obtain ⟨m, hm⟩ := hmul.out c n
    obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ m ((quotients J hJ).limπ m p.1)
    have h₁ : {x | (quotients J hJ).limπ m x = (quotients J hJ).limπ m p.1} ∈ 𝓝 p.1 :=
      (hasBasis_nhds _ p.1).mem_of_mem (i := m) trivial
    have h₂ : {y | (quotients J hJ).limπ n y = (quotients J hJ).limπ n p.2} ∈ 𝓝 p.2 :=
      (hasBasis_nhds _ p.2).mem_of_mem (i := n) trivial
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod h₁ h₂] with q hq
    rw [limπ_mul_eq (hb.trans hq.1.symm) (hc.trans hq.2.symm) hm, limπ_mul_eq hb hc hm]

end Ring

/-! ### Smooth modules are modules over the completion -/

section Module

variable [Fact (∀ (b : A) (n : ℕ), ∃ m, ∀ x ∈ J m, x * b ∈ J n)]
  {V : Type*} [AddCommGroup V] [Module A V]

variable (hJ) in
/-- **A smooth `A`-module is a module over the completion** `lim A ⧸ Jₙ`: a vector killed by `Jₙ`
is acted on through representatives of `n`-th coordinates. -/
@[reducible]
def limModuleOfSmooth (hV : ∀ v : V, ∃ n, ∀ a ∈ J n, a • v = 0) :
    Module (quotients J hJ).lim V where
  smul := limSMul
  one_smul v := limSMul_one (hV v)
  mul_smul x y v := limSMul_mul x y (hV v)
  smul_zero := limSMul_zero_right
  smul_add x v w := limSMul_add_right x (hV v) (hV w)
  add_smul x y v := limSMul_add_left x y (hV v)
  zero_smul := limSMul_zero_left

/-- On a vector killed by `Jₙ`, a point of the completion acts as any representative of its
`n`-th coordinate. -/
theorem limModuleOfSmooth_smul_eq (hV : ∀ v : V, ∃ n, ∀ a ∈ J n, a • v = 0)
    {x : (quotients J hJ).lim} {v : V} {n : ℕ} (hv : ∀ a ∈ J n, a • v = 0) {b : A}
    (hb : quotientsπ J hJ n b = (quotients J hJ).limπ n x) :
    letI := limModuleOfSmooth hJ hV
    x • v = b • v :=
  limSMul_eq hv hb

/-- The image of `b ∈ A` in the completion acts on a smooth module as `b`. -/
theorem limModuleOfSmooth_toLimQuotients_smul (hV : ∀ v : V, ∃ n, ∀ a ∈ J n, a • v = 0) (b : A)
    (v : V) :
    letI := limModuleOfSmooth hJ hV
    toLimQuotients J hJ b • v = b • v :=
  limSMul_toLimQuotients b (hV v)

end Module

end TauCeti.ModuleTower
