/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization
import TauCeti.RingTheory.Valuation.FinsetDvd
import TauCeti.LinearAlgebra.Quotient.PiSpanSingleton

/-!
# Elementary automorphisms of a free pro-`p` group and the exponent vector of a relator

Let `F = freeProP p X` be the free pro-`p` group on a type `X`. This file studies the two kinds of
elementary automorphisms of `F` that act on the exponent vector `TauCeti.freeProP.exponentSum` in
`ℤ_p^X` through elementary matrices, computes that action, and uses them, for `X` finite, to
normalise the exponent vector of an arbitrary element of `F`:

* `TauCeti.freeProP.congr σ`, for a bijection `σ` of the generating type, permutes the generators;
  it permutes the coordinates of the exponent vector.
* `TauCeti.freeProP.transvection x₀ x hx a`, for `x ≠ x₀` and a `p`-adic exponent `a`, sends the
  generator at `x₀` to `x₀ · x ^ a` and fixes the other generators; its inverse is the transvection
  with exponent `-a`, and it adds `a` times the coordinate at `x₀` to the coordinate at `x` of the
  exponent vector.

The normalisation is the elimination step of Labute's classification of Demushkin groups: if the
exponent vector of `r ∈ F` is `q • w` with `w x₀ = 1`, then some automorphism `e` of `F` has
`exponentSum (e r) = q e_{x₀}`, that is `e r ∈ x₀ ^ q · [F, F]` by
`TauCeti.freeProP.toAdd_exponentSum_eq_single_iff`
(`TauCeti.freeProP.exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_eq_smul`). Since `ℤ_p`
is a valuation ring, some coordinate of the exponent vector divides all the others, so every `r`
admits such a normalisation, with the pivot coordinate placed at any prescribed generator
(`TauCeti.freeProP.exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_forall_dvd`,
`TauCeti.freeProP.exists_continuousMulEquiv_toAdd_exponentSum_eq_single`). For a one-relator
pro-`p` group `⟨X ∣ r⟩` this is the statement that, after a change of basis of `F`, the relator is
`x₀ ^ q` times an element of the closed commutator subgroup, where `q` generates the ideal of
`ℤ_p` spanned by the exponent sums of `r`; the abelianization of the group is then
`ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ q ℤ_p`, so `q` is the coordinate whose `p`-adic valuation the one-relator
abelianization structure theorem reads off.

## Main definitions

* `TauCeti.freeProP.transvection`: the automorphism `x₀ ↦ x₀ · x ^ a` of `freeProP p X`.

## Main results

* `TauCeti.freeProP.transvection_symm`, `TauCeti.freeProP.transvection_zero`,
  `TauCeti.freeProP.transvection_add`: the transvections at fixed `x₀, x` form a one-parameter
  group of automorphisms.
* `TauCeti.freeProP.toAdd_exponentSum_congr`, `TauCeti.freeProP.toAdd_exponentSum_transvection`:
  the exponent vectors of the images under the two elementary automorphisms.
* `TauCeti.freeProP.exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_eq_smul`: if the
  exponent vector of `r` is `q • w` with `w x₀ = 1`, an automorphism of `freeProP p X` carries `r`
  to an element with exponent vector `q e_{x₀}`.
* `TauCeti.freeProP.exists_continuousMulEquiv_toAdd_exponentSum_eq_single`: every element of
  `freeProP p X`, for `X` finite, is carried by an automorphism to an element whose exponent
  vector is supported at a prescribed generator, with value a coordinate of the original exponent
  vector dividing all the others.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.3.
-/

public section

namespace TauCeti

open Multiplicative

universe u

variable {p : ℕ} [Fact p.Prime] {X Y : Type u}

namespace freeProP

/-! ### Permuting the generators -/

/-- **Permuting the generators permutes the exponent vector**: the exponent vector of `congr σ y`
is the exponent vector of `y` composed with `σ⁻¹`. -/
@[simp]
theorem toAdd_exponentSum_congr (σ : X ≃ Y) (y : freeProP p X) :
    (exponentSum p Y (congr σ y)).toAdd = (exponentSum p X y).toAdd ∘ σ.symm := by
  classical
  -- Both sides are continuous homomorphisms of `y`; compare them on the generators.
  let Ψ : Multiplicative (X → ℤ_[p]) →ₜ* Multiplicative (Y → ℤ_[p]) :=
    { toFun u := ofAdd (u.toAdd ∘ σ.symm)
      map_one' := by simp
      map_mul' u v := by rw [toAdd_mul, ← ofAdd_add]; rfl
      continuous_toFun := continuous_ofAdd.comp
        (continuous_pi fun y ↦ (continuous_apply (σ.symm y)).comp continuous_toAdd) }
  have hΨ : ∀ u, Ψ u = ofAdd (u.toAdd ∘ σ.symm) := fun u ↦ rfl
  have h : (exponentSum p Y).comp (congr (p := p) σ : freeProP p X →ₜ* freeProP p Y) =
      Ψ.comp (exponentSum p X) := hom_ext fun x ↦ by
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_coe,
      congr_of, exponentSum_of]
    rw [hΨ, toAdd_ofAdd]
    refine congrArg ofAdd (funext fun y ↦ ?_)
    simp [Pi.single_apply, Equiv.symm_apply_eq]
  have := DFunLike.congr_fun h y
  simpa [hΨ] using congrArg Multiplicative.toAdd this

/-! ### Transvections -/

section Transvection

open scoped Classical in
/-- The lifts of the families `x₀ ↦ x₀ · x ^ a` compose by adding the exponents: the composition
law behind `TauCeti.freeProP.transvection`. -/
private theorem lift_update_mul_padicPow_comp {x₀ x : X} (hx : x ≠ x₀) (a b : ℤ_[p]) :
    (lift (isProP_freeProP p X)
        (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) b))).comp
      (lift (isProP_freeProP p X)
        (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) a))) =
      lift (isProP_freeProP p X)
        (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) (a + b))) :=
  hom_ext fun x' ↦ by
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_of]
    by_cases hx' : x' = x₀
    · subst hx'
      have h := (isProP_freeProP p X).map_padicPow (isProP_freeProP p X)
        (lift (isProP_freeProP p X)
          (Function.update of x' (of x' * (isProP_freeProP p X).padicPow (of x) b)) :
            freeProP p X →* freeProP p X)
        (lift _ _).continuous (of x) a
      rw [MonoidHom.coe_ofClass] at h
      rw [Function.update_self, Function.update_self, map_mul, lift_of, Function.update_self, h,
        lift_of, Function.update_of_ne hx, mul_assoc, ← (isProP_freeProP p X).padicPow_add,
        add_comm]
    · rw [Function.update_of_ne hx', Function.update_of_ne hx', lift_of, Function.update_of_ne hx']

open scoped Classical in
/-- The lift of the family `x₀ ↦ x₀ · x ^ 0` is the identity. -/
private theorem lift_update_mul_padicPow_zero (x₀ x : X) :
    lift (isProP_freeProP p X)
        (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) 0)) =
      ContinuousMonoidHom.id (freeProP p X) :=
  hom_ext fun x' ↦ by
    rw [lift_of, (isProP_freeProP p X).padicPow_zero, mul_one, Function.update_eq_self]
    rfl

open scoped Classical in
/-- **The transvection `x₀ ↦ x₀ · x ^ a`** of the free pro-`p` group on `X`, for generators
`x ≠ x₀` and a `p`-adic exponent `a`: the continuous automorphism sending the generator at `x₀` to
`x₀ · x ^ a` and fixing every other generator. Its inverse is the transvection with exponent `-a`
(`TauCeti.freeProP.transvection_symm`). On the exponent vectors in `ℤ_p^X` it is the elementary
matrix adding `a` times the coordinate at `x₀` to the coordinate at `x`
(`TauCeti.freeProP.toAdd_exponentSum_transvection`). -/
noncomputable def transvection (x₀ x : X) (hx : x ≠ x₀) (a : ℤ_[p]) :
    freeProP p X ≃ₜ* freeProP p X where
  toFun := lift (isProP_freeProP p X)
    (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) a))
  invFun := lift (isProP_freeProP p X)
    (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) (-a)))
  left_inv y := by
    have h := lift_update_mul_padicPow_comp hx a (-a)
    rw [add_neg_cancel, lift_update_mul_padicPow_zero] at h
    simpa using DFunLike.congr_fun h y
  right_inv y := by
    have h := lift_update_mul_padicPow_comp hx (-a) a
    rw [neg_add_cancel, lift_update_mul_padicPow_zero] at h
    simpa using DFunLike.congr_fun h y
  map_mul' := map_mul _
  continuous_toFun := (lift _ _).continuous
  continuous_invFun := (lift _ _).continuous

variable {x₀ x : X} (hx : x ≠ x₀) (a : ℤ_[p])

/-- The transvection `x₀ ↦ x₀ · x ^ a` is the lift of the family sending `x₀` to `x₀ · x ^ a` and
every other generator to itself. -/
theorem coe_transvection [DecidableEq X] :
    ⇑(transvection x₀ x hx a) = ⇑(lift (isProP_freeProP p X)
      (Function.update of x₀ (of x₀ * (isProP_freeProP p X).padicPow (of x) a))) := by
  -- `transvection` is built with the classical instance; identify the two `DecidableEq X`.
  obtain rfl := Subsingleton.elim ‹DecidableEq X› (Classical.decEq X)
  rfl

/-- The transvection `x₀ ↦ x₀ · x ^ a` sends the generator at `x₀` to `x₀ · x ^ a`. -/
@[simp]
theorem transvection_of_self :
    transvection x₀ x hx a (of x₀) = of x₀ * (isProP_freeProP p X).padicPow (of x) a := by
  classical
  rw [coe_transvection, lift_of, Function.update_self]

/-- The transvection `x₀ ↦ x₀ · x ^ a` fixes the generators other than `x₀`. -/
@[simp]
theorem transvection_of_of_ne {x' : X} (hx' : x' ≠ x₀) :
    transvection x₀ x hx a (of x') = of x' := by
  classical
  rw [coe_transvection, lift_of, Function.update_of_ne hx']

/-- The inverse of the transvection `x₀ ↦ x₀ · x ^ a` is the transvection `x₀ ↦ x₀ · x ^ (-a)`. -/
@[simp]
theorem transvection_symm : (transvection x₀ x hx a).symm = transvection x₀ x hx (-a) :=
  ContinuousMulEquiv.ext fun _ ↦ rfl

/-- The transvection with exponent `0` is the identity. -/
@[simp]
theorem transvection_zero : transvection x₀ x hx 0 = ContinuousMulEquiv.refl (freeProP p X) :=
  ContinuousMulEquiv.ext fun y ↦ DFunLike.congr_fun (lift_update_mul_padicPow_zero x₀ x) y

/-- **Transvections at fixed `x₀, x` compose by adding the exponents.** -/
theorem transvection_add (b : ℤ_[p]) :
    transvection x₀ x hx (a + b) = (transvection x₀ x hx a).trans (transvection x₀ x hx b) :=
  ContinuousMulEquiv.ext fun y ↦ (DFunLike.congr_fun (lift_update_mul_padicPow_comp hx a b) y).symm

/-- **The exponent vector under a transvection.** The transvection `x₀ ↦ x₀ · x ^ a` adds `a`
times the coordinate at `x₀` to the coordinate at `x` of the exponent vector, and leaves the other
coordinates unchanged. -/
@[simp]
theorem toAdd_exponentSum_transvection [DecidableEq X] (y : freeProP p X) :
    (exponentSum p X (transvection x₀ x hx a y)).toAdd =
      (exponentSum p X y).toAdd + Pi.single x (a * (exponentSum p X y).toAdd x₀) := by
  -- Both sides are continuous homomorphisms of `y`; compare them on the generators.
  let Ψ : Multiplicative (X → ℤ_[p]) →ₜ* Multiplicative (X → ℤ_[p]) :=
    { toFun u := ofAdd (u.toAdd + Pi.single x (a * u.toAdd x₀))
      map_one' := by simp
      map_mul' u v := by
        rw [toAdd_mul, ← ofAdd_add]
        congr 1
        simp only [Pi.add_apply, mul_add, Pi.single_add]
        abel
      continuous_toFun := by
        have h₁ : Continuous fun u : Multiplicative (X → ℤ_[p]) ↦ a * u.toAdd x₀ :=
          continuous_const.mul ((continuous_apply x₀).comp continuous_toAdd)
        have h₂ : Continuous fun u : Multiplicative (X → ℤ_[p]) ↦
            (Pi.single x (a * u.toAdd x₀) : X → ℤ_[p]) :=
          (continuous_single x).comp h₁
        exact continuous_ofAdd.comp (continuous_toAdd.add h₂) }
  have hΨ : ∀ u, Ψ u = ofAdd (u.toAdd + Pi.single x (a * u.toAdd x₀)) := fun u ↦ rfl
  have h : (exponentSum p X).comp (transvection x₀ x hx a : freeProP p X →ₜ* freeProP p X) =
      Ψ.comp (exponentSum p X) := hom_ext fun x' ↦ by
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_coe,
      exponentSum_of]
    rw [hΨ, toAdd_ofAdd]
    by_cases hx' : x' = x₀
    · subst hx'
      rw [transvection_of_self, map_mul, exponentSum_padicPow_of, exponentSum_of, ← ofAdd_add,
        Pi.single_eq_same, mul_one]
    · rw [transvection_of_of_ne hx a hx', exponentSum_of, Pi.single_eq_of_ne' hx', mul_zero,
        Pi.single_zero, add_zero]
  have := DFunLike.congr_fun h y
  simpa [hΨ] using congrArg Multiplicative.toAdd this

end Transvection

/-! ### Normalising the exponent vector -/

section Normalisation

variable [Finite X] [DecidableEq X]

/-- **Normalising the exponent vector of a relator.** If the exponent vector of `r ∈ freeProP p X`
is `q • w` with `w x₀ = 1`, then an automorphism of `freeProP p X` carries `r` to an element with
exponent vector `q e_{x₀}`, that is to `x₀ ^ q` times an element of the closed commutator subgroup
(`TauCeti.freeProP.toAdd_exponentSum_eq_single_iff`). -/
theorem exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_eq_smul {r : freeProP p X} {x₀ : X}
    {w : X → ℤ_[p]} {q : ℤ_[p]} (hw : w x₀ = 1) (hr : (exponentSum p X r).toAdd = q • w) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, (exponentSum p X (e r)).toAdd = Pi.single x₀ q := by
  cases nonempty_fintype X
  -- The automorphism is the composite of the transvections `x₀ ↦ x₀ · x ^ (-w x)` over the
  -- generators `x ≠ x₀`. Kill the coordinates in a finite set `s` of generators other than `x₀`,
  -- one transvection at a time; the coordinate at `x₀` stays `q`.
  suffices h : ∀ s : Finset X, x₀ ∉ s → ∃ e : freeProP p X ≃ₜ* freeProP p X,
      ∀ x, (exponentSum p X (e r)).toAdd x = if x ∈ s then 0 else q * w x by
    obtain ⟨e, he⟩ := h (Finset.univ.erase x₀) (Finset.notMem_erase x₀ _)
    refine ⟨e, funext fun x ↦ ?_⟩
    rw [he x, Pi.single_apply]
    by_cases hx : x = x₀
    · subst hx
      simp [hw]
    · simp [hx]
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ ↦ ⟨ContinuousMulEquiv.refl _, fun x ↦ by simp [hr]⟩
  | insert x s hxs ih =>
    intro hx₀
    have hxx₀ : x ≠ x₀ := fun h ↦ hx₀ (h ▸ Finset.mem_insert_self x s)
    have hx₀s : x₀ ∉ s := fun h ↦ hx₀ (Finset.mem_insert_of_mem h)
    obtain ⟨e, he⟩ := ih hx₀s
    refine ⟨e.trans (transvection x₀ x hxx₀ (-w x)), fun x' ↦ ?_⟩
    rw [ContinuousMulEquiv.trans_apply, toAdd_exponentSum_transvection, Pi.add_apply, he x',
      he x₀, ite_eq_right hx₀s, hw, mul_one, Pi.single_apply]
    by_cases hx' : x' = x
    · subst hx'
      simp [hxs, mul_comm]
    · simp [hx', Finset.mem_insert]

/-- **Normalising the exponent vector, pivot form.** If the coordinate at `x₁` of the exponent
vector `v` of `r ∈ freeProP p X` divides every coordinate, then for every generator `x₀` an
automorphism of `freeProP p X` carries `r` to an element with exponent vector `v x₁ • e_{x₀}`. -/
theorem exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_forall_dvd {r : freeProP p X}
    {x₁ : X} (hx₁ : ∀ x, (exponentSum p X r).toAdd x₁ ∣ (exponentSum p X r).toAdd x) (x₀ : X) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X,
      (exponentSum p X (e r)).toAdd = Pi.single x₀ ((exponentSum p X r).toAdd x₁) := by
  obtain ⟨w, hw, hv⟩ := exists_eq_smul_of_forall_dvd hx₁
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_eq_smul hw hv
  -- Move the pivot from `x₁` to `x₀` by the transposition of the two generators.
  refine ⟨e.trans (congr (Equiv.swap x₁ x₀)), funext fun x ↦ ?_⟩
  rw [ContinuousMulEquiv.trans_apply, toAdd_exponentSum_congr, Function.comp_apply, he,
    Equiv.symm_swap]
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- **Every element of a free pro-`p` group of finite rank has a normalisable exponent vector.**
For `r ∈ freeProP p X` and a generator `x₀`, some coordinate `v x₁` of the exponent vector `v` of
`r` divides all the others, and an automorphism of `freeProP p X` carries `r` to an element with
exponent vector `v x₁ • e_{x₀}`, that is to `x₀ ^ (v x₁)` times an element of the closed
commutator subgroup. The coordinate `v x₁` generates the ideal of `ℤ_p` spanned by the exponent
sums of `r`, so it is determined up to a unit of `ℤ_p`. -/
theorem exists_continuousMulEquiv_toAdd_exponentSum_eq_single (r : freeProP p X) (x₀ : X) :
    ∃ (x₁ : X) (e : freeProP p X ≃ₜ* freeProP p X),
      (∀ x, (exponentSum p X r).toAdd x₁ ∣ (exponentSum p X r).toAdd x) ∧
        (exponentSum p X (e r)).toAdd = Pi.single x₀ ((exponentSum p X r).toAdd x₁) := by
  have : Nonempty X := ⟨x₀⟩
  obtain ⟨x₁, hx₁⟩ := PreValuationRing.exists_forall_dvd (exponentSum p X r).toAdd
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_toAdd_exponentSum_eq_single_of_forall_dvd hx₁ x₀
  exact ⟨x₁, e, hx₁, he⟩

end Normalisation

end freeProP

end TauCeti
