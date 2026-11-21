/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.Tate.Twist
public import TauCeti.Geometry.Hodge.TensorProduct.Basic
public import TauCeti.Geometry.Hodge.WeilOperator

/-!
# Hodge structures as representations of the Deligne torus

A pure Hodge structure of weight `n` on a complex vector space `W` with conjugation `ω` gives an
action of the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` on `W`. In the homology convention of Deligne and
Milne, the point `(z₁, z₂)` of `S(ℂ) ≃ ℂˣ × ℂˣ` (`TauCeti.DeligneTorus.complexSplitting`) acts on
the Hodge component `H^{p,q}` by `z₁^{-p} z₂^{-q}`, that is through the character `(-p, -q)` of
`TauCeti.DeligneTorus.characterGroup`. On real points `z ∈ S(ℝ) = ℂˣ`, which sit in `S(ℂ)` as
`(z, conj z)`, the action is `z^{-p} conj(z)^{-q}` and commutes with `ω`: the action is defined
over `ℝ`. The cocharacter `μ(z) = (z, 1)` acts on `H^{p,q}` by `z^{-p}`, the weight
`w(r) = (r⁻¹, r⁻¹)` acts on all of `W` by `r^n`, and the real point `-i` acts by the Weil operator.

The Hodge components are recovered from the action of `μ` as its eigenspaces, so a Hodge structure
of weight `n` is determined by its action. The construction is compatible with Tate twists (the
`m`-th twist multiplies the action by the character `(m, m)`, the `m`-th power of the norm on real
points), duals (the dual structure carries the contragredient action) and tensor products (the
tensor product structure carries the tensor product action).

## Main definitions

* `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction`: the action `h_ℂ` of `S(ℂ)` on `W`.
* `TauCeti.Hodge.HodgeStructureOn.deligneAction`: the action `h` of `S(ℝ)` on `W`.

## Main results

* `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction_apply_of_mem`: `h_ℂ` acts on `H^{p,n-p}`
  through the character `(-p, p - n)`.
* `TauCeti.Hodge.HodgeStructureOn.conj_complexDeligneAction`: conjugating `h_ℂ(f)` by `ω` gives
  `h_ℂ` of the complex conjugate point, and
  `TauCeti.Hodge.HodgeStructureOn.conj_deligneAction`: the real action commutes with `ω`.
* `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction_mu_apply_of_mem`,
  `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction_weight`: `μ(z)` acts on `H^{p,n-p}` by
  `z^{-p}` and the weight `w(r)` acts by `r^n`.
* `TauCeti.Hodge.HodgeStructureOn.deligneAction_realPointsMulEquiv_symm_apply_of_mem`: the real
  point `z` acts on `H^{p,n-p}` by `z^{-p} conj(z)^{p-n}`.
* `TauCeti.Hodge.HodgeStructureOn.deligneAction_neg_I`: the real point `-i` acts by the Weil
  operator.
* `TauCeti.Hodge.HodgeStructureOn.mem_piece_iff_complexDeligneAction_mu` and
  `TauCeti.Hodge.HodgeStructureOn.eq_of_complexDeligneAction_mu`: the Hodge components are the
  eigenspaces of `μ`, so the action of `μ` determines the Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.tateTwist_complexDeligneAction`,
  `TauCeti.Hodge.HodgeStructureOn.tateTwist_deligneAction`,
  `TauCeti.Hodge.HodgeStructureOn.dual_complexDeligneAction`,
  `TauCeti.Hodge.HodgeStructureOn.tensorProduct_complexDeligneAction`: compatibility with Tate
  twists, duals and tensor products.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.1.
-/

public section

open TauCeti.DeligneTorus WithConv
open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-! ### The action of `S(ℂ)` -/

/-- **The action `h_ℂ` of the Deligne torus over `ℂ`** attached to a pure Hodge structure of
weight `n`: the point `(z₁, z₂)` of `S(ℂ) ≃ ℂˣ × ℂˣ` acts on `H^{p,q}` by `z₁^{-p} z₂^{-q}`, that
is through the character `(-p, -q) = (-p, p - n)`. -/
noncomputable def complexDeligneAction (hs : HodgeStructureOn W ω n) :
    WithConv (DeligneTorus.S →ₐ[ℝ] ℂ) →* Module.End ℂ W where
  toFun f := hs.pieceSMul fun p ↦ characterGroup ℂ (.ofAdd (-p, p - n)) f
  map_one' := by simp only [map_one, Units.val_one]; exact hs.pieceSMul_one
  map_mul' f g := by
    simp only [map_mul, Units.val_mul]
    exact hs.pieceSMul_mul _ _

/-- `h_ℂ(f)` is `pieceSMul` of the characters `(-p, p - n)` evaluated at `f`. -/
theorem complexDeligneAction_apply (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) :
    hs.complexDeligneAction f =
      hs.pieceSMul fun p ↦ characterGroup ℂ (.ofAdd (-p, p - n)) f :=
  (rfl)

/-- `h_ℂ(f)` acts on the Hodge component `H^{p,n-p}` through the character `(-p, p - n)`. -/
theorem complexDeligneAction_apply_of_mem (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) {p : ℤ} {x : W} (hx : x ∈ hs.piece p) :
    hs.complexDeligneAction f x = (characterGroup ℂ (.ofAdd (-p, p - n)) f : ℂ) • x := by
  rw [complexDeligneAction_apply, hs.pieceSMul_apply_of_mem _ hx]

/-- **The Hodge cocharacter** `μ(z) = (z, 1)` acts on the Hodge component `H^{p,n-p}` by
`z^{-p}`. -/
theorem complexDeligneAction_mu_apply_of_mem (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W}
    (hx : x ∈ hs.piece p) (z : ℂˣ) :
    hs.complexDeligneAction (mu ℂ z) x = ((z ^ (-p) : ℂˣ) : ℂ) • x := by
  rw [hs.complexDeligneAction_apply_of_mem _ hx, characterGroup_mu]

/-- **The weight** `w(r) = (r⁻¹, r⁻¹)` acts on a pure Hodge structure of weight `n` by the scalar
`r^n`. -/
@[simp]
theorem complexDeligneAction_weight (hs : HodgeStructureOn W ω n) (r : ℂˣ) (x : W) :
    hs.complexDeligneAction (weight ℂ r) x = ((r ^ n : ℂˣ) : ℂ) • x := by
  refine hs.piece_induction_on (motive := fun x ↦ hs.complexDeligneAction (weight ℂ r) x =
    ((r ^ n : ℂˣ) : ℂ) • x) x (fun p y hy ↦ ?_) fun y z hy hz ↦ ?_
  · have hexp : -(-p + (p - n)) = n := by ring
    rw [hs.complexDeligneAction_apply_of_mem _ hy, characterGroup_weight, hexp]
  · rw [map_add, hy, hz, smul_add]

/-- **`h_ℂ` is defined over `ℝ`**: conjugating `h_ℂ(f)` by the conjugation `ω` gives `h_ℂ` of the
complex conjugate of the point `f`. -/
theorem conj_complexDeligneAction (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) (x : W) :
    ω.toEquiv (hs.complexDeligneAction f (ω.toEquiv x)) =
      hs.complexDeligneAction (AlgHom.mapValue Complex.conjAe.toAlgHom f) x := by
  refine hs.piece_induction_on (motive := fun x ↦
    ω.toEquiv (hs.complexDeligneAction f (ω.toEquiv x)) =
      hs.complexDeligneAction (AlgHom.mapValue Complex.conjAe.toAlgHom f) x) x
    (fun p y hy ↦ ?_) fun y z hy hz ↦ ?_
  · have h₁ : -(n - p) = p - n := by ring
    have h₂ : n - p - n = -p := by ring
    rw [hs.complexDeligneAction_apply_of_mem _ (hs.conj_mem_piece hy),
      LinearEquiv.map_smulₛₗ, ω.apply_apply, hs.complexDeligneAction_apply_of_mem _ hy,
      characterGroup_conj, h₁, h₂, Units.coe_star, Complex.star_def]
  · rw [map_add, map_add, map_add, hy, hz, map_add]

/-! ### The action of `S(ℝ)` -/

/-- **The action `h` of the real points of the Deligne torus** attached to a pure Hodge structure:
the restriction of `h_ℂ` along `S(ℝ) → S(ℂ)`. The real point `z ∈ S(ℝ) = ℂˣ` acts on `H^{p,q}` by
`z^{-p} conj(z)^{-q}`. -/
noncomputable def deligneAction (hs : HodgeStructureOn W ω n) :
    WithConv (DeligneTorus.S →ₐ[ℝ] ℝ) →* Module.End ℂ W :=
  hs.complexDeligneAction.comp (AlgHom.mapValue (Algebra.ofId ℝ ℂ))

/-- `h` is `h_ℂ` on the image of a real point in `S(ℂ)`. -/
theorem deligneAction_apply (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℝ)) :
    hs.deligneAction f = hs.complexDeligneAction (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) :=
  (rfl)

/-- The real point `z ∈ S(ℝ) = ℂˣ` acts on the Hodge component `H^{p,n-p}` by
`z^{-p} conj(z)^{p-n}`. -/
theorem deligneAction_realPointsMulEquiv_symm_apply_of_mem (hs : HodgeStructureOn W ω n)
    (z : ℂˣ) {p : ℤ} {x : W} (hx : x ∈ hs.piece p) :
    hs.deligneAction (realPointsMulEquiv.symm z) x =
      ((z ^ (-p) * star z ^ (p - n) : ℂˣ) : ℂ) • x := by
  rw [deligneAction_apply, hs.complexDeligneAction_apply_of_mem _ hx, characterGroup_apply,
    complexSplitting_real, MulEquiv.apply_symm_apply]

/-- **The real action commutes with the conjugation**: `h(f)` is the complexification of a real
linear map. -/
@[simp]
theorem conj_deligneAction (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℝ)) (x : W) :
    ω.toEquiv (hs.deligneAction f x) = hs.deligneAction f (ω.toEquiv x) := by
  have hreal : AlgHom.mapValue Complex.conjAe.toAlgHom (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      AlgHom.mapValue (Algebra.ofId ℝ ℂ) f := by
    rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.comp_assoc,
      Subsingleton.elim (Complex.conjAe.toAlgHom.comp (Algebra.ofId ℝ ℂ)) (Algebra.ofId ℝ ℂ)]
  rw [deligneAction_apply]
  conv_rhs => rw [← hreal, ← hs.conj_complexDeligneAction, ω.apply_apply]

/-- **The weight on real points**: `w(r)` for `r ∈ ℝˣ` acts by `r^n`. -/
@[simp]
theorem deligneAction_weight (hs : HodgeStructureOn W ω n) (r : ℝˣ) (x : W) :
    hs.deligneAction (weight ℝ r) x = ((r ^ n : ℝˣ) : ℂ) • x := by
  rw [deligneAction_apply, mapValue_weight, hs.complexDeligneAction_weight]
  simp

/-- **The Weil operator is `h(-i)`**: the real point `-i` acts on `H^{p,n-p}` by
`(-i)^{-p} i^{p-n} = i^{2p-n}`. -/
theorem deligneAction_neg_I (hs : HodgeStructureOn W ω n) :
    hs.deligneAction (realPointsMulEquiv.symm
      (Units.mk0 (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero))) = hs.weilOperator := by
  refine hs.weilOperator_unique _ fun p x hx ↦ ?_
  rw [hs.deligneAction_realPointsMulEquiv_symm_apply_of_mem _ hx]
  congr 1
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_star, Units.val_mk0,
    Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  rw [← Complex.inv_I, inv_zpow', neg_neg, ← zpow_add₀ Complex.I_ne_zero]
  congr 1
  ring

/-! ### The Hodge components are the eigenspaces of `μ` -/

/-- **The Hodge components are the eigenspaces of `μ`**: a vector lies in `H^{p,n-p}` exactly when
every `μ(z)` acts on it by `z^{-p}`. -/
theorem mem_piece_iff_complexDeligneAction_mu (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W} :
    x ∈ hs.piece p ↔ ∀ z : ℂˣ, hs.complexDeligneAction (mu ℂ z) x = ((z ^ (-p) : ℂˣ) : ℂ) • x := by
  refine ⟨fun hx z ↦ hs.complexDeligneAction_mu_apply_of_mem hx z, fun h ↦ ?_⟩
  have hproj (q : ℤ) (hq : q ≠ p) : hs.proj q x = 0 := by
    have hq' := congrArg (hs.proj q) (h (Units.mk0 2 two_ne_zero))
    rw [complexDeligneAction_apply, proj_pieceSMul, map_smul, characterGroup_mu] at hq'
    have hne : ((Units.mk0 (2 : ℂ) two_ne_zero ^ (-q) : ℂˣ) : ℂ) ≠
        ((Units.mk0 (2 : ℂ) two_ne_zero ^ (-p) : ℂˣ) : ℂ) := fun heq ↦ by
      have hnorm := congrArg (fun w : ℂ ↦ ‖w‖) heq
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Complex.norm_two] at hnorm
      exact hq (neg_injective (zpow_right_injective₀ zero_lt_two (by norm_num) hnorm))
    have hzero := sub_eq_zero.2 hq'
    rw [← sub_smul, smul_eq_zero] at hzero
    exact hzero.resolve_left (sub_ne_zero.2 hne)
  refine hs.mem_of_proj_mem fun q ↦ ?_
  by_cases hq : q = p
  · subst hq
    exact hs.proj_mem q x
  · rw [hproj q hq]
    exact zero_mem _

/-- **A Hodge structure is determined by its action**: two pure Hodge structures of the same
weight on the same space with conjugation, on which every `μ(z)` acts in the same way, are
equal. -/
theorem eq_of_complexDeligneAction_mu {hs hs' : HodgeStructureOn W ω n}
    (h : ∀ z : ℂˣ, hs.complexDeligneAction (mu ℂ z) = hs'.complexDeligneAction (mu ℂ z)) :
    hs = hs' :=
  piece_injective <| funext fun p ↦ Submodule.ext fun x ↦ by
    simp only [mem_piece_iff_complexDeligneAction_mu, h]

/-! ### Tate twists, duals and tensor products -/

/-- **Tate twists**: the action of the `m`-th Tate twist is the action of the original structure
multiplied by the character `(m, m)`. -/
theorem tateTwist_complexDeligneAction (hs : HodgeStructureOn W ω n) (m : ℤ)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) :
    (hs.tateTwist m).complexDeligneAction f =
      (characterGroup ℂ (.ofAdd (m, m)) f : ℂ) • hs.complexDeligneAction f := by
  refine (hs.tateTwist m).addHom_ext_of_piece fun p x hx ↦ ?_
  have hx' : x ∈ hs.piece (p + m) := by rwa [tateTwist_piece] at hx
  have hpair : (-p, p - (n - 2 * m)) = (m, m) + (-(p + m), p + m - n) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [(hs.tateTwist m).complexDeligneAction_apply_of_mem _ hx, LinearMap.smul_apply,
    hs.complexDeligneAction_apply_of_mem _ hx', hpair, characterGroup_add_apply, Units.val_mul,
    mul_smul]

/-- **Tate twists on real points**: the real point `z` acts on the `m`-th Tate twist as on the
original structure, multiplied by `|z|^{2m}`, the `m`-th power of the norm. -/
theorem tateTwist_deligneAction (hs : HodgeStructureOn W ω n) (m : ℤ) (z : ℂˣ) :
    (hs.tateTwist m).deligneAction (realPointsMulEquiv.symm z) =
      ((Complex.normSq z : ℂ) ^ m) • hs.deligneAction (realPointsMulEquiv.symm z) := by
  rw [deligneAction_apply, deligneAction_apply, tateTwist_complexDeligneAction,
    characterGroup_apply, complexSplitting_real, MulEquiv.apply_symm_apply]
  congr 1
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_star, ← mul_zpow,
    Complex.star_def, Complex.mul_conj]

/-- **Duals**: the dual Hodge structure carries the contragredient action,
`h_ℂ(f) φ = φ ∘ h_ℂ(f⁻¹)`. -/
theorem dual_complexDeligneAction (hs : HodgeStructureOn W ω n)
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) :
    hs.dual.complexDeligneAction f = (hs.complexDeligneAction f⁻¹).dualMap := by
  refine hs.dual.addHom_ext_of_piece fun p φ hφ ↦ hs.addHom_ext_of_piece fun a u hu ↦ ?_
  rw [hs.dual.complexDeligneAction_apply_of_mem _ hφ, LinearMap.dualMap_apply,
    hs.complexDeligneAction_apply_of_mem _ hu, map_smul, LinearMap.smul_apply]
  by_cases ha : a = -p
  · subst ha
    congr 1
    rw [map_inv (characterGroup ℂ (.ofAdd (- -p, -p - n))) f]
    have hpair : (-p, p - -n) = -(- -p, -p - n) := by
      ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
    rw [hpair, characterGroup_neg_apply]
  · rw [hs.apply_eq_zero_of_mem_piece_of_ne hu hφ ha, smul_zero, smul_zero]

section TensorProduct

variable {W₁ : Type u} {W₂ : Type v} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
  [Module ℂ W₂] {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

/-- **Tensor products**: the tensor product Hodge structure carries the tensor product action. -/
theorem tensorProduct_complexDeligneAction (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (f : WithConv (DeligneTorus.S →ₐ[ℝ] ℂ)) :
    (hs₁.tensorProduct hs₂).complexDeligneAction f =
      TensorProduct.map (hs₁.complexDeligneAction f) (hs₂.complexDeligneAction f) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  refine hs₁.piece_induction_on (motive := fun x ↦ ∀ y,
    (hs₁.tensorProduct hs₂).complexDeligneAction f (x ⊗ₜ y) =
      TensorProduct.map (hs₁.complexDeligneAction f) (hs₂.complexDeligneAction f) (x ⊗ₜ y)) x
    (fun p x hx y ↦ ?_) (fun x x' hx hx' y ↦ ?_) y
  · refine hs₂.piece_induction_on (motive := fun y ↦
      (hs₁.tensorProduct hs₂).complexDeligneAction f (x ⊗ₜ y) =
        TensorProduct.map (hs₁.complexDeligneAction f) (hs₂.complexDeligneAction f) (x ⊗ₜ y)) y
      (fun q y hy ↦ ?_) fun y y' hy hy' ↦ ?_
    · have hpair : (-(p + q), p + q - (n₁ + n₂)) = (-p, p - n₁) + (-q, q - n₂) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
      rw [(hs₁.tensorProduct hs₂).complexDeligneAction_apply_of_mem _
          (hs₁.tmul_mem_tensorProduct hs₂ hx hy), TensorProduct.map_tmul,
        hs₁.complexDeligneAction_apply_of_mem _ hx, hs₂.complexDeligneAction_apply_of_mem _ hy,
        hpair, characterGroup_add_apply, Units.val_mul, TensorProduct.smul_tmul_smul]
    · rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  · rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']

end TensorProduct

end HodgeStructureOn

end TauCeti.Hodge
