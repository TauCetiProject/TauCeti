/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.LinearAlgebra.LatticePairing.Basic

import TauCeti.Algebra.AddCircle
import TauCeti.Algebra.Module.CharacterModule
import TauCeti.LinearAlgebra.Dual.Divisibility

/-!
# The discriminant pairing of a nondegenerate lattice pairing

Let `u : Y × X → ℤ` be a nondegenerate lattice pairing: its adjoint `u♯ : Y → Hom(X, ℤ)` is
injective with finite cokernel `componentGroup u`. No symmetry is assumed and `X`, `Y` may differ.
This file constructs the *discriminant pairing*

```text
componentGroup u × componentGroup u.flip → ℚ / ℤ,   ([a], [b]) ↦ b(y) / m,
```

for any `m ≠ 0` and `y ∈ Y` with `u♯ y = m a`. Such a pair exists because the cokernel is finite,
and `b(y) / m` does not depend on it because `u♯` is injective. Changing `a` by `u♯ y'` changes
the value by the integer `b(y')`; changing `b` by `u x` (the transpose adjoint) changes it by
`u(y, x) / m = a(x)`. Over `ℚ` this is the inverse of the pairing `u`, read modulo `ℤ`.

When `X` and `Y` are reflexive (for instance free of finite rank), the transpose `u.flip` is again
nondegenerate, and the discriminant pairing is perfect: both of its adjoints are bijective onto
the `ℚ / ℤ`-duals `Hom(componentGroup u.flip, ℚ / ℤ)` and `Hom(componentGroup u, ℚ / ℤ)`.

For the rank-one pairing `rankOne n`, `n ≠ 0`, the pairing of the rank-one classes of `r` and `s`
is `r s / n`, with the positive sign: at `n = 5` the classes of `1, 1` pair to `1/5` and those of
`1, 2` to `2/5`. This is the normalisation of Grothendieck's pairing on the component groups of a
Tate curve with parameter of valuation `n` (Werner, §4).

## Main declarations

* `TauCeti.LatticePairing.discriminantPairing`: the pairing of the two cokernels into `ℚ / ℤ`.
* `TauCeti.LatticePairing.discriminantPairing_mk`: its value `b(y) / m` on representatives.
* `TauCeti.LatticePairing.instIsNondegenerateFlip`: the transpose of a nondegenerate pairing of
  reflexive modules is nondegenerate.
* `TauCeti.LatticePairing.bijective_discriminantPairing` and
  `TauCeti.LatticePairing.bijective_discriminantPairing_flip`: perfectness.
* `TauCeti.LatticePairing.natCard_componentGroup_flip`: the two cokernels have the same order.
* `TauCeti.LatticePairing.discriminantPairing_rankOne`: the rank-one value `r s / n`.

## References

* A. Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX, §11.4 and
  Theorem 11.5.
* A. Werner, *On Grothendieck's pairing of component groups in the semistable reduction case*,
  J. reine angew. Math. 486 (1997), §4.
-/

public section

namespace TauCeti

namespace LatticePairing

variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable (u : LatticePairing X Y) [u.IsNondegenerate]

/-- The vector `u♯⁻¹(n a)` of `Y`, for `n = |componentGroup u|`, as a linear function of the
functional `a` on `X`. -/
private noncomputable def adjointPreimage : (X →ₗ[ℤ] ℤ) →ₗ[ℤ] Y :=
  (LinearEquiv.ofInjective u IsNondegenerate.injective).symm.toLinearMap ∘ₗ
    (Nat.card u.componentGroup • LinearMap.id).codRestrict (LinearMap.range u)
      u.natCard_smul_mem_range

private theorem apply_adjointPreimage (a : X →ₗ[ℤ] ℤ) :
    u (adjointPreimage u a) = Nat.card u.componentGroup • a := by
  simp [adjointPreimage, ← LinearEquiv.ofInjective_apply (h := IsNondegenerate.injective)]

/-- On the adjoint of `y`, the preimage is `n y`. -/
private theorem adjointPreimage_apply_self (y : Y) :
    adjointPreimage u (u y) = (Nat.card u.componentGroup : ℤ) • y :=
  IsNondegenerate.injective (u := u) (by rw [apply_adjointPreimage, map_zsmul, natCast_zsmul])

private theorem natCard_componentGroup_ne_zero : Nat.card u.componentGroup ≠ 0 :=
  Nat.card_pos.ne'

/-- The rational inverse form `Hom(X, ℤ) × Hom(Y, ℤ) → ℚ`, `(a, b) ↦ b(u♯⁻¹(n a)) / n`. -/
private noncomputable def inverseForm : (X →ₗ[ℤ] ℤ) →ₗ[ℤ] (Y →ₗ[ℤ] ℤ) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun a b ↦ (b (adjointPreimage u a) : ℚ) / Nat.card u.componentGroup)
    (fun a a' b ↦ by simp [add_div]) (fun k a b ↦ by simp [mul_div_assoc])
    (fun a b b' ↦ by simp [add_div]) (fun k a b ↦ by simp [mul_div_assoc])

/-- The inverse form is `b(y) / m` for any `m ≠ 0` and `y` with `u♯ y = m a`. -/
private theorem inverseForm_apply_of_eq {m : ℤ} (hm : m ≠ 0) {y : Y} {a : X →ₗ[ℤ] ℤ}
    (h : u y = m • a) (b : Y →ₗ[ℤ] ℤ) : inverseForm u a b = (b y : ℚ) / m := by
  set n := Nat.card u.componentGroup
  have hy : m • adjointPreimage u a = (n : ℤ) • y := IsNondegenerate.injective (u := u) (by
    rw [map_zsmul, map_zsmul, apply_adjointPreimage, h]
    module)
  have hb : m * b (adjointPreimage u a) = n * b y := by
    simpa only [map_zsmul, smul_eq_mul] using congrArg b hy
  rw [inverseForm, LinearMap.mk₂_apply,
    div_eq_div_iff (Nat.cast_ne_zero.mpr (natCard_componentGroup_ne_zero u))
      (Int.cast_ne_zero.mpr hm)]
  exact_mod_cast (by linarith : b (adjointPreimage u a) * m = b y * (n : ℤ))

/-- The inverse form on the adjoint of `y` is evaluation at `y`. -/
private theorem inverseForm_apply_self (y : Y) (b : Y →ₗ[ℤ] ℤ) :
    inverseForm u (u y) b = b y := by
  rw [inverseForm_apply_of_eq u one_ne_zero (one_smul ℤ (u y)).symm, Int.cast_one, div_one]

/-- The inverse form on the transpose adjoint of `x` is evaluation at `x`. -/
private theorem inverseForm_apply_flip (a : X →ₗ[ℤ] ℤ) (x : X) :
    inverseForm u a (u.flip x) = a x := by
  have hn : (Nat.card u.componentGroup : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (natCard_componentGroup_ne_zero u)
  have h : u (adjointPreimage u a) = (Nat.card u.componentGroup : ℤ) • a := by
    rw [apply_adjointPreimage, natCast_zsmul]
  rw [inverseForm_apply_of_eq u hn h]
  simp [h, natCard_componentGroup_ne_zero u]

/-- The inverse form reduced modulo `ℤ`. -/
private noncomputable def inverseFormModOne :
    (X →ₗ[ℤ] ℤ) →ₗ[ℤ] (Y →ₗ[ℤ] ℤ) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (inverseForm u).compr₂
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) :
      ℚ →+ AddCircle (1 : ℚ)).toIntLinearMap

private theorem inverseFormModOne_apply (a : X →ₗ[ℤ] ℤ) (b : Y →ₗ[ℤ] ℤ) :
    inverseFormModOne u a b = (inverseForm u a b : AddCircle (1 : ℚ)) := by
  simp [inverseFormModOne]

private theorem range_le_ker_inverseFormModOne :
    LinearMap.range u ≤ LinearMap.ker (inverseFormModOne u) := by
  rintro _ ⟨y, rfl⟩
  ext b
  rw [LinearMap.zero_apply, inverseFormModOne_apply, inverseForm_apply_self,
    AddCircle.coe_intCast_eq_zero]

private theorem range_flip_le_ker_flip_inverseFormModOne :
    LinearMap.range u.flip ≤ LinearMap.ker (inverseFormModOne u).flip := by
  rintro _ ⟨x, rfl⟩
  ext a
  rw [LinearMap.zero_apply, LinearMap.flip_apply, inverseFormModOne_apply,
    inverseForm_apply_flip, AddCircle.coe_intCast_eq_zero]

/-- The discriminant pairing `componentGroup u × componentGroup u.flip → ℚ / ℤ` of a
nondegenerate lattice pairing: on classes `[a]` and `[b]` it is `b(y) / m` modulo `ℤ` for any
`m ≠ 0` and `y` with `u♯ y = m a` (`discriminantPairing_mk`). -/
noncomputable def discriminantPairing :
    u.componentGroup →+ (componentGroup u.flip →+ AddCircle (1 : ℚ)) :=
  LinearMap.toAddMonoidHom'.comp <| LinearMap.toAddMonoidHom <|
    LinearMap.liftQ₂ (LinearMap.range u) (LinearMap.range u.flip) (inverseFormModOne u)
      (range_le_ker_inverseFormModOne u) (range_flip_le_ker_flip_inverseFormModOne u)

private theorem discriminantPairing_mk_mk (a : X →ₗ[ℤ] ℤ) (b : Y →ₗ[ℤ] ℤ) :
    u.discriminantPairing (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      (inverseForm u a b : AddCircle (1 : ℚ)) := by
  simp [discriminantPairing, inverseFormModOne_apply]

/-- **Evaluation of the discriminant pairing.** If `u♯ y = m a` with `m ≠ 0`, the pairing of the
classes of `a` and `b` is `b(y) / m` modulo `ℤ`. -/
theorem discriminantPairing_mk {m : ℤ} (hm : m ≠ 0) {y : Y} {a : X →ₗ[ℤ] ℤ}
    (h : u y = m • a) (b : Y →ₗ[ℤ] ℤ) :
    u.discriminantPairing (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      ((b y / m : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantPairing_mk_mk, inverseForm_apply_of_eq u hm h]

/-! ### Perfectness -/

/-- The pairing of the classes of `a` and `b` vanishes exactly when `n` divides
`b(u♯⁻¹(n a))`, for `n = |componentGroup u|`. -/
private theorem discriminantPairing_mk_mk_eq_zero_iff (a : X →ₗ[ℤ] ℤ) (b : Y →ₗ[ℤ] ℤ) :
    u.discriminantPairing (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = 0 ↔
      (Nat.card u.componentGroup : ℤ) ∣ b (adjointPreimage u a) := by
  rw [discriminantPairing_mk_mk, inverseForm, LinearMap.mk₂_apply,
    AddCircle.coe_intCast_div_natCast_eq_zero_iff (natCard_componentGroup_ne_zero u)]

private theorem isLeftRegular_natCard_componentGroup :
    IsLeftRegular (Nat.card u.componentGroup : ℤ) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (Nat.cast_ne_zero.mpr (natCard_componentGroup_ne_zero u))

/-- A class of `componentGroup u` pairing to zero with every class of the transpose cokernel is
zero, when `Y` is reflexive. -/
theorem injective_discriminantPairing [Module.IsReflexive ℤ Y] :
    Function.Injective u.discriminantPairing := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  -- `n` divides `b(u♯⁻¹(n a))` for every `b`, so `u♯⁻¹(n a) = n y'` by reflexivity.
  obtain ⟨g, hg⟩ := LinearMap.exists_smul_eq_of_forall_dvd
    (f := Module.Dual.eval ℤ Y (adjointPreimage u a)) (isLeftRegular_natCard_componentGroup u)
    fun b ↦ (discriminantPairing_mk_mk_eq_zero_iff u a b).mp
      (DFunLike.congr_fun hc (Submodule.Quotient.mk b))
  set y' := (Module.evalEquiv ℤ Y).symm g
  have hy' : adjointPreimage u a = (Nat.card u.componentGroup : ℤ) • y' := by
    apply (Module.bijective_dual_eval ℤ Y).1
    ext b
    simp [y', ← hg]
  -- Then `n u♯ y' = n a`, so `a = u♯ y'`.
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨y', LinearMap.ext fun x ↦ isLeftRegular_natCard_componentGroup u ?_⟩
  have hx := LinearMap.congr_fun (apply_adjointPreimage u a) x
  simp only [hy', map_zsmul, LinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul] at hx
  exact hx

/-- A class of the transpose cokernel pairing to zero with every class of `componentGroup u` is
zero, when `X` is reflexive. -/
theorem injective_discriminantPairing_flip [Module.IsReflexive ℤ X] :
    Function.Injective u.discriminantPairing.flip := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  -- `n` divides `b(u♯⁻¹(n a))` for every `a`, so `a ↦ b(u♯⁻¹(n a)) / n` is evaluation at some
  -- `x` by reflexivity.
  obtain ⟨g, hg⟩ := LinearMap.exists_smul_eq_of_forall_dvd (f := b ∘ₗ adjointPreimage u)
    (isLeftRegular_natCard_componentGroup u) fun a ↦
      (discriminantPairing_mk_mk_eq_zero_iff u a b).mp
        (DFunLike.congr_fun hc (Submodule.Quotient.mk a))
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨(Module.evalEquiv ℤ X).symm g, LinearMap.ext fun y ↦ ?_⟩
  have hy := LinearMap.congr_fun hg (u y)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, adjointPreimage_apply_self, map_zsmul,
    smul_eq_mul] at hy
  rw [LinearMap.flip_apply, Module.apply_evalEquiv_symm_apply]
  exact isLeftRegular_natCard_componentGroup u hy

/-- The transpose of a nondegenerate lattice pairing is nondegenerate, when `X` is reflexive. -/
instance instIsNondegenerateFlip [Module.IsReflexive ℤ X] : IsNondegenerate u.flip where
  injective x x' h := by
    apply (Module.bijective_dual_eval ℤ X).1
    ext a
    refine isLeftRegular_natCard_componentGroup u ?_
    have hxy := LinearMap.congr_fun h (adjointPreimage u a)
    simp only [LinearMap.flip_apply, apply_adjointPreimage, LinearMap.smul_apply,
      nsmul_eq_mul] at hxy
    simpa only [Module.Dual.eval_apply] using hxy
  finite_componentGroup := Finite.of_injective _ u.injective_discriminantPairing_flip

/-- The cokernels of a nondegenerate pairing of reflexive modules and of its transpose have the
same order. -/
theorem natCard_componentGroup_flip [Module.IsReflexive ℤ X] [Module.IsReflexive ℤ Y] :
    Nat.card (componentGroup u.flip) = Nat.card u.componentGroup :=
  -- Here and below, `natCard_characterModule` counts the characters `A →+ AddCircle (1 : ℚ)`
  -- of a cokernel `A` through the definitional equality `CharacterModule A = A →+ AddCircle 1`.
  le_antisymm
    ((Nat.card_le_card_of_injective _ u.injective_discriminantPairing_flip).trans_eq
      (natCard_characterModule (componentGroup u)))
    ((Nat.card_le_card_of_injective _ u.injective_discriminantPairing).trans_eq
      (natCard_characterModule (componentGroup u.flip)))

/-- **Perfectness of the discriminant pairing.** For reflexive `X` and `Y` (for instance free of
finite rank), every character of the transpose cokernel is the pairing with a unique class of
`componentGroup u`. -/
theorem bijective_discriminantPairing [Module.IsReflexive ℤ X] [Module.IsReflexive ℤ Y] :
    Function.Bijective u.discriminantPairing :=
  u.injective_discriminantPairing.bijective_of_nat_card_le
    ((natCard_characterModule (componentGroup u.flip)).trans_le u.natCard_componentGroup_flip.le)

/-- **Perfectness of the discriminant pairing**, in the other variable: for reflexive `X` and
`Y`, every character of `componentGroup u` is the pairing with a unique class of the transpose
cokernel. -/
theorem bijective_discriminantPairing_flip [Module.IsReflexive ℤ X] [Module.IsReflexive ℤ Y] :
    Function.Bijective u.discriminantPairing.flip :=
  u.injective_discriminantPairing_flip.bijective_of_nat_card_le
    ((natCard_characterModule (componentGroup u)).trans_le u.natCard_componentGroup_flip.ge)

/-! ### The rank-one pairings -/

/-- For `n ≠ 0`, the discriminant pairing of `rankOne n` takes the rank-one classes of `r` and
`s` to `r s / n` modulo `ℤ`. -/
@[simp]
theorem discriminantPairing_rankOne (n : ℤ) [NeZero n] (r s : ℤ) :
    (rankOne n).discriminantPairing (rankOneClass n r) (rankOneDualClass n s) =
      ((r * s / n : ℚ) : AddCircle (1 : ℚ)) := by
  have h : rankOne n r = n • LinearMap.mul ℤ ℤ r := LinearMap.ext_ring (by simp)
  rw [rankOneClass_apply, rankOneDualClass_apply,
    discriminantPairing_mk (rankOne n) (NeZero.ne n) h]
  simp [mul_comm]

end LatticePairing

end TauCeti
