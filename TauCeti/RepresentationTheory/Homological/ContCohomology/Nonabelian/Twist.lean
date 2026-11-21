/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Twisting the coefficients of continuous nonabelian cohomology

A continuous cocycle `c` changes the action of `G` on `A` to `g ⋆ a = c(g) (g • a) c(g)⁻¹`,
without changing the group or its topology. Right multiplication by `c` identifies cocycles for
the twisted action with cocycles for the original action. This identification respects gauge
equivalence and sends the trivial cocycle to `c`. Thus `NonabelianH1.twistEquiv` is an equivalence
of sets taking the twisted neutral class to `[c]`, not necessarily to the original neutral class.
It allows arguments about a fibre over a given class to be reduced to neutral-class arguments.

## References

* J.-P. Serre, *Galois Cohomology*, I.5.3, Proposition 35.
* M. Kim, *The motivic fundamental group of the projective line minus three points and the
  theorem of Siegel*, §1, proof of Proposition 1.
-/

public section

namespace TauCeti.NonabelianH1

variable {G A : Type*} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

-- The compiler needs the representation exposed to reuse the group operations of `A`.
/-- The coefficient group `A` with the action twisted by `c`. The multiplication and topology
are those of `A`, but the action is `g ⋆ a = c(g) (g • a) c(g)⁻¹`. -/
@[expose] def Twist (_c : Cocycle G A) : Type _ := A

namespace Twist

variable (c : Cocycle G A)

instance : Group (Twist c) := inferInstanceAs (Group A)

instance : TopologicalSpace (Twist c) := inferInstanceAs (TopologicalSpace A)

/-- The identity on the underlying group, forgetting the twisted action. -/
def toOriginal : Twist c ≃* A := MulEquiv.refl A

/-- Forgetting the twisted action is continuous for the inherited topology. -/
@[continuity, fun_prop]
theorem continuous_toOriginal : Continuous (toOriginal c) := continuous_id

/-- The inverse identification with the original group is also continuous. -/
@[continuity, fun_prop]
theorem continuous_toOriginal_symm : Continuous (toOriginal c).symm := continuous_id

/-- The `G`-action followed by conjugation by the cocycle value. -/
instance : MulDistribMulAction G (Twist c) :=
  .compHom (Twist c) ({
    toFun g := ((toOriginal c).trans (MulDistribMulAction.toMulAut G A g)).trans
      ((MulAut.conj (c g)).trans (toOriginal c).symm)
    map_one' := MulEquiv.ext fun x ↦ (toOriginal c).injective (by simp)
    map_mul' g h := MulEquiv.ext fun x ↦ (toOriginal c).injective (by
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply,
        MulAut.mul_apply, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply,
        c.apply_mul, mul_smul, smul_mul', smul_inv', mul_inv_rev]
      group) } : G →* MulAut (Twist c))

/-- In the original group, the new action is the old action followed by conjugation by `c g`. -/
@[simp]
theorem toOriginal_smul (g : G) (x : Twist c) :
    toOriginal c (g • x) = c g * (g • toOriginal c x) * (c g)⁻¹ :=
  (toOriginal c).apply_symm_apply _

/-- The underlying identification for the trivial cocycle is equivariant. -/
theorem toOriginal_one_smul (g : G) (x : Twist (1 : Cocycle G A)) :
    toOriginal (1 : Cocycle G A) (g • x) = g • toOriginal (1 : Cocycle G A) x := by
  simp

/-- An element is fixed under the twisted action exactly when it satisfies these intertwining
identities in the original group. -/
theorem mem_fixedPoints_iff (x : Twist c) :
    x ∈ FixedPoints.subgroup G (Twist c) ↔ ∀ g : G,
      c g * (g • toOriginal c x) = toOriginal c x * c g := by
  simp only [FixedPoints.mem_subgroup, ← (toOriginal c).injective.eq_iff (a := _ • _),
    toOriginal_smul, mul_inv_eq_iff_eq_mul]

instance [ContinuousMul A] : ContinuousMul (Twist c) := inferInstanceAs (ContinuousMul A)

instance [ContinuousInv A] : ContinuousInv (Twist c) := inferInstanceAs (ContinuousInv A)

instance [IsTopologicalGroup A] : IsTopologicalGroup (Twist c) where

instance [ContinuousMul A] [ContinuousInv A] [ContinuousSMul G A] : ContinuousSMul G (Twist c) where
  continuous_smul := by
    have h : (fun p : G × Twist c ↦ p.1 • p.2) = fun p ↦ (toOriginal c).symm
        (c p.1 * (p.1 • toOriginal c p.2) * (c p.1)⁻¹) := by
      funext p
      apply (toOriginal c).injective
      simp
    rw [h]
    fun_prop

end Twist

open Twist (toOriginal)

/-- Right multiplication by `c` converts the twisted cocycle identity to the original one. -/
theorem translated_apply_mul_iff (c : Cocycle G A) (d : G → Twist c) (g h : G) :
    toOriginal c (d (g * h)) * c (g * h) =
      (toOriginal c (d g) * c g) * (g • (toOriginal c (d h) * c h)) ↔
    d (g * h) = d g * g • d h := by
  rw [← (toOriginal c).injective.eq_iff (a := d (g * h)), map_mul (toOriginal c),
    Twist.toOriginal_smul]
  have hmul : (toOriginal c (d g) * (c g * (g • toOriginal c (d h)) * (c g)⁻¹)) * c (g * h) =
      (toOriginal c (d g) * c g) * (g • (toOriginal c (d h) * c h)) := by
    simp [c.apply_mul, smul_mul', mul_assoc]
  rw [← hmul, mul_left_inj]

section Translation

variable [ContinuousMul A] [ContinuousInv A] (c : Cocycle G A)

/-- The cocycles for the twisted action correspond to the original cocycles by right
multiplication by `c`. The inverse is right multiplication by the pointwise inverse of `c`. -/
def cocycleTwistEquiv : Cocycle G (Twist c) ≃ Cocycle G A where
  toFun d :=
    { toFun := fun g ↦ toOriginal c (d g) * c g
      continuous_toFun := by fun_prop
      map_mul' := fun g h ↦ (translated_apply_mul_iff c d g h).mpr (d.apply_mul g h) }
  invFun d :=
    { toFun := fun g ↦ (toOriginal c).symm (d g * (c g)⁻¹)
      continuous_toFun := by fun_prop
      map_mul' := fun g h ↦
        (translated_apply_mul_iff c (fun k ↦ (toOriginal c).symm (d k * (c k)⁻¹)) g h).mp
          (by simpa using d.apply_mul g h) }
  left_inv d := Cocycle.ext fun g ↦ by
    apply (toOriginal c).injective
    simp
  right_inv d := Cocycle.ext fun g ↦ by simp

/-- Evaluation of translation from the twist to the original coefficients. -/
@[simp]
theorem cocycleTwistEquiv_apply (d : Cocycle G (Twist c)) (g : G) :
    cocycleTwistEquiv c d g = toOriginal c (d g) * c g := (rfl)

/-- Evaluation of translation back into the twisted coefficients. -/
@[simp]
theorem toOriginal_cocycleTwistEquiv_symm_apply (d : Cocycle G A) (g : G) :
    toOriginal c ((cocycleTwistEquiv c).symm d g) = d g * (c g)⁻¹ :=
  (toOriginal c).apply_symm_apply _

/-- Translation carries the trivial cocycle to the twisting cocycle. -/
@[simp]
theorem cocycleTwistEquiv_one : cocycleTwistEquiv c 1 = c := by
  ext g
  simp

omit [ContinuousMul A] [ContinuousInv A] in
private theorem toOriginal_gauge_mul (a x : Twist c) (g : G) :
    toOriginal c (a⁻¹ * x * g • a) * c g =
      (toOriginal c a)⁻¹ * (toOriginal c x * c g) * (g • toOriginal c a) := by
  simp [mul_assoc]

/-- Translation preserves and reflects gauge equivalence; it uses the same coefficient element
read in the original group. This does not require joint continuity of the actions. -/
theorem cocycleTwistEquiv_equiv_iff {d e : Cocycle G (Twist c)} :
    cocycleTwistEquiv c d ≈ cocycleTwistEquiv c e ↔ d ≈ e := by
  have gauge (a : Twist c) (g : G) :
      cocycleTwistEquiv c e g = (toOriginal c a)⁻¹ * cocycleTwistEquiv c d g *
        (g • toOriginal c a) ↔ e g = a⁻¹ * d g * g • a := by
    simp only [cocycleTwistEquiv_apply, ← toOriginal_gauge_mul, mul_left_inj,
      (toOriginal c).injective.eq_iff]
  rw [Cocycle.equiv_iff, Cocycle.equiv_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(toOriginal c).symm a, fun g ↦ (gauge _ g).mp ?_⟩
    simpa only [MulEquiv.apply_symm_apply] using ha g
  · rintro ⟨a, ha⟩
    exact ⟨toOriginal c a, fun g ↦ (gauge a g).mpr (ha g)⟩

/-- Translation intertwines the gauge operations on cocycles. -/
@[simp]
theorem cocycleTwistEquiv_twist [ContinuousSMul G A] (d : Cocycle G (Twist c)) (a : Twist c) :
    cocycleTwistEquiv c (d.twist a) = (cocycleTwistEquiv c d).twist (toOriginal c a) := by
  ext g
  simp only [Cocycle.twist_apply, cocycleTwistEquiv_apply, toOriginal_gauge_mul]

/-- Twisting gives a bijection between the twisted and original continuous `H¹` sets.
This sends the twisted neutral class to the class of `c`. -/
def twistEquiv : NonabelianH1 G (Twist c) ≃ NonabelianH1 G A where
  toFun := lift (fun d ↦ mk (cocycleTwistEquiv c d)) fun _ _ h ↦
    mk_eq_mk_iff.mpr (Cocycle.equiv_iff.mp ((cocycleTwistEquiv_equiv_iff c).mpr h))
  invFun := lift (fun d ↦ mk ((cocycleTwistEquiv c).symm d)) fun d e h ↦ by
    refine mk_eq_mk_iff.mpr (Cocycle.equiv_iff.mp ((cocycleTwistEquiv_equiv_iff c).mp ?_))
    simpa only [Equiv.apply_symm_apply] using h
  left_inv x := by
    induction x using induction_on
    simp only [lift_mk, Equiv.symm_apply_apply]
  right_inv x := by
    induction x using induction_on
    simp only [lift_mk, Equiv.apply_symm_apply]

/-- Translation of the class of a twisted cocycle is the class of its translate. -/
@[simp]
theorem twistEquiv_mk (d : Cocycle G (Twist c)) :
    twistEquiv c (mk d) = mk (cocycleTwistEquiv c d) :=
  lift_mk _ _ _

/-- Inverse translation of a class is computed by inverse translation of a representative. -/
@[simp]
theorem twistEquiv_symm_mk (d : Cocycle G A) :
    (twistEquiv c).symm (mk d) = mk ((cocycleTwistEquiv c).symm d) :=
  lift_mk _ _ _

/-- The twisted neutral class translates to the class of `c`. -/
@[simp]
theorem twistEquiv_one : twistEquiv c 1 = mk c := by
  rw [one_def, twistEquiv_mk, cocycleTwistEquiv_one]

end Translation

end TauCeti.NonabelianH1
