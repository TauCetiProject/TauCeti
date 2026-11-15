/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# Computing corestriction on the profinite integers

Reduction modulo a positive integer `n` defines an open subgroup of `ℤ̂` of index `n`.
Its cosets have the transversal `1, gen, …, gen ^ (n - 1)`. For a continuous one-cocycle
`c` the transversal corestriction of its restriction is

```text
cor (res c) γ = n • c γ + γ • (∑ i < n, c (gen ^ i)) - ∑ i < n, c (gen ^ i).
```

For trivial coefficients the correction vanishes already on cochains. For general actions
it is a coboundary, so the normalization holds on cohomology. The final sign-action example
exhibits a nonzero correction, testing the action factor in the transversal formula.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.5.7).
* J.-P. Serre, *Local Fields*, Chapter VII, §7, Proposition 6.
-/

public noncomputable section

namespace TauCeti.zHat

open ContCohomology

universe u v

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (n : ℕ+) (M : Type v) [AddCommGroup M] [DistribMulAction zHat.{u} M]

/-- Corestriction of a restricted cocycle for the cyclic transversal, including its explicit
coboundary correction. No triviality assumption on the coefficient action is made. -/
theorem cochainsCor1_modTransversal_res {c : zHat.{u} → M}
    (hc : groupCohomology.IsCocycle₁ c) (γ : zHat.{u}) :
    cochainsCor1 zHat M (modSubgroup n).toSubgroup (modTransversal n)
      (mk_modTransversal n) (fun x ↦ c x) γ =
        (n : ℕ) • c γ + γ • (∑ i ∈ Finset.range (n : ℕ), c (gen ^ i)) -
          ∑ i ∈ Finset.range (n : ℕ), c (gen ^ i) := by
  have h := congrFun (cochainsCor1_res zHat M (modSubgroup n).toSubgroup
    (modTransversal n) (mk_modTransversal n) hc) γ
  rw [modSubgroup_index, sum_modTransversal] at h
  simpa only [Pi.add_apply, Pi.smul_apply, d0_apply, sub_eq_add_neg, add_assoc] using h

/-- With trivial coefficients, cyclic-transversal corestriction after restriction is
multiplication by `n` already on cocycles, without a correction. -/
theorem cochainsCor1_modTransversal_res_of_trivial {c : zHat.{u} → M}
    (hc : groupCohomology.IsCocycle₁ c) (htriv : ∀ (g : zHat.{u}) (m : M), g • m = m)
    (γ : zHat.{u}) :
    cochainsCor1 zHat M (modSubgroup n).toSubgroup (modTransversal n)
      (mk_modTransversal n) (fun x ↦ c x) γ = (n : ℕ) • c γ := by
  rw [cochainsCor1_modTransversal_res n M hc, htriv]
  abel

/-- At the generator, cyclic-transversal corestriction of a restricted cocycle is the
geometric action sum on its value at the generator. For a nontrivial action this sum need
not equal `n • c gen`. -/
theorem cochainsCor1_modTransversal_res_gen {c : zHat.{u} → M}
    (hc : groupCohomology.IsCocycle₁ c) :
    cochainsCor1 zHat M (modSubgroup n).toSubgroup (modTransversal n)
      (mk_modTransversal n) (fun x ↦ c x) gen =
        ∑ i ∈ Finset.range (n : ℕ), gen ^ i • c gen := by
  classical
  have hcomm (i : ℕ) : gen • c (gen ^ i) - c (gen ^ i) = gen ^ i • c gen - c gen := by
    have h := hc gen (gen ^ i)
    rw [((Commute.refl (gen : zHat.{u})).pow_right i).eq, hc] at h
    exact sub_eq_sub_iff_add_eq_add.2 h.symm
  rw [cochainsCor1_modTransversal_res n M hc, Finset.smul_sum, add_sub_assoc,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ ↦ hcomm i), Finset.sum_sub_distrib]
  simp

/-- For trivial `ℤ/m` coefficients, the residue character with value `a` at the generator
is carried by corestriction after restriction to the character with value `n • a`. This
computes the transfer on actual continuous characters, including modulus one. -/
theorem cochainsCor1_modTransversal_character (m : ℕ+) [DistribMulAction zHat.{u} (ZMod m)]
    (htriv : ∀ (g : zHat.{u}) (a : ZMod m), g • a = a) (a : ZMod m) (γ : zHat.{u}) :
    cochainsCor1 zHat (ZMod m) (modSubgroup n).toSubgroup (modTransversal n)
      (mk_modTransversal n) (fun x ↦ toZMod m (Additive.ofMul (x : zHat.{u})) * a) γ =
        (n : ZMod m) * (toZMod m (Additive.ofMul γ) * a) := by
  have hc : groupCohomology.IsCocycle₁
      (fun g : zHat.{u} ↦ toZMod m (Additive.ofMul g) * a) := by
    intro g h
    simp only [htriv, ofMul_mul, map_add, add_mul]
    exact add_comm _ _
  simpa only [nsmul_eq_mul] using
    cochainsCor1_modTransversal_res_of_trivial n (ZMod m) hc htriv γ

end TauCeti.zHat

namespace TauCeti.zHat

open ContCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-! ## A nontrivial action: the sign module modulo four -/

/-- The sign action of `ℤ̂` on `ℤ/4`: the generator acts by negation. Install this named
instance locally when using `signCocycle`, to keep the action explicit. -/
@[instance_reducible] def signDistribMulAction : DistribMulAction zHat.{u} (ZMod 4) :=
  DistribMulAction.compHom (ZMod 4)
    (lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* (ZMod 4)ˣ).toMonoidHom

attribute [local instance] signDistribMulAction

/-- The sign action is continuous, because it factors through a finite discrete unit group. -/
instance signContinuousSMul : ContinuousSMul zHat.{u} (ZMod 4) :=
  MulAction.continuousSMul_compHom (lift (-1 : (ZMod 4)ˣ)).continuous

/-- The sign action is multiplication by the finite unit-valued sign character. -/
theorem sign_smul (g : zHat.{u}) (m : ZMod 4) :
    g • m = (lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) g • m := by
  simp only [MulAction.compHom_smul_def, ContinuousMonoidHom.coe_toMonoidHom,
    MonoidHom.coe_ofClass]

/-- The generator negates coefficients in the sign module modulo four. -/
@[simp]
theorem sign_smul_gen (m : ZMod 4) : (gen : zHat.{u}) • m = -m := by
  rw [sign_smul, lift_gen]
  simp

/-- The sign cocycle modulo four: `0` on even profinite integers and `1` on odd ones. -/
def signCocycle : Z1 zHat.{u} (ZMod 4) :=
  ⟨fun g ↦ if (lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) g = 1 then 0 else 1,
    mem_Z1_iff.2 ⟨(continuous_of_discreteTopology (f := fun a : (ZMod 4)ˣ ↦
      if a = 1 then (0 : ZMod 4) else 1)).comp (lift _).continuous, by
      intro g h
      have hfinite : ∀ a b : (ZMod 4)ˣ,
          (if a * b = 1 then (0 : ZMod 4) else 1) =
            a • (if b = 1 then (0 : ZMod 4) else 1) +
              (if a = 1 then (0 : ZMod 4) else 1) := by decide
      simpa only [map_mul, MulAction.compHom_smul_def, ContinuousMonoidHom.coe_toMonoidHom,
        MonoidHom.coe_ofClass] using
        hfinite ((lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) g)
          ((lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) h)⟩⟩

/-- Evaluation of the sign cocycle by its finite sign character. This is an explicit rewrite:
the simp normal form keeps `signCocycle` so that its generator evaluations can apply. -/
theorem signCocycle_apply (g : zHat.{u}) :
    (signCocycle : zHat.{u} → ZMod 4) g =
      if (lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) g = 1 then 0 else 1 := (rfl)

/-- The sign cocycle takes value one at the generator. -/
@[simp]
theorem signCocycle_gen : (signCocycle : zHat.{u} → ZMod 4) gen = 1 := by
  rw [signCocycle_apply, lift_gen]
  decide

/-- The sign cocycle vanishes at the generator of the subgroup of index two. -/
@[simp]
theorem signCocycle_gen_sq : (signCocycle : zHat.{u} → ZMod 4) (gen ^ 2) = 0 := by
  rw [signCocycle_apply, map_pow, lift_gen]
  decide

/-- Doubling the sign cocycle is the coboundary of `-1`. This is an equality of cochains. -/
theorem two_smul_signCocycle :
    (2 : ℕ) • (signCocycle : zHat.{u} → ZMod 4) = d0 zHat (ZMod 4) (-1) := by
  funext g
  rw [Pi.smul_apply, signCocycle_apply, d0_apply]
  have hfinite : ∀ a : (ZMod 4)ˣ,
      (2 : ℕ) • (if a = 1 then (0 : ZMod 4) else 1) = a • (-1 : ZMod 4) - (-1) := by
    decide
  simpa only [MulAction.compHom_smul_def, ContinuousMonoidHom.coe_toMonoidHom,
    MonoidHom.coe_ofClass] using
    hfinite ((lift (-1 : (ZMod 4)ˣ) : zHat.{u} →ₜ* _) g)

/-- The sign cocycle has nonzero cohomology class: an odd value cannot be a sign coboundary. -/
theorem signCocycle_class_ne_zero : (signCocycle : H1 zHat.{u} (ZMod 4)) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := mem_B1_iff.1 (H1pi_eq_zero_iff.1 h)
  have hg := hm gen
  rw [sign_smul_gen, signCocycle_gen] at hg
  have hfinite : ∀ m : ZMod 4, -m - m ≠ 1 := by decide
  exact hfinite m hg

/-- The nonzero sign class is killed by two. -/
@[simp]
theorem two_smul_signCocycle_class_eq_zero :
    (2 : ℕ) • (signCocycle : H1 zHat.{u} (ZMod 4)) = 0 := by
  have hclass : (((2 : ℕ) • signCocycle : Z1 zHat.{u} (ZMod 4)) :
      H1 zHat.{u} (ZMod 4)) = 0 := by
    apply H1pi_eq_zero_iff.2
    refine mem_B1_iff.2 ⟨-1, fun g ↦ ?_⟩
    simpa only [d0_apply, AddSubgroup.coe_nsmul, Pi.smul_apply] using
      (congrFun two_smul_signCocycle g).symm
  simpa only [two_nsmul, ← QuotientAddGroup.mk_add] using hclass

/-- On the sign cocycle, index-two corestriction after restriction is zero at the generator,
whereas twice the cocycle is `2`. Thus the normalization fails on cochains. -/
theorem cochainsCor1_signCocycle_gen :
    cochainsCor1 zHat (ZMod 4) (modSubgroup (2 : ℕ+)).toSubgroup
      (modTransversal 2) (mk_modTransversal 2)
        (fun x ↦ (signCocycle : zHat.{u} → ZMod 4) x) gen = 0 := by
  rw [cochainsCor1_modTransversal_res_gen 2 (ZMod 4) (mem_Z1_iff.1 signCocycle.property).2]
  simp [Finset.sum_range_succ]

/-- The index-two normalization is false for sign cocycle representatives, although it holds
for their cohomology classes. -/
theorem cochainsCor1_res_signCocycle_ne_two_smul :
    cochainsCor1 zHat (ZMod 4) (modSubgroup (2 : ℕ+)).toSubgroup
      (modTransversal 2) (mk_modTransversal 2)
        (fun x ↦ (signCocycle : zHat.{u} → ZMod 4) x) ≠
      (2 : ℕ) • (signCocycle : zHat.{u} → ZMod 4) := by
  intro h
  have hg := congrFun h gen
  rw [cochainsCor1_signCocycle_gen, Pi.smul_apply, signCocycle_gen] at hg
  norm_num at hg
  exact (by decide : (0 : ZMod 4) ≠ 2) hg

/-- On cohomology the correction disappears: corestriction after restriction kills the
nonzero sign class of order two. -/
theorem explicitCor1_res_signCocycle :
    explicitCor1 zHat (ZMod 4) (modSubgroup (2 : ℕ+)).toSubgroup
      (modSubgroup 2).isOpen
      (explicitRes1 zHat (ZMod 4) (modSubgroup 2).toSubgroup
        (signCocycle : H1 zHat.{u} (ZMod 4))) = 0 := by
  have htwo : ((2 : ℕ+) : ℕ) = 2 := rfl
  rw [explicitCor1_comp_res1, modSubgroup_index, htwo, two_smul_signCocycle_class_eq_zero]

end TauCeti.zHat
