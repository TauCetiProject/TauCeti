/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti AI contributors
-/
module

public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.Topology.Algebra.Group.Profinite.QuotientTower

/-!
# The congruence towers of `ℤ_pˣ` and `ℤ_p`

The reductions modulo `p ^ n` present both the units `ℤ_pˣ` and the additive group `ℤ_p` as
towers of finite quotients (`TauCeti.FiniteQuotientTower`).

* `TauCeti.FiniteQuotientTower.unitTower p`: the reductions
  `PadicInt.unitsToZModPow n : ℤ_pˣ → (ℤ/p^nℤ)ˣ` with transition maps `ZMod.unitsMap`. Its
  kernels are the principal unit groups `U^(n) = 1 + p^n ℤ_p` (`ker_unitTower`).
* `TauCeti.FiniteQuotientTower.padicTower p`: the truncations `PadicInt.toZModPow n` of `ℤ_p`,
  written multiplicatively as homomorphisms `Multiplicative ℤ_p → Multiplicative (ℤ/p^nℤ)` (the
  form in which `ℤ_p` is a group for convolution and for the completed group algebra), with
  transition maps the reductions `ZMod.castHom`.

Both towers include `p = 2` and the trivial level `n = 0`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Ann. Math. Qué.
  (2024), Remarks 3.11–3.12 and Proposition 3.16.
-/

public section

namespace TauCeti

namespace FiniteQuotientTower

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The units -/

/-- The **congruence tower of `ℤ_pˣ`**: the reductions `ℤ_pˣ → (ℤ/p^nℤ)ˣ` modulo `p ^ n`, with
the reductions `(ℤ/p^nℤ)ˣ → (ℤ/p^mℤ)ˣ` for `m ≤ n` as transition maps. -/
noncomputable def unitTower : FiniteQuotientTower ℤ_[p]ˣ fun n ↦ (ZMod (p ^ n))ˣ where
  q := PadicInt.unitsToZModPow
  surjective_q := PadicInt.unitsToZModPow_surjective
  t h := ZMod.unitsMap (pow_dvd_pow p h)
  t_q _ := PadicInt.unitsMap_unitsToZModPow _
  separates {u} hu := by
    by_contra! h
    refine hu ((Subgroup.mem_bot).mp ?_)
    rw [← iInf_unitsPrincipal_eq_bot (p := p), Subgroup.mem_iInf]
    exact fun n ↦ unitsToZModPow_eq_one_iff.mp (h n)

variable {p}

/-- The projections of the congruence tower of `ℤ_pˣ` are the reductions modulo `p ^ n`. -/
@[simp]
theorem unitTower_q (n : ℕ) : (unitTower p).q n = PadicInt.unitsToZModPow n :=
  (rfl)

/-- The transition maps of the congruence tower of `ℤ_pˣ` are the reductions of units. -/
@[simp]
theorem unitTower_t {m n : ℕ} (h : m ≤ n) :
    (unitTower p).t h = ZMod.unitsMap (pow_dvd_pow p h) :=
  (rfl)

/-- The kernels of the congruence tower of `ℤ_pˣ` are the principal unit groups
`U^(n) = 1 + p^n ℤ_p`. -/
theorem ker_unitTower (n : ℕ) : ((unitTower p).ker n : Subgroup ℤ_[p]ˣ) = unitsPrincipal p n :=
  (toSubgroup_ker _ n).trans (ker_unitsToZModPow p n)

/-- A unit lies in the `n`-th kernel of the congruence tower of `ℤ_pˣ` exactly when it is a
principal unit of level `n`. -/
theorem mem_ker_unitTower {n : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ (unitTower p).ker n ↔ u ∈ unitsPrincipal p n :=
  (unitTower p).mem_ker.trans unitsToZModPow_eq_one_iff

/-! ### The additive group -/

variable (p) in
/-- The **congruence tower of `ℤ_p`**, written multiplicatively: the truncations
`ℤ_p → ℤ/p^nℤ` modulo `p ^ n`, with the reductions `ℤ/p^nℤ → ℤ/p^mℤ` for `m ≤ n` as transition
maps. -/
noncomputable def padicTower :
    FiniteQuotientTower (Multiplicative ℤ_[p]) fun n ↦ Multiplicative (ZMod (p ^ n)) where
  q n :=
    { toMonoidHom := AddMonoidHom.toMultiplicative (PadicInt.toZModPow n : ℤ_[p] →+* _)
      continuous_toFun := PadicInt.continuous_toZModPow n }
  surjective_q n := ZMod.ringHom_surjective (PadicInt.toZModPow n)
  t {m n} h := AddMonoidHom.toMultiplicative (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)))
  t_q {m n} h x := PadicInt.cast_toZModPow m n h x.toAdd
  separates {x} hx := by
    by_contra! h
    refine hx (Multiplicative.toAdd.injective (PadicInt.ext_of_toZModPow.mp fun n ↦ ?_))
    rw [toAdd_one, map_zero]
    -- The `n`-th projection is `toZModPow n` read through `Multiplicative`.
    exact congrArg Multiplicative.toAdd (h n)

/-- The projections of the congruence tower of `ℤ_p` are the truncations modulo `p ^ n`. -/
@[simp]
theorem padicTower_q_apply (n : ℕ) (x : Multiplicative ℤ_[p]) :
    ((padicTower p).q n x).toAdd = PadicInt.toZModPow n x.toAdd :=
  (rfl)

/-- The transition maps of the congruence tower of `ℤ_p` are the reductions `ZMod.cast`. -/
@[simp]
theorem padicTower_t_apply {m n : ℕ} (h : m ≤ n) (a : Multiplicative (ZMod (p ^ n))) :
    ((padicTower p).t h a).toAdd = ZMod.cast a.toAdd :=
  (rfl)

/-- The kernels of the congruence tower of `ℤ_p` are the ideals `p ^ n ℤ_p`. -/
theorem mem_ker_padicTower {n : ℕ} {x : Multiplicative ℤ_[p]} :
    x ∈ (padicTower p).ker n ↔ x.toAdd ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  rw [mem_ker, ← PadicInt.ker_toZModPow, RingHom.mem_ker, ← Multiplicative.toAdd.injective.eq_iff,
    padicTower_q_apply, toAdd_one]

end FiniteQuotientTower

end TauCeti
