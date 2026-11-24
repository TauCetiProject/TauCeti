/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Units of the profinite integers

An element of the profinite integers `Additive zHat` is a unit exactly when all of its finite
reductions are units, equivalently when all of its `ℓ`-adic components are units. The product
decomposition of the profinite integers therefore restricts to a topological group isomorphism
between their unit group and the product of the groups `ℤ_[ℓ]ˣ`.

A compatible family of characters `G →* (ZMod n)ˣ` consequently assembles uniquely into a
character `G →* (Additive zHat)ˣ`. The assembled character is continuous whenever all of its
finite-level characters are continuous.

The kernels of the reductions `(Additive zHat)ˣ →* (ZMod n)ˣ` form the open principal congruence
subgroups `TauCeti.zHat.detGamma n`, with join `detGamma m ⊔ detGamma n = detGamma (gcd m n)`
via the primewise unit decomposition.

## Main definitions

* `TauCeti.zHat.unitsEquivPiPadicInt`: the topological group isomorphism
  `(Additive zHat)ˣ ≃ₜ* ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ`.
* `TauCeti.zHat.unitsLift`: the character into the profinite units assembled from compatible
  characters at every finite level.
* `TauCeti.zHat.detGamma`: the principal congruence subgroup of level `n : ℕ+` in
  `(Additive zHat)ˣ`.

## Main results

* `TauCeti.zHat.isUnit_iff_toZMod`, `TauCeti.zHat.isUnit_iff_component`: the finite-level and
  `ℓ`-adic unit criteria.
* `TauCeti.zHat.map_toZMod_unitsLift`, `TauCeti.zHat.unitsLift_unique`: the characterizing
  property of the assembled character.
* `TauCeti.zHat.continuous_unitsLift`: continuity is detected at the finite levels.
* `TauCeti.zHat.unitsMap_toZMod_surjective`: reduction of profinite units modulo every positive
  integer `n` is surjective onto `(ZMod n)ˣ`.
* `TauCeti.zHat.surjective_of_forall_surjective_unitsMap_toZMod`: a continuous map from a compact
  space into `(Additive zHat)ˣ` is surjective when it is surjective at every finite level.
* `TauCeti.zHat.detGamma_one`, `TauCeti.zHat.detGamma_le_detGamma_of_dvd`,
  `TauCeti.zHat.detGamma_gcd_eq_sup`: level-one, divisibility, and join laws for `detGamma`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti

namespace zHat

universe u v

/-- A profinite integer is a unit exactly when each of its `ℓ`-adic components is a unit. -/
theorem isUnit_iff_component (a : Additive zHat.{u}) :
    IsUnit a ↔ ∀ (ℓ : ℕ) (_ : Fact ℓ.Prime), IsUnit (component ℓ a) := by
  constructor
  · exact fun ha ℓ _ ↦ ha.map (component ℓ)
  · intro h
    rw [← MulEquiv.isUnit_map ringEquivPiPadicInt.{u}, Pi.isUnit_iff]
    exact fun ℓ ↦ by simpa only [ringEquivPiPadicInt_apply] using h ℓ ⟨ℓ.property⟩

/-- A profinite integer is a unit exactly when its reduction modulo every positive integer is a
unit. -/
theorem isUnit_iff_toZMod (a : Additive zHat.{u}) :
    IsUnit a ↔ ∀ n : ℕ+, IsUnit (toZMod n a) := by
  refine ⟨fun ha n ↦ ha.map (toZMod n), fun h ↦ (isUnit_iff_component a).2 fun ℓ hℓ ↦ ?_⟩
  by_contra hunit
  have hdvd : (ℓ : ℤ_[ℓ]) ∣ component ℓ a :=
    PadicInt.norm_lt_one_iff_dvd _ |>.mp (PadicInt.not_isUnit_iff.mp hunit)
  have hz : PadicInt.toZModPow 1 (component ℓ a) = 0 :=
    (PadicInt.toZModPow_eq_zero_iff_dvd 1 _).2 (by simpa using hdvd)
  have hlevel : IsUnit (PadicInt.toZModPow 1 (component ℓ a)) := by
    rw [toZModPow_component]
    exact h _
  have : Nontrivial (ZMod (ℓ ^ 1)) :=
    ZMod.nontrivial_iff.mpr (by simpa using hℓ.out.ne_one)
  rw [hz] at hlevel
  exact not_isUnit_zero hlevel

/-- **The unit-group decomposition of the profinite integers.** The product decomposition
`Additive zHat ≃+* ∀ ℓ, ℤ_[ℓ]` restricts to an isomorphism of topological groups on units. -/
noncomputable def unitsEquivPiPadicInt :
    (Additive zHat.{u})ˣ ≃ₜ* ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ :=
  let e : Additive zHat.{u} ≃ₜ* (∀ ℓ : Nat.Primes, ℤ_[ℓ]) :=
    { toMulEquiv := ringEquivPiPadicInt.toMulEquiv
      continuous_toFun := continuous_ringEquivPiPadicInt
      continuous_invFun := continuous_ringEquivPiPadicInt_symm }
  (Units.mapContinuousMulEquiv e).trans ContinuousMulEquiv.piUnits

/-- The `ℓ`-adic coordinate of the unit-group decomposition is induced by `zHat.component ℓ`. -/
@[simp]
theorem unitsEquivPiPadicInt_apply (a : (Additive zHat.{u})ˣ) (ℓ : Nat.Primes) :
    unitsEquivPiPadicInt a ℓ = Units.map (component ℓ) a := by
  rw [unitsEquivPiPadicInt, ContinuousMulEquiv.trans_apply]
  apply Units.ext
  refine (MulEquiv.val_piUnits_apply _ _).trans ?_
  rw [Units.mapContinuousMulEquiv_apply, Units.coe_map, Units.coe_map]
  exact ringEquivPiPadicInt_apply (a : Additive zHat.{u}) ℓ

/-- The `ℓ`-adic component of the inverse unit-group decomposition is the prescribed unit. -/
@[simp]
theorem component_unitsEquivPiPadicInt_symm (a : ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ)
    (ℓ : Nat.Primes) :
    component ℓ (unitsEquivPiPadicInt.symm a : Additive zHat.{u}) = a ℓ := by
  have h := congrFun (unitsEquivPiPadicInt.apply_symm_apply a) ℓ
  rw [unitsEquivPiPadicInt_apply] at h
  exact congrArg Units.val h

section UnitsLift

variable {G : Type v} [Monoid G]
variable (χ : ∀ n : ℕ+, G →* (ZMod n)ˣ)
variable (hχ : ∀ (m n : ℕ+) (h : (n : ℕ) ∣ m) (g : G),
  ZMod.unitsMap h (χ m g) = χ n g)

include hχ

private theorem unitsCoe_compatible (g : G) (m n : ℕ+) (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (χ n g : ZMod n) = (χ m g : ZMod m) := by
  exact congrArg Units.val (hχ n m h g)

private noncomputable def unitsLiftValue (g : G) : Additive zHat.{u} :=
  (existsUnique_forall_toZMod_eq (fun n ↦ (χ n g : ZMod n))
    (unitsCoe_compatible χ hχ g)).exists.choose

private theorem toZMod_unitsLiftValue (g : G) (n : ℕ+) :
    toZMod n (unitsLiftValue χ hχ g) = (χ n g : ZMod n) :=
  (existsUnique_forall_toZMod_eq (fun n ↦ (χ n g : ZMod n))
    (unitsCoe_compatible χ hχ g)).exists.choose_spec n

private noncomputable def unitsLiftMonoid : G →* Additive zHat.{u} :=
  { toFun := unitsLiftValue χ hχ
    map_one' := ext_of_toZMod fun n ↦ by
      rw [toZMod_unitsLiftValue, map_one, map_one, Units.val_one]
    map_mul' := fun g g' ↦ ext_of_toZMod fun n ↦ by
      rw [toZMod_unitsLiftValue, map_mul, map_mul, toZMod_unitsLiftValue,
        toZMod_unitsLiftValue, Units.val_mul] }

private theorem unitsLiftMonoid_apply (g : G) :
    unitsLiftMonoid χ hχ g = unitsLiftValue χ hχ g := rfl

private theorem isUnit_unitsLiftMonoid (g : G) : IsUnit (unitsLiftMonoid χ hχ g) :=
  (isUnit_iff_toZMod _).2 fun n ↦ by
    simpa only [unitsLiftMonoid_apply, toZMod_unitsLiftValue] using Units.isUnit (χ n g)

/-- **Assembly of compatible finite-level characters.** A family of characters
`χ n : G →* (ZMod n)ˣ` compatible with reduction along divisibility assembles into a character
`G →* (Additive zHat)ˣ`, characterized by `zHat.map_toZMod_unitsLift`. -/
noncomputable def unitsLift : G →* (Additive zHat.{u})ˣ :=
  IsUnit.liftRight (unitsLiftMonoid χ hχ) (isUnit_unitsLiftMonoid χ hχ)

/-- The underlying profinite integer of the assembled character has the prescribed reduction
modulo `n`. -/
@[simp]
theorem toZMod_coe_unitsLift (n : ℕ+) (g : G) :
    toZMod n (unitsLift.{u, v} χ hχ g : Additive zHat.{u}) = (χ n g : ZMod n) := by
  rw [unitsLift, IsUnit.coe_liftRight]
  exact toZMod_unitsLiftValue χ hχ g n

/-- The reduction modulo `n` of the assembled character is its prescribed level-`n` character. -/
@[simp]
theorem map_toZMod_unitsLift (n : ℕ+) (g : G) :
    Units.map (toZMod.{u} n) (unitsLift.{u, v} χ hχ g) = χ n g := by
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_ofClass, toZMod_coe_unitsLift]

/-- The compatible finite-level reductions uniquely determine the assembled character. -/
theorem unitsLift_unique (ψ : G →* (Additive zHat.{u})ˣ)
    (hψ : ∀ (n : ℕ+) (g : G), Units.map (toZMod.{u} n) (ψ g) = χ n g) :
    ψ = unitsLift.{u, v} χ hχ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply ext_of_toZMod
  intro n
  have hn := congrArg Units.val
    ((hψ n g).trans (map_toZMod_unitsLift χ hχ n g).symm)
  simp only [Units.coe_map, MonoidHom.coe_ofClass] at hn
  exact hn

/-- The assembled character is continuous whenever all of its finite-level characters are
continuous. -/
theorem continuous_unitsLift [TopologicalSpace G]
    (hcont : ∀ n : ℕ+, Continuous (χ n)) : Continuous (unitsLift.{u, v} χ hχ) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_iff_forall_continuous_toZMod.mpr
    intro n
    exact (Units.continuous_val.comp (hcont n)).congr fun g ↦
      (toZMod_coe_unitsLift χ hχ n g).symm
  · apply continuous_iff_forall_continuous_toZMod.mpr
    intro n
    exact (Units.continuous_coe_inv.comp (hcont n)).congr fun g ↦ by
      simpa only [Function.comp_apply, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass] using
        congrArg Units.val (congrArg Inv.inv (map_toZMod_unitsLift χ hχ n g).symm)

end UnitsLift

/-- **Reduction of profinite units modulo `n` is surjective.** Every unit of `ℤ/nℤ` lifts to a
unit of `ℤ̂`: lifting the residue representative `a ∈ ℕ` coprime to `n` to `a` in each `ℓ`-adic
factor with `ℓ ∣ n` and to `1` in all other factors produces a profinite unit reducing to it. -/
theorem unitsMap_toZMod_surjective (n : ℕ+) :
    Function.Surjective (Units.map (toZMod.{u} n).toMonoidHom) := fun v ↦ by
  classical
  let a : ℕ := (v : ZMod n).val
  have hcop : a.Coprime n := ZMod.val_coe_unit_coprime v
  have hunit (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ n) : IsUnit (a : ℤ_[ℓ]) := by
    have : Fact (ℓ : ℕ).Prime := ⟨ℓ.property⟩
    exact PadicInt.isUnit_natCast_of_coprime (hcop.symm.coprime_dvd_left hℓ)
  let f : ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ := fun ℓ ↦
    if hℓ : (ℓ : ℕ) ∣ n then (hunit ℓ hℓ).unit else 1
  refine ⟨unitsEquivPiPadicInt.symm f, Units.ext ?_⟩
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  refine ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (dvd_pow_self p hk).trans hpk
  rw [cast_toZMod_eq_toZModPow_component n hpk,
    component_unitsEquivPiPadicInt_symm f ⟨p, hp⟩]
  simp only [f, hpn, ↓reduceDIte, IsUnit.unit_spec, map_natCast, a]
  rw [← ZMod.cast_natCast hpk, ZMod.natCast_zmod_val]

/-- **Surjectivity onto the profinite units is detected at the finite levels.** A continuous map
from a compact space into `(Additive zHat)ˣ` is surjective once each of its reductions onto
`(ZMod n)ˣ` is surjective. -/
theorem surjective_of_forall_surjective_unitsMap_toZMod {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {f : X → (Additive zHat.{u})ˣ} (hf : Continuous f)
    (h : ∀ n : ℕ+, Function.Surjective fun x ↦ (Units.map (toZMod.{u} n) (f x) : (ZMod n)ˣ)) :
    Function.Surjective f := by
  intro a
  refine (exists_eq_of_forall_exists_toZMod_eq (Units.continuous_val.comp hf) a fun n ↦ ?_).imp
    fun x hx ↦ Units.ext hx
  obtain ⟨x, hx⟩ := h n (Units.map (toZMod.{u} n) a)
  refine ⟨x, ?_⟩
  simpa only [Function.comp_apply, Units.coe_map, MonoidHom.coe_ofClass] using
    congrArg Units.val hx

section Congruence

/-- The principal congruence subgroup of level `n : ℕ+` in `(Additive zHat)ˣ`, consisting of
units reducing to `1` modulo `n`. -/
noncomputable def detGamma (n : ℕ+) : OpenSubgroup (Additive zHat.{u})ˣ where
  toSubgroup := (Units.map (toZMod.{u} n).toMonoidHom).ker
  isOpen' := (isOpen_discrete {1}).preimage (Continuous.units_map _ (continuous_toZMod n))

@[simp]
theorem mem_detGamma_iff (n : ℕ+) (a : (Additive zHat.{u})ˣ) :
    a ∈ detGamma.{u} n ↔ Units.map (toZMod.{u} n).toMonoidHom a = 1 :=
  Iff.rfl

/-- `detGamma 1` is the whole unit group `(Additive zHat)ˣ`. -/
@[simp]
theorem detGamma_one : detGamma.{u} 1 = ⊤ :=
  OpenSubgroup.ext fun a ↦ by
    simp only [mem_detGamma_iff, OpenSubgroup.mem_top, iff_true]
    apply Units.ext
    simp only [PNat.one_coe]
    exact Subsingleton.elim _ _

/-- `detGamma n ≤ detGamma m` whenever `m ∣ n`. -/
theorem detGamma_le_detGamma_of_dvd {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    detGamma.{u} n ≤ detGamma.{u} m := by
  intro a ha
  rw [mem_detGamma_iff] at ha ⊢
  apply Units.ext
  have hval := congrArg (ZMod.castHom h (ZMod m)) (congrArg Units.val ha)
  rw [Units.val_one, map_one] at hval
  simpa [Units.coe_map, cast_toZMod h] using hval

private theorem mem_detGamma_iff_forall_component {n : ℕ+} {a : (Additive zHat.{u})ˣ} :
    a ∈ detGamma.{u} n ↔ ∀ ℓ : Nat.Primes,
      Units.map (PadicInt.toZModPow ((n : ℕ).factorization ℓ)).toMonoidHom
        (unitsEquivPiPadicInt a ℓ) = 1 := by
  constructor
  · intro ha ℓ
    have hdvd : (ℓ : ℕ) ^ (n : ℕ).factorization ℓ ∣ n := Nat.ordProj_dvd n ℓ
    let m : ℕ+ := ⟨(ℓ : ℕ) ^ (n : ℕ).factorization ℓ, pow_pos ℓ.property.pos _⟩
    have hm := detGamma_le_detGamma_of_dvd (m := m) hdvd ha
    rw [mem_detGamma_iff] at hm
    apply Units.ext
    have hval : toZMod.{u} m (a : Additive zHat.{u}) = 1 := by
      simpa [Units.coe_map] using congrArg Units.val hm
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      unitsEquivPiPadicInt_apply, Units.val_one]
    exact (toZModPow_component ℓ ((n : ℕ).factorization ℓ) _).trans hval
  · intro h
    rw [mem_detGamma_iff]
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe, Units.val_one]
    refine ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_
    have : Fact p.Prime := ⟨hp⟩
    have hle : k ≤ (n : ℕ).factorization p :=
      (hp.pow_dvd_iff_le_factorization n.ne_zero).mp hpk
    have hℓ : PadicInt.toZModPow ((n : ℕ).factorization p) (component p (a : Additive zHat.{u})) =
        1 := by
      have h1 := congrArg Units.val (h ⟨p, hp⟩)
      have h2 : (unitsEquivPiPadicInt a ⟨p, hp⟩ : ℤ_[p]) = component p (a : Additive zHat.{u}) :=
        congrArg Units.val (unitsEquivPiPadicInt_apply a ⟨p, hp⟩)
      simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, h2,
        Units.val_one] using h1
    rw [cast_toZMod_eq_toZModPow_component n hpk, ← PadicInt.cast_toZModPow k _ hle, hℓ,
      ZMod.cast_one (pow_dvd_pow p hle), ZMod.cast_one hpk]

/-- **Join law for principal congruence subgroups of `ℤ̂ˣ`:**
`detGamma m ⊔ detGamma n = detGamma (gcd m n)`. -/
theorem detGamma_gcd_eq_sup (m n : ℕ+) :
    detGamma.{u} m ⊔ detGamma.{u} n =
      detGamma.{u} ⟨Nat.gcd m n, Nat.gcd_pos_of_pos_left n m.pos⟩ := by
  classical
  let d : ℕ+ := ⟨Nat.gcd m n, Nat.gcd_pos_of_pos_left n m.pos⟩
  have hd : (d : ℕ) = Nat.gcd m n := rfl
  refine le_antisymm
    (sup_le (detGamma_le_detGamma_of_dvd (Nat.gcd_dvd_left _ _))
      (detGamma_le_detGamma_of_dvd (Nat.gcd_dvd_right _ _)))
    fun a ha ↦ ?_
  let x : ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ := fun ℓ ↦
    if (m : ℕ).factorization ℓ ≤ (n : ℕ).factorization ℓ then unitsEquivPiPadicInt a ℓ else 1
  let y : ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ := fun ℓ ↦
    if (m : ℕ).factorization ℓ ≤ (n : ℕ).factorization ℓ then 1 else unitsEquivPiPadicInt a ℓ
  have hmul : unitsEquivPiPadicInt.symm x * unitsEquivPiPadicInt.symm y = a := by
    apply unitsEquivPiPadicInt.injective
    ext ℓ
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply, Units.val_mul, x, y]
    split_ifs <;> simp
  have hx : unitsEquivPiPadicInt.symm x ∈ detGamma.{u} m := by
    rw [mem_detGamma_iff_forall_component]
    intro ℓ
    rw [ContinuousMulEquiv.apply_symm_apply]
    dsimp only [x]
    split_ifs with hle
    · have hfac : (d : ℕ).factorization ℓ = (m : ℕ).factorization ℓ := by
        rw [hd, Nat.factorization_gcd m.ne_zero n.ne_zero]
        exact min_eq_left hle
      rw [← hfac]
      exact mem_detGamma_iff_forall_component.mp (ha : a ∈ detGamma.{u} d) ℓ
    · simp
  have hy : unitsEquivPiPadicInt.symm y ∈ detGamma.{u} n := by
    rw [mem_detGamma_iff_forall_component]
    intro ℓ
    rw [ContinuousMulEquiv.apply_symm_apply]
    dsimp only [y]
    split_ifs with hle
    · simp
    · have hfac : (d : ℕ).factorization ℓ = (n : ℕ).factorization ℓ := by
        rw [hd, Nat.factorization_gcd m.ne_zero n.ne_zero]
        exact min_eq_right (le_of_not_ge hle)
      rw [← hfac]
      exact mem_detGamma_iff_forall_component.mp (ha : a ∈ detGamma.{u} d) ℓ
  rw [← hmul]
  exact Subgroup.mul_mem_sup hx hy

end Congruence

end zHat

end TauCeti
