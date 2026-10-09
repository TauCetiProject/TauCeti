/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring

/-!
# The profinite integers as the inverse limit of the `ZMod n`

The ring of profinite integers `Additive zHat` (see
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring`) projects onto every finite quotient
`ZMod n` of `ℤ`, and is determined by these projections: it is the inverse limit of the rings
`ZMod n` along the reduction maps `ZMod.castHom`. This file builds the projections and proves
that limit property, in the form of a universal property for additive and for ring
homomorphisms into `Additive zHat`.

The projection `zHat.toZMod n` is the continuous homomorphism `zHat.lift (ofAdd 1)` into the
finite discrete group `Multiplicative (ZMod n)`, read additively; it is a ring homomorphism for
the product of `Additive zHat`, and the projections are compatible along divisibility
(`zHat.cast_toZMod`). Every open normal subgroup of `zHat` contains the kernel of some
projection (`zHat.exists_monoidHom_mk_eq_toZMod`), so two profinite integers with the same
projections are equal (`zHat.ext_of_toZMod`), a map into the profinite integers is continuous as
soon as its projections are (`zHat.continuous_iff_forall_continuous_toZMod`), and a compatible
family of residues is realized by a unique profinite integer
(`zHat.existsUnique_forall_toZMod_eq`). The last statement assembles a compatible family of
additive homomorphisms `A →+ ZMod n` into a unique additive homomorphism
`zHat.addLift f : A →+ Additive zHat`, continuous when every member of the family is. A compatible
family of ring homomorphisms `R →+* ZMod n` assembles in the same way into a unique ring
homomorphism `zHat.ringLift f : R →+* Additive zHat`, whose underlying additive homomorphism is the
additive lift of the family. The integers embed into the profinite integers: `Additive zHat` has
characteristic zero.

The index `n` of the finite levels runs over `ℕ+`: for `n = 0` the group `Multiplicative (ZMod 0)`
is `ℤ`, which is not profinite, and no lift exists.

## Main definitions

* `TauCeti.zHat.toZMod`: reduction of a profinite integer modulo `n`, a continuous ring
  homomorphism `Additive zHat →+* ZMod n`.
* `TauCeti.zHat.addLift`: the additive homomorphism into `Additive zHat` assembled from a
  compatible family of additive homomorphisms into the `ZMod n`.
* `TauCeti.zHat.ringLift`: the ring homomorphism into `Additive zHat` assembled from a compatible
  family of ring homomorphisms into the `ZMod n`.

## Main results

* `TauCeti.zHat.cast_toZMod`, `TauCeti.zHat.castHom_comp_toZMod`: the projections are compatible
  along divisibility.
* `TauCeti.zHat.ext_of_toZMod`, `TauCeti.zHat.ext_iff_toZMod`,
  `TauCeti.zHat.existsUnique_forall_toZMod_eq`: a profinite integer is determined by its
  projections, and every compatible family of residues comes from one.
* `TauCeti.zHat.toZMod_addLift`, `TauCeti.zHat.addLift_unique`,
  `TauCeti.zHat.continuous_addLift`: the universal property of `Additive zHat` as the inverse
  limit of the groups `ZMod n`.
* `TauCeti.zHat.toZMod_ringLift`, `TauCeti.zHat.ringLift_unique`,
  `TauCeti.zHat.continuous_ringLift`: the universal property of `Additive zHat` as the inverse
  limit of the rings `ZMod n`; `TauCeti.zHat.coe_addMonoidHom_ringLift` compares it with the
  additive one.
* `TauCeti.zHat.continuous_iff_forall_continuous_toZMod`: continuity into `Additive zHat` is
  detected by the projections.
* The `CharZero (Additive zHat)` instance and `TauCeti.zHat.ofInt_injective`: the integers embed
  into the profinite integers.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
* Mathlib's `Mathlib.NumberTheory.Padics.RingHoms`, the same inverse-limit API for the `p`-adic
  integers, whose structure this file follows: `PadicInt.toZModPow`, `PadicInt.cast_toZModPow`,
  `PadicInt.zmod_cast_comp_toZModPow`, `PadicInt.ext_of_toZModPow`, `PadicInt.lift`,
  `PadicInt.lift_spec`, `PadicInt.lift_unique` and `PadicInt.lift_self` correspond to
  `TauCeti.zHat.toZMod`, `TauCeti.zHat.cast_toZMod`, `TauCeti.zHat.castHom_comp_toZMod`,
  `TauCeti.zHat.ext_iff_toZMod`, `TauCeti.zHat.ringLift`, `TauCeti.zHat.toZMod_comp_ringLift`,
  `TauCeti.zHat.ringLift_unique` and `TauCeti.zHat.ringLift_toZMod`.
-/

public section

namespace TauCeti

namespace zHat

universe u v

open Additive Multiplicative

section ToZMod

variable (n : ℕ+)

variable {n} in
/-- The lift into the finite cyclic group `Multiplicative (ZMod n)` of any element `c` is the
lift of the generator `ofAdd 1`, multiplied by `c` in `ZMod n`. -/
private theorem toAdd_lift_apply (c : Multiplicative (ZMod n)) (x : zHat.{u}) :
    ((lift c : zHat.{u} →ₜ* Multiplicative (ZMod n)) x).toAdd =
      c.toAdd * ((lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) x).toAdd := by
  -- Write `c` as the power `(ofAdd 1) ^ c.toAdd.val` and use that the lift respects powers.
  have hc : c = ofAdd (1 : ZMod n) ^ ((c.toAdd.val : ℕ) : ℤ) := by
    rw [zpow_natCast, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  conv_lhs => rw [hc]
  rw [lift_zpow_apply, toAdd_zpow, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Reduction modulo `n`.** The projection of the profinite integers onto `ZMod n` is the
continuous homomorphism `zHat.lift (ofAdd 1)` into the finite discrete group
`Multiplicative (ZMod n)`, read additively. It is a ring homomorphism for the product of
`Additive zHat`, and the profinite integers are the inverse limit of these projections
(`zHat.existsUnique_forall_toZMod_eq`). -/
noncomputable def toZMod : Additive zHat.{u} →+* ZMod n where
  toFun a := ((lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) a.toMul).toAdd
  map_one' := by simp
  map_mul' a b := by
    -- The product `a * b` is the lift of `a.toMul` at `b.toMul`, and the reduction of a lift
    -- is a multiple of the reduction, by `toAdd_lift_apply`.
    simp only [toMul_mul, map_lift]
    rw [toAdd_lift_apply ((lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) a.toMul)]
  map_zero' := by simp
  map_add' a b := by simp

/-- The reduction of `a` modulo `n` is the lift of the generator of `Multiplicative (ZMod n)`,
evaluated at `a.toMul` and read additively. -/
theorem toZMod_apply (a : Additive zHat.{u}) :
    toZMod n a = ((lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) a.toMul).toAdd := by
  rfl

variable {n} in
/-- The lift of the generator of `Multiplicative (ZMod n)` is reduction modulo `n`, read
multiplicatively. -/
@[simp]
theorem lift_ofAdd_one_apply (x : zHat.{u}) :
    (lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) x = ofAdd (toZMod n (ofMul x)) := by
  rw [toZMod_apply, toMul_ofMul, ofAdd_toAdd]

/-- Reduction modulo `n` is continuous. -/
theorem continuous_toZMod : Continuous (toZMod n : Additive zHat.{u} → ZMod n) :=
  continuous_toAdd.comp ((lift _).continuous.comp continuous_toMul)

/-- **Compatibility of the projections along divisibility.** Reducing modulo `n` and then modulo
a divisor `m` of `n` is reducing modulo `m`. -/
@[simp]
theorem cast_toZMod {m n : ℕ+} (h : (m : ℕ) ∣ n) (a : Additive zHat.{u}) :
    (ZMod.cast (toZMod n a) : ZMod m) = toZMod m a := by
  -- Both sides are continuous homomorphisms out of `ℤ̂` into `Multiplicative (ZMod m)` sending
  -- the generator to `ofAdd 1`; by naturality of the lift they agree.
  let f : Multiplicative (ZMod n) →ₜ* Multiplicative (ZMod m) :=
    ⟨AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod m)).toAddMonoidHom,
      continuous_of_discreteTopology⟩
  have hf1 : f (ofAdd 1) = ofAdd 1 := by
    simp [f, ZMod.cast_one h]
  have hf : f ((lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod n)) a.toMul) =
      (lift (ofAdd 1) : zHat.{u} →ₜ* Multiplicative (ZMod m)) a.toMul := by
    rw [map_lift, hf1]
  rw [lift_ofAdd_one_apply, lift_ofAdd_one_apply, ofMul_toMul] at hf
  simpa [f] using hf

/-- Compatibility of the projections along divisibility, as an equality of ring homomorphisms:
`ZMod.castHom` after reduction modulo `n` is reduction modulo a divisor `m` of `n`. -/
theorem castHom_comp_toZMod {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    (ZMod.castHom h (ZMod m)).comp (toZMod n : Additive zHat.{u} →+* ZMod n) = toZMod m :=
  RingHom.ext fun a ↦ by rw [RingHom.comp_apply, ZMod.castHom_apply, cast_toZMod h]

/-- **Every finite quotient of `ℤ̂` factors through a finite level.** For an open normal
subgroup `U` of `zHat` there is a level `n` and a homomorphism `ψ` from `Multiplicative (ZMod n)`
to `zHat ⧸ U` such that the quotient map is `ψ` after reduction modulo `n`. In particular `U`
contains the kernel of `toZMod n`. -/
theorem exists_monoidHom_mk_eq_toZMod (U : OpenNormalSubgroup zHat.{u}) :
    ∃ (n : ℕ+) (ψ : Multiplicative (ZMod n) →* zHat.{u} ⧸ U.toSubgroup),
      ∀ a : Additive zHat.{u}, (a.toMul : zHat.{u} ⧸ U.toSubgroup) = ψ (ofAdd (toZMod n a)) := by
  -- The class of the generator has order dividing the index `n` of `U`, so it defines a
  -- homomorphism `ψ` out of `Multiplicative (ZMod n)`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ+, (n : ℕ) = U.toSubgroup.index :=
    ⟨⟨U.toSubgroup.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite⟩, rfl⟩
  have hg : zmultiplesHom (Additive (zHat.{u} ⧸ U.toSubgroup))
      (ofMul (gen : zHat.{u} ⧸ U.toSubgroup)) ((n : ℕ) : ℤ) = 0 := by
    rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, ← QuotientGroup.mk_pow, ofMul_eq_zero,
      QuotientGroup.eq_one_iff, hn]
    exact U.toSubgroup.pow_index_mem gen
  let ψ : Multiplicative (ZMod n) →* zHat.{u} ⧸ U.toSubgroup :=
    AddMonoidHom.toMultiplicativeLeft (ZMod.lift n ⟨_, hg⟩)
  have hψ : ψ (ofAdd 1) = (gen : zHat.{u} ⧸ U.toSubgroup) := by
    simp only [ψ, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd]
    rw [← Int.cast_one, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul, toMul_ofMul]
  refine ⟨n, ψ, fun a ↦ ?_⟩
  -- The quotient map and `ψ ∘ lift (ofAdd 1)` are continuous homomorphisms out of `ℤ̂`
  -- agreeing on the generator, hence equal.
  let φ : zHat.{u} →ₜ* zHat.{u} ⧸ U.toSubgroup :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  let φ' : zHat.{u} →ₜ* zHat.{u} ⧸ U.toSubgroup :=
    ContinuousMonoidHom.comp ⟨ψ, continuous_of_discreteTopology⟩ (lift (ofAdd 1))
  have hφ : φ = φ' := hom_ext <| by
    -- Expose the values of the two bundled homomorphisms at the generator.
    change (gen : zHat.{u} ⧸ U.toSubgroup) = ψ (lift (ofAdd 1) gen)
    rw [lift_gen, hψ]
  have hφa := DFunLike.congr_fun hφ a.toMul
  -- Expose the values of the two bundled homomorphisms at `a.toMul`.
  change (a.toMul : zHat.{u} ⧸ U.toSubgroup) = ψ (lift (ofAdd 1) a.toMul) at hφa
  rwa [lift_ofAdd_one_apply, ofMul_toMul] at hφa

/-- **A profinite integer is determined by its projections.** -/
@[ext (iff := false)]
theorem ext_of_toZMod {a b : Additive zHat.{u}} (h : ∀ n : ℕ+, toZMod n a = toZMod n b) :
    a = b := by
  refine toMul.injective (eq_of_forall_mk_eq fun U ↦ ?_)
  obtain ⟨n, ψ, hψ⟩ := exists_monoidHom_mk_eq_toZMod U
  rw [hψ a, hψ b, h n]

/-- Two profinite integers are equal exactly when their reductions modulo every `n` agree. -/
theorem ext_iff_toZMod {a b : Additive zHat.{u}} :
    a = b ↔ ∀ n : ℕ+, toZMod n a = toZMod n b :=
  ⟨fun h _ ↦ h ▸ rfl, ext_of_toZMod⟩

/-- **Continuity into `ℤ̂` is detected by the projections.** A map into the profinite integers
is continuous exactly when all of its reductions modulo `n` are. -/
theorem continuous_iff_forall_continuous_toZMod {X : Type*} [TopologicalSpace X]
    {f : X → Additive zHat.{u}} :
    Continuous f ↔ ∀ n : ℕ+, Continuous fun x ↦ toZMod n (f x) := by
  refine ⟨fun hf n ↦ (continuous_toZMod n).comp hf, fun h ↦ ?_⟩
  have hmul : Continuous fun x ↦ (f x).toMul := by
    refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
    obtain ⟨n, ψ, hψ⟩ := exists_monoidHom_mk_eq_toZMod U
    simp_rw [hψ]
    exact continuous_of_discreteTopology.comp (continuous_ofAdd.comp (h n))
  exact (continuous_ofMul.comp hmul).congr fun x ↦ ofMul_toMul (f x)

/-- The integers embed into the profinite integers: no positive integer reduces to zero
modulo every `n`. -/
instance : CharZero (Additive zHat.{u}) :=
  charZero_of_inj_zero fun k hk ↦ by
    -- Reduce modulo `k + 1`.
    have h := congrArg (toZMod ⟨k + 1, k.succ_pos⟩) hk
    rw [map_natCast, map_zero, PNat.mk_coe, ZMod.natCast_eq_zero_iff] at h
    exact Nat.eq_zero_of_dvd_of_lt h k.lt_succ_self

/-- The canonical homomorphism from `ℤ` to the profinite integers is injective. -/
theorem ofInt_injective : Function.Injective (ofInt : Multiplicative ℤ →* zHat.{u}) :=
  fun a b h ↦ by
    have h' := congrArg ofMul h
    rw [ofMul_ofInt, ofMul_ofInt, Int.cast_inj] at h'
    exact toAdd.injective h'

/-- **The profinite integers are the inverse limit of the `ZMod n`.** A family of residues
`x n : ZMod n`, compatible along the reduction maps, is realized by a unique profinite
integer. -/
theorem existsUnique_forall_toZMod_eq (x : ∀ n : ℕ+, ZMod n)
    (hx : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (x n) = x m) :
    ∃! a : Additive zHat.{u}, ∀ n, toZMod n a = x n := by
  -- The fibre of `toZMod n` over `x n` is closed and nonempty, realized by the integer
  -- `(x n).val`, and the fibres are directed under reverse inclusion because the fibre at
  -- `m * n` lies in those at `m` and at `n`; compactness gives a common point.
  have hcl (n : ℕ+) : IsClosed (toZMod n ⁻¹' {x n} : Set (Additive zHat.{u})) :=
    isClosed_singleton.preimage (continuous_toZMod n)
  have hne (n : ℕ+) : (toZMod n ⁻¹' {x n} : Set (Additive zHat.{u})).Nonempty :=
    ⟨((x n).val : Additive zHat.{u}), by simp⟩
  have hsub {m n : ℕ+} (h : (m : ℕ) ∣ n) :
      (toZMod n ⁻¹' {x n} : Set (Additive zHat.{u})) ⊆ toZMod m ⁻¹' {x m} := fun a ha ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    rw [← RingHom.congr_fun (castHom_comp_toZMod h) a, RingHom.comp_apply, ha, hx]
  have hdir : Directed (· ⊇ ·) fun n : ℕ+ ↦ (toZMod n ⁻¹' {x n} : Set (Additive zHat.{u})) :=
    fun m n ↦ ⟨m * n, hsub (PNat.mul_coe m n ▸ dvd_mul_right (m : ℕ) n),
      hsub (PNat.mul_coe m n ▸ dvd_mul_left (n : ℕ) m)⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir hne
    (fun n ↦ (hcl n).isCompact) hcl
  refine ⟨a, fun n ↦ Set.mem_iInter.mp ha n, fun b hb ↦ ext_of_toZMod fun n ↦ ?_⟩
  exact (hb n).trans (Set.mem_iInter.mp ha n).symm

end ToZMod

section AddLift

variable {A : Type v} [AddZeroClass A] (f : ∀ n : ℕ+, A →+ ZMod n)
  (hf : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), (ZMod.castHom h (ZMod m) : ZMod n →+ ZMod m).comp (f n) =
    f m)

/-- **The universal property of `ℤ̂` as an inverse limit, for additive maps.** A family of additive
homomorphisms `f n : A →+ ZMod n`, compatible along the reduction maps, assembles into the additive
homomorphism `A →+ Additive zHat` whose reduction modulo `n` is `f n` (`zHat.toZMod_addLift`); it is
the only one (`zHat.addLift_unique`). -/
noncomputable def addLift : A →+ Additive zHat.{u} :=
  let g : A → Additive zHat.{u} := fun a ↦
    (existsUnique_forall_toZMod_eq (fun n ↦ f n a)
      fun m n h ↦ DFunLike.congr_fun (hf m n h) a).exists.choose
  have hg : ∀ a n, toZMod n (g a) = f n a := fun a ↦
    (existsUnique_forall_toZMod_eq (fun n ↦ f n a)
      fun m n h ↦ DFunLike.congr_fun (hf m n h) a).exists.choose_spec
  { toFun := g
    -- The additivity axioms are checked level by level, through `ext_of_toZMod`.
    map_zero' := ext_of_toZMod fun n ↦ by rw [hg, map_zero, map_zero]
    map_add' a b := ext_of_toZMod fun n ↦ by rw [hg, map_add, map_add, hg, hg] }

/-- The reduction modulo `n` of the assembled additive homomorphism is the `n`-th member of the
family. -/
@[simp]
theorem toZMod_addLift (n : ℕ+) (a : A) : toZMod n (addLift f hf a) = f n a :=
  (existsUnique_forall_toZMod_eq (fun n ↦ f n a)
    fun m n h ↦ DFunLike.congr_fun (hf m n h) a).exists.choose_spec n

/-- The reduction modulo `n` of the assembled additive homomorphism is the `n`-th member of the
family, as an equality of additive homomorphisms. -/
theorem toZMod_comp_addLift (n : ℕ+) :
    (toZMod n : Additive zHat.{u} →+ ZMod n).comp (addLift f hf) = f n :=
  AddMonoidHom.ext (toZMod_addLift f hf n)

/-- An additive homomorphism into `ℤ̂` whose reductions are the members of the family is the
assembled additive homomorphism. -/
theorem addLift_unique (g : A →+ Additive zHat.{u})
    (hg : ∀ n, (toZMod n : Additive zHat.{u} →+ ZMod n).comp g = f n) :
    g = addLift f hf :=
  AddMonoidHom.ext fun a ↦ ext_of_toZMod fun n ↦ by
    rw [toZMod_addLift, ← hg n, AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass]

/-- **Naturality of the additive universal property in `A`.** Precomposing the assembled additive
homomorphism with `g : B →+ A` assembles the precomposed family. -/
theorem addLift_comp {B : Type*} [AddZeroClass B] (g : B →+ A) :
    (addLift f hf).comp g =
      addLift (fun n ↦ (f n).comp g) fun m n h ↦ by rw [← AddMonoidHom.comp_assoc, hf m n h] :=
  addLift_unique _ _ _ fun n ↦ by rw [← AddMonoidHom.comp_assoc, toZMod_comp_addLift]

/-- The assembled additive homomorphism is continuous as soon as every member of the family is. -/
theorem continuous_addLift [TopologicalSpace A]
    (hcont : ∀ n : ℕ+, Continuous (f n : A → ZMod n)) : Continuous (addLift f hf) :=
  continuous_iff_forall_continuous_toZMod.mpr fun n ↦ by
    simpa only [toZMod_addLift] using hcont n

/-- Assembling the projections themselves gives the identity of `ℤ̂`. -/
theorem addLift_toZMod :
    addLift (fun n ↦ (toZMod n : Additive zHat.{u} →+ ZMod n))
      (fun _ _ h ↦ congrArg RingHom.toAddMonoidHom (castHom_comp_toZMod h)) =
        AddMonoidHom.id (Additive zHat.{u}) :=
  (addLift_unique _ _ _ fun _ ↦ AddMonoidHom.comp_id _).symm

end AddLift

section RingLift

variable {R : Type v} [NonAssocSemiring R] (f : ∀ n : ℕ+, R →+* ZMod n)
  (hf : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), (ZMod.castHom h (ZMod m)).comp (f n) = f m)

/-- **The universal property of `ℤ̂` as an inverse limit.** A family of ring homomorphisms
`f n : R →+* ZMod n`, compatible along the reduction maps, assembles into the ring homomorphism
`R →+* Additive zHat` whose reduction modulo `n` is `f n` (`zHat.toZMod_ringLift`); it is the
only one (`zHat.ringLift_unique`). Its underlying additive homomorphism is the additive lift
`zHat.addLift` of the same family (`zHat.coe_addMonoidHom_ringLift`). -/
noncomputable def ringLift : R →+* Additive zHat.{u} :=
  { addLift (fun n ↦ (f n : R →+ ZMod n))
      (fun m n h ↦ congrArg RingHom.toAddMonoidHom (hf m n h)) with
    -- The multiplicative axioms are checked level by level, through `ext_of_toZMod`.
    map_one' := ext_of_toZMod fun n ↦ by
      rw [AddMonoidHom.toFun_eq_coe, toZMod_addLift, AddMonoidHom.coe_ofClass, map_one, map_one]
    map_mul' r s := ext_of_toZMod fun n ↦ by
      simp only [AddMonoidHom.toFun_eq_coe, map_mul, toZMod_addLift, AddMonoidHom.coe_ofClass] }

/-- The reduction modulo `n` of the assembled ring homomorphism is the `n`-th member of the
family. -/
@[simp]
theorem toZMod_ringLift (n : ℕ+) (r : R) : toZMod n (ringLift f hf r) = f n r :=
  toZMod_addLift (fun n ↦ (f n : R →+ ZMod n))
    (fun m n h ↦ congrArg RingHom.toAddMonoidHom (hf m n h)) n r

/-- The ring homomorphism assembled from a compatible family is, as an additive homomorphism, the
additive lift of the same family. -/
theorem coe_addMonoidHom_ringLift :
    (ringLift f hf : R →+ Additive zHat.{u}) =
      addLift (fun n ↦ (f n : R →+ ZMod n))
        (fun m n h ↦ congrArg RingHom.toAddMonoidHom (hf m n h)) :=
  addLift_unique _ _ _ fun n ↦ AddMonoidHom.ext (toZMod_ringLift f hf n)

/-- The reduction modulo `n` of the assembled ring homomorphism is the `n`-th member of the
family, as an equality of ring homomorphisms. -/
theorem toZMod_comp_ringLift (n : ℕ+) : (toZMod n).comp (ringLift f hf) = f n :=
  RingHom.ext (toZMod_ringLift f hf n)

/-- A ring homomorphism into `ℤ̂` whose reductions are the members of the family is the
assembled ring homomorphism. -/
theorem ringLift_unique (g : R →+* Additive zHat.{u}) (hg : ∀ n, (toZMod n).comp g = f n) :
    g = ringLift f hf :=
  RingHom.ext fun r ↦ ext_of_toZMod fun n ↦ by
    rw [toZMod_ringLift, ← hg n, RingHom.comp_apply]

/-- **Naturality of the universal property in `R`.** Precomposing the assembled ring
homomorphism with `g : S →+* R` assembles the precomposed family. -/
theorem ringLift_comp {S : Type*} [NonAssocSemiring S] (g : S →+* R) :
    (ringLift f hf).comp g =
      ringLift (fun n ↦ (f n).comp g) fun m n h ↦ by rw [← RingHom.comp_assoc, hf m n h] := by
  refine ringLift_unique _ _ _ fun n ↦ ?_
  rw [← RingHom.comp_assoc, toZMod_comp_ringLift]

/-- The assembled ring homomorphism is continuous as soon as every member of the family is. -/
theorem continuous_ringLift [TopologicalSpace R] (hcont : ∀ n : ℕ+, Continuous (f n : R → ZMod n)) :
    Continuous (ringLift f hf) :=
  continuous_iff_forall_continuous_toZMod.mpr fun n ↦ by
    simpa only [toZMod_ringLift] using hcont n

/-- Assembling the projections themselves gives the identity of `ℤ̂`. -/
theorem ringLift_toZMod :
    ringLift (fun n ↦ (toZMod n : Additive zHat.{u} →+* ZMod n))
      (fun _ _ h ↦ castHom_comp_toZMod h) = RingHom.id (Additive zHat.{u}) :=
  (ringLift_unique _ _ _ fun n ↦ RingHom.comp_id (toZMod n)).symm

end RingLift

end zHat

end TauCeti
