/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The p-adic integers as an inverse limit

The ring of `p`-adic integers is the inverse limit of the finite rings `ZMod (p ^ n)`. This
file gives that inverse limit a concrete carrier: a point is a family whose finer residues
reduce to its coarser residues. Mathlib's universal maps `PadicInt.toZModPow` and
`PadicInt.lift` identify this ring with `ℤ_[p]`.

The topology on the inverse limit is the subspace topology from the product of the discrete
finite rings; the compatibility conditions are closed, so the inverse limit is compact for
every nonzero modulus. The algebraic equivalence is a homeomorphism because its forward map is
continuous and `ℤ_[p]` is compact.

## Main definitions

* `PadicInt.inverseLimit`: the ring of compatible families in `∏ n, ZMod (p ^ n)`.
* `PadicInt.inverseLimit.lift`: the universal map into the inverse limit determined by a
  compatible family of ring homomorphisms.
* `PadicInt.toInverseLimit`: the compatible family of residues of a `p`-adic integer.
* `PadicInt.inverseLimitRingEquiv`: the ring equivalence from `ℤ_[p]` to the inverse limit.
* `PadicInt.inverseLimitHomeomorph`: the same equivalence as a homeomorphism.
* `PadicInt.inverseLimitContinuousMulEquiv`: the corresponding topological isomorphism of
  additive groups, written multiplicatively.

## References

* J.-P. Serre, *Local Fields*, Chapter II, Section 2.
-/

public section

namespace PadicInt

variable (p : ℕ)

/-- The inverse limit of the rings `ZMod (p ^ n)`: compatible residue families, with the
subspace topology inherited from their product. -/
def inverseLimit : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := {x | ∀ ⦃m n : ℕ⦄ (h : m ≤ n),
    (ZMod.cast (x n) : ZMod (p ^ m)) = x m}
  zero_mem' _ _ _ := by simp
  one_mem' m n h := calc
    (ZMod.cast ((1 : ∀ k, ZMod (p ^ k)) n) : ZMod (p ^ m)) =
        ZMod.cast (1 : ZMod (p ^ n)) := rfl
    _ = 1 := ZMod.cast_one (pow_dvd_pow p h)
    _ = (1 : ∀ k, ZMod (p ^ k)) m := rfl
  add_mem' {x y} hx hy m n h := by
    calc
      (ZMod.cast ((x + y) n) : ZMod (p ^ m)) = ZMod.cast (x n + y n) := rfl
      _ = ZMod.cast (x n) + ZMod.cast (y n) := ZMod.cast_add (pow_dvd_pow p h) _ _
      _ = x m + y m := by rw [hx h, hy h]
  mul_mem' {x y} hx hy m n h := by
    calc
      (ZMod.cast ((x * y) n) : ZMod (p ^ m)) = ZMod.cast (x n * y n) := rfl
      _ = ZMod.cast (x n) * ZMod.cast (y n) := ZMod.cast_mul (pow_dvd_pow p h) _ _
      _ = x m * y m := by rw [hx h, hy h]
  neg_mem' {x} hx m n h := by
    calc
      (ZMod.cast ((-x) n) : ZMod (p ^ m)) = ZMod.cast (-x n) := rfl
      _ = -ZMod.cast (x n) := ZMod.cast_neg (pow_dvd_pow p h) _
      _ = -x m := by rw [hx h]

variable {p} in
/-- Membership in `PadicInt.inverseLimit`: a family belongs to the inverse limit exactly when
each of its finer residues reduces to the coarser ones. Use `.mpr` to build an element of the
inverse limit from a compatibility proof. -/
theorem mem_inverseLimit_iff {x : ∀ n : ℕ, ZMod (p ^ n)} :
    x ∈ inverseLimit p ↔
      ∀ ⦃m n : ℕ⦄, m ≤ n → (ZMod.cast (x n) : ZMod (p ^ m)) = x m :=
  Iff.rfl

namespace inverseLimit

/-- The projection from the inverse limit to `ZMod (p ^ n)`. -/
def proj (n : ℕ) : inverseLimit p →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n : ℕ ↦ ZMod (p ^ n)) n).comp (inverseLimit p).subtype

@[simp]
theorem proj_apply (n : ℕ) (x : inverseLimit p) : proj p n x = x.1 n :=
  (rfl)

/-- The projections from the inverse limit form a compatible family. -/
@[simp]
theorem cast_proj (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (proj p n) = proj p m := by
  ext x
  exact x.2 h

variable {R : Type*} [NonAssocSemiring R] (f : ∀ n : ℕ, R →+* ZMod (p ^ n))
  (hf : ∀ (m n : ℕ) (h : m ≤ n),
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (f n) = f m)

/-- The universal property of the inverse limit: a family of ring homomorphisms
`f n : R →+* ZMod (p ^ n)` compatible with the reduction maps assembles into a single ring
homomorphism to `PadicInt.inverseLimit p`. -/
def lift : R →+* inverseLimit p :=
  (RingHom.pi f).codRestrict (inverseLimit p) fun x ↦
    mem_inverseLimit_iff.mpr fun m n h ↦ DFunLike.congr_fun (hf m n h) x

@[simp]
theorem lift_apply (x : R) (n : ℕ) : (lift p f hf x).1 n = f n x :=
  (rfl)

/-- `PadicInt.inverseLimit.lift` recovers the given family on each projection. -/
@[simp]
theorem proj_comp_lift (n : ℕ) : (proj p n).comp (lift p f hf) = f n :=
  (rfl)

/-- `PadicInt.inverseLimit.lift` is the only homomorphism recovering the given family on each
projection. -/
theorem lift_unique (g : R →+* inverseLimit p) (hg : ∀ n : ℕ, (proj p n).comp g = f n) :
    g = lift p f hf :=
  RingHom.ext fun x ↦ Subtype.ext (funext fun n ↦ DFunLike.congr_fun (hg n) x)

end inverseLimit

/-- The compatible families are cut out of the product of the discrete rings `ZMod (p ^ n)` by
closed conditions. -/
theorem isClosed_inverseLimit :
    IsClosed (inverseLimit p : Set (∀ n : ℕ, ZMod (p ^ n))) := by
  have hcarrier : (inverseLimit p : Set (∀ n : ℕ, ZMod (p ^ n))) =
      ⋂ m, ⋂ n, ⋂ _ : m ≤ n, {x | (ZMod.cast (x n) : ZMod (p ^ m)) = x m} := by
    ext x
    simp only [SetLike.mem_coe, mem_inverseLimit_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hcarrier]
  exact isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

/-- The inverse limit of the finite rings `ZMod (p ^ n)` is compact. -/
instance compactSpace_inverseLimit [NeZero p] : CompactSpace (inverseLimit p) :=
  isCompact_iff_compactSpace.mp (isClosed_inverseLimit p).isCompact

variable [Fact p.Prime]

/-- The residue family of a `p`-adic integer, regarded as a homomorphism to the inverse
limit. -/
noncomputable def toInverseLimit : ℤ_[p] →+* inverseLimit p where
  toFun x := ⟨fun n ↦ toZModPow n x, fun {_ _} h ↦ cast_toZModPow _ _ h x⟩
  map_one' := Subtype.ext (funext fun n ↦ map_one (toZModPow n))
  map_mul' x y := Subtype.ext (funext fun n ↦ map_mul (toZModPow n) x y)
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (toZModPow n))
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (toZModPow n) x y)

@[simp]
theorem inverseLimit_proj_toInverseLimit (n : ℕ) :
    (inverseLimit.proj p n).comp (toInverseLimit p) = toZModPow n := by
  rfl

@[simp]
theorem toInverseLimit_apply (x : ℤ_[p]) (n : ℕ) :
    (toInverseLimit p x).1 n = toZModPow n x :=
  (rfl)

/-- A compatible residue family determines a `p`-adic integer by Mathlib's inverse-limit
universal property. -/
noncomputable def fromInverseLimit : inverseLimit p →+* ℤ_[p] :=
  lift (inverseLimit.cast_proj p)

@[simp]
theorem toZModPow_fromInverseLimit (n : ℕ) :
    (toZModPow n).comp (fromInverseLimit p) = inverseLimit.proj p n :=
  lift_spec (inverseLimit.cast_proj p) n

/-- The ring of `p`-adic integers is the inverse limit of the rings `ZMod (p ^ n)`. -/
noncomputable def inverseLimitRingEquiv : ℤ_[p] ≃+* inverseLimit p where
  toFun := toInverseLimit p
  invFun := fromInverseLimit p
  left_inv x := by
    apply ext_of_toZModPow.mp
    intro n
    have h := DFunLike.congr_fun (toZModPow_fromInverseLimit p n) (toInverseLimit p x)
    exact h.trans rfl
  right_inv x := by
    apply Subtype.ext
    funext n
    exact DFunLike.congr_fun (toZModPow_fromInverseLimit p n) x
  map_mul' := map_mul (toInverseLimit p)
  map_add' := map_add (toInverseLimit p)

@[simp]
theorem inverseLimitRingEquiv_apply (x : ℤ_[p]) :
    inverseLimitRingEquiv p x = toInverseLimit p x :=
  (rfl)

@[simp]
theorem inverseLimitRingEquiv_symm_apply (x : inverseLimit p) :
    (inverseLimitRingEquiv p).symm x = fromInverseLimit p x :=
  (rfl)

/-- Taking all residues modulo `p ^ n` is continuous into their inverse limit. -/
theorem continuous_toInverseLimit : Continuous (toInverseLimit p) := by
  exact (continuous_pi fun n ↦ continuous_toZModPow n).subtype_mk _

/-- The ring equivalence from `ℤ_[p]` to its inverse-limit presentation is continuous. -/
theorem continuous_inverseLimitRingEquiv : Continuous (inverseLimitRingEquiv p) :=
  (continuous_toInverseLimit p).congr fun x ↦ (inverseLimitRingEquiv_apply p x).symm

/-- The ring equivalence from `ℤ_[p]` to its inverse-limit presentation is a homeomorphism. -/
noncomputable def inverseLimitHomeomorph : ℤ_[p] ≃ₜ inverseLimit p :=
  (continuous_inverseLimitRingEquiv p).homeoOfEquivCompactToT2

/-- The underlying map of `PadicInt.inverseLimitHomeomorph` is the ring equivalence taking a
`p`-adic integer to all of its residues. -/
@[simp]
theorem inverseLimitHomeomorph_toEquiv :
    (inverseLimitHomeomorph p : ℤ_[p] ≃ inverseLimit p) = inverseLimitRingEquiv p :=
  (rfl)

/-- The additive group of `ℤ_[p]` is topologically isomorphic to the additive group of its
inverse-limit presentation. -/
noncomputable def inverseLimitContinuousMulEquiv :
    Multiplicative ℤ_[p] ≃ₜ* Multiplicative (inverseLimit p) where
  toMulEquiv := AddEquiv.toMultiplicative (inverseLimitRingEquiv p).toAddEquiv
  continuous_toFun := by
    -- The multiplicative type tag has the same topology and underlying function.
    change Continuous (inverseLimitRingEquiv p)
    exact continuous_inverseLimitRingEquiv p
  continuous_invFun := by
    -- The multiplicative type tag has the same topology and underlying inverse function.
    change Continuous (inverseLimitRingEquiv p).symm
    exact (continuous_inverseLimitRingEquiv p).continuous_symm_of_equiv_compact_to_t2

@[simp]
theorem inverseLimitContinuousMulEquiv_apply (x : ℤ_[p]) :
    inverseLimitContinuousMulEquiv p (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (toInverseLimit p x) :=
  (rfl)

@[simp]
theorem inverseLimitContinuousMulEquiv_symm_apply (x : inverseLimit p) :
    (inverseLimitContinuousMulEquiv p).symm (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (fromInverseLimit p x) :=
  (rfl)

end PadicInt
