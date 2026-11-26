/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.IntegralDomain
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Reading primitive Dirichlet characters on Frobenius cosets

For a homomorphism `f` out of the units modulo `N`, the cyclotomic inertia at a prime `p` is the
image under `f` of the kernel of reduction to the prime-to-`p` part of `N`. The Frobenius coset for
`p ^ i` is the image under `f` of the fiber over `p ^ i` under that reduction. For a positive power
`p ^ i` and a character with values in a field of characteristic zero, the average of the
character on this coset is the value at `p ^ i` of the primitive character inducing its pullback
to level `N`.
In particular, at a ramified prime the primitive value is not in general the value of the
character at level `N` (which vanishes at primes dividing `N`).

The inertia-mean statement is the cyclotomic character calculation in L. Alpöge's Lean
formalization of the Riemann hypothesis for Dirichlet L-functions,
`UpperTheory.Comparison₂.prim_read` in
`Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>). The proof here uses the conductor
criterion for factoring through a reduction of units and character orthogonality.
-/

public section

open scoped Pointwise

namespace MonoidHom

variable {N p i : ℕ} {G : Type*} [Group G]

/-- The image of cyclotomic inertia at `p` under a homomorphism from the units modulo `N`.
The reduction defining it drops the entire `p`-primary part of `N`. -/
def cyclotomicInertia (f : (ZMod N)ˣ →* G) (p : ℕ) : Subgroup G :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker.map f

/-- Membership in the image of cyclotomic inertia is witnessed by a unit reducing to `1`. -/
@[simp] theorem mem_cyclotomicInertia_iff (f : (ZMod N)ˣ →* G) {g : G} :
    g ∈ f.cyclotomicInertia p ↔
      ∃ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.ordCompl_dvd N p) u = 1 ∧ f u = g := by
  simp [cyclotomicInertia, Subgroup.mem_map]

variable [NeZero N]

/-- The power `p ^ i` of the prime-to-`p` part of `N` lifts to the units modulo `N`. -/
private theorem exists_unitsMap_eq_pow (hp : p.Prime) (i : ℕ) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.ordCompl_dvd N p) u =
      ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N)) ^ i :=
  ZMod.unitsMap_surjective (Nat.ordCompl_dvd N p) _

/-- The image of the units modulo `N` that reduce to `p ^ i` modulo the prime-to-`p` part of `N`.
This is the arithmetic Frobenius coset when `f` is a cyclotomic Artin map. -/
noncomputable def frobeniusCoset (f : (ZMod N)ˣ →* G) (hp : p.Prime) (i : ℕ) : Finset G := by
  classical
  let v := ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N))
  exact (Finset.univ.filter fun u ↦ ZMod.unitsMap (Nat.ordCompl_dvd N p) u = v ^ i).image f

/-- The elements of a Frobenius coset are the images of the units with the prescribed reduction. -/
@[simp] theorem mem_frobeniusCoset_iff (f : (ZMod N)ˣ →* G) (hp : p.Prime) {g : G} :
    g ∈ f.frobeniusCoset hp i ↔ ∃ u : (ZMod N)ˣ,
      ZMod.unitsMap (Nat.ordCompl_dvd N p) u =
        ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N)) ^ i ∧ f u = g := by
  classical
  simp [frobeniusCoset]

/-- The Frobenius coset at a positive prime power, indexed by the natural number itself.
Off the positive prime powers it is empty. -/
noncomputable def primePowerFrobeniusCoset (f : (ZMod N)ˣ →* G) (n : ℕ) : Finset G := by
  classical
  exact if hn : IsPrimePow n then
    f.frobeniusCoset (Nat.minFac_prime hn.ne_one) (n.factorization n.minFac) else ∅

open scoped Classical in
/-- At an arbitrary index, use its least prime factor and its exponent if it is a prime power,
and return the empty finset otherwise. -/
theorem primePowerFrobeniusCoset_def (f : (ZMod N)ˣ →* G) (n : ℕ) :
    f.primePowerFrobeniusCoset n = if hn : IsPrimePow n then
      f.frobeniusCoset (Nat.minFac_prime hn.ne_one) (n.factorization n.minFac) else ∅ :=
  (rfl)

/-- Indexing by a positive prime power recovers the coset at that prime and exponent. -/
@[simp] theorem primePowerFrobeniusCoset_pow (f : (ZMod N)ˣ →* G) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    f.primePowerFrobeniusCoset (p ^ k) = f.frobeniusCoset hp k := by
  have hexp : (p ^ k).factorization (p ^ k).minFac = k := by
    rw [hp.pow_minFac hk, Nat.factorization_pow_self hp]
  rw [primePowerFrobeniusCoset_def, dite_eq_left (hp.isPrimePow.pow hk), hexp]
  congr
  exact hp.pow_minFac hk

/-- There is no coset attached to a number that is not a positive prime power. -/
@[simp] theorem primePowerFrobeniusCoset_of_not_isPrimePow (f : (ZMod N)ˣ →* G) {n : ℕ}
    (hn : ¬ IsPrimePow n) : f.primePowerFrobeniusCoset n = ∅ := by
  simp [primePowerFrobeniusCoset_def, hn]

/-- Membership is witnessed by a prime and a positive exponent giving the index and its coset. -/
@[simp] theorem mem_primePowerFrobeniusCoset_iff (f : (ZMod N)ˣ →* G) {n : ℕ} {g : G} :
    g ∈ f.primePowerFrobeniusCoset n ↔
      ∃ (p k : ℕ) (hp : p.Prime), 0 < k ∧ p ^ k = n ∧ g ∈ f.frobeniusCoset hp k := by
  constructor
  · intro hg
    by_cases hn : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
      exact ⟨p, k, hp, hk, rfl, by simpa only [f.primePowerFrobeniusCoset_pow hp hk.ne'] using hg⟩
    · simp [f.primePowerFrobeniusCoset_of_not_isPrimePow hn] at hg
  · rintro ⟨p, k, hp, hk, rfl, hg⟩
    rwa [f.primePowerFrobeniusCoset_pow hp hk.ne']

/-- Any lift of `p ^ i` gives a representative of the Frobenius coset modulo inertia. -/
theorem coe_frobeniusCoset_eq_leftCoset (f : (ZMod N)ˣ →* G) (hp : p.Prime)
    {u : (ZMod N)ˣ} (hu : ZMod.unitsMap (Nat.ordCompl_dvd N p) u =
      ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N)) ^ i) :
    (f.frobeniusCoset hp i : Set G) = f u • (f.cyclotomicInertia p : Set G) := by
  ext g
  simp only [mem_frobeniusCoset_iff, ← hu, mem_leftCoset_iff,
    SetLike.mem_coe, mem_cyclotomicInertia_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨u⁻¹ * a, by simp [ha], by simp⟩
  · rintro ⟨a, ha, hfa⟩
    exact ⟨u * a, by simp [ha], by simp [hfa]⟩

/-- The Frobenius coset is nonempty, even when the prime divides the level. -/
theorem frobeniusCoset_nonempty (f : (ZMod N)ˣ →* G) (hp : p.Prime) (i : ℕ) :
    (f.frobeniusCoset hp i).Nonempty := by
  obtain ⟨u, hu⟩ := exists_unitsMap_eq_pow (N := N) hp i
  exact ⟨f u, (mem_frobeniusCoset_iff f hp).2 ⟨u, hu, rfl⟩⟩

/-- Every Frobenius coset has as many elements as the image of inertia. -/
theorem card_frobeniusCoset (f : (ZMod N)ˣ →* G) (hp : p.Prime) (i : ℕ) :
    (f.frobeniusCoset hp i).card = Nat.card (f.cyclotomicInertia p) := by
  obtain ⟨u, hu⟩ := exists_unitsMap_eq_pow (N := N) hp i
  calc
    _ = Nat.card (f.frobeniusCoset hp i : Set G) := by
      rw [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := by
      rw [f.coe_frobeniusCoset_eq_leftCoset hp hu]
      exact Nat.card_congr (Subgroup.leftCosetEquivSubgroup (f u))

/-- The sum of a character over a Frobenius coset is its value at a lift of `p ^ i` times its sum
over the image of inertia. -/
theorem sum_frobeniusCoset_eq_mul_sum_cyclotomicInertia {R : Type*} [Semiring R]
    (f : (ZMod N)ˣ →* G) (χ : G →* Rˣ) (hp : p.Prime) [Fintype (f.cyclotomicInertia p)]
    {u : (ZMod N)ˣ} (hu : ZMod.unitsMap (Nat.ordCompl_dvd N p) u =
      ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N)) ^ i) :
    ∑ g ∈ f.frobeniusCoset hp i, (χ g : R) =
      (χ (f u) : R) * ∑ a : f.cyclotomicInertia p, (χ a : R) := by
  let e : (f.frobeniusCoset hp i) ≃ f.cyclotomicInertia p :=
    (Equiv.subtypeEquivRight fun g ↦
      Set.ext_iff.mp (f.coe_frobeniusCoset_eq_leftCoset hp hu) g).trans
      (Subgroup.leftCosetEquivSubgroup (f u))
  rw [← Finset.sum_attach, Finset.attach_eq_univ, Finset.mul_sum]
  refine Fintype.sum_equiv e _ _ fun g ↦ ?_
  -- The equivalence transports membership and then translates by `(f u)⁻¹`.
  have hg : (e g : G) = (f u)⁻¹ * (g : G) := rfl
  rw [hg, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]

/-- The primitive conductor of the pullback is prime to `p` exactly when the character is
trivial on cyclotomic inertia. -/
theorem not_dvd_conductor_ofUnitHom_comp_iff {R : Type*} [CommMonoidWithZero R]
    (f : (ZMod N)ˣ →* G) (χ : G →* Rˣ) (hp : p.Prime) :
    ¬ p ∣ DirichletCharacter.conductor (MulChar.ofUnitHom (χ.comp f)) ↔
      f.cyclotomicInertia p ≤ χ.ker := by
  let ψ : DirichletCharacter R N := MulChar.ofUnitHom (χ.comp f)
  have hd := Nat.ordCompl_dvd N p
  calc
    ¬ p ∣ ψ.conductor ↔ ψ.FactorsThrough (ordCompl[p] N) :=
      (DirichletCharacter.factorsThrough_iff_not_dvd_conductor hp
        (Nat.ordProj_mul_ordCompl_eq_self N p).symm (Nat.not_dvd_ordCompl hp (NeZero.ne N)) ψ).symm
    _ ↔ f.cyclotomicInertia p ≤ χ.ker := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, cyclotomicInertia,
        Subgroup.map_le_iff_le_comap]
      simp [ψ, MonoidHom.comap_ker, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq]

/-- If `χ` is trivial on cyclotomic inertia, the primitive character inducing the pullback of `χ`
takes at `p ^ i` the value of `χ` at the image of any lift of `p ^ i`. -/
theorem primitiveCharacter_apply_pow_eq_of_le_ker {R : Type*} [CommMonoidWithZero R]
    (f : (ZMod N)ˣ →* G) (χ : G →* Rˣ) (hp : p.Prime) (hχ : f.cyclotomicInertia p ≤ χ.ker)
    {u : (ZMod N)ˣ} (hu : ZMod.unitsMap (Nat.ordCompl_dvd N p) u =
      ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp (NeZero.ne N)) ^ i) :
    DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom (χ.comp f)) ((p ^ i : ℕ) : ZMod _) =
      (χ (f u) : R) := by
  let ψ : DirichletCharacter R N := MulChar.ofUnitHom (χ.comp f)
  have hd := Nat.ordCompl_dvd N p
  have hcd := Nat.dvd_ordCompl_of_dvd_not_dvd ψ.conductor_dvd_level
    ((f.not_dvd_conductor_ofUnitHom_comp_iff χ hp).2 hχ)
  let ψ₀ := ψ.primitiveCharacter.changeLevel hcd
  have hψ : ψ₀.changeLevel hd = ψ := by
    rw [← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
  calc
    _ = ψ₀ (p ^ i : ℕ) := (DirichletCharacter.changeLevel_natCast_of_coprime hcd _
          ((Nat.coprime_ordCompl hp (NeZero.ne N)).pow_left i)).symm
    _ = ψ₀ (ZMod.unitsMap hd u : ZMod (ordCompl[p] N)) := by simp [hu]
    _ = ψ₀.changeLevel hd (u : ZMod N) := by
      rw [ZMod.unitsMap_val]
      exact (ψ₀.changeLevel_eq_cast_of_dvd hd u).symm
    _ = ψ (u : ZMod N) := congrArg (fun η : DirichletCharacter R N ↦ η (u : ZMod N)) hψ
    _ = _ := MulChar.ofUnitHom_coe _ _

/-- The primitive character inducing the pullback of `χ`, evaluated at a positive power of `p`,
is the mean of `χ` over the Frobenius coset. Inertia either acts trivially, in which case all terms
in the mean are the same, or acts nontrivially, in which case the mean is zero. -/
theorem primitiveCharacter_apply_pow_eq_frobeniusCoset_mean {R : Type*} [Field R] [CharZero R]
    (f : (ZMod N)ˣ →* G) (χ : G →* Rˣ) (hp : p.Prime) (hi : i ≠ 0) :
    DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom (χ.comp f)) ((p ^ i : ℕ) : ZMod _) =
      (∑ g ∈ f.frobeniusCoset hp i, (χ g : R)) / (f.frobeniusCoset hp i).card := by
  classical
  let ψ : DirichletCharacter R N := MulChar.ofUnitHom (χ.comp f)
  let I := f.cyclotomicInertia p
  obtain ⟨u, hu⟩ := exists_unitsMap_eq_pow (N := N) hp i
  have : Finite I := ((Set.toFinite _).image f).to_subtype
  let : Fintype I := Fintype.ofFinite I
  have hcard : ((f.frobeniusCoset hp i).card : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (f.frobeniusCoset_nonempty hp i))
  rw [f.sum_frobeniusCoset_eq_mul_sum_cyclotomicInertia χ hp hu]
  by_cases hχ : I ≤ χ.ker
  · have hones : ∀ a : I, (χ a : R) = 1 := fun a ↦
      congrArg Units.val (MonoidHom.mem_ker.mp (hχ a.property))
    rw [f.primitiveCharacter_apply_pow_eq_of_le_ker χ hp hχ hu,
      Finset.sum_congr rfl (fun a _ ↦ hones a), Finset.sum_const, nsmul_one, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← f.card_frobeniusCoset hp i, mul_div_cancel_right₀ _ hcard]
  · have hpcond : p ∣ ψ.conductor := by
      by_contra h
      exact hχ ((f.not_dvd_conductor_ofUnitHom_comp_iff χ hp).1 h)
    have hpzero := ψ.primitiveCharacter_apply_prime_eq_zero hp hpcond
    have hne : ((Units.coeHom R).comp (χ.comp I.subtype)) ≠ 1 := by
      intro h
      exact hχ fun a ha ↦ Units.val_eq_one.mp (DFunLike.congr_fun h (⟨a, ha⟩ : I))
    have hzero : (∑ a : I, (χ a : R)) = 0 := sum_hom_units_eq_zero _ hne
    rw [hzero, mul_zero, zero_div, Nat.cast_pow, map_pow, hpzero, zero_pow hi]

end MonoidHom
