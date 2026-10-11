/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Invariant rings and localization

Let a group `G` act on a commutative ring `A` by ring automorphisms, and write `Aᴳ` for the
invariant subring `FixedPoints.subring A G`. This file compares invariants with localization.

For an invariant element `r`, the action extends to the localization `A[1/r]`
(`Localization.Away (r : A)`), compatibly with `A → A[1/r]`. When `G` is finite, taking invariants
commutes with this localization: `A[1/r]ᴳ` is the localization of `Aᴳ` away from `r`. A fraction
`a / rⁿ` fixed by every `g` satisfies `rᵐ (g • a - a) = 0` for some `m`, which can be chosen
independently of `g` because `G` is finite, and then `a / rⁿ = rᵐ a / rⁿ⁺ᵐ` with `rᵐ a`
invariant.

Also for finite `G`, the local homomorphism `(Aᴳ)_P → A_Q` induced by `Aᴳ ⊆ A` at a prime `Q` of
`A` lying over a prime `P` of `Aᴳ` is injective. If an invariant `a` is killed by some `t ∉ Q`,
prime avoidance applied to the annihilator of `a`, which is `G`-stable, and the finitely many
primes `g⁻¹ • Q` gives such a `t` outside every `g⁻¹ • Q`; then the invariant `∏ g, g • t` lies
outside `P` and kills `a`.

These are the two local facts behind the categorical universal property of the affine invariant
quotient `Spec A ⟶ Spec Aᴳ` for arbitrary target schemes.

## Main definitions

* `TauCeti.FixedPoints.awayRingAut r`: the action of `G` on `A[1/r]` for an invariant `r`, which
  provides the instance `MulSemiringAction G (Localization.Away (r : A))`.
* The instance `Algebra (FixedPoints.subring A G) (FixedPoints.subring (Localization.Away (r : A))
  G)` given by `A → A[1/r]`.

## Main results

* `TauCeti.FixedPoints.smul_algebraMap_away`: `A → A[1/r]` is `G`-equivariant.
* `TauCeti.FixedPoints.isLocalization_away`: for finite `G`, `A[1/r]ᴳ` is the localization of
  `Aᴳ` away from `r`.
* `TauCeti.FixedPoints.localRingHom_injective`: for finite `G`, `(Aᴳ)_P → A_Q` is injective.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

namespace TauCeti.FixedPoints

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A]

section Away

variable (r : FixedPoints.subring A G)

/-- An element of `G` maps the powers of an invariant element to themselves. -/
private theorem map_powers_toRingEquiv (g : G) :
    (Submonoid.powers (r : A)).map (MulSemiringAction.toRingEquiv G A g).toMonoidHom =
      Submonoid.powers (r : A) := by
  rw [Submonoid.map_powers]
  congr 1
  exact r.2 g

/-- The action of `G` on the localization `A[1/r]` at an invariant element `r`, induced by its
action on `A`. -/
noncomputable def awayRingAut : G →* RingAut (Localization.Away (r : A)) where
  toFun g := IsLocalization.ringEquivOfRingEquiv _ _ (MulSemiringAction.toRingEquiv G A g)
    (map_powers_toRingEquiv r g)
  map_one' := RingEquiv.toRingHom_injective <|
    IsLocalization.ringHom_ext (Submonoid.powers (r : A)) <| RingHom.ext fun a ↦ by simp
  map_mul' g h := RingEquiv.toRingHom_injective <|
    IsLocalization.ringHom_ext (Submonoid.powers (r : A)) <| RingHom.ext fun a ↦ by
      simp

/-- The action of `G` on `A[1/r]` given by `awayRingAut`. -/
noncomputable instance : MulSemiringAction G (Localization.Away (r : A)) :=
  MulSemiringAction.compHom _ (awayRingAut r)

/-- The action of `G` on `A[1/r]` extends the action on `A`. -/
@[simp]
theorem smul_algebraMap_away (g : G) (a : A) :
    g • algebraMap A (Localization.Away (r : A)) a =
      algebraMap A (Localization.Away (r : A)) (g • a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_powers_toRingEquiv r g) a

/-- The localization map `A → A[1/r]` sends invariants to invariants. -/
theorem algebraMap_mem_fixedPoints (a : FixedPoints.subring A G) :
    algebraMap A (Localization.Away (r : A)) a ∈
      FixedPoints.subring (Localization.Away (r : A)) G := fun g ↦ by
  rw [smul_algebraMap_away, a.2 g]

/-- The algebra structure of `A[1/r]ᴳ` over `Aᴳ` given by the localization map `A → A[1/r]`. -/
noncomputable instance :
    Algebra (FixedPoints.subring A G) (FixedPoints.subring (Localization.Away (r : A)) G) :=
  (((algebraMap A (Localization.Away (r : A))).comp (FixedPoints.subring A G).subtype).codRestrict
    _ (algebraMap_mem_fixedPoints r)).toAlgebra

/-- The algebra map `Aᴳ → A[1/r]ᴳ` is the localization map `A → A[1/r]`. -/
@[simp]
theorem coe_algebraMap_away (a : FixedPoints.subring A G) :
    (algebraMap (FixedPoints.subring A G) (FixedPoints.subring (Localization.Away (r : A)) G) a :
      Localization.Away (r : A)) = algebraMap A (Localization.Away (r : A)) a :=
  rfl

/-- **Invariants commute with localization at an invariant element.** For a finite group `G`,
the invariants of `A[1/r]` are the localization of the invariants `Aᴳ` away from `r`. -/
instance isLocalization_away [Finite G] :
    IsLocalization.Away r (FixedPoints.subring (Localization.Away (r : A)) G) := by
  have hinj : Function.Injective
      ((↑) : FixedPoints.subring (Localization.Away (r : A)) G → Localization.Away (r : A)) :=
    Subtype.val_injective
  refine (_root_.isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `r` is a unit of `A[1/r]` whose inverse is again invariant.
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    have hu : IsUnit (algebraMap A (Localization.Away (r : A)) r) :=
      IsLocalization.Away.algebraMap_isUnit (r : A)
    have hg (g : G) : g • (hu.unit : Localization.Away (r : A)) = hu.unit := by
      simp only [IsUnit.unit_spec, smul_algebraMap_away, r.2 g]
    refine isUnit_iff_exists_inv.mpr
      ⟨⟨(hu.unit⁻¹ : (Localization.Away (r : A))ˣ), fun g ↦ ?_⟩, hinj ?_⟩
    · refine Units.eq_inv_of_mul_eq_one_left ?_
      rw [← hg g, ← smul_mul', Units.mul_inv, smul_one]
    · simp only [Subring.coe_mul, coe_algebraMap_away, Subring.coe_one]
      exact hu.mul_val_inv
  · -- A fixed fraction `a / rⁿ` equals `rᴹ a / rⁿ⁺ᴹ` with `rᴹ a` invariant.
    rintro ⟨z, hz⟩
    obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (r : A)) z
    simp only at ha
    have hfix (g : G) : ∃ m : ℕ, (r : A) ^ m * a = (r : A) ^ m * (g • a) := by
      have h := congrArg (g • ·) ha
      simp only [smul_mul', hz g, smul_algebraMap_away, smul_pow', r.2 g] at h
      obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (r : A))
        (ha.symm.trans h)
      exact ⟨m, hm⟩
    choose m hm using hfix
    have := Fintype.ofFinite G
    set M := ∑ g, m g
    have hM (g : G) : (r : A) ^ M * a = (r : A) ^ M * (g • a) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ g) : m g ≤ M)
      rw [show M = m g + k from hk, pow_add, mul_comm ((r : A) ^ m g), mul_assoc, mul_assoc, hm g]
    have hb : (r : A) ^ M * a ∈ FixedPoints.subring A G := fun g ↦ by
      rw [smul_mul', smul_pow', r.2 g, ← hM g]
    refine ⟨(⟨_, hb⟩, ⟨r ^ (n + M), n + M, rfl⟩), hinj ?_⟩
    simp only [Subring.coe_mul, coe_algebraMap_away, SubmonoidClass.coe_pow, pow_add, map_mul,
      map_pow]
    rw [← mul_assoc, ← map_pow, ha, ← map_pow, ← map_mul, mul_comm]
    exact map_mul _ _ _
  · intro x y hxy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (r : A))
      (congrArg Subtype.val hxy)
    exact ⟨⟨r ^ m, m, rfl⟩, Subtype.ext (by simpa using hm)⟩

end Away

section LocalRingHom

variable [Finite G]

/-- If an invariant `x` is killed by an element outside a prime `Q`, it is killed by an invariant
element outside `Q`. This is prime avoidance for the `G`-stable annihilator of `x` and the
finitely many primes `g⁻¹ • Q`. -/
theorem exists_mul_eq_zero_of_mul_eq_zero (Q : Ideal A) [Q.IsPrime] (x : FixedPoints.subring A G)
    {t : A} (htQ : t ∉ Q) (htx : t * x = 0) :
    ∃ s ∈ FixedPoints.subring A G, s ∉ Q ∧ s * x = 0 := by
  have := Fintype.ofFinite G
  set I : Ideal A := (Ideal.span {(x : A)}).annihilator
  have hI (u : A) : u ∈ I ↔ u * x = 0 := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  obtain ⟨u, huI, hu⟩ : ∃ u ∈ I, ∀ g : G, g • u ∉ Q := by
    by_contra! h
    have hsub : (I : Set A) ⊆ ⋃ g ∈ (Finset.univ : Finset G),
        (Q.comap (MulSemiringAction.toRingHom G A g) : Set A) := fun u hu ↦ by
      obtain ⟨g, hg⟩ := h u hu
      exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ g)) hg
    obtain ⟨g, -, hg⟩ := (Ideal.subset_union_prime 1 1
      (fun g _ _ _ ↦ Ideal.comap_isPrime _ Q)).mp hsub
    -- The annihilator of `x` is `G`-stable, so it contains `g⁻¹ • t`, and then `t ∈ Q`.
    have hmem : g⁻¹ • t ∈ I := by
      rw [hI, ← x.2 g⁻¹, ← smul_mul', htx, smul_zero]
    exact htQ (by simpa using hg hmem)
  refine ⟨∏ g : G, g • u, fun h ↦ ?_, ?_, ?_⟩
  · rw [Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g ↦ (mul_smul h g u).symm
  · exact fun hmem ↦ by
      obtain ⟨g, -, hg⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hmem
      exact hu g hg
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun g : G ↦ g • u) (Finset.mem_univ 1)
    rw [hc, one_smul, mul_comm u, mul_assoc, (hI u).mp huI, mul_zero]

/-- **Invariants inject into stalks.** For a finite group `G`, a prime `Q` of `A` and the prime
`P` of `Aᴳ` below it, the induced homomorphism of local rings `(Aᴳ)_P → A_Q` is injective. -/
theorem localRingHom_injective (P : Ideal (FixedPoints.subring A G)) (Q : Ideal A) [P.IsPrime]
    [Q.IsPrime] (hPQ : P = Q.comap (algebraMap (FixedPoints.subring A G) A)) :
    Function.Injective
      (Localization.localRingHom P Q (algebraMap (FixedPoints.subring A G) A) hPQ) := by
  refine IsLocalization.injective_of_map_algebraMap_zero (M := P.primeCompl) _ _ fun x hx ↦ ?_
  rw [Localization.localRingHom_to_map,
    IsLocalization.map_eq_zero_iff Q.primeCompl] at hx
  obtain ⟨⟨t, htQ⟩, htx⟩ := hx
  obtain ⟨s, hs, hsQ, hsx⟩ := exists_mul_eq_zero_of_mul_eq_zero Q x htQ htx
  refine (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mpr
    ⟨⟨⟨s, hs⟩, fun h ↦ hsQ (by rwa [hPQ] at h)⟩, Subtype.ext hsx⟩

end LocalRingHom

end TauCeti.FixedPoints
