/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.Algebra.CharP.LocalRing
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.Algebra.MonoidAlgebra.Exactness
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.PGroupInvariants

/-!
# Monoid algebras over a local ring

For a finite monoid `G` (for instance a finite group) and a local ring `R` with residue field `k`,
the free module `R[G]^ι` of finite rank is a finitely generated `R`-module, so Nakayama's lemma
over `R` detects surjectivity of its endomorphisms after reduction to `k[G]^ι`.
The Orzech property then upgrades surjectivity to bijectivity.

For a commutative `p`-group `Q` and a local ring `R` in which `p` is not a unit, the group
algebra `R[Q]` is itself local, and the augmentation `R[Q] → R` is a local homomorphism: an element
of `R[Q]` is a unit as soon as its augmentation is. Indeed every maximal ideal of `R[Q]` lies over
the maximal ideal of `R`, because `R[Q]` is integral over `R`, so its residue field has
characteristic `p`; there `q - 1` is nilpotent, as `(q - 1) ^ (p ^ k) = q ^ (p ^ k) - 1 = 0`, and
therefore zero. So every maximal ideal contains the augmentation ideal.

For a finite `p`-group `G`, not necessarily commutative, the same holds: an element of `R[G]` is
a unit as soon as its augmentation is, so `R[G]` is local. Over the residue field `k` of `R`, which
has characteristic `p`, every simple `k[G]`-module has a nonzero vector fixed by `G`, so a proper
left ideal of `k[G]` lies in the augmentation ideal; Nakayama's lemma over `R` lifts invertibility
from `k[G]` to `R[G]`. Conversely, if `R[G]` is local for a finite group `G`, then `G` is a
`p`-group: an element of prime order `q ≠ p` would give, `q` being a unit of `R`, the average of
the cyclic subgroup it generates, which is neither a unit nor one minus a unit.

## Main results

* `TauCeti.MonoidAlgebra.bijective_of_forall_exists_mapRingHom_residue_eq`: an `R[G]`-linear
  endomorphism of `R[G]^ι` that is onto modulo the maximal ideal is bijective.
* `TauCeti.MonoidAlgebra.isLocalHom_lift_one_of_isPGroup`: for a commutative `p`-group `Q`
  the augmentation `R[Q] → R` is a local homomorphism.
* `TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup`: `R[Q]` is a local ring.
* `TauCeti.MonoidAlgebra.isLocalHom_augmentation_of_isPGroup`: for a finite `p`-group `G`, not
  necessarily commutative, the augmentation `R[G] → R` is a local homomorphism.
* `TauCeti.MonoidAlgebra.isLocalRing_iff_isPGroup`: for a finite group `G`, the group algebra
  `R[G]` is local if and only if `G` is a `p`-group.
-/

public section

open MonoidAlgebra IsLocalRing

namespace TauCeti.MonoidAlgebra

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Monoid G] [Finite G] {ι : Type*}
  [Finite ι]

/-- **Nakayama's lemma for `R[G]^ι`.** An `R[G]`-linear endomorphism of `R[G]^ι` that is onto
modulo the maximal ideal is bijective. -/
theorem bijective_of_forall_exists_mapRingHom_residue_eq
    (θ : (ι → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] (ι → MonoidAlgebra R G))
    (h : ∀ y : ι → MonoidAlgebra R G, ∃ x, ∀ i,
      mapRingHom G (residue R) (θ x i) = mapRingHom G (residue R) (y i)) :
    Function.Bijective θ := by
  classical
  have := Fintype.ofFinite ι
  -- `R[G]^ι` is a finitely generated `R`-module and `θ` is onto modulo `𝔪 • R[G]^ι`.
  have hle : (⊤ : Submodule R (ι → MonoidAlgebra R G)) ≤
      LinearMap.range (θ.restrictScalars R) ⊔ maximalIdeal R • ⊤ := by
    intro y _
    obtain ⟨x, hx⟩ := h y
    refine Submodule.mem_sup.mpr ⟨θ x, ⟨x, rfl⟩, y - θ x, ?_, add_sub_cancel _ _⟩
    rw [← Finset.univ_sum_single (y - θ x)]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single R (fun _ ↦ MonoidAlgebra R G) i) ?_
    rw [← ker_residue, ← mapRingHom_eq_zero_iff, Pi.sub_apply, map_sub, hx, sub_self]
  have hsurj : Function.Surjective θ := LinearMap.range_eq_top.mp (top_unique
    (Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top (ringJacobson_eq_maximalIdeal R).ge
      hle))
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism (θ.restrictScalars R) hsurj, hsurj⟩

section PGroup

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {Q : Type*} [CommGroup Q]

/-- Every maximal ideal of `R[Q]` contains `q - 1` for each `q` in the `p`-group `Q`. -/
private theorem single_sub_one_mem_of_isMaximal (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q)
    (𝔐 : Ideal (MonoidAlgebra R Q)) [𝔐.IsMaximal] (q : Q) : single q (1 : R) - 1 ∈ 𝔐 := by
  -- `R[Q]` is integral over `R`: each group element has order a power of `p`.
  have : Algebra.IsIntegral R (MonoidAlgebra R Q) :=
    TauCeti.MonoidAlgebra.isIntegral_of_isMulTorsion fun m ↦ by
      obtain ⟨k, hk⟩ := hQ m
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ k, pow_pos (Fact.out : p.Prime).pos k, hk⟩
  -- `𝔐` lies over the maximal ideal of `R`, which contains `p`.
  have hcomap : 𝔐.comap (algebraMap R (MonoidAlgebra R Q)) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔐)
  have hp𝔐 : (p : MonoidAlgebra R Q) ∈ 𝔐 := by
    rw [← map_natCast (algebraMap R (MonoidAlgebra R Q)), ← Ideal.mem_comap, hcomap]
    exact hp
  -- In the residue field of `𝔐`, of characteristic `p`, the element `q - 1` is nilpotent.
  let _ := Ideal.Quotient.field 𝔐
  have : CharP (MonoidAlgebra R Q ⧸ 𝔐) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk 𝔐), Ideal.Quotient.eq_zero_iff_mem]
    exact hp𝔐
  obtain ⟨k, hk⟩ := hQ q
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)]
  simp [sub_pow_char_pow, ← map_pow, single_pow, hk, ← one_def]

/-- **The augmentation of the group algebra of a `p`-group is local.** For a commutative `p`-group
`Q` and a local ring `R` in which `p` is not a unit, the augmentation `R[Q] → R` is a local
homomorphism: an element of `R[Q]` whose augmentation is a unit is a unit. -/
theorem isLocalHom_lift_one_of_isPGroup (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q) :
    IsLocalHom (MonoidAlgebra.lift R R Q 1) := by
  refine ⟨fun x hx ↦ ?_⟩
  by_contra hx'
  obtain ⟨𝔐, h𝔐, hx𝔐⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hx𝔐 : x ∈ 𝔐 := hx𝔐 (Ideal.subset_span rfl)
  -- `𝔐` contains the augmentation ideal, which is generated by the differences `q - 1`.
  have hker : RingHom.ker (augmentation R Q) ≤ 𝔐 := by
    rw [ker_augmentation_eq_span, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    exact single_sub_one_mem_of_isMaximal hp hQ 𝔐 q
  -- `x` differs from the constant `algebraMap (augmentation x)` by an element of `𝔐`.
  have hdiff : ∀ y : MonoidAlgebra R Q,
      algebraMap R (MonoidAlgebra R Q) (MonoidAlgebra.lift R R Q 1 y) - y ∈ 𝔐 := fun y ↦
    hker <| by
      rw [RingHom.mem_ker, map_sub, MonoidAlgebra.lift_one_apply]
      simp
  have hmem := 𝔐.add_mem (hdiff x) hx𝔐
  rw [sub_add_cancel] at hmem
  exact h𝔐.ne_top (𝔐.eq_top_of_isUnit_mem hmem (hx.map _))

/-- **The group algebra of a `p`-group is local.** For a commutative `p`-group `Q` and a local
ring `R` in which `p` is not a unit, the group algebra `R[Q]` is a local ring. -/
theorem isLocalRing_of_isPGroup (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q) :
    IsLocalRing (MonoidAlgebra R Q) :=
  have := isLocalHom_lift_one_of_isPGroup hp hQ
  (MonoidAlgebra.lift R R Q 1 : MonoidAlgebra R Q →+* R).domain_isLocalRing

end PGroup

section FinitePGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Over a field of characteristic `p`, an element of the group algebra of a finite `p`-group with
nonzero augmentation has a left inverse. -/
private theorem exists_mul_eq_one_of_augmentation_ne_zero {k : Type*} [Field k] [CharP k p]
    (hG : IsPGroup p G) {x : MonoidAlgebra k G} (hx : augmentation k G x ≠ 0) :
    ∃ y, y * x = 1 := by
  -- Otherwise `x` lies in a maximal left ideal `𝔪`. The simple module `k[G] ⧸ 𝔪` is generated by
  -- a nonzero vector fixed by `G`, so `x` acts on it both by zero and by its augmentation.
  by_contra! h
  obtain ⟨𝔪, h𝔪, hx𝔪⟩ := Ideal.exists_le_maximal (Ideal.span {x}) fun htop ↦ by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (htop ▸ Submodule.mem_top (x := 1))
    exact h y hy
  have hx𝔪 : x ∈ 𝔪 := hx𝔪 (Ideal.mem_span_singleton_self x)
  let M := MonoidAlgebra k G ⧸ 𝔪
  have : IsSimpleModule (MonoidAlgebra k G) M := isSimpleModule_iff_isCoatom.mpr h𝔪.out
  have : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra k G) M
  -- A nonzero vector `s` fixed by `G`, on which `k[G]` acts through the augmentation.
  obtain ⟨s, hs0, hs⟩ := Representation.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one p
    (Representation.ofModule' (k := k) (G := G) M) fun g ↦ by
      obtain ⟨n, hn⟩ := hG g
      exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hact (y : MonoidAlgebra k G) : y • s = augmentation k G y • s := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => rw [add_smul, hy, hz, map_add, add_smul]
    | single g r =>
      have hg : single g (1 : k) • s = s := by
        simpa [TauCeti.Representation.ofModule'_apply] using hs g
      calc single g r • s = r • (single g (1 : k) • s) := by
            rw [← smul_assoc, smul_single', mul_one]
        _ = augmentation k G (single g r) • s := by rw [hg, augmentation_single]
  -- The vector `s` generates `M`, so `1 = y • s`, and `x • 1 = 0` since `x ∈ 𝔪`.
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp
    (IsSimpleModule.span_singleton_eq_top (MonoidAlgebra k G) hs0 ▸
      Submodule.mem_top (x := Submodule.Quotient.mk (1 : MonoidAlgebra k G)))
  have h1 : (Submodule.Quotient.mk (1 : MonoidAlgebra k G) : M) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact fun h1 ↦ h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  apply h1
  have hx1 : x • (Submodule.Quotient.mk (1 : MonoidAlgebra k G) : M) = 0 := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
    exact hx𝔪
  rw [← hy, smul_smul, hact, map_mul, mul_smul, ← hact, hy] at hx1
  exact (smul_eq_zero.mp hx1).resolve_left hx

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The augmentation of the group algebra of a finite `p`-group is local.** For a finite
`p`-group `G`, not necessarily commutative, and a local ring `R` in which `p` is not a unit, an
element of `R[G]` whose augmentation is a unit is a unit. -/
theorem isLocalHom_augmentation_of_isPGroup (hp : ¬IsUnit (p : R)) (hG : IsPGroup p G) :
    IsLocalHom (augmentation R G) := by
  refine ⟨fun x hx ↦ ?_⟩
  have : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr <| by
    rw [← map_natCast (residue R), residue_eq_zero_iff]
    exact hp
  -- A lift `u` of a left inverse of the reduction of `x` modulo the maximal ideal.
  obtain ⟨ū, hū⟩ := exists_mul_eq_one_of_augmentation_ne_zero hG
    (x := mapRingHom G (residue R) x) (by
      rw [augmentation_mapRingHom]
      exact (hx.map (residue R)).ne_zero)
  obtain ⟨u, rfl⟩ : ∃ u, mapRingHom G (residue R) u = ū := by
    rw [coe_mapRingHom]
    exact MonoidAlgebra.map_surjective _ residue_surjective ū
  -- Right multiplication by `x` is onto modulo the maximal ideal, so it is bijective.
  let θ : (Unit → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] (Unit → MonoidAlgebra R G) :=
    LinearMap.pi fun i ↦ (LinearMap.toSpanSingleton _ _ x).comp (LinearMap.proj i)
  have hθ (z : Unit → MonoidAlgebra R G) (i : Unit) : θ z i = z i * x := by simp [θ]
  obtain ⟨hinj, hsurj⟩ := bijective_of_forall_exists_mapRingHom_residue_eq θ fun y ↦
    ⟨fun i ↦ y i * u, fun i ↦ by
      rw [hθ, map_mul, map_mul, mul_assoc, hū, mul_one]⟩
  obtain ⟨z, hz⟩ := hsurj 1
  have hzx : z () * x = 1 := by simpa [hθ] using congrFun hz ()
  have hxz : x * z () = 1 := by
    simpa using congrFun (hinj (a₁ := fun _ ↦ x * z ()) (a₂ := 1)
      (funext fun i ↦ by rw [hθ, hθ, mul_assoc, hzx, Pi.one_apply, one_mul, mul_one])) ()
  exact ⟨⟨x, z (), hxz, hzx⟩, rfl⟩

omit [IsLocalRing R] in
/-- **A finite group with local group algebra is a `p`-group.** If `R` is a local ring in which
the prime `p` is not a unit and the group algebra `R[G]` of a finite group is local, then `G` is a
`p`-group. The ring `R` need not be assumed local: it is the image of `R[G]` under the
augmentation. -/
theorem isPGroup_of_isLocalRing (hp : ¬IsUnit (p : R)) [IsLocalRing (MonoidAlgebra R G)] :
    IsPGroup p G := by
  classical
  -- `R` is local, as the image of the augmentation.
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (MonoidAlgebra R G) inferInstance
  have : IsLocalRing R :=
    IsLocalRing.of_surjective' (augmentation R G) fun r ↦ ⟨single 1 r, by simp⟩
  rw [isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero]
  intro q hq
  obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
  have : Fact q.Prime := ⟨hqprime⟩
  refine Nat.mem_primeFactors.mpr ⟨hqprime, ?_, (Fact.out : p.Prime).ne_zero⟩
  -- Otherwise an element `h` of order `q` generates a subgroup whose average `e` is not a unit,
  -- being killed by `h - 1`, while `1 - e` is not a unit either, having augmentation zero.
  by_contra hqp
  -- The prime `q` is a unit in `R`: the residue characteristic divides `p` but not `q`.
  have hqR : IsUnit (q : R) := by
    rw [IsLocalRing.isUnit_natCast_iff_not_dvd]
    intro hq
    rw [IsLocalRing.isUnit_natCast_iff_not_dvd, not_not] at hp
    rcases (Nat.dvd_prime hqprime).mp hq with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hqp (h1 ▸ hp)
  -- An element `h` of order `q` and the average `e` of the subgroup it generates.
  obtain ⟨h, horder⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  let H := Subgroup.zpowers h
  let _ : Fintype H := Fintype.ofFinite H
  have hcard : IsUnit ((Fintype.card H : ℕ) : R) := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_zpowers, horder]
  let _ := hcard.invertible
  let e := mapDomainRingHom R H.subtype (GroupAlgebra.average R H)
  have he : e * (single h 1 - 1) = 0 := by
    have hh : single h (1 : R) =
        mapDomainRingHom R H.subtype (single ⟨h, Subgroup.mem_zpowers h⟩ 1) := by
      simp
    rw [mul_sub, mul_one, hh, ← map_mul, GroupAlgebra.mul_average_right, sub_self]
  have haug : augmentation R G e = 1 := by
    rw [← RingHom.comp_apply, augmentation_comp_mapDomainRingHom]
    simp [GroupAlgebra.average, Algebra.smul_def, Finset.card_univ]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with he' | he'
  · refine (single_sub_one_ne_zero_iff (R := R) (g := h)).mpr (fun h1 ↦ ?_)
      (he'.mul_right_eq_zero.mp he)
    rw [h1, orderOf_one] at horder
    exact hqprime.one_lt.ne horder
  · simpa [haug] using he'.map (augmentation R G)

/-- **The group algebra of a finite group is local exactly over a `p`-group.** For a finite group
`G`, not necessarily commutative, and a local ring `R` in which the prime `p` is not a unit, the
group algebra `R[G]` is a local ring if and only if `G` is a `p`-group. -/
theorem isLocalRing_iff_isPGroup (hp : ¬IsUnit (p : R)) :
    IsLocalRing (MonoidAlgebra R G) ↔ IsPGroup p G :=
  ⟨fun _ ↦ isPGroup_of_isLocalRing hp, fun hG ↦
    have := isLocalHom_augmentation_of_isPGroup hp hG
    (augmentation R G).domain_isLocalRing⟩

end FinitePGroup

end TauCeti.MonoidAlgebra
