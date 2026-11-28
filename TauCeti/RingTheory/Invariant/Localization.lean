/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.Localization.Action
import TauCeti.GroupTheory.GroupAction.Closure
import TauCeti.RingTheory.Invariant.PrimeAvoidance

/-!
# Invariant rings and localization

Let a monoid `G` act on a commutative semiring `A` by ring endomorphisms (automorphisms if `G` is
a group), and write `Aᴳ` for the invariants, as the subsemiring `FixedPoints.subsemiring A G` or,
when `A` is a ring, the subring `FixedPoints.subring A G`. This file shows that, when `G` is
finitely generated, for instance finite, taking invariants commutes with localization at invariant
elements.

For a semiring `R` with `[Algebra R A] [SMulCommClass G R A]`, for instance `R = Aᴳ`, and a
submonoid `M` of `R`, `G` fixes the denominators of `M⁻¹A` (`Localization
(Algebra.algebraMapSubmonoid A M)`) and acts on it
(`TauCeti.Localization.instMulSemiringActionLocalization`), so the localization map `A → M⁻¹A`
restricts to `Aᴳ → (M⁻¹A)ᴳ`. When `G` is finitely generated, for instance finite, and `M` is a
submonoid of `Aᴳ` itself, `(M⁻¹A)ᴳ` is the localization of `Aᴳ` at `M`. A fraction `a / s` fixed by
every generator `g` satisfies `t_g (g • a) = t_g a` for some `t_g ∈ M`, which can be replaced by the
product `t` of the `t_g` because there are finitely many generators, and then `a / s = t a / (s t)`
with `t a` invariant. Taking `M` to be the powers of an invariant `r` gives the localization
`A[1/r]` of `A` at `r`.

The argument only uses finitely many ring endomorphisms `σ i` of `A` and `τ i` of a localization
`S` of `A`, compatible with the localization map, and is stated in that form
(`TauCeti.FixedPoints.isLocalization_of_mem_range_iff`): the localization is taken at the image of
a submonoid `M` of a semiring `R` that maps injectively onto the elements of `A` fixed by every
`σ i`, and the elements of `S` fixed by every `τ i` are then the localization of `R` at `M`.

Also for a finite group `G` acting on a commutative ring `A`, the local homomorphism
`(Aᴳ)_P → A_Q` induced by `Aᴳ ⊆ A` at a prime `Q` of `A` lying over a prime `P` of `Aᴳ` is
injective. If an invariant `a` is killed by some `t ∉ Q`, it is killed by an invariant outside `Q`
(`Ideal.exists_mem_fixedPoints_notMem_mul_eq_zero_of_mul_eq_zero`), which lies outside `P`.

These are the two local facts behind the categorical universal property of the affine invariant
quotient `Spec A ⟶ Spec Aᴳ` for arbitrary target schemes.

## Main definitions

* For a semiring `R` with `[Algebra R A] [SMulCommClass G R A]` (for instance `R = Aᴳ`) and a
  submonoid `M` of `R`, the instances `Algebra (FixedPoints.subsemiring A G)
  (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G)` and, for a ring
  `A`, `Algebra (FixedPoints.subring A G)
  (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G)`, given by `A → M⁻¹A`.

## Main results

* `TauCeti.FixedPoints.isLocalization_of_mem_range_iff`: for a localization `S` of `A` at the
  image of a submonoid `M` of a semiring `R` mapping injectively onto the elements of `A` fixed by
  finitely many ring endomorphisms, the elements of `S` fixed by compatible ring endomorphisms are
  the localization of `R` at `M`.
* `TauCeti.FixedPoints.isLocalization_subsemiring` and, for a ring `A`,
  `TauCeti.FixedPoints.isLocalization`: for finitely generated `G` and a submonoid `M` of `Aᴳ`,
  `(M⁻¹A)ᴳ` is the localization of `Aᴳ` at `M`.
* `TauCeti.FixedPoints.localRingHom_injective`: for a finite group `G`, `(Aᴳ)_P → A_Q` is
  injective.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

namespace TauCeti.FixedPoints

/-- **Fixed elements commute with localization.** Let `S` be a localization of `A` at the image of
a submonoid `M` of `R`, and let finitely many ring endomorphisms `σ i` of `A` and `τ i` of `S` be
compatible with `A → S`. If `R → A` and `R' → S` are injective with images the elements fixed by
every `σ i`, respectively every `τ i`, and `R → R'` is compatible with them, then `R'` is the
localization of `R` at `M`. A fraction `a / s` fixed by every `τ i` satisfies
`t_i σ i a = t_i a` for some `t_i ∈ M`, which can be replaced by the product `t` of the `t_i`
since there are finitely many `i`; then `a / s = t a / (s t)` with `t a` fixed. -/
theorem isLocalization_of_mem_range_iff {ι R A R' S : Type*} [Finite ι] [CommSemiring R]
    [CommSemiring A] [CommSemiring R'] [CommSemiring S] [Algebra R A] [Algebra A S] [Algebra R' S]
    [Algebra R R'] {M : Submonoid R} [IsLocalization (Algebra.algebraMapSubmonoid A M) S]
    (σ : ι → A →+* A) (τ : ι → S →+* S)
    (hστ : ∀ i a, τ i (algebraMap A S a) = algebraMap A S (σ i a))
    (hR : Function.Injective (algebraMap R A))
    (hσ : ∀ a, a ∈ Set.range (algebraMap R A) ↔ ∀ i, σ i a = a)
    (hR' : Function.Injective (algebraMap R' S))
    (hτ : ∀ s, s ∈ Set.range (algebraMap R' S) ↔ ∀ i, τ i s = s)
    (h : ∀ x, algebraMap R' S (algebraMap R R' x) = algebraMap A S (algebraMap R A x)) :
    IsLocalization M R' := by
  have hfix (x : R) (i : ι) :
      τ i (algebraMap A S (algebraMap R A x)) = algebraMap A S (algebraMap R A x) := by
    rw [hστ, (hσ _).mp ⟨x, rfl⟩ i]
  refine (_root_.isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `m ∈ M` is a unit of `S` whose inverse is again fixed.
    intro m
    have hu : IsUnit (algebraMap A S (algebraMap R A m)) :=
      IsLocalization.map_units S ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem m⟩
    obtain ⟨v, hv⟩ := (hτ (Ring.inverse (algebraMap A S (algebraMap R A m)))).mpr fun i ↦ by
      rw [hu.map_ringInverse (τ i), hfix]
    refine isUnit_iff_exists_inv.mpr ⟨v, hR' ?_⟩
    rw [map_mul, h, hv, map_one]
    exact Ring.mul_inverse_cancel _ hu
  · -- A fixed fraction `a / s` equals `t a / (s t)` with `t ∈ M` and `t a` fixed.
    intro z
    obtain ⟨⟨a, _, ⟨s, hs, rfl⟩⟩, ha⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid A M) (algebraMap R' S z)
    have hk (i : ι) : ∃ t ∈ M, algebraMap R A t * σ i a = algebraMap R A t * a := by
      have hi := congrArg (τ i) ha
      rw [map_mul, (hτ _).mp ⟨z, rfl⟩ i, hfix, hστ] at hi
      obtain ⟨⟨_, t, ht, rfl⟩, hti⟩ :=
        IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) (hi.symm.trans ha)
      exact ⟨t, ht, hti⟩
    choose t ht hti using hk
    have := Fintype.ofFinite ι
    set T := ∏ i, t i
    have hT (i : ι) : algebraMap R A T * σ i a = algebraMap R A T * a := by
      -- `T = t i * c`, and multiplying `hti i` by `c` gives the claim.
      obtain ⟨c, hc⟩ : t i ∣ T := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      have hc' := congrArg (· * algebraMap R A c) (hti i)
      simpa only [hc, map_mul, mul_right_comm] using hc'
    obtain ⟨b, hb⟩ := (hσ (algebraMap R A T * a)).mpr fun i ↦ by
      rw [map_mul, (hσ _).mp ⟨T, rfl⟩ i, hT i]
    refine ⟨(b, ⟨s * T, mul_mem hs (prod_mem fun i _ ↦ ht i)⟩), hR' ?_⟩
    simp only [map_mul, h, hb, ← ha]
    ring
  · -- Elements of `R` identified in `R'` are identified after multiplication by some `t ∈ M`.
    intro x y hxy
    have hxy' : algebraMap A S (algebraMap R A x) = algebraMap A S (algebraMap R A y) := by
      rw [← h, ← h, hxy]
    obtain ⟨⟨_, t, ht, rfl⟩, hty⟩ :=
      IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hxy'
    exact ⟨⟨t, ht⟩, hR (by simpa only [map_mul] using hty)⟩


section Semiring

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]

section Localization

variable {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The localization map `A → M⁻¹A` sends invariants to invariants. -/
theorem algebraMap_mem_fixedPoints {a : A} (ha : a ∈ FixedPoints.subsemiring A G) :
    algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a ∈
      FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G := fun g ↦ by
  rw [Localization.smul_algebraMap, ha g]

/-- The algebra structure of `(M⁻¹A)ᴳ` over `Aᴳ`, as invariant subsemirings, given by the
localization map `A → M⁻¹A`. -/
noncomputable instance instAlgebraLocalizationSubsemiring :
    Algebra (FixedPoints.subsemiring A G)
      (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  ((algebraMap A (Localization (Algebra.algebraMapSubmonoid A M))).restrict
    (FixedPoints.subsemiring A G) (FixedPoints.subsemiring _ G)
      fun _ ha ↦ algebraMap_mem_fixedPoints ha).toAlgebra

/-- The algebra map `Aᴳ → (M⁻¹A)ᴳ` of invariant subsemirings is the localization map
`A → M⁻¹A`. -/
@[simp]
theorem coe_algebraMap_localization_subsemiring (a : FixedPoints.subsemiring A G) :
    (algebraMap (FixedPoints.subsemiring A G)
        (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) a :
      Localization (Algebra.algebraMapSubmonoid A M)) =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.coe_restrict_apply]

end Localization

/-- **Invariants commute with localization at invariant elements.** For a finitely generated monoid
`G`, for instance a finite one, and a submonoid `M` of the invariant subsemiring `Aᴳ`, the
invariants of `M⁻¹A` are the localization of `Aᴳ` at `M`. The elements fixed by `G` are those fixed
by a finite generating set, to which `isLocalization_of_mem_range_iff` applies. -/
instance isLocalization_subsemiring [Monoid.FG G] {M : Submonoid (FixedPoints.subsemiring A G)} :
    IsLocalization M
      (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) := by
  obtain ⟨s, hs, hsfin⟩ := Monoid.fg_iff.mp ‹Monoid.FG G›
  have := hsfin.to_subtype
  -- In `A` and in `M⁻¹A`, the invariants are the elements fixed by every generator in `s`.
  have hrange {X : Type _} [CommSemiring X] [MulSemiringAction G X] (x : X) :
      x ∈ Set.range (algebraMap (FixedPoints.subsemiring X G) X) ↔
        ∀ g : s, MulSemiringAction.toRingHom G X g x = x :=
    (Set.ext_iff.mp Subtype.range_coe_subtype _).trans
      ⟨fun hx g ↦ hx g, fun hx g ↦ Submonoid.forall_mem_closure_smul_eq_self_iff.mpr
        (fun g hg ↦ hx ⟨g, hg⟩) g (hs ▸ Submonoid.mem_top g)⟩
  exact isLocalization_of_mem_range_iff (fun g : s ↦ MulSemiringAction.toRingHom G A g)
    (fun g : s ↦ MulSemiringAction.toRingHom G _ g) (fun g ↦ Localization.smul_algebraMap (g : G))
    Subtype.val_injective hrange Subtype.val_injective hrange
    coe_algebraMap_localization_subsemiring

end Semiring

section Ring

variable {G A : Type*} [Monoid G] [CommRing A] [MulSemiringAction G A]

section Localization

variable {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The algebra structure of `(M⁻¹A)ᴳ` over `Aᴳ`, as invariant subrings, given by the localization
map `A → M⁻¹A`. It is `instAlgebraLocalizationSubsemiring`, since the invariant subring and
subsemiring have the same elements. -/
noncomputable instance instAlgebraLocalization :
    Algebra (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  inferInstanceAs <| Algebra (FixedPoints.subsemiring A G)
    (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G)

/-- The algebra map `Aᴳ → (M⁻¹A)ᴳ` of invariant subrings is the localization map `A → M⁻¹A`.
This is `coe_algebraMap_localization_subsemiring`, restated for the subring forms, which `simp`
does not identify with the subsemiring forms. -/
@[simp]
theorem coe_algebraMap_localization (a : FixedPoints.subring A G) :
    (algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) a :
      Localization (Algebra.algebraMapSubmonoid A M)) =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a :=
  coe_algebraMap_localization_subsemiring a

end Localization

/-- **Invariants commute with localization at invariant elements.** For a finitely generated monoid
`G`, for instance a finite one, and a submonoid `M` of the invariant subring `Aᴳ`, the invariants of
`M⁻¹A` are the localization of `Aᴳ` at `M`. This is `isLocalization_subsemiring`, since the
invariant subring and subsemiring have the same elements. -/
instance isLocalization [Monoid.FG G] {M : Submonoid (FixedPoints.subring A G)} :
    IsLocalization M (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  isLocalization_subsemiring (G := G) (A := A) (M := M)

end Ring

section LocalRingHom

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

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
  obtain ⟨s, hs, hsQ, hsx⟩ := Q.exists_mem_fixedPoints_notMem_mul_eq_zero_of_mul_eq_zero x htQ htx
  refine (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mpr
    ⟨⟨⟨s, hs⟩, fun h ↦ hsQ (by rwa [hPQ] at h)⟩, Subtype.ext hsx⟩

end LocalRingHom

end TauCeti.FixedPoints
