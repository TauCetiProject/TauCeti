/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.StalkRank
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Module.Projective.Semilocal

/-!
# The projective `K₀` of a semilocal ring

Over a commutative semilocal ring `R`, a ring with finitely many maximal ideals, finitely
generated projective modules cancel free summands and are classified by their rank functions
(`TauCeti/Algebra/Module/Projective/Semilocal.lean`). In the split Grothendieck group of finitely
generated projective `R`-modules, equality of classes is stable equivalence, so here two modules
have the same class exactly when they are isomorphic, and exactly when they have the same rank at
every prime.

Consequently the rank `K₀(R) →+* H(R)`, `H(R) = LocallyConstant (Spec R) ℤ`, is injective. It is
surjective for every commutative ring, split by the rank section, so over a semilocal ring it is a
ring isomorphism

  `K₀(R) ≃+* H(R)`, `[P] ↦ (p ↦ rank_{Rₚ} Pₚ)`.

If `Spec R` has `c` connected components, `H(R)` is `ℤᶜ`. The number `c` need not be the number of
maximal ideals: the localization of `ℤ` at the complement of `(2) ∪ (3)` is a semilocal domain with
two maximal ideals and connected spectrum, so its `K₀` is `ℤ`. The semilocal hypothesis cannot be
dropped: over the Dedekind domain `ℤ[√-5]`, the prime `(2, 1 + √-5)` and the ring itself have rank
one everywhere but different classes.

Applied to the local rings `Rₚ`, the isomorphism shows that for an arbitrary commutative ring `R`
the kernel of the rank consists of the classes whose images in `K₀(Rₚ)` vanish for every prime
`p`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankRingEquiv`: the rank isomorphism `K₀(R) ≃+* H(R)` of a
  semilocal ring.

## Main results

* `TauCeti.SplitK0.of_eq_of_iff_nonempty_linearEquiv`: over a semilocal ring, two finitely
  generated projective modules have the same class if and only if they are isomorphic.
* `TauCeti.SplitK0.of_eq_of_iff_rankAtStalk_eq`: over a semilocal ring, two finitely generated
  projective modules have the same class if and only if they have the same rank at every prime.
* `TauCeti.FiniteProjectiveModules.rank_injective`: over a semilocal ring the rank is injective.
* `TauCeti.FiniteProjectiveModules.rankRingEquiv_symm_apply`: the inverse of the rank isomorphism
  is the rank section.
* `TauCeti.FiniteProjectiveModules.rank_eq_zero_iff_forall_map_eq_zero`: over any commutative ring
  a class has rank zero if and only if its image in `K₀(Rₚ)` vanishes for every prime `p`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Definition 2.3, pp. 71–72, and Exercise 2.6, p. 79.
-/

public section

namespace TauCeti.SplitK0

universe u

variable {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)]
  {P Q : (finiteProjectiveModules R).FullSubcategory}

/-- **Classes in the projective `K₀` of a semilocal ring are isomorphism classes.** If `R` has
finitely many maximal ideals, two finitely generated projective `R`-modules have the same class
in split `K₀` if and only if they are isomorphic. -/
theorem of_eq_of_iff_nonempty_linearEquiv :
    of.{u} P = of.{u} Q ↔ Nonempty (P.obj ≃ₗ[R] Q.obj) := by
  rw [of_eq_of_iff_stableEquivalent]
  exact ⟨StableEquivalent.nonempty_linearEquiv_of_finite_maximalSpectrum,
    fun ⟨e⟩ ↦ .of_equiv e⟩

/-- **Rank detects classes in the projective `K₀` of a semilocal ring.** If `R` has finitely
many maximal ideals, two finitely generated projective `R`-modules have the same class in split
`K₀` if and only if they have the same rank at every prime. -/
theorem of_eq_of_iff_rankAtStalk_eq :
    of.{u} P = of.{u} Q ↔
      Module.rankAtStalk (R := R) P.obj = Module.rankAtStalk (R := R) Q.obj := by
  rw [of_eq_of_iff_nonempty_linearEquiv, Module.nonempty_linearEquiv_iff_rankAtStalk_eq]

end TauCeti.SplitK0

namespace TauCeti.FiniteProjectiveModules

universe u

/-! ### The rank isomorphism of a semilocal ring -/

section Semilocal

variable (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]

/-- **The rank is injective on the projective `K₀` of a semilocal ring.** If `R` has finitely many
maximal ideals, a class in `K₀(R)` is determined by its rank function on `Spec R`. -/
theorem rank_injective : Function.Injective (rank R) := by
  refine (injective_iff_map_eq_zero (rank R)).mpr fun x hx ↦ ?_
  obtain ⟨P, Q, rfl⟩ := SplitK0.exists_eq_sub x
  rw [map_sub, sub_eq_zero] at hx
  rw [sub_eq_zero, SplitK0.of_eq_of_iff_rankAtStalk_eq]
  ext p
  simpa using congr($hx p)

/-- **The projective `K₀` of a semilocal ring is the ring of locally constant ranks.** If `R` has
finitely many maximal ideals, the rank `K₀(R) →+* H(R)`, `H(R) = LocallyConstant (Spec R) ℤ`, is a
ring isomorphism, sending the class of a finitely generated projective module `P` to its rank
function `p ↦ rank_{Rₚ} Pₚ` (`TauCeti.FiniteProjectiveModules.rank_of`), with inverse the rank
section `TauCeti.FiniteProjectiveModules.rankSection`. If `Spec R` has `c` connected components,
`H(R)` is `ℤᶜ`; this `c` need not be the number of maximal ideals. -/
noncomputable def rankRingEquiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  RingEquiv.ofBijective (rank R) ⟨rank_injective R, rank_surjective R⟩

@[simp]
theorem coe_rankRingEquiv : ⇑(rankRingEquiv R) = rank R :=
  (rfl)

/-- The inverse of the rank isomorphism of a semilocal ring is the rank section. -/
@[simp]
theorem rankRingEquiv_symm_apply (f : LocallyConstant (PrimeSpectrum R) ℤ) :
    (rankRingEquiv R).symm f = rankSection R f :=
  (rankRingEquiv R).symm_apply_eq.mpr (rank_rankSection R f).symm

/-- Over a semilocal ring the rank section is a left inverse of the rank: every class in `K₀` is
the class `∑ n [P_{U_n}]` built from the clopen fibres `U_n` of its rank. -/
@[simp]
theorem rankSection_rank (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rankSection R (rank R x) = x :=
  rank_injective R (rank_rankSection R (rank R x))

end Semilocal

/-! ### Rank zero is detected by localizations -/

/-- **A class has rank zero exactly when it vanishes at every localization.** For a commutative
ring `R`, a class `x ∈ K₀(R)` lies in the kernel of the rank if and only if its image in `K₀(Rₚ)`
under extension of scalars is zero for every prime `p`. The kernel of the rank need not be zero:
over `ℤ[√-5]` the class `[(2, 1 + √-5)] - [ℤ[√-5]]` is nonzero and vanishes at every
localization. -/
theorem rank_eq_zero_iff_forall_map_eq_zero {R : Type u} [CommRing R]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rank R x = 0 ↔ ∀ p : PrimeSpectrum R,
      SplitK0.map.{u, u}
        (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesExtendScalars x =
        0 := by
  refine ⟨fun hx p ↦ rank_injective (Localization.AtPrime p.asIdeal) ?_, fun hx ↦ ?_⟩
  · ext q
    simp [rank_map, hx]
  · ext p
    -- The closed point of `Spec Rₚ` lies over `p`.
    have hp : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)) = p :=
      PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
    have h := congr($(rank_map (algebraMap R (Localization.AtPrime p.asIdeal)) x)
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)))
    rw [hx p, map_zero] at h
    simpa [hp] using h.symm

end TauCeti.FiniteProjectiveModules
