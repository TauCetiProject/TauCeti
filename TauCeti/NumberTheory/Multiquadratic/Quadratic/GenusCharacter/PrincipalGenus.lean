/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.IntUnitsPower
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.ElementaryTwoQuotient
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Independence
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank

/-!
# The principal genus theorem

Let `K = ℚ(√d)` with `d` squarefree and let `D = ∏ P ∈ s, P` be the prime-discriminant
factorization of the fundamental discriminant of `d`, so that `t = #s` is the number of rational
primes ramifying in `K`. The `t` genus characters `χ_P` assemble into a `ZMod 2`-linear map

`Φ : Cl⁺(K) / Cl⁺(K)² → (P ∈ s) → {±1}`

(`genusCharFunElementaryTwoQuotientFamilyLinearMap`). Two facts about `Φ` are already available:
its image contains every sign vector whose coordinates sum to zero
(`exists_genusCharFunElementaryTwoQuotientFamilyLinearMap_eq`, the Dirichlet-theorem input), and
the source has dimension exactly `t - 1` (`narrowTwoRank_eq_ncard_ramifiedPrimes_sub_one`). Since
the sum-zero hyperplane has the same dimension `t - 1`, no room is left over: `Φ` is **injective**
and its image is **exactly** that hyperplane.

Injectivity is the **principal genus theorem**: a narrow ideal class on which every genus character
is trivial — a class in the principal genus — is a square. Together with the description of the
image it says that the genus characters are a complete and independent system of invariants for
narrow ideal classes modulo squares.

See D. A. Cox, *Primes of the Form x² + ny²*, §3.B (Theorem 3.15 and its corollaries), and
F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main results

* `TauCeti.Multiquadratic.mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff`: the
  sign vectors realized by the genus characters are exactly those of coordinate sum zero.
* `TauCeti.Multiquadratic.genusCharFunElementaryTwoQuotientFamilyLinearMap_injective`: the genus
  characters separate the classes of `Cl⁺(K)/Cl⁺(K)²`.
* `TauCeti.Multiquadratic.isSquare_iff_forall_genusCharFunNarrowClassGroupHom_eq_one`: **the
  principal genus theorem**, a narrow ideal class is a square exactly when all its genus
  characters are trivial.
-/

public section

open Polynomial NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-! ### The sum of the sign coordinates -/

/-- The sum of the coordinates of a sign vector indexed by a finite set of prime discriminants,
as a `ZMod 2`-linear functional. Its kernel is the hyperplane of sign patterns of product one. -/
private noncomputable def signSum (s : Finset ℤ) :
    ((P : ↥s) → Additive ℤˣ) →ₗ[ZMod 2] Additive ℤˣ :=
  ∑ P : ↥s, LinearMap.proj P

/-- The coordinate-sum functional is the sum of the coordinates. -/
private theorem signSum_apply (s : Finset ℤ) (v : ↥s → Additive ℤˣ) :
    signSum s v = ∑ P : ↥s, v P := by
  simp [signSum]

/-- The hyperplane of sign vectors of coordinate sum zero has dimension `#s - 1`. -/
private theorem finrank_ker_signSum {s : Finset ℤ} (hne : s.Nonempty) :
    Module.finrank (ZMod 2) (LinearMap.ker (signSum s)) = s.card - 1 := by
  obtain ⟨P₀, hP₀⟩ := hne
  have hpi : Module.finrank (ZMod 2) ((P : ↥s) → Additive ℤˣ) = s.card := by
    rw [Module.finrank_pi_fintype, TauCeti.finrank_zmod_two_additive_intUnits]
    simp
  have hsurj : Function.Surjective (signSum s) := fun w =>
    ⟨Pi.single ⟨P₀, hP₀⟩ w, by rw [signSum_apply]; simp⟩
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (signSum s)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, TauCeti.finrank_zmod_two_additive_intUnits]
  have hrn := LinearMap.finrank_range_add_finrank_ker (signSum s)
  rw [hpi, hrange] at hrn
  omega

/-! ### The image and the kernel of the genus-character family -/

/-- The dimension of `Cl⁺(K)/Cl⁺(K)²` is `#s - 1`, read off the narrow `2`-rank formula. -/
private theorem finrank_narrowElementaryTwoQuotient_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) :
    Module.finrank (ZMod 2) (NarrowClassGroup.ElementaryTwoQuotient K) = s.card - 1 := by
  rw [← NarrowClassGroup.twoRank_def, narrowTwoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf,
    ncard_ramifiedPrimes_eq_card hmin hgen hsf hs heven hprod]

/-- **The genus characters realize exactly the sign vectors of product one.** For `K = ℚ(√d)` with
`d` squarefree and `∏ P ∈ s, P = fundamentalDiscriminant d` a prime-discriminant factorization, a
sign vector indexed by `s` is a value of the family of singleton genus characters on
`Cl⁺(K)/Cl⁺(K)²` exactly when its coordinates sum to zero — that is, exactly when the product of
its signs is `1`.

The inclusion "⊇" is the Dirichlet-theorem input
`exists_genusCharFunElementaryTwoQuotientFamilyLinearMap_eq`; the inclusion "⊆" holds because
`Cl⁺(K)/Cl⁺(K)²` has dimension `#s - 1`, leaving no room beyond the hyperplane. -/
theorem mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (v : ↥s → Additive ℤˣ) :
    v ∈ LinearMap.range
        (genusCharFunElementaryTwoQuotientFamilyLinearMap hs heven hprod hmin hgen hsf) ↔
      ∑ P : ↥s, v P = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- With no prime discriminants there is only the zero vector.
    have hv : v = 0 := funext fun P => (Finset.notMem_empty _ P.2).elim
    subst hv
    simp
  · set Φ := genusCharFunElementaryTwoQuotientFamilyLinearMap hs heven hprod hmin hgen hsf
    have hrange : LinearMap.range Φ = LinearMap.ker (signSum s) := by
      refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
      · intro w hw
        rw [LinearMap.mem_ker, signSum_apply] at hw
        obtain ⟨x, hx⟩ :=
          exists_genusCharFunElementaryTwoQuotientFamilyLinearMap_eq hs heven hprod hmin hgen hsf
            w hw
        exact ⟨x, hx⟩
      · rw [finrank_ker_signSum hne]
        exact (LinearMap.finrank_range_le Φ).trans
          (finrank_narrowElementaryTwoQuotient_eq hs heven hprod hmin hgen hsf).le
    rw [hrange, LinearMap.mem_ker, signSum_apply]

/-- **The genus characters separate narrow classes modulo squares.** The `ZMod 2`-linear family of
singleton genus characters is injective on `Cl⁺(K)/Cl⁺(K)²`. Equivalently, the `#s` genus
characters span the full dual of `Cl⁺(K)/Cl⁺(K)²`. -/
theorem genusCharFunElementaryTwoQuotientFamilyLinearMap_injective {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) :
    Function.Injective
      (genusCharFunElementaryTwoQuotientFamilyLinearMap hs heven hprod hmin hgen hsf) := by
  set Φ := genusCharFunElementaryTwoQuotientFamilyLinearMap hs heven hprod hmin hgen hsf
  have hsrc := finrank_narrowElementaryTwoQuotient_eq hs heven hprod hmin hgen hsf (s := s)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- With no prime discriminants the source is already trivial.
    have : Subsingleton (NarrowClassGroup.ElementaryTwoQuotient K) :=
      Module.finrank_zero_iff.mp (by simpa using hsrc)
    exact fun a b _ => Subsingleton.elim a b
  · have hrange : LinearMap.range Φ = LinearMap.ker (signSum s) :=
      Submodule.ext fun v =>
        (mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff hs heven hprod hmin hgen
          hsf v).trans (by rw [LinearMap.mem_ker, signSum_apply])
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_ker_signSum hne, hsrc] at hrn
    have hker : Module.finrank (ZMod 2) (LinearMap.ker Φ) = 0 := by
      have : 1 ≤ s.card := Finset.card_pos.mpr hne
      omega
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    exact hker

/-! ### The principal genus theorem -/

/-- **The principal genus theorem.** Let `K = ℚ(√d)` with `d` squarefree and let
`∏ P ∈ s, P = fundamentalDiscriminant d` be the prime-discriminant factorization of its
discriminant. A narrow ideal class of `K` is a square exactly when every genus character is
trivial on it; that is, the principal genus is the group of squares.

This is the classical statement that the genus characters cut out `Cl⁺(K)²` inside `Cl⁺(K)`. -/
theorem isSquare_iff_forall_genusCharFunNarrowClassGroupHom_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (A : NarrowClassGroup K) :
    IsSquare A ↔ ∀ (P : ℤ) (hP : P ∈ s),
      genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr hP) A = 1 := by
  rw [← TauCeti.elementaryTwoQuotientMk_eq_zero_iff]
  constructor
  · intro h P hP
    have hzero := congrArg (genusCharFunElementaryTwoQuotientLinearMap hs heven hprod hmin hgen hsf
      (Finset.singleton_subset_iff.mpr hP)) h
    rw [genusCharFunElementaryTwoQuotientLinearMap_mk, map_zero] at hzero
    exact ofMul_eq_zero.mp hzero
  · intro h
    refine genusCharFunElementaryTwoQuotientFamilyLinearMap_injective hs heven hprod hmin hgen hsf
      ?_
    rw [map_zero]
    funext P
    rw [genusCharFunElementaryTwoQuotientFamilyLinearMap_apply,
      genusCharFunElementaryTwoQuotientLinearMap_mk, h P P.2]
    simp

end TauCeti.Multiquadratic
