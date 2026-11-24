/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.RingTheory.Norm.FractionRing
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.TotalQuotient
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.GroupTheory.FiniteAbelian.IntegralDual
import TauCeti.RingTheory.Ideal.MinimalPrime.Finite
import TauCeti.RingTheory.Ideal.MinimalPrime.Localization
import TauCeti.RingTheory.Localization.FiniteFree
import TauCeti.RingTheory.Norm.Projective
import TauCeti.RingTheory.NovikovSeries.LeadingTerm

/-!
# Minimal primes of Novikov rings and norms on field components

Let `H` be a finitely generated abelian group with torsion subgroup `T`, `N : H →+ ℝ` a period
homomorphism and `R` a Noetherian ring, for instance `R = ℤ`. Two minimal primes of
`Nov(R, H, N)` that meet the group ring `R[T]` in the same ideal are equal
(`TauCeti.NovikovSeries.eq_of_mem_minimalPrimes_of_comap_eq`): the irreducible components of
`Spec Nov(R, H, N)` are separated by the finite group ring `R[T]` alone.

To see this, split `H ≃ F × T` with `F` free. The period map vanishes on the finite group `T`,
and a Novikov series on `H` is a Novikov series on `F` with coefficients in `R[T]`. Reducing these
coefficients modulo a minimal prime `𝔭` of `R[T]` gives a ring homomorphism
`Nov(R, H, N) → Nov(R[T] ⧸ 𝔭, F, N|F)` into a domain, whose kernel `P_𝔭` is a prime meeting
`R[T]` in `𝔭`. A series in every `P_𝔭` has its coefficients in the nilradical of `R[T]`, which is
nilpotent since `R[T]` is Noetherian, so the series is nilpotent. As `R[T]` has finitely many
minimal primes, every minimal prime of `Nov(R, H, N)` is then one of the `P_𝔭`, and is determined
by its intersection with `R[T]`.

Now let `K ≤ H` be a subgroup of finite index containing `T`, so that `R[T] ⊆ Nov(R, K, N|K)`, and
let `R` be a domain. The total ring of fractions `Q(Nov(R, H, N))` is finite free over
`Q(Nov(R, K, N|K))`, both are Artinian, and their primes contract to minimal primes of the Novikov
rings. Two primes of `Q(Nov(R, H, N))` over the same prime of `Q(Nov(R, K, N|K))` meet `R[T]` in
the same ideal, so they are equal. Hence contraction is a bijection between the primes of the two
total rings of fractions (`TauCeti.NovikovSeries.comap_algebraMap_bijective_of_torsion_le`). When
the Novikov rings are reduced, as for `R = ℤ`, these primes index the field components of the total
rings of fractions. Reading the norm modulo a prime (`Algebra.projectiveNorm_mem_iff`), the
norm of the finite cover of an element lies in a prime of the base exactly when the element lies in
the prime above it (`TauCeti.NovikovSeries.fractionNorm_mem_iff_mem_of_torsion_le`): an element
whose component in a field factor is nonzero has a norm whose component in the corresponding field
factor of the base is nonzero. This is what lets identities obtained from the norms of finite
cyclic covers be read one field component at a time.

The hypothesis that `K` contains the torsion of `H` cannot be dropped. For `H = ℤ/2`, `N = 0` and
`K = 0`, the total ring of fractions of `ℚ[ℤ/2]` is `ℚ × ℚ`, the base is the field `ℚ`, and the
norm of the idempotent `(1 + g) / 2` is `0`, although its component in the first field is `1`.

## Main results

* `TauCeti.NovikovSeries.eq_of_mem_minimalPrimes_of_comap_eq`: minimal primes of `Nov(R, H, N)`
  are determined by their intersections with the group ring of the torsion subgroup.
* `TauCeti.NovikovSeries.comap_algebraMap_bijective_of_torsion_le`: for `K` of finite index
  containing the torsion, contraction is a bijection between the primes of the two total rings
  of fractions.
* `TauCeti.NovikovSeries.fractionNorm_mem_iff_mem_of_torsion_le`: the norm of `x` lies in a prime
  of the base total ring of fractions exactly when `x` lies in the prime above it.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  §1.6 and Lemma 3.5(c).
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti

namespace NovikovSeries

section Splitting

/-! ### Reducing the torsion coefficients of a split exponent group -/

variable {R H F T : Type*} [CommRing R] [AddCommGroup H] [AddCommGroup F] [AddCommGroup T]
  [Finite T] {N : H →+ ℝ} (e : H ≃+ F × T)

/-- The period map on the free factor of a splitting `H ≃ F × T`. -/
private def splitPeriod (N : H →+ ℝ) (e : H ≃+ F × T) : F →+ ℝ :=
  N.comp (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl F T))

/-- The period map vanishes on the finite factor, so it factors through the free factor. -/
private theorem period_eq_splitPeriod (h : H) : N h = splitPeriod N e (e h).1 :=
  N.apply_eq_apply_symm_fst e h

/-- The character `h ↦ e^t` of `H` with values in `R[T]`, for the `T`-component `t` of `e h`. -/
private def splitCharacter (R : Type*) [CommRing R] (e : H ≃+ F × T) :
    Multiplicative H →* AddMonoidAlgebra R T :=
  (AddMonoidAlgebra.of R T).comp
    (AddMonoidHom.toMultiplicative ((AddMonoidHom.snd F T).comp e.toAddMonoidHom))

/-- A Novikov series on `H ≃ F × T` as a Novikov series on `F` with coefficients in `R[T]`. -/
private def splitRingHom : NovikovSeries R H N →+*
    NovikovSeries (AddMonoidAlgebra R T) F (splitPeriod N e) :=
  (mapRingHom (RingHom.id _) ((AddMonoidHom.fst F T).comp e.toAddMonoidHom)
      ⟨1, one_pos, fun h => by simp [period_eq_splitPeriod e h]⟩).comp
    ((twist (splitCharacter R e)).comp
      (mapRingHom (algebraMap R (AddMonoidAlgebra R T)) (AddMonoidHom.id H)
        exists_period_rescale_id))

private theorem splitRingHom_single (g : H) (r : R) :
    splitRingHom e (single g r : NovikovSeries R H N) =
      single (e g).1 (AddMonoidAlgebra.single (e g).2 r) := by
  simp [splitRingHom, splitCharacter, mapRingHom_apply, map_single, twist_single,
    AddMonoidAlgebra.single_mul_single]

/-- The coefficient of the split series at `f` collects the coefficients of the series on the
coset `e⁻¹ (f, T)`. -/
private theorem coeff_splitRingHom_apply (a : NovikovSeries R H N) (f : F) (t : T) :
    ((splitRingHom e a).coeff f).coeff t = a.coeff (e.symm (f, t)) := by
  have := Fintype.ofFinite T
  classical
  rw [splitRingHom, RingHom.comp_apply, mapRingHom_apply,
    coeff_map_eq_sum _ _ _ _ (Finset.univ.image fun t' : T => e.symm (f, t'))
      (fun h hh => Finset.mem_image.2 ⟨(e h).2, Finset.mem_univ _, by
        rw [← hh.2, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst]
        simp⟩)
      (fun h hh => by obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 hh; simp),
    Finset.sum_image fun _ _ _ _ h => by simpa using h]
  simp [splitCharacter, AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]

/-- The inclusion of the group ring of the finite factor into the Novikov ring. -/
private def splitInclusion : AddMonoidAlgebra R T →+* NovikovSeries R H N :=
  ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R
    (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr F T)))

variable {D : Type*} [CommRing D]

/-- The reduction `Nov(R, H, N) → Nov(D, F, N|F)` of the torsion coefficients along a ring
homomorphism `ψ : R[T] →+* D`. -/
private def splitReduction (ψ : AddMonoidAlgebra R T →+* D) :
    NovikovSeries R H N →+* NovikovSeries D F (splitPeriod N e) :=
  (mapRingHom ψ (AddMonoidHom.id F) exists_period_rescale_id).comp (splitRingHom e)

/-- The kernel of the reduction of the torsion coefficients along `ψ`. -/
private def splitKer (ψ : AddMonoidAlgebra R T →+* D) : Ideal (NovikovSeries R H N) :=
  RingHom.ker (splitReduction e ψ)

private theorem mem_splitKer_iff {ψ : AddMonoidAlgebra R T →+* D} {a : NovikovSeries R H N} :
    a ∈ splitKer e ψ ↔ ∀ f, ψ ((splitRingHom e a).coeff f) = 0 := by
  simp [splitKer, splitReduction, NovikovSeries.ext_iff]

/-- On the group ring of the finite factor, the reduction along `ψ` is `ψ`, followed by the
inclusion of constants. -/
private theorem splitReduction_comp_splitInclusion (ψ : AddMonoidAlgebra R T →+* D) :
    (splitReduction (N := N) e ψ).comp (splitInclusion e) =
      (algebraMap D (NovikovSeries D F (splitPeriod N e))).comp ψ := by
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun t => ?_ <;>
  simp [splitReduction, splitInclusion, splitRingHom_single, ofAddMonoidAlgebra_single,
    map_single]

/-- The kernel of the reduction along `ψ` meets `R[T]` in the kernel of `ψ`. -/
private theorem comap_splitKer (ψ : AddMonoidAlgebra R T →+* D) :
    (splitKer (N := N) e ψ).comap (splitInclusion e) = RingHom.ker ψ := by
  ext x
  rw [Ideal.mem_comap, splitKer, RingHom.mem_ker, ← RingHom.comp_apply,
    splitReduction_comp_splitInclusion]
  simp

/-- Over a domain, the kernel of the reduction is a prime ideal. -/
private theorem isPrime_splitKer [IsDomain D] [UniqueSums F] (ψ : AddMonoidAlgebra R T →+* D) :
    (splitKer (N := N) e ψ).IsPrime :=
  RingHom.ker_isPrime _

/-- Splitting the exponents is injective: it keeps every coefficient. -/
private theorem splitRingHom_injective :
    Function.Injective (splitRingHom (R := R) (N := N) e) :=
  fun a b hab => ext fun h => by
    have := congrArg (fun c => (c.coeff (e h).1).coeff (e h).2) hab
    simpa [coeff_splitRingHom_apply] using this

variable [IsNoetherianRing (AddMonoidAlgebra R T)]

/-- A series killed by the reductions modulo all minimal primes of `R[T]` is nilpotent: the
coefficients of its split series lie in the nilradical of `R[T]`, which is nilpotent. -/
private theorem isNilpotent_of_forall_mem_splitKer (a : NovikovSeries R H N)
    (ha : ∀ 𝔭 ∈ minimalPrimes (AddMonoidAlgebra R T), a ∈ splitKer e (Ideal.Quotient.mk 𝔭)) :
    IsNilpotent a := by
  obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical (AddMonoidAlgebra R T)
  have hcoeff (f : F) : (splitRingHom e a).coeff f ∈ nilradical (AddMonoidAlgebra R T) := by
    rw [nilradical, ← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun 𝔭 h𝔭 =>
      Ideal.Quotient.eq_zero_iff_mem.1 ((mem_splitKer_iff e).1 (ha 𝔭 h𝔭) f)
  refine ⟨k, splitRingHom_injective e ?_⟩
  ext f
  have := coeff_pow_mem_pow hcoeff k f
  rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  rw [map_pow, this, map_zero, coeff_zero]

variable [UniqueSums F]

/-- A minimal prime of `Nov(R, H, N)` is the kernel of the reduction modulo its intersection
with `R[T]`. -/
private theorem eq_splitKer_comap {P : Ideal (NovikovSeries R H N)} (hP : P ∈ minimalPrimes _) :
    P = splitKer e (Ideal.Quotient.mk (P.comap (splitInclusion e))) := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing (AddMonoidAlgebra R T)
  obtain ⟨𝔭, -, rfl⟩ := Ideal.exists_eq_of_mem_minimalPrimes_of_inf_le
    (s := hfin.toFinset) (f := fun 𝔭 => splitKer (N := N) e (Ideal.Quotient.mk 𝔭))
    (fun 𝔭 h𝔭 => have := ((Set.Finite.mem_toFinset _).1 h𝔭).1.1
      isPrime_splitKer e _)
    (fun _ _ => bot_le)
    (fun a ha => mem_nilradical.2 <| isNilpotent_of_forall_mem_splitKer e a fun 𝔭 h𝔭 =>
      (Submodule.mem_finsetInf.1 ha) 𝔭 ((Set.Finite.mem_toFinset _).2 h𝔭)) hP
  rw [comap_splitKer, Ideal.mk_ker]

end Splitting

section MinimalPrimes

variable {R H : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup H] [AddGroup.FG H]
  {N : H →+ ℝ}

/-- **Minimal primes of a Novikov ring are detected by the torsion.** Two minimal primes of
`Nov(R, H, N)` that meet the group ring of the torsion subgroup of `H` in the same ideal are
equal. -/
theorem eq_of_mem_minimalPrimes_of_comap_eq {P Q : Ideal (NovikovSeries R H N)}
    (hP : P ∈ minimalPrimes _) (hQ : Q ∈ minimalPrimes _)
    (h : P.comap (ofAddMonoidAlgebra.comp
        (AddMonoidAlgebra.mapDomainRingHom R (AddCommGroup.torsion H).subtype)) =
      Q.comap (ofAddMonoidAlgebra.comp
        (AddMonoidAlgebra.mapDomainRingHom R (AddCommGroup.torsion H).subtype))) : P = Q := by
  classical
  -- Split `H ≃ ℤⁿ × T'` with `T'` finite; the image of `T'` lies in the torsion subgroup.
  obtain ⟨n, ι, _, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  have (i : ι) : NeZero (p i ^ k i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i ↦ ZMod (p i ^ k i)) :=
    (inferInstance : Finite (Π₀ i, ZMod (p i ^ k i)))
  let j := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (Fin n →₀ ℤ) _)
  have := Algebra.FiniteType.isNoetherianRing R
    (AddMonoidAlgebra R (DirectSum ι fun i ↦ ZMod (p i ^ k i)))
  -- The inclusion of `R[T']` factors through that of the group ring of the torsion subgroup.
  let jT : (DirectSum ι fun i ↦ ZMod (p i ^ k i)) →+ AddCommGroup.torsion H :=
    j.codRestrict _ fun t =>
      (AddCommGroup.mem_torsion _).2 (j.isOfFinAddOrder (isOfFinAddOrder_of_finite t))
  have hcomp : splitInclusion (N := N) e = (ofAddMonoidAlgebra.comp
      (AddMonoidAlgebra.mapDomainRingHom R (AddCommGroup.torsion H).subtype)).comp
        (AddMonoidAlgebra.mapDomainRingHom R jT) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun t => ?_ <;> simp [splitInclusion, jT, j]
  have h' : P.comap (splitInclusion e) = Q.comap (splitInclusion e) := by
    rw [hcomp, ← Ideal.comap_comap, h, Ideal.comap_comap]
  rw [eq_splitKer_comap e hP, eq_splitKer_comap e hQ, h']

end MinimalPrimes

section TotalQuotient

/-! ### Primes of the total rings of fractions of a finite cover -/

variable (R : Type*) {H : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [AddCommGroup H]
  [AddGroup.FG H] (N : H →+ ℝ) {K : AddSubgroup H}
  [K.FiniteIndex] (QA QB : Type*) [CommRing QA] [CommRing QB]
  [Algebra (NovikovSeries R K (N.comp K.subtype)) QA]
  [IsFractionRing (NovikovSeries R K (N.comp K.subtype)) QA]
  [Algebra (NovikovSeries R H N) QB] [IsFractionRing (NovikovSeries R H N) QB]
  [Algebra QA QB] [Algebra (NovikovSeries R K (N.comp K.subtype)) QB]
  [IsScalarTower (NovikovSeries R K (N.comp K.subtype)) QA QB]
  [IsScalarTower (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) QB]

omit [K.FiniteIndex] [IsFractionRing (NovikovSeries R K (N.comp K.subtype)) QA] in
include R N in
/-- Two primes of the total ring of fractions of the cover over the same prime of the base are
equal: they contract to minimal primes of `Nov(R, H, N)` meeting the group ring of the torsion in
the same ideal. -/
private theorem comap_algebraMap_injective_of_torsion_le (hK : AddCommGroup.torsion H ≤ K) :
    Function.Injective (PrimeSpectrum.comap (algebraMap QA QB)) := by
  have := isArtinianRing_of_isFractionRing R N QB
  intro m₁ m₂ h
  -- The inclusion of the torsion group ring factors through `Nov(R, K, N|K)`.
  let ι : AddMonoidAlgebra R (AddCommGroup.torsion H) →+* NovikovSeries R H N :=
    ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R (AddCommGroup.torsion H).subtype)
  let ιK : AddMonoidAlgebra R (AddCommGroup.torsion H) →+* NovikovSeries R K (N.comp K.subtype) :=
    ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R (AddSubgroup.inclusion hK))
  have hιK : ι = (algebraMap _ (NovikovSeries R H N)).comp ιK := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun t => ?_ <;>
      simp [ι, ιK, ofAddMonoidAlgebra_single, algebraMap_addSubgroup_eq_mapRingHom, map_single]
  have hι : (algebraMap (NovikovSeries R H N) QB).comp ι =
      (algebraMap QA QB).comp ((algebraMap _ QA).comp ιK) := by
    rw [hιK]
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  -- Both primes contract to minimal primes meeting the torsion group ring in the same ideal.
  have hmin (m : PrimeSpectrum QB) :=
    IsLocalization.comap_mem_minimalPrimes_of_krullDimLE_zero
      (M := (NovikovSeries R H N)⁰) le_rfl QB m.asIdeal
  have hcomap (m : PrimeSpectrum QB) : (m.asIdeal.comap (algebraMap _ QB)).comap ι =
      ((PrimeSpectrum.comap (algebraMap QA QB) m).asIdeal).comap ((algebraMap _ QA).comp ιK) := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, Ideal.comap_comap, hι]
  have := eq_of_mem_minimalPrimes_of_comap_eq (hmin m₁) (hmin m₂) (by rw [hcomap, hcomap, h])
  exact PrimeSpectrum.ext <|
    (IsLocalization.orderEmbedding (NovikovSeries R H N)⁰ QB).injective this

omit [IsDomain R] [IsNoetherianRing R] [AddGroup.FG H] in
include R N K in
/-- The total ring of fractions of the cover is finite free over that of the base. -/
private theorem free_and_finite : Module.Free QA QB ∧ Module.Finite QA QB :=
  ⟨IsFractionRing.free_of_free (R := NovikovSeries R K (N.comp K.subtype))
      (S := NovikovSeries R H N) (QR := QA) (T := QB),
    IsFractionRing.finite_of_free (R := NovikovSeries R K (N.comp K.subtype))
      (S := NovikovSeries R H N) (QR := QA) (T := QB)⟩

include R N in
/-- **Primes of a finite cover containing the torsion.** If a subgroup `K` of finite index contains
the torsion of `H`, then contraction from the total ring of fractions of `Nov(R, H, N)` to that of
`Nov(R, K, N|K)` is a bijection on prime ideals: over each prime of the base lies exactly one
prime of the cover. When the Novikov rings are reduced, as for `R = ℤ`, these primes index the
field components of the two total rings of fractions. -/
theorem comap_algebraMap_bijective_of_torsion_le (hK : AddCommGroup.torsion H ≤ K) :
    Function.Bijective (PrimeSpectrum.comap (algebraMap QA QB)) := by
  refine ⟨comap_algebraMap_injective_of_torsion_le R N QA QB hK, fun n => ?_⟩
  -- Lying over: `QB` is finite free over `QA`, so integral over it and faithful.
  obtain ⟨_, _⟩ := free_and_finite R N (K := K) QA QB
  have : Nontrivial QB := IsFractionRing.nontrivial (NovikovSeries R H N) QB
  have : Algebra.IsIntegral QA QB := .of_finite QA QB
  obtain ⟨m, -, hm, hmn⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral n.asIdeal (⊥ : Ideal QB) (by
      rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective QA QB)]
      exact bot_le)
  exact ⟨⟨m, hm⟩, PrimeSpectrum.ext hmn⟩

/-- **The norm of a finite cover on field components.** If a subgroup `K` of finite index contains
the torsion of `H`, then for a prime `m` of the total ring of fractions of `Nov(R, H, N)` over a
prime `n` of that of `Nov(R, K, N|K)`, the norm of `x` lies in `n` exactly when `x` lies in `m`.
So the image of the norm in the residue field `QA ⧸ n` vanishes exactly when the image of `x` in
`QB ⧸ m` does; for reduced Novikov rings, as for `R = ℤ`, these residue fields are the field
components of the total rings of fractions. -/
theorem fractionNorm_mem_iff_mem_of_torsion_le (hK : AddCommGroup.torsion H ≤ K) {n : Ideal QA}
    {m : Ideal QB} [m.IsPrime] [m.LiesOver n] (x : QB) :
    Algebra.fractionNorm (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) QA QB x ∈
      n ↔ x ∈ m := by
  obtain ⟨_, _⟩ := free_and_finite R N (K := K) QA QB
  have : n.IsPrime := by
    rw [Ideal.over_def m n]
    infer_instance
  rw [Algebra.fractionNorm_eq_norm, ← Algebra.projectiveNorm_eq_norm,
    Algebra.projectiveNorm_mem_iff]
  refine ⟨fun ⟨P, ⟨hP, _⟩, hxP⟩ => ?_, fun hx => ⟨m, ⟨inferInstance, inferInstance⟩, hx⟩⟩
  -- The prime `P` over `n` containing `x` is `m`, the only prime over `n`.
  have hPm : (⟨P, hP⟩ : PrimeSpectrum QB) = ⟨m, inferInstance⟩ :=
    comap_algebraMap_injective_of_torsion_le R N QA QB hK <| PrimeSpectrum.ext <| by
      rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, ← Ideal.under_def,
        ← Ideal.under_def, ← Ideal.over_def P n, ← Ideal.over_def m n]
  rw [PrimeSpectrum.mk.injEq] at hPm
  exact hPm ▸ hxP

end TotalQuotient

end NovikovSeries

end TauCeti
