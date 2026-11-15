/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.UpperBound.LaurentSubalgebra
public import TauCeti.RingTheory.Localization.Hartogs

/-!
# The Starfish lemma for cluster upper bounds

Let `R` be a Noetherian domain satisfying Serre's condition `(S_2)` (in particular, any Noetherian
integrally closed domain), `C` a coefficient semiring mapping to `R`, and `F` an ambient field into
which `R` embeds faithfully (`[FaithfulSMul R F]`, which includes `[IsFractionRing R F]`). Given a
family of coordinates `x : K → R` and one-step replacements `x' : K → R`, the *Starfish lemma*
states that the cluster upper bound
`upperBound C (algebraMap R F ∘ x) (fun k ↦ algebraMap R F ∘ Function.update x k (x' k))`
lies in the image of `R` inside `F` as soon as no height-one prime of `R` contains two distinct
initial coordinates `x i, x j` (`i ≠ j`) or a coordinate together with its replacement `x i, x' i`.

Geometrically, for finite `K` the initial chart and its one-step neighbors invert the products
`a_init = ∏ i, x i` and `a_k = ∏ i, Function.update x k (x' k) i`. The complement of the union of
their principal open sets `D(a_init)` and `D(a_k)` in `Spec R` is the union of the common zero loci
`V(x i, x j)` (`i ≠ j`) and `V(x i, x' i)`. When this closed complement contains no height-one
primes, `(S_2)` forces local depth at least two at every prime in the complement, and algebraic
Hartogs (`Localization.subalgebra.iInf_ofField_powers_eq_bot_of_two_le_depth`) identifies the
intersection of the nondegenerate principal localizations inside `Frac(R)` with `R`. Transporting
along `IsFractionRing.liftAlgHom` and reducing infinite index sets to finite subfamilies yields the
inclusion in full generality without finiteness or nonvanishing hypotheses on `x` and `x'`.

## Main definitions

* `TauCeti.starfishBasicOpen`: the open union in `PrimeSpectrum R` of `D(∏ i, x i)` and
  `D(∏ i, Function.update x k (x' k) i)` over `k : K`.
* `TauCeti.starfishAlgEquiv`: the `C`-algebra isomorphism between the cluster upper bound and `R`
  when `R` is generated over `C` by elements whose images lie in the upper bound.

## Main results

* `TauCeti.compl_coe_starfishBasicOpen` and
  `TauCeti.forall_height_eq_one_mem_starfishBasicOpen_iff`: the complement of `starfishBasicOpen` is
  `⋃_{i ≠ j} V(x i, x j) ∪ ⋃_i V(x i, x' i)`, so `starfishBasicOpen` contains all height-one primes
  if and only if every pair `(x i, x j)` (`i ≠ j`) and `(x i, x' i)` is coprime at height one.
* `TauCeti.iInf_laurentSubalgebra_le_range_of_two_le_depth` and
  `TauCeti.iInf_laurentSubalgebra_le_range_of_satisfiesSerreS_two`: intersection of a family of
  finite-coordinate Laurent subalgebras lies in `R` under local depth `≥ 2` or `(S_2)`.
* `TauCeti.upperBound_le_of_starfish` and
  `TauCeti.upperBound_le_of_starfish_of_isIntegrallyClosed`: the Starfish lemma in the `(S_2)` and
  normal Noetherian cases.
* `TauCeti.iInf_laurentSubalgebra_foldl_le_of_starfish`: the intersection of Laurent subalgebras
  over all finite mutation words lies in the image of `R`.
* `TauCeti.upperBound_eq_range_of_starfish`: equality with the image of `R` when a `C`-generating
  set of `R` maps into the upper bound.

## References

* A. Berenstein, S. Fomin, and A. Zelevinsky, *Cluster algebras III: Upper bounds and double Bruhat
  cells*, Duke Math. J. 126 (2005), 1–52, Theorem 2.10.
* S. Fomin, L. Williams, and A. Zelevinsky, *Introduction to Cluster Algebras. Chapter 6*,
  arXiv:2008.09189, Proposition 6.4.1 and Remark 6.4.4.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-! ### Prime-spectrum geometry of the star of charts -/

section PrimeSpectrum

variable {R K : Type*} [CommSemiring R] [Fintype K] [DecidableEq K]

/-- The union in `PrimeSpectrum R` of the principal open set `D(∏ i, x i)` of the initial chart and
the principal open sets `D(∏ i, Function.update x k (x' k) i)` of its one-step neighbors. -/
def starfishBasicOpen (x x' : K → R) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  PrimeSpectrum.basicOpen (∏ i, x i) ⊔
    ⨆ k, PrimeSpectrum.basicOpen (∏ i, Function.update x k (x' k) i)

/-- Unfolds `TauCeti.starfishBasicOpen`. -/
theorem starfishBasicOpen_def (x x' : K → R) :
    starfishBasicOpen x x' =
      PrimeSpectrum.basicOpen (∏ i, x i) ⊔
        ⨆ k, PrimeSpectrum.basicOpen (∏ i, Function.update x k (x' k) i) :=
  (rfl)

/-- A prime `p` belongs to `starfishBasicOpen x x'` if and only if either `∏ i, x i ∉ p` or some
one-step product `∏ i, Function.update x k (x' k) i` lies outside `p`. -/
@[simp]
theorem mem_starfishBasicOpen_iff {x x' : K → R} {p : PrimeSpectrum R} :
    p ∈ starfishBasicOpen x x' ↔
      ∏ i, x i ∉ p.asIdeal ∨ ∃ k, ∏ i, Function.update x k (x' k) i ∉ p.asIdeal := by
  simp [starfishBasicOpen_def]

/-- With an empty index set, the initial product is `1` and `starfishBasicOpen` is all of
`PrimeSpectrum R`. -/
@[simp]
theorem starfishBasicOpen_of_isEmpty [IsEmpty K] (x x' : K → R) :
    starfishBasicOpen x x' = ⊤ := by
  simp [starfishBasicOpen_def]

/-- A prime lies outside `starfishBasicOpen x x'` if and only if it contains either two distinct
initial coordinates `x i, x j` (`i ≠ j`) or an initial coordinate together with its replacement
`x i, x' i`. -/
theorem notMem_starfishBasicOpen_iff {x x' : K → R} {p : PrimeSpectrum R} :
    p ∉ starfishBasicOpen x x' ↔
      (∃ i j, i ≠ j ∧ x i ∈ p.asIdeal ∧ x j ∈ p.asIdeal) ∨
        ∃ i, x i ∈ p.asIdeal ∧ x' i ∈ p.asIdeal := by
  rw [mem_starfishBasicOpen_iff, not_or, not_not, not_exists]
  simp_rw [not_not, p.isPrime.prod_mem_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hxi⟩, hupd⟩
    obtain ⟨j, hxj⟩ := hupd i
    by_cases hji : j = i
    · subst j
      rw [Function.update_self] at hxj
      exact Or.inr ⟨i, hxi, hxj⟩
    · rw [Function.update_of_ne hji] at hxj
      exact Or.inl ⟨i, j, Ne.symm hji, hxi, hxj⟩
  · rintro (⟨i, j, hij, hxi, hxj⟩ | ⟨i, hxi, hx'i⟩)
    · refine ⟨⟨i, hxi⟩, fun k ↦ ?_⟩
      by_cases hki : k = i
      · subst k
        exact ⟨j, by rwa [Function.update_of_ne hij.symm]⟩
      · exact ⟨i, by rwa [Function.update_of_ne (Ne.symm hki)]⟩
    · refine ⟨⟨i, hxi⟩, fun k ↦ ?_⟩
      by_cases hki : k = i
      · subst k
        exact ⟨i, by rwa [Function.update_self]⟩
      · exact ⟨i, by rwa [Function.update_of_ne (Ne.symm hki)]⟩

/-- Pairwise non-containment characterization of membership in `starfishBasicOpen x x'`. -/
theorem mem_starfishBasicOpen_iff_forall {x x' : K → R} {p : PrimeSpectrum R} :
    p ∈ starfishBasicOpen x x' ↔
      (∀ i j, i ≠ j → x i ∉ p.asIdeal ∨ x j ∉ p.asIdeal) ∧
        ∀ i, x i ∉ p.asIdeal ∨ x' i ∉ p.asIdeal := by
  rw [← not_iff_not, notMem_starfishBasicOpen_iff, not_and_or]
  refine or_congr ?_ (by push Not; rfl)
  push Not
  rfl

/-- The complement of `starfishBasicOpen x x'` in `PrimeSpectrum R` is the union of the common zero
loci `V(x i, x j)` for `i ≠ j` and `V(x i, x' i)` for `i : K`. -/
theorem compl_coe_starfishBasicOpen (x x' : K → R) :
    (starfishBasicOpen x x' : Set (PrimeSpectrum R))ᶜ =
      (⋃ (i : K) (j : K) (_ : i ≠ j), PrimeSpectrum.zeroLocus {x i, x j}) ∪
        ⋃ i : K, PrimeSpectrum.zeroLocus {x i, x' i} := by
  ext p
  simp only [Set.mem_compl_iff, SetLike.mem_coe, notMem_starfishBasicOpen_iff, Set.mem_union,
    Set.mem_iUnion, PrimeSpectrum.mem_zeroLocus, Set.insert_subset_iff, Set.singleton_subset_iff,
    exists_prop]

end PrimeSpectrum

/-- All height-one primes lie in `starfishBasicOpen x x'` if and only if no height-one prime
contains both members of any pair `(x i, x j)` (`i ≠ j`) or `(x i, x' i)`. -/
theorem forall_height_eq_one_mem_starfishBasicOpen_iff {R K : Type*} [CommRing R] [Fintype K]
    [DecidableEq K] (x x' : K → R) :
    (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∈ starfishBasicOpen x x') ↔
      ∀ p : Ideal R, p.IsPrime → p.height = 1 →
        (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ ∀ i, x i ∉ p ∨ x' i ∉ p := by
  constructor
  · intro h p hp h1
    exact mem_starfishBasicOpen_iff_forall.mp (h ⟨p, hp⟩ h1)
  · intro h p h1
    exact mem_starfishBasicOpen_iff_forall.mpr (h p.asIdeal p.isPrime h1)

/-! ### Finite Laurent chart families and algebraic Hartogs -/

section FiniteFamilies

/-- When `∏ i, x i` generates a submonoid of non-zero-divisors in `R`, the Laurent subalgebra over
`C` generated by the images of `x` in the fraction field `F` lies in the principal localization
`R[(∏ i, x i)⁻¹] ⊆ F`. -/
theorem laurentSubalgebra_le_ofField_powers_prod (C : Type*) {R F I : Type*} [CommSemiring C]
    [CommRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F] [IsScalarTower C R F]
    [IsFractionRing R F] [Fintype I] (x : I → R) (hx : Submonoid.powers (∏ i, x i) ≤ R⁰) :
    laurentSubalgebra C (algebraMap R F ∘ x) ≤
      (Localization.subalgebra.ofField F (Submonoid.powers (∏ i, x i)) hx).restrictScalars C := by
  refine (laurentSubalgebra_le_iff C).mpr ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · exact Subalgebra.algebraMap_mem
      (Localization.subalgebra.ofField F (Submonoid.powers (∏ i, x i)) hx) (x i)
  · exact Localization.subalgebra.inv_algebraMap_mem_ofField_powers_prod Finset.univ x hx
      (Finset.mem_univ i)

private theorem iInf_laurentSubalgebra_le_range_of_two_le_depth_isFractionRing
    {C R K T : Type*} [CommSemiring C] [CommRing R] [IsNoetherianRing R] [Field K]
    [Algebra C R] [Algebra C K] [Algebra R K] [IsScalarTower C R K] [IsFractionRing R K]
    {I : T → Type*} [∀ t, Fintype (I t)] (x : ∀ t, I t → R) (hx : ∀ t i, x t i ≠ 0)
    (hdepth : ∀ (p : Ideal R) [p.IsPrime], (∀ t, ∏ i, x t i ∈ p) →
      2 ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    (⨅ t, laurentSubalgebra C (algebraMap R K ∘ x t)) ≤
      (IsScalarTower.toAlgHom C R K).range := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain
  have hpow (t : T) : Submonoid.powers (∏ i, x t i) ≤ R⁰ :=
    Submonoid.powers_le.mpr
      (Submonoid.prod_mem R⁰ fun i _ ↦ mem_nonZeroDivisors_of_ne_zero (hx t i))
  intro z hz
  rw [Algebra.mem_iInf] at hz
  have hmem :
      z ∈ ⨅ t, Localization.subalgebra.ofField K (Submonoid.powers (∏ i, x t i)) (hpow t) :=
    Algebra.mem_iInf.mpr fun t ↦ laurentSubalgebra_le_ofField_powers_prod C (x t) (hpow t) (hz t)
  rw [Localization.subalgebra.iInf_ofField_powers_eq_bot_of_two_le_depth _ hpow hdepth,
    Algebra.mem_bot] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact (IsScalarTower.toAlgHom C R K).mem_range.mpr ⟨r, hr⟩

private theorem iInf_laurentSubalgebra_le_range_of_two_le_depth_ne_zero {C R F T : Type*}
    [CommSemiring C] [CommRing R] [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F]
    [Algebra R F] [IsScalarTower C R F] [FaithfulSMul R F] [Nonempty T] {I : T → Type*}
    [∀ t, Fintype (I t)] (x : ∀ t, I t → R) (hx : ∀ t i, x t i ≠ 0)
    (hdepth : ∀ (p : Ideal R) [p.IsPrime], (∀ t, ∏ i, x t i ∈ p) →
      2 ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    (⨅ t, laurentSubalgebra C (algebraMap R F ∘ x t)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R F).isDomain
  let K := FractionRing R
  let φR : K →ₐ[R] F :=
    IsFractionRing.liftAlgHom (K := K) (g := Algebra.ofId R F)
      (FaithfulSMul.algebraMap_injective R F)
  let φ : K →ₐ[C] F := φR.restrictScalars C
  have hcomp (t : T) : φ ∘ (algebraMap R K ∘ x t) = algebraMap R F ∘ x t :=
    funext fun i ↦ φR.commutes (x t i)
  obtain ⟨t₀⟩ := ‹Nonempty T›
  intro y hy
  rw [Algebra.mem_iInf] at hy
  have hy₀ : y ∈ (laurentSubalgebra C (algebraMap R K ∘ x t₀)).map φ := by
    rw [map_laurentSubalgebra, hcomp]
    exact hy t₀
  obtain ⟨z, -, rfl⟩ := hy₀
  have hz : z ∈ ⨅ t, laurentSubalgebra C (algebraMap R K ∘ x t) := by
    refine Algebra.mem_iInf.mpr fun t ↦ ?_
    have hzt := hy t
    rw [← hcomp t, ← map_laurentSubalgebra] at hzt
    obtain ⟨z', hz', hzz'⟩ := hzt
    exact φ.toRingHom.injective hzz' ▸ hz'
  obtain ⟨r, hr⟩ := (IsScalarTower.toAlgHom C R K).mem_range.mp
    (iInf_laurentSubalgebra_le_range_of_two_le_depth_isFractionRing x hx hdepth hz)
  refine (IsScalarTower.toAlgHom C R F).mem_range.mpr ⟨r, ?_⟩
  rw [IsScalarTower.toAlgHom_apply, ← φR.commutes r, ← IsScalarTower.toAlgHom_apply C R K r, hr]
  rfl

/-- **Algebraic Hartogs for Laurent chart families.** Let `R` be a Noetherian ring embedding
faithfully into a field `F` over `C`, and let `x : ∀ t, I t → R` be a family of finite coordinate
tuples. If `depth R_p ≥ 2` at every prime `p` containing each product `∏ i, x t i`, then
`⋂_t C[x_{t,i}^{±1}]` lies in the image of `R` in `F`. -/
theorem iInf_laurentSubalgebra_le_range_of_two_le_depth {C R F T : Type*} [CommSemiring C]
    [CommRing R] [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] {I : T → Type*} [∀ t, Fintype (I t)]
    (x : ∀ t, I t → R)
    (hdepth : ∀ (p : Ideal R) [p.IsPrime], (∀ t, ∏ i, x t i ∈ p) →
      2 ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    (⨅ t, laurentSubalgebra C (algebraMap R F ∘ x t)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R F).isDomain
  let T' := {t : T // ∀ i, x t i ≠ 0}
  have hprod_mem (p : Ideal R) (hall : ∀ t : T', ∏ i, x t.1 i ∈ p) (t : T) :
      ∏ i, x t i ∈ p := by
    by_cases ht : ∀ i, x t i ≠ 0
    · exact hall ⟨t, ht⟩
    · push Not at ht
      obtain ⟨i, hi⟩ := ht
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
      exact p.zero_mem
  have : Nonempty T' := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    -- At the minimal prime `(0)`, `R_{(0)}` is a field of depth `0`, contradicting `2 ≤ depth`.
    have h20 := hdepth ⊥ (hprod_mem ⊥ fun t ↦ isEmptyElim t)
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal R)) = ⊥ := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal R)
        (Localization.AtPrime (⊥ : Ideal R)), Ideal.map_bot]
    have h0 : IsLocalRing.depth
        (ModuleCat.of (Localization.AtPrime (⊥ : Ideal R))
          (Localization.AtPrime (⊥ : Ideal R))) = 0 :=
      by_contra fun h ↦ IsLocalRing.maximalIdeal_ne_bot_of_depth_ne_zero h hmax
    exact absurd (h0 ▸ h20) (by decide)
  exact (le_iInf fun t : T' ↦ iInf_le _ t.1).trans
    (iInf_laurentSubalgebra_le_range_of_two_le_depth_ne_zero (fun t : T' ↦ x t.1)
      (fun t ↦ t.2) fun p _ hall ↦ hdepth p (hprod_mem p hall))

/-- **Laurent chart intersection under `(S_2)`.** Over a Noetherian ring `R` satisfying `(S_2)` and
embedding faithfully into a field `F` over `C`, if `x : ∀ t, I t → R` is a nonempty family of
finite coordinate tuples whose products `∏ i, x t i` do not simultaneously vanish at any height-one
prime, then `⋂_t C[x_{t,i}^{±1}]` lies in the image of `R` in `F`. -/
theorem iInf_laurentSubalgebra_le_range_of_satisfiesSerreS_two {C R F T : Type*} [CommSemiring C]
    [CommRing R] [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] (hS₂ : Module.SatisfiesSerreS 2 R R) [Nonempty T]
    {I : T → Type*} [∀ t, Fintype (I t)] (x : ∀ t, I t → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ t, ∏ i, x t i ∉ p) :
    (⨅ t, laurentSubalgebra C (algebraMap R F ∘ x t)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R F).isDomain
  by_cases hT' : ∃ t₀ : T, ∀ i, x t₀ i ≠ 0
  · obtain ⟨t₀, ht₀⟩ := hT'
    have hprod₀ : ∏ i, x t₀ i ∈ R⁰ :=
      Submonoid.prod_mem R⁰ fun i _ ↦ mem_nonZeroDivisors_of_ne_zero (ht₀ i)
    refine iInf_laurentSubalgebra_le_range_of_two_le_depth x fun p hp hall ↦ ?_
    have hp1 : 1 ≤ p.height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hprod₀).trans
        (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem p).mpr (hall t₀)))
    have hne1 : p.height ≠ 1 := fun h1 ↦ by
      obtain ⟨t, ht⟩ := hcover p hp h1
      exact ht (hall t)
    have hp2 : 2 ≤ p.height :=
      (ENat.add_one_le_iff ENat.one_ne_top).mpr (lt_of_le_of_ne hp1 hne1.symm)
    have hdim : 2 ≤ ringKrullDim (Localization.AtPrime p) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
      exact WithBot.coe_le_coe.mpr hp2
    have hSp := (Module.satisfiesSerreS_self_iff.mp hS₂) p
    rw [min_eq_left (by exact_mod_cast hdim), ← WithBot.coe_natCast, WithBot.coe_le_coe] at hSp
    exact_mod_cast hSp
  · -- Every tuple has a zero entry, so `hcover` rules out height-one primes and `R` is a field.
    push Not at hT'
    obtain ⟨t₀⟩ := ‹Nonempty T›
    refine (iInf_le _ t₀).trans ((laurentSubalgebra_le_iff C).mpr ⟨fun j ↦ ?_, fun j ↦ ?_⟩)
    · exact (IsScalarTower.toAlgHom C R F).mem_range.mpr ⟨x t₀ j, rfl⟩
    · by_cases hj : x t₀ j = 0
      · simp [hj, zero_mem]
      · have hu : IsUnit (x t₀ j) := by
          by_contra hnu
          have hne : Ideal.span {x t₀ j} ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hnu
          have : Nontrivial (R ⧸ Ideal.span {x t₀ j}) := Ideal.Quotient.nontrivial_iff.mpr hne
          obtain ⟨P, hPass, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
            (1 : R ⧸ Ideal.span {x t₀ j}) one_ne_zero
          have hP1 := hS₂.height_eq_one_of_isAssociatedPrime_quotient_span_singleton
            (mem_nonZeroDivisors_of_ne_zero hj) hPass
          obtain ⟨t, ht⟩ := hcover P hPass.isPrime hP1
          obtain ⟨i, hi⟩ := hT' t
          exact ht (Finset.prod_eq_zero (Finset.mem_univ i) hi ▸ P.zero_mem)
        obtain ⟨u, hu⟩ := hu
        refine (IsScalarTower.toAlgHom C R F).mem_range.mpr ⟨↑u⁻¹, ?_⟩
        rw [IsScalarTower.toAlgHom_apply, Function.comp_apply, ← hu]
        simp

end FiniteFamilies

/-! ### The Starfish lemma -/

section Starfish

private theorem upperBound_le_of_starfish_finite {C R F K : Type*} [CommSemiring C]
    [CommRing R] [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [Finite K] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  cases nonempty_fintype K
  let family : Option K → K → R := fun o ↦ Option.elim o x fun k ↦ Function.update x k (x' k)
  have heq : upperBound C (algebraMap R F ∘ x)
      (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) =
      ⨅ o : Option K, laurentSubalgebra C (algebraMap R F ∘ family o) := by
    rw [upperBound_def, iInf_option]
    rfl
  rw [heq]
  refine iInf_laurentSubalgebra_le_range_of_satisfiesSerreS_two hS₂ family fun p hp h1 ↦ ?_
  have hstar := (forall_height_eq_one_mem_starfishBasicOpen_iff x x').mpr hcover ⟨p, hp⟩ h1
  rw [mem_starfishBasicOpen_iff] at hstar
  exact Option.exists.mpr hstar

/-- **Starfish lemma** (`(S_2)` case). Let `R` be a Noetherian ring satisfying `(S_2)` that embeds
faithfully into a field `F` over `C` (for instance `F = FractionRing R`). If no height-one prime of
`R` contains two distinct coordinates `x i, x j` (`i ≠ j`) or a coordinate together with its
one-step replacement `x i, x' i`, then the cluster upper bound over `C` lies in the image of `R` in
`F`. Neither finiteness of `K` nor nonvanishing of `x` and `x'` is required. -/
theorem upperBound_le_of_starfish {C R F K : Type*} [CommSemiring C] [CommRing R]
    [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  intro z hz
  rw [mem_upperBound_iff] at hz
  obtain ⟨S₀, hS₀⟩ := exists_finset_mem_laurentSubalgebra hz.1
  choose T hT using fun k ↦ exists_finset_mem_laurentSubalgebra (hz.2 k)
  let M : Finset K := S₀ ∪ S₀.biUnion T
  let xM : M → R := fun i ↦ x i
  let x'M : M → R := fun i ↦ x' i
  have hSM : S₀ ⊆ M := Finset.subset_union_left
  have hzM₀ : z ∈ laurentSubalgebra C (algebraMap R F ∘ xM) :=
    laurentSubalgebra_comp_le C (algebraMap R F ∘ xM) (Set.inclusion hSM) hS₀
  have hzM (k : M) : z ∈ laurentSubalgebra C (algebraMap R F ∘ Function.update xM k (x'M k)) := by
    by_cases hk : (k : K) ∈ S₀
    · have hTM : T k ≤ M := (Finset.subset_biUnion_of_mem T hk).trans Finset.subset_union_right
      have hfun : (algebraMap R F ∘ Function.update xM k (x'M k)) ∘ Set.inclusion hTM =
          fun j : T k ↦ algebraMap R F (Function.update x k (x' k) j) := by
        ext j
        by_cases hjk : (j : K) = k
        · have hjM : Set.inclusion hTM j = k := Subtype.ext hjk
          simp [xM, x'M, hjM, hjk]
        · have hjM : Set.inclusion hTM j ≠ k := fun h ↦ hjk (congrArg Subtype.val h)
          simp [xM, x'M, hjM, hjk]
      exact laurentSubalgebra_comp_le C (algebraMap R F ∘ Function.update xM k (x'M k))
        (Set.inclusion hTM) (hfun.symm ▸ hT k)
    · have hfun : (algebraMap R F ∘ Function.update xM k (x'M k)) ∘ Set.inclusion hSM =
          fun j : S₀ ↦ algebraMap R F (x j) := by
        ext j
        have hjM : Set.inclusion hSM j ≠ k := fun h ↦ hk (congrArg Subtype.val h ▸ j.2)
        simp [xM, hjM]
      exact laurentSubalgebra_comp_le C (algebraMap R F ∘ Function.update xM k (x'M k))
        (Set.inclusion hSM) (hfun.symm ▸ hS₀)
  have hcovM : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j : M, i ≠ j → xM i ∉ p ∨ xM j ∉ p) ∧ (∀ i : M, xM i ∉ p ∨ x'M i ∉ p) :=
    fun p hp h1 ↦ ⟨fun i j hij ↦ (hcover p hp h1).1 i j (Subtype.coe_ne_coe.mpr hij),
      fun i ↦ (hcover p hp h1).2 i⟩
  exact upperBound_le_of_starfish_finite hS₂ xM x'M hcovM ((mem_upperBound_iff C).mpr ⟨hzM₀, hzM⟩)

/-- **Starfish lemma for normal Noetherian domains.** Over a Noetherian integrally closed domain `R`
embedding faithfully into a field `F` over `C`, height-one coprimality of the star pairs implies
that the cluster upper bound lies in the image of `R` in `F`. -/
theorem upperBound_le_of_starfish_of_isIntegrallyClosed {C R F K : Type*} [CommSemiring C]
    [CommRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra C R]
    [Algebra C F] [Algebra R F] [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R F).isDomain
  exact upperBound_le_of_starfish satisfiesSerreS_two_of_isIntegrallyClosed x x' hcover

end Starfish

/-! ### Reachable mutation words and algebra realizations -/

section Realization

/-- Since the empty word and singleton words reach the initial chart and its one-step neighbors, the
intersection of Laurent subalgebras over all finite mutation words lies in the image of `R` whenever
the initial star satisfies the Starfish hypotheses. -/
theorem iInf_laurentSubalgebra_foldl_le_of_starfish {C R F K V : Type*} [CommSemiring C]
    [CommRing R] [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (μ : K → V → V) (coord : V → K → F) (s : V)
    (x x' : K → R) (hinit : coord s = algebraMap R F ∘ x)
    (hstep : ∀ k, coord (μ k s) = algebraMap R F ∘ Function.update x k (x' k))
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p)) :
    (⨅ w : List K, laurentSubalgebra C (coord (w.foldl (fun t k ↦ μ k t) s))) ≤
      (IsScalarTower.toAlgHom C R F).range := by
  refine (Mutation.iInf_foldl_le_upperBound μ (fun t ↦ laurentSubalgebra C (coord t)) s).trans ?_
  rw [Mutation.upperBound_laurentSubalgebra, hinit]
  simp_rw [hstep]
  exact upperBound_le_of_starfish hS₂ x x' hcover

/-- **Starfish equality criterion.** When `R` is generated as a `C`-algebra by a set `s` whose image
lies in the cluster upper bound, the Starfish hypotheses identify the cluster upper bound with the
image of `R` in `F`. -/
theorem upperBound_eq_range_of_starfish {C R F K : Type*} [CommSemiring C] [CommRing R]
    [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p))
    {s : Set R} (hs : Algebra.adjoin C s = ⊤)
    (hgen : algebraMap R F '' s ⊆
      (upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) : Set F)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) =
      (IsScalarTower.toAlgHom C R F).range := by
  refine le_antisymm (upperBound_le_of_starfish hS₂ x x' hcover) ?_
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  exact hgen

/-- **Starfish `C`-algebra equivalence.** Under the hypotheses of
`TauCeti.upperBound_eq_range_of_starfish`, the cluster upper bound is isomorphic as a `C`-algebra to
`R` via `algebraMap R F`. -/
noncomputable def starfishAlgEquiv {C R F K : Type*} [CommSemiring C] [CommRing R]
    [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p))
    {s : Set R} (hs : Algebra.adjoin C s = ⊤)
    (hgen : algebraMap R F '' s ⊆
      (upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) : Set F)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) ≃ₐ[C] R :=
  ((AlgEquiv.ofInjective (IsScalarTower.toAlgHom C R F)
      (FaithfulSMul.algebraMap_injective R F)).trans
    (Subalgebra.equivOfEq _ _
      (upperBound_eq_range_of_starfish hS₂ x x' hcover hs hgen).symm)).symm

/-- The inverse of `TauCeti.starfishAlgEquiv` embeds `R` into `F` via `algebraMap R F`. -/
@[simp]
theorem coe_starfishAlgEquiv_symm_apply {C R F K : Type*} [CommSemiring C] [CommRing R]
    [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p))
    {s : Set R} (hs : Algebra.adjoin C s = ⊤)
    (hgen : algebraMap R F '' s ⊆
      (upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) : Set F))
    (r : R) :
    ((starfishAlgEquiv hS₂ x x' hcover hs hgen).symm r : F) = algebraMap R F r := by
  rw [starfishAlgEquiv]
  rfl

/-- Applying `algebraMap R F` after `TauCeti.starfishAlgEquiv` recovers the underlying element of
`F`. -/
@[simp]
theorem algebraMap_starfishAlgEquiv_apply {C R F K : Type*} [CommSemiring C] [CommRing R]
    [IsNoetherianRing R] [Field F] [Algebra C R] [Algebra C F] [Algebra R F]
    [IsScalarTower C R F] [FaithfulSMul R F] [DecidableEq K]
    (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p))
    {s : Set R} (hs : Algebra.adjoin C s = ⊤)
    (hgen : algebraMap R F '' s ⊆
      (upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) : Set F))
    (u : upperBound C (algebraMap R F ∘ x)
      (fun k ↦ algebraMap R F ∘ Function.update x k (x' k))) :
    algebraMap R F (starfishAlgEquiv hS₂ x x' hcover hs hgen u) = (u : F) := by
  let e := starfishAlgEquiv hS₂ x x' hcover hs hgen
  rw [← coe_starfishAlgEquiv_symm_apply hS₂ x x' hcover hs hgen (e u), e.symm_apply_apply]

end Realization

/-! ### Checks -/

/-- Direct compatibility with `[IsFractionRing R F]` callers over `[Finite K]`. -/
example {C R F K : Type*} [CommRing C] [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field F]
    [Algebra C R] [Algebra C F] [Algebra R F] [IsScalarTower C R F] [IsFractionRing R F]
    [Finite K] [DecidableEq K] (hS₂ : Module.SatisfiesSerreS 2 R R) (x x' : K → R)
    (hcover : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      (∀ i j, i ≠ j → x i ∉ p ∨ x j ∉ p) ∧ (∀ i, x i ∉ p ∨ x' i ∉ p)) :
    upperBound C (algebraMap R F ∘ x)
        (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) ≤
      (IsScalarTower.toAlgHom C R F).range :=
  upperBound_le_of_starfish hS₂ x x' hcover

/-- In rank zero (`K = Empty`) with `C = R`, the star basic open is `⊤` and the upper bound equals
the image of `R` in `F`. -/
example {R F : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (hS₂ : Module.SatisfiesSerreS 2 R R)
    (x x' : Empty → R) :
    starfishBasicOpen x x' = ⊤ ∧
      upperBound R (algebraMap R F ∘ x)
          (fun k ↦ algebraMap R F ∘ Function.update x k (x' k)) =
        (IsScalarTower.toAlgHom R R F).range :=
  ⟨starfishBasicOpen_of_isEmpty x x',
    upperBound_eq_range_of_starfish hS₂ x x' (fun _ _ _ ↦ ⟨isEmptyElim, isEmptyElim⟩)
      (s := ∅) (eq_top_iff.mpr fun r _ ↦ Subalgebra.algebraMap_mem _ r) (by simp)⟩

/-- In rank one (`K = Unit`), the complement of `starfishBasicOpen` is the single common zero locus
`V(a, b)` of the coordinate and its replacement. -/
example {R : Type*} [CommSemiring R] (a b : R) :
    (starfishBasicOpen (fun _ : Unit ↦ a) (fun _ : Unit ↦ b) : Set (PrimeSpectrum R))ᶜ =
      PrimeSpectrum.zeroLocus {a, b} := by
  simp [compl_coe_starfishBasicOpen, Set.iUnion_const]

end TauCeti
