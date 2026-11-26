/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Genericity.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
import TauCeti.NumberTheory.Chebotarev.PrimesCongruent
import TauCeti.NumberTheory.Chebotarev.SplitsCompletely
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.NumberTheory.NumberField.Frobenius.Tower
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic
import TauCeti.NumberTheory.NumberField.SplittingField

/-!
# Decomposed generic primes

Let `F` be a number field, `k` a field and `r : Gal(L/F) → GL_n(k)` a representation of the
Galois group of a finite Galois extension `L / F`; every continuous representation of the
absolute Galois group of `F` on a finite-dimensional vector space over a finite field factors
through such a finite quotient. Following Allen, Calegari, Caraiani, Gee, Helm, Le Hung, Newton,
Scholze, Taylor and Thorne, a rational prime `p` is *decomposed generic* for `r` if `p` is a unit
in `k`, `p` splits completely in `F`, and at every prime `Q` of `L` above `p` the inertia group
acts trivially and the eigenvalues `α₁, …, αₙ` of a Frobenius element at `Q`, listed with
multiplicity, satisfy `αᵢ / αⱼ ≠ p` for `i ≠ j` (`MonoidHom.IsGenericAt`). Since `p` splits
completely, the residue fields of `F` above `p` have `p` elements, so `p` is the residue
cardinality in the local genericity condition at every such prime. The representation is
*decomposed generic* if some prime is.

This is the hypothesis on residual representations under which those authors control the
torsion in the cohomology of locally symmetric spaces for `GL_n` over CM fields. The main result
of this file is that one witness produces infinitely many: if `k` has positive characteristic
`ℓ`, the set of decomposed generic primes for `r` is either empty or infinite.

The proof is the Chebotarev argument of ACC+ Lemma 4.3.2. Embed `L` in a finite Galois extension
`N / ℚ` containing the `ℓ`-th roots of unity, and let `σ ∈ Gal(N/ℚ)` be a Frobenius element at a
prime of `N` above a witness `p`. Every rational prime `p' ≠ ℓ` unramified in `N` whose
Frobenius class is that of `σ` is again a witness:

* the decomposition groups above `p` fix `F` because `p` splits completely in `F`, so the
  conjugates of `σ`, which generate the decomposition groups above `p'`, fix `F` too, and `p'`
  splits completely in `F`;
* the Frobenius elements of `L / F` above `p'` are restrictions of conjugates of `σ`, hence
  Frobenius elements above `p`, at which the eigenvalue condition holds;
* `σ` raises the `ℓ`-th roots of unity both to the `p`-th and to the `p'`-th power, so
  `p ≡ p' (mod ℓ)` and the two primes are the same element of `k`.

The Chebotarev density theorem provides infinitely many such `p'`. The ramified prime `p` itself
need not lie in this Frobenius fibre: only the residue action of `σ` at one prime above `p` is
used.

## Main definitions

* `MonoidHom.IsDecomposedGenericPrime r p`: the rational prime `p` is decomposed generic for
  `r : Gal(L/F) →* GL n k`.
* `MonoidHom.IsDecomposedGeneric r`: some rational prime is decomposed generic for `r`.

## Main results

* `MonoidHom.IsDecomposedGenericPrime.absNorm_eq`: the primes of `F` above a decomposed generic
  prime `p` have norm `p`.
* `MonoidHom.isDecomposedGenericPrime_map_iff`: the condition is invariant under extension of
  the coefficient field.
* `MonoidHom.IsDecomposedGeneric.infinite_setOf_isDecomposedGenericPrime`: in positive
  characteristic, a decomposed generic representation has infinitely many decomposed generic
  primes.
* `MonoidHom.IsDecomposedGeneric.exists_isDecomposedGenericPrime_notMem`: so witnesses can avoid
  any finite set of primes.

## References

* P. B. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor, J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  Definition 4.3.1 and Lemma 4.3.2.
-/

public section

open Ideal Module NumberField

namespace MonoidHom

variable {F L k n : Type*} [Field F] [NumberField F] [Field L] [Algebra F L] [Field k] [Fintype n]
  [DecidableEq n]

/-- A rational prime `p` is **decomposed generic** for a representation `r : Gal(L/F) →* GL n k`
if `p` is a unit in `k`, `p` splits completely in `F` (there are `[F : ℚ]` primes of `𝓞 F` above
`p`), and at every prime `Q` of `𝓞 L` above `p` the representation is generic at `p` with respect
to the inertia group of `Q`, at every arithmetic Frobenius element of `Gal(L/F)` at `Q`
(`MonoidHom.IsGenericAt`): the inertia group acts trivially, and no ratio of two eigenvalues of
the Frobenius matrix, listed with multiplicity, is `p`.

Complete splitting makes `p` the residue cardinality at every prime of `F` above `p`. Testing
arithmetic rather than geometric Frobenius elements gives the same condition
(`MonoidHom.isGenericAt_inv_iff`). -/
def IsDecomposedGenericPrime (r : Gal(L/F) →* GL n k) (p : ℕ) : Prop :=
  p.Prime ∧ (p : k) ≠ 0 ∧ ((span {(p : ℤ)}).primesOver (𝓞 F)).ncard = finrank ℚ F ∧
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (σ : Gal(L/F)),
      IsArithFrobAt (𝓞 F) σ Q → r.IsGenericAt (Q.inertia Gal(L/F)) σ p

/-- A representation `r : Gal(L/F) →* GL n k` is **decomposed generic** if some rational prime is
decomposed generic for it (`MonoidHom.IsDecomposedGenericPrime`). -/
def IsDecomposedGeneric (r : Gal(L/F) →* GL n k) : Prop :=
  ∃ p, r.IsDecomposedGenericPrime p

variable {r : Gal(L/F) →* GL n k} {p : ℕ}

/-- The defining condition of `MonoidHom.IsDecomposedGeneric`. -/
theorem isDecomposedGeneric_iff : r.IsDecomposedGeneric ↔ ∃ p, r.IsDecomposedGenericPrime p :=
  Iff.rfl

/-- A decomposed generic prime is prime. -/
theorem IsDecomposedGenericPrime.prime (h : r.IsDecomposedGenericPrime p) : p.Prime :=
  h.1

/-- A decomposed generic prime is a unit in the coefficient field: it differs from its
characteristic. -/
theorem IsDecomposedGenericPrime.natCast_ne_zero (h : r.IsDecomposedGenericPrime p) :
    (p : k) ≠ 0 :=
  h.2.1

/-- A decomposed generic prime splits completely in `F`. -/
theorem IsDecomposedGenericPrime.ncard_primesOver_eq_finrank (h : r.IsDecomposedGenericPrime p) :
    ((span {(p : ℤ)}).primesOver (𝓞 F)).ncard = finrank ℚ F :=
  h.2.2.1

/-- The primes of `F` above a decomposed generic prime `p` have absolute norm `p`: `p` is the
residue cardinality in the local genericity conditions. -/
theorem IsDecomposedGenericPrime.absNorm_eq (h : r.IsDecomposedGenericPrime p)
    (𝔮 : Ideal (𝓞 F)) [𝔮.IsPrime] [𝔮.LiesOver (span {(p : ℤ)})] : absNorm 𝔮 = p :=
  absNorm_eq_of_ncard_primesOver_eq_finrank 𝔮 h.ncard_primesOver_eq_finrank

/-- The defining conditions of `MonoidHom.IsDecomposedGenericPrime`. -/
theorem isDecomposedGenericPrime_iff :
    r.IsDecomposedGenericPrime p ↔
      p.Prime ∧ (p : k) ≠ 0 ∧ ((span {(p : ℤ)}).primesOver (𝓞 F)).ncard = finrank ℚ F ∧
        ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (σ : Gal(L/F)),
          IsArithFrobAt (𝓞 F) σ Q → r.IsGenericAt (Q.inertia Gal(L/F)) σ p :=
  Iff.rfl

/-- At every prime `Q` of `L` above a decomposed generic prime `p`, the representation is generic
at `p` with respect to the inertia group of `Q`, at every arithmetic Frobenius element at `Q`. -/
theorem IsDecomposedGenericPrime.isGenericAt (h : r.IsDecomposedGenericPrime p)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] {σ : Gal(L/F)}
    (hσ : IsArithFrobAt (𝓞 F) σ Q) : r.IsGenericAt (Q.inertia Gal(L/F)) σ p :=
  h.2.2.2 Q σ hσ

/-- **Decomposed genericity is invariant under extension of scalars.** A rational prime is
decomposed generic for `r` exactly when it is decomposed generic for `r` with coefficients
extended to a field extension `K` of `k`. -/
@[simp]
theorem isDecomposedGenericPrime_map_iff {K : Type*} [Field K] [Algebra k K] :
    ((Matrix.GeneralLinearGroup.map (algebraMap k K)).comp r).IsDecomposedGenericPrime p ↔
      r.IsDecomposedGenericPrime p := by
  have hcast : (p : K) = algebraMap k K p := (map_natCast (algebraMap k K) p).symm
  simp only [isDecomposedGenericPrime_iff, hcast, isGenericAt_map_iff, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff]

/-- **Decomposed genericity of a representation is invariant under extension of scalars.** -/
@[simp]
theorem isDecomposedGeneric_map_iff {K : Type*} [Field K] [Algebra k K] :
    ((Matrix.GeneralLinearGroup.map (algebraMap k K)).comp r).IsDecomposedGeneric ↔
      r.IsDecomposedGeneric := by
  simp only [isDecomposedGeneric_iff, isDecomposedGenericPrime_map_iff]

variable [NumberField L] [IsGalois F L]

/-! ### The Chebotarev argument

Throughout, `N` is a finite Galois extension of `ℚ` containing `L`. -/

section Chebotarev

open scoped Pointwise

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]

variable [Algebra F N] [Algebra L N] [IsScalarTower F L N]

omit [NumberField L] [IsGalois ℚ N] in
/-- **Frobenius elements above a decomposed generic prime.** If `p` is decomposed generic for `r`
and an element `ψ` of `Gal(N/F)` is, read in `Gal(N/ℚ)`, an arithmetic Frobenius element at a
prime of `N` above `p`, then `r` of its restriction to `L` is generic at `p`. -/
private theorem isGenericAt_restrictNormal_of_isArithFrobAt {r : Gal(L/F) →* GL n k} {p : ℕ}
    (hp : r.IsDecomposedGenericPrime p) (P : Ideal (𝓞 N)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] {ψ : Gal(N/F)} (hψ : IsArithFrobAt ℤ (ψ.restrictScalars ℚ) P) :
    (r (ψ.restrictNormal L) : Matrix n n k).IsGenericAt p := by
  have hψF : IsArithFrobAt (𝓞 F) ψ P :=
    isArithFrobAt_of_isArithFrobAt_int_of_absNorm_eq (P.under (𝓞 F))
      (hp.absNorm_eq (P.under (𝓞 F))) P hψ
  exact (isGenericAt_iff.mp (hp.isGenericAt (P.under (𝓞 L)) hψF.restrictNormal)).2

/-- **The eigenvalue condition propagates along a Frobenius fibre.** Let `σ` be a Frobenius
element at a prime of `N` above a decomposed generic prime `p`, and `p'` a prime in the Frobenius
fibre of `σ` that splits completely in `F` and equals `p` in `k`. At every prime of `L` above `p'`
the representation is generic at `p'`. -/
private theorem isGenericAt_of_mem_frobeniusPrimeSet {r : Gal(L/F) →* GL n k} {p : ℕ}
    (hp : r.IsDecomposedGenericPrime p) (Q₀ : Ideal (𝓞 N)) [Q₀.IsPrime]
    [Q₀.LiesOver (span {(p : ℤ)})] {σ : Gal(N/ℚ)} (hσ : IsArithFrobAt ℤ σ Q₀)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∈ Chebotarev.frobeniusPrimeSet ℚ N (ConjClasses.mk σ))
    (hsplit : ((span {((absNorm v.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 F)).ncard = finrank ℚ F)
    (hcast : ((absNorm v.asIdeal : ℕ) : k) = p) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {((absNorm v.asIdeal : ℕ) : ℤ)})] {τ : Gal(L/F)}
    (hτ : IsArithFrobAt (𝓞 F) τ Q) :
    r.IsGenericAt (Q.inertia Gal(L/F)) τ (absNorm v.asIdeal) := by
  have hv' := Rat.HeightOneSpectrum.prime_absNorm_asIdeal v
  have : Fact (absNorm v.asIdeal).Prime := ⟨hv'⟩
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  obtain ⟨𝔔, h𝔔⟩ : (Q.primesOver (𝓞 N)).Nonempty := Set.nonempty_coe_sort.mp inferInstance
  have := h𝔔.1
  have := h𝔔.2
  have : 𝔔.LiesOver (span {((absNorm v.asIdeal : ℕ) : ℤ)}) := LiesOver.trans 𝔔 Q _
  have := Rat.HeightOneSpectrum.liesOver_of_liesOver_span_absNorm v 𝔔
  have hur := Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet hv 𝔔
  obtain ⟨γ, hγ⟩ := Chebotarev.exists_isArithFrobAt_conj_of_mem_frobeniusPrimeSet_mk hv 𝔔
  -- A Frobenius element `ψ` of `N / F` at `𝔔` is the conjugate `γ σ γ⁻¹`: residue degree one
  -- makes it a Frobenius over `ℤ`, and `𝔔` is unramified.
  obtain ⟨ψ, hψ⟩ := NumberField.exists_isArithFrobAt F 𝔔
    (ne_bot_of_liesOver_of_ne_bot (p := span {((absNorm v.asIdeal : ℕ) : ℤ)})
      (by simpa using hv'.ne_zero) 𝔔)
  have hψℤ := isArithFrobAt_int_of_absNorm_eq (𝔔.under (𝓞 F))
    (absNorm_eq_of_ncard_primesOver_eq_finrank _ hsplit) 𝔔 hψ
  have heq : ψ.restrictScalars ℚ = γ * σ * γ⁻¹ := by
    have := hψℤ.mul_inv_mem_inertia ((isArithFrobAt_ringOfIntegers_rat_iff _ 𝔔).mp hγ)
    rwa [(isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) 𝔔).mp hur, Subgroup.mem_bot,
      mul_inv_eq_one] at this
  have hgen := isGenericAt_restrictNormal_of_isArithFrobAt hp (γ • Q₀) (heq ▸ hσ.conj γ)
  -- `Q` is unramified over `F`, so `τ` is the restriction of `ψ` and inertia acts trivially.
  have : Algebra.IsUnramifiedAt (𝓞 F) 𝔔 := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 ℚ) 𝔔
  have : Algebra.IsUnramifiedAt (𝓞 F) Q := Algebra.IsUnramifiedAt.of_liesOver (𝓞 F) Q 𝔔
  have hbot := (isUnramifiedAt_iff_inertia_eq_bot (K := F) Q).mp inferInstance
  have hres : IsArithFrobAt (𝓞 F) (ψ.restrictNormal L) Q := by
    rw [𝔔.over_def Q]
    exact hψ.restrictNormal
  have hτψ : τ = ψ.restrictNormal L := by
    have := hτ.mul_inv_mem_inertia hres
    rwa [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact isGenericAt_iff.mpr ⟨hbot ▸ bot_le, by rw [hτψ, hcast]; exact hgen⟩

omit [NumberField L] in
/-- The main theorem for a given Galois extension `N / ℚ` containing `L` and a primitive `ℓ`-th
root of unity. -/
private theorem infinite_setOf_isDecomposedGenericPrime_of_isPrimitiveRoot
    {r : Gal(L/F) →* GL n k} {p : ℕ} (hk : ringChar k ≠ 0) {ζ : N}
    (hζ : IsPrimitiveRoot ζ (ringChar k)) (hp : r.IsDecomposedGenericPrime p) :
    {p | r.IsDecomposedGenericPrime p}.Infinite := by
  have : NumberField L := NumberField.of_tower F N L
  have : NeZero (ringChar k) := ⟨hk⟩
  have hℓ : (ringChar k).Prime := (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hk
  -- `ℓ` lies outside a prime of `𝓞 ℚ` exactly when that prime's norm differs from `ℓ`.
  have hm (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (hw : absNorm w.asIdeal ≠ ringChar k) :
      ((ringChar k : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    rw [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
    exact fun h ↦ hw ((Nat.prime_dvd_prime_iff_eq
      (Rat.HeightOneSpectrum.prime_absNorm_asIdeal w) hℓ).mp h)
  obtain ⟨v₀, rfl⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp.prime
  have : Fact (absNorm v₀.asIdeal).Prime := ⟨hp.prime⟩
  obtain ⟨Q₀, hQ₀⟩ : ((span {((absNorm v₀.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 N)).Nonempty :=
    Set.nonempty_coe_sort.mp inferInstance
  have := hQ₀.1
  have := hQ₀.2
  have := Rat.HeightOneSpectrum.liesOver_of_liesOver_span_absNorm v₀ Q₀
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (K := N) (p := absNorm v₀.asIdeal) Q₀
  -- The norms of the primes of the Frobenius fibre of `σ`, other than `ℓ`, are all witnesses.
  refine (((Chebotarev.infinite_frobeniusPrimeSet ℚ N (ConjClasses.mk σ)).image
    Rat.HeightOneSpectrum.absNorm_asIdeal_injective.injOn).sdiff
      (Set.finite_singleton (ringChar k))).mono ?_
  rintro _ ⟨⟨v, hv, rfl⟩, hvk⟩
  have : Fact (absNorm v.asIdeal).Prime := ⟨Rat.HeightOneSpectrum.prime_absNorm_asIdeal v⟩
  -- `σ` raises the `ℓ`-th roots of unity to the norms of both primes, which are then equal in `k`.
  have hcast : ((absNorm v.asIdeal : ℕ) : k) = absNorm v₀.asIdeal := by
    have h := Chebotarev.natCast_absNorm_eq_of_mem_frobeniusPrimeSet hζ
      (hm v₀ fun h ↦ hp.natCast_ne_zero (h ▸ ringChar.Nat.cast_ringChar)) Q₀
      ((isArithFrobAt_ringOfIntegers_rat_iff σ Q₀).mpr hσ) hv (hm v hvk)
    rw [ZMod.natCast_eq_natCast_iff] at h
    exact (CharP.natCast_eq_natCast k (ringChar k)).mpr h
  have hsplit := Chebotarev.ncard_primesOver_eq_finrank_of_mem_frobeniusPrimeSet _
    hp.ncard_primesOver_eq_finrank Q₀ hσ hv
  exact ⟨Fact.out, hcast ▸ hp.natCast_ne_zero, hsplit,
    fun Q _ _ τ hτ ↦ isGenericAt_of_mem_frobeniusPrimeSet hp Q₀ hσ hv hsplit hcast Q hτ⟩

end Chebotarev

open Polynomial in
/-- **Infinitely many decomposed generic primes** (ACC+ Lemma 4.3.2). If the coefficient field
`k` has positive characteristic and `r : Gal(L/F) →* GL n k` is decomposed generic, then there are
infinitely many rational primes that are decomposed generic for `r`. Positive characteristic
covers residual representations, with coefficients in a finite field or its algebraic closure. -/
theorem IsDecomposedGeneric.infinite_setOf_isDecomposedGenericPrime (h : r.IsDecomposedGeneric)
    (hk : ringChar k ≠ 0) : {p | r.IsDecomposedGenericPrime p}.Infinite := by
  obtain ⟨p, hp⟩ := h
  have : NeZero (ringChar k) := ⟨hk⟩
  -- Embed `L` in the splitting field `N` over `ℚ` of `g = m_θ · Φ_ℓ`, with `θ` a primitive
  -- element of `L / ℚ`; `N` is Galois over `ℚ` and contains a primitive `ℓ`-th root of unity.
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ L
  set g : ℚ[X] := minpoly ℚ θ * cyclotomic (ringChar k) ℚ
  have hg : g ≠ 0 :=
    mul_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral θ)) (cyclotomic_ne_zero _ _)
  have hsplits (f : ℚ[X]) (hf : f ∣ g) : (f.map (algebraMap ℚ g.SplittingField)).Splits :=
    (SplittingField.splits g).of_dvd (Polynomial.map_ne_zero hg) (Polynomial.map_dvd _ hf)
  obtain ⟨i⟩ : Nonempty (L →ₐ[ℚ] g.SplittingField) :=
    IntermediateField.nonempty_algHom_of_adjoin_splits (fun s hs ↦ by
      rw [Set.mem_singleton_iff.mp hs]
      exact ⟨Algebra.IsIntegral.isIntegral θ, hsplits _ (dvd_mul_right _ _)⟩) hθ
  let _ : Algebra L g.SplittingField := i.toRingHom.toAlgebra
  let _ : Algebra F g.SplittingField :=
    ((algebraMap L g.SplittingField).comp (algebraMap F L)).toAlgebra
  have : IsScalarTower F L g.SplittingField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsGalois ℚ g.SplittingField := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ, hζ⟩ := (hsplits _ (dvd_mul_left _ _)).exists_eval_eq_zero (by
    rw [degree_map]
    exact (degree_cyclotomic_pos _ ℚ (NeZero.pos _)).ne')
  rw [map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff] at hζ
  exact infinite_setOf_isDecomposedGenericPrime_of_isPrimitiveRoot hk hζ hp

/-- **Decomposed generic primes avoid any finite set.** If `k` has positive characteristic and
`r` is decomposed generic, then for every finite set `s` of natural numbers some prime outside `s`
is decomposed generic for `r`. -/
theorem IsDecomposedGeneric.exists_isDecomposedGenericPrime_notMem (h : r.IsDecomposedGeneric)
    (hk : ringChar k ≠ 0) {s : Set ℕ} (hs : s.Finite) :
    ∃ p ∉ s, r.IsDecomposedGenericPrime p := by
  obtain ⟨p, hp, hps⟩ := ((h.infinite_setOf_isDecomposedGenericPrime hk).sdiff hs).nonempty
  exact ⟨p, hps, hp⟩

/-- In positive characteristic, a representation is decomposed generic exactly when it has
infinitely many decomposed generic primes. -/
theorem isDecomposedGeneric_iff_infinite (hk : ringChar k ≠ 0) :
    r.IsDecomposedGeneric ↔ {p | r.IsDecomposedGenericPrime p}.Infinite :=
  ⟨fun h ↦ h.infinite_setOf_isDecomposedGenericPrime hk, fun h ↦ h.nonempty⟩

end MonoidHom

end
