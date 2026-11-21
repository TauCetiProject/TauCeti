/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.NumberField.FixedField
import TauCeti.FieldTheory.Galois.ConjugateFields
import TauCeti.FieldTheory.GaloisGroups.Symmetric.Realization
import TauCeti.GroupTheory.AlmostConjugate.GassmannPair
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.SplittingType
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.SplittingField
import TauCeti.RepresentationTheory.OfMulAction.QuotientToInvariants

/-!
# Arithmetic equivalence and Gassmann's theorem

Two number fields are *arithmetically equivalent* when they have the same Dedekind zeta function,
equivalently the same number of integral ideals of every absolute norm. By multiplicativity of the
norm-counting function and its Euler product, the ideal counts at powers of a rational prime `p`
depend only on the multiset of residue degrees of the primes above `p`
(`TauCeti.normCoeff_one_apply_pow_eq_prod_inertiaDeg`,
`TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq`).

For a Galois extension `L / K` of number fields and two almost-conjugate subgroups `H, H' ≤
Gal(L / K)`, the permutation representations `ℚ[Gal(L / K) ⧸ H]` and `ℚ[Gal(L / K) ⧸ H']`
agree on fixed-point counts and therefore descend to equivalent permutation representations of
`D(Q) / I(Q)` on the inertia-orbit spaces `I(Q) \ (Gal(L / K) ⧸ H)` and `I(Q) \ (Gal(L / K) ⧸ H')`
at every prime `Q` of `𝓞 L` (`TauCeti.fullCycleType_toPerm_orbitRelQuotient_eq`). Comparing full
cycle types of an arithmetic Frobenius modulo `I(Q)` via
`Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg` shows that `L ^ H` and `L ^ H'`
have the same multiset of residue degrees above every maximal ideal of `𝓞 K`, ramified primes
included (`TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate`).

Over `ℚ` this yields **Gassmann's theorem**: fixed fields of almost-conjugate subgroups have the
same number of ideals of every norm and the same Dedekind zeta function
(`Subgroup.dedekindZetaCoeff_fixedField_eq_of_almostConjugate`,
`Subgroup.dedekindZeta_fixedField_eq_of_almostConjugate`). Realizing `S₁₆` as a Galois group over
`ℚ` (`TauCeti.exists_monic_int_polynomial_hasFullSymmetricGaloisGroup`) and pulling back the
non-conjugate almost-conjugate pair of order `16` in `S₁₆` (`TauCeti.exists_S16_gassmann_pair`)
then yields two nonisomorphic number fields with the same Dedekind zeta function
(`TauCeti.exists_dedekindZetaCoeff_eq_not_isomorphic`), since fixed fields of subgroups of a finite
Galois extension are isomorphic exactly when the subgroups are conjugate
(`Subgroup.nonempty_fixedField_algEquiv_iff_exists_map_conj_eq`).

## Main results

* `TauCeti.normCoeff_one_apply_pow_eq_prod_inertiaDeg`: the ideal count at a rational prime power
  `p ^ k` is determined by the multiset of residue degrees above `p`.
* `TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq`: equal residue-degree multisets above
  every rational prime imply equal Dedekind zeta coefficients.
* `TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate`: almost-conjugate subgroups of
  `Gal(L / K)` have fixed fields with the same multiset of residue degrees above every maximal
  ideal of `𝓞 K` (ramified or unramified).
* `Subgroup.dedekindZetaCoeff_fixedField_eq_of_almostConjugate`: **Gassmann's theorem** for ideal
  counts.
* `Subgroup.dedekindZeta_fixedField_eq_of_almostConjugate`: **Gassmann's theorem** for Dedekind
  zeta functions.
* `TauCeti.exists_dedekindZetaCoeff_eq_not_isomorphic`: existence of two nonisomorphic number
  fields with the same Dedekind zeta coefficients.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open Ideal IsDedekindDomain MulAction NumberField
open scoped NumberField Pointwise

namespace TauCeti

/-! ### Local Euler factors from residue degrees -/

open scoped Classical in
/-- **The prime-power ideal count from residue degrees.** At a rational prime `v` of `𝓞 ℚ` with
absolute norm `p`, the value of `normCoeff K 1` at `p ^ k` depends only on the multiset of
residue degrees of the primes of `𝓞 K` above `v`. -/
theorem normCoeff_one_apply_pow_eq_prod_inertiaDeg (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) (Ideal.absNorm v.asIdeal ^ k) =
      (((Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ))).map
        (fun d ↦ ArithmeticFunction.ofPowerSeries (Ideal.absNorm v.asIdeal ^ d)
          (PowerSeries.mk fun _ ↦ (1 : ℂ)))).prod (Ideal.absNorm v.asIdeal ^ k) := by
  have hp : (Ideal.absNorm v.asIdeal).Prime := by
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v
  -- Identify `v.asIdeal.primesOver (𝓞 K)` with the height-one primes above `v`.
  let e := HeightOneSpectrum.equivPrimesOver (𝓞 K) (p := v.asIdeal) v.ne_bot
  let toSpec : v.asIdeal.primesOver (𝓞 K) → HeightOneSpectrum (𝓞 K) := fun P ↦ (e.symm P).val
  have htoSpec_inj : Function.Injective toSpec := Subtype.val_injective.comp e.symm.injective
  have htoSpec_asIdeal : ∀ P, (toSpec P).asIdeal = P.val := fun P ↦ by
    rw [← HeightOneSpectrum.equivPrimesOver_apply (𝓞 K) (p := v.asIdeal) v.ne_bot (e.symm P)]
    exact congrArg Subtype.val (e.apply_symm_apply P)
  -- Every height-one prime of `𝓞 K` containing `N(v)` divides the lift of `v.asIdeal`.
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 K),
      (Ideal.absNorm v.asIdeal : 𝓞 K) ∈ Q.asIdeal → Q ∈ Finset.univ.image toSpec := by
    intro Q hQ
    have hdvd : Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) v.asIdeal := by
      rw [Ideal.dvd_iff_le, ← Rat.RingOfIntegers.ideal_span_absNorm_eq_self v.asIdeal,
        Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
      exact hQ
    exact Finset.mem_image.mpr ⟨e ⟨Q, hdvd⟩, Finset.mem_univ _, by simp [toSpec]⟩
  -- Apply the local Euler product formula over `Finset.univ.image toSpec`.
  rw [IdealArithmeticFunction.normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor
      IdealArithmeticFunction.isMultiplicative_one hp _ hmem k,
    Finset.prod_image (fun _ _ _ _ h ↦ htoSpec_inj h)]
  congr 1
  rw [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun P _ ↦ ?_)
  have := P.property.1
  have := P.property.2
  rw [IdealArithmeticFunction.localArithmeticFactor_def, htoSpec_asIdeal,
    ← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.val]
  congr 1
  ext n
  simp

open scoped Classical in
/-- **Equal residue-degree multisets imply equal Dedekind zeta coefficients.** If two number fields
`K` and `L` have the same multiset of residue degrees above every height-one prime of `𝓞 ℚ`, then
they have the same number of integral ideals of every absolute norm. -/
theorem dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ)) =
        (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 L))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ))) (n : ℕ) :
    dedekindZetaCoeff K n = dedekindZetaCoeff L n := by
  by_cases hn : n = 0
  · subst hn
    simp
  have hfun : normCoeff K (1 : IdealArithmeticFunction K) =
      normCoeff L (1 : IdealArithmeticFunction L) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      IdealArithmeticFunction.isMultiplicative_one.normCoeff _
      IdealArithmeticFunction.isMultiplicative_one.normCoeff]
    intro p k hp
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    rw [← hv, normCoeff_one_apply_pow_eq_prod_inertiaDeg,
      normCoeff_one_apply_pow_eq_prod_inertiaDeg, h v]
  have hn_eq := congrArg (fun f : ArithmeticFunction ℂ ↦ f n) hfun
  simp only [normCoeff_one_apply, hn, ite_false] at hn_eq
  exact Nat.cast_injective hn_eq

/-! ### Gassmann's theorem -/

open scoped Classical in
/-- **Almost-conjugate subgroups have the same residue degrees at every prime.** For a Galois
extension `L / K` of number fields and almost-conjugate subgroups `H, H' ≤ Gal(L / K)`, the fixed
fields `L ^ H` and `L ^ H'` have the same multiset of residue degrees above every maximal ideal
`p` of `𝓞 K`, including primes that ramify in `L`. -/
theorem map_inertiaDeg_fixedField_eq_of_almostConjugate
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {H H' : Subgroup (L ≃ₐ[K] L)}
    (hHH' : H.AlmostConjugate H') (p : Ideal (𝓞 K)) [p.IsMaximal] :
    (Finset.univ : Finset (p.primesOver (𝓞 ↥(IntermediateField.fixedField H)))).val.map
        (fun P ↦ P.val.inertiaDeg (𝓞 K)) =
      (Finset.univ : Finset (p.primesOver (𝓞 ↥(IntermediateField.fixedField H')))).val.map
        (fun P ↦ P.val.inertiaDeg (𝓞 K)) := by
  -- Choose a prime `Q` of `𝓞 L` above `p` and an arithmetic Frobenius `σ` at `Q`.
  obtain ⟨Q, hQmax, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) p
    fun x hx ↦ by
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
        ((RingHom.mem_ker.mp hx).trans (map_zero _).symm)
      exact hx0 ▸ p.zero_mem
  have : Q.IsMaximal := hQmax
  have : Q.IsPrime := hQmax.isPrime
  have : Q.LiesOver p := ⟨hQp.symm⟩
  have hQne : Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hQmax (NumberField.RingOfIntegers.not_isField L)
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q hQne
  -- Read both residue-degree multisets as Frobenius cycle types on inertia-orbit spaces.
  rw [← Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg p Q H hσ,
    ← Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg p Q H' hσ]
  -- Almost-conjugacy gives equal fixed-coset counts on `D(Q)`, hence equal cycle types on
  -- `I`-orbits.
  have hfix : ∀ d : stabilizer (L ≃ₐ[K] L) Q,
      Nat.card (fixedBy ((L ≃ₐ[K] L) ⧸ H) d) = Nat.card (fixedBy ((L ≃ₐ[K] L) ⧸ H') d) :=
    fun d ↦ Subgroup.almostConjugate_iff_forall_natCard_fixedBy_eq.mp hHH' d.val
  exact fullCycleType_toPerm_orbitRelQuotient_eq hfix (Q.inertia (stabilizer (L ≃ₐ[K] L) Q))
    (QuotientGroup.mk ⟨σ, hσ.mem_stabilizer⟩)

end TauCeti

namespace Subgroup

/-- **Gassmann's theorem.** If two subgroups `H` and `K` of the Galois group of a Galois number
field `E / ℚ` are almost conjugate, then their fixed fields have the same number of integral ideals
of every absolute norm. -/
theorem dedekindZetaCoeff_fixedField_eq_of_almostConjugate
    {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] (H K : Subgroup (E ≃ₐ[ℚ] E))
    (hHK : H.AlmostConjugate K) (n : ℕ) :
    TauCeti.dedekindZetaCoeff (IntermediateField.fixedField H) n =
      TauCeti.dedekindZetaCoeff (IntermediateField.fixedField K) n :=
  TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq _ _
    (fun v ↦ TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate hHK v.asIdeal) n

/-- **Gassmann's theorem for Dedekind zeta functions.** Almost-conjugate subgroups of the Galois
group of a Galois number field `E / ℚ` have fixed fields with the same Dedekind zeta function. -/
theorem dedekindZeta_fixedField_eq_of_almostConjugate
    {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] (H K : Subgroup (E ≃ₐ[ℚ] E))
    (hHK : H.AlmostConjugate K) (s : ℂ) :
    NumberField.dedekindZeta (IntermediateField.fixedField H) s =
      NumberField.dedekindZeta (IntermediateField.fixedField K) s := by
  rw [TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff,
    TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  congr 1
  ext n
  exact congrArg Nat.cast (H.dedekindZetaCoeff_fixedField_eq_of_almostConjugate K hHK n)

end Subgroup

namespace TauCeti

/-! ### Nonisomorphic arithmetically equivalent number fields -/

/-- **Nonisomorphic number fields with the same zeta function** (Gassmann). There exist two number
fields with the same number of integral ideals of every absolute norm that are not isomorphic. -/
theorem exists_dedekindZetaCoeff_eq_not_isomorphic :
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : NumberField K) (_ : NumberField L),
      (∀ n : ℕ, dedekindZetaCoeff K n = dedekindZetaCoeff L n) ∧ IsEmpty (K ≃+* L) := by
  -- Realize `S₁₆` as the Galois group of a splitting field `E / ℚ`.
  obtain ⟨f, -, hdeg, -, hsym⟩ :=
    exists_monic_int_polynomial_hasFullSymmetricGaloisGroup 16 (by decide)
  let g : Polynomial ℚ := f.map (Int.castRingHom ℚ)
  have hgdeg : g.natDegree = 16 := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
  have : IsGalois ℚ g.SplittingField := IsGalois.of_separable_splitting_field hsym.separable
  obtain ⟨e₀⟩ := hsym.nonempty_mulEquiv
  let e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) ≃* Equiv.Perm (Fin 16) :=
    e₀.trans (Equiv.permCongrHom (finCongr hgdeg))
  -- Pull back the non-conjugate Gassmann pair from `S₁₆` to `Gal(E / ℚ)`.
  obtain ⟨H₀, K₀, -, -, hac₀, hnc₀⟩ := exists_S16_gassmann_pair
  let H : Subgroup (g.SplittingField ≃ₐ[ℚ] g.SplittingField) :=
    H₀.comap (e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) →* Equiv.Perm (Fin 16))
  let K : Subgroup (g.SplittingField ≃ₐ[ℚ] g.SplittingField) :=
    K₀.comap (e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) →* Equiv.Perm (Fin 16))
  have hac : H.AlmostConjugate K := hac₀.comap e
  have hnc : ¬ ∃ σ : g.SplittingField ≃ₐ[ℚ] g.SplittingField, H.map (MulAut.conj σ) = K :=
    fun h ↦ hnc₀ ((Subgroup.exists_map_conj_comap_eq_iff e H₀ K₀).mp h)
  -- Their fixed fields are arithmetically equivalent by Gassmann's theorem and nonisomorphic.
  refine ⟨↥(IntermediateField.fixedField H), ↥(IntermediateField.fixedField K),
    inferInstance, inferInstance, inferInstance, inferInstance,
    H.dedekindZetaCoeff_fixedField_eq_of_almostConjugate K hac, ⟨fun φ ↦ ?_⟩⟩
  have halg : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(IntermediateField.fixedField K) :=
    AlgEquiv.ofRingEquiv (f := φ) fun q ↦ by
      simp [eq_ratCast]
  exact hnc ((Subgroup.nonempty_fixedField_algEquiv_iff_exists_map_conj_eq H K).mp ⟨halg⟩)

end TauCeti
