/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Transitivity
import TauCeti.RingTheory.Invariant.Profinite.Frobenius

/-!
# Density of Frobenius elements in the absolute Galois group of a number field

Let `F` be a number field, `G_F` its absolute Galois group and `O` the integral closure of `𝓞 F` in
`F^alg`. For a set `Pl` of finite places of `F`, the **Frobenius set** `frobeniusSet Pl ⊆ G_F` is
the set of arithmetic Frobenius lifts (`TauCeti.GaloisRep.IsArithFrobAtIntegralPrime`) at the
maximal ideals of `O` above the places in `Pl`. It is stable under conjugation.

The main result is that the Frobenius set of a set of places of Dirichlet density one is dense in
`G_F` (`TauCeti.GaloisRep.dense_frobeniusSet`). It is the Chebotarev density theorem read in the
profinite group `G_F`. Every open normal subgroup of `G_F` is the fixing subgroup of a finite
Galois subextension `E` of `F^alg / F`, so a coset of it is a fibre of the restriction map
`G_F → Gal(E/F)`. At a place `v` unramified in `E` all Frobenius lifts at a maximal ideal `Q`
above `v` differ by elements of the inertia group `I_Q`, which fixes `E`; so they all restrict to
the same element of `Gal(E/F)`, an arithmetic Frobenius at the prime `Q ∩ 𝓞 E`. Conversely,
every arithmetic Frobenius at a prime of `𝓞 E` above `v` arises in this way, after moving `Q` by
an element of `G_F`. Therefore the places `v` of `Pl`, unramified in `E`, above which some `Q` has
all its Frobenius lifts in a given fibre over `τ ∈ Gal(E/F)` are the places of `Pl` in the
Chebotarev set of the conjugacy class `C` of `τ`. When `Pl` has density one they have Dirichlet
density `#C / #Gal(E/F) > 0`
(`TauCeti.GaloisRep.hasDirichletDensity_setOf_forall_isArithFrobAtIntegralPrime`), so every coset
of every open normal subgroup meets the Frobenius set.

Density is what makes Frobenius elements determine continuous objects on `G_F`: two continuous
maps from `G_F` to a Hausdorff space agreeing on `frobeniusSet Pl` agree everywhere
(`Continuous.ext_on`). This is the input from Chebotarev to the recognition of Galois
representations by their Frobenius characteristic polynomials.

## Main definitions

* `TauCeti.GaloisRep.frobeniusSet Pl`: the arithmetic Frobenius lifts in `G_F` at the maximal
  ideals of `O` above the places in `Pl`.

## Main results

* `TauCeti.GaloisRep.conj_mem_frobeniusSet`: the Frobenius set is stable under conjugation.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime.restrictNormalHom`: the restriction of a Frobenius
  lift at `Q` to a normal subextension `E` is an arithmetic Frobenius at `Q ∩ 𝓞 E`.
* `TauCeti.GaloisRep.restrictNormalHom_eq_of_isArithFrobAtIntegralPrime`: above a place
  unramified in a finite Galois subextension `E`, all Frobenius lifts at a prime restrict to the
  same element of `Gal(E/F)`.
* `TauCeti.GaloisRep.mem_frobeniusPrimeSet_restrictNormalHom_iff`: a place `v` lies in the
  Chebotarev set of the class of `g|_E` exactly when it is unramified in `E` and all Frobenius
  lifts at some maximal ideal above `v` restrict to `g|_E`.
* `TauCeti.GaloisRep.hasDirichletDensity_setOf_forall_isArithFrobAtIntegralPrime`: those places
  of a set `Pl` of density one have Dirichlet density `#C / #Gal(E/F)`.
* `TauCeti.GaloisRep.dense_frobeniusSet`: the Frobenius set of a set of places of Dirichlet
  density one is dense in `G_F`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ENS 7 (1974), 6.12.
* J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. Math. IHÉS 54
  (1981), §2.1, Théorème 1.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Theorem 2.3.
-/

public section

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-! ### Frobenius sets -/

/-- The **Frobenius set** of a set `Pl` of finite places of `F`: the arithmetic Frobenius lifts
`σ ∈ G_F` at the maximal ideals `Q` of the integral closure `O` of `𝓞 F` in `F^alg` lying over the
places in `Pl`. -/
def frobeniusSet (Pl : Set (HeightOneSpectrum (𝓞 F))) : Set (Field.absoluteGaloisGroup F) :=
  {σ | ∃ v ∈ Pl, ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal ∧
    Q.under (𝓞 F) = v.asIdeal ∧ IsArithFrobAtIntegralPrime σ Q}

variable {Pl Pl' : Set (HeightOneSpectrum (𝓞 F))} {σ : Field.absoluteGaloisGroup F}

@[simp]
theorem mem_frobeniusSet :
    σ ∈ frobeniusSet Pl ↔ ∃ v ∈ Pl, ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)),
      Q.IsMaximal ∧ Q.under (𝓞 F) = v.asIdeal ∧ IsArithFrobAtIntegralPrime σ Q :=
  Iff.rfl

/-- A larger set of places has a larger Frobenius set. -/
theorem frobeniusSet_mono (h : Pl ⊆ Pl') : frobeniusSet Pl ⊆ frobeniusSet Pl' :=
  fun _ ⟨v, hv, hQ⟩ ↦ ⟨v, h hv, hQ⟩

@[simp]
theorem frobeniusSet_empty : frobeniusSet (∅ : Set (HeightOneSpectrum (𝓞 F))) = ∅ := by
  simp [Set.eq_empty_iff_forall_notMem]

/-- The Frobenius set of a union of sets of places is the union of their Frobenius sets. -/
theorem frobeniusSet_union : frobeniusSet (Pl ∪ Pl') = frobeniusSet Pl ∪ frobeniusSet Pl' := by
  ext σ
  simp only [mem_frobeniusSet, Set.mem_union, or_and_right, exists_or]

/-- **The Frobenius set is stable under conjugation.** If `σ` is an arithmetic Frobenius lift at
`Q`, then `τ σ τ⁻¹` is one at `τ • Q`, which lies over the same place. -/
theorem conj_mem_frobeniusSet (hσ : σ ∈ frobeniusSet Pl) (τ : Field.absoluteGaloisGroup F) :
    τ * σ * τ⁻¹ ∈ frobeniusSet Pl := by
  obtain ⟨v, hv, Q, hQ, hQv, hσQ⟩ := hσ
  refine ⟨v, hv, τ • Q, ?_, by rw [Ideal.under_smul, hQv], hσQ.conj τ⟩
  rw [Ideal.pointwise_smul_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)

/-! ### Frobenius lifts and finite Galois subextensions -/

/-- **Restriction of a Frobenius lift.** If `σ ∈ G_F` is an arithmetic Frobenius at an ideal `Q`
of `O`, its restriction to a normal subextension `E` of `F^alg / F` is an arithmetic Frobenius
at `Q ∩ 𝓞 E`. -/
theorem IsArithFrobAtIntegralPrime.restrictNormalHom (E : IntermediateField F (AlgebraicClosure F))
    [Normal F E] {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))}
    (hσ : IsArithFrobAtIntegralPrime σ Q) :
    IsArithFrobAt (𝓞 F) (AlgEquiv.restrictNormalHom E σ)
      (Q.comap (ringOfIntegersToIntegralClosure E)) := by
  have : Q.LiesOver (Q.under (𝓞 F)) := ⟨rfl⟩
  intro y
  rw [← Ideal.over_def (Q.comap (ringOfIntegersToIntegralClosure E)) (Q.under (𝓞 F)),
    Ideal.mem_comap, MulSemiringAction.toAlgHom_apply, map_sub, map_pow,
    ringOfIntegersToIntegralClosure_smul]
  exact hσ _

variable [NumberField F]

/-- **Frobenius lifts above an unramified place restrict uniformly.** Let `E` be a finite normal
subextension of `F^alg / F` and `Q` an ideal of `O` above a place `v` unramified in `E`. Two
arithmetic Frobenius lifts at `Q` differ by an element of the inertia group `I_Q`, which lies in
the inertia group of a maximal ideal containing `Q` and therefore fixes `E`; so they have the same
restriction to `E`. -/
theorem restrictNormalHom_eq_of_isArithFrobAtIntegralPrime
    (E : IntermediateField F (AlgebraicClosure F)) [NumberField E] [Normal F E]
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))}
    {v : HeightOneSpectrum (𝓞 F)} (hQv : Q.under (𝓞 F) = v.asIdeal)
    (hv : v ∉ Chebotarev.ramifiedPrimes F E) {σ σ' : Field.absoluteGaloisGroup F}
    (hσ : IsArithFrobAtIntegralPrime σ Q) (hσ' : IsArithFrobAtIntegralPrime σ' Q) :
    AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E σ' := by
  -- a maximal ideal `M ⊇ Q` still lies over `v`, and `I_Q ≤ I_M`
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q fun h ↦
    v.isPrime.ne_top (by rw [← hQv, h, Ideal.under, Ideal.comap_top])
  have hMv : M.under (𝓞 F) = v.asIdeal :=
    (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hM.ne_top) (hQv ▸ Ideal.comap_mono hQM)).symm
  have := hM.isPrime
  have h : σ * σ'⁻¹ ∈ (AlgEquiv.restrictNormalHom E).ker := E.restrictNormalHom_ker ▸
    inertiaGroup_le_fixingSubgroup E hMv hv
      (AddSubgroup.inertia_mono (G := Field.absoluteGaloisGroup F) (fun _ hx ↦ hQM hx)
        (hσ.mul_inv_mem_inertia hσ'))
  exact (MonoidHom.eq_iff _).2 ((MonoidHom.normal_ker _).mem_comm h)

/-- **A Frobenius lift witnesses the Chebotarev set of its restriction.** If `σ ∈ G_F` is an
arithmetic Frobenius at an ideal `Q` of `O` above a place `v` unramified in a finite Galois
subextension `E` of `F^alg / F`, then `v` lies in the Chebotarev set of the conjugacy class of the
restriction of `σ` to `E`. -/
theorem mem_frobeniusPrimeSet_restrictNormalHom (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [IsGalois F E] {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))}
    {v : HeightOneSpectrum (𝓞 F)} (hQv : Q.under (𝓞 F) = v.asIdeal)
    (hv : v ∉ Chebotarev.ramifiedPrimes F E) (hσ : IsArithFrobAtIntegralPrime σ Q) :
    v ∈ Chebotarev.frobeniusPrimeSet F E (ConjClasses.mk (AlgEquiv.restrictNormalHom E σ)) := by
  rw [Chebotarev.mem_ramifiedPrimes_iff, not_not] at hv
  have : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
  have := Ideal.comap_liesOver Q v.asIdeal (ringOfIntegersToIntegralClosure E)
  exact Chebotarev.mem_frobeniusPrimeSet_mk_of_isArithFrobAt hv _ (hσ.restrictNormalHom E)

/-- An arithmetic Frobenius lift exists at every maximal ideal of `O` above a finite place. -/
private theorem exists_isArithFrobAtIntegralPrime
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} [Q.IsPrime]
    {v : HeightOneSpectrum (𝓞 F)} (hQv : Q.under (𝓞 F) = v.asIdeal) :
    ∃ σ : Field.absoluteGaloisGroup F, IsArithFrobAtIntegralPrime σ Q := by
  let _ : TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⊥
  have : DiscreteTopology (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⟨rfl⟩
  have := continuousSMul_integralClosure F
  have : Finite (𝓞 F ⧸ Q.under (𝓞 F)) := by
    rw [hQv]
    exact Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact IsArithFrobAt.exists_of_isInvariant_of_profinite (𝓞 F) (Field.absoluteGaloisGroup F) Q

/-- **The Chebotarev set of a restriction, in terms of Frobenius lifts.** Let `E` be a finite
Galois subextension of `F^alg / F` and `g ∈ G_F`. A finite place `v` of `F` lies in the Chebotarev
set of the conjugacy class of `g|_E` in `Gal(E/F)` exactly when `v` is unramified in `E` and has a
maximal ideal `Q` of `O` above it at which every arithmetic Frobenius lift restricts to `g|_E`,
that is, lies in the coset `g G_E`. -/
theorem mem_frobeniusPrimeSet_restrictNormalHom_iff
    (E : IntermediateField F (AlgebraicClosure F)) [NumberField E] [IsGalois F E]
    (g : Field.absoluteGaloisGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ Chebotarev.frobeniusPrimeSet F E (ConjClasses.mk (AlgEquiv.restrictNormalHom E g)) ↔
      v ∉ Chebotarev.ramifiedPrimes F E ∧
        ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal ∧
          Q.under (𝓞 F) = v.asIdeal ∧ ∀ σ : Field.absoluteGaloisGroup F,
            IsArithFrobAtIntegralPrime σ Q →
              AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E g := by
  refine ⟨fun hg ↦ ?_, fun ⟨hv, Q, hQ, hQv, h⟩ ↦ ?_⟩
  · have hv : v ∉ Chebotarev.ramifiedPrimes F E := fun h ↦
      Chebotarev.frobeniusPrimeSet_subset_compl_ramifiedPrimes _ hg (Finset.mem_coe.2 h)
    refine ⟨hv, ?_⟩
    -- a Frobenius lift `σ₀` at any `Q₀` above `v` restricts into the class of `g|_E`
    obtain ⟨Q₀, hQ₀, hQ₀v⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := integralClosure (𝓞 F) (AlgebraicClosure F)) v.asIdeal
    have hQ₀v : Q₀.under (𝓞 F) = v.asIdeal := ((Ideal.liesOver_iff _ _).1 hQ₀v).symm
    have := hQ₀.isPrime
    obtain ⟨σ₀, hσ₀⟩ := exists_isArithFrobAtIntegralPrime hQ₀v
    have hclass : ConjClasses.mk (AlgEquiv.restrictNormalHom E σ₀) =
        ConjClasses.mk (AlgEquiv.restrictNormalHom E g) := by
      by_contra hne
      exact Set.disjoint_left.1 (Chebotarev.disjoint_frobeniusPrimeSet hne)
        (mem_frobeniusPrimeSet_restrictNormalHom E hQ₀v hv hσ₀) hg
    -- conjugating by a lift `γ` of the conjugating element moves `Q₀` to the required `Q`
    obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hclass)
    obtain ⟨γ, rfl⟩ : ∃ γ : Field.absoluteGaloisGroup F, AlgEquiv.restrictNormalHom E γ = c :=
      AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F) c
    refine ⟨γ • Q₀, ?_, by rw [Ideal.under_smul, hQ₀v], fun σ hσ ↦ ?_⟩
    · rw [Ideal.pointwise_smul_eq_comap]
      exact Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)
    · rw [restrictNormalHom_eq_of_isArithFrobAtIntegralPrime E (by rw [Ideal.under_smul, hQ₀v]) hv
        hσ (hσ₀.conj γ), ← hc]
      -- `rw [map_mul]` fails here: `G_F` is `Gal(F^alg/F)` only up to unfolding a definition
      exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (map_mul _ _ _) (map_inv _ _))
  · have := hQ.isPrime
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAtIntegralPrime hQv
    rw [← h σ hσ]
    exact mem_frobeniusPrimeSet_restrictNormalHom E hQv hv hσ

/-- **Chebotarev density for Frobenius lifts in `G_F`.** Let `Pl` be a set of finite places of `F`
of Dirichlet density one, `E` a finite Galois subextension of `F^alg / F` and `g ∈ G_F`. The places
`v ∈ Pl`, unramified in `E`, with a maximal ideal of `O` above them at which every arithmetic
Frobenius lift lies in the coset `g G_E` (that is, restricts to `g|_E`), have Dirichlet density
`#C / #Gal(E/F)`, where `C` is the conjugacy class of `g|_E`. -/
theorem hasDirichletDensity_setOf_forall_isArithFrobAtIntegralPrime
    (E : IntermediateField F (AlgebraicClosure F)) [NumberField E] [Normal F E]
    (hPl : NumberField.Set.HasDirichletDensity Pl 1) (g : Field.absoluteGaloisGroup F) :
    NumberField.Set.HasDirichletDensity
      {v | v ∈ Pl ∧ v ∉ Chebotarev.ramifiedPrimes F E ∧
        ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal ∧
          Q.under (𝓞 F) = v.asIdeal ∧ ∀ σ : Field.absoluteGaloisGroup F,
            IsArithFrobAtIntegralPrime σ Q →
              AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E g}
      ((Nat.card (ConjClasses.mk (AlgEquiv.restrictNormalHom E g)).carrier : ℝ) /
        (Nat.card (E ≃ₐ[F] E) : ℝ)) := by
  have : IsGalois F E := {}
  have hset : {v | v ∈ Pl ∧ v ∉ Chebotarev.ramifiedPrimes F E ∧
      ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal ∧
        Q.under (𝓞 F) = v.asIdeal ∧ ∀ σ : Field.absoluteGaloisGroup F,
          IsArithFrobAtIntegralPrime σ Q →
            AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E g} =
      Chebotarev.frobeniusPrimeSet F E (ConjClasses.mk (AlgEquiv.restrictNormalHom E g)) ∩ Pl := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_frobeniusPrimeSet_restrictNormalHom_iff,
      and_comm]
  rw [hset]
  exact (Chebotarev.hasDirichletDensity_frobeniusPrimeSet F E _).inter_of_hasDirichletDensity_one
    hPl

/-- **Frobenius elements are dense.** The Frobenius set of a set of finite places of `F` of
Dirichlet density one is dense in `G_F`. Every nonempty open set contains a coset `g G_E` of the
fixing subgroup of a finite Galois subextension `E`, and by Chebotarev some Frobenius lift above
a place of the set lies in that coset. -/
theorem dense_frobeniusSet (hPl : NumberField.Set.HasDirichletDensity Pl 1) :
    Dense (frobeniusSet Pl) := by
  refine dense_iff_inter_open.2 fun W hW ⟨g, hgW⟩ ↦ ?_
  -- `g G_E ⊆ W` for a finite normal subextension `E`
  have h1 : (1 : Field.absoluteGaloisGroup F) ∈
      (fun x : Field.absoluteGaloisGroup F ↦ g * x) ⁻¹' W := by
    rwa [Set.mem_preimage, mul_one]
  obtain ⟨E, _, _, hEW⟩ := (krullTopology_mem_nhds_one_iff_of_normal F (AlgebraicClosure F)
    ((fun x : Field.absoluteGaloisGroup F ↦ g * x) ⁻¹' W)).1
      ((hW.preimage (continuous_const_mul g)).mem_nhds h1)
  have : NumberField E := NumberField.of_module_finite F E
  -- some place of `Pl` has a maximal ideal above it whose Frobenius lifts lie in `g G_E`
  have hpos : (Nat.card (ConjClasses.mk (AlgEquiv.restrictNormalHom E g)).carrier : ℝ) /
      (Nat.card (E ≃ₐ[F] E) : ℝ) ≠ 0 := by
    have : Nonempty (ConjClasses.mk (AlgEquiv.restrictNormalHom E g)).carrier :=
      ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
    exact div_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne') (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  obtain ⟨v, hv, -, Q, hQ, hQv, h⟩ :=
    ((hasDirichletDensity_setOf_forall_isArithFrobAtIntegralPrime E hPl g).infinite hpos).nonempty
  have := hQ.isPrime
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAtIntegralPrime hQv
  refine ⟨σ, ?_, v, hv, Q, hQ, hQv, hσ⟩
  have hmem : g⁻¹ * σ ∈ E.fixingSubgroup :=
    E.restrictNormalHom_ker ▸ (MonoidHom.eq_iff _).1 (h σ hσ)
  have hσW := Set.mem_preimage.1 (hEW hmem)
  rwa [mul_inv_cancel_left] at hσW

end TauCeti.GaloisRep
