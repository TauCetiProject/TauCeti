/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.IndEtale
public import TauCeti.RingTheory.Henselization.IndEtale
public import TauCeti.RingTheory.Henselization.Map

/-!
# Recognising the henselization of a pair

The henselization `(Rʰ, Iʰ)` of a pair `(R, I)` is ind-étale over `R`
(`TauCeti.Henselization.indEtale`), has the same closed fibre `R ⧸ I`
(`TauCeti.Henselization.quotient_bijective`) and is Henselian
(`TauCeti.Henselization.henselian`). This file shows that these three properties characterise it:
if `S` is an ind-étale `R`-algebra such that `R ⧸ I → S ⧸ IS` is bijective and `(S, IS)` is
Henselian, then the `R`-algebra map `Rʰ → S` of the universal property is an isomorphism. Flatness
of `S` is automatic for an ind-étale algebra and is not a hypothesis.

The inverse `S → Rʰ` is the lift, through the Henselian pair `(Rʰ, Iʰ)`, of the map
`S → S ⧸ IS ≅ R ⧸ I → Rʰ ⧸ Iʰ`; such lifts exist and are unique for ind-étale algebras
(`TauCeti.HenselianRing.comp_bijective_of_indEtale`). The two composites are the identity by
uniqueness of lifts on either side.

As a consequence, henselization is insensitive to ind-étale extensions with the same closed
fibre: the henselization of `(S, IS)` is the henselization of `(R, I)`. For example, the
henselization of `ℤ_(5)` at `5` is the henselization of `(ℤ, (5))`.

## Main results

* `TauCeti.Henselization.bijective_lift_of_indEtale`: for an ind-étale `R`-algebra `S` which is
  Henselian along `IS` and has `R ⧸ I → S ⧸ IS` bijective, the map `Rʰ → S` is bijective.
* `TauCeti.Henselization.algEquivOfIndEtale`: the resulting `R`-algebra isomorphism `Rʰ ≃ S`.
* `TauCeti.Henselization.mapAlgEquivOfIndEtale`: for an ind-étale `R`-algebra `S` with
  `R ⧸ I → S ⧸ IS` bijective, the henselization of `(R, I)` is the henselization of `(S, IS)`.

## References

* D. Clausen, A. Mathew, M. Morrow, *K-theory and topological cyclic homology of henselian
  pairs*, J. Amer. Math. Soc. 34 (2021), Remark 3.19.
* [Stacks Project, Lemma 15.12.1 (0A02)](https://stacks.math.columbia.edu/tag/0A02), the universal
  property of the henselization.
-/

public section

universe u

namespace TauCeti.Henselization

section Henselian

variable {R : Type u} [CommRing R] (I : Ideal R) (S : Type u) [CommRing S] [Algebra R S]
  [Algebra.IndEtale R S] [HenselianRing S (I.map (algebraMap R S))]

/-- **Recognition of the henselization.** Let `S` be an ind-étale `R`-algebra such that
`(S, IS)` is a Henselian pair and `R ⧸ I → S ⧸ IS` is bijective. Then the `R`-algebra map from
the henselization of `(R, I)` to `S` given by the universal property is bijective. -/
theorem bijective_lift_of_indEtale (h : Function.Bijective (reducedMap I S)) :
    Function.Bijective (lift (I := I) (J := I.map (algebraMap R S)) le_rfl) := by
  set J := I.map (algebraMap R S)
  -- The isomorphism `R ⧸ I ≃ S ⧸ IS` and the map `R ⧸ I → Rʰ ⧸ Iʰ`, as `R`-algebra maps.
  have he : ⇑(IsScalarTower.toAlgHom R (R ⧸ I) (S ⧸ J)) = reducedMap I S := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [J]
  let e : (R ⧸ I) ≃ₐ[R] S ⧸ J := AlgEquiv.ofBijective (IsScalarTower.toAlgHom R _ _) (he ▸ h)
  let q : R ⧸ I →ₐ[R] algebra I ⧸ extended I := IsScalarTower.toAlgHom R _ _
  -- Lift `S → S ⧸ IS ≅ R ⧸ I → Rʰ ⧸ Iʰ` to `σ : S → Rʰ`.
  obtain ⟨σ, hσ⟩ := (HenselianRing.comp_bijective_of_indEtale (extended I) (A := S)).2
    (q.comp (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)))
  -- `lift` reduces modulo `Iʰ` to a map `Rʰ ⧸ Iʰ → S ⧸ IS`.
  let l : algebra I ⧸ extended I →ₐ[R] S ⧸ J :=
    Ideal.quotientMapₐ J (lift le_rfl) (Ideal.map_le_iff_le_comap.mp (map_extended I _).le)
  have hlq : l.comp q = e.toAlgHom := Ideal.Quotient.algHom_ext R (Subsingleton.elim _ _)
  refine (AlgEquiv.ofAlgHom (lift le_rfl) σ ?_
    (algHom_ext_of_map_le_jacobson (extended_le_jacobson I))).bijective
  -- `lift ∘ σ` and the identity of `S` agree modulo `IS`, hence agree.
  refine (HenselianRing.comp_bijective_of_indEtale J).1 (AlgHom.ext fun s ↦ ?_)
  have hs := congrArg l (AlgHom.congr_fun hσ s)
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotient_map_mkₐ] at hs
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hs, ← AlgHom.comp_apply l, ← AlgHom.comp_assoc, hlq]
  simp

/-- **Recognition of the henselization.** The henselization of `(R, I)` is isomorphic, as an
`R`-algebra, to any ind-étale `R`-algebra `S` such that `(S, IS)` is a Henselian pair and
`R ⧸ I → S ⧸ IS` is bijective. The isomorphism is the map of the universal property
(`coe_algEquivOfIndEtale`). -/
noncomputable def algEquivOfIndEtale (h : Function.Bijective (reducedMap I S)) :
    algebra I ≃ₐ[R] S :=
  AlgEquiv.ofBijective _ (bijective_lift_of_indEtale I S h)

/-- The recognition isomorphism is the map `lift` of the universal property. -/
@[simp]
theorem coe_algEquivOfIndEtale (h : Function.Bijective (reducedMap I S)) :
    ⇑(algEquivOfIndEtale I S h) = lift (I := I) (J := I.map (algebraMap R S)) le_rfl :=
  (rfl)

end Henselian

section IndEtale

variable {R : Type u} [CommRing R] (I : Ideal R) (S : Type u) [CommRing S] [Algebra R S]
  [Algebra.IndEtale R S] [Algebra R (algebra (I.map (algebraMap R S)))]
  [IsScalarTower R S (algebra (I.map (algebraMap R S)))]

/-- **Henselization is insensitive to ind-étale extensions with the same closed fibre.** If `S` is
an ind-étale `R`-algebra such that `R ⧸ I → S ⧸ IS` is bijective, then the henselization of
`(R, I)` is isomorphic, as an `R`-algebra, to the henselization of `(S, IS)`. The isomorphism is the
map of henselizations induced by `R → S` (`coe_mapAlgEquivOfIndEtale`). -/
noncomputable def mapAlgEquivOfIndEtale (h : Function.Bijective (reducedMap I S)) :
    algebra I ≃ₐ[R] algebra (I.map (algebraMap R S)) :=
  have hI : (I.map (algebraMap R S)).map (algebraMap S (algebra (I.map (algebraMap R S)))) =
      I.map (algebraMap R (algebra (I.map (algebraMap R S)))) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have := Algebra.IndEtale.comp (R := R) (S := S) (algebra (I.map (algebraMap R S)))
  have : HenselianRing _ (I.map (algebraMap R (algebra (I.map (algebraMap R S))))) :=
    hI ▸ henselian (I.map (algebraMap R S))
  algEquivOfIndEtale I _ (reducedMap_bijective_of_tower I S _ h (quotient_bijective _))

/-- The isomorphism `mapAlgEquivOfIndEtale` is the map of henselizations induced by `R → S`. -/
@[simp]
theorem coe_mapAlgEquivOfIndEtale (h : Function.Bijective (reducedMap I S)) :
    ⇑(mapAlgEquivOfIndEtale I S h) = map (algebraMap R S) le_rfl :=
  congrArg DFunLike.coe (map_unique _ _ (mapAlgEquivOfIndEtale I S h).toRingHom (by
    ext r
    simp [← IsScalarTower.algebraMap_apply]))

end IndEtale

-- For a maximal ideal `p` of `ℤ`, such as `(5)`, the henselization of `(ℤ_(p), pℤ_(p))` is the
-- henselization of `(ℤ, p)`: `ℤ_(p)` is ind-étale over `ℤ` with the same residue field.
noncomputable example (p : Ideal ℤ) [p.IsMaximal] :
    algebra p ≃ₐ[ℤ] algebra (p.map (algebraMap ℤ (Localization.AtPrime p))) :=
  -- The scalar tower is stated with the `ℤ`-actions of the `ℤ`-algebra structures, so it is
  -- passed explicitly rather than found by instance search.
  @mapAlgEquivOfIndEtale ℤ _ p (Localization.AtPrime p) _ _ _ _
    (.of_algebraMap_eq' (RingHom.ext_int _ _)) <|
    reducedMap_bijective_of_isLocalization _ p.primeCompl _ <| by
      let := Ideal.Quotient.field p
      rintro _ ⟨x, hx, rfl⟩
      exact isUnit_iff_ne_zero.mpr fun h ↦ hx (Ideal.Quotient.eq_zero_iff_mem.mp h)

end TauCeti.Henselization
