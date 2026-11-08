/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.FaithfullyFlat

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Affinoid.MaximalSpectrum
import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Dagger.Noetherian
import TauCeti.RingTheory.Flat.IntegrallyClosed
import TauCeti.RingTheory.RegularLocalRing.Flat
import TauCeti.RingTheory.RegularLocalRing.Maximal
import TauCeti.RingTheory.RingHom.FaithfullyFlat
import TauCeti.RingTheory.RingHom.Quotient

/-!
# Faithful flatness of the completion of a dagger algebra

Let `K` be a complete nontrivially normed ultrametric field and `A ≅ W_n ⧸ I` a `K`-dagger
algebra, with completion `τ : A → Â = T_n ⧸ I T_n`. This file shows that `τ` is faithfully flat,
and compares `A` and `Â` locally at their classical points.

* **Finite quotients.** For an ideal `J` of `A` of finite codimension, `A ⧸ J → Â ⧸ J Â` is
  bijective. This reduces to the same statement for `W_n ⊆ T_n`
  (`TauCeti.Dagger.washnitzerAlgebra.quotientMap_map_toTate_bijective`) applied to the preimage of
  `J` in `W_n`, which contains `I`.
* **Faithful flatness.** Modulo `I`, the faithfully flat map `W_n → T_n`
  (`TauCeti.Dagger.washnitzerAlgebra.faithfullyFlat_toTate`) becomes `τ`, and faithful flatness is
  stable under base change.
* **Completed local rings.** For a maximal ideal `m` of `A`, the extended ideal `m Â` is the
  maximal ideal of `Â` above `m`, so the residue fields of `A` at `m` and of `Â` at `m Â` agree,
  and the quotients `A ⧸ m ^ k` and `Â ⧸ (m Â) ^ k` agree. Taking
  the inverse limit, `τ` induces an isomorphism of the `m`-adic completion of `A` with the
  `m Â`-adic completion of `Â`; more generally this holds for every ideal whose radical is maximal.
* **Regularity.** At corresponding maximal ideals the localization of `τ` is a flat local
  homomorphism of noetherian local rings under which the maximal ideal of `A_m` generates that of
  `Â_{m Â}`, so one local ring is regular iff the other is. Hence `A` is a regular ring iff `Â` is.

Since `τ` is injective, `A` is reduced, resp. a domain, as soon as `Â` is
(`isReduced_of_injective`, `Function.Injective.isDomain`), and normality descends along the
faithfully flat `τ`.

## Main results

* `TauCeti.Dagger.faithfullyFlat_toCompletion`: the completion map `τ : A → Â` is faithfully flat,
  and `TauCeti.Dagger.toCompletion_injective`: it is injective.
* `TauCeti.Dagger.comap_map_toCompletion`: every ideal `J` of `A` satisfies `J Â ∩ A = J`.
* `TauCeti.Dagger.quotientMap_map_toCompletion_bijective`: for an ideal `J` of `A` of finite
  codimension, the map `A ⧸ J → Â ⧸ J Â` is bijective.
* `TauCeti.Dagger.isMaximal_map_toCompletion` and
  `TauCeti.Dagger.map_comap_toCompletion_of_isMaximal`: maximal ideals of `A` and `Â` correspond by
  extension and contraction.
* `TauCeti.Dagger.quotientMap_toCompletion_bijective`: the residue fields of `A` and `Â` at
  corresponding maximal ideals agree.
* `TauCeti.Dagger.adicCompletionAlgEquiv`: the completions of `A` and `Â` along an ideal of `A`
  with maximal radical and along its extension agree; for a maximal ideal these are the completed
  local rings.
* `TauCeti.Dagger.isRegularRing_completion_iff`: `Â` is a regular ring iff `A` is.
* `TauCeti.Dagger.isIntegrallyClosed_of_completion`: if `Â` is an integrally closed domain, so
  is `A`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Theorem 1.7 (1)–(3) and its proof.
* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7, for regularity along flat local
  homomorphisms whose closed fibre is a field.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section Presentation

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Type*} [CommRing A] [Algebra K A]
  [IsDaggerAlgebra K A]

variable (K) in
/-- An ideal of `A` of finite codimension has a preimage of finite codimension in `W_n`. -/
private theorem finite_quotient_comap_presentation (J : Ideal A) [Module.Finite K (A ⧸ J)] :
    Module.Finite K (washnitzerAlgebra (Fin (presentationDim K A)) K ⧸
      J.comap (presentation K A)) :=
  -- `W_n ⧸ J' → A ⧸ J` is an injective linear map into a finite-dimensional space.
  Module.Finite.of_injective (Ideal.quotientMapₐ J (presentation K A) le_rfl).toLinearMap
    Ideal.quotientMap_injective

/-- The extension of an ideal `J` of `A` to `Â = T_n ⧸ I T_n` is the image of `J' T_n`, where
`J'` is the preimage of `J` in `W_n`. -/
private theorem map_toCompletion_eq (J : Ideal A) :
    J.map (toCompletion K A) =
      ((J.comap (presentation K A)).map (washnitzerAlgebra.toTate _ K)).map
        (Ideal.Quotient.mk _) := by
  conv_lhs => rw [← Ideal.map_comap_of_surjective _ (presentation_surjective K A) J]
  rw [← Ideal.map_coe (toCompletion K A), ← Ideal.map_coe (presentation K A), Ideal.map_map,
    ← Ideal.map_coe (washnitzerAlgebra.toTate _ K) (J.comap (presentation K A)), Ideal.map_map]
  congr 1
  ext f
  simp

/-- The ideal `I T_n` defining `Â` lies in `J' T_n` for the preimage `J'` of any ideal of `A`. -/
private theorem map_ker_le_map_comap (J : Ideal A) :
    (RingHom.ker (presentation K A)).map (washnitzerAlgebra.toTate _ K) ≤
      (J.comap (presentation K A)).map (washnitzerAlgebra.toTate _ K) :=
  Ideal.map_mono (Ideal.ker_le_comap _)

end Presentation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The completion map of a dagger algebra is faithfully flat. -/
theorem faithfullyFlat_toCompletion : (toCompletion K A).toRingHom.FaithfullyFlat := by
  have h := RingHom.FaithfullyFlat.isStableUnderBaseChange.quotientMap
    RingHom.FaithfullyFlat.respectsIso
    (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K).toRingHom
    (RingHom.ker (presentation K A)) washnitzerAlgebra.faithfullyFlat_toTate
  let e := (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm
  let q := Ideal.quotientMap
    ((RingHom.ker (presentation K A)).map
      (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K))
    (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K).toRingHom Ideal.le_comap_map
  have he : e.toRingHom.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.bijective
  -- `Ideal.map` uses the same underlying function for an algebra hom and its ring hom;
  -- the coercion equalities are `AlgHom.toRingHom_eq_coe` and `Ideal.map_coe`.
  have hq : q.FaithfullyFlat := h
  have hmap : (toCompletion K A).toRingHom = q.comp e.toRingHom := by
    ext a
    obtain ⟨f, rfl⟩ := presentation_surjective K A a
    simp [q, e]
  rw [hmap]
  exact he.comp hq

/-- A dagger algebra embeds in its affinoid completion, including when it has nilpotents. -/
theorem toCompletion_injective : Function.Injective (toCompletion K A) :=
  faithfullyFlat_toCompletion.injective

variable (K) in
/-- **Ideals of a dagger algebra are contracted from its completion.** Every ideal `J` of `A`
satisfies `J Â ∩ A = J`, since `τ` is faithfully flat. -/
@[simp]
theorem comap_map_toCompletion (J : Ideal A) :
    (J.map (toCompletion K A)).comap (toCompletion K A) = J := by
  let := (toCompletion K A).toRingHom.toAlgebra
  have : Module.FaithfullyFlat A (completion K A) := faithfullyFlat_toCompletion (K := K)
  exact J.comap_map_eq_self_of_faithfullyFlat (B := completion K A)

variable (K) in
/-- **Finite quotients of a dagger algebra are quotients of its completion.** For an ideal `J` of
`A` of finite codimension, the map `A ⧸ J → Â ⧸ J Â` is bijective. -/
theorem quotientMap_map_toCompletion_bijective (J : Ideal A) [Module.Finite K (A ⧸ J)] :
    Function.Bijective (Ideal.quotientMapₐ (J.map (toCompletion K A)) (toCompletion K A)
      Ideal.le_comap_map) := by
  refine ⟨Ideal.quotientMap_injective' (H := Ideal.le_comap_map)
    (comap_map_toCompletion K J).le, fun y ↦ ?_⟩
  have := finite_quotient_comap_presentation K J
  set J' := J.comap (presentation K A)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  -- Approximate `t ∈ T_n` by a series `f ∈ W_n` modulo `J' T_n`.
  obtain ⟨x, hx⟩ := (washnitzerAlgebra.quotientMap_map_toTate_bijective J').2
    (Ideal.Quotient.mk _ t)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk _ (presentation K A f), ?_⟩
  rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hx
  rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
    toCompletion_presentation, ← map_sub, map_toCompletion_eq,
    Ideal.mem_quotient_iff_mem (map_ker_le_map_comap J)]
  simpa using hx

/-- **Maximal ideals extend to maximal ideals of the completion.** For a maximal ideal `m` of a
dagger algebra `A`, the ideal `m Â` of the completion is maximal. -/
theorem isMaximal_map_toCompletion (m : Ideal A) [hm : m.IsMaximal] :
    (m.map (toCompletion K A)).IsMaximal := by
  have := IsDaggerAlgebra.finite_quotient_of_isMaximal K m
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hm ⊢
  exact MulEquiv.isField hm
    (AlgEquiv.ofBijective _ (quotientMap_map_toCompletion_bijective K m)).symm.toMulEquiv

/-- **Maximal ideals of the completion are extended from the dagger algebra.** Every maximal
ideal `m` of `Â` is generated by its contraction `m ∩ A`. -/
@[simp]
theorem map_comap_toCompletion_of_isMaximal (m : Ideal (completion K A)) [hm : m.IsMaximal] :
    (m.comap (toCompletion K A)).map (toCompletion K A) = m := by
  have : (m.comap (toCompletion K A)).IsMaximal :=
    isAffinoidAlgebra_completion.comap_isMaximal _ m
  exact (isMaximal_map_toCompletion _).eq_of_le hm.ne_top Ideal.map_comap_le

/-- **Residue fields of a dagger algebra and of its completion agree.** For a maximal ideal `m`
of the completion `Â`, the induced map `A ⧸ (m ∩ A) → Â ⧸ m` is bijective. -/
theorem quotientMap_toCompletion_bijective (m : Ideal (completion K A)) [m.IsMaximal] :
    Function.Bijective (Ideal.quotientMapₐ m (toCompletion K A) le_rfl) := by
  set p := m.comap (toCompletion K A)
  have : p.IsMaximal := isAffinoidAlgebra_completion.comap_isMaximal _ m
  have := IsDaggerAlgebra.finite_quotient_of_isMaximal K p
  -- `m = p Â`, so this is the bijection `A ⧸ p → Â ⧸ p Â`.
  have key : ∀ m' : Ideal (completion K A), m' = p.map (toCompletion K A) →
      ∀ H : p ≤ m'.comap (toCompletion K A),
        Function.Bijective (Ideal.quotientMapₐ m' (toCompletion K A) H) := by
    rintro _ rfl -
    exact quotientMap_map_toCompletion_bijective K p
  exact key m (map_comap_toCompletion_of_isMaximal m).symm le_rfl

variable (K) in
/-- **Completed local rings of a dagger algebra and of its completion agree.** For an ideal `J` of
`A` whose radical is maximal, for instance a maximal ideal, the completion map `τ` induces an
isomorphism of the `J`-adic completion of `A` with the `J Â`-adic completion of `Â`. -/
noncomputable def adicCompletionAlgEquiv (J : Ideal A) [J.radical.IsMaximal] :
    AdicCompletion J A ≃ₐ[K] AdicCompletion (J.map (toCompletion K A)) (completion K A) :=
  AlgEquiv.ofBijective (AdicCompletion.mapₐ (toCompletion K A) Ideal.le_comap_map) <|
    AdicCompletion.mapₐ_bijective _ _ fun n ↦ by
      have := IsDaggerAlgebra.finite_quotient_pow_of_isMaximal_radical K J n
      -- `(J Â) ^ n = J ^ n Â`, so this is the bijection `A ⧸ J ^ n → Â ⧸ J ^ n Â`.
      have key : ∀ J' : Ideal (completion K A), J' = (J ^ n).map (toCompletion K A) →
          ∀ H : J ^ n ≤ J'.comap (toCompletion K A).toRingHom,
            Function.Bijective (Ideal.quotientMap J' (toCompletion K A).toRingHom H) := by
        rintro _ rfl -
        exact quotientMap_map_toCompletion_bijective K (J ^ n)
      exact key _ (Ideal.map_pow _ _ _).symm _

/-- The comparison of completed local rings is the map of adic completions induced by `τ`. -/
@[simp]
theorem toAlgHom_adicCompletionAlgEquiv (J : Ideal A) [J.radical.IsMaximal] :
    (adicCompletionAlgEquiv K J).toAlgHom =
      AdicCompletion.mapₐ (toCompletion K A) Ideal.le_comap_map :=
  (rfl)

/-- The comparison of completed local rings extends the completion map `τ : A → Â`. -/
@[simp]
theorem adicCompletionAlgEquiv_of (J : Ideal A) [J.radical.IsMaximal] (a : A) :
    adicCompletionAlgEquiv K J (AdicCompletion.of J A a) =
      AdicCompletion.of (J.map (toCompletion K A)) (completion K A) (toCompletion K A a) :=
  AdicCompletion.mapₐ_of _ _ a

/-- At a maximal ideal `m` of `Â` and its contraction `m ∩ A`, the localization `Â_m` is a regular
local ring iff `A_{m ∩ A}` is: the localized completion map is flat, and the maximal ideal of
`A_{m ∩ A}` generates that of `Â_m`. -/
private theorem isRegularLocalRing_localization_iff (m : Ideal (completion K A)) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ↔
      IsRegularLocalRing (Localization.AtPrime (m.comap (toCompletion K A))) := by
  have : IsNoetherianRing A := IsDaggerAlgebra.isNoetherianRing (K := K)
  have : IsNoetherianRing (completion K A) := isAffinoidAlgebra_completion.isNoetherianRing
  set p := m.comap (toCompletion K A)
  have : p.IsMaximal := isAffinoidAlgebra_completion.comap_isMaximal _ m
  let φ := Localization.localRingHom p m (toCompletion K A).toRingHom rfl
  let := φ.toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime m) :=
    (faithfullyFlat_toCompletion (K := K) (A := A)).flat.localRingHom m p rfl
  refine isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq ?_
  have hφ : φ.comp (algebraMap A (Localization.AtPrime p)) =
      (algebraMap (completion K A) (Localization.AtPrime m)).comp (toCompletion K A).toRingHom :=
    RingHom.ext fun a ↦ Localization.localRingHom_to_map p m _ rfl a
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
    RingHom.algebraMap_toAlgebra, Ideal.map_map, hφ, ← Ideal.map_map, AlgHom.toRingHom_eq_coe,
    Ideal.map_coe, map_comap_toCompletion_of_isMaximal]

/-- **A dagger algebra is regular iff its completion is.** The completion `Â` of a dagger algebra
`A` is a regular ring if and only if `A` is. -/
theorem isRegularRing_completion_iff : IsRegularRing (completion K A) ↔ IsRegularRing A := by
  have : IsNoetherianRing A := IsDaggerAlgebra.isNoetherianRing (K := K)
  have : IsNoetherianRing (completion K A) := isAffinoidAlgebra_completion.isNoetherianRing
  rw [isRegularRing_iff_localization_maximal, isRegularRing_iff_localization_maximal]
  refine ⟨fun h m _ ↦ ?_, fun h m _ ↦ ?_⟩
  · obtain ⟨m', ⟨hm', rfl⟩, -⟩ := completion_existsUnique_isMaximal_comap K m
    exact (isRegularLocalRing_localization_iff m').mp (h m')
  · have : (m.comap (toCompletion K A)).IsMaximal :=
      isAffinoidAlgebra_completion.comap_isMaximal _ m
    exact (isRegularLocalRing_localization_iff m).mpr (h _)

/-- **Normality descends from the completion.** If the completion `Â` of a dagger algebra `A` is
an integrally closed domain, then `A` is integrally closed. -/
theorem isIntegrallyClosed_of_completion [IsDomain (completion K A)]
    [IsIntegrallyClosed (completion K A)] : IsIntegrallyClosed A := by
  let := (toCompletion K A).toRingHom.toAlgebra
  have : Module.FaithfullyFlat A (completion K A) := faithfullyFlat_toCompletion (K := K)
  exact IsIntegrallyClosed.of_faithfullyFlat A (completion K A)

end TauCeti.Dagger
