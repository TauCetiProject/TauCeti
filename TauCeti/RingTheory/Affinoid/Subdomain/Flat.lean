/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Basic
public import TauCeti.RingTheory.RingHom.FaithfullyFlat

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Flat.QuotientPow

/-!
# Flatness of affinoid subdomains

The restriction map `A → B` of an affinoid subdomain of an affinoid algebra is flat
(`TauCeti.IsAffinoidSubdomainMap.flat`). For a finite family of affinoid subdomains covering the
classical maximal spectrum, the map from `A` into the product of their coordinate algebras is
faithfully flat. Neither reducedness of `A` nor a rational presentation of the subdomains is
assumed, and nilpotents are allowed. The family may be empty, in which case its covering
hypothesis forces `A` to be the zero ring. Rational domains `A → A⟨f/g⟩` are the special case
obtained by applying these results to `TauCeti.RationalFraction.isAffinoidSubdomainMap`.

Flatness uses only the universal property. For every classical point `x ∈ U` and every `n`, it
gives isomorphisms `A ⧸ 𝔪ₓⁿ ≃ B ⧸ 𝔪ₓⁿ B`
(`TauCeti.IsAffinoidSubdomainMap.quotientPowAlgEquiv`), and every maximal ideal of `B` lies over
such a point. Since `A` and `B` are noetherian, the criterion
`RingHom.Flat.of_bijective_quotientMap_pow` turns these isomorphisms into flatness; it combines
the Artin–Rees lemma in `A` with the separation of finite `B`-modules by powers of maximal ideals.
No completion, Gerritzen–Grauert decomposition or adic comparison is used. Faithfulness uses the
classical point lifting theorem: every maximal ideal of `A` remains proper in some member of the
cover.

These are the algebraic descent inputs for affinoid-cover Čech complexes; no identification of
completed and algebraic tensor products is used.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.flat`: the restriction map of an affinoid subdomain is flat.
* `TauCeti.IsAffinoidSubdomainMap.faithfullyFlat_pi`: a finite affinoid cover gives a faithfully
  flat map into the product of the coordinate algebras.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.3.2 and 8.2.
-/

public section

namespace TauCeti

universe u

namespace IsAffinoidSubdomainMap

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- **Restriction maps of affinoid subdomains are flat.** If `φ : A → B` represents an affinoid
subdomain of `Sp A`, then `B` is flat over `A`. Nilpotents are allowed in `A`. -/
theorem flat {B : Type u} [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A) :
    φ.toRingHom.Flat := by
  have := hA.isNoetherianRing
  have := h.isAffinoidAlgebra.isNoetherianRing
  refine RingHom.Flat.of_bijective_quotientMap_pow fun n hn k ↦ ?_
  -- The point of `U` below a maximal ideal `𝔫` of `B` has maximal ideal `φ⁻¹ 𝔫`; `hn` is needed
  -- as an instance by `IsAffinoidAlgebra.comap_isMaximal`.
  have := hn
  let x : MaximalSpectrum A := ⟨n.comap φ, h.isAffinoidAlgebra.comap_isMaximal φ n⟩
  have hx : x ∈ U := by
    convert h.range_maximalSpectrumComap_subset ⟨⟨n, hn⟩, rfl⟩
    exact MaximalSpectrum.ext
      (IsAffinoidAlgebra.maximalSpectrumComap_asIdeal h.isAffinoidAlgebra φ ⟨n, hn⟩).symm
  have he : ⇑(h.quotientPowAlgEquiv hA hx k) =
      Ideal.quotientMap ((n.comap φ ^ k).map φ) φ.toRingHom Ideal.le_comap_map := by
    ext q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [quotientPowAlgEquiv_mk]
    -- The two sides differ only by `Ideal.map φ = Ideal.map φ.toRingHom`, which holds by `rfl`
    -- (`Ideal.map_coe`).
    exact (Ideal.quotientMap_mk ..).symm
  exact he ▸ (h.quotientPowAlgEquiv hA hx k).bijective

/-- **Finite affinoid covers are faithfully flat.** A finite family of affinoid subdomains
covering the classical spectrum gives a faithfully flat map into the product of their
representing algebras. -/
theorem faithfullyFlat_pi {ι : Type*} [Finite ι] {B : ι → Type u} [∀ i, CommRing (B i)]
    [∀ i, Algebra K (B i)] {φ : ∀ i, A →ₐ[K] B i} {U : ι → Set (MaximalSpectrum A)}
    (h : ∀ i, IsAffinoidSubdomainMap (φ i) (U i)) (hA : IsAffinoidAlgebra K A)
    (hcover : ∀ x : MaximalSpectrum A, ∃ i, x ∈ U i) :
    (RingHom.pi fun i ↦ (φ i).toRingHom).FaithfullyFlat :=
  RingHom.FaithfullyFlat.pi_of_exists_map_ne_top (fun i ↦ (h i).flat hA) fun M hM ↦
    let ⟨i, hi⟩ := hcover ⟨M, hM⟩
    ⟨i, ((h i).isMaximal_map hA hi).ne_top⟩

end IsAffinoidSubdomainMap

end TauCeti
