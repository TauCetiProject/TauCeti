/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
public import TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup

/-!
# Places of full local degree in extensions of prime degree

Let `L/K` be a Galois extension of number fields of prime degree `p`. The decomposition group of
a place `w` of `L` is a subgroup of the group `Gal(L/K)` of order `p`, so it is trivial or
everything: the place below `w` splits completely, or it has a single place above it with local
degree `p`. A nontrivial solvable extension does not split completely at almost every place
(`TauCeti.ClassFieldTheory.finrank_eq_one_of_stabilizer_eq_bot`, a consequence of the first
fundamental inequality), so outside every finite set of finite places of `K` there is one whose
places above it have decomposition group the whole of `Gal(L/K)`
(`exists_notMem_forall_stabilizer_eq_top_of_finrank_prime`).

In the language of the absolute Galois group `G_K = Gal(Kˢ/K)`: an open normal subgroup `V` of
`G_K` of prime index is the subgroup fixing a Galois extension `E` of `K` of prime degree inside
`Kˢ`, with `G_K ⧸ V ≃ Gal(E/K)`. For a place `v` as above and the embedding `τ : Kˢ →ₐ[K] K_vˢ`
of `AlgHom.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap`, the
decomposition map `G_{K_v} → G_K` composed with `G_K → G_K ⧸ V` is surjective
(`OpenNormalSubgroup.exists_notMem_surjective_absoluteGaloisGroupMap_of_index_prime`). This is the
form in which a place of full local degree enters cohomological arguments over `G_K`, for instance
to evaluate a character of `G_K ⧸ V` on a local Artin symbol at `v`.

## Main results

* `TauCeti.ClassFieldTheory.exists_notMem_forall_stabilizer_eq_top_of_finrank_prime`: a Galois
  extension of number fields of prime degree has, outside every finite set of finite places of
  the ground field, a place at which every decomposition group is the whole Galois group.
* `OpenNormalSubgroup.exists_notMem_surjective_absoluteGaloisGroupMap_of_index_prime`: for
  an open normal subgroup `V` of `G_K` of prime index, outside every finite set of finite places
  of `K` there are a place `v` and an embedding `τ : Kˢ →ₐ[K] K_vˢ` along which `G_{K_v}` maps
  onto `G_K ⧸ V`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 4.6.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

open IsDedekindDomain NumberField
open scoped Pointwise

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **An extension of prime degree has places of full local degree.** Let `L/K` be a Galois
extension of number fields of prime degree and `S` a finite set of finite places of `K`. Then some
finite place `v ∉ S` has decomposition group the whole of `Gal(L/K)` at every place `w` of `L`
above it. -/
theorem exists_notMem_forall_stabilizer_eq_top_of_finrank_prime {L : Type} [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (hL : (Module.finrank K L).Prime)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v ∉ S, ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal = ⊤ := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime := ⟨(IsGalois.card_aut_eq_finrank K L).symm ▸ hL⟩
  have : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card rfl
  -- Otherwise every place outside `S` has a place above it whose decomposition group, a proper
  -- subgroup of a group of prime order, is trivial; then `L = K`.
  by_contra! h
  exact hL.ne_one (finrank_eq_one_of_stabilizer_eq_bot S fun v hv ↦
    (h v hv).imp fun w hw ↦ (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_right hw)

end TauCeti.ClassFieldTheory

namespace OpenNormalSubgroup

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **Decomposition maps onto a quotient of `G_K` of prime order.** Let `V` be an open normal
subgroup of `G_K = Gal(Kˢ/K)` of prime index and `S` a finite set of finite places of `K`. Then
there are a finite place `v ∉ S` and an embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ` such
that the decomposition map `absoluteGaloisGroupMap τ : G_{K_v} → G_K`, followed by the quotient
map `G_K → G_K ⧸ V`, is surjective. -/
theorem exists_notMem_surjective_absoluteGaloisGroupMap_of_index_prime
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hV : V.toSubgroup.index.Prime)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v ∉ S, ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      Function.Surjective fun g : AbsoluteGaloisGroup (v.adicCompletion K) ↦
        (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup) := by
  -- `V` fixes a finite Galois subextension `E` of `Kˢ/K`, and `G_K ⧸ V ≃ Gal(E/K)` by restriction.
  obtain ⟨E, _, _, rfl⟩ := exists_galoisOpenNormalSubgroup_eq V
  have : NumberField E := NumberField.of_module_finite K E
  let e : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K E E.val).toSubgroup ≃* Gal(E/K) :=
    (QuotientGroup.quotientMulEquivOfEq (galoisOpenNormalSubgroup_toSubgroup K E E.val)).trans
      (quotientFixingSubgroupFieldRangeEquiv K E E.val)
  have hE : (Module.finrank K E).Prime := by
    rwa [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr e.toEquiv, ← Subgroup.index]
  obtain ⟨v, hvS, hv⟩ := exists_notMem_forall_stabilizer_eq_top_of_finrank_prime hE S
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  obtain ⟨τ, hτ⟩ :=
    E.val.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap
      (v := w.under (𝓞 K)) w
  refine ⟨_, hvS, τ, fun q ↦ ?_⟩
  -- The class `q` restricts to an element of the decomposition group of `w`, which is everything.
  obtain ⟨g, hg⟩ := hτ ((hv ⟨w, inferInstance⟩).ge (Subgroup.mem_top (e q)))
  refine ⟨g, e.injective ?_⟩
  simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    quotientFixingSubgroupFieldRangeEquiv_mk]
  exact hg

end OpenNormalSubgroup
