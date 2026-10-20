/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# A place of full local degree in a prime-degree Galois extension

Let `L/K` be a Galois extension of number fields of prime degree. Some finite place `w` of `L`
has nontrivial decomposition group: otherwise `L/K` would split completely at every finite place,
and the first fundamental inequality would force `L = K`. Since `Gal(L/K)` has prime order, that
nontrivial decomposition group is the whole Galois group. The identification of a decomposition
group with the Galois group of the corresponding completion then shows that the restriction map
from the absolute Galois group of `K_v` onto `Gal(L/K)` is surjective.

The quotient form applies this result to the finite extension cut out by an open normal subgroup
`V` of `G_K`. It produces an embedding of separable closures for which the decomposition map
`G_{K_v} → G_K / V` is onto. This is the local-degree input used to construct prescribed
idele-layer invariants in prime-degree layers.

## Main results

* `TauCeti.ClassFieldTheory.exists_stabilizer_eq_top_of_finrank_prime`: a prime-degree Galois
  extension of number fields has a finite place whose decomposition group is the whole Galois group.
* `IntermediateField.exists_surjective_restrictNormalHom_absoluteGaloisGroupMap_of_finrank_prime`:
  a prime-degree finite Galois subextension of `Kˢ/K` has a finite place whose local absolute
  Galois group restricts onto its Galois group.
* `OpenNormalSubgroup.exists_surjective_quotient_absoluteGaloisGroupMap_of_degree_prime`:
  the corresponding statement for the quotient attached to a prime-degree open normal layer.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Propositions 4.6 and 4.7.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise

variable {K : Type} [Field K] [NumberField K]

namespace TauCeti.ClassFieldTheory

variable {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **A prime-degree Galois extension has a prime with full decomposition group.** If `L/K` is a
Galois extension of number fields of prime degree, then some finite place `w` of `L` has
decomposition group all of `Gal(L/K)`. Otherwise every decomposition group would be trivial, as
`Gal(L/K)` has prime order, and `finrank_eq_one_of_stabilizer_eq_bot` would force `L = K`. -/
theorem exists_stabilizer_eq_top_of_finrank_prime [IsGalois K L]
    (hL : (Module.finrank K L).Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}),
      MulAction.stabilizer Gal(L/K) w.1.asIdeal = ⊤ := by
  let _ : Fact (Nat.card Gal(L/K)).Prime := ⟨by
    rwa [IsGalois.card_aut_eq_finrank K L]⟩
  let _ : IsCyclic Gal(L/K) := isCyclic_of_prime_card (p := Nat.card Gal(L/K)) rfl
  let _ : IsMulCommutative Gal(L/K) := IsCyclic.isMulCommutative
  have hnot : ¬ ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        MulAction.stabilizer Gal(L/K) w.1.asIdeal = ⊥ := fun h ↦
    hL.ne_one (finrank_eq_one_of_stabilizer_eq_bot (∅ : Finset _) fun v _ ↦ h v)
  push Not at hnot
  obtain ⟨v, hv⟩ := hnot
  obtain ⟨w₀, hw₀⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  let w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    ⟨w₀, hw₀ ▸ inferInstance⟩
  refine ⟨v, w, ?_⟩
  exact (Subgroup.eq_bot_or_eq_top_of_prime_card
    (MulAction.stabilizer Gal(L/K) w.1.asIdeal)).resolve_left (hv w)

end TauCeti.ClassFieldTheory

namespace IntermediateField

open TauCeti TauCeti.ClassFieldTheory

/-- **A prime-degree Galois extension has a place of full local degree.** If `L/K` is a finite
Galois subextension of the separable closure and `[L : K]` is prime, then at some finite place
`v` the map from `G_{K_v}` to `Gal(L/K)`, obtained by an embedding `Kˢ → K_vˢ` and
restriction to `L`, is surjective. -/
theorem exists_surjective_restrictNormalHom_absoluteGaloisGroupMap_of_finrank_prime
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hL : (Module.finrank K L).Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      Function.Surjective fun g : AbsoluteGaloisGroup (v.adicCompletion K) ↦
        AlgEquiv.restrictNormalHom L (absoluteGaloisGroupMap τ g) := by
  let _ : NumberField L := NumberField.of_module_finite K L
  obtain ⟨v, w, hw⟩ := exists_stabilizer_eq_top_of_finrank_prime hL
  let _ : w.1.asIdeal.LiesOver v.asIdeal := w.2
  -- Lift the restriction `L → L_w → K_vˢ` to an embedding `Kˢ → K_vˢ`, then lift each element
  -- of `Gal(L/K) = D_w ≃ Gal(L_w/K_v)` through `G_{K_v} → Gal(L_w/K_v)`.
  let τ' : w.1.adicCompletion L →ₐ[v.adicCompletion K]
      SeparableClosure (v.adicCompletion K) := IsSepClosed.lift
  let φ : L →ₐ[K] SeparableClosure (v.adicCompletion K) :=
    (τ'.restrictScalars K).comp (IsScalarTower.toAlgHom K L (w.1.adicCompletion L))
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable
    L (E := SeparableClosure K) (M := SeparableClosure (v.adicCompletion K)) φ
  have hτ_apply (x : L) : τ x = τ' (algebraMap L (w.1.adicCompletion L) x) :=
    congrArg (fun f : L →ₐ[K] _ ↦ f x) hτ
  refine ⟨v, τ, fun σ ↦ ?_⟩
  let σw : MulAction.stabilizer Gal(L/K) w.1.asIdeal := ⟨σ, by rw [hw]; trivial⟩
  obtain ⟨g, hg⟩ := τ'.restrictNormalHom_surjective
    (HeightOneSpectrum.decompositionHom v w.1 σw)
  refine ⟨g, AlgEquiv.ext fun x ↦ ?_⟩
  apply Subtype.ext
  apply τ.injective
  have hres :
      (((AlgEquiv.restrictNormalHom L (absoluteGaloisGroupMap τ g)) x : L) :
          SeparableClosure K) = absoluteGaloisGroupMap τ g (x : SeparableClosure K) :=
    AlgEquiv.restrictNormal_commutes (absoluteGaloisGroupMap τ g) L x
  -- The goal applies `τ` through `τ.toRingHom`; restate it with the algebra-hom coercion used by
  -- `absoluteGaloisGroupMap_commutes` and `hτ_apply`.
  change τ _ = τ _
  calc
    _ = τ (absoluteGaloisGroupMap τ g (x : SeparableClosure K)) := congrArg τ hres
    _ = g (τ x) := absoluteGaloisGroupMap_commutes τ g x
    _ = g (τ' (algebraMap L (w.1.adicCompletion L) x)) := by rw [hτ_apply]
    _ = τ' (τ'.restrictNormalHom g (algebraMap L (w.1.adicCompletion L) x)) :=
      (AlgHom.restrictNormalHom_commutes τ' g _).symm
    _ = τ' (algebraMap L (w.1.adicCompletion L) (σ x)) := by
      rw [hg, HeightOneSpectrum.decompositionHom_algebraMap]
    _ = τ (σ x) := (hτ_apply (σ x)).symm

end IntermediateField

namespace OpenNormalSubgroup

open TauCeti TauCeti.ClassFieldTheory

/-- **A prime-degree layer has a surjective decomposition map at some finite place.** Let `V` be
an open normal subgroup of `G_K` whose layer has prime degree. There are a finite place `v` and an
embedding `τ : Kˢ → K_vˢ` for which the induced map `G_{K_v} → G_K / V` is onto. -/
theorem exists_surjective_quotient_absoluteGaloisGroupMap_of_degree_prime
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hV : (NormalLayer.ofOpenNormal V).degree.Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      Function.Surjective fun g : AbsoluteGaloisGroup (v.adicCompletion K) ↦
        (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup) := by
  have hfin : (Module.finrank K (classField K V)).Prime := by
    rw [← IsGalois.card_aut_eq_finrank K (classField K V),
      Nat.card_congr (galClassFieldEquiv V).toEquiv]
    simpa only [NormalLayer.degree_eq_natCard_gal] using hV
  obtain ⟨v, τ, hsurj⟩ :=
    IntermediateField.exists_surjective_restrictNormalHom_absoluteGaloisGroupMap_of_finrank_prime
      (classField K V) hfin
  refine ⟨v, τ, fun q ↦ ?_⟩
  let e : Gal(classField K V/K) ≃* AbsoluteGaloisGroup K ⧸ V.toSubgroup :=
    (galClassFieldEquiv V).trans (NormalLayer.galOfOpenNormalEquiv V)
  obtain ⟨g, hg⟩ := hsurj (e.symm q)
  refine ⟨g, ?_⟩
  -- Expose the quotient map hidden by the function in the surjectivity statement.
  change (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup) = q
  calc
    _ = e (AlgEquiv.restrictNormalHom (classField K V) (absoluteGaloisGroupMap τ g)) :=
      (galOfOpenNormalEquiv_galClassFieldEquiv_restrictNormalHom V
        (absoluteGaloisGroupMap τ g)).symm
    _ = e (e.symm q) := congrArg e hg
    _ = q := e.apply_symm_apply q

end OpenNormalSubgroup
