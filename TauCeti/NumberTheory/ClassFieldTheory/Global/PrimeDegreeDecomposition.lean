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
import TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup

/-!
# A place of full local degree in a prime-degree Galois extension

Let `E/F` be a Galois extension of number fields of prime degree. Some finite place `w` of `E`
has nontrivial decomposition group: otherwise `E/F` would split completely at every finite place,
and the first fundamental inequality would force `E = F`. Since `Gal(E/F)` has prime order, that
nontrivial decomposition group is the whole Galois group. The identification of a decomposition
group with the Galois group of the corresponding completion then shows that, for `F` an extension
of a number field `K` and `E` embedded in `Kˢ`, every element of `Gal(E/F)` is the action on `E` of
the image of an element of the absolute Galois group of some completion `K_v`.

Read on the absolute Galois group `G_K`, this applies to the finite normal layers `V ◁ U` of prime
degree: with `F` and `E` the fixed fields of `U` and `V`, it produces an embedding of separable
closures `τ : Kˢ → K_vˢ` for which the decomposition map `φ_τ⁻¹(U) → U ⧸ V` is onto. When `U` is
the whole of `G_K` this is the quotient `G_{K_v} → G_K ⧸ V`. This is the local-degree input used to
construct prescribed idele-layer invariants in prime-degree layers.

## Main results

* `TauCeti.ClassFieldTheory.exists_stabilizer_eq_top_of_finrank_prime`: a prime-degree Galois
  extension of number fields has a finite place whose decomposition group is the whole Galois group.
* `AlgHom.exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime`: for a prime-degree Galois
  extension `E/F` of extensions of `K` and an embedding `ι : E → Kˢ`, some local absolute Galois
  group `G_{K_v}` realizes every element of `Gal(E/F)` on `ι(E)`.
* `IntermediateField.exists_surjective_restrictNormalHom_absoluteGaloisGroupMap_of_finrank_prime`:
  a prime-degree finite Galois subextension of `Kˢ/K` has a finite place whose local absolute
  Galois group restricts onto its Galois group.
* `OpenNormalSubgroup.exists_surjective_quotient_absoluteGaloisGroupMap_of_degree_prime`:
  the corresponding statement for the quotient attached to a prime-degree open normal layer.
* `TauCeti.ClassFieldTheory.NormalLayer.exists_surjective_absoluteGaloisGroupMap_of_degree_prime`:
  for every finite normal layer `V ◁ U` of `G_K` of prime degree, some decomposition map
  `φ_τ⁻¹(U) → U ⧸ V` is onto.

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

namespace AlgHom

open TauCeti TauCeti.ClassFieldTheory

/-- **A prime-degree Galois extension is realized by a local absolute Galois group.** Let `F` be a
number field over `K`, `E/F` a Galois extension of number fields of prime degree, and
`ι : E →ₐ[K] Kˢ` an embedding into the separable closure of `K`. Then for some finite place `v`
of `K` and some embedding `τ : Kˢ → K_vˢ`, every `σ ∈ Gal(E/F)` acts on `ι(E)` as the image under
`absoluteGaloisGroupMap τ` of some element of `G_{K_v}`. -/
theorem exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra K F] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [IsGalois F E] (ι : E →ₐ[K] SeparableClosure K)
    (hE : (Module.finrank F E).Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      ∀ σ : Gal(E/F), ∃ g : AbsoluteGaloisGroup (v.adicCompletion K),
        ∀ x, absoluteGaloisGroupMap τ g (ι x) = ι (σ x) := by
  -- A place `w` of `E` above a place `u` of `F` whose decomposition group is all of `Gal(E/F)`.
  obtain ⟨u, ⟨w, _⟩, hw⟩ := exists_stabilizer_eq_top_of_finrank_prime hE
  obtain ⟨τ, hτ⟩ := ι.exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer
    (v := u.under (𝓞 K)) (u := u) w
  exact ⟨_, τ, fun σ ↦ hτ σ (hw ▸ Subgroup.mem_top σ)⟩

end AlgHom

namespace IntermediateField

open TauCeti

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
  obtain ⟨v, τ, hτ⟩ := L.val.exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime (F := K) hL
  exact ⟨v, τ, fun σ ↦ (hτ σ).imp fun g hg ↦ AlgEquiv.ext fun x ↦ Subtype.ext <|
    (AlgEquiv.restrictNormal_commutes _ L x).trans (hg x)⟩

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

namespace TauCeti.ClassFieldTheory.NormalLayer

open TauCeti IntermediateField

/-- **A prime-degree layer has a surjective decomposition map at some finite place.** Let
`V ◁ U` be a finite normal layer of `G_K` of prime degree. There are a finite place `v` of `K` and
an embedding `τ : Kˢ → K_vˢ` for which the decomposition map `φ_τ⁻¹(U) → U ⧸ V`, induced by
`absoluteGaloisGroupMap τ : G_{K_v} → G_K`, is onto. -/
theorem exists_surjective_absoluteGaloisGroupMap_of_degree_prime
    (L : NormalLayer (AbsoluteGaloisGroup K)) (hL : L.degree.Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      Function.Surjective fun g : L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) ↦
        ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup g : L.Gal) := by
  -- The fixed fields `F` of `U` and `E` of `V`: `E/F` is Galois, of prime degree.
  obtain ⟨F, hF⟩ : ∃ F, fixedField L.ground.toSubgroup = F := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, fixedField L.top.toSubgroup = E := ⟨_, rfl⟩
  have hle : F ≤ E := hF ▸ hE ▸ fixedField_le (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)
  have : FiniteDimensional K F := hF ▸ finiteDimensional_fixedField_toSubgroup L.ground
  have : FiniteDimensional K E := hE ▸ finiteDimensional_fixedField_toSubgroup L.top
  have : NumberField F := .of_module_finite K F
  have : NumberField E := .of_module_finite K E
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower F E (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K F E := .of_algebraMap_eq fun _ ↦ rfl
  have := L.isGalois_of_fixedField hF hE
  let e := L.galEquivOfFixedField hF hE
  have hfin : (Module.finrank F E).Prime := by
    rwa [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr e.toEquiv,
      ← NormalLayer.degree_eq_natCard_gal]
  obtain ⟨v, τ, hτ⟩ := E.val.exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime hfin
  refine ⟨v, τ, fun γ ↦ ?_⟩
  obtain ⟨g, hg⟩ := hτ (e γ)
  -- The image of `g` acts on `F` as `e γ` does, trivially, so it lies in `U`.
  have hgU : g ∈ L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) := by
    rw [Subgroup.mem_comap, toSubgroup_eq_fixingSubgroup_of_fixedField_eq hF]
    rintro ⟨x, hx⟩
    exact (hg ⟨x, hle hx⟩).trans (congrArg E.val ((e γ).commutes ⟨x, hx⟩))
  refine ⟨⟨g, hgU⟩, e.injective (AlgEquiv.ext fun x ↦ Subtype.ext ?_)⟩
  rw [coe_galEquivOfFixedField_mk_apply, ContinuousMonoidHom.subgroupComap_apply_coe]
  exact hg x

end TauCeti.ClassFieldTheory.NormalLayer
