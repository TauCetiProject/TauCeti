/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Torsion
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Joint detection in formal glueing

Let `R → S` be flat, let `G` be a finite set of elements of `R`, and suppose the induced map
`R/I → S/IS` is bijective, where `I = (G)`. An element of any `R`-module is zero if it is zero
both after base change to `S` and after localization at every element of `G`. Consequently,
injectivity, surjectivity and bijectivity of module maps can be tested on these pieces.

The element criterion proves injectivity of the first map in the formal-glueing complex
`0 → M → (S ⊗ M) × ∏ M_g → ⋯`. It does not assert exactness at the next term, which additionally
requires existence of a lift of compatible local elements. The map-detection criteria allow
one to check a proposed reconstruction isomorphism on the same pieces.

## References

* [Stacks Project, Lemma 15.91.9](https://stacks.math.columbia.edu/tag/05EK), injectivity of the
  first map, using the ideal-power torsion comparison of Lemma 15.91.3 (05EC).
-/

public section

open TensorProduct Function

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  {G : Finset R}
  (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
    (algebraMap R S) Ideal.le_comap_map))
  {M : Type*} [AddCommGroup M] [Module R M]

include hG

/-- An element is zero if it vanishes after formal-glueing base change and on each principal
open of the complement. No finiteness assumption on the module is needed. -/
theorem eq_zero_of_one_tmul_eq_zero_of_localized (m : M) (hS : (1 : S) ⊗ₜ[R] m = 0)
    (hloc : ∀ g ∈ G, LocalizedModule.mkLinearMap (.powers g) M m = 0) : m = 0 := by
  have hm : m ∈ (Ideal.span (G : Set R)).primaryComponent M := by
    refine (Ideal.mem_primaryComponent_span_iff G).mpr fun g hg ↦ ?_
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (.powers g)
      (LocalizedModule.mkLinearMap (.powers g) M)).mp (hloc g hg)
    obtain ⟨n, hn⟩ := s.2
    exact ⟨n, by simpa only [Submonoid.smul_def, ← hn] using hs⟩
  have hfg : (Ideal.span (G : Set R)).FG := ⟨G, rfl⟩
  let e := primaryComponentEquivTensorProduct (M := M) hG hfg
  have he : e ⟨m, hm⟩ = 0 := Subtype.ext <|
    (coe_primaryComponentEquivTensorProduct_apply hG hfg ⟨m, hm⟩).trans hS
  exact congrArg Subtype.val (e.injective (he.trans (map_zero e).symm))

/-- A module is zero if its base change and each principal localization in the
formal-glueing cover are zero. No finite generation of the module is required. -/
theorem subsingleton_of_baseChange_and_localized [Subsingleton (S ⊗[R] M)]
    (hloc : ∀ g ∈ G, Subsingleton (LocalizedModule (.powers g) M)) : Subsingleton M := by
  refine (subsingleton_iff_forall_eq 0).mpr fun m ↦ ?_
  apply eq_zero_of_one_tmul_eq_zero_of_localized hG m (Subsingleton.elim _ _)
  intro g hg
  have := hloc g hg
  exact Subsingleton.elim _ _

/-- **Injectivity of the formal-glueing augmentation.** A module embeds into the product of
its base change and its principal localizations. This is the first exactness assertion in
Stacks 05EK, not the assertion that all compatible local elements have a global lift. -/
@[stacks 05EK "injectivity of the first map"]
theorem injective_mk_prod_pi_mkLinearMap :
    Injective ((TensorProduct.mk R S M 1).prod
      (LinearMap.pi fun g : G ↦ LocalizedModule.mkLinearMap (.powers (g : R)) M)) := by
  refine (injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_
  exact eq_zero_of_one_tmul_eq_zero_of_localized hG m (congrArg Prod.fst hm)
    (fun g hg ↦ congrFun (congrArg Prod.snd hm) ⟨g, hg⟩)

end TauCeti

namespace LinearMap

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  {G : Finset R}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Injectivity can be tested after a flat base change that preserves `R/(G)`, together with
localization at the generators of `(G)`. -/
theorem injective_iff_baseChange_and_localized (f : M →ₗ[R] N)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Injective f ↔ Injective (f.baseChange S) ∧
      ∀ g ∈ G, Injective (LocalizedModule.map (.powers g) f) := by
  refine ⟨fun hf ↦ ⟨Module.Flat.lTensor_preserves_injective_linearMap f hf,
    fun g _ ↦ LocalizedModule.map_injective _ f hf⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  refine (injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_
  apply TauCeti.eq_zero_of_one_tmul_eq_zero_of_localized hG m
  · apply (injective_iff_map_eq_zero _).mp hS
    simp [hm]
  · intro g hg
    apply (injective_iff_map_eq_zero _).mp (hloc g hg)
    simp [hm]

/-- Surjectivity can be tested on the formal-glueing pieces, without finite generation of
either module. -/
theorem surjective_iff_baseChange_and_localized (f : M →ₗ[R] N)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Surjective f ↔ Surjective (f.baseChange S) ∧
      ∀ g ∈ G, Surjective (LocalizedModule.map (.powers g) f) := by
  refine ⟨fun hf ↦ ⟨f.lTensor_surjective S hf,
    fun g _ ↦ LocalizedModule.map_surjective _ f hf⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  have : Subsingleton (S ⊗[R] (N ⧸ f.range)) :=
    (Submodule.baseChange_eq_top_iff_subsingleton S f.range).mp (by
      rw [LinearMap.baseChange_range]
      exact LinearMap.range_eq_top.mpr hS)
  have : Subsingleton (N ⧸ f.range) :=
    TauCeti.subsingleton_of_baseChange_and_localized hG fun g hg ↦
      (f.localizedMap_surjective_iff_subsingleton_localized_coker (.powers g)).mp (hloc g hg)
  intro n
  simpa using (Subsingleton.elim (f.range.mkQ n) 0)

/-- A module map is an isomorphism if and only if it is an isomorphism on every
formal-glueing piece. -/
theorem bijective_iff_baseChange_and_localized (f : M →ₗ[R] N)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Bijective f ↔ Bijective (f.baseChange S) ∧
      ∀ g ∈ G, Bijective (LocalizedModule.map (.powers g) f) := by
  simp only [Bijective, f.injective_iff_baseChange_and_localized hG,
    f.surjective_iff_baseChange_and_localized hG, forall_and]
  tauto

end LinearMap
