/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Tate cohomology of a directed union of subrepresentations

Let `G` be a finite group and `M` a representation of `G` that is the directed union of
subrepresentations `A i`, in the sense that the maps `f i : A i ⟶ M` are injective and every finite
subset of `M` lies in the image of one of them. This file shows that every Tate cohomology class
of `M`, in every integer degree, comes from one of the `A i`
(`TauCeti.TateCohomology.exists_tateCohomologyFunctor_map_eq`).

In degree `n ≥ 0` the Tate complex of `M` consists of the functions `Gⁿ → M`, and in degree
`n < 0` of the finitely supported functions `G^(-n-1) → M`. Either way an element has finitely many
values, since `G` is finite, so it comes from some `A i` (`exists_tateComplex_map_f_eq`). The
maps of Tate complexes induced by the `f i` are injective in every degree
(`tateComplex_map_f_injective`), so a lift of a cocycle is a cocycle, and the statement follows
from its counterpart for complexes of modules,
`HomologicalComplex.exists_homologyMap_eq_of_injective`.

This is how the Tate cohomology of the ideles of a number field, the union of the `S`-ideles over
the finite sets `S` of places, is computed from that of the `S`-ideles.

## Main results

* `TauCeti.TateCohomology.exists_tateCohomologyFunctor_map_eq`: a Tate cohomology class of a
  directed union of subrepresentations comes from one of them.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
-/

public section

open CategoryTheory groupCohomology groupHomology

universe u

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- An injective morphism of representations induces injective maps on the Tate complexes, in
every degree. -/
theorem tateComplex_map_f_injective {M N : Rep k G} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (n : ℤ) : Function.Injective ((tateComplex.map f).f n) := by
  rcases n with n | n
  · -- in degree `n ≥ 0` the map is `cochainsMap`, composition with `f` on functions `Gⁿ → M`
    simp only [CochainComplex.ConnectData.map_f]
    have : Function.Injective ((cochainsMap (MonoidHom.id G) f).f n).hom := by
      rw [cochainsMap_id_f_hom_eq_compLeft]
      exact hf.comp_left
    exact this
  · -- in degree `-n - 1` it is `chainsMap`, `Finsupp.mapRange f` on the inhomogeneous `n`-chains
    simp only [CochainComplex.ConnectData.map_f]
    have : Function.Injective ((chainsMap (MonoidHom.id G) f).f n).hom := by
      rw [chainsMap_id_f_hom_eq_mapRange]
      exact Finsupp.mapRange_injective _ (map_zero _) hf
    exact this

/-- If every finite subset of `M` lies in the image of one of the maps `f i : A i ⟶ M`, then every
element of the Tate complex of `M`, in every degree, comes from the Tate complex of one of the
`A i`. -/
theorem exists_tateComplex_map_f_eq {κ : Type*} {M : Rep k G} {A : κ → Rep k G}
    (f : ∀ i, A i ⟶ M) (hf : ∀ i, Function.Injective (f i).hom)
    (h : ∀ s : Finset M, ∃ i, ∀ m ∈ s, m ∈ Set.range (f i).hom) (n : ℤ)
    (z : (tateComplex M).X n) : ∃ i y, (tateComplex.map (f i)).f n y = z := by
  classical
  rcases n with n | n
  · -- in degree `n ≥ 0` the Tate complex is the module of inhomogeneous cochains
    -- (`CochainComplex.ConnectData.X_ofNat`), so `z` is a function on the finite set `Gⁿ`
    let z' : (Fin n → G) → M := z
    obtain ⟨i, hi⟩ := h (Finset.univ.image z')
    choose y hy using fun g ↦ hi (z' g) (Finset.mem_image_of_mem z' (Finset.mem_univ g))
    refine ⟨i, (y : (Fin n → G) → A i), ?_⟩
    -- the map is `cochainsMap`, composition with `f i`
    simp only [CochainComplex.ConnectData.map_f]
    have : ((cochainsMap (MonoidHom.id G) (f i)).f n).hom y = z' := by
      rw [cochainsMap_id_f_hom_eq_compLeft]
      exact funext hy
    exact this
  · -- in degree `-n - 1` the Tate complex is the module of inhomogeneous chains
    -- (`CochainComplex.ConnectData.X_negSucc`), so `z` is a finitely supported function on `Gⁿ`;
    -- lift its values through a section of `f i`
    let z' : (Fin n → G) →₀ M := z
    obtain ⟨i, hi⟩ := h (z'.support.image z')
    let g : M → A i := fun m ↦ if hm : m ∈ Set.range (f i).hom then hm.choose else 0
    have hg (m : M) (hm : m ∈ Set.range (f i).hom) : (f i).hom (g m) = m := by
      simp only [g, hm, ↓reduceDIte]
      exact hm.choose_spec
    have hg0 : g 0 = 0 := hf i (by rw [hg 0 ⟨0, map_zero _⟩, map_zero])
    refine ⟨i, (Finsupp.mapRange g hg0 z' : (Fin n → G) →₀ A i), ?_⟩
    -- the map is `chainsMap`, `Finsupp.mapRange (f i)`
    simp only [CochainComplex.ConnectData.map_f]
    have : ((chainsMap (MonoidHom.id G) (f i)).f n).hom (Finsupp.mapRange g hg0 z') = z' := by
      rw [chainsMap_id_f_hom_eq_mapRange]
      ext x
      refine hg _ ?_
      by_cases hx : x ∈ z'.support
      · exact hi _ (Finset.mem_image_of_mem z' hx)
      · rw [Finsupp.notMem_support_iff.1 hx]
        exact ⟨0, map_zero _⟩
    exact this

/-- **Tate cohomology of a directed union.** Let `f i : A i ⟶ M` be injective morphisms of
representations of a finite group such that every finite subset of `M` lies in the image of one
of them. Then every class of `H-hat^n(G, M)`, for every `n : ℤ`, is the image of a class of
`H-hat^n(G, A i)` for some `i`. -/
theorem exists_tateCohomologyFunctor_map_eq {κ : Type*} {M : Rep k G} {A : κ → Rep k G}
    (f : ∀ i, A i ⟶ M) (hf : ∀ i, Function.Injective (f i).hom)
    (h : ∀ s : Finset M, ∃ i, ∀ m ∈ s, m ∈ Set.range (f i).hom) (n : ℤ)
    (x : tateCohomology M n) : ∃ i y, ((tateCohomologyFunctor n).map (f i)).hom y = x :=
  HomologicalComplex.exists_homologyMap_eq_of_injective n (fun i ↦ tateComplex.map (f i))
    (fun i ↦ tateComplex_map_f_injective (f i) (hf i) _)
    (exists_tateComplex_map_f_eq f hf h n) x

end TauCeti.TateCohomology
