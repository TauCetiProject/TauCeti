/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso

/-!
# The small-chain theorem with local coefficients

For an open cover, the inclusion of subordinate twisted singular chains is a
quasi-isomorphism. Thus homology with arbitrary module-valued local coefficients can be
computed using only simplices lying in individual cover members. This is the homological
small-chain comparison needed for excision; no projectivity or freeness of the fibres is
required.

Subdivision makes each finite chain small. Its iterated prism identifies a cycle with its
subdivision modulo a boundary. For injectivity, the prism of an already small cycle stays
small, so subdividing a filling gives a filling inside the small-chain complex.

## References

* A. Hatcher, *Algebraic Topology*, proof of Proposition 2.21 and Section 3.H.
* The twisted subdivision and prism constructions in
  `TauCeti.AlgebraicTopology.Singular.Twisted.Subdivision`.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X) {ι : Type*} (U : ι → Set X)

/-- **The small-chain theorem with local coefficients.** The canonical inclusion of twisted
singular chains subordinate to an open cover induces isomorphisms on homology in every degree,
including degree zero. Coefficient fibres may be arbitrary modules over an arbitrary ring. -/
theorem quasiIso_smallTwistedChainComplexι (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) : QuasiIso (smallTwistedChainComplexι L U) := by
  rw [quasiIso_iff]
  intro n
  rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (n := n) (p := n + 1)
    (m := n - 1) (by simp)
    (by cases n <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])]
  let C := L.twistedChainComplex
  let S := smallTwistedChainComplex L U
  let j := smallTwistedChainComplexι L U
  have hj (k : ℕ) : Function.Injective (j.f k) :=
    (ModuleCat.mono_iff_injective (j.f k)).1 inferInstance
  have liftSmall {k : ℕ} (c : C.X k) (hc : c ∈ smallTwistedChains L U k) :
      ∃ a : S.X k, j.f k a = c := by
    rw [← range_smallTwistedChainComplexι_f L U k] at hc
    exact LinearMap.mem_range.1 hc
  constructor
  · -- Subdivide an ambient cycle, retaining its prism as the boundary correction.
    intro c hc
    obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_small L U hU hcov c
    let s := ((End.of (twistedSubdivisionChainMap L)) ^ N).asHom
    obtain ⟨a, ha⟩ := liftSmall (s.f n c) (hN N le_rfl)
    have hcycle : S.d n (n - 1) a = 0 := by
      apply hj (n - 1)
      rw [← HomologicalComplex.Hom.comm_apply, ha,
        HomologicalComplex.Hom.comm_apply, hc, map_zero, map_zero]
    exact ⟨a, hcycle, ((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) c,
      ha ▸ (by simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
        ((twistedSubdivisionHomotopy L).idPow N).d_hom_apply_of_d_eq_zero c hc)⟩
  · -- Subdivide a filling, then correct its boundary by the small cycle's prism.
    intro a ha b hb
    obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_small L U hU hcov b
    let s := ((End.of (twistedSubdivisionChainMap L)) ^ N).asHom
    obtain ⟨b', hb'⟩ := liftSmall (s.f (n + 1) b) (hN N le_rfl)
    have hsmall : j.f n a ∈ smallTwistedChains L U n := by
      rw [← range_smallTwistedChainComplexι_f L U n]
      exact LinearMap.mem_range_self _ a
    obtain ⟨p, hp⟩ := liftSmall
      (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) (j.f n a))
      (idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains L U hsmall N)
    have hcycle : C.d n (n - 1) (j.f n a) = 0 := by
      rw [HomologicalComplex.Hom.comm_apply, ha, map_zero]
    refine ⟨b' + p, hj n ?_⟩
    rw [← HomologicalComplex.Hom.comm_apply, map_add, map_add, hb', hp,
      HomologicalComplex.Hom.comm_apply, hb,
      ((twistedSubdivisionHomotopy L).idPow N).d_hom_apply_of_d_eq_zero _ hcycle,
      HomologicalComplex.id_f, ModuleCat.id_apply]
    abel

/-- Along the inclusion of a subset `S` containing every member of `U`, the chains of `S`
subordinate to the preimages of the members of `U` are identified with the chains of `X`
subordinate to `U`. -/
private lemma isIso_smallTwistedChainComplexMap_subtypeVal {S : Set X} (hUS : ∀ i, U i ⊆ S) :
    IsIso (smallTwistedChainComplexMap (fun i ↦ TopCat.ofHom (ContinuousMap.subtypeVal S) ⁻¹' U i)
      U (TopCat.ofHom (ContinuousMap.subtypeVal S)) L id
        fun i ↦ Set.mapsTo_preimage (TopCat.ofHom (ContinuousMap.subtypeVal S)) (U i)) := by
  have : Mono (TopCat.ofHom (ContinuousMap.subtypeVal S)) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  set φ := smallTwistedChainComplexMap (fun i ↦ TopCat.ofHom (ContinuousMap.subtypeVal S) ⁻¹' U i)
    U (TopCat.ofHom (ContinuousMap.subtypeVal S)) L id
      fun i ↦ Set.mapsTo_preimage (TopCat.ofHom (ContinuousMap.subtypeVal S)) (U i)
  -- `φ` followed by the inclusion of the small chains of `X` is the pushforward of the inclusion of
  -- the small chains of `S`.
  have hφ (n : ℕ) (a) : ((smallTwistedChainComplexι L U).f n).hom ((φ.f n).hom a) =
      ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal S)) L).f n).hom
        (((smallTwistedChainComplexι _ _).f n).hom a) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, smallTwistedChainComplexMap_ι]
  have hι (n : ℕ) := (ModuleCat.mono_iff_injective ((smallTwistedChainComplexι L U).f n)).1
    inferInstance
  suffices ∀ n, IsIso (φ.f n) from HomologicalComplex.Hom.isIso_of_components φ
  refine fun n ↦ (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab ↦ ?_, fun c ↦ ?_⟩
  · have hab' := congrArg ((smallTwistedChainComplexι L U).f n).hom hab
    rw [hφ, hφ] at hab'
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
      ((ModuleCat.mono_iff_injective _).1 inferInstance hab')
  · -- A chain subordinate to `U` is supported in `S`, hence the pushforward of a chain of `S`,
    -- which is subordinate to the preimages of the `U i`.
    have hc : ((smallTwistedChainComplexι L U).f n).hom c ∈ smallTwistedChains L U n := by
      rw [← range_smallTwistedChainComplexι_f]
      exact LinearMap.mem_range_self _ c
    obtain ⟨a, ha⟩ : ((smallTwistedChainComplexι L U).f n).hom c ∈ LinearMap.range
        ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal S)) L).f n).hom := by
      rw [range_twistedChainComplexMap_subtypeVal_f]
      exact smallTwistedChains_mono L U _ (fun _ ↦ ()) hUS n hc
    rw [← ha, twistedChainComplexMap_f_mem_smallTwistedChains_iff,
      ← range_smallTwistedChainComplexι_f] at hc
    obtain ⟨b, rfl⟩ := hc
    exact ⟨b, hι n (by rw [hφ, ha])⟩

/-- **The small-chain theorem inside a subset.** If the members of a family `U` lie in a subset `S`
of `X`, cover it, and are open in `S`, then the inclusion of the twisted chains subordinate to `U`
into the twisted chains supported in `S` induces isomorphisms on homology in every degree. -/
theorem quasiIso_smallTwistedChainComplexInclusion {S : Set X} (hUS : ∀ i, U i ⊆ S)
    (hSU : S ⊆ ⋃ i, U i) (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set S)) :
    QuasiIso (smallTwistedChainComplexInclusion (V := fun _ : Unit ↦ S)
      fun n ↦ smallTwistedChains_mono L U _ (fun _ ↦ ()) hUS n) := by
  -- Compare with the small-chain theorem for the cover of `S` by the preimages of the `U i`.
  have := isIso_smallTwistedChainComplexMap_subtypeVal L U hUS
  have : QuasiIso (smallTwistedChainComplexι
      ((pullback (TopCat.ofHom (ContinuousMap.subtypeVal S)).hom).obj L)
      (fun i ↦ TopCat.ofHom (ContinuousMap.subtypeVal S) ⁻¹' U i)) :=
    quasiIso_smallTwistedChainComplexι _ _ hU <| Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hSU x.2)
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  rw [← quasiIso_iff_comp_left (smallTwistedChainComplexMap _ U _ L id
    fun i ↦ Set.mapsTo_preimage (TopCat.ofHom (ContinuousMap.subtypeVal S)) (U i))]
  convert (inferInstance : QuasiIso (smallTwistedChainComplexι
    ((pullback (TopCat.ofHom (ContinuousMap.subtypeVal S)).hom).obj L)
    (fun i ↦ TopCat.ofHom (ContinuousMap.subtypeVal S) ⁻¹' U i) ≫
      (subspaceTwistedChainComplexIso L S).hom)) using 1
  apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ S))).1
  simp

end TauCeti.LocalCoefficientSystem
