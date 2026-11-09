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

end TauCeti.LocalCoefficientSystem
