/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic

import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
import TauCeti.Topology.Connected.ProperRay

/-!
# Degree-zero Borel–Moore homology of spaces without compact components

Let `X` be a locally compact, σ-compact Hausdorff space which is locally path-connected and none
of whose connected components is compact, for instance a second-countable manifold without
compact components. Then degree-zero Borel–Moore homology of `X` vanishes, for every local
coefficient system `L` (`TauCeti.LocalCoefficientSystem.isZero_borelMooreHomology_zero`). In
contrast, zeroth singular homology is the colimit of `L` over the fundamental groupoid, which is
nonzero for a nonzero constant system. In Borel–Moore homology a point can be pushed off to
infinity along a proper ray, because the infinite chain swept out by the ray is locally finite.

Concretely, every locally finite `0`-chain `c` is the boundary of a locally finite `1`-chain
(`TauCeti.LocalCoefficientSystem.locallyFiniteBoundary_zero_surjective`). The points `p i` where `c`
has a nonzero coefficient `c i` form a locally finite family, so they start a locally finite
family of rays: paths `q i k` from `z i k` to `z i (k + 1)` with `z i 0 = p i`
(`TauCeti.exists_locallyFinite_range_path`). Transporting `c i` along the first `k` paths of its
ray gives a coefficient `m i k` in the fibre at `z i k`. The singular `1`-simplex of `q i k`
carrying `-m i k` has boundary `[z i k] m i k - [z i (k + 1)] m i (k + 1)`
(`TauCeti.LocalCoefficientSystem.d_ιTwistedChainComplex_simplex₁_apply`). These chains lie on the
locally finite family of path images, so their sum is locally finite, and its boundary is the sum
of their boundaries (`locallyFiniteBoundary_locallyFiniteSum`), which telescopes along each
ray to `[p i] c i`.

## Main results

* `TauCeti.LocalCoefficientSystem.locallyFiniteBoundary_zero_surjective`: every locally finite
  `0`-chain is a boundary.
* `TauCeti.LocalCoefficientSystem.isZero_borelMooreHomology_zero`: degree-zero Borel–Moore
  homology vanishes.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V
  (Borel–Moore homology of noncompact spaces).
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

open TauCeti.TopCat

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The path class of the concatenation of the first `k` paths of a sequence of composable
paths. -/
private def rayTransport {z : ℕ → X} (q : ∀ k, Path (z k) (z (k + 1))) (k : ℕ) :
    FundamentalGroupoid.mk (z 0) ⟶ FundamentalGroupoid.mk (z k) :=
  match k with
  | 0 => 𝟙 _
  | k + 1 => rayTransport q k ≫ Path.Homotopic.Quotient.mk (q k)

variable [T2Space X] [WeaklyLocallyCompactSpace X] [LocallyPathConnectedSpace X]
  [SigmaCompactSpace X]

/-- On a locally compact, σ-compact, locally path-connected Hausdorff space without compact
connected components, every locally finite `0`-chain with local coefficients is the boundary of a
locally finite `1`-chain: each point carrying a coefficient is joined to infinity by a proper
ray. -/
theorem locallyFiniteBoundary_zero_surjective
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    Function.Surjective (locallyFiniteBoundary L 0) := by
  classical
  rintro ⟨c, hc⟩
  rw [mem_locallyFiniteChains] at hc
  -- The singular vertices carrying a nonzero coefficient, and the rays they start.
  let S := {σ : (TopCat.toSSet.obj X) _⦋0⦌ // c σ ≠ 0}
  have hS : ∀ i : S, simplexMap i.1 (toTopInitialVertex _) = TopCat.toSSetObj₀Equiv i.1 :=
    fun i ↦ congrArg FundamentalGroupoid.as (initialVertex_zero i.1)
  have hp : LocallyFinite fun i : S ↦ ({TopCat.toSSetObj₀Equiv i.1} : Set X) := by
    refine ((isLocallyFiniteChain_iff_locallyFinite.1 hc).comp_injective
      Subtype.val_injective).subset fun i ↦ ?_
    rintro _ rfl
    exact ⟨i.2, _, hS i⟩
  obtain ⟨z, q, hz0, hq⟩ := exists_locallyFinite_range_path hX _ hp
  -- The coefficient of `c` at the start of each ray, transported along the ray.
  let m : ∀ i k, L.obj (FundamentalGroupoid.mk (z i k)) := fun i k ↦
    (L.map (eqToHom ((initialVertex_zero i.1).trans (congrArg FundamentalGroupoid.mk (hz0 i).symm))
      ≫ rayTransport (q i) k)).hom (c i.1)
  -- The vertex chains along the rays, and the edge chains whose boundaries are their differences.
  let e : S × ℕ → (twistedChainComplex L).X 0 := fun ik ↦
    (ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm (z ik.1 ik.2))).hom (m ik.1 ik.2)
  let y : S × ℕ → (twistedChainComplex L).X 1 := fun ik ↦
    (ιTwistedChainComplex L 1 (simplex₁ (q ik.1 ik.2).toContinuousMap)).hom
      ((L.map (eqToHom (initialVertex_simplex₁ (q ik.1 ik.2)).symm)).hom (-m ik.1 ik.2))
  have hm (i : S) (k : ℕ) :
      m i (k + 1) = (L.map (Path.Homotopic.Quotient.mk (q i k))).hom (m i k) := by
    simp only [m, rayTransport, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hdy (ik : S × ℕ) :
      ((twistedChainComplex L).d 1 0).hom (y ik) = e ik - e (ik.1, ik.2 + 1) := by
    simp only [y, e, map_neg, d_ιTwistedChainComplex_simplex₁_apply, neg_sub, hm]
  have hy (ik : S × ℕ) σ (hσ : (twistedChainComplexCoeff L σ).hom (y ik) ≠ 0) :
      Set.range (simplexMap σ) ⊆ Set.range (q ik.1 ik.2) :=
    range_simplexMap_subset_range_of_ne_zero_simplex₁ L _ hσ
  have he (ik : S × ℕ) σ (hσ : (twistedChainComplexCoeff L σ).hom (e ik) ≠ 0) :
      Set.range (simplexMap σ) ⊆ Set.range (q ik.1 ik.2) :=
    range_simplexMap_subset_range_of_ne_zero_vertex L (q ik.1 ik.2) hσ
  have he0 (i : S) : e (i, 0) = (ιTwistedChainComplex L 0 i.1).hom (c i.1) := by
    simp only [e, m, rayTransport, Category.comp_id]
    rw [ιTwistedChainComplex_zero_apply_eq_toSSetObj₀Equiv_symm L i.1 (hz0 i).symm]
  refine ⟨locallyFiniteSum hq hy, Subtype.ext (funext fun ρ ↦ ?_)⟩
  -- Along each ray the coefficients on `ρ` of the boundaries telescope to that of its start.
  rw [locallyFiniteBoundary_locallyFiniteSum, coe_locallyFiniteSum, locallyFiniteSumFun_apply]
  simp_rw [hdy, map_sub]
  rw [finsum_sub_add_one_prod (finite_setOf_twistedChainComplexCoeff_ne_zero hq he ρ)]
  simp_rw [he0]
  by_cases hρ : c ρ = 0
  · rw [hρ, finsum_eq_zero_of_forall_eq_zero fun i ↦
      twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L
        (fun h ↦ i.2 (h ▸ hρ)) _]
  · rw [finsum_eq_single _ (⟨ρ, hρ⟩ : S) fun i hi ↦
      twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L
        (fun h ↦ hi (Subtype.ext h)) _]
    exact twistedChainComplexCoeff_ιTwistedChainComplex_apply L ρ (c ρ)

/-- **Degree-zero Borel–Moore homology vanishes on spaces without compact components.** On a
locally compact, σ-compact, locally path-connected Hausdorff space none of whose connected
components is compact, degree-zero Borel–Moore homology with coefficients in any local coefficient
system is zero. -/
theorem isZero_borelMooreHomology_zero (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    IsZero (borelMooreHomology L 0) := by
  have : Epi (ModuleCat.ofHom (locallyFiniteBoundary L 0)) :=
    (ModuleCat.epi_iff_surjective _).2 (locallyFiniteBoundary_zero_surjective L hX)
  have : Epi ((locallyFiniteChainComplex L).d 1 0) := by
    rw [locallyFiniteChainComplex_d]
    infer_instance
  refine IsZero.of_iso ?_ (locallyFiniteChainComplex L).isoHomologyι₀
  exact IsZero.of_epi_eq_zero ((locallyFiniteChainComplex L).pOpcycles 0)
    ((cancel_epi ((locallyFiniteChainComplex L).d 1 0)).1 (by
      rw [HomologicalComplex.d_pOpcycles, comp_zero]))

end TauCeti.LocalCoefficientSystem
