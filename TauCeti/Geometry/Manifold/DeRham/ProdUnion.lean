/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.SimplyConnected
import TauCeti.AlgebraicTopology.FundamentalGroup.Product

/-!
# The first de Rham cohomology of a union of two products

Let `M` and `N` be simply connected manifolds, and `D ⊆ M`, `D' ⊆ N` simply connected open
subsets. The open subset

`(D × N) ∪ (M × D')`

of `M × N` has no first de Rham cohomology
(`TauCeti.subsingleton_deRhamCohomology_one_prod_univ_sup_univ_prod`). Both pieces are products of
simply connected spaces, so they have no first cohomology, and they meet in `D × D'`, which is
connected; the Mayer–Vietoris sequence (`TauCeti.subsingleton_deRhamCohomology_one_sup`) does the
rest.

For `M = N = S²` and discs `D = D'` around a point `∞`, this open set is a neighbourhood of the two
transverse spheres `{∞} × S²` and `S² × {∞}`. Its vanishing first cohomology makes a one-form
closed there exact, so that its primitive function can be cut off near the two spheres
(`TauCeti.exists_eventuallyEq_mextDerivₗ_of_subsingleton_deRhamCohomology`), as in the relative
form of Gromov's recognition of the standard symplectic `ℝ⁴`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §2 (the Mayer–Vietoris
  sequence).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  proof of Theorem 9.4.7.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ N] [T2Space N] [SigmaCompactSpace N]

/-- **The first cohomology of a union of two products.** For simply connected manifolds `M` and
`N` and simply connected open subsets `D ⊆ M` and `D' ⊆ N`, the open subset `(D × N) ∪ (M × D')`
of `M × N` has no first de Rham cohomology. -/
theorem subsingleton_deRhamCohomology_one_prod_univ_sup_univ_prod [SimplyConnectedSpace M]
    [SimplyConnectedSpace N] {D : Opens M} {D' : Opens N} (hD : IsSimplyConnected (D : Set M))
    (hD' : IsSimplyConnected (D' : Set N)) :
    Subsingleton (deRhamCohomology (I.prod I')
      (⟨(D : Set M) ×ˢ univ, D.isOpen.prod isOpen_univ⟩ ⊔
        ⟨univ ×ˢ (D' : Set N), isOpen_univ.prod D'.isOpen⟩ : Opens (M × N)) 1) := by
  set U : Opens (M × N) := ⟨(D : Set M) ×ˢ univ, D.isOpen.prod isOpen_univ⟩
  set V : Opens (M × N) := ⟨univ ×ˢ (D' : Set N), isOpen_univ.prod D'.isOpen⟩
  -- Both pieces are products of simply connected sets; as types, `U` and `V` are these products
  -- by definition of the coercion of an open set.
  have : SimplyConnectedSpace U :=
    (hD.prod (simplyConnectedSpace_iff_univ.mp ‹_›)).simplyConnectedSpace
  have : SimplyConnectedSpace V :=
    ((simplyConnectedSpace_iff_univ.mp ‹_›).prod hD').simplyConnectedSpace
  -- They meet in `D × D'`, which is connected.
  have hUV : ((U ⊓ V : Opens (M × N)) : Set (M × N)) = (D : Set M) ×ˢ (D' : Set N) := by
    simp only [U, V, Opens.coe_inf, Opens.coe_mk, prod_inter_prod, inter_univ, univ_inter]
  have : PreconnectedSpace (U ⊓ V : Opens (M × N)) := Subtype.preconnectedSpace <| by
    rw [hUV]
    exact hD.isPathConnected.isConnected.isPreconnected.prod
      hD'.isPathConnected.isConnected.isPreconnected
  exact subsingleton_deRhamCohomology_one_sup
    (subsingleton_deRhamCohomology_one_of_simplyConnectedSpace (I := I.prod I') (M := U))
    (subsingleton_deRhamCohomology_one_of_simplyConnectedSpace (I := I.prod I') (M := V))

end TauCeti
