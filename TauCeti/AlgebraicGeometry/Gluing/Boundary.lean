/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Gluing.Separated
import TauCeti.Topology.Frontier

/-!
# Separated gluing away from the boundary

Suppose a map from an open subscheme `V ⊆ Y` to `X` is universally closed and restricts to
an open immersion on `U ⊆ V`, all over a common base `S`. For an open `W ⊆ Y` containing `U`,
we can glue `X` to `W` along `U`. When `X` and `Y` are separated over `S`, the gluing is
separated exactly when `V ∩ W` misses the frontier of `U` in `Y`.

In particular one can take `W` to be the complement of the closure of `V ∖ U`. In the two-open
construction of a compactification this removes the unwanted boundary of a proper extension
while retaining the whole open along which the pieces are glued.

## References

* The Stacks Project, [Lemma 38.33.7](https://stacks.math.columbia.edu/tag/0F40).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} {U V W : Y.Opens}

/-- The gluing of `X` and `W` along `U` is separated exactly when no point of the frontier
of `U` lies in both `V` and `W`, provided the overlap map to `X` extends to a universally
closed map on `V`. -/
theorem IsSeparated.pushout_desc_iff_disjoint_frontier (hUV : U ≤ V) (hUW : U ≤ W)
    (p : V.toScheme ⟶ X) [UniversallyClosed p] [IsOpenImmersion (Y.homOfLE hUV ≫ p)]
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f] [IsSeparated g] (hp : p ≫ f = V.ι ≫ g) :
    IsSeparated (pushout.desc (f := Y.homOfLE hUV ≫ p) (g := Y.homOfLE hUW)
      f (W.ι ≫ g) (by simp [hp])) ↔
      Disjoint ((V ⊓ W : Y.Opens) : Set Y) (frontier (U : Set Y)) := by
  let i := Y.homOfLE (le_inf hUV hUW)
  let graph := pullback.lift (f := f) (g := W.ι ≫ g)
    (Y.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ p) (Y.homOfLE inf_le_right) (by simp [hp])
  have : IsClosedImmersion graph := V.isClosedImmersion_pullbackLift_inf W p f g hp
  have hfac : pullback.lift (f := f) (g := W.ι ≫ g) (Y.homOfLE hUV ≫ p)
      (Y.homOfLE hUW) (by simp [hp]) = i ≫ graph := by
    apply pullback.hom_ext <;> simp [i, graph]
  rw [IsSeparated.pushout_desc_iff, hfac, IsClosedImmersion.comp_iff]
  rw [IsClosedImmersion.iff_isPreimmersion, and_iff_right (inferInstance : IsPreimmersion i)]
  simpa only [i, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
    TopologicalSpace.Opens.map_coe, Scheme.Opens.opensRange_ι] using
    (V ⊓ W).ι.isOpenEmbedding.isOpenMap.isClosed_preimage_iff_disjoint_frontier
      (V ⊓ W).ι.continuous U.isOpen

/-- Gluing to the complement of the closure of `V ∖ U` gives a separated scheme over the
base. This complement is the open `V ⇨ U`, the largest open meeting `V` only in `U`. -/
theorem IsSeparated.pushout_desc_himp (hUV : U ≤ V) (p : V.toScheme ⟶ X)
    [UniversallyClosed p] [IsOpenImmersion (Y.homOfLE hUV ≫ p)]
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f] [IsSeparated g] (hp : p ≫ f = V.ι ≫ g) :
    IsSeparated (pushout.desc (f := Y.homOfLE hUV ≫ p) (g := Y.homOfLE (le_himp : U ≤ V ⇨ U))
      f ((V ⇨ U).ι ≫ g) (by simp [hp])) := by
  apply (IsSeparated.pushout_desc_iff_disjoint_frontier hUV le_himp p f g hp).2
  rw [inf_himp_self, inf_eq_right.mpr hUV]
  exact (disjoint_frontier_iff_isOpen.mpr U.isOpen).symm

end AlgebraicGeometry
