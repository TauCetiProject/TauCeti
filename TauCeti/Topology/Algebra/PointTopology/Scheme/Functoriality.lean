/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts

/-!
# Functoriality of the topology on scheme-valued points

A morphism of schemes over `Spec k` acts on `R`-points by composition. Over a local
topological ring with open units and continuous inversion on the units, this action is
continuous, and open immersions induce open embeddings. Thus an open subscheme carries
exactly the subspace topology on its points. No finiteness or separation assumptions
on the schemes or coefficient ring are needed.

For an open immersion, the image consists of the points whose underlying scheme
morphism lands in the open subscheme. When `R` is local it suffices to test the image
of the closed point of `Spec R`. On affine schemes the action agrees with
precomposition of algebra homomorphisms under the equivalence `Spec.homEquivAlgHom`,
as expressed by `map_homEquivAlgHom_symm`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1 and its
  proof, pp. 3–4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}

variable [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- A morphism over the base is continuous on points over a local topological ring
with open units and continuous inversion on the units. -/
@[continuity, fun_prop]
theorem continuous_map (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    Continuous (map (R := R) g hg) := by
  refine (continuous_iff fX _).2 fun A i hi _ ↦ ?_
  have hcomp : map (R := R) g hg ∘ chartPoint fX A i hi =
      chartPoint fY A (i ≫ g) (by rw [Category.assoc, hg, hi]) := by
    funext x
    exact map_chartPoint g hg A i hi x
  rw [hcomp]
  exact continuous_chartPoint_of_isLocalRing fY A (i ≫ g) _

/-- An open immersion over the base induces an open embedding on points. -/
theorem isOpenEmbedding_of_isOpenImmersion (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsOpenImmersion g] : IsOpenEmbedding (map (R := R) g hg) := by
  refine .of_continuous_injective_isOpenMap (continuous_map g hg) (map_injective g hg) ?_
  intro s hs
  refine isOpen_iff_forall_mem_open.2 fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint fX x
  let hj : (i ≫ g) ≫ fY = Spec.algebraMap k A := by rw [Category.assoc, hg, hi]
  refine ⟨chartPoint fY A (i ≫ g) hj '' (chartPoint fX A i hi ⁻¹' s), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨chartPoint fX A i hi a, ha, map_chartPoint g hg A i hi a⟩
  · exact (isOpenEmbedding_chartPoint fY A (i ≫ g) hj).isOpenMap _
      (hs.preimage (continuous_chartPoint fX A i hi))
  · exact ⟨z, hx, (map_chartPoint g hg A i hi z).symm⟩

end TauCeti.SchemePointTopology
