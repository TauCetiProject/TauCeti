/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Hom
public import TauCeti.Topology.PathSpace.Moore

/-!
# The augmented DG algebra of chains on the Moore loop space

For a pointed space `(B, b)`, the Moore loop space `Ω_b B = MooreLoopSpace B b` is a topological
monoid, strictly associative and strictly unital under concatenation.  Its normalized cubical
chains `C_*(Ω_b B; R)`, with the Pontryagin product, `C_n` in cohomological degree `-n` and the
boundary as differential, form an augmented differential graded algebra: the DG algebra over
which the DG local systems on `(B, b)` are right modules.

A based map `f : (B, b) → (B', b')` induces the continuous monoid homomorphism
`MooreLoopSpace.map f`, hence a morphism of augmented DG algebras
`C_*(Ωf) : C_*(Ω_b B; R) → C_*(Ω_{b'} B'; R)`, functorially in `f`.

## Main definitions

* `TauCeti.loopChainAlgebra B b R`: the algebra `C_*(Ω_b B; R)`.
* `TauCeti.loopChainAugmentation B b R`: its augmentation.
* `TauCeti.loopChainMap R f hf`: the DG algebra morphism `C_*(Ωf)` of a based map.

## Main results

* `TauCeti.loopChain_isDGAlgebra`: `C_*(Ω_b B; R)` is a differential graded algebra.
* `TauCeti.loopChainMap_id`, `TauCeti.loopChainMap_comp`: functoriality.
* `TauCeti.loopChainAugmentation_comp_loopChainMap`: compatibility with the augmentations.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

section Algebra

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- The **chain algebra of the Moore loop space**: `C_*(Ω_b B; R)`, the normalized cubical chains
of the Moore loops at `b`, with the Pontryagin product. -/
abbrev loopChainAlgebra : Type _ := normalizedCubicalChainAlgebra (MooreLoopSpace B b) R

/-- **`C_*(Ω_b B; R)` is a differential graded algebra**, with the chains of dimension `n` in
cohomological degree `-n` and the boundary as differential. -/
theorem loopChain_isDGAlgebra :
    IsDGAlgebra (R := R) (A := loopChainAlgebra B b R) (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) :=
  cubicalChain_isDGAlgebra (MooreLoopSpace B b) R

/-- The **augmentation** of `C_*(Ω_b B; R)`, induced by the map to a point. -/
def loopChainAugmentation : DGAlgAugmentation (loopChain_isDGAlgebra B b R) :=
  cubicalChainAugmentation (MooreLoopSpace B b) R

end Algebra

section Map

variable {B B' B'' : Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  {b : B} {b' : B'} {b'' : B''} (R : Type*) [CommRing R]

/-- The **morphism of DG algebras `C_*(Ωf)`** induced by a based map `f : (B, b) → (B', b')`. -/
def loopChainMap (f : C(B, B')) (hf : f b = b') :
    DGAlgHom (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B' b' R) :=
  cubicalChainDGAlgHom R (MooreLoopSpace.map f hf)

/-- The identity map induces the identity. -/
@[simp]
theorem loopChainMap_id :
    loopChainMap R (.id B) (ContinuousMap.id_apply b) =
      DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  rw [loopChainMap, MooreLoopSpace.map_id, cubicalChainDGAlgHom_id]

/-- The morphism induced by a composite is the composite of the induced morphisms. -/
theorem loopChainMap_comp (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b') :
    loopChainMap R (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (loopChainMap R g hg).comp (loopChainMap R f hf) := by
  rw [loopChainMap, MooreLoopSpace.map_comp g f hg hf, cubicalChainDGAlgHom_comp]
  rfl

/-- The morphisms induced by based maps are compatible with the augmentations. -/
theorem loopChainAugmentation_comp_loopChainMap (f : C(B, B')) (hf : f b = b') :
    (loopChainAugmentation B' b' R).comp (loopChainMap R f hf) = loopChainAugmentation B b R :=
  cubicalChainAugmentation_comp_dgAlgHom _

end Map

end TauCeti

end
