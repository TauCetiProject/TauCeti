/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic

/-!
# Classical local systems embed fully faithfully into DG local systems

On a path-connected pointed space `(X, x)`, the functor `classicalDGLocalSystemFunctor R x`
from classical local systems to DG local systems over `C_*(Ω_x X; R)` is fully faithful.

Faithfulness is `classicalDGLocalSystemMap_injective`.  For fullness, a morphism
`f : L_x → L'_x` of DG local systems commutes with the action of the point chain of every Moore
loop; that chain acts by the monodromy of the class of the loop (`classicalAction_lof_ofCube`),
and every class of `π₁(X, x)` is the class of a Moore loop, so `f` commutes with the monodromy.
An equivariant map between the fibers at the basepoint extends to a morphism of local systems by
transport along paths from the basepoint (`TauCeti.Groupoid.natTransOfEnd`), and the extension
induces `f`.

## Main definitions

* `TauCeti.classicalDGLocalSystemPreimage`: the morphism of local systems inducing a given
  morphism of DG local systems.
* `TauCeti.classicalDGLocalSystemFunctorFullyFaithful`: the functor from classical to DG local
  systems is fully faithful.

## Main results

* `TauCeti.classicalDGLocalSystem_hom_naturality`: a morphism of DG local systems commutes with
  the monodromy.
* `TauCeti.classicalDGLocalSystemMap_preimage`: the preimage induces the given morphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer,
  1978, Chapter VI, §1 (local systems on a path-connected space and `π₁`-modules).
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}

/-- **A morphism of DG local systems commutes with the monodromy**: the monodromy of a class
`g ∈ π₁(X, x)` is the action of the point chain of a Moore loop of class `g⁻¹`. -/
theorem classicalDGLocalSystem_hom_naturality {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L') (g : FundamentalGroup X x)
    (m : L.obj (FundamentalGroupoid.mk x)) :
    f (L.map g m) = L'.map g (f m) := by
  obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective x g⁻¹
  let a := cubicalChainLof (MooreLoopSpace X x) R 0
    (NormalizedCubicalChain.ofCube (MooreLoopSpace X x) R (SingularCube.point γ))
  have hL := classicalAction_lof_ofCube L (SingularCube.point γ)
  have hL' := classicalAction_lof_ofCube L' (SingularCube.point γ)
  rw [SingularCube.point_apply, hγ, inv_inv] at hL hL'
  exact (congrArg f (LinearMap.congr_fun hL m).symm).trans
    ((map_smul f (op a) m).trans (LinearMap.congr_fun hL' (f m)))

/-- The underlying linear map of a morphism of DG local systems, between the fibers. -/
-- The carrier of `classicalDGLocalSystem x L` is the fiber `L_x` by definition, so the forgetful
-- image of `f` is retyped as a morphism between the fibers; `fiberHom_apply` records this.
private def fiberHom {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L') :
    L.obj (FundamentalGroupoid.mk x) ⟶ L'.obj (FundamentalGroupoid.mk x) :=
  ModuleCat.ofHom (DGRightModuleCat.forgetToModuleCat.map f).hom

private theorem fiberHom_apply {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L')
    (m : L.obj (FundamentalGroupoid.mk x)) : fiberHom f m = f m :=
  rfl

variable [PathConnectedSpace X]

/-- **The preimage of a morphism of DG local systems**: on a path-connected space, a morphism
`f : L_x → L'_x` of DG local systems commutes with the monodromy, so it extends to a morphism of
local systems `L ⟶ L'` by transport along paths from the basepoint. -/
def classicalDGLocalSystemPreimage {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L') : L ⟶ L' :=
  Groupoid.natTransOfEnd (FundamentalGroupoid.nonempty_hom _) (fiberHom f) fun g ↦ by
    ext m
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, fiberHom_apply, fiberHom_apply]
    exact classicalDGLocalSystem_hom_naturality f g m

/-- The component of the preimage at the basepoint is the given morphism. -/
@[simp]
theorem classicalDGLocalSystemPreimage_app_mk_apply {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L')
    (m : L.obj (FundamentalGroupoid.mk x)) :
    (classicalDGLocalSystemPreimage f).app (FundamentalGroupoid.mk x) m = f m := by
  rw [classicalDGLocalSystemPreimage, Groupoid.natTransOfEnd_app_self, fiberHom_apply]

/-- **The preimage induces the given morphism of DG local systems.** -/
@[simp]
theorem classicalDGLocalSystemMap_preimage {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L') :
    classicalDGLocalSystemMap (classicalDGLocalSystemPreimage f) = f :=
  DGRightModuleCat.hom_ext (M := classicalDGLocalSystem x L) (N := classicalDGLocalSystem x L')
    fun m ↦ (classicalDGLocalSystemMap_apply _ m).trans
      (classicalDGLocalSystemPreimage_app_mk_apply f m)

/-- **The preimage of an induced morphism is the morphism itself.** -/
@[simp]
theorem classicalDGLocalSystemPreimage_map {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (φ : L ⟶ L') : classicalDGLocalSystemPreimage (classicalDGLocalSystemMap (x := x) φ) = φ :=
  classicalDGLocalSystemMap_injective (classicalDGLocalSystemMap_preimage _)

/-- The preimage of the identity is the identity. -/
@[simp]
theorem classicalDGLocalSystemPreimage_id (L : LocalCoefficientSystem.{u, u, w} R X) :
    classicalDGLocalSystemPreimage (𝟙 (classicalDGLocalSystem x L)) = 𝟙 L :=
  classicalDGLocalSystemMap_injective ((classicalDGLocalSystemMap_preimage _).trans
    ((classicalDGLocalSystemFunctor R x).map_id L).symm)

/-- The preimage of a composite is the composite of the preimages. -/
@[simp]
theorem classicalDGLocalSystemPreimage_comp {L L' L'' : LocalCoefficientSystem.{u, u, w} R X}
    (f : classicalDGLocalSystem x L ⟶ classicalDGLocalSystem x L')
    (g : classicalDGLocalSystem x L' ⟶ classicalDGLocalSystem x L'') :
    classicalDGLocalSystemPreimage (f ≫ g) =
      classicalDGLocalSystemPreimage f ≫ classicalDGLocalSystemPreimage g :=
  classicalDGLocalSystemMap_injective ((classicalDGLocalSystemMap_preimage _).trans
    (((classicalDGLocalSystemFunctor R x).map_comp _ _).trans (by
      rw [classicalDGLocalSystemFunctor_map, classicalDGLocalSystemFunctor_map,
        classicalDGLocalSystemMap_preimage, classicalDGLocalSystemMap_preimage]
      -- The composite is taken between `(classicalDGLocalSystemFunctor R x).obj _` and
      -- `classicalDGLocalSystem x _`, which agree by `classicalDGLocalSystemFunctor_obj`.
      rfl)).symm)

variable (R x) in
/-- On a path-connected space, the functor from classical to DG local systems is full. -/
instance : (classicalDGLocalSystemFunctor R x).Full where
  map_surjective f := ⟨classicalDGLocalSystemPreimage f, classicalDGLocalSystemMap_preimage f⟩

variable (R x) in
/-- **Classical local systems are DG local systems**: on a path-connected space, the functor
from classical local systems to DG local systems over `C_*(Ω_x X; R)` is fully faithful. -/
def classicalDGLocalSystemFunctorFullyFaithful :
    (classicalDGLocalSystemFunctor.{u, w} R x).FullyFaithful :=
  .ofFullyFaithful _

end TauCeti
