/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# DG local systems

A **DG local system** on a pointed space `(B, b)` is a right differential graded module over the
chain algebra `C_*(Ω_b B; R)` of the Moore loop space (the source's Definition 1.8); they form the
category `DGLocalSystem B b R` of right DG modules over that DG algebra.  For a path-connected
space this is the notion of local coefficients used for Morse and Floer homology with DG
coefficients.

The **pullback** along a based map `f : (B, b) → (B', b')` is restriction of scalars along the
DG algebra morphism `C_*(Ωf)` of `TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra`.  It is
functorial up to the canonical isomorphisms: the pullback along the identity is isomorphic to the
identity functor, and the pullback along a composite to the composite of the pullbacks.

For a space that is not path-connected, one chooses a basepoint `b_c` in each path component `c`
(`PathComponentBasepoints`), and a DG local system is a family `(𝓕_c)` of DG local systems on the
pointed spaces `(B, b_c)` (`DGLocalSystemFamily`).  A map `f : B' → B` that sends each chosen
basepoint of `B'` to the chosen basepoint of the path component of its image pulls such families
back component by component (`DGLocalSystemFamily.pullback`).  Basepoint change, and hence the
pullback along maps that do not preserve the chosen basepoints, needs the derived tensor product
and is not treated here.

## Main definitions

* `TauCeti.DGLocalSystem B b R`: DG local systems on `(B, b)`.
* `TauCeti.DGLocalSystem.pullback R f hf`: the pullback along a based map.
* `TauCeti.DGLocalSystem.pullbackId`, `TauCeti.DGLocalSystem.pullbackComp`: its functoriality.
* `TauCeti.PathComponentBasepoints B`: a choice of basepoint in each path component.
* `TauCeti.DGLocalSystemFamily β R`: DG local systems on a space with chosen basepoints.
* `TauCeti.DGLocalSystemFamily.pullback R f hf`: their pullback along a map preserving the chosen
  basepoints.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definition 1.8.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe uM

section Pointed

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- The category of **DG local systems** on a pointed space `(B, b)`: right differential graded
modules over the chain algebra `C_*(Ω_b B; R)` of the Moore loop space. -/
abbrev DGLocalSystem : Type _ :=
  DGRightModuleCat.{_, _, uM} (loopChain_isDGAlgebra B b R)

end Pointed

namespace DGLocalSystem

variable {B B' B'' : Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  {b : B} {b' : B'} {b'' : B''} (R : Type*) [CommRing R]

/-- The **pullback** of DG local systems along a based map `f : (B, b) → (B', b')`: restriction of
scalars along `C_*(Ωf) : C_*(Ω_b B) → C_*(Ω_{b'} B')`. -/
def pullback (f : C(B, B')) (hf : f b = b') :
    DGLocalSystem.{uM} B' b' R ⥤ DGLocalSystem.{uM} B b R :=
  DGRightModuleCat.restrictScalars (loopChainMap R f hf)

/-- The pullback along the identity is isomorphic to the identity functor. -/
def pullbackId : pullback.{uM} R (.id B) (ContinuousMap.id_apply b) ≅ 𝟭 _ :=
  eqToIso (by rw [pullback, loopChainMap_id]) ≪≫ DGRightModuleCat.restrictScalarsId

/-- The pullback along a composite is isomorphic to the composite of the pullbacks. -/
def pullbackComp (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b') :
    pullback.{uM} R (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) ≅
      pullback R g hg ⋙ pullback R f hf :=
  eqToIso (by rw [pullback, loopChainMap_comp R g f hg hf]) ≪≫
    DGRightModuleCat.restrictScalarsComp _ _

end DGLocalSystem

/-- A choice of a basepoint in each path component of a space. -/
structure PathComponentBasepoints (B : Type*) [TopologicalSpace B] where
  /-- The chosen basepoint of a path component. -/
  point : ZerothHomotopy B → B
  /-- The chosen basepoint of a path component lies in that component. -/
  mk_point : ∀ c, ZerothHomotopy.mk (point c) = c

section Family

variable {B : Type*} [TopologicalSpace B] (β : PathComponentBasepoints B) (R : Type*) [CommRing R]

/-- The category of **DG local systems on a space with chosen basepoints**: families `(𝓕_c)`
indexed by the path components `c`, with `𝓕_c` a DG local system on `(B, b_c)`. -/
abbrev DGLocalSystemFamily : Type _ :=
  ∀ c : ZerothHomotopy B, DGLocalSystem.{uM} B (β.point c) R

/-- The category structure on families: componentwise (the product of the categories of DG
local systems at the chosen basepoints). -/
instance : Category (DGLocalSystemFamily.{uM} β R) :=
  @CategoryTheory.pi (ZerothHomotopy B) (fun c ↦ DGLocalSystem.{uM} B (β.point c) R)
    fun _ ↦ inferInstance

namespace DGLocalSystemFamily

variable {B' : Type*} [TopologicalSpace B'] {β} {β' : PathComponentBasepoints B'}

/-- The **pullback** of DG local systems along a map `f : B' → B` sending each chosen basepoint
`b'_{c'}` of `B'` to the chosen basepoint of the path component of `f (b'_{c'})`: componentwise,
the pullback of the based map `f : (B', b'_{c'}) → (B, b_{f(c')})`. -/
@[expose] def pullback (f : C(B', B))
    (hf : ∀ c', f (β'.point c') = β.point (ZerothHomotopy.mk (f (β'.point c')))) :
    DGLocalSystemFamily.{uM} β R ⥤ DGLocalSystemFamily.{uM} β' R where
  obj 𝓕 c' := (DGLocalSystem.pullback R f (hf c')).obj (𝓕 (ZerothHomotopy.mk (f (β'.point c'))))
  map φ c' := (DGLocalSystem.pullback R f (hf c')).map (φ (ZerothHomotopy.mk (f (β'.point c'))))
  map_id _ := funext fun c' ↦ (DGLocalSystem.pullback R f (hf c')).map_id _
  map_comp _ _ := funext fun c' ↦ (DGLocalSystem.pullback R f (hf c')).map_comp _ _

/-- The component of the pullback of a family at `c'` is the pullback of the component at the
path component of `f (b'_{c'})`. -/
@[simp]
theorem pullback_obj (f : C(B', B))
    (hf : ∀ c', f (β'.point c') = β.point (ZerothHomotopy.mk (f (β'.point c'))))
    (𝓕 : DGLocalSystemFamily.{uM} β R) (c' : ZerothHomotopy B') :
    (pullback R f hf).obj 𝓕 c' =
      (DGLocalSystem.pullback R f (hf c')).obj (𝓕 (ZerothHomotopy.mk (f (β'.point c')))) :=
  rfl

end DGLocalSystemFamily

end Family

end TauCeti

end
