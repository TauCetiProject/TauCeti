/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor
public import Mathlib.CategoryTheory.Pi.Basic
public import TauCeti.Topology.PathComponent

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
(`TauCeti.PathComponentBasepoints`), and a DG local system is a family `(𝓕_c)` of DG local
systems on the pointed spaces `(B, b_c)` (`DGLocalSystemFamily`).  A map `f : B' → B` that sends
each chosen basepoint of `B'` to the chosen basepoint of the path component of its image pulls
such families back component by component (`DGLocalSystemFamily.pullback`), again functorially up
to the canonical isomorphisms.  Basepoint change, and hence the pullback along maps that do not
preserve the chosen basepoints, needs the derived tensor product and is not treated here.

## Main definitions

* `TauCeti.DGLocalSystem B b R`: DG local systems on `(B, b)`.
* `TauCeti.DGLocalSystem.pullback R f hf`: the pullback along a based map.
* `TauCeti.DGLocalSystem.pullbackId`, `TauCeti.DGLocalSystem.pullbackComp`: its functoriality.
* `TauCeti.DGLocalSystemFamily β R`: DG local systems on a space with chosen basepoints.
* `TauCeti.DGLocalSystemFamily.pullback R f hf`: their pullback along a map preserving the chosen
  basepoints, with `pullbackId` and `pullbackComp`.

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
abbrev pullback (f : C(B, B')) (hf : f b = b') :
    DGLocalSystem.{uM} B' b' R ⥤ DGLocalSystem.{uM} B b R :=
  DGRightModuleCat.restrictScalars (loopChainMap R f hf)

/-- The pullback is restriction of scalars along `C_*(Ωf)`, so the restriction-of-scalars API
applies to it. -/
theorem pullback_eq (f : C(B, B')) (hf : f b = b') :
    pullback.{uM} R f hf = DGRightModuleCat.restrictScalars (loopChainMap R f hf) :=
  (rfl)

/-- The pullback along the identity is isomorphic to the identity functor. -/
def pullbackId : pullback.{uM} R (.id B) (ContinuousMap.id_apply b) ≅ 𝟭 _ :=
  eqToIso (by rw [pullback, loopChainMap_id]) ≪≫ DGRightModuleCat.restrictScalarsId

/-- The component of `pullbackId` at `M`. -/
@[simp]
theorem pullbackId_hom_app (M : DGLocalSystem.{uM} B b R) :
    (pullbackId R).hom.app M =
      eqToHom (by rw [pullback, loopChainMap_id]) ≫
        (DGRightModuleCat.restrictScalarsIdApp M).hom := by
  rw [pullbackId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, ← Iso.app_hom,
    DGRightModuleCat.restrictScalarsId_app]

/-- The component of the inverse of `pullbackId` at `M`. -/
@[simp]
theorem pullbackId_inv_app (M : DGLocalSystem.{uM} B b R) :
    (pullbackId R).inv.app M =
      (DGRightModuleCat.restrictScalarsIdApp M).inv ≫
        eqToHom (by rw [pullback, loopChainMap_id]) := by
  rw [pullbackId, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, ← Iso.app_inv,
    DGRightModuleCat.restrictScalarsId_app]

/-- The pullback along a composite is isomorphic to the composite of the pullbacks. -/
def pullbackComp (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b') :
    pullback.{uM} R (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) ≅
      pullback R g hg ⋙ pullback R f hf :=
  eqToIso (by rw [pullback, loopChainMap_comp R g f hg hf]) ≪≫
    DGRightModuleCat.restrictScalarsComp _ _

/-- The component of `pullbackComp` at `M`. -/
@[simp]
theorem pullbackComp_hom_app (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b')
    (M : DGLocalSystem.{uM} B'' b'' R) :
    (pullbackComp R g f hg hf).hom.app M =
      eqToHom (by rw [pullback, loopChainMap_comp R g f hg hf]) ≫
        (DGRightModuleCat.restrictScalarsCompApp (loopChainMap R f hf) (loopChainMap R g hg)
          M).hom := by
  rw [pullbackComp, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, ← Iso.app_hom,
    DGRightModuleCat.restrictScalarsComp_app]

/-- The component of the inverse of `pullbackComp` at `M`. -/
@[simp]
theorem pullbackComp_inv_app (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b')
    (M : DGLocalSystem.{uM} B'' b'' R) :
    (pullbackComp R g f hg hf).inv.app M =
      (DGRightModuleCat.restrictScalarsCompApp (loopChainMap R f hf) (loopChainMap R g hg)
          M).inv ≫
        eqToHom (by rw [pullback, loopChainMap_comp R g f hg hf]) := by
  rw [pullbackComp, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, ← Iso.app_inv,
    DGRightModuleCat.restrictScalarsComp_app]

end DGLocalSystem

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
    DGLocalSystemFamily.{uM} β R ⥤ DGLocalSystemFamily.{uM} β' R :=
  @Functor.pi' _ (fun c' ↦ DGLocalSystem.{uM} B' (β'.point c') R) (fun _ ↦ inferInstance) _ _
    fun c' ↦
      @Pi.eval _ (fun c ↦ DGLocalSystem.{uM} B (β.point c) R) (fun _ ↦ inferInstance)
          (ZerothHomotopy.mk (f (β'.point c'))) ⋙
        DGLocalSystem.pullback R f (hf c')

/-- The component of the pullback of a family at `c'` is the pullback of the component at the
path component of `f (b'_{c'})`. -/
@[simp]
theorem pullback_obj (f : C(B', B))
    (hf : ∀ c', f (β'.point c') = β.point (ZerothHomotopy.mk (f (β'.point c'))))
    (𝓕 : DGLocalSystemFamily.{uM} β R) (c' : ZerothHomotopy B') :
    (pullback R f hf).obj 𝓕 c' =
      (DGLocalSystem.pullback R f (hf c')).obj (𝓕 (ZerothHomotopy.mk (f (β'.point c')))) :=
  (rfl)

/-- The component of the pullback of a morphism of families at `c'`. -/
@[simp]
theorem pullback_map (f : C(B', B))
    (hf : ∀ c', f (β'.point c') = β.point (ZerothHomotopy.mk (f (β'.point c'))))
    {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖) (c' : ZerothHomotopy B') :
    (pullback R f hf).map φ c' =
      (DGLocalSystem.pullback R f (hf c')).map (φ (ZerothHomotopy.mk (f (β'.point c')))) :=
  (rfl)

/-- The component of `pullbackId`, for an index `c₁` equal to `c` (transport along `h`). -/
def pullbackIdApp {c₁ c : ZerothHomotopy B} (h : c₁ = c)
    (hb : (ContinuousMap.id B) (β.point c) = β.point c₁) (𝓕 : DGLocalSystemFamily.{uM} β R) :
    (DGLocalSystem.pullback R (.id B) hb).obj (𝓕 c₁) ≅ 𝓕 c := by
  subst h
  exact (DGLocalSystem.pullbackId R).app (𝓕 c₁)

/-- Naturality of `pullbackIdApp` in the family. -/
theorem pullbackIdApp_naturality {c₁ c : ZerothHomotopy B} (h : c₁ = c)
    (hb : (ContinuousMap.id B) (β.point c) = β.point c₁) {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R}
    (φ : 𝓕 ⟶ 𝓖) :
    (DGLocalSystem.pullback R (.id B) hb).map (φ c₁) ≫ (pullbackIdApp R h hb 𝓖).hom =
      (pullbackIdApp R h hb 𝓕).hom ≫ φ c := by
  subst h
  exact (DGLocalSystem.pullbackId R).hom.naturality (φ c₁)

/-- The pullback of families along the identity is isomorphic to the identity functor. -/
def pullbackId :
    pullback.{uM} R (.id B) (β := β) (β' := β)
        (fun c ↦ by rw [ContinuousMap.id_apply, β.mk_point]) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun 𝓕 ↦ @Pi.isoMk _ (fun c ↦ DGLocalSystem.{uM} B (β.point c) R) (fun _ ↦ inferInstance) _ _
      fun c ↦ pullbackIdApp R (β.mk_point c) _ 𝓕)
    (fun φ ↦ funext fun c ↦ pullbackIdApp_naturality R (β.mk_point c) _ φ)

variable {B'' : Type*} [TopologicalSpace B''] {β'' : PathComponentBasepoints B''}

/-- The component of `pullbackComp`, for indices `c' = c` (transport along `h`). -/
def pullbackCompApp (g : C(B, B'')) (f : C(B', B)) {y : B'} {x : B} {c' c : ZerothHomotopy B''}
    (h : c' = c) (hf : f y = x) (hg : g x = β''.point c) (hgf : (g.comp f) y = β''.point c')
    (𝓕 : DGLocalSystemFamily.{uM} β'' R) :
    (DGLocalSystem.pullback R (g.comp f) hgf).obj (𝓕 c') ≅
      (DGLocalSystem.pullback R f hf).obj ((DGLocalSystem.pullback R g hg).obj (𝓕 c)) := by
  subst h
  exact (DGLocalSystem.pullbackComp R g f hg hf).app (𝓕 c')

/-- Naturality of `pullbackCompApp` in the family. -/
theorem pullbackCompApp_naturality (g : C(B, B'')) (f : C(B', B)) {y : B'} {x : B}
    {c' c : ZerothHomotopy B''} (h : c' = c) (hf : f y = x) (hg : g x = β''.point c)
    (hgf : (g.comp f) y = β''.point c') {𝓕 𝓖 : DGLocalSystemFamily.{uM} β'' R} (φ : 𝓕 ⟶ 𝓖) :
    (DGLocalSystem.pullback R (g.comp f) hgf).map (φ c') ≫
        (pullbackCompApp R g f h hf hg hgf 𝓖).hom =
      (pullbackCompApp R g f h hf hg hgf 𝓕).hom ≫
        (DGLocalSystem.pullback R f hf).map ((DGLocalSystem.pullback R g hg).map (φ c)) := by
  subst h
  exact (DGLocalSystem.pullbackComp R g f hg hf).hom.naturality (φ c')

/-- The pullback of families along a composite is isomorphic to the composite of the
pullbacks. -/
def pullbackComp (g : C(B, B'')) (f : C(B', B))
    (hg : ∀ c, g (β.point c) = β''.point (ZerothHomotopy.mk (g (β.point c))))
    (hf : ∀ c', f (β'.point c') = β.point (ZerothHomotopy.mk (f (β'.point c')))) :
    pullback.{uM} R (g.comp f) (β := β'') (β' := β')
        (fun c' ↦ (congrArg g (hf c')).trans ((hg _).trans
          (congrArg (fun x ↦ β''.point (ZerothHomotopy.mk (g x))) (hf c').symm))) ≅
      pullback R g hg ⋙ pullback R f hf :=
  NatIso.ofComponents
    (fun 𝓕 ↦
      @Pi.isoMk _ (fun c' ↦ DGLocalSystem.{uM} B' (β'.point c') R) (fun _ ↦ inferInstance) _ _
        fun c' ↦ pullbackCompApp R g f (congrArg (fun x ↦ ZerothHomotopy.mk (g x)) (hf c')) (hf c')
        (hg _) _ 𝓕)
    (fun φ ↦ funext fun c' ↦
      pullbackCompApp_naturality R g f (congrArg (fun x ↦ ZerothHomotopy.mk (g x)) (hf c'))
        (hf c') (hg _) _ φ)

end DGLocalSystemFamily

end Family

end TauCeti

end
