/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Family.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Family.Pullback
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.CompositeChange
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Unit

/-!
# Identity and composition laws of the pullback of DG local systems

On a space with a chosen basepoint `b_c` in each path component `c`, a DG local system is a family
`(𝓕_c)` of DG local systems at the chosen basepoints, and along a map `f : B' → B` it pulls back by
changing the basepoint of `𝓕_{f(c')}` from `b_{f(c')}` to `f(b'_{c'})` and then restricting scalars
along `C_*(Ωf)` (`TauCeti.DGLocalSystemFamily.pullbackBasepointChange`). This file proves that this
pullback is functorial up to natural quasi-isomorphisms, and deduces that DG local systems on a
space do not depend on the chosen basepoints.

* **Composition law.** For `f : B' → B` and `g : B'' → B'`, the pullback along `f` followed by
  the pullback along `g` compares to the pullback along `f ∘ g` by a natural transformation
  (`TauCeti.DGLocalSystemFamily.pullbackBasepointChangeComp`) which is a quasi-isomorphism at
  every family and path component
  (`TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackBasepointChangeComp_app`). For a single DG local
  system `M` at `x ∈ B` and points `y ∈ B'`, `z ∈ B''`, it is the composite
  `g^*((f^*(M ⊗ C_*(P_{x→f y} B))) ⊗ C_*(P_{y→g z} B'))`
  `→ g^*f^*((M ⊗ C_*(P_{x→f y} B)) ⊗ C_*(P_{f y→f g z} B))`
  `→ g^*f^*(M ⊗ C_*(P_{x→f g z} B)) ≅ (f ∘ g)^*(M ⊗ C_*(P_{x→f g z} B))`
  (`TauCeti.DGLocalSystem.pullbackBasepointChangeCompHom`) of the commutation of basepoint change
  with pullback (`TauCeti.DGLocalSystem.changeBasepointPullbackHom`), the composite change of
  basepoint (`TauCeti.tensorPathChainConcat`) and the composition isomorphism of restriction of
  scalars (`TauCeti.DGLocalSystem.pullbackComp`). The first two are quasi-isomorphisms when the
  basepoints involved are joined by paths, which holds for chosen basepoints of path components.
* **Identity law.** Changing the chosen basepoints `β` to themselves, the pullback along the
  identity, is naturally isomorphic to the identity functor
  (`TauCeti.DGLocalSystemFamily.pullbackBasepointChangeId`), through the identification
  `𝓕_c ⊗ C_*(P_{b_c→b_c} B) ≅ 𝓕_c` (`TauCeti.tensorPathChainOneIso`).
* **Independence of the chosen basepoints.** Changing the chosen basepoints from `β` to `β'` and
  back to `β` compares to the identity by a natural transformation
  (`TauCeti.DGLocalSystemFamily.changeBasepointsRoundTrip`) which is a quasi-isomorphism at every
  family and path component
  (`TauCeti.DGLocalSystemFamily.isQuasiIso_changeBasepointsRoundTrip_app`). Applied to `β, β'` and
  to `β', β`, the changes of chosen basepoints `TauCeti.DGLocalSystemFamily.changeBasepoints` in
  both directions are mutually inverse up to natural componentwise quasi-isomorphisms.

The families of DG local systems in the identity law have carriers in a universe containing those
of the space and of the ring, as do all pullbacks of families.

## Main definitions

* `TauCeti.DGLocalSystem.pullbackBasepointChangeCompHom`: the composition law for a single DG
  local system.
* `TauCeti.DGLocalSystemFamily.pullbackBasepointChangeComp`: the composition law of the pullback
  of families.
* `TauCeti.DGLocalSystemFamily.pullbackBasepointChangeId`: the identity law of the pullback of
  families.
* `TauCeti.DGLocalSystemFamily.changeBasepointsRoundTrip`: changing the chosen basepoints and
  back compares to the identity.

## Main results

* `TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackBasepointChangeComp_app`: the composition law
  is a quasi-isomorphism.
* `TauCeti.DGLocalSystemFamily.isQuasiIso_changeBasepointsRoundTrip_app`: independence of the
  chosen basepoints up to quasi-isomorphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u w v

namespace DGLocalSystem

open DGRightModuleCat

variable {B B' B'' : Type u} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  {R : Type w} [CommRing R] (f : C(B', B)) (g : C(B'', B')) {x : B} (y : B') (z : B'')

/-- **The composition law of the pullback, for a single DG local system.** For maps
`f : B' → B`, `g : B'' → B'`, points `x ∈ B`, `y ∈ B'`, `z ∈ B''` and a DG local system `M` at
`x`, the morphism of DG local systems at `z`

`g^*((f^*(M ⊗ C_*(P_{x→f y} B))) ⊗ C_*(P_{y→g z} B')) ⟶ (f ∘ g)^*(M ⊗ C_*(P_{x→f g z} B))`,

`(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ f_* τ)`: the commutation of basepoint change with `f^*`, followed by the
composite change of basepoint and the identification `g^* f^* ≅ (f ∘ g)^*`. -/
def pullbackBasepointChangeCompHom (M : DGLocalSystem.{v} B x R) :
    (pullback R g rfl).obj ((basepointChange R y (g z)).obj
      ((pullback R f rfl).obj ((basepointChange R x (f y)).obj M))) ⟶
    (pullback R (f.comp g) rfl).obj ((basepointChange R x (f (g z))).obj M) :=
  (pullback R g rfl).map (changeBasepointPullbackHom f ((basepointChange R x (f y)).obj M)) ≫
    (pullback R g rfl).map ((pullback R f rfl).map (tensorPathChainConcat M (f y) (f (g z)))) ≫
    (pullbackComp R f g rfl rfl).inv.app ((basepointChange R x (f (g z))).obj M)

/-- The composition law for a single DG local system, as a composite. -/
theorem pullbackBasepointChangeCompHom_def (M : DGLocalSystem.{v} B x R) :
    pullbackBasepointChangeCompHom f g y z M =
      (pullback R g rfl).map (changeBasepointPullbackHom f ((basepointChange R x (f y)).obj M)) ≫
        (pullback R g rfl).map ((pullback R f rfl).map (tensorPathChainConcat M (f y) (f (g z)))) ≫
          (pullbackComp R f g rfl rfl).inv.app ((basepointChange R x (f (g z))).obj M) :=
  (rfl)

/-- The composition law for a single DG local system is natural in the DG local system. -/
@[reassoc]
theorem pullbackBasepointChangeCompHom_naturality {M N : DGLocalSystem.{v} B x R} (φ : M ⟶ N) :
    (pullback R g rfl).map ((basepointChange R y (g z)).map
      ((pullback R f rfl).map ((basepointChange R x (f y)).map φ))) ≫
        pullbackBasepointChangeCompHom f g y z N =
      pullbackBasepointChangeCompHom f g y z M ≫
        (pullback R (f.comp g) rfl).map ((basepointChange R x (f (g z))).map φ) := by
  -- Write `G = g^*` and `F = f^*`. The composite is pasted from three commuting squares: the
  -- naturality of the commutation of basepoint change with `F`, read after `G`, of the composite
  -- change, read after `F` and `G`, and of `pullbackComp`.
  exact ((CommSq.mk (changeBasepointPullbackHom_naturality (b := g z) f _
    ((basepointChange R x (f y)).map φ))).map (pullback R g rfl)).vert_comp
      ((((CommSq.mk (tensorPathChainConcat_naturality M φ (f y) (f (g z)))).map
        (pullback R f rfl)).map (pullback R g rfl)).vert_comp
          (CommSq.mk ((pullbackComp R f g rfl rfl).inv.naturality _))) |>.w

/-- **The composition law is a quasi-isomorphism** when `x` is joined to `f y` and `y` to `g z` by
Moore paths. -/
theorem isQuasiIso_pullbackBasepointChangeCompHom (M : DGLocalSystem.{v} B x R)
    (hx : Nonempty (MoorePathBetween B x (f y))) (hy : Nonempty (MoorePathBetween B' y (g z))) :
    IsQuasiIso (pullbackBasepointChangeCompHom f g y z M) :=
  IsQuasiIso.comp ((isQuasiIso_restrictScalars_map_iff _ _).2
    (isQuasiIso_changeBasepointPullbackHom f _ hy)) <| IsQuasiIso.comp
      ((isQuasiIso_restrictScalars_map_iff _ _).2 ((isQuasiIso_restrictScalars_map_iff _ _).2
        (isQuasiIso_tensorPathChainConcat M hx)))
      (isQuasiIso_of_isIso ((pullbackComp R f g rfl rfl).app _).inv)

end DGLocalSystem

namespace DGLocalSystemFamily

open DGRightModuleCat

variable {B B' B'' : Type u} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  (R : Type w) [CommRing R] {β : PathComponentBasepoints B}

/-- The component of `pullbackBasepointChangeComp` at a family and a path component. -/
def pullbackBasepointChangeCompApp (f : C(B', B)) (g : C(B'', B'))
    (β' : PathComponentBasepoints B') (β'' : PathComponentBasepoints B'')
    (𝓕 : DGLocalSystemFamily.{v} β R) (c'' : ZerothHomotopy B'') :
    ((pullbackBasepointChange R f β' ⋙ pullbackBasepointChange R g β'').obj 𝓕) c'' ⟶
      (pullbackBasepointChange R (f.comp g) β'').obj 𝓕 c'' :=
  eqToHom (by rw [Functor.comp_obj, pullbackBasepointChange_obj, pullbackBasepointChange_obj]) ≫
    DGLocalSystem.pullbackBasepointChangeCompHom f g
      (β'.point (ZerothHomotopy.mk (g (β''.point c'')))) (β''.point c'') _ ≫
    eqToHom ((congrArg (fun c ↦ (DGLocalSystem.pullback R (f.comp g) rfl).obj
      ((DGLocalSystem.basepointChange R (β.point c) (f (g (β''.point c'')))).obj (𝓕 c)))
      (β'.mk_apply_point_mk f.continuous (g (β''.point c'')))).trans
        (pullbackBasepointChange_obj R (f.comp g) β'' 𝓕 c'').symm)

/-- The component of `pullbackBasepointChangeComp`, as a composite. -/
theorem pullbackBasepointChangeCompApp_def (f : C(B', B)) (g : C(B'', B'))
    (β' : PathComponentBasepoints B') (β'' : PathComponentBasepoints B'')
    (𝓕 : DGLocalSystemFamily.{v} β R) (c'' : ZerothHomotopy B'') :
    pullbackBasepointChangeCompApp R f g β' β'' 𝓕 c'' =
      eqToHom (by rw [Functor.comp_obj, pullbackBasepointChange_obj,
        pullbackBasepointChange_obj]) ≫
      DGLocalSystem.pullbackBasepointChangeCompHom f g
        (β'.point (ZerothHomotopy.mk (g (β''.point c'')))) (β''.point c'') _ ≫
      eqToHom ((congrArg (fun c ↦ (DGLocalSystem.pullback R (f.comp g) rfl).obj
        ((DGLocalSystem.basepointChange R (β.point c) (f (g (β''.point c'')))).obj (𝓕 c)))
        (β'.mk_apply_point_mk f.continuous (g (β''.point c'')))).trans
          (pullbackBasepointChange_obj R (f.comp g) β'' 𝓕 c'').symm) :=
  (rfl)

/-- **The composition law of the pullback** of families: the pullback along `f` followed by the
pullback along `g` compares to the pullback along `f ∘ g`. At the path component `c''` of `B''`
it is `TauCeti.DGLocalSystem.pullbackBasepointChangeCompHom`, followed by the identification of
the path component of `f(b'_{g(c'')})` with that of `f(g(b''_{c''}))`. It is a quasi-isomorphism
at every family and path component
(`TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackBasepointChangeComp_app`). -/
def pullbackBasepointChangeComp (f : C(B', B)) (g : C(B'', B'))
    (β' : PathComponentBasepoints B') (β'' : PathComponentBasepoints B'') :
    pullbackBasepointChange.{u, u, w, v} (β := β) R f β' ⋙ pullbackBasepointChange R g β'' ⟶
      pullbackBasepointChange R (f.comp g) β'' where
  app 𝓕 c'' := pullbackBasepointChangeCompApp R f g β' β'' 𝓕 c''
  naturality 𝓕 𝓖 φ := funext fun c'' ↦ by
    simp only [Functor.comp_map, pullbackBasepointChangeCompApp, Pi.comp_apply,
      pullbackBasepointChange_map, Functor.map_comp, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [DGLocalSystem.pullbackBasepointChangeCompHom_naturality_assoc]
    -- Split off the `eqToHom` across the path components of `f(b'_{g(b''_{c''})})` and
    -- `f(g(b''_{c''}))`, and move it past `φ`.
    exact whisker_eq _ <| whisker_eq _ <| (whisker_eq _ (eqToHom_trans _ _).symm).trans <|
      eqToHom_naturality_assoc (fun c ↦ (DGLocalSystem.pullback R (f.comp g) rfl).map
        ((DGLocalSystem.basepointChange R (β.point c) (f (g (β''.point c'')))).map (φ c)))
        (β'.mk_apply_point_mk f.continuous (g (β''.point c''))) _

/-- The components of `pullbackBasepointChangeComp` are `pullbackBasepointChangeCompApp`. -/
@[simp]
theorem pullbackBasepointChangeComp_app (f : C(B', B)) (g : C(B'', B'))
    (β' : PathComponentBasepoints B') (β'' : PathComponentBasepoints B'')
    (𝓕 : DGLocalSystemFamily.{v} β R) (c'' : ZerothHomotopy B'') :
    (pullbackBasepointChangeComp R f g β' β'').app 𝓕 c'' =
      pullbackBasepointChangeCompApp R f g β' β'' 𝓕 c'' :=
  (rfl)

/-- **The composition law of the pullback is a quasi-isomorphism** at every family and every path
component. -/
theorem isQuasiIso_pullbackBasepointChangeComp_app (f : C(B', B)) (g : C(B'', B'))
    (β' : PathComponentBasepoints B') (β'' : PathComponentBasepoints B'')
    (𝓕 : DGLocalSystemFamily.{v} β R) (c'' : ZerothHomotopy B'') :
    IsQuasiIso ((pullbackBasepointChangeComp R f g β' β'').app 𝓕 c'') :=
  IsQuasiIso.comp (isQuasiIso_of_isIso _) <| IsQuasiIso.comp
    (DGLocalSystem.isQuasiIso_pullbackBasepointChangeCompHom f g _ _ _
      (nonempty_moorePathBetween_iff.2 (β.joined_point_mk _))
      (nonempty_moorePathBetween_iff.2 (β'.joined_point_mk _)))
    (isQuasiIso_of_isIso _)

/-- The identification `𝓕_{c₁} ⊗ C_*(P_{b_{c₁}→b_c} B) ≅ 𝓕_c` for an index `c₁` equal to `c`
(transport along `h`). -/
def changeBasepointsSelfApp {c₁ c : ZerothHomotopy B} (h : c₁ = c)
    (𝓕 : DGLocalSystemFamily.{max u w v} β R) :
    (DGLocalSystem.basepointChange R (β.point c₁) (β.point c)).obj (𝓕 c₁) ≅ 𝓕 c := by
  subst h
  exact tensorPathChainOneIso.{u, w, v} B (β.point c₁) R (𝓕 c₁)

/-- For the index `c` itself, `changeBasepointsSelfApp` is `TauCeti.tensorPathChainOneIso`. -/
@[simp]
theorem changeBasepointsSelfApp_rfl (c : ZerothHomotopy B)
    (𝓕 : DGLocalSystemFamily.{max u w v} β R) :
    changeBasepointsSelfApp.{u, w, v} R (rfl : c = c) 𝓕 =
      tensorPathChainOneIso.{u, w, v} B (β.point c) R (𝓕 c) :=
  (rfl)

/-- Naturality of `changeBasepointsSelfApp` in the family. -/
@[reassoc]
theorem changeBasepointsSelfApp_naturality {c₁ c : ZerothHomotopy B} (h : c₁ = c)
    {𝓕 𝓖 : DGLocalSystemFamily.{max u w v} β R} (φ : 𝓕 ⟶ 𝓖) :
    (DGLocalSystem.basepointChange R (β.point c₁) (β.point c)).map (φ c₁) ≫
        (changeBasepointsSelfApp.{u, w, v} R h 𝓖).hom =
      (changeBasepointsSelfApp.{u, w, v} R h 𝓕).hom ≫ φ c := by
  subst h
  exact tensorPathChainOneIso_hom_naturality (φ c₁)

/-- The component of `pullbackBasepointChangeId` at a family and a path component. -/
def pullbackBasepointChangeIdApp (𝓕 : DGLocalSystemFamily.{max u w v} β R)
    (c : ZerothHomotopy B) : (changeBasepoints R β β).obj 𝓕 c ≅ 𝓕 c :=
  eqToIso (pullbackBasepointChange_obj R (.id B) β 𝓕 c) ≪≫
    (DGLocalSystem.pullbackId R).app _ ≪≫ changeBasepointsSelfApp.{u, w, v} R (β.mk_point c) 𝓕

/-- The component of `pullbackBasepointChangeId`, as a composite. -/
theorem pullbackBasepointChangeIdApp_hom (𝓕 : DGLocalSystemFamily.{max u w v} β R)
    (c : ZerothHomotopy B) :
    (pullbackBasepointChangeIdApp.{u, w, v} R 𝓕 c).hom =
      eqToHom (pullbackBasepointChange_obj R (.id B) β 𝓕 c) ≫
        (DGLocalSystem.pullbackId R).hom.app _ ≫
          (changeBasepointsSelfApp.{u, w, v} R (β.mk_point c) 𝓕).hom :=
  (rfl)

/-- **Identity law of the pullback**: changing the chosen basepoints `β` of a space to themselves,
the pullback along the identity, is naturally isomorphic to the identity functor. At the path
component `c` it is the identification `𝓕_c ⊗ C_*(P_{b_c→b_c} B) ≅ 𝓕_c`. -/
def pullbackBasepointChangeId :
    changeBasepoints R β β ≅ 𝟭 (DGLocalSystemFamily.{max u w v} β R) :=
  NatIso.ofComponents
    (fun 𝓕 ↦ @Pi.isoMk _ (fun c ↦ DGLocalSystem.{max u w v} B (β.point c) R)
      (fun _ ↦ inferInstance) _ _ fun c ↦ pullbackBasepointChangeIdApp.{u, w, v} R 𝓕 c)
    (fun φ ↦ funext fun c ↦ by
      simp only [Pi.comp_apply, Pi.isoMk_hom, pullbackBasepointChangeIdApp_hom,
        pullbackBasepointChange_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Functor.id_map]
      exact whisker_eq _ ((CommSq.mk ((DGLocalSystem.pullbackId R).hom.naturality _)).vert_comp
        (CommSq.mk (changeBasepointsSelfApp_naturality R (β.mk_point c) φ))).w)

/-- The components of `pullbackBasepointChangeId` are `pullbackBasepointChangeIdApp`. -/
@[simp]
theorem pullbackBasepointChangeId_hom_app (𝓕 : DGLocalSystemFamily.{max u w v} β R)
    (c : ZerothHomotopy B) :
    (pullbackBasepointChangeId.{u, w, v} R).hom.app 𝓕 c =
      (pullbackBasepointChangeIdApp.{u, w, v} R 𝓕 c).hom :=
  (rfl)

/-- **Independence of the chosen basepoints**: changing the chosen basepoints of a space from `β`
to `β'` and back to `β` compares naturally to the identity, through the composition law and the
identity law of the pullback. -/
def changeBasepointsRoundTrip (β β' : PathComponentBasepoints B) :
    changeBasepoints R β β' ⋙ changeBasepoints R β' β ⟶
      𝟭 (DGLocalSystemFamily.{max u w v} β R) :=
  -- The target of the composition law is the pullback along
  -- `(ContinuousMap.id B).comp (ContinuousMap.id B)`, which is definitionally `ContinuousMap.id B`,
  -- so it is the source `changeBasepoints R β β` of the identity law.
  pullbackBasepointChangeComp R (.id B) (.id B) β' β ≫ (pullbackBasepointChangeId.{u, w, v} R).hom

/-- The components of `changeBasepointsRoundTrip`: the composition law followed by the identity
law. -/
@[simp]
theorem changeBasepointsRoundTrip_app (β β' : PathComponentBasepoints B)
    (𝓕 : DGLocalSystemFamily.{max u w v} β R) (c : ZerothHomotopy B) :
    (changeBasepointsRoundTrip.{u, w, v} R β β').app 𝓕 c =
      pullbackBasepointChangeCompApp R (.id B) (.id B) β' β 𝓕 c ≫
        (pullbackBasepointChangeIdApp.{u, w, v} R 𝓕 c).hom :=
  (rfl)

/-- **Independence of the chosen basepoints**: the round trip of the change of chosen basepoints is
a quasi-isomorphism at every family and every path component. -/
theorem isQuasiIso_changeBasepointsRoundTrip_app (β β' : PathComponentBasepoints B)
    (𝓕 : DGLocalSystemFamily.{max u w v} β R) (c : ZerothHomotopy B) :
    IsQuasiIso ((changeBasepointsRoundTrip.{u, w, v} R β β').app 𝓕 c) :=
  IsQuasiIso.comp (isQuasiIso_pullbackBasepointChangeComp_app R _ _ β' β 𝓕 c)
    (isQuasiIso_of_isIso (pullbackBasepointChangeIdApp.{u, w, v} R 𝓕 c).hom)

end DGLocalSystemFamily

end TauCeti
