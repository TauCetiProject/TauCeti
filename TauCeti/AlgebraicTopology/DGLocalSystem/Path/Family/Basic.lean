/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between

/-!
# Basepoint change and the pullback of DG local systems along arbitrary maps

For points `a` and `b` of a space `B`, a DG local system `𝓕` at `a` changes basepoint to `b` by
tensoring with the chain bimodule of Moore paths from `a` to `b`,
`𝓕 ↦ 𝓕 ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B)` (`TauCeti.DGLocalSystem.basepointChange`, in
`TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange`). When `a` and `b` are joined by a
path, this ordinary tensor product preserves and reflects quasi-isomorphisms
(`TauCeti.DGLocalSystem.isQuasiIso_basepointChange_map_iff`).

On a space with a chosen basepoint `b_c` in each path component `c`, a DG local system is a family
`(𝓕_c)` of DG local systems at the chosen basepoints (`TauCeti.DGLocalSystemFamily`). Along a map
`f : B' → B`, the path component `c'` of `B'` with chosen basepoint `b'_{c'}` lies over the path
component `f(c')` of `B`, which contains both `f(b'_{c'})` and its own chosen basepoint
`b_{f(c')}`. The **pullback** of `(𝓕_c)` along `f`
(`TauCeti.DGLocalSystemFamily.pullbackBasepointChange`) changes the basepoint of `𝓕_{f(c')}`
from `b_{f(c')}` to `f(b'_{c'})`, and then restricts scalars along
`C_*(Ωf) : C_*(Ω_{b'_{c'}} B') → C_*(Ω_{f(b'_{c'})} B)`. Unlike the strict pullback
`TauCeti.DGLocalSystemFamily.pullback`, it needs no compatibility of `f` with the chosen
basepoints. It preserves componentwise quasi-isomorphisms, and reflects them at the path
components of `B` met by `f`; so when `f` is surjective on path components it reflects them
everywhere. For `f` the identity, it changes the chosen basepoints of a space
(`TauCeti.DGLocalSystemFamily.changeBasepoints`), which therefore preserves and reflects
componentwise quasi-isomorphisms.

## Main definitions

* `TauCeti.DGLocalSystemFamily.pullbackBasepointChange R f β'`: the pullback of DG local systems
  on spaces with chosen basepoints along an arbitrary map.
* `TauCeti.DGLocalSystemFamily.changeBasepoints R β β'`: the change between two choices of
  basepoints.

## Main results

* `TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackBasepointChange_map_app_iff`: a component of the
  pullback of a morphism is a quasi-isomorphism exactly when the corresponding component of the
  morphism is one.
* `TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackBasepointChange_map_iff`: the pullback of a
  morphism of families is a componentwise quasi-isomorphism exactly when the morphism is one at
  every path component met by `f`.
* `TauCeti.DGLocalSystemFamily.isQuasiIso_changeBasepoints_map_iff`: changing the chosen
  basepoints preserves and reflects componentwise quasi-isomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/
public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u u' w v

namespace DGLocalSystemFamily

variable {B : Type u} [TopologicalSpace B] {B' : Type u'} [TopologicalSpace B'] (R : Type w)
  [CommRing R] {β : PathComponentBasepoints B}

/-- The **pullback** of DG local systems on spaces with chosen basepoints along an arbitrary map
`f : B' → B`. At the path component `c'` of `B'`, it changes the basepoint of `𝓕_{f(c')}` from
the chosen basepoint `b_{f(c')}` to `f(b'_{c'})`, and then restricts scalars along `C_*(Ωf)` at
`b'_{c'}`. -/
def pullbackBasepointChange (f : C(B', B)) (β' : PathComponentBasepoints B') :
    DGLocalSystemFamily.{v} β R ⥤ DGLocalSystemFamily.{max v u w} β' R :=
  @Functor.pi' _ (fun c' ↦ DGLocalSystem.{max v u w} B' (β'.point c') R)
    (fun _ ↦ inferInstance) _ _ fun c' ↦
      @Pi.eval _ (fun c ↦ DGLocalSystem.{v} B (β.point c) R) (fun _ ↦ inferInstance)
          (ZerothHomotopy.mk (f (β'.point c'))) ⋙
        DGLocalSystem.basepointChange R (β.point (ZerothHomotopy.mk (f (β'.point c'))))
          (f (β'.point c')) ⋙
        DGLocalSystem.pullback R f rfl

/-- The component of the pullback of a family at `c'`: the component at the path component of
`f (b'_{c'})`, moved to the basepoint `f (b'_{c'})` and restricted along `f`. -/
@[simp]
theorem pullbackBasepointChange_obj (f : C(B', B)) (β' : PathComponentBasepoints B')
    (𝓕 : DGLocalSystemFamily.{v} β R) (c' : ZerothHomotopy B') :
    (pullbackBasepointChange R f β').obj 𝓕 c' =
      (DGLocalSystem.pullback R f rfl).obj ((DGLocalSystem.basepointChange R
        (β.point (ZerothHomotopy.mk (f (β'.point c')))) (f (β'.point c'))).obj
          (𝓕 (ZerothHomotopy.mk (f (β'.point c'))))) :=
  (rfl)

/-- The component of the pullback of a morphism of families at `c'`. -/
@[simp]
theorem pullbackBasepointChange_map (f : C(B', B)) (β' : PathComponentBasepoints B')
    {𝓕 𝓖 : DGLocalSystemFamily.{v} β R} (φ : 𝓕 ⟶ 𝓖) (c' : ZerothHomotopy B') :
    (pullbackBasepointChange R f β').map φ c' =
      eqToHom (pullbackBasepointChange_obj R f β' 𝓕 c') ≫
        (DGLocalSystem.pullback R f rfl).map ((DGLocalSystem.basepointChange R
          (β.point (ZerothHomotopy.mk (f (β'.point c')))) (f (β'.point c'))).map
            (φ (ZerothHomotopy.mk (f (β'.point c'))))) ≫
          eqToHom (pullbackBasepointChange_obj R f β' 𝓖 c').symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

variable {R}

/-- **The pullback preserves and reflects quasi-isomorphisms**: its component at `c'` is a
quasi-isomorphism exactly when the component of the morphism at the path component of
`f (b'_{c'})` is one. -/
theorem isQuasiIso_pullbackBasepointChange_map_app_iff (f : C(B', B))
    (β' : PathComponentBasepoints B') {𝓕 𝓖 : DGLocalSystemFamily.{v} β R} (φ : 𝓕 ⟶ 𝓖)
    (c' : ZerothHomotopy B') :
    DGRightModuleCat.IsQuasiIso ((pullbackBasepointChange R f β').map φ c') ↔
      DGRightModuleCat.IsQuasiIso (φ (ZerothHomotopy.mk (f (β'.point c')))) :=
  (DGRightModuleCat.isQuasiIso_restrictScalars_map_iff _ _).trans
    (DGLocalSystem.isQuasiIso_basepointChange_map_iff
      -- The chosen basepoint lies in the path component of `f (b'_{c'})`.
      (nonempty_moorePathBetween_iff.2 (β.joined_point_mk (f (β'.point c')))) _)

/-- **The pullback of a morphism of families is a componentwise quasi-isomorphism** exactly when
the morphism is a quasi-isomorphism at every path component of `B` met by `f`. -/
theorem isQuasiIso_pullbackBasepointChange_map_iff (f : C(B', B))
    (β' : PathComponentBasepoints B') {𝓕 𝓖 : DGLocalSystemFamily.{v} β R} (φ : 𝓕 ⟶ 𝓖) :
    (∀ c', DGRightModuleCat.IsQuasiIso ((pullbackBasepointChange R f β').map φ c')) ↔
      ∀ x', DGRightModuleCat.IsQuasiIso (φ (ZerothHomotopy.mk (f x'))) := by
  simp_rw [isQuasiIso_pullbackBasepointChange_map_app_iff]
  refine ⟨fun h x ↦ ?_, fun h c' ↦ h _⟩
  exact β'.mk_apply_point_mk f.continuous x ▸ h (ZerothHomotopy.mk x)

variable (R) in
/-- The **change of chosen basepoints** from `β` to `β'` on the same space: the pullback along the
identity, which at the path component `c` changes the basepoint from `b_c` to `b'_c`. -/
abbrev changeBasepoints (β β' : PathComponentBasepoints B) :
    DGLocalSystemFamily.{v} β R ⥤ DGLocalSystemFamily.{max v u w} β' R :=
  pullbackBasepointChange (β := β) R (.id B) β'

/-- **Changing the chosen basepoints preserves and reflects quasi-isomorphisms of families.** -/
theorem isQuasiIso_changeBasepoints_map_iff (β β' : PathComponentBasepoints B)
    {𝓕 𝓖 : DGLocalSystemFamily.{v} β R} (φ : 𝓕 ⟶ 𝓖) :
    (∀ c, DGRightModuleCat.IsQuasiIso ((changeBasepoints R β β').map φ c)) ↔
      ∀ c, DGRightModuleCat.IsQuasiIso (φ c) := by
  rw [isQuasiIso_pullbackBasepointChange_map_iff]
  exact ⟨fun h c ↦ β.mk_point c ▸ h (β.point c), fun h x ↦ h _⟩

end DGLocalSystemFamily

end TauCeti
