/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological
public import TauCeti.Geometry.Manifold.Opens
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# Pulling back homological orientations along open embeddings

An open embedding `j : M → N` into a Hausdorff space identifies the integral local homology
`H_d(M, M ∖ {x}; ℤ)` with `H_d(N, N ∖ {j x}; ℤ)` by excision
(`TauCeti.localHomologyIsoOfIsOpenEmbedding`), and so identifies the local orientations at `x`
with those at `j x` (`Topology.IsOpenEmbedding.localOrientationEquiv`). These identifications
intertwine the transport of local orientations along paths
(`TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom`). So an orientation
`o` of `N` pulls back to an orientation `o.comap hj` of `M`, whose local orientation at `x`
corresponds to the local orientation of `o` at `j x` (`TauCeti.HomologicalOrientation.comap`).

For the inclusion of an open subset this is the restriction of an orientation to the subset; in
particular open subsets of orientable manifolds are orientable. For a homeomorphism `e : M ≃ₜ N`
it compares orientations of `M` and of `N`: `e` is orientation-preserving for orientations `o` of
`M` and `o'` of `N` when `o'.comap e.isOpenEmbedding = o`. In the dimension of a connected
manifold `M` the pulled-back orientation is `o` or `-o`
(`TauCeti.HomologicalOrientation.eq_or_eq_neg`), so such a homeomorphism either preserves or
reverses orientation.

## Main definitions

* `Topology.IsOpenEmbedding.localOrientationEquiv`: the local orientations of `M` at `x` and of `N`
  at `j x` correspond.
* `TauCeti.HomologicalOrientation.comap`: the pullback of an orientation along an open embedding.

## Main results

* `Topology.IsOpenEmbedding.localOrientationEquiv_id`,
  `Topology.IsOpenEmbedding.localOrientationEquiv_trans`: the correspondence of local
  orientations is functorial.
* `Topology.IsOpenEmbedding.localHomologyMap_localOrientationEquiv_symm`: the map of local
  homology induced by `j` carries the local orientation corresponding to `z` back to `z`.
* `IsOpen.localHomologyMap_inclusion_localOrientationEquiv_symm`: the inclusion of open sets
  `V ⊆ U` carries the local orientations of `V` to the corresponding ones of `U`.
* `TauCeti.HomologicalOrientation.localOrientationEquiv_comap_apply`: the local
  orientation of the pullback at `x` corresponds to the local orientation at `j x`.
* `TauCeti.HomologicalOrientation.comap_neg`, `TauCeti.HomologicalOrientation.comap_id`,
  `TauCeti.HomologicalOrientation.comap_comap`: pullback commutes with reversal and is functorial.
* `TauCeti.HomologicalOrientation.comap_symm_comap`: pulling back along a homeomorphism and then
  along its inverse is the identity.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3: local orientations, computed by excision in a neighbourhood, and orientations as
  locally consistent choices of local orientations.
-/

public section

noncomputable section

open CategoryTheory Topology

universe w

namespace Topology.IsOpenEmbedding

open TauCeti

variable {M N : Type w} [TopologicalSpace M] [TopologicalSpace N] [T1Space N] {j : M → N}

/-- An open embedding `j : M → N` into a `T₁` space identifies the local orientations of `M` at `x`
in degree `d` with those of `N` at `j x`, through the isomorphism of integral local homology
induced by `j`. -/
def localOrientationEquiv (hj : IsOpenEmbedding j) (x : M) (d : ℕ) :
    LocalOrientation M x d ≃ LocalOrientation N (j x) d :=
  (ModuleLocalOrientation.equivLocalOrientation M x d).symm.trans
    ((hj.moduleLocalOrientationEquiv (ModuleCat.of ℤ (ULift.{w} ℤ)) x d).trans
      (ModuleLocalOrientation.equivLocalOrientation N (j x) d))

/-- On local homology classes, the correspondence of local orientations is the map induced by
`j`. -/
@[simp]
lemma coe_localOrientationEquiv (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    (hj.localOrientationEquiv x d z).val =
      (localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d).hom z.val := by
  simp [localOrientationEquiv]

/-- The inverse correspondence acts on local homology classes by the inverse isomorphism. -/
@[simp]
lemma coe_localOrientationEquiv_symm (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation N (j x) d) :
    ((hj.localOrientationEquiv x d).symm z).val =
      (localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d).inv z.val := by
  simp [localOrientationEquiv]

/-- The map of local homology induced by `j` carries the local orientation at `x` corresponding
to a local orientation `z` at `j x` back to `z`. -/
lemma localHomologyMap_localOrientationEquiv_symm (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation N (j x) d) (h : j ⁻¹' {j x} ⊆ {x}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) ⟨j, hj.continuous⟩ h d
      ((hj.localOrientationEquiv x d).symm z).val = z.val := by
  rw [coe_localOrientationEquiv_symm,
    ← ModuleLocalOrientation.coe_equivLocalOrientation_symm (j x) d z,
    ← hj.coe_moduleLocalOrientationEquiv_symm]
  exact hj.localHomologyMap_moduleLocalOrientationEquiv_symm (ModuleCat.of ℤ (ULift.{w} ℤ)) x
    ((ModuleLocalOrientation.equivLocalOrientation N (j x) d).symm z) h

/-- The correspondence of local orientations commutes with reversal. -/
@[simp]
lemma localOrientationEquiv_neg (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    hj.localOrientationEquiv x d (-z) =
      -hj.localOrientationEquiv x d z := by
  simp [localOrientationEquiv]

/-- The identity identifies the local orientations at `x` with themselves. -/
@[simp]
lemma localOrientationEquiv_id [T1Space M] (x : M) (d : ℕ) :
    IsOpenEmbedding.id.localOrientationEquiv x d = Equiv.refl _ :=
  Equiv.ext fun _ ↦ by simp [localOrientationEquiv]

/-- The correspondences of local orientations along open embeddings are functorial. -/
@[simp]
lemma localOrientationEquiv_trans {P : Type w} [TopologicalSpace P] [T1Space P] {j' : N → P}
    (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (x : M) (d : ℕ) :
    (hj.localOrientationEquiv x d).trans (hj'.localOrientationEquiv (j x) d) =
      (hj'.comp hj).localOrientationEquiv x d :=
  Equiv.ext fun z ↦ by
    simp only [localOrientationEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact congrArg _ <| by
      rw [← Equiv.trans_apply, IsOpenEmbedding.moduleLocalOrientationEquiv_trans]

/-- The inclusion of open sets `V ⊆ U` carries the local orientation of `V` at `x` corresponding to
a local orientation `z` of the ambient space at `x` to the local orientation of `U` at `x`
corresponding to `z`. -/
lemma _root_.IsOpen.localHomologyMap_inclusion_localOrientationEquiv_symm {U V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) {x : N} (hx : x ∈ V) {d : ℕ}
    (z : LocalOrientation N x d)
    (h : ContinuousMap.inclusion hVU ⁻¹' {(⟨x, hVU hx⟩ : U)} ⊆ {(⟨x, hx⟩ : V)}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (ContinuousMap.inclusion hVU) h d
        ((hV.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ d).symm z).val =
      ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hVU hx⟩ d).symm z).val := by
  -- Both sides map to `z` under the excision isomorphism of `U`, which is injective.
  refine (ConcreteCategory.bijective_of_isIso (localHomologyIsoOfIsOpenEmbedding
    (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) hU.isOpenEmbedding_subtypeVal
    ⟨x, hVU hx⟩ d).hom).1 ?_
  rw [localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  exact (hV.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨x, hx⟩ z
    _).trans
    (hU.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨x, hVU hx⟩ z
      _).symm

end Topology.IsOpenEmbedding

namespace TauCeti

namespace HomologicalOrientation

variable {M N P E : Type w} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [TopologicalSpace P] [T2Space P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [ChartedSpace E N] [ChartedSpace E P] {d : ℕ} {j : M → N}

/-- The **pullback of an orientation along an open embedding** `j : M → N`: the local orientation
at `x` is the one corresponding to the local orientation of `o` at `j x` under the excision
isomorphism induced by `j`. -/
def comap (o : HomologicalOrientation N E d) (hj : IsOpenEmbedding j) :
    HomologicalOrientation M E d :=
  ModuleOrientation.equivHomologicalOrientation
    ((ModuleOrientation.equivHomologicalOrientation.symm o).comap hj)

lemma _root_.TauCeti.ModuleOrientation.equivHomologicalOrientation_comap
    (o : ModuleOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) N E d) (hj : IsOpenEmbedding j) :
    ModuleOrientation.equivHomologicalOrientation (o.comap hj) =
      (ModuleOrientation.equivHomologicalOrientation o).comap hj := by
  rw [comap, Equiv.symm_apply_apply]

@[simp]
lemma _root_.TauCeti.ModuleOrientation.equivHomologicalOrientation_symm_comap
    (o : HomologicalOrientation N E d) (hj : IsOpenEmbedding j) :
    ModuleOrientation.equivHomologicalOrientation.symm (o.comap hj) =
      (ModuleOrientation.equivHomologicalOrientation.symm o).comap hj :=
  ModuleOrientation.equivHomologicalOrientation.symm_apply_apply _

lemma comap_apply (o : HomologicalOrientation N E d) (hj : IsOpenEmbedding j) (x : M) :
    o.comap hj x = (hj.localOrientationEquiv x d).symm (o (j x)) :=
  Subtype.ext <| by
    rw [comap, ModuleOrientation.coe_equivHomologicalOrientation_apply,
      ModuleOrientation.comap_apply, hj.coe_moduleLocalOrientationEquiv_symm,
      ModuleOrientation.coe_equivHomologicalOrientation_symm_apply,
      IsOpenEmbedding.coe_localOrientationEquiv_symm]

/-- The local orientation of the pullback at `x` corresponds to the local orientation of `o` at
`j x`. -/
@[simp]
lemma localOrientationEquiv_comap_apply (o : HomologicalOrientation N E d)
    (hj : IsOpenEmbedding j) (x : M) :
    hj.localOrientationEquiv x d (o.comap hj x) = o (j x) := by
  rw [comap_apply, Equiv.apply_symm_apply]

/-- The pullback depends only on the open embedding as a function, not on the proof that it is
one. -/
lemma comap_congr (o : HomologicalOrientation N E d) {j' : M → N} (hj : IsOpenEmbedding j)
    (hj' : IsOpenEmbedding j') (hjj' : j = j') : o.comap hj = o.comap hj' := by
  subst hjj'
  rfl

/-- Pulling back commutes with reversing orientations. -/
@[simp]
lemma comap_neg (o : HomologicalOrientation N E d) (hj : IsOpenEmbedding j) :
    (-o).comap hj = -o.comap hj := by
  rw [comap, comap, ModuleOrientation.equivHomologicalOrientation_symm_neg,
    ModuleOrientation.comap_neg, ModuleOrientation.equivHomologicalOrientation_neg]

/-- Pulling back along the identity does not change an orientation. -/
@[simp]
lemma comap_id (o : HomologicalOrientation M E d) : o.comap IsOpenEmbedding.id = o := by
  rw [comap, ModuleOrientation.comap_id, Equiv.apply_symm_apply]

/-- **Pulling back is functorial**: pulling back along `j` an orientation pulled back along `j'`
is pulling back along `j' ∘ j`. -/
lemma comap_comap (o : HomologicalOrientation P E d) {j' : N → P} (hj' : IsOpenEmbedding j')
    (hj : IsOpenEmbedding j) : (o.comap hj').comap hj = o.comap (hj'.comp hj) := by
  rw [comap, comap, comap, Equiv.symm_apply_apply, ModuleOrientation.comap_comap]

/-- Pulling back along `j'` and then along `j` is pulling back along any open embedding `k` equal to
`j' ∘ j`, for instance the inclusion of an open subset of an open subset. -/
lemma comap_comap_of_comp_eq (o : HomologicalOrientation P E d) {j' : N → P} {k : M → P}
    (hj' : IsOpenEmbedding j') (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    (hjk : j' ∘ j = k) : (o.comap hj').comap hj = o.comap hk := by
  rw [comap_comap, o.comap_congr _ hk hjk]

/-- Restricting an orientation of `M` to an open `W` and then to an open `V ⊆ W`, along the
inclusion `V ⟶ W` in `Opens (TopCat.of M)`, is restricting it to `V`. -/
@[simp]
lemma comap_comap_toTopCat_map (o : HomologicalOrientation N E d)
    {V W : TopologicalSpace.Opens (TopCat.of N)} (f : V ⟶ W) :
    (o.comap W.isOpenEmbedding).comap (TopologicalSpace.Opens.isOpenEmbedding_toTopCat_map f) =
      o.comap V.isOpenEmbedding :=
  o.comap_comap_of_comp_eq _ _ _ (funext fun _ ↦ rfl)

/-- Pulling an orientation back along a homeomorphism and then along its inverse gives it back. -/
@[simp]
lemma comap_symm_comap (o : HomologicalOrientation N E d) (e : M ≃ₜ N) :
    (o.comap e.isOpenEmbedding).comap e.symm.isOpenEmbedding = o := by
  rw [comap_comap, o.comap_congr _ IsOpenEmbedding.id (funext e.apply_symm_apply), comap_id]

end HomologicalOrientation

end TauCeti
