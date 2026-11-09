/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological

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
  let e := localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
    (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d
  e.toLinearEquiv.toEquiv.subtypeEquiv fun z ↦
    ⟨fun hz ↦ hz.map e, fun hz ↦ (e.hom_inv_id_apply z) ▸ hz.map e.symm⟩

/-- On local homology classes, the correspondence of local orientations is the map induced by
`j`. -/
@[simp]
lemma coe_localOrientationEquiv (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    (hj.localOrientationEquiv x d z).val =
      (localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d).hom z.val :=
  (rfl)

/-- The inverse correspondence acts on local homology classes by the inverse isomorphism. -/
@[simp]
lemma coe_localOrientationEquiv_symm (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation N (j x) d) :
    ((hj.localOrientationEquiv x d).symm z).val =
      (localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d).inv z.val :=
  (rfl)

/-- The correspondence of local orientations commutes with reversal. -/
@[simp]
lemma localOrientationEquiv_neg (hj : IsOpenEmbedding j) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    hj.localOrientationEquiv x d (-z) =
      -hj.localOrientationEquiv x d z :=
  Subtype.ext ((localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
    (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x d).hom.hom.map_neg z.val)

/-- The identity identifies the local orientations at `x` with themselves. -/
@[simp]
lemma localOrientationEquiv_id [T1Space M] (x : M) (d : ℕ) :
    IsOpenEmbedding.id.localOrientationEquiv x d = Equiv.refl _ :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_id]
    rfl

/-- The correspondences of local orientations along open embeddings are functorial. -/
@[simp]
lemma localOrientationEquiv_trans {P : Type w} [TopologicalSpace P] [T1Space P] {j' : N → P}
    (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (x : M) (d : ℕ) :
    (hj.localOrientationEquiv x d).trans (hj'.localOrientationEquiv (j x) d) =
      (hj'.comp hj).localOrientationEquiv x d :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [Equiv.trans_apply, coe_localOrientationEquiv, coe_localOrientationEquiv,
      coe_localOrientationEquiv, ← ConcreteCategory.comp_apply, ← Iso.trans_hom,
      localHomologyIsoOfIsOpenEmbedding_trans]

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
    HomologicalOrientation M E d where
  toFun x := (hj.localOrientationEquiv x d).symm (o (j x))
  localOrientationTransport_toFun' {x y} f := by
    apply (hj.localOrientationEquiv y.as d).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    -- Elementwise, `j` intertwines the transports of `M` and of `N`.
    have h : (localHomologyIsoOfIsOpenEmbedding (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hj y.as d).hom
        (localHomologyTransport (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d f
          ((hj.localOrientationEquiv x.as d).symm (o (j x.as))).val) =
        localHomologyTransport (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) N E d
          ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f) ((localHomologyIsoOfIsOpenEmbedding
            (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) hj x.as d).hom
            ((hj.localOrientationEquiv x.as d).symm (o (j x.as))).val) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom
          (localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom
            (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) (E := E) hj d f) _).trans
          (ConcreteCategory.comp_apply _ _ _))
    rw [IsOpenEmbedding.coe_localOrientationEquiv, coe_localOrientationTransport, h,
      ← IsOpenEmbedding.coe_localOrientationEquiv, Equiv.apply_symm_apply]
    exact (coe_localOrientationTransport N E d _ _).symm.trans
      (congrArg Subtype.val (o.localOrientationTransport_apply
        ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f)))

lemma comap_apply (o : HomologicalOrientation N E d) (hj : IsOpenEmbedding j) (x : M) :
    o.comap hj x = (hj.localOrientationEquiv x d).symm (o (j x)) :=
  (rfl)

/-- The local orientation of the pullback at `x` corresponds to the local orientation of `o` at
`j x`. -/
@[simp]
lemma localOrientationEquiv_comap_apply (o : HomologicalOrientation N E d)
    (hj : IsOpenEmbedding j) (x : M) :
    hj.localOrientationEquiv x d (o.comap hj x) = o (j x) :=
  Equiv.apply_symm_apply _ _

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
  ext x : 1
  apply (hj.localOrientationEquiv x d).injective
  rw [localOrientationEquiv_comap_apply, neg_apply, neg_apply,
    IsOpenEmbedding.localOrientationEquiv_neg, localOrientationEquiv_comap_apply]

/-- Pulling back along the identity does not change an orientation. -/
@[simp]
lemma comap_id (o : HomologicalOrientation M E d) : o.comap IsOpenEmbedding.id = o := by
  ext x : 1
  apply (IsOpenEmbedding.localOrientationEquiv IsOpenEmbedding.id x d).injective
  rw [localOrientationEquiv_comap_apply, IsOpenEmbedding.localOrientationEquiv_id]
  rfl

/-- **Pulling back is functorial**: pulling back along `j` an orientation pulled back along `j'`
is pulling back along `j' ∘ j`. -/
lemma comap_comap (o : HomologicalOrientation P E d) {j' : N → P} (hj' : IsOpenEmbedding j')
    (hj : IsOpenEmbedding j) : (o.comap hj').comap hj = o.comap (hj'.comp hj) := by
  ext x : 1
  apply ((hj'.comp hj).localOrientationEquiv x d).injective
  rw [localOrientationEquiv_comap_apply, ← IsOpenEmbedding.localOrientationEquiv_trans hj hj',
    Equiv.trans_apply, localOrientationEquiv_comap_apply, localOrientationEquiv_comap_apply]
  rfl

/-- Pulling an orientation back along a homeomorphism and then along its inverse gives it back. -/
@[simp]
lemma comap_symm_comap (o : HomologicalOrientation N E d) (e : M ≃ₜ N) :
    (o.comap e.isOpenEmbedding).comap e.symm.isOpenEmbedding = o := by
  rw [comap_comap, o.comap_congr _ IsOpenEmbedding.id (funext e.apply_symm_apply), comap_id]

end HomologicalOrientation

end TauCeti
