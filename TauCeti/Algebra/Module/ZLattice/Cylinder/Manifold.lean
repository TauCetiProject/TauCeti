/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Cylinder
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Quotients by discrete subgroups are cylinders `Tʳ × ℝⁿ⁻ʳ` as manifolds

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E`, and let `B` be a real
basis of `E` indexed by `ι ⊕ κ` whose vectors `B (inl i)` span `L` over `ℤ`; every discrete
subgroup has such an adapted basis (`AddSubgroup.exists_basis_span_range_comp_inl_eq`). Cylinder
coordinates, the `ι`-coordinates in `B` reduced modulo one and the `κ`-coordinates, identify the
quotient with a cylinder as topological groups (`Module.Basis.quotientCylinderEquiv`):

`E / L ≃ (ℝ / ℤ)^ι × ℝ^κ`.

This file shows that this identification is a `C^n` diffeomorphism for every `n`, analytic
included, for the quotient manifold structure of the orbit space of translation by `L`
(`TauCeti.instIsManifoldAddQuotient`) and the product of the torus `(ℝ / ℤ)^ι`, modelled on
`ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)`, with the vector space `ℝ^κ`
(`Module.Basis.orbitRelQuotientCylinderDiffeomorph`).

Both directions are smooth because both are linear maps read through local diffeomorphisms: the
orbit projection `E → E / L` is a surjective local diffeomorphism
(`TauCeti.isLocalDiffeomorph_addQuotientMk`), and composed with it the cylinder map is the linear
coordinate map of `B` followed by reduction modulo one on the `ι`-coordinates; the map
`(t, y) ↦ (([tᵢ])ᵢ, y)` from `ℝ^ι × ℝ^κ` onto the cylinder is a surjective local diffeomorphism
(`AddCircle.isLocalDiffeomorph_coe_pi`), and composed with it the inverse map is the linear map
`(t, y) ↦ ∑ᵢ tᵢ B (inl i) + ∑ₖ yₖ B (inr k)` followed by the orbit projection. Smoothness descends
along surjective local diffeomorphisms (`IsLocalDiffeomorph.contMDiff_comp_iff`).

For a full lattice (`κ` empty) the quotient is a torus; in general the rank `|ι|` of `L` may be
smaller than the dimension of `E`, and the quotient is a noncompact cylinder.

## Main definitions

* `Module.Basis.orbitRelQuotientCylinderDiffeomorph`: the `C^n` diffeomorphism
  `E / L ≃ (ℝ / ℤ)^ι × ℝ^κ` of cylinder coordinates.

## Main results

* `Module.Basis.orbitRelQuotientCylinderDiffeomorph_apply_mk`: it sends the orbit of `x` to the
  cylinder coordinates of `x`.
* `Module.Basis.orbitRelQuotientCylinderDiffeomorph_symm_apply`: its inverse sends reduced
  coordinates `t` and coordinates `y` to the orbit of the vector with coordinates `t` and `y`.

## References

* N. Bourbaki, *General Topology*, Chapter VII, § 1, no. 2, Theorem 2 (discrete subgroups of `ℝⁿ`
  and the quotients `Tʳ × ℝⁿ⁻ʳ`).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Module Submodule
open scoped Manifold ContDiff

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Basis (ι ⊕ κ) ℝ E)
  {L : Submodule ℤ E} (hL : L = span ℤ (Set.range (B ∘ Sum.inl)))

include hL

omit [Fintype ι] [Fintype κ] in
/-- Cylinder coordinates on the orbit space of translation by `L`: the isomorphism of topological
groups `Module.Basis.quotientCylinderEquiv` read on the orbit space through
`Submodule.orbitRelQuotientContinuousAddEquiv`. The two compose because the quotient `E ⧸ L` by the
submodule and the quotient `E ⧸ L.toAddSubgroup` by its underlying subgroup are the same type, by
structure projections. -/
private def orbitRelQuotientCylinderEquiv :
    AddAction.orbitRel.Quotient L E ≃ₜ+ UnitAddTorus ι × (κ → ℝ) :=
  L.orbitRelQuotientContinuousAddEquiv.trans
    (B.quotientCylinderEquiv (L := L.toAddSubgroup) (by rw [hL]))

omit [Fintype ι] [Fintype κ] in
/-- In cylinder coordinates, the orbit of `x` under translation by `L` is sent to the cylinder
coordinates of `x`. -/
private theorem orbitRelQuotientCylinderEquiv_apply_mk (x : E) :
    B.orbitRelQuotientCylinderEquiv hL (Quotient.mk (AddAction.orbitRel L E) x) =
      B.cylinderCoordinates x :=
  (congrArg (B.quotientCylinderEquiv (L := L.toAddSubgroup) (by rw [hL]))
    (L.orbitRelQuotientContinuousAddEquiv_mk x)).trans
    (B.quotientCylinderEquiv_apply_mk (L := L.toAddSubgroup) _ x)

omit [Fintype ι] [Fintype κ] in
/-- The inverse cylinder coordinates send reduced coordinates `t` and coordinates `y` to the orbit
of the vector with coordinates `t` and `y`. -/
private theorem orbitRelQuotientCylinderEquiv_symm_apply [Finite ι] [Finite κ]
    (t : ι → ℝ) (y : κ → ℝ) :
    (B.orbitRelQuotientCylinderEquiv hL).symm (fun i ↦ (t i : UnitAddCircle), y) =
      Quotient.mk (AddAction.orbitRel L E) (B.equivFun.symm (Sum.elim t y)) :=
  (congrArg L.orbitRelQuotientContinuousAddEquiv.symm
    (B.quotientCylinderEquiv_symm_apply (L := L.toAddSubgroup) _ t y)).trans
    (L.orbitRelQuotientContinuousAddEquiv_symm_mk _)

variable [DiscreteTopology L] (n : ℕ∞ω)

/-- Cylinder coordinates on the orbit space are smooth: composed with the orbit projection, they
are the linear coordinate map of `B` followed by reduction modulo one on the torus factor. -/
private theorem contMDiff_orbitRelQuotientCylinderEquiv :
    ContMDiff 𝓘(ℝ, E) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, κ → ℝ)) n
      (B.orbitRelQuotientCylinderEquiv hL) := by
  refine (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℝ, E)) (n := n)).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl |>.1 ?_
  have h : ⇑(B.orbitRelQuotientCylinderEquiv hL) ∘ Quotient.mk (AddAction.orbitRel L E) = fun x ↦
      ((fun i ↦ ((B.coord (.inl i) x : ℝ) : UnitAddCircle)), fun k ↦ B.coord (.inr k) x) := by
    funext x
    rw [Function.comp_apply, B.orbitRelQuotientCylinderEquiv_apply_mk hL]
    ext i <;> simp
  rw [h]
  exact ((AddCircle.contMDiff_coe_pi 1 n).comp
    (ContinuousLinearMap.pi fun i ↦ (B.coord (.inl i)).toContinuousLinearMap).contMDiff).prodMk
    (ContinuousLinearMap.pi fun k ↦ (B.coord (.inr k)).toContinuousLinearMap).contMDiff

/-- The inverse cylinder coordinates are smooth: composed with the covering map
`ℝ^ι × ℝ^κ → (ℝ / ℤ)^ι × ℝ^κ`, they are the orbit projection of the vector with the given
coordinates, a linear function of them. -/
private theorem contMDiff_orbitRelQuotientCylinderEquiv_symm :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, κ → ℝ)) 𝓘(ℝ, E) n
      (B.orbitRelQuotientCylinderEquiv hL).symm := by
  -- The covering map, reduction modulo one on the first factor, is a surjective local
  -- diffeomorphism.
  have hq : IsLocalDiffeomorph (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, κ → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, κ → ℝ)) n
      (Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : UnitAddCircle)) (id : (κ → ℝ) → κ → ℝ)) :=
    (AddCircle.isLocalDiffeomorph_coe_pi 1 n).prodMap
      (Diffeomorph.refl 𝓘(ℝ, κ → ℝ) (κ → ℝ) n).isLocalDiffeomorph
  have hqs : Function.Surjective
      (Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : UnitAddCircle)) (id : (κ → ℝ) → κ → ℝ)) :=
    (Function.Surjective.piMap fun _ ↦ QuotientAddGroup.mk_surjective).prodMap
      Function.surjective_id
  refine (hq.contMDiff_comp_iff hqs le_rfl).1 ?_
  -- The vector with coordinates `(t, y)` is their image under a linear equivalence.
  have h : ⇑(B.orbitRelQuotientCylinderEquiv hL).symm ∘
        Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : UnitAddCircle)) (id : (κ → ℝ) → κ → ℝ) =
      Quotient.mk (AddAction.orbitRel L E) ∘
        ⇑(((ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ fun _ ↦ ℝ).symm.trans
          B.equivFun.toContinuousLinearEquiv.symm : (ι → ℝ) × (κ → ℝ) →L[ℝ] E)) := by
    funext ⟨t, y⟩
    -- The inverse of `ContinuousLinearEquiv.sumPiEquivProdPi` is `Sum.rec`, which agrees with
    -- `Sum.elim` on both summands.
    have hs : (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ fun _ ↦ ℝ).symm (t, y) =
        Sum.elim t y := by
      ext (i | k) <;> rfl
    simpa [hs] using B.orbitRelQuotientCylinderEquiv_symm_apply hL t y
  rw [h]
  -- `(fst, snd)` passes from the product model to the model of the product vector space.
  exact (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℝ, E)) (n := n)).contMDiff.comp
    ((ContinuousLinearMap.contMDiff _).comp (contMDiff_fst.prodMk_space contMDiff_snd))

/-- **Cylinder coordinates are a `C^n` diffeomorphism.** If `L` is the integer span of the vectors
`B (inl i)` of a real basis `B` of `E` indexed by `ι ⊕ κ`, reducing the `ι`-coordinates in `B`
modulo one and keeping the `κ`-coordinates identifies the orbit space `E / L` of translation by
`L` with the cylinder `(ℝ / ℤ)^ι × ℝ^κ`, as `C^n` manifolds, for every `n` (analytic included).
The underlying isomorphism of topological groups is `Module.Basis.quotientCylinderEquiv`, read on
the orbit space through `Submodule.orbitRelQuotientContinuousAddEquiv`. -/
def orbitRelQuotientCylinderDiffeomorph :
    AddAction.orbitRel.Quotient L E ≃ₘ^n⟮𝓘(ℝ, E),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, κ → ℝ)⟯ UnitAddTorus ι × (κ → ℝ) :=
  { toEquiv := (B.orbitRelQuotientCylinderEquiv hL).toEquiv
    contMDiff_toFun := B.contMDiff_orbitRelQuotientCylinderEquiv hL n
    contMDiff_invFun := B.contMDiff_orbitRelQuotientCylinderEquiv_symm hL n }

/-- The cylinder diffeomorphism sends the orbit of `x` to the cylinder coordinates of `x`: the
`ι`-coordinates of `x` in `B` modulo one, and its `κ`-coordinates. -/
@[simp]
theorem orbitRelQuotientCylinderDiffeomorph_apply_mk (x : E) :
    B.orbitRelQuotientCylinderDiffeomorph hL n (Quotient.mk (AddAction.orbitRel L E) x) =
      B.cylinderCoordinates x :=
  B.orbitRelQuotientCylinderEquiv_apply_mk hL x

/-- The inverse of the cylinder diffeomorphism sends reduced coordinates `t` and coordinates `y` to
the orbit of the vector with coordinates `t` and `y` in the basis `B`. -/
@[simp]
theorem orbitRelQuotientCylinderDiffeomorph_symm_apply (t : ι → ℝ) (y : κ → ℝ) :
    (B.orbitRelQuotientCylinderDiffeomorph hL n).symm (fun i ↦ (t i : UnitAddCircle), y) =
      Quotient.mk (AddAction.orbitRel L E) (B.equivFun.symm (Sum.elim t y)) :=
  B.orbitRelQuotientCylinderEquiv_symm_apply hL t y

end Module.Basis
