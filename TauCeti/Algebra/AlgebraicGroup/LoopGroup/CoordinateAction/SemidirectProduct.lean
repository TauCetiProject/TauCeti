/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.CoordinateAction.Loop
public import TauCeti.Algebra.Category.Grp.SemidirectProduct
public import TauCeti.RingTheory.PowerSeries.Coordinate.Functor
import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# Loop groups extended by coordinate changes

Let `H` be a Hopf algebra over a commutative ring `k`. The group
`Aut(O)(R) = TauCeti.FormalCoordinate R` of formal coordinate changes acts on the convolution
groups `WithConv (H →ₐ[k] R⸨t⸩)` and `WithConv (H →ₐ[k] R⟦t⟧)` by `ρ_φ (g) = σ_(φ⁻¹) ∘ g`,
through group automorphisms. When `H` is commutative these are the loop group `LG(R) = G(R⸨t⸩)`
and the positive loop group `L⁺G(R) = G(R⟦t⟧)` of `G = Spec H`. The semidirect products for these
actions, Mathlib's `SemidirectProduct` along `MulDistribMulAction.toMulAut`, have the
multiplication

  `(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`.

Since the actions are natural in `R`, the semidirect products `LG ⋊ Aut(O)` and
`L⁺G ⋊ Aut(O)` are group functors on all commutative `k`-algebras, nonreduced ones included,
built by `TauCeti.GrpCat.semidirectProductFunctor` from the group functors
`TauCeti.HopfAlgebra.loopGroup`, `TauCeti.HopfAlgebra.positiveLoopGroup` and the restriction of
`TauCeti.FormalCoordinate.groupFunctor` along `forget₂ (CommAlgCat k) CommRingCat`. Since the
inclusion `L⁺G → LG` is equivariant it extends, by `TauCeti.GrpCat.semidirectProductMap`, to an
injective natural homomorphism `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`. The loop groups embed as the normal
factors `(g, 1)` through `TauCeti.GrpCat.semidirectProductInl`.

The loop factor `R⸨t⸩` carries its coefficientwise `k`-algebra structure `HahnSeries.instAlgebra`,
as in `TauCeti.HopfAlgebra.loopGroup`. Statements about the elements of `LG ⋊ Aut(O)` select it
with `attribute [local instance 1100] HahnSeries.instAlgebra`, as this file does.

## Main definitions

* `TauCeti.HopfAlgebra.loopSemidirectProduct k H`: the group functor `LG ⋊ Aut(O)`.
* `TauCeti.HopfAlgebra.positiveLoopSemidirectProduct k H`: the group functor `L⁺G ⋊ Aut(O)`.
* `TauCeti.HopfAlgebra.positiveLoopSemidirectProductToLoopSemidirectProduct k H`: the natural
  inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`, injective at every `R`.
* `TauCeti.HopfAlgebra.loopToSemidirectProduct k H` and
  `TauCeti.HopfAlgebra.positiveLoopToSemidirectProduct k H`: the natural inclusions
  `g ↦ (g, 1)` of `LG` and `L⁺G`.

## Main results

* `TauCeti.HopfAlgebra.positiveLoopSemidirectProductToLoopSemidirectProduct_app_injective`: the
  inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)` is injective.
* `positiveLoopToSemidirectProduct_comp_positiveLoopSemidirectProductToLoopSemidirectProduct`:
  the inclusions of the loop groups commute with the inclusions `L⁺G → LG` and
  `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §1.3.1 for the loop group, §§3.5.3–3.5.4 for the group of coordinate changes.
-/

public section

open CategoryTheory WithConv
open scoped LaurentSeries PowerSeries

-- The coefficientwise `k`-algebra structure on Laurent series, as in `CommAlgCat.laurentSeries`.
attribute [local instance 1100] HahnSeries.instAlgebra

universe u v w

namespace TauCeti.HopfAlgebra

variable (k : Type u) [CommRing k] (H : Type v) [Semiring H] [_root_.HopfAlgebra k H]

/-- The group functor `LG ⋊ Aut(O) : R ↦ WithConv (H →ₐ[k] R⸨t⸩) ⋊ FormalCoordinate R` on
commutative `k`-algebras, the semidirect product of the loop group by the coordinate changes acting
through `ρ_φ (g) = σ_(φ⁻¹) ∘ g`; for a commutative `H` the first factor is the loop group
`G(R⸨t⸩)` of `G = Spec H`. A morphism `f : R ⟶ S` acts on both factors through the
coefficients. -/
@[expose] noncomputable def loopSemidirectProduct : CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  GrpCat.semidirectProductFunctor (loopGroup k H)
    (forget₂ (CommAlgCat.{w} k) CommRingCat.{w} ⋙ FormalCoordinate.groupFunctor)
    (fun R ↦ MulDistribMulAction.toMulAut (FormalCoordinate R) (WithConv (H →ₐ[k] R⸨X⸩)))
    fun _ _ f φ g ↦ by
      rw [loopGroup_map_apply, loopGroup_map_apply, Functor.comp_map,
        FormalCoordinate.groupFunctor_map_apply]
      exact LaurentSeries.mapValue_mapAlgHom_smul f.hom φ g

/-- The group functor `L⁺G ⋊ Aut(O) : R ↦ WithConv (H →ₐ[k] R⟦t⟧) ⋊ FormalCoordinate R` on
commutative `k`-algebras, the semidirect product of the positive loop group by the coordinate
changes acting through `ρ_φ (g) = σ_(φ⁻¹) ∘ g`; for a commutative `H` the first factor is the
positive loop group `G(R⟦t⟧)` of `G = Spec H`. -/
@[expose] noncomputable def positiveLoopSemidirectProduct :
    CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  GrpCat.semidirectProductFunctor (positiveLoopGroup k H)
    (forget₂ (CommAlgCat.{w} k) CommRingCat.{w} ⋙ FormalCoordinate.groupFunctor)
    (fun R ↦ MulDistribMulAction.toMulAut (FormalCoordinate R) (WithConv (H →ₐ[k] R⟦X⟧)))
    fun _ _ f φ g ↦ by
      rw [positiveLoopGroup_map_apply, positiveLoopGroup_map_apply, Functor.comp_map,
        FormalCoordinate.groupFunctor_map_apply]
      exact FormalCoordinate.mapValue_mapAlgHom_smul f.hom φ g

/-- The group `(LG ⋊ Aut(O))(R)` is the semidirect product
`WithConv (H →ₐ[k] R⸨t⸩) ⋊ FormalCoordinate R`. -/
lemma loopSemidirectProduct_obj (R : CommAlgCat.{w} k) :
    (loopSemidirectProduct k H).obj R = GrpCat.of
      (WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :=
  (rfl)

/-- The group `(L⁺G ⋊ Aut(O))(R)` is the semidirect product
`WithConv (H →ₐ[k] R⟦t⟧) ⋊ FormalCoordinate R`. -/
lemma positiveLoopSemidirectProduct_obj (R : CommAlgCat.{w} k) :
    (positiveLoopSemidirectProduct k H).obj R = GrpCat.of
      (WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :=
  (rfl)

variable {k H}

/-- A morphism `f : R ⟶ S` acts on `LG ⋊ Aut(O)` by applying `f` to the coefficients of both
factors. -/
@[simp]
lemma loopSemidirectProduct_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (loopSemidirectProduct k H).map f x =
      ⟨AlgHom.mapValue (HahnSeries.mapAlgHom f.hom) x.left,
        FormalCoordinate.map (f.hom : R →+* S) x.right⟩ :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on `L⁺G ⋊ Aut(O)` by applying `f` to the coefficients of both
factors. -/
@[simp]
lemma positiveLoopSemidirectProduct_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (positiveLoopSemidirectProduct k H).map f x =
      ⟨AlgHom.mapValue (PowerSeries.mapAlgHom f.hom) x.left,
        FormalCoordinate.map (f.hom : R →+* S) x.right⟩ :=
  (rfl)

variable (k H)

/-- The natural inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`, the inclusion `L⁺G → LG` on the first
factor and the identity on the coordinate changes. It is a homomorphism because the inclusion of
arcs into loops is equivariant. -/
noncomputable def positiveLoopSemidirectProductToLoopSemidirectProduct :
    positiveLoopSemidirectProduct.{u, v, w} k H ⟶ loopSemidirectProduct k H :=
  GrpCat.semidirectProductMap (positiveLoopToLoop k H) (𝟙 _) fun R (φ : FormalCoordinate R) g ↦ by
    rw [positiveLoopToLoop_app_apply, positiveLoopToLoop_app_apply]
    exact LaurentSeries.mapValue_ofPowerSeriesAlg_smul φ g

variable {k H}

/-- The inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)` includes the arc and keeps the coordinate
change. -/
@[simp]
lemma positiveLoopSemidirectProductToLoopSemidirectProduct_app_apply (R : CommAlgCat.{w} k)
    (x : WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (positiveLoopSemidirectProductToLoopSemidirectProduct k H).app R x =
      ⟨AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k) x.left, x.right⟩ := by
  refine (GrpCat.semidirectProductMap_app_apply _ _ _ R _).trans ?_
  exact SemidirectProduct.ext (positiveLoopToLoop_app_apply k H R x.left) rfl

/-- An element of `L⁺G ⋊ Aut(O)` is determined by its image in `LG ⋊ Aut(O)`. -/
theorem positiveLoopSemidirectProductToLoopSemidirectProduct_app_injective
    (R : CommAlgCat.{w} k) :
    Function.Injective ((positiveLoopSemidirectProductToLoopSemidirectProduct k H).app R) :=
  GrpCat.semidirectProductMap_app_injective _ _ _ R (positiveLoopToLoop_app_injective k H R)
    fun _ _ ↦ id

variable (k H)

/-- The natural inclusion `g ↦ (g, 1)` of the loop group `LG` into `LG ⋊ Aut(O)`. -/
noncomputable def loopToSemidirectProduct :
    loopGroup.{u, v, w} k H ⟶ loopSemidirectProduct k H :=
  GrpCat.semidirectProductInl _ _ _ _

/-- The natural inclusion `g ↦ (g, 1)` of the positive loop group `L⁺G` into `L⁺G ⋊ Aut(O)`. -/
noncomputable def positiveLoopToSemidirectProduct :
    positiveLoopGroup.{u, v, w} k H ⟶ positiveLoopSemidirectProduct k H :=
  GrpCat.semidirectProductInl _ _ _ _

variable {k H}

/-- The inclusion of `LG` into `LG ⋊ Aut(O)` sends a loop `g` to `(g, 1)`. -/
lemma loopToSemidirectProduct_app_apply (R : CommAlgCat.{w} k)
    (g : WithConv (H →ₐ[k] R⸨X⸩)) :
    (loopToSemidirectProduct k H).app R g = SemidirectProduct.inl g :=
  GrpCat.semidirectProductInl_app_apply (loopGroup k H) _ _ _ R g

/-- The inclusion of `L⁺G` into `L⁺G ⋊ Aut(O)` sends an arc `g` to `(g, 1)`. -/
lemma positiveLoopToSemidirectProduct_app_apply (R : CommAlgCat.{w} k)
    (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    (positiveLoopToSemidirectProduct k H).app R g = SemidirectProduct.inl g :=
  GrpCat.semidirectProductInl_app_apply (positiveLoopGroup k H) _ _ _ R g

/-- The inclusions of the loop groups into their semidirect products commute with the inclusions
`L⁺G → LG` and `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`. -/
theorem positiveLoopToSemidirectProduct_comp_positiveLoopSemidirectProductToLoopSemidirectProduct :
    positiveLoopToSemidirectProduct.{u, v, w} k H ≫
        positiveLoopSemidirectProductToLoopSemidirectProduct k H =
      positiveLoopToLoop k H ≫ loopToSemidirectProduct k H :=
  GrpCat.semidirectProductInl_comp_map _ _ _

/-- For the trivial group, `LG ⋊ Aut(O)` is the group of coordinate changes: the projection to
the second factor is an isomorphism. -/
example (R : CommAlgCat.{w} k) :
    Function.Bijective (SemidirectProduct.rightHom :
      (WithConv (k →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) →*
        FormalCoordinate R) :=
  ⟨fun _ _ hxy ↦ SemidirectProduct.ext
      ((WithConv.convPoint_eq_one _).trans (WithConv.convPoint_eq_one _).symm) hxy,
    SemidirectProduct.rightHom_surjective⟩

end TauCeti.HopfAlgebra
