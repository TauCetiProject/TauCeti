/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.CoordinateAction.Loop
public import TauCeti.RingTheory.PowerSeries.Coordinate.Functor
import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# Loop groups extended by coordinate changes

Let `G` be the affine group over a commutative ring `k` with coordinate Hopf algebra `H`. The
group `Aut(O)(R) = TauCeti.FormalCoordinate R` of formal coordinate changes acts on the loops
`LG(R) = G(R⸨t⸩)` and on the arcs `L⁺G(R) = G(R⟦t⟧)` by `ρ_φ (g) = σ_(φ⁻¹) ∘ g`, through group
automorphisms. The semidirect products for these actions, Mathlib's `SemidirectProduct` along
`MulDistribMulAction.toMulAut`, have the multiplication

  `(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`.

Since the actions are natural in `R`, the semidirect products `LG ⋊ Aut(O)` and
`L⁺G ⋊ Aut(O)` are group functors on all commutative `k`-algebras, nonreduced ones included, and
since the inclusion `L⁺G → LG` is equivariant it extends to an injective natural homomorphism
`L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`. The loop groups embed as the normal factors `(g, 1)`, and the
projections to the coordinate change are natural along the group functor
`TauCeti.FormalCoordinate.groupFunctor k` of `Aut(O)`.

## Main definitions

* `TauCeti.HopfAlgebra.loopSemidirectProduct k H`: the group functor `LG ⋊ Aut(O)`.
* `TauCeti.HopfAlgebra.positiveLoopSemidirectProduct k H`: the group functor `L⁺G ⋊ Aut(O)`.
* `TauCeti.HopfAlgebra.positiveLoopSemidirectProductToLoop k H`: the natural inclusion
  `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`, injective at every `R`.
* `TauCeti.HopfAlgebra.loopToSemidirectProduct k H` and
  `TauCeti.HopfAlgebra.positiveLoopToSemidirectProduct k H`: the natural inclusions
  `g ↦ (g, 1)` of `LG` and `L⁺G`.

## Main results

* `TauCeti.HopfAlgebra.positiveLoopSemidirectProductToLoop_app_injective`: the inclusion
  `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)` is injective.
* `TauCeti.HopfAlgebra.rightHom_loopSemidirectProduct_map`: the projection `LG ⋊ Aut(O) → Aut(O)`
  is natural in `R`.

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

/-- The group functor `LG ⋊ Aut(O) : R ↦ G(R⸨t⸩) ⋊ FormalCoordinate R` on commutative
`k`-algebras, the semidirect product of the loop group by the coordinate changes acting through
`ρ_φ (g) = σ_(φ⁻¹) ∘ g`. A morphism `f : R ⟶ S` acts on both factors through the coefficients. -/
@[expose] noncomputable def loopSemidirectProduct : CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of
    (WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R)
  map {R S} f := GrpCat.ofHom <| SemidirectProduct.map
    (AlgHom.mapValue (HahnSeries.mapAlgHom f.hom)) (FormalCoordinate.map (f.hom : R →+* S))
    fun φ ↦ MonoidHom.ext fun g ↦ LaurentSeries.mapValue_mapAlgHom_smul f.hom φ g
  map_id R := GrpCat.ext fun x ↦ SemidirectProduct.ext (by simp) (by simp)
  map_comp f g := GrpCat.ext fun x ↦ SemidirectProduct.ext
    (by simp [HahnSeries.mapAlgHom_comp, AlgHom.mapValue_comp])
    (FormalCoordinate.ext <| by simp [AlgHom.comp_toRingHom, PowerSeries.map_comp])

/-- The group functor `L⁺G ⋊ Aut(O) : R ↦ G(R⟦t⟧) ⋊ FormalCoordinate R` on commutative
`k`-algebras, the semidirect product of the positive loop group by the coordinate changes acting
through `ρ_φ (g) = σ_(φ⁻¹) ∘ g`. -/
@[expose] noncomputable def positiveLoopSemidirectProduct :
    CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of
    (WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R)
  map {R S} f := GrpCat.ofHom <| SemidirectProduct.map
    (AlgHom.mapValue (PowerSeries.mapAlgHom f.hom)) (FormalCoordinate.map (f.hom : R →+* S))
    fun φ ↦ MonoidHom.ext fun g ↦ FormalCoordinate.mapValue_mapAlgHom_smul f.hom φ g
  map_id R := GrpCat.ext fun x ↦ SemidirectProduct.ext
    (ofConv_injective <| AlgHom.ext fun h ↦ PowerSeries.ext fun n ↦ by
      simp [PowerSeries.mapAlgHom_apply]) (by simp)
  map_comp f g := GrpCat.ext fun x ↦ SemidirectProduct.ext
    (ofConv_injective <| AlgHom.ext fun h ↦ PowerSeries.ext fun n ↦ by
      simp [PowerSeries.mapAlgHom_apply])
    (FormalCoordinate.ext <| by simp [AlgHom.comp_toRingHom, PowerSeries.map_comp])

/-- The group `(LG ⋊ Aut(O))(R)` is the semidirect product `G(R⸨t⸩) ⋊ FormalCoordinate R`. -/
lemma loopSemidirectProduct_obj (R : CommAlgCat.{w} k) :
    (loopSemidirectProduct k H).obj R = GrpCat.of
      (WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :=
  (rfl)

/-- The group `(L⁺G ⋊ Aut(O))(R)` is the semidirect product `G(R⟦t⟧) ⋊ FormalCoordinate R`. -/
lemma positiveLoopSemidirectProduct_obj (R : CommAlgCat.{w} k) :
    (positiveLoopSemidirectProduct k H).obj R = GrpCat.of
      (WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :=
  (rfl)

variable {k H}

/-- A morphism `f : R ⟶ S` acts on `LG ⋊ Aut(O)` by applying `f` to the coefficients of both
factors. -/
lemma loopSemidirectProduct_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (loopSemidirectProduct k H).map f x =
      ⟨AlgHom.mapValue (HahnSeries.mapAlgHom f.hom) x.left,
        FormalCoordinate.map (f.hom : R →+* S) x.right⟩ :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on `L⁺G ⋊ Aut(O)` by applying `f` to the coefficients of both
factors. -/
lemma positiveLoopSemidirectProduct_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (positiveLoopSemidirectProduct k H).map f x =
      ⟨AlgHom.mapValue (PowerSeries.mapAlgHom f.hom) x.left,
        FormalCoordinate.map (f.hom : R →+* S) x.right⟩ :=
  (rfl)

/-- The projection `LG ⋊ Aut(O) → Aut(O)` to the coordinate change is natural in `R`. -/
lemma rightHom_loopSemidirectProduct_map {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    SemidirectProduct.rightHom ((loopSemidirectProduct k H).map f x) =
      (FormalCoordinate.groupFunctor k).map f (SemidirectProduct.rightHom x) :=
  (rfl)

/-- The projection `L⁺G ⋊ Aut(O) → Aut(O)` to the coordinate change is natural in `R`. -/
lemma rightHom_positiveLoopSemidirectProduct_map {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (x : WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    SemidirectProduct.rightHom ((positiveLoopSemidirectProduct k H).map f x) =
      (FormalCoordinate.groupFunctor k).map f (SemidirectProduct.rightHom x) :=
  (rfl)

variable (k H)

/-- The natural inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`, the inclusion `L⁺G → LG` on the first
factor and the identity on the coordinate changes. It is a homomorphism because the inclusion of
arcs into loops is equivariant. -/
noncomputable def positiveLoopSemidirectProductToLoop :
    positiveLoopSemidirectProduct.{u, v, w} k H ⟶ loopSemidirectProduct k H where
  app R := GrpCat.ofHom <| SemidirectProduct.map
    (AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k)) (MonoidHom.id _) fun φ ↦
      MonoidHom.ext fun g ↦ LaurentSeries.mapValue_ofPowerSeriesAlg_smul φ g
  naturality R S f := GrpCat.ext fun x ↦ SemidirectProduct.ext (by
    -- the inclusion `R⟦X⟧ → R⸨X⸩` is natural in `R`
    have key := congr(AlgHom.mapValue (H := H) ($((CommAlgCat.ofPowerSeries k).naturality f)).hom)
    simp only [CommAlgCat.hom_comp, CommAlgCat.ofPowerSeries_app_hom, AlgHom.mapValue_comp] at key
    exact DFunLike.congr_fun key x.left) rfl

variable {k H}

/-- The inclusion `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)` includes the arc and keeps the coordinate
change. -/
lemma positiveLoopSemidirectProductToLoop_app_apply (R : CommAlgCat.{w} k)
    (x : WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) :
    (positiveLoopSemidirectProductToLoop k H).app R x =
      ⟨AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k) x.left, x.right⟩ :=
  (rfl)

/-- An element of `L⁺G ⋊ Aut(O)` is determined by its image in `LG ⋊ Aut(O)`. -/
theorem positiveLoopSemidirectProductToLoop_app_injective (R : CommAlgCat.{w} k) :
    Function.Injective ((positiveLoopSemidirectProductToLoop k H).app R) := by
  intro x y hxy
  have hl : AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k) x.left =
      AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k) y.left :=
    congrArg SemidirectProduct.left hxy
  refine SemidirectProduct.ext (AlgHom.mapValue_injective ?_ hl)
    (congrArg SemidirectProduct.right hxy :)
  rw [HahnSeries.coe_ofPowerSeriesAlg]
  exact HahnSeries.ofPowerSeries_injective

variable (k H)

/-- The natural inclusion `g ↦ (g, 1)` of the loop group `LG` into `LG ⋊ Aut(O)`. -/
noncomputable def loopToSemidirectProduct :
    loopGroup.{u, v, w} k H ⟶ loopSemidirectProduct k H where
  app _ := GrpCat.ofHom SemidirectProduct.inl
  naturality _ _ _ := GrpCat.ext fun _ ↦ SemidirectProduct.ext rfl (map_one _).symm

/-- The natural inclusion `g ↦ (g, 1)` of the positive loop group `L⁺G` into `L⁺G ⋊ Aut(O)`. -/
noncomputable def positiveLoopToSemidirectProduct :
    positiveLoopGroup.{u, v, w} k H ⟶ positiveLoopSemidirectProduct k H where
  app _ := GrpCat.ofHom SemidirectProduct.inl
  naturality _ _ _ := GrpCat.ext fun _ ↦ SemidirectProduct.ext rfl (map_one _).symm

variable {k H}

/-- The inclusion of `LG` into `LG ⋊ Aut(O)` sends a loop `g` to `(g, 1)`. -/
lemma loopToSemidirectProduct_app_apply (R : CommAlgCat.{w} k)
    (g : WithConv (H →ₐ[k] R⸨X⸩)) :
    (loopToSemidirectProduct k H).app R g = SemidirectProduct.inl g :=
  (rfl)

/-- The inclusion of `L⁺G` into `L⁺G ⋊ Aut(O)` sends an arc `g` to `(g, 1)`. -/
lemma positiveLoopToSemidirectProduct_app_apply (R : CommAlgCat.{w} k)
    (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    (positiveLoopToSemidirectProduct k H).app R g = SemidirectProduct.inl g :=
  (rfl)

/-- The inclusions of the loop groups into their semidirect products commute with the inclusions
`L⁺G → LG` and `L⁺G ⋊ Aut(O) → LG ⋊ Aut(O)`. -/
theorem positiveLoopToSemidirectProduct_comp_positiveLoopSemidirectProductToLoop :
    positiveLoopToSemidirectProduct.{u, v, w} k H ≫ positiveLoopSemidirectProductToLoop k H =
      positiveLoopToLoop k H ≫ loopToSemidirectProduct k H := by
  refine NatTrans.ext <| funext fun R ↦ GrpCat.ext fun x ↦ SemidirectProduct.ext ?_ rfl
  exact (HopfAlgebra.positiveLoopToLoop_app_apply k H R x).symm

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
