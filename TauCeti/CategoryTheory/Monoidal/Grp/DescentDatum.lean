/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.DescentDatum
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Descent data on monoid and group objects

Let `p : S' ⟶ S` be a morphism in a category `C` with pullbacks. Using the terminal descent datum
`DescentDatum.unit p` and binary product `D₁.prod D₂` defined in
`TauCeti.CategoryTheory.Monoidal.Cartesian.DescentDatum`, a descent datum `D` on a monoid object `X`
in `Over S'` is compatible with the monoid structure (`DescentDatum.IsMon D`) when the unit
`η[X] : 𝟙_ (Over S') ⟶ X` and multiplication `μ[X] : X ⊗ X ⟶ X` intertwine the actions of `unit p`,
`D.prod D`, and `D`. When `X` is a group object, compatibility with the monoid structure
automatically implies that inversion `ι[X] : X ⟶ X` is a morphism of descent data
(`DescentDatum.invHom`), by uniqueness of inverses in the group of morphisms into `X` in `Over S'`.

Canonical base-change descent data on monoid objects satisfy `IsMon` (`baseChange_isMon`), and
`IsMon` transfers across monoid isomorphisms of descent data (`Hom.isMon_iff`) and restricts along
monomorphic monoid homomorphisms (`Hom.isMon_of_mono`).

## Main definitions

* `TauCeti.DescentDatum.IsMon`: compatibility of a descent datum with a `MonObj` structure on its
  carrier, bundling `oneHom` and `mulHom`, and `invHom` when the carrier is a `GrpObj`.

## Main statements

* `TauCeti.DescentDatum.IsMon.inv_act`: automatic equivariance of group inversion.
* `TauCeti.DescentDatum.baseChange_isMon`: canonical base-change descent data satisfy `IsMon`.
* `TauCeti.DescentDatum.Hom.isMon_of_mono`, `TauCeti.DescentDatum.Hom.isMon_iff`: restriction and
  invariance of `IsMon` along monomorphic and isomorphic monoid homomorphisms.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* M. Demazure and A. Grothendieck, *Schémas en groupes* (SGA 3), Exposé I, §2.
-/

public section

namespace TauCeti.DescentDatum

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C}

section IsMon

variable {p : S' ⟶ S}

/-- Compatibility of a descent datum `D` on a monoid object `X` in `Over S'` with the monoid
structure: the unit `η[X]` and multiplication `μ[X]` intertwine the actions of `unit p`,
`D.prod D`, and `D`. When `X` is a group object, inversion is automatically compatible as well
(`invHom`). -/
class IsMon {X : Over S'} [MonObj X] (D : DescentDatum p X) : Prop where
  /-- The unit `η[X] : 𝟙_ (Over S') ⟶ X` intertwines `unit p` and `D`. -/
  one_act :
    pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (X.hom ≫ p) (𝟙 S') η[X].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      (unit p).act ≫ η[X].left
  /-- The multiplication `μ[X] : X ⊗ X ⟶ X` intertwines `D.prod D` and `D`. -/
  mul_act :
    pullback.map p ((X ⊗ X).hom ≫ p) p (X.hom ≫ p) (𝟙 S') μ[X].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      (D.prod D).act ≫ μ[X].left

attribute [reassoc] IsMon.one_act IsMon.mul_act

/-- The unit `η[X]` of a monoid object with a compatible descent datum `D`, bundled as a morphism
of descent data `unit p ⟶ D`. -/
noncomputable def oneHom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    Hom (unit p) D where
  hom := η[X]
  map_act := IsMon.one_act

/-- The underlying morphism of `oneHom D` is `η[X]`. -/
@[simp]
theorem oneHom_hom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    (oneHom D).hom = η[X] :=
  (rfl)

/-- The multiplication `μ[X]` of a monoid object with a compatible descent datum `D`, bundled as a
morphism of descent data `D.prod D ⟶ D`. -/
noncomputable def mulHom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    Hom (D.prod D) D where
  hom := μ[X]
  map_act := IsMon.mul_act

/-- The underlying morphism of `mulHom D` is `μ[X]`. -/
@[simp]
theorem mulHom_hom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    (mulHom D).hom = μ[X] :=
  (rfl)

/-- **Automatic equivariance of inversion.** If `D` is a monoid-compatible descent datum on a
group object `G` in `Over S'`, then the inversion `ι[G] : G ⟶ G` commutes with `D.act`
(informally, `s · g⁻¹ = (s · g)⁻¹`). -/
@[reassoc]
theorem IsMon.inv_act {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    pullback.map p (G.hom ≫ p) p (G.hom ≫ p) (𝟙 S') ι[G].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      D.act ≫ ι[G].left := by
  -- In the group of morphisms `A ⟶ G` in `Over S'` under pointwise multiplication, the morphism
  -- `β` representing `(s, g) ↦ s · g⁻¹` satisfies `α * β = 1` for `α` representing `D.act`,
  -- because `D` preserves multiplication and the identity; hence `β = α⁻¹`.
  let A : Over S' := Over.mk (pullback.fst p (G.hom ≫ p))
  let α : A ⟶ G := Over.homMk D.act (by simp [A])
  let β : A ⟶ G := Over.homMk
    (pullback.map p (G.hom ≫ p) p (G.hom ≫ p) (𝟙 S') ι[G].left (𝟙 S)
      (by simp) (by simp) ≫ D.act) (by simp [A])
  suffices h : β = α⁻¹ by
    simpa [α, β, Hom.inv_def] using congrArg CommaMorphism.left h
  refine (mul_eq_one_iff_inv_eq.mp ?_).symm
  rw [Hom.mul_def, Hom.one_def]
  ext1
  -- Express `(α * β).left` via `(D.prod D).act ≫ μ[G].left` applied to `(g, g⁻¹)`.
  let δ : A.left ⟶ pullback p ((G ⊗ G).hom ≫ p) :=
    pullback.map p (G.hom ≫ p) p ((G ⊗ G).hom ≫ p) (𝟙 S')
      (CartesianMonoidalCategory.lift (𝟙 G) ι[G]).left (𝟙 S) (by simp) (by simp)
  have hlift : (CartesianMonoidalCategory.lift α β).left = δ ≫ (D.prod D).act := by
    refine Over.tensorObj_ext _ _ ?_ ?_
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, prod_act_pullback_fst,
        α, Over.homMk_left]
      refine Eq.trans (Category.id_comp D.act).symm
        (Eq.trans (congrArg (· ≫ D.act) ?_) (Category.assoc _ _ _))
      refine pullback.hom_ext ?_ ?_ <;> simp [δ]
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, prod_act_pullback_snd,
        β, Over.homMk_left]
      refine Eq.trans (congrArg (· ≫ D.act) ?_) (Category.assoc _ _ _)
      refine pullback.hom_ext ?_ ?_ <;> simp [δ]
  have hmap_mul : δ ≫ pullback.map p ((G ⊗ G).hom ≫ p) p (G.hom ≫ p) (𝟙 S') μ[G].left (𝟙 S)
      (by simp) (by simp) =
      pullback.map p (G.hom ≫ p) p ((𝟙_ (Over S')).hom ≫ p) (𝟙 S') (toUnit G).left (𝟙 S)
        (by simp) (by simp) ≫
        pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (G.hom ≫ p) (𝟙 S') η[G].left (𝟙 S)
          (by simp) (by simp) := by
    have hinv : pullback.lift (𝟙 G.left) ι[G].left (by simp) ≫ μ[G].left =
        G.hom ≫ η[G].left := by
      have h := congrArg Over.Hom.left (GrpObj.right_inv G)
      simpa only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] using h
    refine pullback.hom_ext ?_ ?_
    · simp [δ]
    · simp [δ, hinv]
  simp only [Over.comp_left, hlift, Category.assoc, ← IsMon.mul_act, reassoc_of% hmap_mul,
    IsMon.one_act]
  simp [A]

/-- The inversion `ι[G]` of a group object with a monoid-compatible descent datum `D`, bundled as a
morphism of descent data `D ⟶ D`. -/
noncomputable def invHom {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    Hom D D where
  hom := ι[G]
  map_act := IsMon.inv_act D

/-- The underlying morphism of `invHom D` is `ι[G]`. -/
@[simp]
theorem invHom_hom {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    (invHom D).hom = ι[G] :=
  (rfl)

/-- The canonical descent datum on the base change of a monoid object over `S` is compatible with
its base-changed monoid structure. -/
instance baseChange_isMon (p : S' ⟶ S) (X₀ : Over S) [MonObj X₀] :
    (baseChange p X₀).IsMon where
  one_act := by
    let φ := (baseChangeHom p η[X₀]).comp (baseChangeUnitHom p).inv
    have hφ : φ.hom = η[(Over.pullback p).obj X₀] := by simp [φ, Functor.obj.η_def]
    simpa only [hφ] using φ.map_act
  mul_act := by
    let ψ := (baseChangeHom p μ[X₀]).comp (baseChangeProdHom p X₀ X₀).inv
    have hψ : ψ.hom = μ[(Over.pullback p).obj X₀] := by simp [ψ, Functor.obj.μ_def]
    simpa only [hψ] using ψ.map_act

/-- **Restriction of `IsMon` along a monomorphic homomorphism.** If `f : D ⟶ E` is a morphism of
descent data whose underlying morphism `f.hom : X ⟶ Y` is a monoid homomorphism with monic
underlying map in `C`, and `E` is compatible with the monoid structure on `Y`, then `D` is
compatible with the monoid structure on `X`. -/
theorem Hom.isMon_of_mono {X Y : Over S'} [MonObj X] [MonObj Y]
    {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [Mono f.hom.left] [IsMonHom f.hom] [E.IsMon] : D.IsMon where
  one_act := by
    let φ := Hom.mkOfCompMono η[X] f (oneHom E) (by simp)
    have hφ : φ.hom = η[X] := Hom.mkOfCompMono_hom _ _ _ _
    simpa only [hφ] using φ.map_act
  mul_act := by
    let ψ := Hom.mkOfCompMono μ[X] f ((mulHom E).comp (f.prodMap f)) (by simp)
    have hψ : ψ.hom = μ[X] := Hom.mkOfCompMono_hom _ _ _ _
    simpa only [hψ] using ψ.map_act

/-- If `f : D ⟶ E` is an isomorphism of descent data whose underlying morphism in `Over S'` is a
monoid isomorphism, then `D` is compatible with the monoid structure if and only if `E` is. -/
theorem Hom.isMon_iff {X Y : Over S'} [MonObj X] [MonObj Y]
    {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [IsIso f.hom] [IsMonHom f.hom] : D.IsMon ↔ E.IsMon := by
  have : IsMonHom f.inv.hom := by
    have : IsMonHom (asIso f.hom).hom := ‹_›
    simpa [Hom.inv_hom] using (inferInstance : IsMonHom (asIso f.hom).inv)
  exact ⟨fun _ ↦ f.inv.isMon_of_mono, fun _ ↦ f.isMon_of_mono⟩

end IsMon

end TauCeti.DescentDatum
