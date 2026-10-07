/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Chart
import TauCeti.LinearAlgebra.CrossProduct

/-!
# The Bosma–Lenstra addition morphism on `E ×_S E`

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model and let `S = Spec R`. The Bosma–Lenstra chart cover
`WeierstrassCurve.additionCover` of `E ×_S E` has pieces
`Spec (Localization.Away (chartPairLaw W i j k))`, on which the addition law selected by `k` has a
unit coordinate and defines a morphism `WeierstrassCurve.additionOnPiece W i j k` to `E`. This file
shows that these morphisms agree, as morphisms of schemes, on the overlaps of the pieces, and glues
them to the addition morphism `E ×_S E ⟶ E` over `S`.

## Main definitions

* `WeierstrassCurve.additionMorphism W`: the addition morphism `E ×_S E ⟶ E`.

## Main results

* `WeierstrassCurve.fst_additionOnPiece_eq_snd_additionOnPiece`: the addition morphisms on two
  pieces of the chart cover agree on their overlap.
* `WeierstrassCurve.SpecMap_chartPairι_additionMorphism`: on each piece of the chart cover, the
  addition morphism is `additionOnPiece`.
* `WeierstrassCurve.additionMorphism_projModelOver`: the addition morphism lies over `S`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`:
* from `AdditionChartOverlap.lean`: `pieceMorOfTriple_agree` and `pieceMorOfTriple_cross_agree`,
  within `fst_additionOnPiece_eq_snd_additionOnPiece`;
* from `AdditionChartGlue.lean`: `chartHomOfTriple_lawOne_eq_lawTwo`, within
  `fst_additionOnPiece_eq_snd_additionOnPiece`;
* from `AdditionChartGlobal.lean`: `addOn_agree` and `blCoverMor_agree`, within
  `fst_additionOnPiece_eq_snd_additionOnPiece`; `mulModelHom`, as `additionMorphism`;
  `blOpenZ_ι_mulModelHom` and `blOpenY_ι_mulModelHom`, as `SpecMap_chartPairι_additionMorphism`;
  and `mulModelHom_projModelπ`, as `additionMorphism_projModelOver`.

The source works over a Jacobson domain, on the four products of the `Y`- and `Z`-charts, whose
rings are then domains, and glues each law on the open where it is regular before gluing the two
laws. Here the base ring is arbitrary, all nine products of two charts are used, and the pieces of
both laws are glued in one step over the whole of `E ×_S E`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct Matrix
open Algebra.TensorProduct (includeLeftRingHom includeRight)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- If the `A`-points of two charts of `projModel W` given by `α` and `β` are equal, then the
-- images of the universal points differ by a unit.
private theorem exists_smul_of_SpecMap_chartι_eq {A : CommRingCat.{u}} {i i' : Fin 3}
    {α : CommRingCat.of (W.toProjective.ChartRing i) ⟶ A}
    {β : CommRingCat.of (W.toProjective.ChartRing i') ⟶ A}
    (h : Spec.map α ≫ W.chartι i = Spec.map β ≫ W.chartι i') :
    ∃ u : Aˣ, α.hom ∘ W.toProjective.chartPoint i = u • (β.hom ∘ W.toProjective.chartPoint i') := by
  rw [W.chartι_eq_projModelPoint i, W.chartι_eq_projModelPoint i', ← CommRingCat.ofHom_hom α,
    ← CommRingCat.ofHom_hom β, SpecMap_projModelPoint, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff] at h
  exact h.2

-- Pushed along `φ`, from the product `ChartRing i ⊗[R] ChartRing j` of two charts, the six law
-- coordinates are the two laws at the images of the universal points.
private theorem comp_chartPairLaw {A : CommRingCat.{u}} {i j : Fin 3}
    (φ : CommRingCat.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) ⟶ A) :
    φ.hom ∘ W.chartPairLaw i j = Sum.elim
      ((W.toProjective.map (CommRingCat.ofHom (algebraMap R _) ≫
          CommRingCat.ofHom includeLeftRingHom ≫ φ).hom).addXYZ
        ((CommRingCat.ofHom includeLeftRingHom ≫ φ).hom ∘ W.toProjective.chartPoint i)
        ((CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ).hom ∘
          W.toProjective.chartPoint j))
      ((W.toProjective.map (CommRingCat.ofHom (algebraMap R _) ≫
          CommRingCat.ofHom includeLeftRingHom ≫ φ).hom).dblAddXYZ
        ((CommRingCat.ofHom includeLeftRingHom ≫ φ).hom ∘ W.toProjective.chartPoint i)
        ((CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ).hom ∘
          W.toProjective.chartPoint j)) := by
  have hW : (W.toProjective.baseChange
      (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)).map φ.hom =
        W.toProjective.map (CommRingCat.ofHom (algebraMap R _) ≫
          CommRingCat.ofHom includeLeftRingHom ≫ φ).hom := by
    rw [Projective.map, Projective.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_map]
    congr 1
  -- both laws commute with `φ`, applied to the curve and to the points
  rw [← hW]
  ext (k | k)
  · exact (congrArg φ.hom (W.chartPairLaw_inl i j k)).trans
      (congrFun (Projective.map_addXYZ φ.hom _ _) k).symm
  · exact (congrArg φ.hom (W.chartPairLaw_inr i j k)).trans
      (congrFun (Projective.map_dblAddXYZ φ.hom _ _) k).symm

-- Pushed along `φ`, the two laws selected by `s` and `s'` have vanishing cross product.
private theorem cross_comp_chartPairLaw {A : CommRingCat.{u}} {i j : Fin 3}
    (φ : CommRingCat.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) ⟶ A)
    (s s' : Fin 3 ⊕ Fin 3) : (fun m ↦ φ.hom (W.chartPairLaw i j (s.map (fun _ ↦ m) (fun _ ↦ m)))) ⨯₃
      (fun m ↦ φ.hom (W.chartPairLaw i j (s'.map (fun _ ↦ m) (fun _ ↦ m)))) = 0 := by
  -- the images of the universal points solve the equation of `W` along `R → A`
  have hP := (W.toProjective.equation_chartPoint i).map
    (CommRingCat.ofHom includeLeftRingHom ≫ φ).hom
  have hQ : (W.toProjective.map (CommRingCat.ofHom (algebraMap R _) ≫
      CommRingCat.ofHom includeLeftRingHom ≫ φ).hom).Equation
        ((CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ).hom ∘
          W.toProjective.chartPoint j) := by
    have hc : CommRingCat.ofHom (algebraMap R (W.toProjective.ChartRing i)) ≫
        CommRingCat.ofHom includeLeftRingHom ≫ φ = CommRingCat.ofHom (algebraMap R _) ≫
          CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ :=
      congrArg (CommRingCat.ofHom · ≫ φ) Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    rw [hc]
    exact (W.toProjective.equation_chartPoint j).map _
  -- each law coordinate pushed along `φ` is the corresponding coordinate of a law at the images
  have h := congrFun (W.comp_chartPairLaw φ)
  simp only [Function.comp_apply] at h
  simp only [h]
  cases s <;> cases s' <;> simp only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  · exact cross_self _
  · exact Projective.addXYZ_cross_dblAddXYZ hP hQ
  · rw [← cross_anticomm]
    exact neg_eq_zero.mpr (Projective.addXYZ_cross_dblAddXYZ hP hQ)
  · exact cross_self _

-- If the images along `φ` and `ψ` of the universal points of two products of charts differ by
-- units `u` and `v`, over the same structure map from `R`, then the six law coordinates differ by
-- `(u v)²`.
private theorem comp_chartPairLaw_eq_smul {A : CommRingCat.{u}} {i j i' j' : Fin 3}
    {φ : CommRingCat.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) ⟶ A}
    {ψ : CommRingCat.of (W.toProjective.ChartRing i' ⊗[R] W.toProjective.ChartRing j') ⟶ A}
    {u v : Aˣ} (hg : CommRingCat.ofHom (algebraMap R _) ≫ CommRingCat.ofHom includeLeftRingHom ≫ φ =
      CommRingCat.ofHom (algebraMap R _) ≫ CommRingCat.ofHom includeLeftRingHom ≫ ψ)
    (hu : (CommRingCat.ofHom includeLeftRingHom ≫ φ).hom ∘ W.toProjective.chartPoint i =
      u • ((CommRingCat.ofHom includeLeftRingHom ≫ ψ).hom ∘ W.toProjective.chartPoint i'))
    (hv : (CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ).hom ∘
        W.toProjective.chartPoint j =
      v • ((CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ ψ).hom ∘
        W.toProjective.chartPoint j')) :
    φ.hom ∘ W.chartPairLaw i j = ((u * v : A) ^ 2) • (ψ.hom ∘ W.chartPairLaw i' j') := by
  rw [comp_chartPairLaw, comp_chartPairLaw, hg, hu, hv, Units.smul_def, Units.smul_def,
    Projective.addXYZ_smul, Projective.dblAddXYZ_smul]
  ext (m | m) <;> rfl

-- Along `φ`, the addition morphism on the piece indexed by `k` is the point whose homogeneous
-- coordinates are the image of the law selected by `k`.
private theorem exists_SpecMap_additionOnPiece {A : CommRingCat.{u}} {i j : Fin 3}
    (k : Fin 3 ⊕ Fin 3) (φ : CommRingCat.of (Localization.Away (W.chartPairLaw i j k)) ⟶ A) :
    ∃ hP hm, Spec.map φ ≫ W.additionOnPiece i j k =
      W.projModelPoint (CommRingCat.ofHom (algebraMap R _) ≫ φ).hom (i := k.elim id id)
        (P := fun m ↦ (CommRingCat.ofHom (algebraMap
          (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) _) ≫ φ).hom
            (W.chartPairLaw i j (k.map (fun _ ↦ m) (fun _ ↦ m)))) hP hm := by
  -- along `φ`, a point of `projModel W` over the localization is the point of the images
  have key {P : Fin 3 → Localization.Away (W.chartPairLaw i j k)} {hP} {m : Fin 3}
      (hm : IsUnit (P m)) : ∃ hP' hm', Spec.map φ ≫ W.projModelPoint (algebraMap R _) hP hm =
        W.projModelPoint (CommRingCat.ofHom (algebraMap R _) ≫ φ).hom (P := φ.hom ∘ P) hP' hm' :=
    ⟨_, _, SpecMap_projModelPoint φ.hom hm⟩
  cases k
  · rw [additionOnPiece_inl]
    exact key _
  · rw [additionOnPiece_inr]
    exact key _

-- The localization of the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)` away from a law coordinate
-- lies over `Spec R`, along its structure map.
private theorem SpecMap_chartPairι_fst_projModelOver (i j : Fin 3) (k : Fin 3 ⊕ Fin 3) :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (W.chartPairLaw i j k)))) ≫
      W.chartPairι i j ≫ pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (W.chartPairLaw i j k)))) := by
  rw [chartPairι_fst_assoc, chartι_projModelOver, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq R
      (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)
      (Localization.Away (W.chartPairLaw i j k))]

-- On `Spec A`, two points of pieces of the cover with the same image in `E ×_S E` have the same
-- image under the addition morphisms.
private theorem SpecMap_additionOnPiece_eq {A : CommRingCat.{u}} {i j i' j' : Fin 3}
    {k k' : Fin 3 ⊕ Fin 3} (φ : CommRingCat.of (Localization.Away (W.chartPairLaw i j k)) ⟶ A)
    (ψ : CommRingCat.of (Localization.Away (W.chartPairLaw i' j' k')) ⟶ A)
    (h : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ W.chartPairι i j =
      Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ W.chartPairι i' j') :
    Spec.map φ ≫ W.additionOnPiece i j k = Spec.map ψ ≫ W.additionOnPiece i' j' k' := by
  -- both points lie over the same morphism `Spec A ⟶ Spec R`
  have hg := congrArg (· ≫ pullback.fst _ _ ≫ W.projModelOver) h
  simp only [Category.assoc, SpecMap_chartPairι_fst_projModelOver, ← Spec.map_comp,
    Spec.map_inj] at hg
  -- their projections to `E` are the images `P = u • P'` and `Q = v • Q'` of the universal points
  have h₁ := congrArg (· ≫ pullback.fst _ _) h
  have h₂ := congrArg (· ≫ pullback.snd _ _) h
  simp only [Category.assoc, chartPairι_fst, chartPairι_snd, ← Spec.map_comp_assoc] at h₁ h₂
  obtain ⟨u, hu⟩ := W.exists_smul_of_SpecMap_chartι_eq h₁
  obtain ⟨v, hv⟩ := W.exists_smul_of_SpecMap_chartι_eq h₂
  -- read through the first charts, both points lie over the same morphism `Spec A ⟶ Spec R`
  have hgi := congrArg (· ≫ W.projModelOver) h₁
  simp only [Category.assoc, chartι_projModelOver, ← Spec.map_comp, Spec.map_inj] at hgi
  -- hence the six law coordinates on the two pieces are proportional, by `(u v)²`
  have hF := W.comp_chartPairLaw_eq_smul hgi hu hv
  -- so the two laws selected by `k` and `k'` are unit multiples of each other
  obtain ⟨hT, hm, e⟩ := W.exists_SpecMap_additionOnPiece k φ
  obtain ⟨hT', hm', e'⟩ := W.exists_SpecMap_additionOnPiece k' ψ
  rw [e, e', projModelPoint_eq_projModelPoint_iff]
  refine ⟨congrArg CommRingCat.Hom.hom hg,
    TauCeti.exists_eq_units_smul_of_crossProduct_eq_zero ?_ hm hm'⟩
  -- the law selected by `k` along `φ` is `(u v)²` times the one along `ψ`, and along `ψ` the
  -- laws selected by `k` and `k'` have vanishing cross product
  calc _ = ((u * v : A) ^ 2 • _) ⨯₃ _ := congrArg (· ⨯₃ _) (funext fun m ↦ congrFun hF _)
    _ = (u * v : A) ^ 2 • 0 := by
      rw [map_smul, LinearMap.smul_apply]
      exact congrArg ((u * v : A) ^ 2 • ·) (cross_comp_chartPairLaw W _ k k')
    _ = 0 := smul_zero _

/-- The Bosma–Lenstra addition morphisms on the pieces of the chart cover `additionCover W` of
`E ×_S E` agree on overlaps: for any two pieces `a` and `b`, the composites of `additionOnPiece`
on `a` and on `b` with the two projections from the fibre product of the pieces over `E ×_S E`
are equal. This is the compatibility condition of `Scheme.Cover.glueMorphisms`. -/
theorem fst_additionOnPiece_eq_snd_additionOnPiece [W.IsElliptic] (a b : W.additionCover.I₀) :
    pullback.fst (W.additionCover.f a) (W.additionCover.f b) ≫ W.additionOnPiece a.1.1 a.1.2 a.2 =
      pullback.snd (W.additionCover.f a) (W.additionCover.f b) ≫
        W.additionOnPiece b.1.1 b.1.2 b.2 := by
  -- check on the affine open cover of the overlap, whose maps to the two pieces are `Spec` maps
  let 𝒱 := (pullback (W.additionCover.f a) (W.additionCover.f b)).affineCover
  refine 𝒱.hom_ext _ _ fun x ↦ ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱.f x ≫ pullback.fst _ _)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (𝒱.f x ≫ pullback.snd _ _)
  have h := W.SpecMap_additionOnPiece_eq φ ψ ?_
  · rw [hφ, hψ] at h
    exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
  · rw [hφ, hψ]
    exact (Category.assoc _ _ _).trans
      ((congrArg (𝒱.f x ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

/-- The **Bosma–Lenstra addition morphism** `E ×_S E ⟶ E` of an elliptic Weierstrass curve `W`
over `R`, for `E = projModel W` and `S = Spec R`: the morphism whose restriction to each piece of
the chart cover `additionCover W` is the addition morphism `additionOnPiece` on that piece
(`SpecMap_chartPairι_additionMorphism`). It lies over `S` (`additionMorphism_projModelOver`). -/
noncomputable def additionMorphism [W.IsElliptic] : pullback W.projModelOver W.projModelOver ⟶
    W.projModel :=
  W.additionCover.openCover.glueMorphisms (fun a ↦ W.additionOnPiece a.1.1 a.1.2 a.2)
    W.fst_additionOnPiece_eq_snd_additionOnPiece

/-- On the piece `Spec (Localization.Away (chartPairLaw W i j k))` of the chart cover
`additionCover W`, the addition morphism `E ×_S E ⟶ E` is the addition morphism
`additionOnPiece W i j k` of that piece. -/
@[reassoc (attr := simp)]
theorem SpecMap_chartPairι_additionMorphism [W.IsElliptic] (i j : Fin 3) (k : Fin 3 ⊕ Fin 3) :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (W.chartPairLaw i j k)))) ≫
      W.chartPairι i j ≫ W.additionMorphism = W.additionOnPiece i j k :=
  (Category.assoc _ _ _).symm.trans (W.additionCover.openCover.ι_glueMorphisms _ _ ((i, j), k))

/-- The addition morphism `E ×_S E ⟶ E` lies over `S = Spec R`: its composite with the structure
morphism of `E` is the structure morphism of `E ×_S E`. -/
@[reassoc (attr := simp)]
theorem additionMorphism_projModelOver [W.IsElliptic] : W.additionMorphism ≫ W.projModelOver =
    pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver :=
  -- on each piece, both sides are `Spec` of the structure map of the localization
  W.additionCover.openCover.hom_ext _ _ fun _ ↦
    (((Category.assoc _ _ _).trans (W.SpecMap_chartPairι_additionMorphism_assoc _ _ _ _)).trans
      (W.additionOnPiece_projModelOver _ _ _)).trans
        ((Category.assoc _ _ _).trans (W.SpecMap_chartPairι_fst_projModelOver _ _ _)).symm

end WeierstrassCurve
