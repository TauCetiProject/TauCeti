/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.CategoryTheory.CommSq
public import TauCeti.Topology.Algebra.PointTopology.FiberProduct
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality

/-!
# Scheme-valued points of fibre products

Let `X ⟶ Z ⟵ Y` be morphisms of schemes over `Spec k`, and let `P` with projections
`p₁ : P ⟶ X` and `p₂ : P ⟶ Y` be a fibre product, given as an `IsPullback` square. The universal
property identifies the `R`-points of `P` with the pairs of `R`-points of `X` and `Y` having the
same image in `Z`, through the two projections
(`TauCeti.SchemePointTopology.pointsEquivOfIsPullback`). Over a local topological ring with open
units and continuous inversion on the units, this bijection is a homeomorphism onto the subspace
of compatible pairs (`TauCeti.SchemePointTopology.pointsHomeomorphOfIsPullback`): the point functor
preserves fibre products. No finiteness or separation assumptions are needed. The chosen fibre
product `pullback g₁ g₂` is the special case `TauCeti.SchemePointTopology.pullbackPointsHomeomorph`,
and a fibre product over the base itself has the product of the point spaces as its points
(`TauCeti.SchemePointTopology.pointsProdEquivOfIsPullback`, and as a homeomorphism
`TauCeti.SchemePointTopology.pointsProdHomeomorphOfIsPullback`).

Affine charts `Spec A ⟶ X` and `Spec B ⟶ Y` over an affine chart `Spec C ⟶ Z` give an affine
chart `Spec (A ⊗[C] B) ⟶ P` (`TauCeti.AlgebraicGeometry.tensorProductChart`), on whose points
the inverse comparison is the affine comparison
`TauCeti.PointTopology.relativeTensorProductHomeomorph`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 2.1 and Prop. 3.1 and
  their proofs, pp. 2–4.
* A. Grothendieck, M. Raynaud, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII,
  §1.1, p. 239.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology TensorProduct
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology
open TauCeti.AlgebraicGeometry (tensorProductChart tensorProductChart_fst tensorProductChart_snd
  tensorProductChart_fst_assoc tensorProductChart_snd_assoc)

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X Y Z P : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
  {fZ : Z ⟶ Spec (.of k)} {fP : P ⟶ Spec (.of k)} {g₁ : X ⟶ Z} {g₂ : Y ⟶ Z}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y}

section FibreProduct

variable (hP : IsPullback p₁ p₂ g₁ g₂) (hp₁ : p₁ ≫ fX = fP) (hg₁ : g₁ ≫ fZ = fX)
  (hg₂ : g₂ ≫ fZ = fY)

/-- **Points of a fibre product.** The `R`-points of a fibre product `P` of `X ⟶ Z ⟵ Y` are the
pairs of `R`-points of `X` and `Y` with the same image in `Z`, through the two projections. -/
noncomputable def pointsEquivOfIsPullback :
    Points (R := R) fP ≃
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} where
  toFun x := ⟨(map p₁ hp₁ x, map p₂ (hP.toCommSq.snd_comp_eq_of_fst_comp_eq hg₁ hg₂ hp₁) x),
    Subtype.ext (by simp [hP.w])⟩
  invFun p := ⟨hP.lift p.1.1.val p.1.2.val (by simpa using congrArg Subtype.val p.2), by
    rw [← hp₁, IsPullback.lift_fst_assoc, p.1.1.property]⟩
  left_inv x := Subtype.ext (hP.hom_ext (by simp) (by simp))
  right_inv p := Subtype.ext (Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)))

/-- The fibre-product comparison sends a point to its two projections. -/
@[simp]
theorem pointsEquivOfIsPullback_apply_coe (x : Points (R := R) fP) :
    (pointsEquivOfIsPullback hP hp₁ hg₁ hg₂ x).1 =
      (map p₁ hp₁ x, map p₂ (hP.toCommSq.snd_comp_eq_of_fst_comp_eq hg₁ hg₂ hp₁) x) :=
  (rfl)

/-- The inverse fibre-product comparison is the morphism into the fibre product given by the
universal property. -/
@[simp]
theorem pointsEquivOfIsPullback_symm_apply_val
    (p : {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2}) :
    ((pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm p).val =
      hP.lift p.1.1.val p.1.2.val (by simpa using congrArg Subtype.val p.2) :=
  (rfl)

/-- The first projection of the inverse fibre-product comparison is the first point of the
pair. -/
@[simp]
theorem map_fst_pointsEquivOfIsPullback_symm
    (p : {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2}) :
    map p₁ hp₁ ((pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm p) = p.1.1 :=
  Subtype.ext (by simp)

/-- The second projection of the inverse fibre-product comparison is the second point of the
pair. -/
@[simp]
theorem map_snd_pointsEquivOfIsPullback_symm (h : p₂ ≫ fY = fP)
    (p : {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2}) :
    map p₂ h ((pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm p) = p.1.2 :=
  Subtype.ext (by simp)

include hP hp₁ hg₁ hg₂ in
/-- The points of a fibre product, sent to their two projections, are exactly the pairs of points
with the same image in `Z`. -/
theorem range_prodMk_map_of_isPullback (hp₂ : p₂ ≫ fY = fP) :
    Set.range (fun x : Points (R := R) fP ↦ (map p₁ hp₁ x, map p₂ hp₂ x)) =
      {p | map g₁ hg₁ p.1 = map g₂ hg₂ p.2} := by
  ext p
  refine ⟨?_, fun hp ↦ ⟨(pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm ⟨p, hp⟩, by simp⟩⟩
  rintro ⟨x, rfl⟩
  exact (pointsEquivOfIsPullback hP hp₁ hg₁ hg₂ x).2

section TensorProductChart

variable {A B C : CommAlgCat.{u} k} [Algebra C A] [Algebra C B]
  {iA : Spec (.of A) ⟶ X} {iB : Spec (.of B) ⟶ Y} {iC : Spec (.of C) ⟶ Z}
  (hA : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ iC = iA ≫ g₁)
  (hB : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ iC = iB ≫ g₂)

variable [IsScalarTower k C A]

include hp₁ in
/-- The tensor-product chart is a morphism over the base. -/
theorem tensorProductChart_comp (hiA : iA ≫ fX = Spec.algebraMap k A) :
    tensorProductChart hP hA hB ≫ fP = Spec.algebraMap k (CommAlgCat.of k (A ⊗[C] B)) := by
  rw [← hp₁, tensorProductChart_fst_assoc, hiA, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Algebra.TensorProduct.algebraMap_def]

variable [IsScalarTower k C B]

/-- On the tensor-product chart, the fibre-product comparison sends a point to the chart points
of its restrictions to the two factors. -/
theorem pointsEquivOfIsPullback_chartPoint (hiA : iA ≫ fX = Spec.algebraMap k A)
    (hiB : iB ≫ fY = Spec.algebraMap k B) (x : CommAlgCat.of k (A ⊗[C] B) →ₐ[k] R) :
    (pointsEquivOfIsPullback hP hp₁ hg₁ hg₂ (chartPoint fP (CommAlgCat.of k (A ⊗[C] B))
        (tensorProductChart hP hA hB) (tensorProductChart_comp hP hp₁ hA hB hiA) x)).1 =
      (chartPoint fX A iA hiA (x.comp Algebra.TensorProduct.includeLeft),
        chartPoint fY B iB hiB
          (x.comp (Algebra.TensorProduct.includeRight.restrictScalars k))) := by
  ext1 <;> apply Subtype.ext <;>
    simp only [pointsEquivOfIsPullback_apply_coe, map_val, chartPoint_val, Category.assoc,
      tensorProductChart_fst, tensorProductChart_snd, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp] <;>
    congr 2

include hA hB in
/-- Two chart points of `X` and `Y` over a monomorphic chart of `Z` have the same image in `Z`
exactly when the two algebra maps agree on `C`. -/
theorem map_chartPoint_eq_map_chartPoint_iff (hiA : iA ≫ fX = Spec.algebraMap k A)
    (hiB : iB ≫ fY = Spec.algebraMap k B) (hiC : iC ≫ fZ = Spec.algebraMap k C) [Mono iC]
    (a : A →ₐ[k] R) (b : B →ₐ[k] R) :
    map g₁ hg₁ (chartPoint fX A iA hiA a) = map g₂ hg₂ (chartPoint fY B iB hiB b) ↔
      a.comp (IsScalarTower.toAlgHom k C A) = b.comp (IsScalarTower.toAlgHom k C B) := by
  have hA' : Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom k C A).toRingHom) ≫ iC =
      iA ≫ g₁ := by
    rwa [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]
  have hB' : Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom k C B).toRingHom) ≫ iC =
      iB ≫ g₂ := by
    rwa [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]
  rw [map_chartPoint, map_chartPoint]
  simp only [← hA', ← hB']
  rw [chartPoint_spec_map_comp fZ iC hiC, chartPoint_spec_map_comp fZ iC hiC]
  exact (chartPoint_injective fZ C iC hiC).eq_iff

/-- On compatible pairs of chart points, the inverse fibre-product comparison is the
tensor-product chart applied to the lift of the two algebra maps to `A ⊗[C] B`. -/
theorem pointsEquivOfIsPullback_symm_chartPoint (hiA : iA ≫ fX = Spec.algebraMap k A)
    (hiB : iB ≫ fY = Spec.algebraMap k B) (hiC : iC ≫ fZ = Spec.algebraMap k C) [Mono iC]
    (a : A →ₐ[k] R) (b : B →ₐ[k] R)
    (h : map g₁ hg₁ (chartPoint fX A iA hiA a) = map g₂ hg₂ (chartPoint fY B iB hiB b)) :
    (pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm
        ⟨(chartPoint fX A iA hiA a, chartPoint fY B iB hiB b), h⟩ =
      chartPoint fP (CommAlgCat.of k (A ⊗[C] B)) (tensorProductChart hP hA hB)
        (tensorProductChart_comp hP hp₁ hA hB hiA) (a.tensorProductLift b
          ((map_chartPoint_eq_map_chartPoint_iff hg₁ hg₂ hA hB hiA hiB hiC a b).1 h)) := by
  apply Subtype.ext
  simp only [pointsEquivOfIsPullback_symm_apply_val, chartPoint_val]
  refine hP.hom_ext ?_ ?_ <;>
    simp only [IsPullback.lift_fst, IsPullback.lift_snd, Category.assoc, tensorProductChart_fst,
      tensorProductChart_snd, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp] <;>
    congr 2 <;> ext <;> simp

end TensorProductChart

section Topology

variable [TopologicalSpace R] [IsLocalRing R] [IsOpenUnits R]

/-- Over a local ring with a topology having continuous multiplication, open units and continuous
inversion on the units, the fibre-product comparison of points is continuous. -/
@[continuity, fun_prop]
theorem continuous_pointsEquivOfIsPullback [ContinuousMul R] :
    Continuous (pointsEquivOfIsPullback (R := R) hP hp₁ hg₁ hg₂) :=
  ((continuous_map _ _).prodMk (continuous_map _ _)).subtype_mk _

variable [IsTopologicalRing R]

/-- Over a local topological ring with open units and continuous inversion on the units, the
inverse fibre-product comparison of points is continuous. -/
@[continuity, fun_prop]
theorem continuous_pointsEquivOfIsPullback_symm :
    Continuous (pointsEquivOfIsPullback (R := R) hP hp₁ hg₁ hg₂).symm := by
  refine continuous_iff_continuousAt.2 fun ⟨⟨x, y⟩, hxy⟩ ↦ ?_
  -- Affine charts `Spec A ⟶ X` and `Spec B ⟶ Y` over an affine chart `Spec C ⟶ Z`.
  obtain ⟨C, iC, hiC, _, hz⟩ := exists_mem_range_chartPoint fZ (map g₁ hg₁ x)
  obtain ⟨A, iA, hiA, _, φA, hφA, a, rfl⟩ := exists_chartPoint_over g₁ hg₁ C iC hiC x hz
  obtain ⟨B, iB, hiB, _, φB, hφB, b, rfl⟩ :=
    exists_chartPoint_over g₂ hg₂ C iC hiC y (hxy ▸ hz)
  let : Algebra C A := φA.toAlgebra
  let : Algebra C B := φB.toAlgebra
  have : IsScalarTower k C A := .of_algebraMap_eq fun r ↦ (φA.commutes r).symm
  have : IsScalarTower k C B := .of_algebraMap_eq fun r ↦ (φB.commutes r).symm
  have hA : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ iC = iA ≫ g₁ := by
    rwa [RingHom.algebraMap_toAlgebra]
  have hB : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ iC = iB ≫ g₂ := by
    rwa [RingHom.algebraMap_toAlgebra]
  let S : Set (Points (R := R) fX × Points (R := R) fY) := {p | map g₁ hg₁ p.1 = map g₂ hg₂ p.2}
  let c := Prod.map (chartPoint (R := R) fX A iA hiA) (chartPoint (R := R) fY B iB hiB)
  have hc : IsOpenEmbedding (S.restrictPreimage c) :=
    ((isOpenEmbedding_chartPoint fX A iA hiA).prodMap
      (isOpenEmbedding_chartPoint fY B iB hiB)).restrictPreimage S
  have hcompat := map_chartPoint_eq_map_chartPoint_iff (R := R) hg₁ hg₂ hA hB hiA hiB hiC
  let τ : c ⁻¹' S → {q : (A →ₐ[k] R) × (B →ₐ[k] R) //
      q.1.comp (IsScalarTower.toAlgHom k C A) = q.2.comp (IsScalarTower.toAlgHom k C B)} :=
    fun q ↦ ⟨q.1, (hcompat q.1.1 q.1.2).1 q.2⟩
  have hτ : Continuous τ := continuous_subtype_val.subtype_mk _
  -- On compatible pairs of chart points, the inverse comparison is read in the chart.
  have key : (pointsEquivOfIsPullback (R := R) hP hp₁ hg₁ hg₂).symm ∘ S.restrictPreimage c =
      chartPoint fP (CommAlgCat.of k (A ⊗[C] B)) (tensorProductChart hP hA hB)
          (tensorProductChart_comp hP hp₁ hA hB hiA) ∘
        ⇑(PointTopology.relativeTensorProductHomeomorph k C A B R).symm ∘ τ := by
    funext ⟨⟨a', b'⟩, hq⟩
    simp only [Function.comp_apply, Set.restrictPreimage_mk, c, Prod.map_apply]
    rw [pointsEquivOfIsPullback_symm_chartPoint hP hp₁ hg₁ hg₂ hA hB hiA hiB hiC]
    congr 1
    refine ((PointTopology.relativeTensorProductHomeomorph k C A B R).eq_symm_apply).2 ?_
    ext <;> simp [τ]
  have hmem : S.restrictPreimage c ⟨(a, b), hxy⟩ =
      ⟨(chartPoint fX A iA hiA a, chartPoint fY B iB hiB b), hxy⟩ := by
    simp [c]
  rw [← hmem, ← hc.continuousAt_iff, key]
  exact ((continuous_chartPoint _ _ _ _).comp
    ((PointTopology.relativeTensorProductHomeomorph k C A B R).symm.continuous.comp
      hτ)).continuousAt

/-- **The point functor preserves fibre products.** Over a local topological ring with open units
and continuous inversion on the units, the `R`-points of a fibre product `P` of `X ⟶ Z ⟵ Y` are
homeomorphic, through the two projections, to the subspace of pairs of `R`-points of `X` and `Y`
with the same image in `Z`. -/
noncomputable def pointsHomeomorphOfIsPullback :
    Points (R := R) fP ≃ₜ
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} where
  toEquiv := pointsEquivOfIsPullback hP hp₁ hg₁ hg₂
  continuous_toFun := continuous_pointsEquivOfIsPullback hP hp₁ hg₁ hg₂
  continuous_invFun := continuous_pointsEquivOfIsPullback_symm hP hp₁ hg₁ hg₂

/-- The fibre-product homeomorphism has the fibre-product comparison of points as its underlying
equivalence. -/
@[simp]
theorem pointsHomeomorphOfIsPullback_toEquiv :
    (pointsHomeomorphOfIsPullback (R := R) hP hp₁ hg₁ hg₂).toEquiv =
      pointsEquivOfIsPullback hP hp₁ hg₁ hg₂ :=
  (rfl)

/-- The fibre-product homeomorphism is the fibre-product comparison of points. -/
@[simp]
theorem coe_pointsHomeomorphOfIsPullback :
    ⇑(pointsHomeomorphOfIsPullback (R := R) hP hp₁ hg₁ hg₂) =
      pointsEquivOfIsPullback hP hp₁ hg₁ hg₂ :=
  (rfl)

/-- The inverse fibre-product homeomorphism is the inverse fibre-product comparison of points. -/
@[simp]
theorem coe_pointsHomeomorphOfIsPullback_symm :
    ⇑(pointsHomeomorphOfIsPullback (R := R) hP hp₁ hg₁ hg₂).symm =
      (pointsEquivOfIsPullback hP hp₁ hg₁ hg₂).symm :=
  (rfl)

include hP hg₁ hg₂ in
/-- Over a local topological ring with open units and continuous inversion on the units, the two
projections embed the points of a fibre product in the product of the point spaces. -/
theorem isEmbedding_prodMk_map_of_isPullback (hp₂ : p₂ ≫ fY = fP) :
    IsEmbedding fun x : Points (R := R) fP ↦ (map p₁ hp₁ x, map p₂ hp₂ x) :=
  IsEmbedding.subtypeVal.comp (pointsHomeomorphOfIsPullback hP hp₁ hg₁ hg₂).isEmbedding

include hP hg₁ hg₂ in
/-- If the points of `Z` form a Hausdorff space, the projections embed the points of a fibre
product as a closed subspace of the product of the point spaces. -/
theorem isClosedEmbedding_prodMk_map_of_isPullback [T2Space (Points (R := R) fZ)]
    (hp₂ : p₂ ≫ fY = fP) :
    IsClosedEmbedding fun x : Points (R := R) fP ↦ (map p₁ hp₁ x, map p₂ hp₂ x) := by
  refine ⟨isEmbedding_prodMk_map_of_isPullback hP hp₁ hg₁ hg₂ hp₂, ?_⟩
  rw [range_prodMk_map_of_isPullback hP hp₁ hg₁ hg₂]
  exact isClosed_eq ((continuous_map _ _).comp continuous_fst)
    ((continuous_map _ _).comp continuous_snd)

end Topology

section Pullback

variable (g₁ g₂)

/-- **Points of the fibre product.** The `R`-points of `pullback g₁ g₂` are the pairs of
`R`-points of `X` and `Y` with the same image in `Z`, through the two projections. -/
noncomputable abbrev pullbackPointsEquiv :
    Points (R := R) (pullback.fst g₁ g₂ ≫ fX) ≃
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} :=
  pointsEquivOfIsPullback (.of_hasPullback g₁ g₂) rfl hg₁ hg₂

variable [TopologicalSpace R] [IsLocalRing R] [IsOpenUnits R] [IsTopologicalRing R]

/-- Over a local topological ring with open units and continuous inversion on the units, the
`R`-points of `pullback g₁ g₂` are homeomorphic, through the two projections, to the subspace of
pairs of `R`-points of `X` and `Y` with the same image in `Z`. -/
noncomputable abbrev pullbackPointsHomeomorph :
    Points (R := R) (pullback.fst g₁ g₂ ≫ fX) ≃ₜ
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} :=
  pointsHomeomorphOfIsPullback (.of_hasPullback g₁ g₂) rfl hg₁ hg₂

end Pullback

end FibreProduct

section Prod

variable (hXY : IsPullback p₁ p₂ fX fY) (hp₁ : p₁ ≫ fX = fP)

/-- **Points of a product.** The `R`-points of a fibre product `P` of `X` and `Y` over `Spec k` are
the pairs of `R`-points of `X` and `Y`, through the two projections. -/
noncomputable def pointsProdEquivOfIsPullback :
    Points (R := R) fP ≃ Points (R := R) fX × Points (R := R) fY :=
  (pointsEquivOfIsPullback hXY hp₁ (Category.comp_id fX) (Category.comp_id fY)).trans
    (Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _)

/-- The product comparison sends a point to its two projections. -/
@[simp]
theorem pointsProdEquivOfIsPullback_apply (x : Points (R := R) fP) :
    pointsProdEquivOfIsPullback hXY hp₁ x = (map p₁ hp₁ x,
      map p₂ (hXY.toCommSq.snd_comp_eq_of_fst_comp_eq (Category.comp_id fX)
        (Category.comp_id fY) hp₁) x) :=
  (rfl)

/-- The inverse product comparison is the morphism into the fibre product given by the universal
property. -/
@[simp]
theorem pointsProdEquivOfIsPullback_symm_apply_val
    (p : Points (R := R) fX × Points (R := R) fY) :
    ((pointsProdEquivOfIsPullback hXY hp₁).symm p).val =
      hXY.lift p.1.val p.2.val (p.1.property.trans p.2.property.symm) :=
  (rfl)

/-- The first projection of the inverse product comparison is the first point of the pair. -/
@[simp]
theorem map_fst_pointsProdEquivOfIsPullback_symm (p : Points (R := R) fX × Points (R := R) fY) :
    map p₁ hp₁ ((pointsProdEquivOfIsPullback hXY hp₁).symm p) = p.1 :=
  map_fst_pointsEquivOfIsPullback_symm hXY hp₁ _ _ _

/-- The second projection of the inverse product comparison is the second point of the pair. -/
@[simp]
theorem map_snd_pointsProdEquivOfIsPullback_symm (h : p₂ ≫ fY = fP)
    (p : Points (R := R) fX × Points (R := R) fY) :
    map p₂ h ((pointsProdEquivOfIsPullback hXY hp₁).symm p) = p.2 :=
  map_snd_pointsEquivOfIsPullback_symm hXY hp₁ _ _ h _

variable [TopologicalSpace R] [IsLocalRing R] [IsOpenUnits R]

/-- Over a local ring with a topology having continuous multiplication, open units and continuous
inversion on the units, the product comparison of points is continuous. -/
@[continuity, fun_prop]
theorem continuous_pointsProdEquivOfIsPullback [ContinuousMul R] :
    Continuous (pointsProdEquivOfIsPullback (R := R) hXY hp₁) :=
  continuous_subtype_val.comp (continuous_pointsEquivOfIsPullback hXY hp₁ _ _)

variable [IsTopologicalRing R]

/-- Over a local topological ring with open units and continuous inversion on the units, the
inverse product comparison of points is continuous. -/
@[continuity, fun_prop]
theorem continuous_pointsProdEquivOfIsPullback_symm :
    Continuous (pointsProdEquivOfIsPullback (R := R) hXY hp₁).symm :=
  (continuous_pointsEquivOfIsPullback_symm hXY hp₁ _ _).comp (continuous_id.subtype_mk _)

/-- Over a local topological ring with open units and continuous inversion on the units, the
`R`-points of a fibre product `P` of `X` and `Y` over `Spec k` are homeomorphic, through the two
projections, to the product of the `R`-points of `X` and `Y`. -/
noncomputable def pointsProdHomeomorphOfIsPullback :
    Points (R := R) fP ≃ₜ Points (R := R) fX × Points (R := R) fY where
  toEquiv := pointsProdEquivOfIsPullback hXY hp₁
  continuous_toFun := continuous_pointsProdEquivOfIsPullback hXY hp₁
  continuous_invFun := continuous_pointsProdEquivOfIsPullback_symm hXY hp₁

/-- The product homeomorphism has the product comparison of points as its underlying
equivalence. -/
@[simp]
theorem pointsProdHomeomorphOfIsPullback_toEquiv :
    (pointsProdHomeomorphOfIsPullback (R := R) hXY hp₁).toEquiv =
      pointsProdEquivOfIsPullback hXY hp₁ :=
  (rfl)

/-- The product homeomorphism is the product comparison of points. -/
@[simp]
theorem coe_pointsProdHomeomorphOfIsPullback :
    ⇑(pointsProdHomeomorphOfIsPullback (R := R) hXY hp₁) = pointsProdEquivOfIsPullback hXY hp₁ :=
  (rfl)

/-- The inverse product homeomorphism is the inverse product comparison of points. -/
@[simp]
theorem coe_pointsProdHomeomorphOfIsPullback_symm :
    ⇑(pointsProdHomeomorphOfIsPullback (R := R) hXY hp₁).symm =
      (pointsProdEquivOfIsPullback hXY hp₁).symm :=
  (rfl)

end Prod

end TauCeti.SchemePointTopology
