/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.Topology.Algebra.PointTopology.FiberProduct
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality

/-!
# Scheme-valued points of fibre products

Let `X ⟶ Z ⟵ Y` be morphisms of schemes over `Spec k`. The universal property of the fibre
product identifies the `R`-points of `X ×_Z Y` with the pairs of `R`-points of `X` and `Y` having
the same image in `Z`, through the two projections
(`TauCeti.SchemePointTopology.pullbackPointsEquiv`). Over a local topological ring with open
units and continuous inversion on the units, this bijection is a homeomorphism onto the subspace
of compatible pairs (`TauCeti.SchemePointTopology.pullbackPointsHomeomorph`): the point functor
preserves fibre products. No finiteness or separation assumptions are needed.

The projections act continuously on points. For the inverse, a compatible pair lies in the points
of affine charts `Spec A ⟶ X` and `Spec B ⟶ Y` over an affine chart `Spec C ⟶ Z`, and then in
the points of the affine chart `Spec (A ⊗[C] B) ⟶ X ×_Z Y`, an open immersion. On the open set of
such pairs the inverse is the affine comparison
`TauCeti.PointTopology.relativeTensorProductHomeomorph`, read in this chart.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 2.1 and Prop. 3.1 and
  their proofs, pp. 2–4.
* A. Grothendieck, M. Raynaud, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII,
  §1.1, p. 239.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology TensorProduct
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
  {fZ : Z ⟶ Spec (.of k)} (g₁ : X ⟶ Z) (g₂ : Y ⟶ Z) (hg₁ : g₁ ≫ fZ = fX) (hg₂ : g₂ ≫ fZ = fY)

include hg₁ hg₂ in
/-- The second projection of the fibre product is a morphism over the base. -/
theorem pullback_snd_comp_eq : pullback.snd g₁ g₂ ≫ fY = pullback.fst g₁ g₂ ≫ fX := by
  rw [← hg₁, ← hg₂, pullback.condition_assoc]

/-- **Points of a fibre product.** The `R`-points of `X ×_Z Y` are the pairs of `R`-points of
`X` and `Y` with the same image in `Z`, through the two projections. -/
noncomputable def pullbackPointsEquiv :
    Points (R := R) (pullback.fst g₁ g₂ ≫ fX) ≃
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} where
  toFun x := ⟨(map (pullback.fst g₁ g₂) rfl x,
    map (pullback.snd g₁ g₂) (pullback_snd_comp_eq g₁ g₂ hg₁ hg₂) x),
    Subtype.ext (by simp [pullback.condition])⟩
  invFun p := ⟨pullback.lift p.1.1.val p.1.2.val (by simpa using congrArg Subtype.val p.2), by
    simp [p.1.1.property]⟩
  left_inv x := Subtype.ext (pullback.hom_ext (by simp) (by simp))
  right_inv p := Subtype.ext (Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)))

/-- The first component of the fibre-product comparison is the first projection. -/
@[simp]
theorem pullbackPointsEquiv_apply_fst (x : Points (R := R) (pullback.fst g₁ g₂ ≫ fX)) :
    (pullbackPointsEquiv g₁ g₂ hg₁ hg₂ x).1.1 = map (pullback.fst g₁ g₂) rfl x :=
  (rfl)

/-- The second component of the fibre-product comparison is the second projection. -/
@[simp]
theorem pullbackPointsEquiv_apply_snd (x : Points (R := R) (pullback.fst g₁ g₂ ≫ fX)) :
    (pullbackPointsEquiv g₁ g₂ hg₁ hg₂ x).1.2 =
      map (pullback.snd g₁ g₂) (pullback_snd_comp_eq g₁ g₂ hg₁ hg₂) x :=
  (rfl)

/-- The inverse fibre-product comparison is the morphism into the fibre product given by the
universal property. -/
@[simp]
theorem pullbackPointsEquiv_symm_apply_val
    (p : {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2}) :
    ((pullbackPointsEquiv g₁ g₂ hg₁ hg₂).symm p).val =
      pullback.lift p.1.1.val p.1.2.val (by simpa using congrArg Subtype.val p.2) :=
  (rfl)

omit [Algebra k R] in
/-- A chart composed with a map of affine schemes is the chart applied to composed points. -/
private theorem chartPoint_spec_map_comp [Algebra k R] {A C : CommAlgCat.{u} k}
    (iC : Spec (.of C) ⟶ Z) (hiC : iC ≫ fZ = Spec.algebraMap k C) (φ : C →ₐ[k] A)
    (h : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ iC) ≫ fZ = Spec.algebraMap k A)
    (a : A →ₐ[k] R) :
    chartPoint fZ A (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ iC) h a =
      chartPoint fZ C iC hiC (a.comp φ) := by
  apply Subtype.ext
  simp only [chartPoint_val, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- A point of `X` whose image in `Z` lies in an affine open chart `Spec C ⟶ Z` lies in an affine
open chart `Spec A ⟶ X` mapping to it, through an algebra map `C → A`. -/
private theorem exists_chartPoint_over [IsLocalRing R] (C : CommAlgCat.{u} k)
    (iC : Spec (.of C) ⟶ Z) (hiC : iC ≫ fZ = Spec.algebraMap k C) [IsOpenImmersion iC]
    (x : Points (R := R) fX) (hx : map g₁ hg₁ x ∈ Set.range (chartPoint fZ C iC hiC)) :
    ∃ (A : CommAlgCat.{u} k) (iA : Spec (.of A) ⟶ X) (hiA : iA ≫ fX = Spec.algebraMap k A)
      (_ : IsOpenImmersion iA) (φ : C →ₐ[k] A),
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ iC = iA ≫ g₁ ∧
        x ∈ Set.range (chartPoint fX A iA hiA) := by
  -- Work in the open subscheme `U = g₁⁻¹(Spec C)`, which contains the image of `x`.
  let U : X.Opens := g₁ ⁻¹ᵁ iC.opensRange
  have hxU : x ∈ Set.range (map U.ι (rfl : U.ι ≫ fX = U.ι ≫ fX)) := by
    rw [mem_range_map_iff, Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have h := (mem_range_chartPoint_iff fZ C iC hiC _).1 hx ⟨p, rfl⟩
    simpa [U] using h
  obtain ⟨x', rfl⟩ := hxU
  obtain ⟨A, i, hi, _, a, rfl⟩ := exists_mem_range_chartPoint (U.ι ≫ fX) x'
  have hiA : (i ≫ U.ι) ≫ fX = Spec.algebraMap k A := by rw [Category.assoc, hi]
  have hrange : Set.range (i ≫ U.ι ≫ g₁) ⊆ Set.range iC := by
    rintro _ ⟨p, rfl⟩
    have h : U.ι (i p) ∈ U := by
      have h' : U.ι (i p) ∈ Set.range U.ι := Set.mem_range_self _
      rwa [Scheme.Opens.range_ι] at h'
    simpa [U] using h
  let : Z.Over (Spec (.of k)) := ⟨fZ⟩
  have : iC.IsOver (Spec (.of k)) := ⟨hiC⟩
  have : (i ≫ U.ι ≫ g₁).IsOver (Spec (.of k)) := ⟨by
    change i ≫ U.ι ≫ g₁ ≫ fZ = _
    rw [hg₁, ← Category.assoc, hiA]
    rfl⟩
  obtain ⟨φ, hφ, -⟩ :=
    AlgebraicGeometry.existsUnique_spec_map_comp_eq_of_range_subset (R := k) iC _ hrange
  refine ⟨A, i ≫ U.ι, hiA, inferInstance, φ, by rw [hφ, Category.assoc], a, ?_⟩
  rw [map_chartPoint]

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R]

/-- The fibre-product comparison is continuous: the projections act continuously on points. -/
theorem continuous_pullbackPointsEquiv :
    Continuous (pullbackPointsEquiv (R := R) g₁ g₂ hg₁ hg₂) :=
  ((continuous_map _ _).prodMk (continuous_map _ _)).subtype_mk _

/-- The inverse fibre-product comparison is continuous: near a compatible pair it is read in an
affine chart `Spec (A ⊗[C] B) ⟶ X ×_Z Y`, where it is the affine comparison
`TauCeti.PointTopology.relativeTensorProductHomeomorph`. -/
theorem continuous_pullbackPointsEquiv_symm :
    Continuous (pullbackPointsEquiv (R := R) g₁ g₂ hg₁ hg₂).symm := by
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
  -- The affine chart `Spec (A ⊗[C] B) ⟶ X ×_Z Y`.
  let j : Spec (.of (A ⊗[C] B)) ⟶ pullback g₁ g₂ := (pullbackSpecIso C A B).inv ≫
    pullback.map _ _ _ _ iA iB iC hφA hφB
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hj₁ : j ≫ pullback.fst g₁ g₂ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ iA := by
    simp [j]
  have hj₂ : j ≫ pullback.snd g₁ g₂ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := B)).toRingHom) ≫ iB := by
    simp [j]
  have hj : j ≫ pullback.fst g₁ g₂ ≫ fX =
      Spec.algebraMap k (CommAlgCat.of k (A ⊗[C] B)) := by
    rw [← Category.assoc, hj₁, Category.assoc, hiA, Spec.algebraMap, Spec.algebraMap,
      ← Spec.map_comp]
    rfl
  -- Compatible pairs of chart points are compatible pairs of algebra maps.
  have hcompat (q : (A →ₐ[k] R) × (B →ₐ[k] R)) :
      map g₁ hg₁ (chartPoint fX A iA hiA q.1) = map g₂ hg₂ (chartPoint fY B iB hiB q.2) ↔
        q.1.comp (IsScalarTower.toAlgHom k C A) = q.2.comp (IsScalarTower.toAlgHom k C B) := by
    rw [map_chartPoint, map_chartPoint]
    simp only [← hφA, ← hφB]
    rw [chartPoint_spec_map_comp iC hiC, chartPoint_spec_map_comp iC hiC]
    exact (chartPoint_injective fZ C iC hiC).eq_iff
  let S : Set (Points (R := R) fX × Points (R := R) fY) := {p | map g₁ hg₁ p.1 = map g₂ hg₂ p.2}
  let c := Prod.map (chartPoint (R := R) fX A iA hiA) (chartPoint (R := R) fY B iB hiB)
  have hc : IsOpenEmbedding (S.restrictPreimage c) :=
    ((isOpenEmbedding_chartPoint fX A iA hiA).prodMap
      (isOpenEmbedding_chartPoint fY B iB hiB)).restrictPreimage S
  let τ : c ⁻¹' S → {q : (A →ₐ[k] R) × (B →ₐ[k] R) //
      q.1.comp (IsScalarTower.toAlgHom k C A) = q.2.comp (IsScalarTower.toAlgHom k C B)} :=
    fun q ↦ ⟨q.1, (hcompat q.1).1 q.2⟩
  have hτ : Continuous τ := continuous_subtype_val.subtype_mk _
  -- On compatible pairs of chart points, the inverse comparison is read in the chart `j`.
  have key : (pullbackPointsEquiv (R := R) g₁ g₂ hg₁ hg₂).symm ∘ S.restrictPreimage c =
      chartPoint _ (CommAlgCat.of k (A ⊗[C] B)) j hj ∘
        (PointTopology.relativeTensorProductHomeomorph k C A B R).symm ∘ τ := by
    funext q
    apply Subtype.ext
    simp only [Function.comp_apply, pullbackPointsEquiv_symm_apply_val, chartPoint_val]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hj₁, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rw [show (S.restrictPreimage c q : Points (R := R) fX × Points (R := R) fY).1 =
        chartPoint fX A iA hiA q.1.1 from rfl, chartPoint_val]
      refine congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ) ≫ iA) (RingHom.ext fun t ↦ ?_)
      simp [τ]
    · rw [pullback.lift_snd, Category.assoc, hj₂, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rw [show (S.restrictPreimage c q : Points (R := R) fX × Points (R := R) fY).2 =
        chartPoint fY B iB hiB q.1.2 from rfl, chartPoint_val]
      refine congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ) ≫ iB) (RingHom.ext fun t ↦ ?_)
      simp [τ]
  have hmem : (⟨(chartPoint fX A iA hiA a, chartPoint fY B iB hiB b), hxy⟩ :
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2}) =
      S.restrictPreimage c ⟨(a, b), hxy⟩ :=
    rfl
  rw [hmem, ← hc.continuousAt_iff, key]
  have h₁ := continuous_chartPoint (R := R) (pullback.fst g₁ g₂ ≫ fX)
    (CommAlgCat.of k (A ⊗[C] B)) j hj
  have h₂ := (PointTopology.relativeTensorProductHomeomorph k C A B R).symm.continuous.comp hτ
  exact (h₁.comp h₂).continuousAt

/-- **The point functor preserves fibre products.** Over a local topological ring with open units
and continuous inversion on the units, the `R`-points of `X ×_Z Y` are homeomorphic, through the
two projections, to the subspace of pairs of `R`-points of `X` and `Y` with the same image in
`Z`. -/
noncomputable def pullbackPointsHomeomorph :
    Points (R := R) (pullback.fst g₁ g₂ ≫ fX) ≃ₜ
      {p : Points (R := R) fX × Points (R := R) fY // map g₁ hg₁ p.1 = map g₂ hg₂ p.2} where
  toEquiv := pullbackPointsEquiv g₁ g₂ hg₁ hg₂
  continuous_toFun := continuous_pullbackPointsEquiv g₁ g₂ hg₁ hg₂
  continuous_invFun := continuous_pullbackPointsEquiv_symm g₁ g₂ hg₁ hg₂

/-- The fibre-product homeomorphism is the fibre-product comparison of points. -/
@[simp]
theorem coe_pullbackPointsHomeomorph :
    ⇑(pullbackPointsHomeomorph (R := R) g₁ g₂ hg₁ hg₂) = pullbackPointsEquiv g₁ g₂ hg₁ hg₂ :=
  (rfl)

end Topology

end TauCeti.SchemePointTopology
