/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.Curves.Node.Descent
public import TauCeti.AlgebraicGeometry.Curves.Node.LocalNormalForm
import Mathlib.RingTheory.Etale.Field
import TauCeti.AlgebraicGeometry.Curves.Node.Locality
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.RingTheory.Node.BaseChange

/-!
# Curves with only ordinary nodes

Let `X` be a scheme over a field `F`. A point `x` of `X` is an **ordinary node or smooth point**
(`TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`) if it lies in the image of an étale
neighbourhood `U ⟶ X` that admits an étale morphism over `F` to the split node chart
`Spec F[u, v] ⧸ (uv)`. This is the étale-local form of an ordinary double point; smooth points
of a curve also have such charts.

This file shows that a scheme over `F` is at worst nodal of relative dimension one exactly when
each of its points has, after some finite separable extension of `F` depending on the point, a
point above it that is an ordinary node or a smooth point. Such extensions are only needed at the
points outside the smooth locus. Equivalently, every point of the base change to a separably
closed extension of `F`, for instance an algebraic closure, is an ordinary node or a smooth point.

The converse direction uses the étale local normal form of a nodal curve
(`AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_notMem_smoothLocus`): at a non-smooth
point the chart is `uv = h` over an étale `F`-algebra `R'`, and `h` vanishes in the residue field
of `R'` at the point below, which is a finite separable extension of `F`.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`: a point is an ordinary node or a smooth
  point of a scheme over a field.

## Main results

* `TauCeti.AlgebraicGeometry.isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus`: points of the smooth
  locus of a curve are smooth points.
* `TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt`: a
  scheme over a field whose points are all ordinary nodes or smooth points is at worst nodal.
* `AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt`: the same
  conclusion when this holds after a field extension.
* `atWorstNodalOfRelativeDimensionOne_iff_forall_exists_isSeparable`: nodality is equivalent to
  every point being an ordinary node or a smooth point after a finite separable extension.
* `atWorstNodalOfRelativeDimensionOne_iff_forall_notMem_smoothLocus_exists_isSeparable`: for a
  curve, these extensions are needed only at the points outside the smooth locus.
* `atWorstNodalOfRelativeDimensionOne_iff_forall_isOrdinaryNodeOrSmoothAt_of_isSepClosed`:
  nodality is equivalent to all points of the base change to a separably closed extension being
  ordinary nodes or smooth points.

## References

* [Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodes.
* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- A point `x` of a scheme `X` over a field `F` is an **ordinary node or a smooth point** if some
étale neighbourhood of `x` is étale over the split node chart `Spec F[u, v] ⧸ (uv)` compatibly
with the maps to `Spec F`. -/
def IsOrdinaryNodeOrSmoothAt (f : X ⟶ Spec (.of F)) (x : X) : Prop :=
  ∃ (U : Scheme.{u}) (e : U ⟶ X) (c : U ⟶ Spec (.of (NodeAlgebra F 0))),
    Etale e ∧ Etale c ∧ x ∈ Set.range e ∧ c ≫ Spec.algebraMap F (NodeAlgebra F 0) = e ≫ f

/-- The image of an ordinary node or smooth point under an étale morphism over `F` is an
ordinary node or a smooth point. -/
theorem IsOrdinaryNodeOrSmoothAt.of_comp {X' : Scheme.{u}} {φ : X' ⟶ X} [Etale φ]
    {f : X ⟶ Spec (.of F)} {x : X'} (h : IsOrdinaryNodeOrSmoothAt (φ ≫ f) x) :
    IsOrdinaryNodeOrSmoothAt f (φ x) := by
  obtain ⟨U, e, c, he, hc, ⟨u, rfl⟩, hce⟩ := h
  exact ⟨U, e ≫ φ, c, inferInstance, hc, ⟨u, rfl⟩, by rw [hce, Category.assoc]⟩

/-- A point in the smooth locus of a curve over a field is a smooth point, hence an ordinary node
or a smooth point. -/
theorem isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus (f : X ⟶ Spec (.of F))
    [LocallyOfFinitePresentation f] [PureRelativeDimension 1 f] {x : X}
    (hx : x ∈ f.smoothLocus) : IsOrdinaryNodeOrSmoothAt f x := by
  let : X.Over (Spec (.of F)) := ⟨f⟩
  have : LocallyOfFinitePresentation (X ↘ Spec (.of F)) := ‹LocallyOfFinitePresentation f›
  have : PureRelativeDimension 1 (X ↘ Spec (.of F)) := ‹PureRelativeDimension 1 f›
  obtain ⟨T, _, g, ψ, y, hg, hψ, hgy, hbase, -, -⟩ :=
    X.exists_etale_nodeAlgebra_zero_of_mem_smoothLocus (R := F) hx
  exact ⟨_, g, ψ, hg, hψ, ⟨y, hgy⟩, hbase.symm⟩

/-- After any field extension `F ⟶ L`, a point of the base change lying over a point of the
smooth locus is a smooth point, hence an ordinary node or a smooth point. -/
theorem isOrdinaryNodeOrSmoothAt_pullback_fst_of_mem_smoothLocus (L : Type u) [Field L]
    [Algebra F L] (f : X ⟶ Spec (.of F)) [LocallyOfFinitePresentation f]
    [PureRelativeDimension 1 f] {y : ↥(pullback (Spec.algebraMap F L) f)}
    (hy : pullback.snd _ f y ∈ f.smoothLocus) :
    IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y := by
  let g := Spec.algebraMap F L
  have h₁ : (pullbackSymmetry g f).hom y ∈ (pullback.snd f g).smoothLocus := by
    refine Scheme.Hom.preimage_smoothLocus_le_smoothLocus_pullback_snd f g ?_
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
    exact hy
  have h₂ : y ∈ ((pullbackSymmetry g f).hom ≫ pullback.snd f g).smoothLocus := by
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact h₁
  have h₃ : y ∈ (pullback.fst g f).smoothLocus := by
    convert h₂ using 2
    exact (pullbackSymmetry_hom_comp_snd g f).symm
  exact isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus _ h₃

/-- An ordinary node or smooth point has an étale neighbourhood that is at worst nodal of
relative dimension one over the base field. -/
theorem IsOrdinaryNodeOrSmoothAt.exists_etale {f : X ⟶ Spec (.of F)} {x : X}
    (h : IsOrdinaryNodeOrSmoothAt f x) :
    ∃ (U : Scheme.{u}) (e : U ⟶ X), Etale e ∧ x ∈ Set.range e ∧
      AtWorstNodalOfRelativeDimensionOne (e ≫ f) := by
  obtain ⟨U, e, c, he, hc, hxe, hce⟩ := h
  refine ⟨U, e, he, hxe, ?_⟩
  rw [← hce]
  exact (NodeAlgebra.atWorstNodalOfRelativeDimensionOne (0 : F)).comp_of_etale c

/-- A scheme over a field all of whose points are ordinary nodes or smooth points is at worst
nodal of relative dimension one. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt (f : X ⟶ Spec (.of F))
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt f x) : AtWorstNodalOfRelativeDimensionOne f := by
  choose U e he hx hU using fun x ↦ (h x).exists_etale
  exact AtWorstNodalOfRelativeDimensionOne.of_etale_cover f e (fun x ↦ ⟨x, hx x⟩) hU

/-- A scheme over a field `F` is at worst nodal of relative dimension one if, after some field
extension `F ⟶ L`, all points of its base change are ordinary nodes or smooth points. For
instance `L` may be an algebraic closure of `F`. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt
    (L : Type u) [Field L] [Algebra F L] (f : X ⟶ Spec (.of F))
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt (pullback.fst (Spec.algebraMap F L) f) x) :
    AtWorstNodalOfRelativeDimensionOne f := by
  have hL : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.algebraMap F L) := by
    obtain ⟨hfl, hs⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap F L))).mpr
      (by simpa using RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    exact ⟨⟨hs, hfl⟩, inferInstance⟩
  exact MorphismProperty.of_pullback_fst_of_descendsAlong hL
    (AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt _ h)

/-- A scheme over a field `F` is at worst nodal of relative dimension one if each point `x` has,
after some finite separable extension `F ⟶ L` depending on `x`, a point above it in the base
change that is an ordinary node or a smooth point. -/
private theorem AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable
    (f : X ⟶ Spec (.of F))
    (h : ∀ x, ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L) (y : ↥(pullback (Spec.algebraMap F L) f)),
      pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y) :
    AtWorstNodalOfRelativeDimensionOne f := by
  choose L _ _ _ _ y hy hL using h
  choose U e he hx hU using fun x ↦ (hL x).exists_etale
  have : ∀ x, Algebra.Etale F (L x) := fun x ↦ ⟨Algebra.FormallyEtale.of_isSeparable F (L x),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  refine AtWorstNodalOfRelativeDimensionOne.of_etale_cover f (fun x ↦ e x ≫ pullback.snd _ f)
    (fun x ↦ ⟨x, ?_⟩) fun x ↦ ?_
  · obtain ⟨u, hu⟩ := hx x
    exact ⟨u, by simp [hu, hy]⟩
  · have := hU x
    rw [atWorstNodalOfRelativeDimensionOne_iff_of_iso_spec _ (Iso.refl _),
      Iso.refl_hom, Category.comp_id] at this
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      atWorstNodalOfRelativeDimensionOne_iff_of_iso_spec _ (Iso.refl _), Iso.refl_hom,
      Category.comp_id]
    exact this.comp_specAlgebraMap (R := F)

/-- Base change of an étale chart of the node `uv = h` over `R'` along an étale map `R' → L`:
the fibre product `Spec T ×_{Spec R'} Spec L` is étale over the node chart `uv = h` over `L`,
compatibly with the projections to `Spec L`. -/
private theorem exists_etale_nodeAlgebra_pullback {R' T L : Type u} [CommRing R'] [CommRing T]
    [Field L] [Algebra R' L] [Algebra.Etale R' L] {h : R'}
    (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' h))) [Etale ψ] :
    ∃ c : pullback (Spec.algebraMap R' L) (ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h)) ⟶
        Spec (.of (NodeAlgebra L (algebraMap R' L h))),
      Etale c ∧ c ≫ Spec.algebraMap L (NodeAlgebra L (algebraMap R' L h)) = pullback.fst _ _ := by
  let c₀ : pullback (Spec.algebraMap R' L) (ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h)) ⟶
      pullback (Spec.algebraMap R' L) (Spec.algebraMap R' (NodeAlgebra R' h)) :=
    pullback.map _ _ _ _ (𝟙 _) ψ (𝟙 _) (by simp) (by simp)
  have : Etale c₀ := by
    have : Etale (c₀ ≫ pullback.snd _ _) := by
      rw [pullback.lift_snd]
      infer_instance
    exact Etale.of_comp c₀ (pullback.snd _ _)
  have : Etale (Spec.map
      (CommRingCat.ofHom (NodeAlgebra.baseChange (S := L) h).symm.toRingHom)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.Etale.of_bijective (NodeAlgebra.baseChange h).symm.bijective
  refine ⟨c₀ ≫ (pullbackSpecIso R' L (NodeAlgebra R' h)).hom ≫
    Spec.map (CommRingCat.ofHom (NodeAlgebra.baseChange h).symm.toRingHom), inferInstance, ?_⟩
  have hr : CommRingCat.ofHom (algebraMap L (NodeAlgebra L (algebraMap R' L h))) ≫
      CommRingCat.ofHom (NodeAlgebra.baseChange h).symm.toRingHom =
        CommRingCat.ofHom (algebraMap L (L ⊗[R'] NodeAlgebra R' h)) := by
    ext r
    exact (NodeAlgebra.baseChange h).symm.commutes r
  simp only [Spec.algebraMap, Category.assoc, ← Spec.map_comp, hr, pullbackSpecIso_hom_fst']
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The chart construction behind the converse criteria. Let `g : Spec T ⟶ X` and
`ψ : Spec T ⟶ Spec R'[u, v] ⧸ (uv - h)` be étale, over an étale `F`-algebra `R'`, and let
`χ : R' →ₐ[F] L` be a map to an étale field extension of `F` whose kernel is the prime of `R'`
below `ψ y` and which kills `h`. Base changing the chart along `χ` gives an étale chart of
`X_L` over `Spec L[u, v] ⧸ (uv)` through a point above `g y`. -/
private theorem exists_isOrdinaryNodeOrSmoothAt_pullback_of_chart (f : X ⟶ Spec (.of F))
    {R' T : Type u} [CommRing R'] [CommRing T] [Algebra F R'] [Algebra.Etale F R'] {h : R'}
    (g : Spec (.of T) ⟶ X) (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' h))) [Etale g]
    [Etale ψ] (hbase : g ≫ f = ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h) ≫ Spec.algebraMap F R')
    (y : Spec (.of T)) (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]
    (χ : R' →ₐ[F] L) (hχ : RingHom.ker χ = (ψ y).asIdeal.comap (algebraMap R' (NodeAlgebra R' h)))
    (hh : χ h = 0) :
    ∃ z : ↥(pullback (Spec.algebraMap F L) f), pullback.snd _ f z = g y ∧
      IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) z := by
  let : Algebra R' L := χ.toRingHom.toAlgebra
  have : IsScalarTower F R' L := IsScalarTower.of_algebraMap_eq fun r ↦ (χ.commutes r).symm
  have : Algebra.Etale R' L := .of_restrictScalars F R' L
  -- The chart `U = Spec T ×_{Spec R'} Spec L` of `X_L`, with its étale map `e` to `X_L`.
  let τ := ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h)
  have hFL : Spec.algebraMap F L = Spec.algebraMap R' L ≫ Spec.algebraMap F R' := by
    simp only [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let e : pullback (Spec.algebraMap R' L) τ ⟶ pullback (Spec.algebraMap F L) f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
      rw [Category.assoc, hbase, hFL, pullback.condition_assoc]
      simp only [τ, Category.assoc])
  have : Etale e := by
    have : Etale (e ≫ pullback.snd _ f) := by
      rw [pullback.lift_snd]
      infer_instance
    exact Etale.of_comp e (pullback.snd _ f)
  -- `U` is étale over the node chart `uv = χ h`, and `χ h = 0`.
  have hc := exists_etale_nodeAlgebra_pullback (L := L) ψ
  rw [show algebraMap R' L h = 0 by simpa [RingHom.algebraMap_toAlgebra] using hh] at hc
  obtain ⟨c, hc, hce⟩ := hc
  -- A point of `U` above `y`: the image of the point of `Spec L` in `Spec R'` is `ker χ`, the
  -- prime below `ψ y` (`Spec.map_apply` sends a point to its `PrimeSpectrum.comap`).
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.algebraMap R' L)
    (g := τ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) y <|
      PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot _).symm.trans hχ)
  refine ⟨e z, ?_, _, e, c, inferInstance, hc, ⟨z, rfl⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, hz]
  · rw [hce, pullback.lift_fst]

/-- The residue fields at the nodes of a nodal curve. At a point `x` outside the smooth locus of
a nodal curve over a field `F`, there is a finite separable extension `K` of `F` such that, for
every étale field extension `L` of `F` receiving `K`, some point above `x` in the base change to
`L` is an ordinary node or a smooth point. -/
private theorem AtWorstNodalOfRelativeDimensionOne.exists_isSeparable_of_notMem_smoothLocus
    {f : X ⟶ Spec (.of F)} (hf : AtWorstNodalOfRelativeDimensionOne f) {x : X}
    (hx : letI := hf.syntomic; x ∉ f.smoothLocus) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : Algebra.IsSeparable F K), ∀ (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]
        (_ : K →ₐ[F] L), ∃ z : ↥(pullback (Spec.algebraMap F L) f), pullback.snd _ f z = x ∧
          IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) z := by
  let : X.Over (Spec (.of F)) := ⟨f⟩
  obtain ⟨R', _, _, _, T, _, h, g, ψ, y, hg, hψ, hgy, hbase, h₀, -⟩ :=
    X.exists_etale_nodeAlgebra_of_notMem_smoothLocus (R := F) hf hx
  -- `K` is the residue field of the étale `F`-algebra `R'` at the prime `p` below `ψ y`.
  let p := (ψ y).asIdeal.comap (algebraMap R' (NodeAlgebra R' h))
  have hh : h ∈ p := by
    rw [Ideal.mem_comap, ← NodeAlgebra.coord_zero_mul_coord_one]
    exact Ideal.mul_mem_right _ _ h₀
  have := Algebra.FormallyUnramified.finite_of_free F R'
  have : IsArtinianRing R' := isArtinian_of_tower F inferInstance
  have : p.IsPrime := (ψ y).isPrime.comap _
  have : p.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p
  let := Ideal.Quotient.field p
  refine ⟨R' ⧸ p, _, _, inferInstance, inferInstance, fun L _ _ _ χ ↦ ?_⟩
  have hχ : RingHom.ker (χ.comp (Ideal.Quotient.mkₐ F p)) = p := by
    ext r
    simp [RingHom.mem_ker, map_eq_zero_iff χ χ.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨z, hz, hzo⟩ := exists_isOrdinaryNodeOrSmoothAt_pullback_of_chart f g ψ hbase y L
    (χ.comp (Ideal.Quotient.mkₐ F p)) hχ (by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hh])
  exact ⟨z, hz.trans hgy, hzo⟩

/-- A point of the smooth locus of a curve over `F` is itself a smooth point of the base change
along the trivial extension `F = F`. -/
private theorem exists_isSeparable_of_mem_smoothLocus (f : X ⟶ Spec (.of F))
    [LocallyOfFinitePresentation f] [PureRelativeDimension 1 f] {x : X}
    (hx : x ∈ f.smoothLocus) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L) (y : ↥(pullback (Spec.algebraMap F L) f)),
      pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y := by
  have : Surjective (Spec.algebraMap F F) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap F F))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  obtain ⟨y, hy⟩ := (pullback.snd (Spec.algebraMap F F) f).surjective x
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, y, hy,
    isOrdinaryNodeOrSmoothAt_pullback_fst_of_mem_smoothLocus F f (hy ▸ hx)⟩

/-- **Nodal curves have ordinary nodes after finite separable extensions.** At each point `x` of a
nodal curve over a field `F` there are a finite separable extension `L` of `F` and a point above
`x` in the base change to `L` that is an ordinary node or a smooth point. -/
theorem AtWorstNodalOfRelativeDimensionOne.exists_isSeparable_isOrdinaryNodeOrSmoothAt
    {f : X ⟶ Spec (.of F)} (hf : AtWorstNodalOfRelativeDimensionOne f) (x : X) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L) (y : ↥(pullback (Spec.algebraMap F L) f)),
      pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y := by
  have : SyntomicOfRelativeDimension 1 f := hf.syntomic
  have : PureRelativeDimension 1 f := .of_syntomicOfRelativeDimension f
  by_cases hx : x ∈ f.smoothLocus
  · exact exists_isSeparable_of_mem_smoothLocus f hx
  obtain ⟨K, _, _, _, _, H⟩ := hf.exists_isSeparable_of_notMem_smoothLocus hx
  have : Algebra.Etale F K := ⟨Algebra.FormallyEtale.of_isSeparable F K,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  obtain ⟨z, hz, hzo⟩ := H K (AlgHom.id F K)
  exact ⟨K, _, _, inferInstance, inferInstance, z, hz, hzo⟩

/-- **Over a separably closed field, nodes are ordinary.** Every point of a nodal curve over a
separably closed field is an ordinary node or a smooth point. -/
theorem AtWorstNodalOfRelativeDimensionOne.isOrdinaryNodeOrSmoothAt [IsSepClosed F]
    {f : X ⟶ Spec (.of F)} (hf : AtWorstNodalOfRelativeDimensionOne f) (x : X) :
    IsOrdinaryNodeOrSmoothAt f x := by
  have : SyntomicOfRelativeDimension 1 f := hf.syntomic
  have : PureRelativeDimension 1 f := .of_syntomicOfRelativeDimension f
  by_cases hx : x ∈ f.smoothLocus
  · exact isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus f hx
  obtain ⟨K, _, _, _, _, H⟩ := hf.exists_isSeparable_of_notMem_smoothLocus hx
  -- The finite separable extension `K` of the separably closed field `F` is `F` itself.
  obtain ⟨z, hz, hzo⟩ := H F
    (AlgEquiv.ofBijective (Algebra.ofId F K) (IsSepClosed.algebraMap_bijective F K)).symm
  -- The base change along `F = F` is étale over `X` by its second projection.
  have hid : Spec.algebraMap F F = 𝟙 _ := by simp [Spec.algebraMap]
  have hfst : pullback.snd (Spec.algebraMap F F) f ≫ f = pullback.fst _ f := by
    rw [← pullback.condition, hid, Category.comp_id]
  rw [← hz]
  exact IsOrdinaryNodeOrSmoothAt.of_comp (hfst ▸ hzo)

/-- **The criterion with finite separable residue extensions.** A scheme over a field `F` is at
worst nodal of relative dimension one if and only if each point `x` has, after some finite
separable extension `F ⟶ L` depending on `x`, a point above it in the base change that is an
ordinary node or a smooth point. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_forall_exists_isSeparable (f : X ⟶ Spec (.of F)) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ x, ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
        (_ : Algebra.IsSeparable F L) (y : ↥(pullback (Spec.algebraMap F L) f)),
        pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y :=
  ⟨fun hf ↦ hf.exists_isSeparable_isOrdinaryNodeOrSmoothAt,
    AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable f⟩

/-- **The criterion with finite separable residue extensions at singular points.** A curve over a
field `F`, locally of finite presentation and of pure relative dimension one, is at worst nodal if
and only if each point outside its smooth locus has, after some finite separable extension
`F ⟶ L` depending on the point, a point above it in the base change that is an ordinary node or a
smooth point. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_forall_notMem_smoothLocus_exists_isSeparable
    (f : X ⟶ Spec (.of F)) [LocallyOfFinitePresentation f] [PureRelativeDimension 1 f] :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ x ∉ f.smoothLocus, ∃ (L : Type u) (_ : Field L) (_ : Algebra F L)
        (_ : FiniteDimensional F L) (_ : Algebra.IsSeparable F L)
        (y : ↥(pullback (Spec.algebraMap F L) f)),
        pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y := by
  refine ⟨fun hf x _ ↦ hf.exists_isSeparable_isOrdinaryNodeOrSmoothAt x, fun h ↦ ?_⟩
  refine AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable f fun x ↦ ?_
  by_cases hx : x ∈ f.smoothLocus
  · exact exists_isSeparable_of_mem_smoothLocus f hx
  · exact h x hx

/-- **The criterion over a separable closure.** A scheme over a field `F` is at worst nodal of
relative dimension one if and only if, for a separably closed extension `L` of `F` such as an
algebraic closure, every point of its base change to `L` is an ordinary node or a smooth point. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_forall_isOrdinaryNodeOrSmoothAt_of_isSepClosed
    (L : Type u) [Field L] [Algebra F L] [IsSepClosed L] (f : X ⟶ Spec (.of F)) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ y, IsOrdinaryNodeOrSmoothAt (pullback.fst (Spec.algebraMap F L) f) y :=
  ⟨fun hf ↦ (MorphismProperty.pullback_fst _ _ hf).isOrdinaryNodeOrSmoothAt,
    AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt L f⟩

end TauCeti.AlgebraicGeometry
