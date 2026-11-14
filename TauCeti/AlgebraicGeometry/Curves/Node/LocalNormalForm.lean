/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.Curves.Node.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
public import TauCeti.RingTheory.Node.LocalNormalForm
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# The étale local normal form of a nodal relative curve

Let `X` be at worst nodal of relative dimension one over `Spec R`, and let `x` be a point of `X`
at which `X` is not smooth over `Spec R`. This file shows that, étale locally around `x` and after
an étale extension `R → R'` of the base, `X` maps étale to the standard node chart
`Spec R'[u, v] ⧸ (uv - h)`, sending a point above `x` into the closed subscheme `u = v = 0`. Both
triangles over `Spec R' ⟶ Spec R` commute.

Over a discrete valuation ring `R` with uniformizer `π`, at a point of the special fibre, the
extension `R'` is a discrete valuation ring, étale over `R` with local structure map, in which `π`
remains a uniformizer, and the chart is `Spec R'[u, v] ⧸ (uv)` or `Spec R'[u, v] ⧸ (uv - πⁿ)` with
`n > 0`.

These are the scheme-level forms of the ring-level normal forms of
`TauCeti.RingTheory.Node.LocalNormalForm`. They are applied to the sections of an affine open
neighbourhood of `x` on which `X` is standard syntomic of relative dimension one over `R`. There
the singular locus is cut out by the first Fitting ideal of the differentials, it is unramified
over `R` because `X` is nodal, and it contains the prime of `x` because `X` is not smooth at `x`.

The theorem `AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_mem_specialFiber` includes
smooth points as well: they admit a split-node chart with parameter zero and no base extension.

## Main results

* `AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra`: the étale local normal form `uv = h` at a
  non-smooth point, over an arbitrary affine base.
* `AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_isDiscreteValuationRing`: the normal form
  `uv = 0` or `uv = πⁿ` over an étale extension of discrete valuation rings, at a non-smooth point
  of the special fibre.
* `AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_mem_specialFiber`: a chart at every
  point of the special fibre, including smooth points.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion and the étale local structure of families of nodal curves.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- A non-smooth point `x` of a nodal relative curve `X` over `Spec R` has an affine open
neighbourhood `V` whose sections are a standard syntomic `R`-algebra of relative dimension one,
with unramified singular locus containing the prime of `x`. The chart `Spec Γ(X, V) ⟶ X` lies
over `Spec R`. -/
private theorem exists_affineOpen_standardSyntomic (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) {x : X}
    (hx : letI := hnodal.syntomic; x ∉ (X ↘ Spec (.of R)).smoothLocus) :
    ∃ (V : X.affineOpens) (hxV : x ∈ V.1),
      letI : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
      ∃ (_ : TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension 1 R Γ(X, V))
        (_ : Algebra.EssFiniteType R Γ(X, V)),
        Algebra.FormallyUnramified R (Γ(X, V) ⧸ fittingIdeal Γ(X, V) Ω[Γ(X, V)⁄R] 1) ∧
        fittingIdeal Γ(X, V) Ω[Γ(X, V)⁄R] 1 ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal ∧
        V.2.fromSpec ≫ (X ↘ Spec (.of R)) = Spec.algebraMap R Γ(X, V) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  obtain ⟨V, hxV, _, hV⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top 1
      (X ↘ Spec (.of R)) x
  let : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  have hS : TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension 1 R Γ(X, V) := by
    refine (TauCeti.isStandardSyntomicOfRelativeDimension_iff 1 _).mp ?_
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
    exact (TauCeti.isStandardSyntomicOfRelativeDimension_respectsIso 1).right _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv hV
  have := hS.finitePresentation
  -- The singular locus over `V` is cut out by the first Fitting ideal of the differentials.
  have hfu := X.formallyUnramified_quotient_singularLocus_ideal hnodal V
  rw [X.singularLocus_ideal (R := R) V] at hfu
  -- The structure morphism is not smooth at `x`, so the prime of `x` contains that ideal.
  have hm := (X ↘ Spec (.of R)).mem_smoothLocus_iff_isSmoothAt hxV
  rw [← Scheme.baseRingToStructurePresheaf_app_eq_appLE] at hm
  refine ⟨V, hxV, hS, inferInstance, hfu,
    (Ideal.fittingIdeal_kaehlerDifferential_le_iff_not_isSmoothAt _).2 (hm.not.1 hx), ?_⟩
  have := isOver_fromSpec R X V
  rwa [Scheme.Hom.isOver_iff, specOverSpec_over] at this

/-- An étale chart of an affine open `V` of `X` over `Spec R`, given by ring maps
`Γ(X, V) → T ← R'[u, v] ⧸ (uv - h)` over `R → R'`, as a diagram of schemes. The étale morphisms
`g : Spec T ⟶ X` and `ψ : Spec T ⟶ Spec R'[u, v] ⧸ (uv - h)` lie over `Spec R' ⟶ Spec R`. If the
point `y` of `Spec T` lies over the prime of `x ∈ V`, then `g` sends `y` to `x`; if `φ` sends both
coordinates into `y`, then `ψ` sends `y` to the closed subscheme `u = v = 0`. -/
private theorem exists_etale_spec_chart (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (V : X.affineOpens) [Algebra R Γ(X, V)]
    (hV : V.2.fromSpec ≫ (X ↘ Spec (.of R)) = Spec.algebraMap R Γ(X, V)) {x : X}
    (hxV : x ∈ V.1) {R' T : Type u} [CommRing R'] [CommRing T] [Algebra R R']
    [Algebra Γ(X, V) T] [Algebra.Etale Γ(X, V) T] [Algebra R' T] [Algebra R T]
    [IsScalarTower R Γ(X, V) T] [IsScalarTower R R' T] (y : Spec (.of T))
    (hxy : (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal = y.asIdeal.comap (algebraMap Γ(X, V) T)) {h : R'}
    (φ : NodeAlgebra R' h →ₐ[R'] T) (hφ : φ.toRingHom.Etale)
    (hφ₀ : φ (NodeAlgebra.coord h 0) ∈ y.asIdeal) (hφ₁ : φ (NodeAlgebra.coord h 1) ∈ y.asIdeal) :
    ∃ (g : Spec (.of T) ⟶ X) (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' h))),
      Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h) ≫
          Spec.algebraMap R R' ∧
        (Spec.algebraMap R' (NodeAlgebra R' h) (ψ y)).asIdeal = y.asIdeal.comap (algebraMap R' T) ∧
        NodeAlgebra.coord h 0 ∈ (ψ y).asIdeal ∧ NodeAlgebra.coord h 1 ∈ (ψ y).asIdeal := by
  have : Etale (Spec.algebraMap Γ(X, V) T) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)
  have : Etale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hφ
  have := V.2.isOpenImmersion_fromSpec
  -- `ψ = Spec φ` lies over `Spec R'`, because `φ` is an `R'`-algebra map.
  have hψ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.algebraMap R' (NodeAlgebra R' h) =
      Spec.algebraMap R' T := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap]
  refine ⟨Spec.algebraMap Γ(X, V) T ≫ V.2.fromSpec, Spec.map (CommRingCat.ofHom φ.toRingHom),
    inferInstance, inferInstance, ?_, ?_, ?_, hφ₀, hφ₁⟩
  · rw [Scheme.Hom.comp_apply]
    refine (congrArg V.2.fromSpec (PrimeSpectrum.ext ?_)).trans (V.2.fromSpec_primeIdealOf ⟨x, hxV⟩)
    rw [Spec.map_apply, CommRingCat.hom_ofHom, hxy]
    exact PrimeSpectrum.comap_asIdeal _ _
  · rw [Category.assoc, hV, reassoc_of% hψ, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  · rw [← Scheme.Hom.comp_apply, hψ, Spec.map_apply, CommRingCat.hom_ofHom]
    exact PrimeSpectrum.comap_asIdeal _ _

/-- **The étale local normal form of a nodal relative curve.** Let `X` be at worst nodal of
relative dimension one over `Spec R`, and let `x` be a point of `X` at which `X` is not smooth over
`Spec R`. Then there are an étale `R`-algebra `R'`, an element `h ∈ R'`, an affine scheme
`Spec T`, a point `y` of `Spec T`, and étale morphisms `g : Spec T ⟶ X` and
`ψ : Spec T ⟶ Spec R'[u, v] ⧸ (uv - h)` such that `g` sends `y` to `x` and lies over the
composite `Spec T ⟶ Spec R'[u, v] ⧸ (uv - h) ⟶ Spec R' ⟶ Spec R`, and `ψ` sends `y` into the
closed subscheme `u = v = 0`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra (X : Scheme.{u})
    [X.Over (Spec (.of R))] (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)))
    {x : X} (hx : letI := hnodal.syntomic; x ∉ (X ↘ Spec (.of R)).smoothLocus) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (T : Type u) (_ : CommRing T) (h : R') (g : Spec (.of T) ⟶ X)
      (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' h))) (y : Spec (.of T)),
      Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R' (NodeAlgebra R' h) ≫
          Spec.algebraMap R R' ∧
        NodeAlgebra.coord h 0 ∈ (ψ y).asIdeal ∧ NodeAlgebra.coord h 1 ∈ (ψ y).asIdeal := by
  obtain ⟨V, hxV, hV⟩ := exists_affineOpen_standardSyntomic X hnodal hx
  let : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  obtain ⟨_, _, _, hfit, hV⟩ := hV
  obtain ⟨R', _, _, _, T, _, _, _, _, _, _, _, Q, _, h, φ, hxQ, hφ₀, hφ₁, hφ⟩ :=
    TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.exists_etale_nodeAlgebra_hom _ hfit
  obtain ⟨g, ψ, hg, hψ, hgx, hgψ, -, hy₀, hy₁⟩ :=
    exists_etale_spec_chart X V hV hxV ⟨Q, ‹_›⟩ hxQ φ hφ hφ₀ hφ₁
  exact ⟨R', ‹_›, ‹_›, ‹_›, T, ‹_›, h, g, ψ, ⟨Q, ‹_›⟩, hg, hψ, hgx, hgψ, hy₀, hy₁⟩

open TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension in
/-- **The étale local normal form of a nodal relative curve over a discrete valuation ring.** Let
`R` be a discrete valuation ring with uniformizer `π`, let `X` be at worst nodal of relative
dimension one over `Spec R`, and let `x` be a point of the special fibre at which `X` is not smooth
over `Spec R`. Then there are

* a discrete valuation ring `R'` which is an étale `R`-algebra with local structure map, in which
  `π` remains a uniformizer, and an element `b ∈ R'` with `b = 0` or `b = πⁿ` for some `n > 0`,
* an affine scheme `Spec T` with a point `y`, and étale morphisms `g : Spec T ⟶ X` and
  `ψ : Spec T ⟶ Spec R'[u, v] ⧸ (uv - b)`,

such that `g` sends `y` to `x` and lies over the composite
`Spec T ⟶ Spec R'[u, v] ⧸ (uv - b) ⟶ Spec R' ⟶ Spec R`, and `ψ` sends `y` into the closed
subscheme `u = v = 0` over the closed point of `Spec R'`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_isDiscreteValuationRing
    [IsDomain R] [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) (X : Scheme.{u})
    [X.Over (Spec (.of R))] (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)))
    {x : X} (hx : letI := hnodal.syntomic; x ∉ (X ↘ Spec (.of R)).smoothLocus)
    (hxs : (X ↘ Spec (.of R)) x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : Algebra.Etale R R') (_ : IsLocalHom (algebraMap R R'))
      (T : Type u) (_ : CommRing T) (b : R') (g : Spec (.of T) ⟶ X)
      (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' b))) (y : Spec (.of T)),
      Irreducible (algebraMap R R' π) ∧ (b = 0 ∨ ∃ n : ℕ, 0 < n ∧ b = algebraMap R R' π ^ n) ∧
        Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R' (NodeAlgebra R' b) ≫
          Spec.algebraMap R R' ∧
        Spec.algebraMap R' (NodeAlgebra R' b) (ψ y) = IsLocalRing.closedPoint R' ∧
        NodeAlgebra.coord b 0 ∈ (ψ y).asIdeal ∧ NodeAlgebra.coord b 1 ∈ (ψ y).asIdeal := by
  obtain ⟨V, hxV, hV⟩ := exists_affineOpen_standardSyntomic X hnodal hx
  let : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  obtain ⟨_, _, _, hfit, hV⟩ := hV
  -- The prime of `x` in `Γ(X, V)` lies over the closed point of `Spec R`.
  have hxR : (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.comap (algebraMap R Γ(X, V)) =
      IsLocalRing.maximalIdeal R := by
    have hpt : Spec.algebraMap R Γ(X, V) (V.2.primeIdealOf ⟨x, hxV⟩) =
        IsLocalRing.closedPoint R := by
      refine (congrArg (fun g ↦ g (V.2.primeIdealOf ⟨x, hxV⟩)) hV).symm.trans ?_
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg _ (V.2.fromSpec_primeIdealOf ⟨x, hxV⟩)).trans hxs)
    -- The prime ideal of `PrimeSpectrum.comap` is `Ideal.comap` (`PrimeSpectrum.comap_asIdeal`),
    -- and that of `IsLocalRing.closedPoint R` is the maximal ideal, both by definition.
    exact congrArg PrimeSpectrum.asIdeal hpt
  obtain ⟨R', _, _, _, _, _, _, T, _, _, _, _, _, _, _, Q, _, b, φ, hπ', hb, hxQ, hQR', hφ₀, hφ₁,
    hφ⟩ := exists_etale_nodeAlgebra_hom_of_isDiscreteValuationRing hπ _ hfit hxR
  obtain ⟨g, ψ, hg, hψ, hgx, hgψ, hψR', hy₀, hy₁⟩ :=
    exists_etale_spec_chart X V hV hxV ⟨Q, ‹_›⟩ hxQ φ hφ hφ₀ hφ₁
  exact ⟨R', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, T, ‹_›, b, g, ψ, ⟨Q, ‹_›⟩, hπ', hb, hg, hψ, hgx, hgψ,
    PrimeSpectrum.ext (hψR'.trans hQR'), hy₀, hy₁⟩

/-- Every point of the special fibre of a nodal relative curve over a DVR has an affine
étale neighbourhood mapping étale to `uv = 0` or `uv = πⁿ` over an étale extension of DVRs.
The image of the chosen point lies over the closed point of the extended base. At smooth
points the base extension can be the identity and the parameter can be zero. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_etale_nodeAlgebra_of_mem_specialFiber
    [IsDomain R] [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) (X : Scheme.{u})
    [X.Over (Spec (.of R))] (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)))
    {x : X} (hxs : (X ↘ Spec (.of R)) x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : Algebra.Etale R R') (_ : IsLocalHom (algebraMap R R'))
      (T : Type u) (_ : CommRing T) (b : R') (g : Spec (.of T) ⟶ X)
      (ψ : Spec (.of T) ⟶ Spec (.of (NodeAlgebra R' b))) (y : Spec (.of T)),
      Irreducible (algebraMap R R' π) ∧ (b = 0 ∨ ∃ n : ℕ, 0 < n ∧ b = algebraMap R R' π ^ n) ∧
        Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R' (NodeAlgebra R' b) ≫
          Spec.algebraMap R R' ∧
        Spec.algebraMap R' (NodeAlgebra R' b) (ψ y) = IsLocalRing.closedPoint R' := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  by_cases hx : x ∈ (X ↘ Spec (.of R)).smoothLocus
  · obtain ⟨T, _, g, ψ, y, hg, hψ, hgy, hbase, -, -⟩ :=
      X.exists_etale_nodeAlgebra_zero_of_mem_smoothLocus hx
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, T, inferInstance, 0, g, ψ, y, ?_, .inl rfl, hg, hψ, hgy, ?_, ?_⟩
    · simpa using hπ
    · simpa [Spec.algebraMap] using hbase
    · rw [← Scheme.Hom.comp_apply, ← hbase, Scheme.Hom.comp_apply, hgy, hxs]
  · obtain ⟨R', _, _, _, _, _, _, T, _, b, g, ψ, y, hπ', hb, hg, hψ, hgy, hbase, hy, -, -⟩ :=
      X.exists_etale_nodeAlgebra_of_isDiscreteValuationRing hπ hnodal hx hxs
    exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, T, inferInstance, b, g, ψ, y, hπ', hb, hg, hψ, hgy, hbase, hy⟩

end TauCeti.AlgebraicGeometry
