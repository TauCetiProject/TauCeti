/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.RingTheory.Grassmannian.Chart.Plucker
public import TauCeti.RingTheory.Grassmannian.Plucker
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The Plücker morphism of the Grassmannian scheme

Let `M` be a module over a commutative ring `R` and `k` a natural number. This file constructs the
**Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R` between the Grassmannian schemes
`Module.Grassmannian.scheme R M k` and `Module.Grassmannian.scheme R (⋀[R]^k M) 1`, the latter
the projective bundle `P(⋀ᵏ M)` of rank-one quotients. On points over an `R`-algebra `A` it sends
the point classifying `N ⊆ A ⊗[R] M` to the point classifying the kernel of
`⋀ᵏ_A (A ⊗[R] M) → ⋀ᵏ_A ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.pluckerBaseChange`): the universal exterior-power quotient
`⋀ᵏ (A ⊗[R] M) → ⋀ᵏ Q = det Q`, where `Q = (A ⊗[R] M) ⧸ N` is the universal quotient.

The point map is natural in `A` (`Module.Grassmannian.pluckerBaseChange_map`), so it is composition
with a morphism of schemes (`Module.Grassmannian.homOfPoints`).

On the chart of `G(k, M)` at `x : Fin k → M`, the Plücker morphism is `Spec` of the Plücker map on
charts `Module.Grassmannian.ChartAlgebra.pluckerChartHom R x` followed by the chart of
`G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`; since that ring map is surjective, `Spec` of it is a closed
immersion.

The preimage of the chart at `x₁ ∧ ⋯ ∧ xₖ` is the chart at `x`: a point lies in either chart
exactly when its residue-field point does, and over a field the images of `x₁, …, xₖ` span the
universal quotient `Q` exactly when their wedge spans `⋀ᵏ Q`. So the square of charts is cartesian,
and since the charts at the wedges `x₁ ∧ ⋯ ∧ xₖ` cover `G(1, ⋀ᵏ M)`, the Plücker morphism is a
closed immersion, for every module `M`.

## Main definitions

* `Module.Grassmannian.pluckerHom R M k`: the Plücker morphism `G(k, M) ⟶ G(1, ⋀ᵏ M)`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_pluckerHom`: the characterisation of `pluckerHom` on
  points.
* `Module.Grassmannian.pluckerHom_toSpec`: `pluckerHom` lies over `Spec R`.
* `Module.Grassmannian.specMap_pluckerChartHom_chartι`: `pluckerHom` on the standard charts.
* `Module.Grassmannian.isClosedImmersion_specMap_pluckerChartHom`: `Spec` of the Plücker map on
  charts `Module.Grassmannian.ChartAlgebra.pluckerChartHom R x` is a closed immersion, since that
  ring map is surjective.
* `Module.Grassmannian.toSchemeHom_apply_mem_opensRange_chartι_iff`: a field-valued point lies in
  the image of the chart at `x` exactly when it lies in the chart at `x`.
* `Module.Grassmannian.pluckerHom_preimage_opensRange_chartι`: the preimage under `pluckerHom` of
  the chart at `x₁ ∧ ⋯ ∧ xₖ` is the chart at `x`.
* `Module.Grassmannian.iSup_opensRange_chartι_ιMulti`: the charts at the wedges cover
  `G(1, ⋀ᵏ M)`.
* `Module.Grassmannian.isPullback_pluckerHom_chartι`: the square of charts is cartesian.
* `Module.Grassmannian.isClosedImmersion_pluckerHom`: **the Plücker morphism is a closed
  immersion.**

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its Plücker embedding.
* U. Görtz, T. Wedhorn, *Algebraic Geometry I* (Vieweg+Teubner, 2010), Chapter 8, for the
  standard charts of the Grassmannian and the Plücker embedding.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

-- the naturality of the point map of `pluckerHom`
private lemma toSchemeHom_pluckerBaseChange_map (S T : Type u) [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (N : G(k, S ⊗[R] M; S)) :
    toSchemeHom (pluckerBaseChange (map f N)) =
      Spec.map (CommRingCat.ofHom (f : S →+* T)) ≫ toSchemeHom (pluckerBaseChange N) := by
  rw [pluckerBaseChange_map, toSchemeHom_map]

variable (R M k) in
/-- **The Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R`: it sends the point classifying
`N ⊆ A ⊗[R] M` over an `R`-algebra `A` to the point classifying the kernel of
`⋀ᵏ (A ⊗[R] M) → ⋀ᵏ ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.toSchemeHom_comp_pluckerHom`). -/
noncomputable def pluckerHom : scheme R M k ⟶ scheme R (⋀[R]^k M) 1 :=
  homOfPoints (fun _ _ _ N ↦ toSchemeHom (pluckerBaseChange N)) toSchemeHom_pluckerBaseChange_map

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **`pluckerHom` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed with
`pluckerHom`, classifies the Plücker point of `N`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_pluckerHom (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ pluckerHom R M k = toSchemeHom (pluckerBaseChange N) :=
  toSchemeHom_comp_homOfPoints _ toSchemeHom_pluckerBaseChange_map N

variable (R M k) in
/-- `pluckerHom` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem pluckerHom_toSpec : pluckerHom R M k ≫ toSpec R (⋀[R]^k M) 1 = toSpec R M k := by
  refine scheme_hom_ext fun A _ _ N ↦ ?_
  rw [toSchemeHom_comp_pluckerHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec]

open ChartAlgebra

variable (R) in
/-- **The Plücker morphism on charts.** On the chart of `G(k, M)` at `x`, the Plücker morphism is
`Spec` of `pluckerChartHom R x` followed by the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`. -/
@[reassoc]
theorem specMap_pluckerChartHom_chartι (x : Fin k → M) :
    Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
        ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x)) ≫
      chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) =
    chartι R x ≫ pluckerHom R M k := by
  rw [← toSchemeHom_chartHomEquiv_id x, toSchemeHom_comp_pluckerHom,
    pluckerBaseChange_chartHomEquiv_id, ← toSchemeHom_chartHomEquiv_id, ← toSchemeHom_map,
    ← chartHomEquiv_comp, AlgHom.comp_id]

variable (R) in
/-- `Spec` of the Plücker map on charts is a closed immersion. -/
theorem isClosedImmersion_specMap_pluckerChartHom (x : Fin k → M) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
      ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x))) :=
  IsClosedImmersion.spec_of_surjective _ (pluckerChartHom_surjective R x)

/-! ### The Plücker morphism is a closed immersion -/

section FieldPoints

/-- A field-valued point lies in the chart at `x` exactly when the morphism classifying it lands in
the chart: for a field `K` and `N ∈ G(k, K ⊗[R] M; K)`, the image of the point of `Spec K` under
`toSchemeHom N` lies in the open of `G(k, M)` that is the image of `chartι R x` exactly when `N`
lies in the chart at `1 ⊗ₜ x`. -/
theorem toSchemeHom_apply_mem_opensRange_chartι_iff {K : Type u} [Field K] [Algebra R K]
    (N : G(k, K ⊗[R] M; K)) (x : Fin k → M) (p : Spec (.of K)) :
    toSchemeHom N p ∈ (chartι R x).opensRange ↔ N ∈ chart K (fun i ↦ (1 : K) ⊗ₜ[R] x i) := by
  refine ⟨fun hp ↦ ?_, fun hN ↦ ?_⟩
  · -- `Spec K` is a point, so `toSchemeHom N` factors through the chart
    have hrange : Set.range (toSchemeHom N) ⊆ Set.range (chartι R x) := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hp
    have hl := IsOpenImmersion.lift_fac (chartι R x) (toSchemeHom N) hrange
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι R x) (toSchemeHom N) hrange)
    rw [← hφ] at hl
    -- the factorization is a map of `R`-algebras
    have hφR : CommRingCat.ofHom (algebraMap R (ChartAlgebra R x)) ≫ φ =
        CommRingCat.ofHom (algebraMap R K) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← chartι_toSpec, reassoc_of% hl, toSchemeHom_toSpec]
    let g : ChartAlgebra R x →ₐ[R] K :=
      { φ.hom with commutes' := fun r ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hφR) r }
    have hg : toSchemeHom N = toSchemeHom (chartHomEquiv R x K g).val := by
      rw [toSchemeHom_chartHomEquiv, ← hl]
      rfl
    rw [toSchemeHom_injective hg]
    exact (chartHomEquiv R x K g).property
  · refine ⟨Spec.map (CommRingCat.ofHom
      ((chartHomEquiv R x K).symm ⟨N, hN⟩ : ChartAlgebra R x →+* K)) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← toSchemeHom_chartHomEquiv, Equiv.apply_symm_apply]

variable (R M k) in
/-- Every point of `G(k, M)` is the image of the point of `Spec K` under the morphism classifying a
point of `G(k, K ⊗[R] M; K)`, for a field `K` (its residue field). -/
theorem exists_toSchemeHom_apply_eq (z : scheme R M k) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra R K) (N : G(k, K ⊗[R] M; K)) (p : Spec (.of K)),
      toSchemeHom N p = z := by
  let K : Type u := IsLocalRing.ResidueField ((scheme R M k).presheaf.stalk z)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((scheme R M k).fromSpecResidueField z ≫ toSpec R M k)
  let _ : Algebra R K := φ.hom.toAlgebra
  obtain ⟨N, hN⟩ := exists_toSchemeHom_eq (A := K) ((scheme R M k).fromSpecResidueField z)
    hφ.symm
  exact ⟨K, inferInstance, inferInstance, N, default,
    by rw [hN]; exact (scheme R M k).fromSpecResidueField_apply z _⟩

end FieldPoints

/-- **The preimage of a Plücker chart.** The preimage under `pluckerHom` of the chart of
`G(1, ⋀ᵏ M)` at the wedge `x₁ ∧ ⋯ ∧ xₖ` is the chart of `G(k, M)` at `x`. -/
theorem pluckerHom_preimage_opensRange_chartι (x : Fin k → M) :
    pluckerHom R M k ⁻¹ᵁ (chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).opensRange =
      (chartι R x).opensRange := by
  ext z
  obtain ⟨K, _, _, N, p, rfl⟩ := exists_toSchemeHom_apply_eq R M k z
  change (toSchemeHom N ≫ pluckerHom R M k) p ∈
      (chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).opensRange ↔
    toSchemeHom N p ∈ (chartι R x).opensRange
  rw [toSchemeHom_comp_pluckerHom, toSchemeHom_apply_mem_opensRange_chartι_iff,
    toSchemeHom_apply_mem_opensRange_chartι_iff]
  exact pluckerBaseChange_mem_chart_iff N x

variable (R M k) in
/-- **The Plücker charts cover `G(1, ⋀ᵏ M)`.** The charts of `G(1, ⋀ᵏ M)` at the wedges
`x₁ ∧ ⋯ ∧ xₖ`, `x : Fin k → M`, cover it, since these wedges span `⋀ᵏ M`. -/
theorem iSup_opensRange_chartι_ιMulti :
    ⨆ x : Fin k → M, (chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨K, _, _, N, p, rfl⟩ := exists_toSchemeHom_apply_eq R (⋀[R]^k M) 1 z
  let v : (Fin k → M) → K ⊗[R] ⋀[R]^k M := fun x ↦ (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R k x
  -- the vectors `1 ⊗ (x₁ ∧ ⋯ ∧ xₖ)` span `K ⊗[R] ⋀ᵏ M`
  have hv : N.toSubmodule ⊔ Submodule.span K (Set.range v) = ⊤ := by
    refine eq_top_iff.2 (le_sup_of_le_right ?_)
    rw [← Submodule.baseChange_top K, ← exteriorPower.ιMulti_span, Submodule.baseChange_span,
      ← Set.range_comp]
    rfl
  -- over a field, one of the chart loci is the unit ideal
  obtain ⟨y, hy⟩ : ∃ y : Fin 1 → (Fin k → M), chartLocus N (v ∘ y) = ⊤ := by
    by_contra! h
    have h' := iSup_chartLocus_eq_top N v hv
    simp only [fun y ↦ (Ideal.eq_bot_or_top (chartLocus N (v ∘ y))).resolve_right (h y),
      iSup_bot, bot_ne_top] at h'
  rw [chartLocus_eq_top_iff] at hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨y 0, ?_⟩
  rw [toSchemeHom_apply_mem_opensRange_chartι_iff]
  convert hy using 2
  ext j
  rw [Subsingleton.elim j 0]
  rfl

/-- **The Plücker morphism on a chart is a base change of the Plücker map on charts.** The square
formed by `Spec` of `pluckerChartHom R x`, the charts at `x` and at `x₁ ∧ ⋯ ∧ xₖ`, and
`pluckerHom` is a pullback square. -/
theorem isPullback_pluckerHom_chartι (x : Fin k → M) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
        ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x)))
      (chartι R x) (chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)) (pluckerHom R M k) :=
  IsOpenImmersion.isPullback _ _ _ _ (specMap_pluckerChartHom_chartι R x).symm
    (pluckerHom_preimage_opensRange_chartι x)

variable (R M k) in
/-- **The Plücker morphism is a closed immersion.** For every module `M` over `R`, the Plücker
morphism `G(k, M) ⟶ G(1, ⋀ᵏ M)` is a closed immersion: over the chart of `G(1, ⋀ᵏ M)` at
`x₁ ∧ ⋯ ∧ xₖ` it is `Spec` of the surjection `pluckerChartHom R x`, and these charts cover
`G(1, ⋀ᵏ M)`. -/
instance isClosedImmersion_pluckerHom : IsClosedImmersion (pluckerHom R M k) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ (iSup_opensRange_chartι_ιMulti R M k)
    fun x ↦ ?_
  have h := (isPullback_pluckerHom_chartι (R := R) x).flip
  have := isClosedImmersion_specMap_pluckerChartHom R x
  refine (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictOpensRange _ _)).2 ?_
  refine (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk h.isoPullback (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact h.isoPullback_hom_snd))).1 this

end Module.Grassmannian
