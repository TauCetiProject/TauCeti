/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Fundamental domains of integer spans

This file records geometric properties of the standard fundamental domain associated to a basis.
Its convexity makes lattice cells preconnected, so cells crossing the boundary of a set can be
detected by their intersection with the frontier in lattice-point counting arguments.

The coordinates of a real basis `b` carry any additive Haar measure `μ` to Lebesgue measure on
`ι → ℝ`, scaled by the measure of the fundamental domain of `b`
(`Module.Basis.addHaar_eq_measure_fundamentalDomain_mul_volume_image`).

It also records basic facts about lattices: a full lattice is the `ℤ`-span of a basis of
the ambient space, and membership in the pull-back `ZLattice.comap` of a lattice is membership of
the image. The pull-back `L ∩ V` of a discrete subgroup to a subspace `V` is again discrete, and
so is the pull-back of a discrete subgroup or of a full lattice along a linear isometry
equivalence.

## Main results

* `ZSpan.convex_fundamentalDomain`: the fundamental domain of a real basis is convex.
* `ZSpan.eq_of_sub_mem_fundamentalDomain`: two integer-span translates placing a point in the
  fundamental domain are equal.
* `ZSpan.fundamentalDomain_pi_basis`: the fundamental domain of a product basis is the product of
  the fundamental domains.
* `Module.Basis.addHaar_eq_measure_fundamentalDomain_mul_volume_image`: `μ s` is the measure of
  the fundamental domain of `b` times the Lebesgue measure of the coordinate image of `s`.
* `Module.Basis.mem_span_basisFun_iff`: a point of `ℝ^ι` lies in the standard lattice `ℤ^ι`
  exactly when it is the coordinate vector of an element of `Λ` in a `ℤ`-basis of `Λ`.
* `ZLattice.exists_basis_span_eq`: a full lattice is the `ℤ`-span of a basis of the ambient space.
* `ZLattice.exists_forall_ne_zero_lt_norm`: a finite-dimensional real normed space has full
  lattices all of whose nonzero vectors are longer than a prescribed bound.
* `ZLattice.mem_comap`: `x ∈ ZLattice.comap K L e` if and only if `e x ∈ L`.
* `ZLattice.instDiscreteTopologyComapSubtype`: the restriction `L ∩ V` of a discrete subgroup `L`
  to a subspace `V` is discrete.
* `ZLattice.instDiscreteTopologyComapLinearIsometryEquiv`,
  `ZLattice.instIsZLatticeComapLinearIsometryEquiv`: the pull-back of a discrete subgroup, or of a
  full lattice, along a linear isometry equivalence is again one.
* `TauCeti.discreteTopology_span_one`: the integer span of `1` in `ℝ` is discrete.
-/

public section

open MeasureTheory Module Set

namespace TauCeti

/-- The integer lattice in the real line has the discrete topology. -/
instance discreteTopology_span_one :
    DiscreteTopology (Submodule.span ℤ {1} : Submodule ℤ ℝ) := by
  rw [← Set.range_eq_singleton (Module.Basis.singleton_apply Unit ℝ)]
  infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The fundamental domain of a basis is convex: it is cut out by the conditions
`b.repr x i ∈ [0, 1)`, one convex condition per coordinate. -/
theorem _root_.ZSpan.convex_fundamentalDomain (β : Basis ι ℝ E) :
    Convex ℝ (ZSpan.fundamentalDomain β) := by
  intro x hx y hy a t ha ht hat
  rw [ZSpan.mem_fundamentalDomain] at hx hy ⊢
  intro i
  simpa using convex_Ico (0 : ℝ) 1 (hx i) (hy i) ha ht hat

/-- Two vectors in the integer span that translate the same point into the fundamental domain
in subtraction form are equal. -/
theorem _root_.ZSpan.eq_of_sub_mem_fundamentalDomain [Finite ι] (β : Basis ι ℝ E)
    {x w₁ w₂ : E} (hw₁ : w₁ ∈ Submodule.span ℤ (Set.range β))
    (hw₂ : w₂ ∈ Submodule.span ℤ (Set.range β))
    (h₁ : x - w₁ ∈ ZSpan.fundamentalDomain β)
    (h₂ : x - w₂ ∈ ZSpan.fundamentalDomain β) : w₁ = w₂ := by
  have hn₁ : -w₁ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₁
  have hn₂ : -w₂ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₂
  have subtype_vadd (w : E) (hw : w ∈ Submodule.span ℤ (Set.range β)) :
      (⟨w, hw⟩ : Submodule.span ℤ (Set.range β)) +ᵥ x = w + x := rfl
  have heq : (⟨-w₁, hn₁⟩ : Submodule.span ℤ (Set.range β)) = ⟨-w₂, hn₂⟩ :=
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain β x).unique
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₁)
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₂)
  exact neg_injective (congrArg Subtype.val heq)

/-- The coordinates of a real basis `b` carry an additive Haar measure `μ` to Lebesgue measure on
`ι → ℝ`, scaled by the measure of the fundamental domain of `b`: every set `s` has
`μ s = μ (fundamentalDomain b) * volume (b.equivFun '' s)`. -/
theorem _root_.Module.Basis.addHaar_eq_measure_fundamentalDomain_mul_volume_image [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (s : Set E) :
    μ s = μ (ZSpan.fundamentalDomain b) * volume (b.equivFun '' s) := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  set φ := b.equivFun
  have hφ : MeasurableEmbedding φ :=
    φ.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have : (μ.map φ).IsAddHaarMeasure := φ.toContinuousLinearEquiv.isAddHaarMeasure_map μ
  -- The image of `μ` is a multiple `c • volume`, and `c` is the measure of the fundamental domain,
  -- whose image is the unit cube.
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, μ.map φ = c • volume :=
    ⟨_, by rw [← addHaarMeasure_eq_volume_pi ι]; exact Measure.addHaarMeasure_unique _ _⟩
  have hμ (t : Set E) : μ t = c * volume (φ '' t) := by
    rw [← smul_eq_mul, ← _root_.smul_apply, ← hc, hφ.map_apply,
      Set.preimage_image_eq t φ.injective]
  have hy (y : ι → ℝ) (i : ι) : b.repr (φ.symm y) i = y i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hF : φ '' ZSpan.fundamentalDomain b = Set.pi Set.univ fun _ ↦ Set.Ico (0 : ℝ) 1 := by
    ext y
    simp only [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, ZSpan.mem_fundamentalDomain,
      hy]
    simp
  rw [hμ s, hμ, hF, Real.volume_pi_Ico]
  simp

/-- The fundamental domain of a product basis `Pi.basis b` is the product of the fundamental
domains of the factors `b i`. -/
theorem _root_.ZSpan.fundamentalDomain_pi_basis {η : Type*} [Fintype η] {F : η → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)] {κ : η → Type*}
    (b : ∀ i, Basis (κ i) ℝ (F i)) :
    ZSpan.fundamentalDomain (Pi.basis b) = Set.univ.pi fun i ↦ ZSpan.fundamentalDomain (b i) := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, Sigma.forall]

/-- A point of `ℝ^ι` lies in the standard lattice `ℤ^ι` exactly when it is the vector of
coordinates in the `ℤ`-basis `b` of some `l : Λ`, read in `ℝ`. -/
theorem _root_.Module.Basis.mem_span_basisFun_iff [Finite ι] {Λ : Type*} [AddCommGroup Λ]
    (b : Basis ι ℤ Λ) {x : ι → ℝ} :
    x ∈ Submodule.span ℤ (range (Pi.basisFun ℝ ι)) ↔ ∃ l : Λ, (fun i ↦ (b.repr l i : ℝ)) = x := by
  have := Fintype.ofFinite ι
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose z hz using h
    have hrepr : ⇑(b.repr (b.equivFun.symm z)) = z := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact ⟨b.equivFun.symm z, funext fun i ↦ by rw [congrFun hrepr i]; simpa using hz i⟩
  · rintro ⟨l, rfl⟩ i
    simp

end TauCeti

universe u

namespace ZLattice

/-- A vector lies in the pull-back of a lattice along a linear map exactly when its image lies in
the lattice. -/
@[simp]
theorem mem_comap (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)
    (e : F →ₗ[K] E) {x : F} : x ∈ ZLattice.comap K L e ↔ e x ∈ L :=
  Iff.rfl

/-- The restriction `L ∩ V` of a discrete subgroup `L` to a subspace `V`, viewed as a subgroup of
`V`, is discrete. -/
instance instDiscreteTopologyComapSubtype {K : Type*} [NormedField K] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace K E] (L : Submodule ℤ E) [DiscreteTopology L]
    (V : Submodule K E) : DiscreteTopology (ZLattice.comap K L V.subtype) :=
  comap_discreteTopology K L continuous_subtype_val V.injective_subtype

section LinearIsometryEquiv

variable {K : Type*} [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E) [DiscreteTopology L]
  (e : F ≃ₗᵢ[K] E)

-- Mathlib states these instances for the map underlying a continuous linear equivalence; the
-- map underlying a linear isometry equivalence is the same by definition, but instance search
-- does not see through `LinearIsometryEquiv.toContinuousLinearEquiv`.
/-- The pull-back of a discrete subgroup along a linear isometry equivalence is discrete. -/
instance instDiscreteTopologyComapLinearIsometryEquiv :
    DiscreteTopology (ZLattice.comap K L e.toLinearEquiv.toLinearMap) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap K L e.toContinuousLinearEquiv.toLinearMap))

/-- The pull-back of a full lattice along a linear isometry equivalence is a full lattice. -/
instance instIsZLatticeComapLinearIsometryEquiv [IsZLattice K L] :
    IsZLattice K (ZLattice.comap K L e.toLinearEquiv.toLinearMap) :=
  inferInstanceAs (IsZLattice K (ZLattice.comap K L e.toContinuousLinearEquiv.toLinearMap))

end LinearIsometryEquiv

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K] {E : Type u} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]

/-- A full lattice is the `ℤ`-span of a `K`-basis of the ambient space, indexed by a finite
type. -/
theorem exists_basis_span_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι K E),
      Submodule.span ℤ (Set.range b) = L :=
  have := module_finite K L
  have := module_free K L
  ⟨_, inferInstance, Classical.decEq _, (Free.chooseBasis ℤ L).ofZLatticeBasis K L,
    (Free.chooseBasis ℤ L).ofZLatticeBasis_span K L⟩

/-- A finite-dimensional real normed space has full lattices whose nonzero vectors are all longer
than any prescribed `R`: pull back the integer span of a basis along `x ↦ c⁻¹ • x` for a large
`c`. In particular a bounded set meets none of its translates by nonzero vectors of such a
lattice once `R` exceeds its diameter. -/
theorem exists_forall_ne_zero_lt_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (R : ℝ) :
    ∃ (L : Submodule ℤ F) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∀ ℓ ∈ L, ℓ ≠ 0 → R < ‖ℓ‖ := by
  set L₀ := Submodule.span ℤ (Set.range (Module.finBasis ℝ F))
  -- The integer span of a basis is discrete, so its nonzero vectors have norm at least some `δ`.
  obtain ⟨δ, hδ, hL₀⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set L₀))
  set c : ℝ := (|R| + 1) / δ
  have hc : 0 < c := by positivity
  let e : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')⁻¹
  refine ⟨ZLattice.comap ℝ L₀ e.toLinearMap, inferInstance, inferInstance, fun ℓ hℓ hne ↦ ?_⟩
  have hmem : c⁻¹ • ℓ ∈ L₀ := by
    simpa [mem_comap, e, Units.smul_def] using hℓ
  have hδℓ : δ ≤ ‖c⁻¹ • ℓ‖ := by
    by_contra! h
    have h0 := hL₀ ⟨_, hmem⟩ (by simpa [dist_eq_norm] using h)
    exact smul_ne_zero (inv_ne_zero hc.ne') hne (congrArg Subtype.val h0)
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_eq_div, le_div_iff₀ hc] at hδℓ
  have hcδ : δ * c = |R| + 1 := by
    simp only [c]
    field_simp
  linarith [le_abs_self R]

end ZLattice
