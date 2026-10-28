/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

import TauCeti.Analysis.Normed.Group.Int

/-!
# Continuous families of full lattices

Let `Λ` be a finite free `ℤ`-module, `E` a finite-dimensional real normed space and `Y` a
topological space. A *period family* is a map `P : Y → (Λ →ₗ[ℤ] E)` such that each period
`y ↦ P y l` is continuous and each `P y` is injective with discrete, full range: that is,
`LinearMap.range (P y)` is a full lattice of `E` in the sense of `IsZLattice ℝ`. A
holomorphic family of complex tori `E ⧸ LinearMap.range (P y)` is described by such data.

Pointwise discreteness says that each lattice `LinearMap.range (P y)` has nonzero vectors of
norm bounded below. This file proves the bound is locally uniform in `y`: on every compact
`K ⊆ Y` there is one `c > 0` with `c ≤ ‖P y l‖` for all `y ∈ K` and all `l ≠ 0`
(`TauCeti.exists_pos_le_norm_period_of_isCompact`). After choosing a `ℤ`-basis `b` of `Λ` the
statement is a uniform bound for the inverses of the real linear isomorphisms
`x ↦ ∑ i, x i • P y (b i)` (`TauCeti.exists_pos_mul_norm_le_norm_sum_smul_period_of_isCompact`).
The proof is compactness of `K` times the unit sphere of `ι → ℝ`, on which the norm of this
combination is continuous and positive, a `ℤ`-basis of a full lattice being an `ℝ`-basis of `E`
(`Module.Basis.ofZLatticeBasis`).

Consequently only finitely many `l` have `‖P y l‖ ≤ R` for some `y ∈ K`
(`TauCeti.finite_setOf_exists_norm_period_le`). This is exactly what makes the period
translation action `l +ᵥ (y, v) = (y, v + P y l)` of `Λ` on `Y × E`
(`TauCeti.periodAddAction`) properly discontinuous, whose orbit space is the total space of the
family of tori. The action is free and acts by homeomorphisms. The first projection descends to
the projection of the family of tori to its parameter space
(`TauCeti.torusFamilyProjection`), a continuous open surjection.

The `ℤ`-basis of the full lattice `LinearMap.range (P y)` given by the periods of a `ℤ`-basis `b`
of `Λ` is packaged as the real basis `TauCeti.periodBasis P b hinj y` of `E`. The global
trivialization of the family built from it is in
`TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd`.

## Main definitions

* `TauCeti.periodBasis`: the periods at `y` of a `ℤ`-basis of `Λ`, as a real basis of `E`.
* `TauCeti.periodAddAction`: the period translation action of `Λ` on `Y × E`.
* `TauCeti.torusFamilyProjection`: the projection `(Y × E)/Λ → Y` descended from `Prod.fst`.

## Main results

* `TauCeti.exists_pos_mul_norm_le_norm_sum_smul_period_of_isCompact`: on a compact set of
  parameters, the real linear maps `x ↦ ∑ i, x i • P y (b i)` are uniformly bounded below.
* `TauCeti.exists_pos_le_norm_period_of_isCompact`: uniform separation of nonzero periods on a
  compact set of parameters.
* `TauCeti.finite_setOf_exists_norm_period_le`: on a compact set of parameters, only finitely
  many periods have norm at most `R`.
* `TauCeti.properlyDiscontinuousVAdd_periodAddAction`, `TauCeti.isCancelVAdd_periodAddAction`,
  `TauCeti.continuousConstVAdd_periodAddAction`: the period translation action on `Y × E` is
  properly discontinuous, free, and continuous.
* `TauCeti.mem_orbit_periodAddAction_iff`: two points lie in one orbit exactly when they have the
  same parameter `y` and differ by a period at `y`.
* `TauCeti.continuous_torusFamilyProjection`, `TauCeti.isOpenMap_torusFamilyProjection`: the
  projection of the family of tori is continuous and open.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Set Metric Function

namespace TauCeti

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Y → Λ →ₗ[ℤ] E)

section Separation

variable [FiniteDimensional ℝ E] [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] {K : Set Y}

/-- The **period basis** at `y`: the periods `P y (b i)` of a `ℤ`-basis `b` of `Λ`, viewed as a
real basis of `E`. They form a `ℤ`-basis of the full lattice `LinearMap.range (P y)`, hence a real
basis of `E`. Its inverse coordinate map `x ↦ ∑ i, x i • P y (b i)` is the real linear
isomorphism `ℝ^ι ≃ E` carrying the standard lattice `ℤ^ι` onto the periods at `y`. -/
noncomputable def periodBasis {ι : Type*} (b : Basis ι ℤ Λ)
    (hinj : ∀ y, Injective (P y)) (y : Y) : Basis ι ℝ E :=
  (b.map (LinearEquiv.ofInjective (P y) (hinj y))).ofZLatticeBasis ℝ (LinearMap.range (P y))

omit [TopologicalSpace Y] in
/-- The `i`-th vector of the period basis at `y` is the period `P y (b i)`. -/
@[simp] theorem periodBasis_apply {ι : Type*} (b : Basis ι ℤ Λ)
    (hinj : ∀ y, Injective (P y)) (y : Y) (i : ι) : periodBasis P b hinj y i = P y (b i) := by
  simp [periodBasis]

omit [TopologicalSpace Y] in
/-- The period basis at `y` spans the lattice of periods at `y` over `ℤ`. -/
theorem span_range_periodBasis {ι : Type*} (b : Basis ι ℤ Λ)
    (hinj : ∀ y, Injective (P y)) (y : Y) :
    Submodule.span ℤ (range (periodBasis P b hinj y)) = LinearMap.range (P y) :=
  Basis.ofZLatticeBasis_span ..

omit [TopologicalSpace Y] in
/-- The coordinates of a period `P y l` in the period basis at `y` are the integer coordinates of
`l` in `b`. -/
@[simp] theorem periodBasis_repr_period {ι : Type*} (b : Basis ι ℤ Λ)
    (hinj : ∀ y, Injective (P y)) (y : Y) (l : Λ) (i : ι) :
    (periodBasis P b hinj y).repr (P y l) i = b.repr l i := by
  have h := Basis.ofZLatticeBasis_repr_apply ℝ (LinearMap.range (P y))
    (b.map (LinearEquiv.ofInjective (P y) (hinj y))) (LinearEquiv.ofInjective (P y) (hinj y) l) i
  rwa [Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h

/-- **Uniform bound for inverse period maps.** For a basis `b` of `Λ`, the real linear maps
`x ↦ ∑ i, x i • P y (b i)` are bounded below by one constant `c > 0` as `y` ranges over a
compact set: `c * ‖x‖ ≤ ‖∑ i, x i • P y (b i)‖`. -/
theorem exists_pos_mul_norm_le_norm_sum_smul_period_of_isCompact {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ Λ) (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (hK : IsCompact K) :
    ∃ c > 0, ∀ y ∈ K, ∀ x : ι → ℝ, c * ‖x‖ ≤ ‖∑ i, x i • P y (b i)‖ := by
  set f : Y × (ι → ℝ) → E := fun p ↦ ∑ i, p.2 i • P p.1 (b i) with hf_def
  have hf : Continuous f := continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp continuous_snd).smul ((hcont (b i)).comp continuous_fst)
  -- On `K × sphere 0 1` the combination does not vanish: the periods of a `ℤ`-basis of `Λ` form
  -- the real basis `periodBasis P b hinj y` of `E`.
  have hpos : ∀ p ∈ K ×ˢ sphere (0 : ι → ℝ) 1, 0 < ‖f p‖ := by
    rintro ⟨y, x⟩ ⟨-, hx⟩
    refine norm_pos_iff.2 fun h0 ↦ ?_
    have hli : LinearIndependent ℝ fun i ↦ P y (b i) := by
      rw [← funext (periodBasis_apply P b hinj y)]
      exact (periodBasis P b hinj y).linearIndependent
    have hx0 : x = 0 := funext (Fintype.linearIndependent_iff.1 hli x h0)
    simp [hx0] at hx
  obtain ⟨c, hc, hcK⟩ :=
    (hK.prod (isCompact_sphere 0 1)).exists_forall_le' hf.norm.continuousOn hpos
  refine ⟨c, hc, fun y hy x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  -- Rescale `x` to the unit sphere and use homogeneity of the combination.
  have h := hcK (y, ‖x‖⁻¹ • x) ⟨hy, by simp [norm_smul, hxn.ne']⟩
  simp only [hf_def, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, norm_smul,
    norm_inv, norm_norm] at h
  rwa [le_inv_mul_iff₀ hxn, mul_comm] at h

/-- **Uniform bound for lattice coordinates.** For a basis `b` of `Λ`, on a compact set of
parameters the coordinates of `l` are bounded by a fixed multiple of the norm of its period:
`c * ‖b.equivFun l‖ ≤ ‖P y l‖`. -/
theorem exists_pos_mul_norm_equivFun_le_norm_period_of_isCompact {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ Λ) (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (hK : IsCompact K) :
    ∃ c > 0, ∀ y ∈ K, ∀ l, c * ‖b.equivFun l‖ ≤ ‖P y l‖ := by
  obtain ⟨c, hc, h⟩ := exists_pos_mul_norm_le_norm_sum_smul_period_of_isCompact P b hcont hinj hK
  refine ⟨c, hc, fun y hy l ↦ ?_⟩
  have hl : P y l = ∑ i, ((b.equivFun l i : ℤ) : ℝ) • P y (b i) := by
    conv_lhs => rw [← b.sum_equivFun l]
    simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  have hn := pi_norm_intCast_real (b.equivFun l)
  have := h y hy fun i ↦ (b.equivFun l i : ℝ)
  rwa [hn, ← hl] at this

variable [Free ℤ Λ] [Module.Finite ℤ Λ]

/-- **Uniform period separation on compact sets.** On a compact set `K` of parameters there is
a single `c > 0` bounding below the norm of every nonzero period at every point of `K`. -/
theorem exists_pos_le_norm_period_of_isCompact (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) (hK : IsCompact K) :
    ∃ c > 0, ∀ y ∈ K, ∀ l ≠ 0, c ≤ ‖P y l‖ := by
  let b := Free.chooseBasis ℤ Λ
  obtain ⟨c, hc, h⟩ :=
    exists_pos_mul_norm_equivFun_le_norm_period_of_isCompact P b hcont hinj hK
  refine ⟨c, hc, fun y hy l hl ↦ (le_mul_of_one_le_right hc.le ?_).trans (h y hy l)⟩
  -- A nonzero integer coordinate vector has sup norm at least one.
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun l i ≠ 0 := by
    by_contra! h0
    exact hl (b.equivFun.injective (by ext i; simp [h0 i]))
  calc (1 : ℝ) ≤ ‖b.equivFun l i‖ := by
        rw [Int.norm_eq_abs]
        exact_mod_cast Int.one_le_abs hi
    _ ≤ ‖b.equivFun l‖ := norm_le_pi_norm _ i

/-- On a compact set `K` of parameters, only finitely many `l` have a period `P y l` of norm at
most `R` at some point `y ∈ K`. -/
theorem finite_setOf_exists_norm_period_le (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) (hK : IsCompact K) (R : ℝ) :
    {l : Λ | ∃ y ∈ K, ‖P y l‖ ≤ R}.Finite := by
  let b := Free.chooseBasis ℤ Λ
  obtain ⟨c, hc, h⟩ :=
    exists_pos_mul_norm_equivFun_le_norm_period_of_isCompact P b hcont hinj hK
  have hball :=
    (isCompact_closedBall (0 : Free.ChooseBasisIndex ℤ Λ → ℤ) (R / c)).finite_of_discrete
  refine (hball.preimage b.equivFun.injective.injOn).subset ?_
  rintro l ⟨y, hy, hl⟩
  rw [mem_preimage, mem_closedBall_zero_iff, le_div_iff₀' hc]
  exact (h y hy l).trans hl

end Separation

/-! ### The period translation action -/

section Action

variable {Y : Type*} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E)

/-- The translation action of `Λ` on `Y × E` by periods, `l +ᵥ (y, v) = (y, v + P y l)`. Its
orbit space is the total space of the family of tori `E ⧸ LinearMap.range (P y)` over `Y`. -/
@[instance_reducible]
def periodAddAction : AddAction Λ (Y × E) where
  vadd l p := (p.1, p.2 + P p.1 l)
  zero_vadd p := by
    -- Unfold the action field to expose the concrete translation.
    change (p.1, p.2 + P p.1 0) = p
    simp
  add_vadd l l' p := by
    -- Unfold the action field to expose the concrete translation.
    change (p.1, p.2 + P p.1 (l + l')) = (p.1, p.2 + P p.1 l' + P p.1 l)
    rw [map_add, add_comm (P p.1 l), add_assoc]

/-- The period translation action fixes the parameter and translates by the period. -/
@[simp] theorem periodAddAction_vadd (l : Λ) (p : Y × E) :
    letI := periodAddAction P
    l +ᵥ p = (p.1, p.2 + P p.1 l) := (rfl)

/-- Two points of `Y × E` lie in one period orbit exactly when they have the same parameter `y`
and their difference is a period at `y`. -/
theorem mem_orbit_periodAddAction_iff {p q : Y × E} :
    letI := periodAddAction P
    q ∈ AddAction.orbit Λ p ↔ q.1 = p.1 ∧ q.2 - p.2 ∈ LinearMap.range (P p.1) := by
  let _ := periodAddAction P
  simp only [AddAction.mem_orbit_iff, periodAddAction_vadd, Prod.ext_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨l, h, hl⟩
    exact ⟨h.symm, l, by rw [← hl, add_sub_cancel_left]⟩
  · rintro ⟨h, l, hl⟩
    exact ⟨l, h.symm, by rw [hl, add_sub_cancel]⟩

/-- The period translation action is free when each period map is injective. -/
theorem isCancelVAdd_periodAddAction (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    IsCancelVAdd Λ (Y × E) := by
  let _ := periodAddAction P
  refine isCancelVAdd_iff_eq_zero_of_vadd_eq.2 fun l p h ↦ hinj p.1 ?_
  simpa using congrArg Prod.snd h

/-- Each period translation is continuous when the periods depend continuously on the
parameter. -/
theorem continuousConstVAdd_periodAddAction [TopologicalSpace Y] [TopologicalSpace E]
    [ContinuousAdd E] (hcont : ∀ l, Continuous fun y ↦ P y l) :
    letI := periodAddAction P
    ContinuousConstVAdd Λ (Y × E) := by
  let _ := periodAddAction P
  refine ⟨fun l ↦ ?_⟩
  simp only [periodAddAction_vadd]
  exact continuous_fst.prodMk (continuous_snd.add ((hcont l).comp continuous_fst))

/-- The projection `(Y × E)/Λ → Y` of the family of tori to its parameter space, descended from
`Prod.fst` along the period translation action. -/
def torusFamilyProjection :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) → Y :=
  letI := periodAddAction P
  Quotient.lift Prod.fst fun _ _ h ↦ ((mem_orbit_periodAddAction_iff P).1 h).1

/-- The projection of the family of tori sends the class of `(y, v)` to `y`. -/
@[simp] theorem torusFamilyProjection_mk (p : Y × E) :
    letI := periodAddAction P
    torusFamilyProjection P (Quotient.mk _ p) = p.1 := (rfl)

/-- The projection of the family of tori is surjective: the class of `(y, 0)` lies over `y`. -/
theorem torusFamilyProjection_surjective : Surjective (torusFamilyProjection P) :=
  fun y ↦ ⟨Quotient.mk _ (y, 0), rfl⟩

/-- The projection of the family of tori is continuous. -/
theorem continuous_torusFamilyProjection [TopologicalSpace Y] [TopologicalSpace E] :
    Continuous (torusFamilyProjection P) :=
  let _ := periodAddAction P
  continuous_fst.quotient_lift _

/-- The projection of the family of tori is open, since it is descended from the open map
`Prod.fst` along the quotient map. -/
theorem isOpenMap_torusFamilyProjection [TopologicalSpace Y] [TopologicalSpace E] :
    IsOpenMap (torusFamilyProjection P) :=
  let _ := periodAddAction P
  IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective isOpenMap_fst

end Action

/-- **Orbit-local finiteness.** The period translation action of a continuous family of full
lattices is properly discontinuous. -/
theorem properlyDiscontinuousVAdd_periodAddAction [FiniteDimensional ℝ E]
    [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    [Free ℤ Λ] [Module.Finite ℤ Λ] (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    ProperlyDiscontinuousVAdd Λ (Y × E) := by
  let _ := periodAddAction P
  refine ⟨fun {K₁ K₂} hK₁ hK₂ ↦ ?_⟩
  obtain ⟨R₁, hR₁⟩ := (hK₁.image continuous_snd).isBounded.exists_norm_le
  obtain ⟨R₂, hR₂⟩ := (hK₂.image continuous_snd).isBounded.exists_norm_le
  refine (finite_setOf_exists_norm_period_le P hcont hinj (hK₁.image continuous_fst)
    (R₁ + R₂)).subset ?_
  rintro l ⟨_, ⟨p, hp, rfl⟩, hq⟩
  refine ⟨p.1, mem_image_of_mem _ hp, ?_⟩
  have h₁ : ‖p.2‖ ≤ R₁ := hR₁ _ (mem_image_of_mem _ hp)
  have h₂ : ‖p.2 + P p.1 l‖ ≤ R₂ := by
    simpa using hR₂ _ (mem_image_of_mem Prod.snd hq)
  calc ‖P p.1 l‖ = ‖(p.2 + P p.1 l) - p.2‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖p.2 + P p.1 l‖ + ‖p.2‖ := norm_sub_le _ _
    _ ≤ R₁ + R₂ := by linarith

end TauCeti
