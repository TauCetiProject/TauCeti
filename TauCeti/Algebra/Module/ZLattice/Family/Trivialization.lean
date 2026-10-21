/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Module.ZLattice.Family.Basic

/-!
# The global trivialization of a continuous family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices in a finite-dimensional real
normed space `E`, as in `TauCeti.Algebra.Module.ZLattice.Family.Basic`, and let `b` be a
`ℤ`-basis of `Λ` indexed by `ι`. At each `y` the periods `P y (b i)` form a real basis of `E`
(`TauCeti.periodBasis`), whose coordinate map `F_y⁻¹ : E ≃ ℝ^ι` carries the lattice
`LinearMap.range (P y)` onto the standard lattice `ℤ^ι = span ℤ (range (Pi.basisFun ℝ ι))`.
Both `F_y` and `F_y⁻¹` depend continuously on `y` in the operator norm.

Consequently `[y, v] ↦ (y, [F_y⁻¹ v])` descends to a homeomorphism
`(Y × E)/Λ ≃ₜ Y × ℝ^ι/ℤ^ι` over `Y` (`TauCeti.periodTrivialization`), from the orbit space of the
period translation action to the product of the parameter space with one fixed torus. The
trivialization is real-linear on fibres, not complex-linear: when `E` is a complex vector space
the complex structure of the fibre `E ⧸ LinearMap.range (P y)` varies with `y`, and a family whose
period ratio varies is not holomorphically a product.

## Main results

* `TauCeti.periodBasis_equivFun_mem_span_iff`: the coordinates of `v` in the period basis at `y` are
  integers exactly when `v` is a period at `y`.
* `TauCeti.continuous_periodBasis_equivFunL_symm`, `TauCeti.continuous_periodBasis_equivFunL`:
  the frame `F_y` and its inverse depend continuously on `y`.
* `TauCeti.periodTrivialization`: the homeomorphism `(Y × E)/Λ ≃ₜ Y × ℝ^ι/ℤ^ι` over `Y`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Set Function Submodule

namespace TauCeti

variable {Y : Type*} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι : Type*} [Finite ι] (b : Basis ι ℤ Λ) (hinj : ∀ y, Injective (P y))

/-- **Integral coordinates detect periods.** The coordinates of `v` in the period basis at `y`
lie in the standard lattice `ℤ^ι` exactly when `v` is a period at `y`. -/
theorem periodBasis_equivFun_mem_span_iff (y : Y) (v : E) :
    (periodBasis P b hinj y).equivFun v ∈ span ℤ (range (Pi.basisFun ℝ ι)) ↔
      v ∈ LinearMap.range (P y) := by
  rw [← span_range_periodBasis P b hinj y, Basis.mem_span_iff_repr_mem,
    Basis.mem_span_iff_repr_mem]
  simp

/-- The period translation relation, read in the period frame: the classes of `(y, v)` and
`(y', v')` agree exactly when `y = y'` and the period coordinates of `v` and `v'` at `y` differ by
an element of the standard lattice. -/
private theorem orbitRel_periodAddAction_iff {p q : Y × E} :
    letI := periodAddAction P
    AddAction.orbitRel Λ (Y × E) p q ↔ p.1 = q.1 ∧
      AddAction.orbitRel (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ)
        ((periodBasis P b hinj q.1).equivFun p.2) ((periodBasis P b hinj q.1).equivFun q.2) := by
  let _ := periodAddAction P
  rw [AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff, AddAction.orbitRel_apply,
    AddAction.mem_orbit_iff, ← periodBasis_equivFun_mem_span_iff P b hinj, map_sub]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨⟨_, h⟩, by simp [Submodule.vadd_def]⟩, ?_⟩
  rintro ⟨l, hl⟩
  simp [← hl, Submodule.vadd_def]

variable [TopologicalSpace Y]

/-- **Continuity of the period frame.** The real linear isomorphism `F_y : ℝ^ι → E`,
`x ↦ ∑ i, x i • P y (b i)`, depends continuously on `y` in the operator norm. -/
theorem continuous_periodBasis_equivFunL_symm (hcont : ∀ l, Continuous fun y ↦ P y l) :
    Continuous fun y ↦ ((periodBasis P b hinj y).equivFunL.symm : (ι → ℝ) →L[ℝ] E) := by
  have := Fintype.ofFinite ι
  have h : (fun y ↦ ((periodBasis P b hinj y).equivFunL.symm : (ι → ℝ) →L[ℝ] E)) =
      fun y ↦ ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (P y (b i)) := by
    ext1 y
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_eq]
    ext j
    classical
    simp [Finsupp.single_apply]
  rw [h]
  exact continuous_finsetSum _ fun i _ ↦
    (ContinuousLinearMap.smulRightL ℝ (ι → ℝ) E (ContinuousLinearMap.proj i)).continuous.comp
      (hcont (b i))

/-- **Continuity of the inverse period frame.** The coordinate map `F_y⁻¹ : E → ℝ^ι` of the period
basis depends continuously on `y` in the operator norm. -/
theorem continuous_periodBasis_equivFunL (hcont : ∀ l, Continuous fun y ↦ P y l) :
    Continuous fun y ↦ ((periodBasis P b hinj y).equivFunL : E →L[ℝ] ι → ℝ) := by
  have := Fintype.ofFinite ι
  have h : (fun y ↦ ((periodBasis P b hinj y).equivFunL : E →L[ℝ] ι → ℝ)) =
      fun y ↦ ((periodBasis P b hinj y).equivFunL.symm : (ι → ℝ) →L[ℝ] E).inverse := by
    ext1 y
    rw [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
  rw [h, continuous_iff_continuousAt]
  exact fun y ↦ ContinuousAt.comp (g := ContinuousLinearMap.inverse)
    (contDiffAt_map_inverse (n := 0) (periodBasis P b hinj y).equivFunL.symm).continuousAt
    (continuous_periodBasis_equivFunL_symm P b hinj hcont).continuousAt

/-- **The global trivialization** of a continuous family of full lattices. For a `ℤ`-basis `b`
of `Λ` indexed by `ι`, the map `[y, v] ↦ (y, [F_y⁻¹ v])`, with `F_y⁻¹` the coordinate map of the
period basis at `y`, is a homeomorphism from the orbit space of the period translation action to
the product of `Y` with the fixed torus `ℝ^ι/ℤ^ι`. It lies over `Y`
(`TauCeti.fst_periodTrivialization`), and on each fibre it is induced by the real linear
isomorphism `F_y⁻¹`. -/
noncomputable def periodTrivialization (hcont : ∀ l, Continuous fun y ↦ P y l) :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ₜ
      Y × AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ) :=
  letI := periodAddAction P
  -- The coordinates `(y, v) ↦ (y, F_y⁻¹ v)` and their inverse, before passing to quotients.
  have hfwd : Continuous fun p : Y × E ↦ (periodBasis P b hinj p.1).equivFunL p.2 := by
    have := Fintype.ofFinite ι
    exact ((continuous_periodBasis_equivFunL P b hinj hcont).comp continuous_fst).clm_apply
      continuous_snd
  have hbwd : Continuous fun p : Y × (ι → ℝ) ↦
      (periodBasis P b hinj p.1).equivFunL.symm p.2 := by
    have := Fintype.ofFinite ι
    exact ((continuous_periodBasis_equivFunL_symm P b hinj hcont).comp continuous_fst).clm_apply
      continuous_snd
  { toFun := Quotient.lift
      (fun p ↦ (p.1, Quotient.mk _ ((periodBasis P b hinj p.1).equivFun p.2)))
      fun p q h ↦ by
        obtain ⟨h₁, h₂⟩ := (orbitRel_periodAddAction_iff P b hinj).1 h
        rw [h₁]
        exact Prod.ext rfl (Quotient.sound h₂)
    invFun r := Quotient.lift
      (fun x ↦ Quotient.mk _ (r.1, (periodBasis P b hinj r.1).equivFun.symm x))
      (fun x x' h ↦ Quotient.sound <| (orbitRel_periodAddAction_iff P b hinj).2
        ⟨rfl, by rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩) r.2
    left_inv := by
      rintro ⟨p⟩
      exact congrArg (Quotient.mk _)
        (Prod.ext rfl ((periodBasis P b hinj p.1).equivFun.symm_apply_apply p.2))
    right_inv := by
      rintro ⟨y, ⟨x⟩⟩
      exact Prod.ext rfl
        (congrArg (Quotient.mk _) ((periodBasis P b hinj y).equivFun.apply_symm_apply x))
    continuous_toFun := Continuous.quotient_lift
      (continuous_fst.prodMk (continuous_quot_mk.comp hfwd)) _
    continuous_invFun := by
      -- `Y × ℝ^ι → Y × ℝ^ι/ℤ^ι` is an open quotient map, so continuity can be checked upstairs.
      refine (IsOpenQuotientMap.id.prodMap
        AddAction.isOpenQuotientMap_quotientMk).continuous_comp_iff.1 ?_
      exact continuous_quot_mk.comp (continuous_fst.prodMk hbwd) }

variable (hcont : ∀ l, Continuous fun y ↦ P y l)

/-- The trivialization sends the class of `(y, v)` to `y` and the class of the period coordinates
of `v` at `y`. -/
@[simp] theorem periodTrivialization_mk (p : Y × E) :
    letI := periodAddAction P
    periodTrivialization P b hinj hcont (Quotient.mk _ p) =
      (p.1, Quotient.mk _ ((periodBasis P b hinj p.1).equivFun p.2)) := (rfl)

/-- The inverse trivialization sends `y` and the class of `x` to the class of
`(y, ∑ i, x i • P y (b i))`. -/
@[simp] theorem periodTrivialization_symm_mk (y : Y) (x : ι → ℝ) :
    letI := periodAddAction P
    (periodTrivialization P b hinj hcont).symm (y, Quotient.mk _ x) =
      Quotient.mk _ (y, (periodBasis P b hinj y).equivFun.symm x) := (rfl)

/-- The trivialization lies over the parameter space. -/
@[simp] theorem fst_periodTrivialization
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (periodTrivialization P b hinj hcont z).1 = torusFamilyProjection P z := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end TauCeti
