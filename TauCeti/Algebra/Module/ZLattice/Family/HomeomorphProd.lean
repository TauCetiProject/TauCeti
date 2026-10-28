/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# The global trivialization of a continuous family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices in a finite-dimensional real
normed space `E`, as in `TauCeti.Algebra.Module.ZLattice.Family.Basic`, and let `b` be a
`ℤ`-basis of `Λ` indexed by `ι`. At each `y` the periods `P y (b i)` form a real basis of `E`
(`TauCeti.periodBasis`), whose coordinate map `F_y⁻¹ : E ≃ ℝ^ι` carries the lattice
`LinearMap.range (P y)` onto the standard lattice `ℤ^ι = span ℤ (range (Pi.basisFun ℝ ι))`.
Both `F_y` and `F_y⁻¹` depend continuously on `y` in the operator norm, as does any family of
bases whose vectors depend continuously on the parameter
(`Module.Basis.continuous_equivFunL_of_continuous`).

Consequently `[y, v] ↦ (y, [F_y⁻¹ v])` descends to a homeomorphism
`(Y × E)/Λ ≃ₜ Y × ℝ^ι/ℤ^ι` over `Y` (`TauCeti.torusFamilyHomeomorphProd`), from the orbit space of
the period translation action to the product of the parameter space with one fixed torus, the
quotient `(ι → ℝ) ⧸ span ℤ (range (Pi.basisFun ℝ ι))`. This is the global trivialization of the
family. The
trivialization is real-linear on fibres, not complex-linear: when `E` is a complex vector space
the complex structure of the fibre `E ⧸ LinearMap.range (P y)` varies with `y`, and a family whose
period ratio varies is not holomorphically a product.

## Main results

* `TauCeti.periodBasis_equivFun_mem_span_iff`: the coordinates of `v` in the period basis at `y` are
  integers exactly when `v` is a period at `y`.
* `TauCeti.continuous_periodBasis_equivFunL_symm`, `TauCeti.continuous_periodBasis_equivFunL`:
  the frame `F_y` and its inverse depend continuously on `y`.
* `TauCeti.torusFamilyHomeomorphProd`: the homeomorphism `(Y × E)/Λ ≃ₜ Y × ℝ^ι/ℤ^ι` over `Y`.

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
`(y', v')` agree exactly when `y = y'` and the period coordinates of `v` and `v'` at `y` have the
same class modulo the standard lattice. -/
private theorem orbitRel_periodAddAction_iff {p q : Y × E} :
    letI := periodAddAction P
    AddAction.orbitRel Λ (Y × E) p q ↔ p.1 = q.1 ∧
      (Submodule.Quotient.mk ((periodBasis P b hinj q.1).equivFun p.2) :
        (ι → ℝ) ⧸ span ℤ (range (Pi.basisFun ℝ ι))) =
        Submodule.Quotient.mk ((periodBasis P b hinj q.1).equivFun q.2) := by
  let _ := periodAddAction P
  rw [AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff, Submodule.Quotient.eq,
    ← map_sub, periodBasis_equivFun_mem_span_iff]

variable [TopologicalSpace Y]

/-- **Continuity of the period frame.** The real linear isomorphism `F_y : ℝ^ι → E`,
`x ↦ ∑ i, x i • P y (b i)`, depends continuously on `y` in the operator norm. -/
theorem continuous_periodBasis_equivFunL_symm (hcont : ∀ l, Continuous fun y ↦ P y l) :
    Continuous fun y ↦ ((periodBasis P b hinj y).equivFunL.symm : (ι → ℝ) →L[ℝ] E) :=
  Basis.continuous_equivFunL_symm_of_continuous fun i ↦ by simpa using hcont (b i)

/-- **Continuity of the inverse period frame.** The coordinate map `F_y⁻¹ : E → ℝ^ι` of the period
basis depends continuously on `y` in the operator norm. -/
theorem continuous_periodBasis_equivFunL (hcont : ∀ l, Continuous fun y ↦ P y l) :
    Continuous fun y ↦ ((periodBasis P b hinj y).equivFunL : E →L[ℝ] ι → ℝ) :=
  Basis.continuous_equivFunL_of_continuous fun i ↦ by simpa using hcont (b i)

/-- **The global trivialization** of a continuous family of full lattices. For a `ℤ`-basis `b`
of `Λ` indexed by `ι`, the map `[y, v] ↦ (y, [F_y⁻¹ v])`, with `F_y⁻¹` the coordinate map of the
period basis at `y`, is a homeomorphism from the orbit space of the period translation action to
the product of `Y` with the fixed torus `ℝ^ι/ℤ^ι`. It lies over `Y`
(`TauCeti.fst_torusFamilyHomeomorphProd`), and on each fibre it is induced by the real linear
isomorphism `F_y⁻¹`. -/
noncomputable def torusFamilyHomeomorphProd (hcont : ∀ l, Continuous fun y ↦ P y l) :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ₜ
      Y × (ι → ℝ) ⧸ span ℤ (range (Pi.basisFun ℝ ι)) :=
  letI := periodAddAction P
  -- The coordinates `(y, v) ↦ (y, F_y⁻¹ v)` and their inverse, before passing to quotients.
  have hfwd : Continuous fun p : Y × E ↦ (periodBasis P b hinj p.1).equivFun p.2 := by
    have := Fintype.ofFinite ι
    refine continuous_pi fun i ↦ ?_
    simpa only [comp_def, ContinuousLinearEquiv.coe_coe, Basis.equivFunL_apply,
      Basis.equivFun_apply] using
      (continuous_apply i).comp <| ((continuous_periodBasis_equivFunL P b hinj hcont).comp
        continuous_fst).clm_apply continuous_snd
  have hbwd : Continuous fun p : Y × (ι → ℝ) ↦
      (periodBasis P b hinj p.1).equivFun.symm p.2 := by
    have := Fintype.ofFinite ι
    simpa only [comp_def, ContinuousLinearEquiv.coe_coe, Basis.equivFunL_symm_apply,
      Basis.equivFun_symm_apply] using
      ((continuous_periodBasis_equivFunL_symm P b hinj hcont).comp continuous_fst).clm_apply
        continuous_snd
  { toFun := Quotient.lift
      (fun p ↦ (p.1, Submodule.Quotient.mk ((periodBasis P b hinj p.1).equivFun p.2)))
      fun p q h ↦ by
        obtain ⟨h₁, h₂⟩ := (orbitRel_periodAddAction_iff P b hinj).1 h
        rw [h₁]
        exact Prod.ext rfl h₂
    invFun r := Quotient.liftOn' r.2
      (fun x ↦ Quotient.mk _ (r.1, (periodBasis P b hinj r.1).equivFun.symm x))
      (fun x x' h ↦ Quotient.sound <| (orbitRel_periodAddAction_iff P b hinj).2
        ⟨rfl, by
          rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          exact (Submodule.Quotient.eq _).2 ((Submodule.quotientRel_def _).1 h)⟩)
    left_inv := by
      rintro ⟨p⟩
      exact congrArg (Quotient.mk _)
        (Prod.ext rfl ((periodBasis P b hinj p.1).equivFun.symm_apply_apply p.2))
    right_inv := by
      rintro ⟨y, z⟩
      induction z using Submodule.Quotient.induction_on with | H x => ?_
      beta_reduce
      rw [← Submodule.Quotient.mk''_eq_mk, Quotient.liftOn'_mk'', Quotient.lift_mk,
        LinearEquiv.apply_symm_apply, Submodule.Quotient.mk''_eq_mk]
    continuous_toFun := Continuous.quotient_lift
      (continuous_fst.prodMk ((span ℤ _).isOpenQuotientMap_mkQ.continuous.comp hfwd)) _
    continuous_invFun := by
      -- `Y × ℝ^ι → Y × ℝ^ι/ℤ^ι` is an open quotient map, so continuity can be checked upstairs.
      refine (IsOpenQuotientMap.id.prodMap
        (span ℤ (range (Pi.basisFun ℝ ι))).isOpenQuotientMap_mkQ).continuous_comp_iff.1 ?_
      exact continuous_quot_mk.comp (continuous_fst.prodMk hbwd) }

variable (hcont : ∀ l, Continuous fun y ↦ P y l)

/-- The homeomorphism sends the class of `(y, v)` to `y` and the class of the period coordinates
of `v` at `y`. -/
@[simp] theorem torusFamilyHomeomorphProd_mk (p : Y × E) :
    letI := periodAddAction P
    torusFamilyHomeomorphProd P b hinj hcont (Quotient.mk _ p) =
      (p.1, Submodule.Quotient.mk ((periodBasis P b hinj p.1).equivFun p.2)) := (rfl)

/-- The inverse homeomorphism sends `y` and the class of `x` to the class of
`(y, ∑ i, x i • P y (b i))`. -/
@[simp] theorem torusFamilyHomeomorphProd_symm_mk (y : Y) (x : ι → ℝ) :
    letI := periodAddAction P
    (torusFamilyHomeomorphProd P b hinj hcont).symm (y, Submodule.Quotient.mk x) =
      Quotient.mk _ (y, (periodBasis P b hinj y).equivFun.symm x) := (rfl)

/-- The homeomorphism lies over the parameter space. -/
@[simp] theorem fst_torusFamilyHomeomorphProd
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (torusFamilyHomeomorphProd P b hinj hcont z).1 = torusFamilyProjection P z := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end TauCeti
