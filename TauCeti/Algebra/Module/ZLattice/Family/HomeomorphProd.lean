/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LinearEquivProd
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

/-- The period coordinate map carries the period lattice onto the standard integral lattice. -/
theorem map_range_periodBasis_equivFun (y : Y) :
    (LinearMap.range (P y)).map
        ((periodBasis P b hinj y).equivFun.restrictScalars ℤ).toLinearMap =
      span ℤ (range (Pi.basisFun ℝ ι)) := by
  ext v
  rw [Submodule.mem_map_equiv]
  simpa only [LinearEquiv.restrictScalars_symm_apply, LinearEquiv.apply_symm_apply] using
    (periodBasis_equivFun_mem_span_iff P b hinj y
      ((periodBasis P b hinj y).equivFun.symm v)).symm

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
  let e := (torusFamilyLinearEquivProd P (span ℤ (range (Pi.basisFun ℝ ι)))
      (fun y ↦ (periodBasis P b hinj y).equivFun.restrictScalars ℤ)
      (map_range_periodBasis_equivFun P b hinj)).trans
    ((Equiv.refl Y).prodCongr (span ℤ _).orbitRelQuotientAddEquiv.toEquiv)
  { toEquiv := e
    continuous_toFun := by
      have hq : Topology.IsQuotientMap (Quotient.mk (AddAction.orbitRel Λ (Y × E))) :=
        isQuotientMap_quotient_mk'
      apply hq.continuous_iff.2
      convert continuous_fst.prodMk
        ((span ℤ (range (Pi.basisFun ℝ ι))).isOpenQuotientMap_mkQ.continuous.comp hfwd) using 1
      funext p
      rcases p with ⟨y, v⟩
      simp [e, comp_def]
    continuous_invFun := by
      -- `Y × ℝ^ι → Y × ℝ^ι/ℤ^ι` is an open quotient map, so continuity can be checked upstairs.
      refine (IsOpenQuotientMap.id.prodMap
        (span ℤ (range (Pi.basisFun ℝ ι))).isOpenQuotientMap_mkQ).continuous_comp_iff.1 ?_
      have hq : Continuous (Quotient.mk (AddAction.orbitRel Λ (Y × E))) :=
        continuous_quotient_mk'
      convert hq.comp (continuous_fst.prodMk hbwd) using 1
      funext p
      rcases p with ⟨y, v⟩
      simp [e, comp_def] }

variable (hcont : ∀ l, Continuous fun y ↦ P y l)

/-- The homeomorphism sends the class of `(y, v)` to `y` and the class of the period coordinates
of `v` at `y`. -/
@[simp] theorem torusFamilyHomeomorphProd_mk (p : Y × E) :
    letI := periodAddAction P
    torusFamilyHomeomorphProd P b hinj hcont (Quotient.mk _ p) =
      (p.1, Submodule.Quotient.mk ((periodBasis P b hinj p.1).equivFun p.2)) := by
  let _ := periodAddAction P
  rcases p with ⟨y, v⟩
  simp [torusFamilyHomeomorphProd]

/-- The inverse homeomorphism sends `y` and the class of `x` to the class of
`(y, ∑ i, x i • P y (b i))`. -/
@[simp] theorem torusFamilyHomeomorphProd_symm_mk (y : Y) (x : ι → ℝ) :
    letI := periodAddAction P
    (torusFamilyHomeomorphProd P b hinj hcont).symm (y, Submodule.Quotient.mk x) =
      Quotient.mk _ (y, (periodBasis P b hinj y).equivFun.symm x) := by
  let _ := periodAddAction P
  simp [torusFamilyHomeomorphProd]

/-- The homeomorphism lies over the parameter space. -/
@[simp] theorem fst_torusFamilyHomeomorphProd
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (torusFamilyHomeomorphProd P b hinj hcont z).1 = torusFamilyProjection P z := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end TauCeti
