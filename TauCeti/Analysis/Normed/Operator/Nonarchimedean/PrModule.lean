/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent
public import TauCeti.Analysis.Normed.Operator.RowCompact.PrModule
public import TauCeti.LinearAlgebra.Charpoly.Projective

/-!
# Fredholm series of row-compact operators on modules with property (Pr)

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1` and Tate scalars, and
`M` a module with property (Pr) (`TauCeti.HasPr R M`): a continuous linear retract
`M →ⁱ C₀(J, R) →ʳ M`, `r ∘ i = id`, of a model space. The **Fredholm series**
`H_u(T) = det (1 - T u)` of an endomorphism `u` of `M` (`ContinuousLinearMap.charPowerSeries`)
is the principal-minor series of the extension `i ∘ u ∘ r` of `u` to `C₀(J, R)`, for a retract
presentation of `M` fixed by choice.

For a row-compact `u` (`ContinuousLinearMap.IsPrCompact`) the series does not depend on the
presentation: for every retract `r ∘ i = id` of `M` through a model space, in any universe,

`H_u = det (1 - T (i ∘ u ∘ r))`
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`).

Given two presentations `(i, r)` and `(i', r')`, the extensions factor as
`i ∘ u ∘ r = (i ∘ r') ∘ (i' ∘ u ∘ r)` and `i' ∘ u ∘ r' = (i' ∘ u ∘ r) ∘ (i ∘ r')`, and the
cyclicity of Fredholm determinants of model-space operators
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_comp_comm`) applies to the
row-compact factor `i' ∘ u ∘ r`. No finite-dimensional complement of the range of `i` is
presumed.

Consequently `H_u` is entire, satisfies `H_{u ∘ v} = H_{v ∘ u}` for maps between two (Pr) modules
when `u` is row compact, is invariant under conjugation by continuous linear equivalences, and
rescales as `H_{c u}(T) = H_u(c T)`. On a model space it is the principal-minor series of the
matrix of `u`. On a finitely generated module with (Pr), which is projective, it is the
reversed characteristic polynomial `det (1 - X u)` of finite projective modules
(`ContinuousLinearMap.charPowerSeries_eq_projectiveCharpolyRev`). This polynomial need not have
degree equal to a rank of `M`, and its leading coefficient need not be a unit: the rank of a
finite projective module may vary over `Spec R`.

## Main definitions

* `ContinuousLinearMap.charPowerSeries`: the Fredholm series `det (1 - T u)` of an endomorphism
  of a module with property (Pr).

## Main results

* `ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`: independence of the presentation.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_eq_charPowerSeries_matrixCoeff`: on a model
  space it is the principal-minor series of the matrix.
* `ContinuousLinearMap.IsPrCompact.charPowerSeries_comp_comm`: cyclicity
  `det (1 - T (u ∘ v)) = det (1 - T (v ∘ u))`.
* `ContinuousLinearMap.IsPrCompact.charPowerSeries_conj`: invariance under conjugation.
* `ContinuousLinearMap.IsPrCompact.isEntire_charPowerSeries`: the series is entire.
* `ContinuousLinearMap.charPowerSeries_eq_projectiveCharpolyRev`: comparison with the finite
  projective determinant.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty

universe u v w

namespace ContinuousLinearMap

section Defs

variable {R : Type w} [SeminormedCommRing R] {M : Type u} [SeminormedAddCommGroup M] [Module R M]

open Classical in
/-- The **Fredholm series** `det (1 - T u)` of an endomorphism `u` of a module `M` with property
(Pr): the principal-minor series of the extension `i ∘ u ∘ r` of `u` through a retract
presentation `r ∘ i = id` of `M` by a model space `C₀(J, R)`, fixed by choice. If `u` is row
compact, it does not depend on the presentation
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`). If `M` does not have property (Pr) the
series is `1`. -/
noncomputable def charPowerSeries (u : M →L[R] M) : PowerSeries R :=
  if h : HasPr R M then
    let p := (hasPr_def R M).1 h
    letI := p.choose_spec.choose
    haveI := p.choose_spec.choose_spec.choose
    (p.choose_spec.choose_spec.choose_spec.choose.comp
      (u.comp p.choose_spec.choose_spec.choose_spec.choose_spec.choose)).matrixCoeff.charPowerSeries
  else 1

/-- The constant coefficient of the Fredholm series is `1`. -/
@[simp]
theorem constantCoeff_charPowerSeries (u : M →L[R] M) :
    PowerSeries.constantCoeff u.charPowerSeries = 1 := by
  rw [charPowerSeries]
  split_ifs <;> simp

/-- The Fredholm series of the zero endomorphism is `1`. -/
@[simp]
theorem charPowerSeries_zero : (0 : M →L[R] M).charPowerSeries = 1 := by
  rw [charPowerSeries]
  split_ifs <;> simp

end Defs

section RowCompact

variable {R : Type w} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type u} {N : Type v} [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]

/-- The extensions of a row-compact `u` through two retract presentations of `M` have the same
principal-minor series. -/
private theorem charPowerSeries_matrixCoeff_comp_comp_eq {u : M →L[R] M} (hu : u.IsPrCompact)
    {J J' : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    [TopologicalSpace J'] [DiscreteTopology J'] [DecidableEq J'] {i : M →L[R] C₀(J, R)}
    {r : C₀(J, R) →L[R] M} (hri : r.comp i = .id R M) {i' : M →L[R] C₀(J', R)}
    {r' : C₀(J', R) →L[R] M} (hri' : r'.comp i' = .id R M) :
    (i.comp (u.comp r)).matrixCoeff.charPowerSeries =
      (i'.comp (u.comp r')).matrixCoeff.charPowerSeries := by
  have h : ∀ x, r (i x) = x := fun x ↦ by simpa using DFunLike.congr_fun hri x
  have h' : ∀ x, r' (i' x) = x := fun x ↦ by simpa using DFunLike.congr_fun hri' x
  -- Both extensions are composites of `i ∘ r'` and the row-compact `i' ∘ u ∘ r`, in either order.
  have h₁ : i.comp (u.comp r) = (i.comp r').comp (i'.comp (u.comp r)) :=
    ext fun x ↦ by simp [h']
  have h₂ : i'.comp (u.comp r') = (i'.comp (u.comp r)).comp (i.comp r') :=
    ext fun x ↦ by simp [h]
  rw [h₁, h₂]
  exact ((hu.isRowCompact_comp i' r).charPowerSeries_matrixCoeff_comp_comm _).symm

/-- **Independence of the presentation.** The Fredholm series of a row-compact endomorphism `u`
of a module with property (Pr) is the principal-minor series of its extension `i ∘ u ∘ r`
through any retract presentation `r ∘ i = id` of the module by a model space. -/
theorem IsPrCompact.charPowerSeries_eq {u : M →L[R] M} (hu : u.IsPrCompact) {J : Type*}
    [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J] {i : M →L[R] C₀(J, R)}
    {r : C₀(J, R) →L[R] M} (hri : r.comp i = .id R M) :
    u.charPowerSeries = (i.comp (u.comp r)).matrixCoeff.charPowerSeries := by
  classical
  have h := hu.hasPr_source
  rw [charPowerSeries, dite_eq_left h]
  let p := (hasPr_def R M).1 h
  let := p.choose_spec.choose
  have := p.choose_spec.choose_spec.choose
  exact charPowerSeries_matrixCoeff_comp_comp_eq hu
    p.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec hri

/-- On a model space, the Fredholm series of a row-compact endomorphism is the principal-minor
series of its matrix. -/
theorem IsRowCompact.charPowerSeries_eq_charPowerSeries_matrixCoeff {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I] {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) : u.charPowerSeries = u.matrixCoeff.charPowerSeries := by
  simpa using (isPrCompact_iff_isRowCompact.2 hu).charPowerSeries_eq
    (i := .id R C₀(I, R)) (r := .id R C₀(I, R)) (id_comp _)

/-- The Fredholm series of a row-compact endomorphism of a module with property (Pr) is entire. -/
theorem IsPrCompact.isEntire_charPowerSeries {u : M →L[R] M} (hu : u.IsPrCompact) :
    u.charPowerSeries.IsEntire := by
  classical
  obtain ⟨J, _, _, _, -, -, -, iM, rM, -, -, hM, -, -⟩ := (isPrCompact_def u).1 hu
  rw [hu.charPowerSeries_eq hM]
  exact (hu.isRowCompact_comp iM rM).isEntire_charPowerSeries

/-- **Cyclicity of Fredholm series on (Pr) modules.** If `u : M →L[R] N` is row compact and
`v : N →L[R] M` is any continuous linear map, the endomorphisms `u ∘ v` of `N` and `v ∘ u` of `M`
have the same Fredholm series: `det (1 - T (u ∘ v)) = det (1 - T (v ∘ u))`. -/
theorem IsPrCompact.charPowerSeries_comp_comm {u : M →L[R] N} (hu : u.IsPrCompact)
    (v : N →L[R] M) : (u.comp v).charPowerSeries = (v.comp u).charPowerSeries := by
  classical
  obtain ⟨J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, h⟩ := (isPrCompact_def u).1 hu
  have hM' : ∀ x, rM (iM x) = x := fun x ↦ by simpa using DFunLike.congr_fun hM x
  have hN' : ∀ x, rN (iN x) = x := fun x ↦ by simpa using DFunLike.congr_fun hN x
  rw [(hu.comp_clm v hu.hasPr_target).charPowerSeries_eq hN,
    (hu.clm_comp v hu.hasPr_source).charPowerSeries_eq hM]
  -- Both extensions are composites of `iN ∘ u ∘ rM` and `iM ∘ v ∘ rN`, in either order.
  have h₁ : iN.comp ((u.comp v).comp rN) = (iN.comp (u.comp rM)).comp (iM.comp (v.comp rN)) :=
    ext fun x ↦ by simp [hM']
  have h₂ : iM.comp ((v.comp u).comp rM) = (iM.comp (v.comp rN)).comp (iN.comp (u.comp rM)) :=
    ext fun x ↦ by simp [hN']
  rw [h₁, h₂, h.charPowerSeries_matrixCoeff_comp_comm]

/-- **Invariance under conjugation.** The Fredholm series of a row-compact endomorphism `u` of a
module with property (Pr) is unchanged by conjugation `e ∘ u ∘ e⁻¹` by a continuous linear
equivalence `e`, which need not be an isometry. -/
theorem IsPrCompact.charPowerSeries_conj {N : Type u} [SeminormedAddCommGroup N] [Module R N]
    {u : M →L[R] M} (hu : u.IsPrCompact) (e : M ≃L[R] N) :
    ((e : M →L[R] N).comp (u.comp (e.symm : N →L[R] M))).charPowerSeries =
      u.charPowerSeries := by
  rw [← comp_assoc,
    (hu.clm_comp (e : M →L[R] N) (hu.hasPr_source.of_equiv e.symm)).charPowerSeries_comp_comm,
    ← comp_assoc, ContinuousLinearEquiv.coe_symm_comp_coe, id_comp]

/-- **Scaling.** For a row-compact endomorphism `u` of a module with property (Pr), the Fredholm
series of `c • u` is that of `u` with the variable rescaled by `c`: `H_{c u}(T) = H_u(c T)`. -/
theorem IsPrCompact.charPowerSeries_smul [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) (c : R) :
    (c • u).charPowerSeries = PowerSeries.rescale c u.charPowerSeries := by
  classical
  obtain ⟨J, _, _, _, -, -, -, iM, rM, -, -, hM, -, -⟩ := (isPrCompact_def u).1 hu
  rw [(hu.smul c).charPowerSeries_eq hM, hu.charPowerSeries_eq hM, smul_comp, comp_smul,
    matrixCoeff_smul,
    Matrix.charPowerSeries_smul c (hu.isRowCompact_comp iM rM).summable_principalMinor]

end RowCompact

section Finite

variable {R : Type w} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type u} [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M]

/-- **Comparison with the finite projective determinant.** On a finitely generated module with
property (Pr), which is projective (`TauCeti.HasPr.projective`), the Fredholm series of every
endomorphism `u` is the reversed characteristic polynomial `det (1 - X u)` of `u` as an
endomorphism of a finite projective module. -/
theorem charPowerSeries_eq_projectiveCharpolyRev [Module.Finite R M] (hM : HasPr R M)
    (u : M →L[R] M) :
    haveI := hM.projective
    u.charPowerSeries = ((u : M →ₗ[R] M).projectiveCharpolyRev : PowerSeries R) := by
  have := hM.projective
  obtain ⟨n, i, r, hri⟩ := hM.exists_comp_eq_id_of_finite
  have h : ∀ x, r (i x) = x := fun x ↦ by simpa using DFunLike.congr_fun hri x
  -- Present `M` through the finite model space `C₀(Fin n, R) ≃ R ^ n`.
  let e := (equivFunOnFintype R R (I := Fin n)).toContinuousLinearEquiv
  have hre : (r.comp (e : C₀(Fin n, R) →L[R] (Fin n → R))).comp
      ((e.symm : (Fin n → R) →L[R] C₀(Fin n, R)).comp i) = .id R M :=
    ext fun x ↦ by simp [h]
  have hlin : (r : (Fin n → R) →ₗ[R] M) ∘ₗ (i : M →ₗ[R] (Fin n → R)) = LinearMap.id :=
    LinearMap.ext h
  rw [(isPrCompact_of_finite hM hM u).charPowerSeries_eq hre, Matrix.charPowerSeries_eq_charpolyRev,
    LinearMap.projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) _ _ hlin,
    LinearMap.toMatrix_eq_toMatrix', matrixCoeff_eq_toMatrix']
  congr 3
  refine LinearMap.ext fun y ↦ funext fun j ↦ ?_
  simp [e]

end Finite

end ContinuousLinearMap
