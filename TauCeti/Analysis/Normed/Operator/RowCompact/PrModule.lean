/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.PotentiallyONable
public import TauCeti.Analysis.Normed.Operator.RowCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Row-compact maps between modules with property (Pr)

A module `M` over a normed ring `R` has property (Pr) (`TauCeti.HasPr R M`) if it is a continuous
linear retract `M →ⁱ C₀(J, R) →ʳ M`, `r ∘ i = id`, of a model space. A continuous linear map
`u : M →L[R] N` between two such modules is **row compact** in the sense of (Pr) modules
(`ContinuousLinearMap.IsPrCompact`) if for some retract presentations `(iM, rM)` of `M` and
`(iN, rN)` of `N` the extension `iN ∘ u ∘ rM : C₀(J, R) →L[R] C₀(I, R)` is row compact
(`ContinuousLinearMap.IsRowCompact`). This extends row compactness from model spaces to their
continuous linear retracts, without choosing an orthonormal basis of `M` or `N`.

Over ultrametric Tate scalars the condition does not depend on the presentations. If
`iN ∘ u ∘ rM` is row compact and `j : N →L[R] C₀(I', R)`, `s : C₀(J', R) →L[R] M` are any
continuous linear maps, then `j ∘ u ∘ s` is the composite `(j ∘ rN) ∘ (iN ∘ u ∘ rM) ∘ (iM ∘ s)`,
which is row compact because row-compact maps form a two-sided operator ideal
(`ContinuousLinearMap.isRowCompact_comp_of_retract`). No finite-dimensional complement of the
range of `iM` is presumed.

The ideal, closedness and approximation properties of row-compact maps transport to (Pr)
modules. Over complete ultrametric Tate scalars, let `M` be a normed module with a bounded scalar
action (`IsBoundedSMul`). If `M` is finitely generated with (Pr), every map into `M` from a module
with (Pr) is row compact. The identity of `M` is row compact exactly when `M` has (Pr) and is
finitely generated. Hence a row-compact endomorphism `u` of `M` with `(1 - u) ^ n = 0` forces `M`
to be finitely generated projective.

## Main definitions

* `ContinuousLinearMap.IsPrCompact`: row compactness of a map between modules with property (Pr),
  through retract presentations.

## Main results

* `ContinuousLinearMap.IsPrCompact.isRowCompact_comp`: for a row-compact `u : M →L[R] N`, every
  composite `j ∘ u ∘ s` with model spaces is row compact; in particular the extension through any
  presentation is.
* `ContinuousLinearMap.isPrCompact_iff_isRowCompact_comp`: independence of the presentation.
* `ContinuousLinearMap.isPrCompact_iff_isRowCompact`: on model spaces the notion is row
  compactness.
* `ContinuousLinearMap.IsPrCompact.comp_clm`, `ContinuousLinearMap.IsPrCompact.clm_comp`,
  `ContinuousLinearMap.isPrCompact_of_tendsto`: the closed operator ideal property.
* `ContinuousLinearMap.IsPrCompact.tendsto_ringOpNorm_comp_indicatorCLM_comp_sub`: a row-compact
  map is the operator-norm limit of its truncations `rN ∘ π_S ∘ iN ∘ u` through any presentation
  of the target.
* `ContinuousLinearMap.IsPrCompact.isCompletelyContinuous`: row-compact maps are completely
  continuous.
* `ContinuousLinearMap.isPrCompact_id_iff`: the identity is row compact exactly on finitely
  generated modules with property (Pr).
* `ContinuousLinearMap.IsPrCompact.projective_of_one_sub_pow_eq_zero`: a row-compact `u` with
  `(1 - u) ^ n = 0` forces the module to be finitely generated projective.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§1–3.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty

universe u v w

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section SeminormedRing

variable {R : Type w} [SeminormedRing R] {M : Type u} {N : Type v}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]

/-- A continuous linear map `u : M →L[R] N` between modules with property (Pr) is **row compact**
if there are continuous linear retract presentations `rM ∘ iM = id` of `M` through `C₀(J, R)` and
`rN ∘ iN = id` of `N` through `C₀(I, R)` such that the extension `iN ∘ u ∘ rM` is row compact.
Over ultrametric Tate scalars this does not depend on the presentations
(`ContinuousLinearMap.isPrCompact_iff_isRowCompact_comp`). The index types live in the universes
of `M` and `N`, as in `TauCeti.HasPr`. -/
def IsPrCompact (u : M →L[R] N) : Prop :=
  ∃ (J : Type u) (_ : TopologicalSpace J) (_ : DiscreteTopology J) (_ : DecidableEq J)
    (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I)
    (iM : M →L[R] C₀(J, R)) (rM : C₀(J, R) →L[R] M) (iN : N →L[R] C₀(I, R))
    (rN : C₀(I, R) →L[R] N),
    rM.comp iM = .id R M ∧ rN.comp iN = .id R N ∧ (iN.comp (u.comp rM)).IsRowCompact

/-- A map is row compact in the sense of (Pr) modules exactly when it has row-compact extensions
through some retract presentations of its source and target. This is the introduction and
elimination interface for `ContinuousLinearMap.IsPrCompact`. -/
theorem isPrCompact_def (u : M →L[R] N) :
    u.IsPrCompact ↔
      ∃ (J : Type u) (_ : TopologicalSpace J) (_ : DiscreteTopology J) (_ : DecidableEq J)
        (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I)
        (iM : M →L[R] C₀(J, R)) (rM : C₀(J, R) →L[R] M) (iN : N →L[R] C₀(I, R))
        (rN : C₀(I, R) →L[R] N),
        rM.comp iM = .id R M ∧ rN.comp iN = .id R N ∧ (iN.comp (u.comp rM)).IsRowCompact :=
  Iff.rfl

/-- **Retract factorisation**: if `rM ∘ iM = id` and `rN ∘ iN = id` present the source and target
of `u`, then `u` factors through its extension as `rN ∘ (iN ∘ u ∘ rM) ∘ iM`. -/
theorem comp_comp_comp_of_retract {J : Type*} [TopologicalSpace J] {I : Type*}
    [TopologicalSpace I] {iM : M →L[R] C₀(J, R)} {rM : C₀(J, R) →L[R] M} {iN : N →L[R] C₀(I, R)}
    {rN : C₀(I, R) →L[R] N} (hM : rM.comp iM = .id R M) (hN : rN.comp iN = .id R N)
    (u : M →L[R] N) : rN.comp ((iN.comp (u.comp rM)).comp iM) = u := by
  ext x
  have hx : rM (iM x) = x := by simpa using DFunLike.congr_fun hM x
  simpa [hx] using DFunLike.congr_fun hN (u x)

/-- A map whose extension through retract presentations of its source and target is row compact
is row compact in the sense of (Pr) modules. -/
theorem isPrCompact_of_isRowCompact_comp {J : Type u} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] {I : Type v} [TopologicalSpace I] [DiscreteTopology I]
    {iM : M →L[R] C₀(J, R)} {rM : C₀(J, R) →L[R] M} {iN : N →L[R] C₀(I, R)}
    {rN : C₀(I, R) →L[R] N} (hM : rM.comp iM = .id R M) (hN : rN.comp iN = .id R N)
    {u : M →L[R] N} (hu : (iN.comp (u.comp rM)).IsRowCompact) : u.IsPrCompact :=
  ⟨J, _, ‹_›, ‹_›, I, _, ‹_›, iM, rM, iN, rN, hM, hN, hu⟩

/-- The source of a row-compact map between (Pr) modules has property (Pr). -/
theorem IsPrCompact.hasPr_source {u : M →L[R] N} (hu : u.IsPrCompact) : HasPr R M :=
  let ⟨J, _, hJ, _, _, _, _, iM, rM, _, _, hM, _⟩ := hu
  (hasPr_def R M).2 ⟨J, _, hJ, iM, rM, hM⟩

/-- The target of a row-compact map between (Pr) modules has property (Pr). -/
theorem IsPrCompact.hasPr_target {u : M →L[R] N} (hu : u.IsPrCompact) : HasPr R N :=
  let ⟨_, _, _, _, I, _, hI, _, _, iN, rN, _, hN, _⟩ := hu
  (hasPr_def R N).2 ⟨I, _, hI, iN, rN, hN⟩

/-- The zero map between two modules is row compact exactly when both have property (Pr). -/
@[simp]
theorem isPrCompact_zero_iff : (0 : M →L[R] N).IsPrCompact ↔ HasPr R M ∧ HasPr R N := by
  classical
  refine ⟨fun h ↦ ⟨h.hasPr_source, h.hasPr_target⟩, fun ⟨hM, hN⟩ ↦ ?_⟩
  obtain ⟨J, _, _, iM, rM, hM⟩ := (hasPr_def R M).1 hM
  obtain ⟨I, _, _, iN, rN, hN⟩ := (hasPr_def R N).1 hN
  exact isPrCompact_of_isRowCompact_comp hM hN (by simp)

/-- Negatives of row-compact maps between (Pr) modules are row compact. -/
theorem IsPrCompact.neg {u : M →L[R] N} (hu : u.IsPrCompact) : (-u).IsPrCompact := by
  obtain ⟨J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, h⟩ := hu
  exact isPrCompact_of_isRowCompact_comp hM hN (by simpa only [neg_comp, comp_neg] using h.neg)

/-- A negative is row compact between (Pr) modules exactly when the map is. -/
@[simp]
theorem isPrCompact_neg_iff {u : M →L[R] N} : (-u).IsPrCompact ↔ u.IsPrCompact :=
  ⟨fun hu ↦ neg_neg u ▸ hu.neg, IsPrCompact.neg⟩

/-- Over Tate scalars, every map into a retract of a model space with a finite index type is row
compact, provided its source has property (Pr). -/
theorem isPrCompact_of_finite_retract [TauCeti.NormedRing.IsTate R] {I : Type v}
    [TopologicalSpace I] [DiscreteTopology I] [Finite I] {iN : N →L[R] C₀(I, R)}
    {rN : C₀(I, R) →L[R] N} (hN : rN.comp iN = .id R N) (hM : HasPr R M) (u : M →L[R] N) :
    u.IsPrCompact := by
  classical
  obtain ⟨J, _, _, iM, rM, hM⟩ := (hasPr_def R M).1 hM
  exact isPrCompact_of_isRowCompact_comp hM hN (isRowCompact_of_finite _)

end SeminormedRing

section SeminormedCommRing

variable {R : Type w} [SeminormedCommRing R] {M : Type u} {N : Type v}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]
  [ContinuousConstSMul R N]

/-- Scalar multiples of row-compact maps between (Pr) modules are row compact. -/
theorem IsPrCompact.smul {u : M →L[R] N} (hu : u.IsPrCompact) (c : R) : (c • u).IsPrCompact := by
  obtain ⟨J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, h⟩ := hu
  exact isPrCompact_of_isRowCompact_comp hM hN
    (by simpa only [smul_comp, comp_smul] using h.smul c)

end SeminormedCommRing

section Ideal

variable {R : Type w} [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  {L : Type*} {M : Type u} {N : Type v} {P : Type*}
  [SeminormedAddCommGroup L] [Module R L] [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N] [SeminormedAddCommGroup P] [Module R P]

/-- **Independence of the presentation.** Over ultrametric Tate scalars, if the extension
`iN ∘ u ∘ rM` of `u` through retract presentations of its source and target is row compact, then
so is every composite `j ∘ u ∘ s` with continuous linear maps `j` into and `s` out of model
spaces: it factors as `(j ∘ rN) ∘ (iN ∘ u ∘ rM) ∘ (iM ∘ s)`. -/
theorem isRowCompact_comp_of_retract {J : Type*} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    {iM : M →L[R] C₀(J, R)} {rM : C₀(J, R) →L[R] M} {iN : N →L[R] C₀(I, R)}
    {rN : C₀(I, R) →L[R] N} (hM : rM.comp iM = .id R M) (hN : rN.comp iN = .id R N)
    {u : M →L[R] N} (hu : (iN.comp (u.comp rM)).IsRowCompact) {J' I' : Type*}
    [TopologicalSpace J'] [DiscreteTopology J'] [DecidableEq J'] [TopologicalSpace I']
    [DiscreteTopology I'] (j : N →L[R] C₀(I', R)) (s : C₀(J', R) →L[R] M) :
    (j.comp (u.comp s)).IsRowCompact := by
  have : j.comp (u.comp s) = (j.comp rN).comp ((iN.comp (u.comp rM)).comp (iM.comp s)) := by
    conv_lhs => rw [← comp_comp_comp_of_retract hM hN u]
    simp only [comp_assoc]
  rw [this]
  exact (hu.comp_clm _).clm_comp _

/-- Over ultrametric Tate scalars, for a row-compact map `u` between (Pr) modules every composite
`j ∘ u ∘ s` with continuous linear maps into and out of model spaces is row compact. In
particular the extension of `u` through any retract presentations is row compact. -/
theorem IsPrCompact.isRowCompact_comp {u : M →L[R] N} (hu : u.IsPrCompact) {J' I' : Type*}
    [TopologicalSpace J'] [DiscreteTopology J'] [DecidableEq J'] [TopologicalSpace I']
    [DiscreteTopology I'] (j : N →L[R] C₀(I', R)) (s : C₀(J', R) →L[R] M) :
    (j.comp (u.comp s)).IsRowCompact :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, hM, hN, h⟩ := hu
  isRowCompact_comp_of_retract hM hN h j s

/-- **Row compactness on (Pr) modules does not depend on the presentation**: over ultrametric
Tate scalars, `u` is row compact exactly when its extension through any one pair of retract
presentations is. -/
theorem isPrCompact_iff_isRowCompact_comp {J : Type u} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] {I : Type v} [TopologicalSpace I] [DiscreteTopology I]
    {iM : M →L[R] C₀(J, R)} {rM : C₀(J, R) →L[R] M} {iN : N →L[R] C₀(I, R)}
    {rN : C₀(I, R) →L[R] N} (hM : rM.comp iM = .id R M) (hN : rN.comp iN = .id R N)
    {u : M →L[R] N} : u.IsPrCompact ↔ (iN.comp (u.comp rM)).IsRowCompact :=
  ⟨fun hu ↦ hu.isRowCompact_comp iN rM, isPrCompact_of_isRowCompact_comp hM hN⟩

/-- **Transport along equivalences with model spaces**: over ultrametric Tate scalars, a map
between potentially orthonormalisable modules is row compact exactly when its conjugate
`eN ∘ u ∘ eM⁻¹` between the model spaces is. -/
theorem isPrCompact_iff_isRowCompact_comp_symm {J : Type u} [TopologicalSpace J]
    [DiscreteTopology J] [DecidableEq J] {I : Type v} [TopologicalSpace I] [DiscreteTopology I]
    (eM : M ≃L[R] C₀(J, R)) (eN : N ≃L[R] C₀(I, R)) {u : M →L[R] N} :
    u.IsPrCompact ↔
      ((eN : N →L[R] C₀(I, R)).comp (u.comp (eM.symm : C₀(J, R) →L[R] M))).IsRowCompact :=
  isPrCompact_iff_isRowCompact_comp eM.coe_symm_comp_coe eN.coe_symm_comp_coe

/-- On model spaces, row compactness in the sense of (Pr) modules is row compactness. -/
@[simp]
theorem isPrCompact_iff_isRowCompact {J : Type u} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] {I : Type v} [TopologicalSpace I] [DiscreteTopology I]
    {u : C₀(J, R) →L[R] C₀(I, R)} : u.IsPrCompact ↔ u.IsRowCompact := by
  refine ⟨fun hu ↦ by simpa using hu.isRowCompact_comp (.id R _) (.id R _), fun hu ↦ ?_⟩
  -- Present `C₀(J, R)` through the reindexing by `ULift J`, which lives in its universe.
  let eJ := (congrLeft R R (Homeomorph.ulift.{w} (X := J))).toContinuousLinearEquiv
  let eI := (congrLeft R R (Homeomorph.ulift.{w} (X := I))).toContinuousLinearEquiv
  exact isPrCompact_of_isRowCompact_comp eJ.coe_comp_coe_symm eI.coe_comp_coe_symm
    ((hu.comp_clm _).clm_comp _)

/-- Sums of row-compact maps between (Pr) modules are row compact. -/
theorem IsPrCompact.add {u v : M →L[R] N} (hu : u.IsPrCompact) (hv : v.IsPrCompact) :
    (u + v).IsPrCompact := by
  obtain ⟨J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, h⟩ := hu
  refine isPrCompact_of_isRowCompact_comp hM hN ?_
  simpa only [add_comp, comp_add] using h.add (hv.isRowCompact_comp iN rM)

/-- Differences of row-compact maps between (Pr) modules are row compact. -/
theorem IsPrCompact.sub {u v : M →L[R] N} (hu : u.IsPrCompact) (hv : v.IsPrCompact) :
    (u - v).IsPrCompact :=
  sub_eq_add_neg u v ▸ hu.add hv.neg

/-- Precomposing a row-compact map between (Pr) modules with a continuous linear map out of a
module with property (Pr) gives a row-compact map. -/
theorem IsPrCompact.comp_clm {u : M →L[R] N} (hu : u.IsPrCompact) (w : L →L[R] M)
    (hL : HasPr R L) : (u.comp w).IsPrCompact := by
  classical
  obtain ⟨K, _, _, iL, rL, hL⟩ := (hasPr_def R L).1 hL
  obtain ⟨I, _, _, iN, rN, hN⟩ := (hasPr_def R N).1 hu.hasPr_target
  have h := hu.isRowCompact_comp iN (w.comp rL)
  rw [← comp_assoc] at h
  exact isPrCompact_of_isRowCompact_comp hL hN h

/-- Postcomposing a row-compact map between (Pr) modules with a continuous linear map into a
module with property (Pr) gives a row-compact map. -/
theorem IsPrCompact.clm_comp {u : M →L[R] N} (hu : u.IsPrCompact) (w : N →L[R] P)
    (hP : HasPr R P) : (w.comp u).IsPrCompact := by
  classical
  obtain ⟨K, _, _, iP, rP, hP⟩ := (hasPr_def R P).1 hP
  obtain ⟨J, _, _, iM, rM, hM⟩ := (hasPr_def R M).1 hu.hasPr_source
  have h := hu.isRowCompact_comp (iP.comp w) rM
  rw [comp_assoc] at h
  exact isPrCompact_of_isRowCompact_comp hM hP h

end Ideal

section Bounded

variable {R : Type w} [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  {M : Type u} {N : Type v} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **Closedness**: over ultrametric Tate scalars, an operator-norm limit of row-compact maps
between (Pr) modules is row compact. -/
theorem isPrCompact_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {u : M →L[R] N}
    {v : ι → M →L[R] N} (h : Tendsto (fun n ↦ ‖u - v n‖) l (𝓝 0))
    (hv : ∀ᶠ n in l, (v n).IsPrCompact) : u.IsPrCompact := by
  obtain ⟨_, J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, -⟩ := hv.exists
  refine isPrCompact_of_isRowCompact_comp hM hN (isRowCompact_of_tendsto
    (v := fun n ↦ iN.comp ((v n).comp rM)) ?_ (hv.mono fun n hn ↦ hn.isRowCompact_comp iN rM))
  refine squeeze_zero (fun _ ↦ ringOpNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using h.const_mul (‖iN‖ * ‖rM‖))
  calc ‖iN.comp (u.comp rM) - iN.comp ((v n).comp rM)‖ = ‖iN.comp ((u - v n).comp rM)‖ := by
        rw [sub_comp, comp_sub]
    _ ≤ ‖iN‖ * (‖u - v n‖ * ‖rM‖) := (ringOpNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ringOpNorm_comp_le _ _) (ringOpNorm_nonneg _))
    _ = ‖iN‖ * ‖rM‖ * ‖u - v n‖ := by ring

/-- **Approximation by truncations**: over ultrametric Tate scalars, if `rN ∘ iN = id` presents
the target of a row-compact map `u` between (Pr) modules, then the truncations
`rN ∘ π_S ∘ iN ∘ u` converge to `u` in operator norm as the finite set `S` of coordinates grows.
Here `π_S = ZeroAtInftyContinuousMap.indicatorCLM R S` is the coordinate projection. -/
theorem IsPrCompact.tendsto_ringOpNorm_comp_indicatorCLM_comp_sub {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] {iN : N →L[R] C₀(I, R)} {rN : C₀(I, R) →L[R] N}
    (hN : rN.comp iN = .id R N) {u : M →L[R] N} (hu : u.IsPrCompact) :
    Tendsto (fun S : Finset I ↦ ‖rN.comp ((indicatorCLM R (S : Set I)).comp (iN.comp u)) - u‖)
      atTop (𝓝 0) := by
  classical
  obtain ⟨J, _, _, iM, rM, hM⟩ := (hasPr_def R M).1 hu.hasPr_source
  set A := iN.comp (u.comp rM)
  have hA := (hu.isRowCompact_comp iN rM).tendsto_ringOpNorm_indicatorCLM_comp_sub
  -- Since `u = rN ∘ A ∘ iM`, the error of the truncation is `rN ∘ (π_S ∘ A - A) ∘ iM`.
  have hS (S : Finset I) : rN.comp ((indicatorCLM R (S : Set I)).comp (iN.comp u)) - u =
      rN.comp (((indicatorCLM R (S : Set I)).comp A - A).comp iM) := by
    rw [sub_comp, comp_sub, comp_comp_comp_of_retract hM hN]
    simp only [A, comp_assoc, hM, comp_id]
  refine squeeze_zero (fun _ ↦ ringOpNorm_nonneg _) (fun S ↦ ?_)
    (by simpa using (hA.const_mul ‖rN‖).mul_const ‖iM‖)
  rw [hS, mul_assoc]
  exact (ringOpNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ringOpNorm_comp_le _ _) (ringOpNorm_nonneg _))

end Bounded

section Ultrametric

variable {R : Type w} [NormedRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  {M : Type u} {N : Type v} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Over ultrametric Tate scalars, row-compact maps between (Pr) modules are completely
continuous. -/
theorem IsPrCompact.isCompletelyContinuous {u : M →L[R] N} (hu : u.IsPrCompact) :
    u.IsCompletelyContinuous := by
  obtain ⟨J, _, _, _, I, _, _, iM, rM, iN, rN, hM, hN, h⟩ := hu
  rw [← comp_comp_comp_of_retract hM hN u]
  exact (h.isCompletelyContinuous.comp_clm iM).clm_comp rN

end Ultrametric

section FiniteUltrametric

variable {R : Type w} [NormedRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  [CompleteSpace R] {M : Type u} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- Over complete ultrametric Tate scalars, every continuous linear map from a module with
property (Pr) into a finitely generated module with property (Pr) is row compact. A finitely
generated module with (Pr) is a retract of `C₀(S, R)` for a finite set `S` of generators. -/
theorem isPrCompact_of_finite [Module.Finite R M] (hM : HasPr R M) {L : Type*}
    [SeminormedAddCommGroup L] [Module R L] (hL : HasPr R L) (u : L →L[R] M) :
    u.IsPrCompact := by
  have := hM.completeSpace
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let : TopologicalSpace s := ⊥
  have : DiscreteTopology s := ⟨rfl⟩
  -- The finite generating set `s` gives a continuous linear surjection `(s → R) → M`; it splits
  -- by property (Pr), and `C₀(s, R)` is the finite free model space `s → R`.
  let q : (s → R) →L[R] M := ⟨Fintype.linearCombination R Subtype.val,
    (Fintype.linearCombination R Subtype.val).continuous_on_pi⟩
  have hq : Function.Surjective q :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R Subtype.val).1
      (by rwa [Subtype.range_coe])
  obtain ⟨t, ht⟩ := hM.lifting_property q (.id R M) hq
  let e := (equivFunOnFintype R R (I := s)).toContinuousLinearEquiv
  refine isPrCompact_of_finite_retract (iN := (e.symm : (s → R) →L[R] C₀(s, R)).comp t)
    (rN := q.comp (e : C₀(s, R) →L[R] (s → R))) ?_ hL _
  exact ContinuousLinearMap.ext fun x ↦ by simpa using DFunLike.congr_fun ht x

/-- **The identity criterion on (Pr) modules**: over complete ultrametric Tate scalars, the
identity of a module is row compact exactly when the module has property (Pr) and is finitely
generated. -/
theorem isPrCompact_id_iff :
    (ContinuousLinearMap.id R M).IsPrCompact ↔ HasPr R M ∧ Module.Finite R M := by
  refine ⟨fun hu ↦ ⟨hu.hasPr_source, ?_⟩, fun ⟨hM, _⟩ ↦ isPrCompact_of_finite hM hM _⟩
  have := hu.hasPr_source.completeSpace
  exact isCompletelyContinuous_id_iff.1 hu.isCompletelyContinuous

/-- **The finiteness germ**: over complete ultrametric Tate scalars, a row-compact endomorphism
`u` of a (Pr) module with `(1 - u) ^ n = 0` forces the module to be finitely generated. -/
theorem IsPrCompact.finite_of_one_sub_pow_eq_zero {u : M →L[R] M} (hu : u.IsPrCompact) {n : ℕ}
    (hn : (1 - u) ^ n = 0) : Module.Finite R M :=
  have := hu.hasPr_source.completeSpace
  hu.isCompletelyContinuous.finite_of_one_sub_pow_eq_zero hn

/-- Over complete ultrametric Tate scalars, a row-compact endomorphism `u` of a (Pr) module with
`(1 - u) ^ n = 0` forces the module to be finitely generated projective. -/
theorem IsPrCompact.projective_of_one_sub_pow_eq_zero {u : M →L[R] M} (hu : u.IsPrCompact)
    {n : ℕ} (hn : (1 - u) ^ n = 0) : Module.Projective R M :=
  have := hu.finite_of_one_sub_pow_eq_zero hn
  hu.hasPr_source.projective

end FiniteUltrametric

end ContinuousLinearMap
