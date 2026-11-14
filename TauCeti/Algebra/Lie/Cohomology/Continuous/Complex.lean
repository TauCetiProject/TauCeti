/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Lie.Cohomology.Continuous.Cochain
public import TauCeti.Algebra.Lie.Cohomology.Continuous.Map

import Mathlib.Topology.LocallyConstant.Algebra

/-!
# The continuous Chevalley–Eilenberg complex and continuous Lie algebra cohomology

Let `L` be a Lie algebra carrying a topology and `M` an `L`-module regarded as discrete. In
`TauCeti.Algebra.Lie.Cohomology.Continuous.Cochain`, the continuous `n`-cochains with values in `M`
were defined as the submodule `continuousCochain R L M n` of locally constant alternating maps
`L [⋀^Fin n]→ₗ[R] M`. This file determines when the Chevalley–Eilenberg differential preserves
continuous cochains, packages continuous cocycles, continuous coboundaries, and continuous
cohomology in every degree, and connects them both to the categorical homology of the continuous
cochain complex and to the low-degree continuous cohomology theories.

For a fixed element `x : L`, the Lie derivative `ω ↦ ⁅x, ω⁆` preserves continuous `n`-cochains as
soon as the bracket of `L` is continuous (`lie_mem_continuousCochain`), with no continuity
assumption on `M`: `⁅x, ω⁆ v` applies the fixed endomorphism `⁅x, ·⁆` to `ω v` and subtracts values
of `ω` after updating one coordinate by `y ↦ ⁅x, y⁆`. By contrast, already in degree zero the
differential `(d ω) ![x] = ⁅x, ω ![]⁆` preserves continuous cochains if and only if every orbit map
`⁅·, m⁆ : L → M` is locally constant (`forall_d_zero_mem_continuousCochain_iff`). When `L` is a
topological additive group this means that every `m : M` is annihilated by a neighbourhood of zero
(`isLocallyConstant_lie_iff`), the smoothness condition satisfied by trivial modules and by smooth
representations of formal current algebras. Together with continuity of the Lie bracket on `L`,
this condition makes `d R L M n` map `continuousCochain R L M n` into
`continuousCochain R L M (n + 1)` in every degree (`d_mem_continuousCochain`).

As in `TauCeti.Algebra.Lie.Cohomology.Continuous.Basic`, the carrier modules
`continuousCocycle R L M n`, `continuousCoboundary R L M n`, and `continuousCohomology R L M n`
carry no proof hypotheses in their types: continuous `n`-cocycles are continuous `n`-cochains in the
kernel of `d`, and continuous `(n + 1)`-coboundaries are those continuous cocycles of the form `d ω`
for a continuous `n`-cochain `ω`. They are functorial along any continuous Lie algebra morphism
`φ : L' →ₗ⁅R⁆ L` and intertwining linear map `e : M →ₗ[R] M'` (`continuousCohomologyMap`,
`continuousCohomologyEquiv`). Under the continuity hypotheses on `L` and `M`, the restricted
differentials `continuousD` assemble into a cochain complex `continuousCochainComplex` in
`ModuleCat R`, equipped with its subcomplex inclusion `continuousCochainComplexι` into
`cochainComplex R L M` and a natural linear equivalence `continuousCohomologyHomologyEquiv` between
`continuousCohomology R L M n` and `(continuousCochainComplex R L M hL hM).homology n`. Finally,
degree zero is identified with `L`-invariants (`continuousCohomologyZeroEquiv`), and over a
topological additive group degree two is identified with `continuousSecondCohomology`
(`continuousCohomologyTwoEquiv`), intertwining the functorial maps.

## Main definitions

* `TauCeti.LieModule.Cohomology.continuousCocycle`,
  `TauCeti.LieModule.Cohomology.continuousCoboundary`,
  `TauCeti.LieModule.Cohomology.continuousCohomology`: continuous cocycles, coboundaries, and
  cohomology of `L` with discrete coefficients in `M` in every degree.
* `TauCeti.LieModule.Cohomology.continuousCocycleMap`,
  `TauCeti.LieModule.Cohomology.continuousCohomologyMap`,
  `TauCeti.LieModule.Cohomology.continuousCohomologyEquiv`: functoriality of continuous cocycles and
  continuous cohomology.
* `TauCeti.LieModule.Cohomology.continuousD`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplex`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplexXIso`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplexι`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplexMap`: the continuous Chevalley–Eilenberg
  cochain complex, its inclusion into `cochainComplex`, and its functoriality.
* `TauCeti.LieModule.Cohomology.continuousCohomologyHomologyEquiv`: linear equivalence between
  `continuousCohomology` and the categorical homology of `continuousCochainComplex`.
* `TauCeti.LieModule.Cohomology.continuousCohomologyZeroEquiv`,
  `TauCeti.LieModule.Cohomology.continuousCohomologyTwoEquiv`: identifications with
  `LieModule.maxTrivSubmodule` in degree zero and `continuousSecondCohomology` in degree two.

## Main results

* `TauCeti.LieModule.Cohomology.lie_mem_continuousCochain`: Lie derivatives preserve continuous
  cochains when the Lie bracket of `L` is continuous.
* `TauCeti.LieModule.Cohomology.forall_d_zero_mem_continuousCochain_iff`: `d` preserves continuous
  `0`-cochains if and only if every orbit map `⁅·, m⁆ : L → M` is locally constant.
* `TauCeti.LieModule.Cohomology.d_mem_continuousCochain`: under continuous bracket on `L` and
  locally constant orbit maps on `M`, `d` preserves continuous cochains in every degree.
* `TauCeti.LieModule.Cohomology.homologyMap_continuousCohomologyHomologyEquiv`: naturality of
  `continuousCohomologyHomologyEquiv` with respect to `continuousCohomologyMap` and `homologyMap`.
* `TauCeti.LieModule.Cohomology.continuousCohomologyTwoEquiv_continuousCohomologyMap`: compatibility
  of `continuousCohomologyMap` in degree two with `continuousSecondCohomologyMap`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  §7.7.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.
-/

public section

open CategoryTheory Filter HomologicalComplex Topology _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

universe u v

section Preservation

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- If the Lie bracket of `L` is continuous, the Lie derivative along any element `x : L` preserves
continuous `n`-cochains, with no continuity hypothesis on the action on `M`. -/
theorem lie_mem_continuousCochain (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆) (x : L) {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ continuousCochain R L M n) :
    ⁅x, ω⁆ ∈ continuousCochain R L M n := by
  rw [mem_continuousCochain_iff] at hω ⊢
  have hupd (i : Fin n) :
      Continuous (fun v : Fin n → L ↦ Function.update v i ⁅x, v i⁆) := by
    refine continuous_pi fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hji
    · have hj : (fun v : Fin n → L ↦ Function.update v j ⁅x, v j⁆ j) =
          (fun p : L × L ↦ ⁅p.1, p.2⁆) ∘ fun v ↦ (x, v j) :=
        funext fun v ↦ Function.update_self j _ v
      rw [hj]
      exact hL.comp (continuous_const.prodMk (continuous_apply j))
    · have hj : (fun v : Fin n → L ↦ Function.update v i ⁅x, v i⁆ j) = fun v ↦ v j :=
        funext fun v ↦ Function.update_of_ne hji _ v
      rw [hj]
      exact continuous_apply j
  let g : LocallyConstant (Fin n → L) M :=
    ⟨fun v ↦ ⁅x, ω v⁆, hω.comp (⁅x, ·⁆)⟩ -
      ∑ i : Fin n, ⟨fun v ↦ ω (Function.update v i ⁅x, v i⁆), hω.comp_continuous (hupd i)⟩
  have hg : ⇑(⁅x, ω⁆ : L [⋀^Fin n]→ₗ[R] M) = ⇑g := by
    ext v
    have hv : g v = LocallyConstant.evalAddMonoidHom v
        (⟨fun v ↦ ⁅x, ω v⁆, hω.comp (⁅x, ·⁆)⟩ -
          ∑ i : Fin n, ⟨fun v ↦ ω (Function.update v i ⁅x, v i⁆), hω.comp_continuous (hupd i)⟩) :=
      rfl
    rw [AlternatingMap.lie_apply, hv, map_sub, map_sum]
    rfl
  exact hg ▸ g.isLocallyConstant

omit [CommRing R] [LieRing L] [LieAlgebra R L] [Module R M] [LieRingModule L M] [LieModule R L M] in
/-- Every orbit map `⁅·, m⁆ : L → M` of a trivial module is locally constant. -/
@[simp]
theorem isLocallyConstant_lie_of_isTrivial [Bracket L M] [LieModule.IsTrivial L M] (m : M) :
    IsLocallyConstant (⁅·, m⁆ : L → M) := by
  have h : (⁅·, m⁆ : L → M) = Function.const L 0 := funext fun x ↦ trivial_lie_zero L M x m
  rw [h]
  exact IsLocallyConstant.const 0

omit [CommRing R] [LieAlgebra R L] [Module R M] [LieModule R L M] in
/-- Over a topological additive group `L`, the orbit map `⁅·, m⁆ : L → M` is locally constant if
and only if `m` is annihilated by a neighbourhood of zero in `L`. -/
theorem isLocallyConstant_lie_iff [IsTopologicalAddGroup L] {m : M} :
    IsLocallyConstant (⁅·, m⁆ : L → M) ↔ ∀ᶠ x in 𝓝 (0 : L), ⁅x, m⁆ = 0 := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  let f : L →+ M :=
    { toFun := (⁅·, m⁆)
      map_zero' := zero_lie m
      map_add' x y := add_lie x y m }
  have hcoe : (f : L → M) = (⁅·, m⁆) := rfl
  rw [← hcoe, IsLocallyConstant.iff_continuous]
  refine ⟨fun hf ↦ by simpa [f, nhds_discrete M] using hf.tendsto 0,
    fun h0 ↦ continuous_of_continuousAt_zero f ?_⟩
  rwa [ContinuousAt, map_zero, nhds_discrete M, tendsto_pure]

/-- The degree-zero Chevalley–Eilenberg differential maps continuous `0`-cochains into continuous
`1`-cochains if and only if every orbit map `⁅·, m⁆ : L → M` is locally constant. -/
theorem forall_d_zero_mem_continuousCochain_iff :
    (∀ ω ∈ continuousCochain R L M 0, d R L M 0 ω ∈ continuousCochain R L M 1) ↔
      ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M) := by
  refine ⟨fun h m ↦ ?_, fun hM ω _ ↦ ?_⟩
  · let ω : L [⋀^Fin 0]→ₗ[R] M := AlternatingMap.constOfIsEmpty R L (Fin 0) m
    have hd := mem_continuousCochain_iff.mp (h ω (mem_continuousCochain_zero ω))
    have hf : Continuous (fun x : L ↦ (![x] : Fin 1 → L)) :=
      continuous_pi <| Fin.cases continuous_id fun i ↦ i.elim0
    have heq : (d R L M 0 ω : (Fin 1 → L) → M) ∘ (fun x : L ↦ ![x]) = (⁅·, m⁆) := by
      ext x
      simp [ω, d_zero_apply]
    simpa [heq] using hd.comp_continuous hf
  · have heq : (d R L M 0 ω : (Fin 1 → L) → M) = (⁅·, ω ![]⁆) ∘ fun v : Fin 1 → L ↦ v 0 :=
      funext (d_zero_apply ω)
    rw [mem_continuousCochain_iff, heq]
    exact (hM (ω ![])).comp_continuous (continuous_apply 0)

/-- **The Chevalley–Eilenberg differential preserves continuous cochains.** If the Lie bracket of
`L` is continuous and every orbit map `⁅·, m⁆ : L → M` is locally constant, then `d R L M n` maps
`continuousCochain R L M n` into `continuousCochain R L M (n + 1)` in every degree. -/
theorem d_mem_continuousCochain (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M n) :
    d R L M n ω ∈ continuousCochain R L M (n + 1) := by
  cases n with
  | zero => exact forall_d_zero_mem_continuousCochain_iff.mpr hM ω hω
  | succ n =>
    rw [mem_continuousCochain_iff] at hω ⊢
    have hterm₁ (i : Fin (n + 2)) : IsLocallyConstant
        (fun v : Fin (n + 2) → L ↦ (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆) := by
      have hrem : IsLocallyConstant (fun v : Fin (n + 2) → L ↦ ω (i.removeNth v)) :=
        hω.comp_continuous (continuous_pi fun k ↦ continuous_apply _)
      have hlie : IsLocallyConstant (fun v : Fin (n + 2) → L ↦ ⁅v i, ω (i.removeNth v)⁆) := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro v₀
        filter_upwards [hrem.eventually_eq v₀,
          ((hM (ω (i.removeNth v₀))).comp_continuous (continuous_apply i)).eventually_eq v₀]
          with v hv₁ hv₂
        exact hv₁.symm ▸ hv₂
      exact hlie.comp ((-1 : ℤ) ^ (i : ℕ) • ·)
    have hterm₂ (i j : Fin (n + 1)) : IsLocallyConstant (fun v : Fin (n + 2) → L ↦
        (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v)))) := by
      have h0 : Continuous (fun v : Fin (n + 2) → L ↦ ⁅v i.castSucc, v j.succ⁆) :=
        hL.comp ((continuous_apply (A := fun _ : Fin (n + 2) ↦ L) i.castSucc).prodMk
          (continuous_apply j.succ))
      have hpair : Continuous (fun v : Fin (n + 2) → L ↦
          Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) :=
        continuous_pi (Fin.cases h0 fun k ↦ continuous_apply _)
      exact (hω.comp_continuous hpair).comp ((-1 : ℤ) ^ (i + j + 1 : ℕ) • ·)
    let g : LocallyConstant (Fin (n + 2) → L) M :=
      (∑ i : Fin (n + 2), ⟨_, hterm₁ i⟩) +
        ∑ i : Fin (n + 1), ∑ j ≥ i, ⟨_, hterm₂ i j⟩
    have hg : ⇑(d R L M (n + 1) ω) = ⇑g := by
      ext v
      have hv : g v = LocallyConstant.evalAddMonoidHom v
          ((∑ i : Fin (n + 2), ⟨_, hterm₁ i⟩) +
            ∑ i : Fin (n + 1), ∑ j ≥ i, ⟨_, hterm₂ i j⟩) := rfl
      rw [d_succ_apply, hv, map_add, map_sum, map_sum]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
      rw [map_sum]
      rfl
    exact hg ▸ g.isLocallyConstant

/-- Over a topological additive group `L`, `d R L M n` preserves continuous cochains whenever the
bracket of `L` is continuous and every element of `M` is annihilated by a neighbourhood of zero. -/
theorem d_mem_continuousCochain_of_nhds_zero [IsTopologicalAddGroup L]
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, ∀ᶠ x in 𝓝 (0 : L), ⁅x, m⁆ = 0) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M n) :
    d R L M n ω ∈ continuousCochain R L M (n + 1) :=
  d_mem_continuousCochain hL (fun m ↦ isLocallyConstant_lie_iff.mpr (hM m)) hω

end Preservation

section Cohomology

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Continuous Chevalley–Eilenberg `n`-cocycles: continuous `n`-cochains annihilated by the
differential `d R L M n`. -/
def continuousCocycle (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  continuousCochain R L M n ⊓ LinearMap.ker (d R L M n)

/-- Inclusion of continuous `n`-cocycles into continuous `n`-cochains. -/
def continuousCocycleToCochain (n : ℕ) :
    continuousCocycle R L M n →ₗ[R] continuousCochain R L M n where
  toFun z := ⟨z.1, z.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous Chevalley–Eilenberg coboundaries as a submodule of continuous cocycles: `⊥` in
degree zero, and in degree `n + 1` those continuous cocycles that are differentials of continuous
`n`-cochains. -/
def continuousCoboundary : (n : ℕ) → Submodule R (continuousCocycle R L M n)
  | 0 => ⊥
  | n + 1 => ((continuousCochain R L M n).map (d R L M n)).comap
      (continuousCocycle R L M (n + 1)).subtype

/-- Continuous Lie algebra cohomology in degree `n` with discrete coefficients: continuous
`n`-cocycles modulo continuous `n`-coboundaries. -/
abbrev continuousCohomology (n : ℕ) :=
  continuousCocycle R L M n ⧸ continuousCoboundary R L M n

/-- The quotient map from continuous `n`-cocycles to degree-`n` continuous cohomology. -/
def continuousCohomologyMk (n : ℕ) :
    continuousCocycle R L M n →ₗ[R] continuousCohomology R L M n :=
  (continuousCoboundary R L M n).mkQ

theorem continuousCohomologyMk_eq_mkQ (n : ℕ) :
    continuousCohomologyMk R L M n = (continuousCoboundary R L M n).mkQ :=
  (rfl)

/-- Every degree-`n` continuous cohomology class is represented by a continuous `n`-cocycle. -/
theorem continuousCohomologyMk_surjective (n : ℕ) :
    Function.Surjective (continuousCohomologyMk R L M n) :=
  (continuousCoboundary R L M n).mkQ_surjective

@[simp]
theorem continuousCoboundary_zero :
    continuousCoboundary R L M 0 = ⊥ :=
  (rfl)

variable {R L M}

@[simp]
theorem coe_continuousCocycleToCochain {n : ℕ} (z : continuousCocycle R L M n) :
    (continuousCocycleToCochain R L M n z : L [⋀^Fin n]→ₗ[R] M) = z.1 :=
  (rfl)

theorem mem_continuousCocycle_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ continuousCocycle R L M n ↔ ω ∈ continuousCochain R L M n ∧ d R L M n ω = 0 :=
  Iff.rfl

/-- Under continuous bracket on `L` and locally constant orbit maps on `M`, differentials of
continuous `n`-cochains are continuous `(n + 1)`-cocycles. -/
theorem d_mem_continuousCocycle (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M n) :
    d R L M n ω ∈ continuousCocycle R L M (n + 1) :=
  ⟨d_mem_continuousCochain hL hM hω, d_d n ω⟩

theorem mem_continuousCoboundary_zero_iff {z : continuousCocycle R L M 0} :
    z ∈ continuousCoboundary R L M 0 ↔ z = 0 :=
  Submodule.mem_bot _

@[simp]
theorem mem_continuousCoboundary_succ_iff {n : ℕ} {z : continuousCocycle R L M (n + 1)} :
    z ∈ continuousCoboundary R L M (n + 1) ↔
      ∃ ω ∈ continuousCochain R L M n, d R L M n ω = z := by
  simp [continuousCoboundary]

/-- Since every `0`-cochain is continuous, a continuous `1`-cocycle is a continuous coboundary if
and only if it corresponds under `oneCochainEquiv` to a principal `1`-cochain `d₀₁ R L M m`. -/
theorem mem_continuousCoboundary_one_iff {z : continuousCocycle R L M 1} :
    z ∈ continuousCoboundary R L M 1 ↔
      ∃ m : M, d₀₁ R L M m = oneCochainEquiv R L M z.1 := by
  rw [mem_continuousCoboundary_succ_iff]
  refine ⟨fun ⟨ω, _, hω⟩ ↦ ⟨ω ![], ?_⟩, fun ⟨m, hm⟩ ↦ ?_⟩
  · rw [← oneCochainEquiv_d_zero, hω]
  · refine ⟨AlternatingMap.constOfIsEmpty R L (Fin 0) m, mem_continuousCochain_zero _, ?_⟩
    apply (oneCochainEquiv R L M).injective
    simpa [oneCochainEquiv_d_zero] using hm

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Descend a linear map on continuous `n`-cocycles that vanishes on continuous coboundaries to
degree-`n` continuous cohomology. -/
def continuousCohomologyLift {n : ℕ} (g : continuousCocycle R L M n →ₗ[R] N)
    (h : ∀ z ∈ continuousCoboundary R L M n, g z = 0) :
    continuousCohomology R L M n →ₗ[R] N :=
  (continuousCoboundary R L M n).liftQ g h

@[simp]
theorem continuousCohomologyLift_mk {n : ℕ} (g : continuousCocycle R L M n →ₗ[R] N)
    (h : ∀ z ∈ continuousCoboundary R L M n, g z = 0) (z : continuousCocycle R L M n) :
    continuousCohomologyLift g h (continuousCohomologyMk R L M n z) = g z :=
  (rfl)

theorem continuousCohomologyLift_unique {n : ℕ} (g : continuousCocycle R L M n →ₗ[R] N)
    (h : ∀ z ∈ continuousCoboundary R L M n, g z = 0)
    (f : continuousCohomology R L M n →ₗ[R] N)
    (hf : f ∘ₗ continuousCohomologyMk R L M n = g) :
    f = continuousCohomologyLift g h :=
  Submodule.linearMap_qext _ hf

/-- Two linear maps out of `continuousCohomology R L M n` agree once they agree on cocycle
representatives. -/
@[ext]
theorem continuousCohomology_hom_ext {n : ℕ}
    {f₁ f₂ : continuousCohomology R L M n →ₗ[R] N}
    (h : f₁ ∘ₗ continuousCohomologyMk R L M n = f₂ ∘ₗ continuousCohomologyMk R L M n) :
    f₁ = f₂ :=
  Submodule.linearMap_qext _ h

@[simp]
theorem continuousCohomologyMk_zero_eq_zero_iff (z : continuousCocycle R L M 0) :
    continuousCohomologyMk R L M 0 z = 0 ↔ z = 0 := by
  rw [continuousCohomologyMk_eq_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_continuousCoboundary_zero_iff]

@[simp]
theorem continuousCohomologyMk_succ_eq_zero_iff {n : ℕ} (z : continuousCocycle R L M (n + 1)) :
    continuousCohomologyMk R L M (n + 1) z = 0 ↔
      ∃ ω ∈ continuousCochain R L M n, d R L M n ω = z := by
  rw [continuousCohomologyMk_eq_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_continuousCoboundary_succ_iff]

theorem continuousCohomologyMk_succ_eq_iff {n : ℕ} (z w : continuousCocycle R L M (n + 1)) :
    continuousCohomologyMk R L M (n + 1) z = continuousCohomologyMk R L M (n + 1) w ↔
      ∃ ω ∈ continuousCochain R L M n,
        d R L M n ω = (z - w : continuousCocycle R L M (n + 1)) := by
  rw [← sub_eq_zero, ← map_sub, continuousCohomologyMk_succ_eq_zero_iff]

end Cohomology

section Functoriality

variable {R L L' L'' M M' M'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
  [LieRing L''] [LieAlgebra R L''] [TopologicalSpace L'']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']

/-- Pulling a continuous `n`-cocycle back along a continuous Lie algebra morphism `φ` and pushing
its values forward along an intertwining linear map `e` yields a continuous `n`-cocycle. -/
theorem cochainMap_mem_continuousCocycle (e : M →ₗ[R] M') {φ : L' →ₗ⁅R⁆ L}
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ continuousCocycle R L M n) :
    cochainMap e φ n ω ∈ continuousCocycle R L' M' n := by
  rw [mem_continuousCocycle_iff] at hω ⊢
  refine ⟨cochainMap_mem_continuousCochain e hφ hω.1, ?_⟩
  rw [← cochainMap_d e φ he, hω.2, map_zero]

/-- Pullback along `φ` and coefficient pushforward along `e`, restricted to continuous
`n`-cocycles. -/
def continuousCocycleMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) (n : ℕ) :
    continuousCocycle R L M n →ₗ[R] continuousCocycle R L' M' n :=
  (cochainMap e φ n).restrict fun _ hω ↦ cochainMap_mem_continuousCocycle e he hφ hω

@[simp]
theorem coe_continuousCocycleMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) {n : ℕ}
    (z : continuousCocycle R L M n) :
    (continuousCocycleMap e φ he hφ n z : L' [⋀^Fin n]→ₗ[R] M') = cochainMap e φ n z :=
  (rfl)

@[simp]
theorem continuousCocycleMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    {hφ : Continuous (LieHom.id : L →ₗ⁅R⁆ L)} (n : ℕ) :
    continuousCocycleMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he hφ n =
      LinearMap.id := by
  ext z : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (cochainMap_id n) z.1

theorem continuousCocycleMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆)
    (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    (continuousCocycleMap e' ψ he' hψ n).comp (continuousCocycleMap e φ he hφ n) =
      continuousCocycleMap (e'.comp e) (φ.comp ψ) (fun x m ↦ by simp [he, he'])
        (hφ.comp hψ) n := by
  ext z : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (cochainMap_comp e e' φ ψ n) z.1

/-- `continuousCocycleMap` maps continuous coboundaries into continuous coboundaries. -/
theorem continuousCocycleMap_mem_continuousCoboundary (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) {n : ℕ}
    {z : continuousCocycle R L M n} (hz : z ∈ continuousCoboundary R L M n) :
    continuousCocycleMap e φ he hφ n z ∈ continuousCoboundary R L' M' n := by
  cases n with
  | zero =>
    rw [mem_continuousCoboundary_zero_iff] at hz ⊢
    rw [hz, map_zero]
  | succ n =>
    obtain ⟨ω, hω, hdω⟩ := mem_continuousCoboundary_succ_iff.mp hz
    exact mem_continuousCoboundary_succ_iff.mpr
      ⟨cochainMap e φ n ω, cochainMap_mem_continuousCochain e hφ hω, by
        rw [← cochainMap_d e φ he, hdω, coe_continuousCocycleMap]⟩

/-- The linear map on degree-`n` continuous cohomology induced by a continuous Lie algebra morphism
`φ : L' →ₗ⁅R⁆ L` and an intertwining linear map `e : M →ₗ[R] M'`. -/
def continuousCohomologyMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) (n : ℕ) :
    continuousCohomology R L M n →ₗ[R] continuousCohomology R L' M' n :=
  (continuousCoboundary R L M n).mapQ (continuousCoboundary R L' M' n)
    (continuousCocycleMap e φ he hφ n)
    fun _ hz ↦ continuousCocycleMap_mem_continuousCoboundary e φ he hφ hz

@[simp]
theorem continuousCohomologyMap_mk (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ) {n : ℕ}
    (z : continuousCocycle R L M n) :
    continuousCohomologyMap e φ he hφ n (continuousCohomologyMk R L M n z) =
      continuousCohomologyMk R L' M' n (continuousCocycleMap e φ he hφ n z) :=
  (rfl)

@[simp]
theorem continuousCohomologyMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    {hφ : Continuous (LieHom.id : L →ₗ⁅R⁆ L)} (n : ℕ) :
    continuousCohomologyMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he hφ n =
      LinearMap.id := by
  simp only [continuousCohomologyMap, continuousCocycleMap_id, Submodule.mapQ_id]

theorem continuousCohomologyMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆)
    (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    (continuousCohomologyMap e' ψ he' hψ n).comp (continuousCohomologyMap e φ he hφ n) =
      continuousCohomologyMap (e'.comp e) (φ.comp ψ) (fun x m ↦ by simp [he, he'])
        (hφ.comp hψ) n := by
  simpa only [continuousCohomologyMap, continuousCocycleMap_comp] using
    (Submodule.mapQ_comp (continuousCoboundary R L M n)
      (continuousCoboundary R L' M' n) (continuousCoboundary R L'' M'' n)
      (continuousCocycleMap e φ he hφ n) (continuousCocycleMap e' ψ he' hψ n)
      (fun _ hz ↦ continuousCocycleMap_mem_continuousCoboundary e φ he hφ hz)
      (fun _ hz ↦ continuousCocycleMap_mem_continuousCoboundary e' ψ he' hψ hz)).symm

/-- Transport of degree-`n` continuous cohomology along a bicontinuous Lie equivalence and an
intertwining linear equivalence of coefficients. -/
def continuousCohomologyEquiv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    continuousCohomology R L M n ≃ₗ[R] continuousCohomology R L' M' n :=
  LinearEquiv.ofLinearMap (continuousCohomologyMap e.toLinearMap φ.toLieHom he hφ n)
    (continuousCohomologyMap e.symm.toLinearMap φ.symm.toLieHom
      (symm_lie_eq_of_lie_eq e φ he) hφ' n)
    (by
      have hp : φ.symm.toLieHom.comp φ.toLieHom = LieHom.id := by ext; simp
      simpa [e.comp_symm, hp] using
        continuousCohomologyMap_comp e.symm.toLinearMap e.toLinearMap
          φ.symm.toLieHom φ.toLieHom (symm_lie_eq_of_lie_eq e φ he) he hφ' hφ n)
    (by
      have hp : φ.toLieHom.comp φ.symm.toLieHom = LieHom.id := by ext; simp
      simpa [e.symm_comp, hp] using
        continuousCohomologyMap_comp e.toLinearMap e.symm.toLinearMap
          φ.toLieHom φ.symm.toLieHom he (symm_lie_eq_of_lie_eq e φ he) hφ hφ' n)

@[simp]
theorem continuousCohomologyEquiv_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    (continuousCohomologyEquiv e φ he hφ hφ' n).toLinearMap =
      continuousCohomologyMap e.toLinearMap φ.toLieHom he hφ n :=
  (rfl)

@[simp]
theorem continuousCohomologyEquiv_symm_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    (continuousCohomologyEquiv e φ he hφ hφ' n).symm.toLinearMap =
      continuousCohomologyMap e.symm.toLinearMap φ.symm.toLieHom
        (symm_lie_eq_of_lie_eq e φ he) hφ' n :=
  (rfl)

@[simp]
theorem continuousCohomologyEquiv_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) {n : ℕ}
    (x : continuousCohomology R L M n) :
    continuousCohomologyEquiv e φ he hφ hφ' n x =
      continuousCohomologyMap e.toLinearMap φ.toLieHom he hφ n x :=
  (rfl)

@[simp]
theorem continuousCohomologyEquiv_symm_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) {n : ℕ}
    (x : continuousCohomology R L' M' n) :
    (continuousCohomologyEquiv e φ he hφ hφ' n).symm x =
      continuousCohomologyMap e.symm.toLinearMap φ.symm.toLieHom
        (symm_lie_eq_of_lie_eq e φ he) hφ' n x :=
  (rfl)

end Functoriality

section Complex

section Differential

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Chevalley–Eilenberg differential restricted to continuous cochains, defined when the Lie
bracket of `L` is continuous and every orbit map `⁅·, m⁆ : L → M` is locally constant. -/
def continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCochain R L M n →ₗ[R] continuousCochain R L M (n + 1) :=
  (d R L M n).restrict fun _ hω ↦ d_mem_continuousCochain hL hM hω

variable {R L M}

@[simp]
theorem coe_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (ω : continuousCochain R L M n) :
    (continuousD R L M hL hM n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω :=
  (rfl)

@[simp]
theorem continuousD_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (ω : continuousCochain R L M n) :
    continuousD R L M hL hM (n + 1) (continuousD R L M hL hM n ω) = 0 :=
  Subtype.ext (d_d n ω.1)

theorem continuousD_comp_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousD R L M hL hM (n + 1) ∘ₗ continuousD R L M hL hM n = 0 :=
  LinearMap.ext (continuousD_continuousD hL hM n)

@[simp]
theorem continuousCohomologyMk_d (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (ω : continuousCochain R L M n) :
    continuousCohomologyMk R L M (n + 1) ⟨d R L M n ω.1, d_mem_continuousCocycle hL hM ω.2⟩ =
      0 :=
  (continuousCohomologyMk_succ_eq_zero_iff _).mpr ⟨ω.1, ω.2, rfl⟩

/-- `continuousCochainMap` commutes with `continuousD` when `e` intertwines the module actions
along `φ`. -/
theorem continuousCochainMap_comp_continuousD {L' M' : Type*}
    [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
    [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
    (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ) :
    (continuousCochainMap e φ hφ (n + 1)).comp (continuousD R L M hL hM n) =
      (continuousD R L' M' hL' hM' n).comp (continuousCochainMap e φ hφ n) := by
  ext ω : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_continuousCochainMap, coe_continuousD,
    cochainMap_d e φ he n ω.1]

end Differential

section CategoricalComplex

variable (R : Type u) [CommRing R]
variable (L M : Type v) [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The continuous Chevalley–Eilenberg cochain complex of `L` with discrete coefficients in `M`,
whose degree-`n` term is `continuousCochain R L M n` and whose differential is `continuousD`. -/
noncomputable def continuousCochainComplex (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (continuousCochain R L M n))
    (fun n ↦ ModuleCat.ofHom (continuousD R L M hL hM n))
    fun n ↦ ModuleCat.hom_ext (continuousD_comp_continuousD hL hM n)

/-- Canonical identification of the degree-`n` object of `continuousCochainComplex` with
`continuousCochain R L M n`. -/
noncomputable def continuousCochainComplexXIso (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplex R L M hL hM).X n ≅
      ModuleCat.of R (continuousCochain R L M n) :=
  Iso.refl _

/-- Under `continuousCochainComplexXIso`, the differential of `continuousCochainComplex` from
degree `n` to degree `n + 1` is `continuousD`. -/
@[reassoc, elementwise]
theorem continuousCochainComplex_d_succ (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplex R L M hL hM).d n (n + 1) ≫
        (continuousCochainComplexXIso R L M hL hM (n + 1)).hom =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousD R L M hL hM n) := by
  simp [continuousCochainComplex, continuousCochainComplexXIso]

/-- The subcomplex inclusion of `continuousCochainComplex` into the algebraic Chevalley–Eilenberg
complex `cochainComplex R L M`. -/
noncomputable def continuousCochainComplexι (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    continuousCochainComplex R L M hL hM ⟶ cochainComplex R L M :=
  CochainComplex.ofHom
    (fun n ↦ (continuousCochainComplexXIso R L M hL hM n).hom ≫
      ModuleCat.ofHom (continuousCochain R L M n).subtype)
    fun n ↦ by
      rw [cochainComplex_d_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      have hx := congrArg Subtype.val
        (continuousCochainComplex_d_succ_apply R L M hL hM n x).symm
      rw [coe_continuousD] at hx
      exact hx

@[simp, reassoc]
theorem continuousCochainComplexι_f (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplexι R L M hL hM).f n =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousCochain R L M n).subtype :=
  (rfl)

variable {R L M}
variable {L' L'' M' M'' : Type v}
  [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
  [LieRing L''] [LieAlgebra R L''] [TopologicalSpace L'']
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']

/-- The chain map on continuous Chevalley–Eilenberg complexes induced by a continuous Lie algebra
morphism `φ : L' →ₗ⁅R⁆ L` and an intertwining linear map `e : M →ₗ[R] M'`. -/
noncomputable def continuousCochainComplexMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) :
    continuousCochainComplex R L M hL hM ⟶ continuousCochainComplex R L' M' hL' hM' :=
  CochainComplex.ofHom
    (fun n ↦ (continuousCochainComplexXIso R L M hL hM n).hom ≫
      ModuleCat.ofHom (continuousCochainMap e φ hφ n) ≫
        (continuousCochainComplexXIso R L' M' hL' hM' n).inv)
    fun n ↦ by
      have hcomm : ModuleCat.ofHom (continuousCochainMap e φ hφ n) ≫
          ModuleCat.ofHom (continuousD R L' M' hL' hM' n) =
        ModuleCat.ofHom (continuousD R L M hL hM n) ≫
          ModuleCat.ofHom (continuousCochainMap e φ hφ (n + 1)) :=
        ModuleCat.hom_ext
          (continuousCochainMap_comp_continuousD e φ he hφ hL hM hL' hM' n).symm
      rw [(Iso.eq_comp_inv _).mpr (continuousCochainComplex_d_succ R L M hL hM n),
        (Iso.eq_comp_inv _).mpr (continuousCochainComplex_d_succ R L' M' hL' hM' n)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

@[reassoc, elementwise]
theorem continuousCochainComplexMap_f (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ) :
    (continuousCochainComplexMap e φ he hφ hL hM hL' hM').f n ≫
        (continuousCochainComplexXIso R L' M' hL' hM' n).hom =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousCochainMap e φ hφ n) := by
  simp [continuousCochainComplexMap]

@[simp]
theorem continuousCochainComplexMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    {hφ : Continuous (LieHom.id : L →ₗ⁅R⁆ L)}
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    continuousCochainComplexMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he hφ
        hL hM hL hM = 𝟙 (continuousCochainComplex R L M hL hM) := by
  ext n : 2
  simp [continuousCochainComplexMap]

theorem continuousCochainComplexMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M'))
    (hL'' : Continuous fun p : L'' × L'' ↦ ⁅p.1, p.2⁆)
    (hM'' : ∀ m'' : M'', IsLocallyConstant (⁅·, m''⁆ : L'' → M'')) :
    continuousCochainComplexMap e φ he hφ hL hM hL' hM' ≫
        continuousCochainComplexMap e' ψ he' hψ hL' hM' hL'' hM'' =
      continuousCochainComplexMap (e'.comp e) (φ.comp ψ)
        (fun x m ↦ by simp [he, he']) (hφ.comp hψ) hL hM hL'' hM'' := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f,
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f e φ he hφ hL hM hL' hM' n),
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f e' ψ he' hψ hL' hM' hL'' hM'' n),
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f (e'.comp e) (φ.comp ψ)
      (fun x m ↦ by simp [he, he']) (hφ.comp hψ) hL hM hL'' hM'' n)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (ModuleCat.ofHom (continuousCochainMap e φ hφ n)),
    ← ModuleCat.ofHom_comp, continuousCochainMap_comp]

/-- The subcomplex inclusion `continuousCochainComplexι` commutes with functoriality. -/
@[reassoc]
theorem continuousCochainComplexMap_comp_ι (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) :
    continuousCochainComplexMap e φ he hφ hL hM hL' hM' ≫
        continuousCochainComplexι R L' M' hL' hM' =
      continuousCochainComplexι R L M hL hM ≫ cochainComplexMap e φ he := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, continuousCochainComplexι_f,
    continuousCochainComplexι_f, cochainComplexMap_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hx := congrArg Subtype.val
    (continuousCochainComplexMap_f_apply e φ he hφ hL hM hL' hM' n x)
  rw [coe_continuousCochainMap] at hx
  exact hx

variable (R L M)

/-- The homology class in `(continuousCochainComplex R L M hL hM).homology n` attached to a
continuous `n`-cocycle. -/
noncomputable def continuousCohomologyClass (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCocycle R L M n →ₗ[R] (continuousCochainComplex R L M hL hM).homology n :=
  (continuousCochainComplex R L M hL hM).moduleCatHomologyClass (CochainComplex.next ℕ n)
    ((continuousCochainComplexXIso R L M hL hM n).inv.hom ∘ₗ
      continuousCocycleToCochain R L M n)
    fun z ↦ ((continuousCochainComplex R L M hL hM).moduleCat_d_inv_eq_zero_iff
      (continuousD R L M hL hM) (continuousCochainComplex_d_succ R L M hL hM)
      (continuousCocycleToCochain R L M n z)).mpr
        (Subtype.ext (mem_continuousCocycle_iff.mp z.2).2)

/-- Every homology class of `continuousCochainComplex` is represented by a continuous cocycle. -/
theorem continuousCohomologyClass_surjective (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    Function.Surjective (continuousCohomologyClass R L M hL hM n) := by
  refine (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_surjective _ _ _
    fun x hx ↦ ?_
  let ω := (continuousCochainComplexXIso R L M hL hM n).hom x
  have hdx : continuousD R L M hL hM n ω = 0 := by
    rw [← (continuousCochainComplex R L M hL hM).moduleCat_d_inv_eq_zero_iff
      (continuousD R L M hL hM) (continuousCochainComplex_d_succ R L M hL hM) ω]
    simpa [ω] using hx
  have hz : ω.1 ∈ continuousCocycle R L M n :=
    mem_continuousCocycle_iff.mpr ⟨ω.2, by simpa using congrArg Subtype.val hdx⟩
  refine ⟨⟨ω.1, hz⟩, ?_⟩
  have hco : continuousCocycleToCochain R L M n ⟨ω.1, hz⟩ = ω := Subtype.ext rfl
  simp [hco, ω]

/-- A continuous cocycle represents the zero homology class in `continuousCochainComplex` if and
only if it is a continuous coboundary. -/
@[simp]
theorem continuousCohomologyClass_eq_zero_iff (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (z : continuousCocycle R L M n) :
    continuousCohomologyClass R L M hL hM n z = 0 ↔
      z ∈ continuousCoboundary R L M n := by
  cases n with
  | zero =>
    rw [continuousCohomologyClass,
      (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_eq_zero_iff _ _ _
        CochainComplex.prev_nat_zero,
      mem_continuousCoboundary_zero_iff,
      (continuousCochainComplex R L M hL hM).shape 0 0 (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, LinearMap.comp_apply]
    refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ by simp [h]⟩
    have h' := congrArg (continuousCochainComplexXIso R L M hL hM 0).hom h.symm
    simpa using congrArg Subtype.val h'
  | succ n =>
    rw [continuousCohomologyClass,
      (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_eq_zero_iff _ _ _
        (CochainComplex.prev_nat_succ n),
      mem_continuousCoboundary_succ_iff]
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨ω, hω, hdω⟩ ↦ ?_⟩
    · let η := (continuousCochainComplexXIso R L M hL hM n).hom y
      refine ⟨η.1, η.2, ?_⟩
      have hy' := congrArg (continuousCochainComplexXIso R L M hL hM (n + 1)).hom hy
      rw [continuousCochainComplex_d_succ_apply, LinearMap.comp_apply,
        ModuleCat.Hom.hom, Iso.inv_hom_id_apply] at hy'
      simpa using congrArg Subtype.val hy'
    · refine ⟨(continuousCochainComplexXIso R L M hL hM n).inv ⟨ω, hω⟩, ?_⟩
      apply (ModuleCat.mono_iff_injective
        (continuousCochainComplexXIso R L M hL hM (n + 1)).hom).mp inferInstance
      rw [continuousCochainComplex_d_succ_apply]
      simp only [LinearMap.comp_apply, Iso.inv_hom_id_apply]
      exact Subtype.ext (by simpa using hdω)

/-- **Comparison with categorical homology.** When the Lie bracket of `L` is continuous and every
orbit map `⁅·, m⁆ : L → M` is locally constant, the concrete quotient
`continuousCohomology R L M n` is linearly equivalent to the degree-`n` homology of
`continuousCochainComplex R L M hL hM`. -/
noncomputable def continuousCohomologyHomologyEquiv
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCohomology R L M n ≃ₗ[R]
      (continuousCochainComplex R L M hL hM).homology n :=
  LinearEquiv.ofBijective
    (continuousCohomologyLift (continuousCohomologyClass R L M hL hM n)
      fun z hz ↦ (continuousCohomologyClass_eq_zero_iff R L M hL hM n z).mpr hz)
    ⟨by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro q hq
      obtain ⟨z, rfl⟩ := continuousCohomologyMk_surjective R L M n q
      rw [LinearMap.mem_ker, continuousCohomologyLift_mk,
        continuousCohomologyClass_eq_zero_iff] at hq
      rw [Submodule.mem_bot, continuousCohomologyMk_eq_mkQ, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hq,
     fun y ↦ by
      obtain ⟨z, rfl⟩ := continuousCohomologyClass_surjective R L M hL hM n y
      exact ⟨continuousCohomologyMk R L M n z, rfl⟩⟩

variable {R L M}

@[simp]
theorem continuousCohomologyHomologyEquiv_mk (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (z : continuousCocycle R L M n) :
    continuousCohomologyHomologyEquiv R L M hL hM n (continuousCohomologyMk R L M n z) =
      continuousCohomologyClass R L M hL hM n z :=
  (rfl)

/-- `continuousCohomologyHomologyEquiv` intertwines `continuousCohomologyMap` with `homologyMap` on
`continuousCochainComplexMap`. -/
theorem homologyMap_continuousCohomologyHomologyEquiv (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ)
    (q : continuousCohomology R L M n) :
    homologyMap (continuousCochainComplexMap e φ he hφ hL hM hL' hM') n
        (continuousCohomologyHomologyEquiv R L M hL hM n q) =
      continuousCohomologyHomologyEquiv R L' M' hL' hM' n
        (continuousCohomologyMap e φ he hφ n q) := by
  obtain ⟨z, rfl⟩ := continuousCohomologyMk_surjective R L M n q
  rw [continuousCohomologyMap_mk, continuousCohomologyHomologyEquiv_mk,
    continuousCohomologyHomologyEquiv_mk, continuousCohomologyClass, continuousCohomologyClass]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass (CochainComplex.next ℕ n) _ _
    (continuousCochainComplexMap e φ he hφ hL hM hL' hM') _ _
    (continuousCocycleMap e φ he hφ n) (fun w ↦ ?_) z
  apply (ModuleCat.mono_iff_injective
    (continuousCochainComplexXIso R L' M' hL' hM' n).hom).mp inferInstance
  rw [continuousCochainComplexMap_f_apply]
  simp only [LinearMap.comp_apply, ModuleCat.Hom.hom, Iso.inv_hom_id_apply]
  exact Subtype.ext (by simp)

end CategoricalComplex

end Complex

section LowDegree

section DegreeZero

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Continuous `0`-cocycles are linearly equivalent to the submodule `LieModule.maxTrivSubmodule`
of `L`-invariant elements of `M`. -/
def continuousCocycleZeroEquiv :
    continuousCocycle R L M 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  LinearEquiv.ofLinearMap
    { toFun z := ⟨z.1 ![], by
        rw [LieModule.mem_maxTrivSubmodule]
        intro x
        simpa [d_zero_apply] using
          congrFun (congrArg DFunLike.coe (mem_continuousCocycle_iff.mp z.2).2) ![x]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    { toFun m := ⟨AlternatingMap.constOfIsEmpty R L (Fin 0) m.1,
        mem_continuousCocycle_iff.mpr ⟨mem_continuousCochain_zero _, by
          ext v
          simpa [d_zero_apply] using m.2 (v 0)⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (by ext m; rfl)
    (by
      ext z v
      rw [Subsingleton.elim v ![]]
      rfl)

/-- Degree-zero continuous cohomology is linearly equivalent to `LieModule.maxTrivSubmodule R L M`.
-/
def continuousCohomologyZeroEquiv :
    continuousCohomology R L M 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  ((continuousCoboundary R L M 0).quotEquivOfEqBot rfl).trans (continuousCocycleZeroEquiv R L M)

variable {R L M}

@[simp]
theorem coe_continuousCocycleZeroEquiv (z : continuousCocycle R L M 0) :
    (continuousCocycleZeroEquiv R L M z : M) = z.1 ![] :=
  (rfl)

@[simp]
theorem continuousCohomologyZeroEquiv_mk (z : continuousCocycle R L M 0) :
    continuousCohomologyZeroEquiv R L M (continuousCohomologyMk R L M 0 z) =
      continuousCocycleZeroEquiv R L M z :=
  (rfl)

end DegreeZero

section DegreeTwo

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Over a topological additive group `L`, `twoCochainEquiv` maps `continuousCocycle R L M 2` onto
`continuousTwoCocycle R L M`. -/
@[simp]
theorem twoCochainEquiv_mem_continuousTwoCocycle_iff {ω : L [⋀^Fin 2]→ₗ[R] M} :
    twoCochainEquiv R L M ω ∈ continuousTwoCocycle R L M ↔
      ω ∈ continuousCocycle R L M 2 := by
  rw [mem_continuousTwoCocycle_iff, mem_continuousCocycle_iff,
    twoCochainEquiv_mem_continuousTwoCochain_iff, mem_twoCocycle_iff]
  refine and_congr_right' ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext v
    have hv : v = ![v 0, v 1, v 2] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, ← d₂₃_twoCochainEquiv, h]
    rfl
  · ext x y z
    rw [d₂₃_twoCochainEquiv, h]
    rfl

variable (R L M)

/-- Continuous `2`-cocycles are linearly equivalent to `continuousTwoCocycle R L M`. -/
def continuousCocycleTwoEquiv :
    continuousCocycle R L M 2 ≃ₗ[R] continuousTwoCocycle R L M :=
  LinearEquiv.ofLinearMap
    ((twoCochainEquiv R L M).toLinearMap.restrict fun _ hω ↦
      twoCochainEquiv_mem_continuousTwoCocycle_iff.mpr hω)
    ((twoCochainEquiv R L M).symm.toLinearMap.restrict fun c hc ↦ by
      rw [← twoCochainEquiv_mem_continuousTwoCocycle_iff]
      simpa using hc)
    (by ext c; simp)
    (by ext ω; simp)

variable {R L M}

@[simp]
theorem coe_continuousCocycleTwoEquiv (z : continuousCocycle R L M 2) :
    (continuousCocycleTwoEquiv R L M z : twoCochain R L M) = twoCochainEquiv R L M z.1 :=
  (rfl)

@[simp]
theorem coe_continuousCocycleTwoEquiv_symm (c : continuousTwoCocycle R L M) :
    ((continuousCocycleTwoEquiv R L M).symm c : L [⋀^Fin 2]→ₗ[R] M) =
      (twoCochainEquiv R L M).symm c.1 :=
  (rfl)

/-- `continuousCocycleTwoEquiv` carries `continuousCoboundary R L M 2` onto
`continuousTwoCoboundary R L M`. -/
@[simp]
theorem map_continuousCocycleTwoEquiv_continuousCoboundary :
    (continuousCoboundary R L M 2).map (continuousCocycleTwoEquiv R L M).toLinearMap =
      continuousTwoCoboundary R L M := by
  ext c
  simp only [Submodule.mem_map, mem_continuousCoboundary_succ_iff, mem_continuousTwoCoboundary_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, ⟨ω, hω, hdω⟩, rfl⟩
    refine ⟨oneCochainEquiv R L M ω, oneCochainEquiv_mem_continuousOneCochain_iff.mpr hω, ?_⟩
    simp [← twoCochainEquiv_d_one, hdω]
  · rintro ⟨f, hf, hdf⟩
    refine ⟨(continuousCocycleTwoEquiv R L M).symm c,
      ⟨(oneCochainEquiv R L M).symm f, ?_, ?_⟩,
      (continuousCocycleTwoEquiv R L M).apply_symm_apply c⟩
    · rw [← oneCochainEquiv_mem_continuousOneCochain_iff]
      simpa using hf
    · apply (twoCochainEquiv R L M).injective
      simpa [twoCochainEquiv_d_one] using hdf

variable (R L M)

/-- **Degree-two comparison.** Over a topological additive group `L`, degree-two continuous
cohomology `continuousCohomology R L M 2` is linearly equivalent to
`continuousSecondCohomology R L M`. -/
def continuousCohomologyTwoEquiv :
    continuousCohomology R L M 2 ≃ₗ[R] continuousSecondCohomology R L M :=
  Submodule.Quotient.equiv (continuousCoboundary R L M 2) (continuousTwoCoboundary R L M)
    (continuousCocycleTwoEquiv R L M) map_continuousCocycleTwoEquiv_continuousCoboundary

variable {R L M}

@[simp]
theorem continuousCohomologyTwoEquiv_mk (z : continuousCocycle R L M 2) :
    continuousCohomologyTwoEquiv R L M (continuousCohomologyMk R L M 2 z) =
      continuousSecondCohomologyMk R L M (continuousCocycleTwoEquiv R L M z) := by
  rw [continuousCohomologyTwoEquiv, continuousCohomologyMk_eq_mkQ,
    continuousSecondCohomologyMk_eq_mkQ]
  rfl

@[simp]
theorem continuousCohomologyTwoEquiv_symm_mk (c : continuousTwoCocycle R L M) :
    (continuousCohomologyTwoEquiv R L M).symm (continuousSecondCohomologyMk R L M c) =
      continuousCohomologyMk R L M 2 ((continuousCocycleTwoEquiv R L M).symm c) := by
  rw [continuousCohomologyTwoEquiv, continuousCohomologyMk_eq_mkQ,
    continuousSecondCohomologyMk_eq_mkQ]
  rfl

/-- With discrete trivial coefficients, `continuousCohomologyTwoEquiv` intertwines
`continuousCohomologyMap` in degree two with `continuousSecondCohomologyMap`. -/
theorem continuousCohomologyTwoEquiv_continuousCohomologyMap {L' M' : Type*}
    [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L'] [IsTopologicalAddGroup L']
    [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M']
    (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    {he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆} (hφ : Continuous φ)
    (q : continuousCohomology R L M 2) :
    continuousCohomologyTwoEquiv R L' M' (continuousCohomologyMap e φ he hφ 2 q) =
      continuousSecondCohomologyMap e φ hφ (continuousCohomologyTwoEquiv R L M q) := by
  obtain ⟨z, rfl⟩ := continuousCohomologyMk_surjective R L M 2 q
  rw [continuousCohomologyMap_mk, continuousCohomologyTwoEquiv_mk, continuousCohomologyTwoEquiv_mk,
    continuousSecondCohomologyMap_mk]
  congr 1
  apply Subtype.ext
  rw [coe_continuousCocycleTwoEquiv, coe_continuousCocycleMap, coe_continuousTwoCocycleMap,
    coe_continuousCocycleTwoEquiv]
  exact twoCochainEquiv_cochainMap e φ z.1

end DegreeTwo

end LowDegree

end TauCeti.LieModule.Cohomology
