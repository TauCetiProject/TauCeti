/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.LowDimTopology.Plumbing.Covector.Cube
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The completed lattice complex on characteristic covectors

Let `P` be a plumbing graph. The lattice complex on characteristic covectors
(`TauCeti.PlumbingGraph.covectorDifferential`) is the free `𝔽₂[U]`-module on the generators
`[K, E]`, with finitely supported chains. Zemke's comparison of lattice homology with Heegaard
Floer homology is stated for its **completion** over `𝔽₂[[U]]`, which this file constructs.

The completion used is the full direct product over the generators: a completed chain is an
arbitrary function `c : [K, E] ↦ c [K, E] ∈ 𝔽₂[[U]]`
(`TauCeti.PlumbingGraph.CompletedCovectorChain`), with no condition on its support. It is
neither the direct sum `⊕ 𝔽₂[[U]]`, the base change of the finite-support complex, nor the
`U`-adic completion of the finite-support complex, the restricted product of the functions with
`c [K, E] → 0` in the `U`-adic topology: those are proper submodules of it as soon as there are
infinitely many generators.

The differential extends to the product because every generator is a face of only finitely many
generators: `D = [K, E]` can occur only in the differentials of `[K, E ∪ {v}]` and of
`[K - 2 v*, E ∪ {v}]` for `v ∉ E`
(`TauCeti.PlumbingGraph.finite_setOf_covectorDifferentialOnGenerator_apply_ne_zero`). So the
completed differential

`(∂ c) D = ∑ᶠ C, ⟨∂ C, D⟩ c C`

(`TauCeti.PlumbingGraph.completedCovectorDifferential`), where `⟨∂ C, D⟩ ∈ 𝔽₂[U]` is the coefficient
of `D` in the differential of the generator `C`, is a finite sum in every component. It is
`𝔽₂[[U]]`-linear and squares to zero
(`TauCeti.PlumbingGraph.completedCovectorDifferential_comp_self`), because the coefficient of `D`
in `∂ ∂ C` is the finite sum `∑_B ⟨∂ C, B⟩ ⟨∂ B, D⟩`, which vanishes by
`TauCeti.PlumbingGraph.covectorDifferential_comp_self`.

The coefficient change from the finite-support complex sends a chain to the function of its
coefficients, read as power series (`TauCeti.PlumbingGraph.covectorChainToCompleted`). It is an
injective chain map
(`TauCeti.PlumbingGraph.completedCovectorDifferential_covectorChainToCompleted`), but not onto
(`TauCeti.PlumbingGraph.not_surjective_covectorChainToCompleted`): `1 + U` is a unit of
`𝔽₂[[U]]`, with inverse `1 + U + U² + ⋯`, so multiplication by `1 + U` is bijective on completed
chains, while no polynomial inverts `1 + U` in `𝔽₂[U]`, so it is not onto on the finite-support
chains (`TauCeti.PlumbingGraph.single_notMem_range_smul_one_add_X`). So completing changes the
carrier.

The completed lattice homology is the homology of the completed differential, as a module over
`𝔽₂[[U]]` (`TauCeti.PlumbingGraph.completedCovectorHomology`). A completed cycle `c` gives the
`𝔽₂[[U]]`-linear map `φ ↦ [φ c]` into it
(`TauCeti.PlumbingGraph.completedCovectorHomologyCycleMap`).

## Main definitions

* `TauCeti.PlumbingGraph.CompletedCovectorChain`: the completed chains, the product of copies of
  `𝔽₂[[U]]` over the generators `[K, E]`.
* `TauCeti.PlumbingGraph.completedCovectorDifferential`: the completed differential.
* `TauCeti.PlumbingGraph.covectorChainToCompleted`: the coefficient change from the
  finite-support complex.
* `TauCeti.PlumbingGraph.completedCovectorShortComplex`,
  `TauCeti.PlumbingGraph.completedCovectorHomology`: the completed lattice homology.
* `TauCeti.PlumbingGraph.completedCovectorHomologyCycleMap`: the map sending a power series to the
  class of its multiple of a completed cycle.

## Main results

* `TauCeti.PlumbingGraph.finite_setOf_covectorDifferentialOnGenerator_apply_ne_zero`: a generator
  is a face of finitely many generators.
* `TauCeti.PlumbingGraph.completedCovectorDifferential_apply`,
  `TauCeti.PlumbingGraph.completedCovectorDifferential_apply_eq_sum`: the components of the
  completed differential.
* `TauCeti.PlumbingGraph.completedCovectorDifferential_comp_self`: `∂ ∘ ∂ = 0`.
* `TauCeti.PlumbingGraph.completedCovectorDifferential_covectorChainToCompleted`: the coefficient
  change is a chain map; `TauCeti.PlumbingGraph.covectorChainToCompleted_injective`: it is
  injective.
* `TauCeti.PlumbingGraph.bijective_smul_one_add_X_completedCovectorChain`,
  `TauCeti.PlumbingGraph.single_notMem_range_smul_one_add_X` and
  `TauCeti.PlumbingGraph.not_surjective_covectorChainToCompleted`: `1 + U` acts bijectively on the
  completed chains but not on the finite-support chains, so the coefficient change is not onto.
* `TauCeti.PlumbingGraph.completedCovectorHomologyCycleMap_apply_eq_zero_iff`,
  `TauCeti.PlumbingGraph.completedCovectorHomologyCycleMap_surjective`: when a class of a
  completed cycle vanishes, and when it generates the completed lattice homology.

## References

* I. Zemke, *The equivalence of lattice and Heegaard Floer homology*,
  [arXiv:2111.14962](https://arxiv.org/abs/2111.14962), §2.3 (the complex on the generators
  `[K, E]` over `𝔽[[U]]`, as a direct product over the generators).
-/

public section

open CategoryTheory

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-! ### Cofaces of a generator -/

/-- The generators of which `D = [K, E]` can be a codimension-one face: `[K, E ∪ {v}]` and
`[K - 2 v*, E ∪ {v}]` for `v ∉ E`. -/
private noncomputable def covectorCofaces (D : P.CovectorCube) : Finset P.CovectorCube := by
  classical
  exact (Finset.univ.filter (· ∉ D.directions)).biUnion fun v =>
    {⟨D.covector, insert v D.directions⟩,
      ⟨P.addTwoMulVec D.covector (-Pi.single v 1), insert v D.directions⟩}

/-- A generator whose differential involves `D` is a coface of `D`. -/
private theorem mem_covectorCofaces_of_apply_ne_zero {C D : P.CovectorCube}
    (h : P.covectorDifferentialOnGenerator C D ≠ 0) : C ∈ P.covectorCofaces D := by
  classical
  obtain ⟨K, E⟩ := C
  rw [covectorDifferentialOnGenerator_mk, Finsupp.finsetSum_apply] at h
  obtain ⟨⟨v, hv⟩, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [covectorCofaces, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases h₁ : (⟨K, E.erase v⟩ : P.CovectorCube) = D
  · subst h₁
    exact ⟨v, Finset.notMem_erase v E, Or.inl (by rw [Finset.insert_erase hv])⟩
  by_cases h₂ : (⟨P.addTwoMulVec K (Pi.single v 1), E.erase v⟩ : P.CovectorCube) = D
  · subst h₂
    refine ⟨v, Finset.notMem_erase v E, Or.inr ?_⟩
    rw [Finset.insert_erase hv, addTwoMulVec_addTwoMulVec, add_neg_cancel, addTwoMulVec_zero]
  simp [h₁, h₂] at hne

/-- **Every generator is a face of only finitely many generators.** The generators `C` whose
differential involves a given generator `D` form a finite set. This is what lets the differential
extend to the completed chains, which have arbitrary support. -/
theorem finite_setOf_covectorDifferentialOnGenerator_apply_ne_zero (D : P.CovectorCube) :
    {C | P.covectorDifferentialOnGenerator C D ≠ 0}.Finite :=
  (P.covectorCofaces D).finite_toSet.subset fun _ hC => P.mem_covectorCofaces_of_apply_ne_zero hC

/-! ### Completed chains and the completed differential -/

omit [DecidableEq V] [Fintype V] in
/-- The completed chains of the lattice complex on characteristic covectors: the direct product,
over the generators `[K, E]`, of copies of `𝔽₂[[U]]`. A completed chain is an arbitrary function
from the generators to `𝔽₂[[U]]`, with no condition on its support. -/
abbrev CompletedCovectorChain : Type _ := P.CovectorCube → PowerSeries (ZMod 2)

/-- The completed differential. Its component at a generator `D` is the finite sum, over the
generators `C` whose differential involves `D`, of the coefficient of `D` in the differential of `C`
times the component of the chain at `C` (`completedCovectorDifferential_apply`). -/
noncomputable def completedCovectorDifferential :
    P.CompletedCovectorChain →ₗ[PowerSeries (ZMod 2)] P.CompletedCovectorChain where
  toFun c D := ∑ C ∈ P.covectorCofaces D,
    (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) * c C
  map_add' c d := by
    funext D
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext D
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun C _ => mul_left_comm _ _ _

/-- The terms of the sum defining a component of the completed differential vanish outside any set
containing the generators whose differential involves that component. -/
private theorem support_mul_subset (c : P.CompletedCovectorChain) (D : P.CovectorCube)
    {s : Set P.CovectorCube} (hs : ∀ C, P.covectorDifferentialOnGenerator C D ≠ 0 → C ∈ s) :
    (Function.support fun C =>
      (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) * c C) ⊆ s :=
  fun C hC => hs C fun h0 => hC (by simp only [h0, Polynomial.coe_zero, zero_mul])

/-- **The components of the completed differential.** The component at `D` is the sum, over all
generators `C`, of the coefficient of `D` in the differential of `C` times the component of the
chain at `C`; only finitely many terms are nonzero
(`finite_setOf_covectorDifferentialOnGenerator_apply_ne_zero`). -/
theorem completedCovectorDifferential_apply (c : P.CompletedCovectorChain) (D : P.CovectorCube) :
    P.completedCovectorDifferential c D =
      ∑ᶠ C, (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) * c C :=
  -- By definition the component is the sum over the cofaces of `D`.
  (finsum_eq_sum_of_support_subset _
    (P.support_mul_subset c D fun _ => P.mem_covectorCofaces_of_apply_ne_zero)).symm

/-- The component at `D` of the completed differential is a sum over any finite set containing the
generators whose differential involves `D`. -/
theorem completedCovectorDifferential_apply_eq_sum (c : P.CompletedCovectorChain)
    (D : P.CovectorCube) {s : Finset P.CovectorCube}
    (hs : ∀ C, P.covectorDifferentialOnGenerator C D ≠ 0 → C ∈ s) :
    P.completedCovectorDifferential c D =
      ∑ C ∈ s, (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) * c C := by
  rw [completedCovectorDifferential_apply]
  exact finsum_eq_sum_of_support_subset _ (P.support_mul_subset c D hs)

/-- The completed differential of the chain supported at a single generator `C` with value `φ` is
`φ` times the differential of `C`, read as power series. -/
@[simp]
theorem completedCovectorDifferential_single [DecidableEq P.CovectorCube] (C : P.CovectorCube)
    (φ : PowerSeries (ZMod 2)) :
    P.completedCovectorDifferential (Pi.single C φ) =
      fun D => φ * (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) := by
  funext D
  rw [P.completedCovectorDifferential_apply_eq_sum _ D (s := {C} ∪ P.covectorCofaces D)
    fun B hB => Finset.mem_union_right _ (P.mem_covectorCofaces_of_apply_ne_zero hB),
    Finset.sum_eq_single_of_mem C (Finset.mem_union_left _ (Finset.mem_singleton_self C))
      fun B _ hB => by rw [Pi.single_eq_of_ne hB, mul_zero],
    Pi.single_eq_same, mul_comm]

/-- **The completed differential squares to zero.** -/
theorem completedCovectorDifferential_comp_self :
    P.completedCovectorDifferential ∘ₗ P.completedCovectorDifferential = 0 := by
  classical
  refine LinearMap.ext fun c => funext fun D => ?_
  set s := P.covectorCofaces D
  set T := s.biUnion P.covectorCofaces
  have hs : ∀ C, P.covectorDifferentialOnGenerator C D ≠ 0 → C ∈ s :=
    fun C => P.mem_covectorCofaces_of_apply_ne_zero
  have hinner : ∀ C ∈ s, P.completedCovectorDifferential c C =
      ∑ B ∈ T, (P.covectorDifferentialOnGenerator B C : PowerSeries (ZMod 2)) * c B :=
    fun C hC => P.completedCovectorDifferential_apply_eq_sum c C fun B hB =>
      Finset.mem_biUnion.mpr ⟨C, hC, P.mem_covectorCofaces_of_apply_ne_zero hB⟩
  -- The coefficient of `D` in `∂ ∂ B` vanishes, and is the inner sum below.
  have hcoeff : ∀ B, ∑ C ∈ s,
      P.covectorDifferentialOnGenerator B C * P.covectorDifferentialOnGenerator C D = 0 := by
    intro B
    rw [← P.covectorDifferential_apply_eq_sum _ D hs]
    simpa using congr_arg (fun x : P.CovectorChain => x D)
      (P.covectorDifferential_covectorDifferential (Finsupp.single B 1))
  rw [LinearMap.comp_apply, P.completedCovectorDifferential_apply_eq_sum _ D hs,
    Finset.sum_congr rfl fun C hC => by rw [hinner C hC], LinearMap.zero_apply, Pi.zero_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun B _ => ?_
  calc ∑ C ∈ s, (P.covectorDifferentialOnGenerator C D : PowerSeries (ZMod 2)) *
        ((P.covectorDifferentialOnGenerator B C : PowerSeries (ZMod 2)) * c B)
      = ((∑ C ∈ s, P.covectorDifferentialOnGenerator B C *
          P.covectorDifferentialOnGenerator C D : PlumbingCoefficient) : PowerSeries (ZMod 2)) *
          c B := by
        rw [Polynomial.coe_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun C _ => by rw [Polynomial.coe_mul]; ring
    _ = 0 := by rw [hcoeff B, Polynomial.coe_zero, zero_mul]

/-- The completed differential of the completed differential of any completed chain vanishes. -/
@[simp]
theorem completedCovectorDifferential_completedCovectorDifferential
    (c : P.CompletedCovectorChain) :
    P.completedCovectorDifferential (P.completedCovectorDifferential c) = 0 :=
  LinearMap.congr_fun P.completedCovectorDifferential_comp_self c

/-! ### The coefficient change from finitely supported chains -/

/-- The coefficient change from the finite-support lattice complex to the completed one: a
finitely supported chain is sent to the function of its coefficients, read as power series. -/
noncomputable def covectorChainToCompleted :
    P.CovectorChain →ₗ[PlumbingCoefficient] P.CompletedCovectorChain :=
  (Algebra.linearMap PlumbingCoefficient (PowerSeries (ZMod 2))).compLeft P.CovectorCube ∘ₗ
    Finsupp.lcoeFun

omit [DecidableEq V] [Fintype V] in
/-- The components of the coefficient change are the coefficients, read as power series. -/
@[simp]
theorem covectorChainToCompleted_apply (x : P.CovectorChain) (C : P.CovectorCube) :
    P.covectorChainToCompleted x C = (x C : PowerSeries (ZMod 2)) :=
  (rfl)

omit [DecidableEq V] [Fintype V] in
/-- The coefficient change sends the chain `a [C]` to the completed chain supported at `C` with
value `a`. -/
@[simp]
theorem covectorChainToCompleted_single [DecidableEq P.CovectorCube] (C : P.CovectorCube)
    (a : PlumbingCoefficient) :
    P.covectorChainToCompleted (Finsupp.single C a) = Pi.single C (a : PowerSeries (ZMod 2)) := by
  funext D
  rcases eq_or_ne D C with rfl | h
  · simp
  · simp [h]

omit [DecidableEq V] [Fintype V] in
/-- The coefficient change is injective. -/
theorem covectorChainToCompleted_injective : Function.Injective P.covectorChainToCompleted :=
  fun _ _ h => Finsupp.ext fun C => Polynomial.coe_injective _ (congr_fun h C)

/-- **The coefficient change is a chain map**: it intertwines the differential of the
finite-support lattice complex with the completed differential. -/
theorem completedCovectorDifferential_covectorChainToCompleted (x : P.CovectorChain) :
    P.completedCovectorDifferential (P.covectorChainToCompleted x) =
      P.covectorChainToCompleted (P.covectorDifferential x) := by
  funext D
  have hs : ∀ C, P.covectorDifferentialOnGenerator C D ≠ 0 → C ∈ P.covectorCofaces D :=
    fun C => P.mem_covectorCofaces_of_apply_ne_zero
  rw [P.completedCovectorDifferential_apply_eq_sum _ D hs, covectorChainToCompleted_apply,
    P.covectorDifferential_apply_eq_sum x D hs, Polynomial.coe_sum]
  exact Finset.sum_congr rfl fun C _ => by
    rw [covectorChainToCompleted_apply, Polynomial.coe_mul, mul_comm]

/-- The coefficient change is a chain map, as an identity of `𝔽₂[U]`-linear maps. -/
theorem completedCovectorDifferential_comp_covectorChainToCompleted :
    P.completedCovectorDifferential.restrictScalars PlumbingCoefficient ∘ₗ
        P.covectorChainToCompleted =
      P.covectorChainToCompleted ∘ₗ P.covectorDifferential :=
  LinearMap.ext P.completedCovectorDifferential_covectorChainToCompleted

/-! ### Completing changes the carrier -/

omit [DecidableEq V] [Fintype V] in
/-- **`1 + U` acts bijectively on the completed chains**, since `1 + U` is a unit of `𝔽₂[[U]]`,
with inverse `1 + U + U² + ⋯`. -/
theorem bijective_smul_one_add_X_completedCovectorChain :
    Function.Bijective fun c : P.CompletedCovectorChain =>
      (1 + PowerSeries.X : PowerSeries (ZMod 2)) • c :=
  IsUnit.smul_bijective (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp))

omit [DecidableEq V] [Fintype V] in
/-- **`1 + U` does not act surjectively on the finite-support chains**: no finitely supported
chain `x` has `(1 + U) x = [C]`, since its coefficient at `C` would be an inverse of `1 + U` in
`𝔽₂[U]`. -/
theorem single_notMem_range_smul_one_add_X (C : P.CovectorCube) :
    Finsupp.single C 1 ∉
      Set.range fun x : P.CovectorChain => (1 + Polynomial.X : PlumbingCoefficient) • x := by
  rintro ⟨x, hx⟩
  have h : (1 + Polynomial.X : PlumbingCoefficient) * x C = 1 := by
    simpa using congr_arg (fun y : P.CovectorChain => y C) hx
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit (IsUnit.of_mul_eq_one _ h)
  rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C] at hdeg
  exact one_ne_zero hdeg

omit [DecidableEq V] [Fintype V] in
/-- **The coefficient change is not onto**: some completed chain is not the image of a finitely
supported chain. -/
theorem not_surjective_covectorChainToCompleted :
    ¬ Function.Surjective P.covectorChainToCompleted := by
  intro hsurj
  set C : P.CovectorCube :=
    ⟨⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩, ∅⟩
  obtain ⟨c, hc⟩ := (P.bijective_smul_one_add_X_completedCovectorChain).2
    (P.covectorChainToCompleted (Finsupp.single C 1))
  obtain ⟨x, rfl⟩ := hsurj c
  refine P.single_notMem_range_smul_one_add_X C ⟨x, P.covectorChainToCompleted_injective ?_⟩
  rw [map_smul, ← hc]
  funext D
  simp only [Pi.smul_apply, Polynomial.smul_eq_coe_mul, smul_eq_mul,
    Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]

/-! ### Completed lattice homology -/

/-- The short complex with the completed differential in both positions, over `𝔽₂[[U]]`. -/
noncomputable def completedCovectorShortComplex : ShortComplex (ModuleCat (PowerSeries (ZMod 2))) :=
  ShortComplex.moduleCatMk P.completedCovectorDifferential P.completedCovectorDifferential
    P.completedCovectorDifferential_comp_self

/-- The left object of the completed short complex is the module of completed chains. -/
@[simp]
theorem completedCovectorShortComplex_X₁ :
    P.completedCovectorShortComplex.X₁ =
      ModuleCat.of (PowerSeries (ZMod 2)) P.CompletedCovectorChain := (rfl)

/-- The middle object of the completed short complex is the module of completed chains. -/
@[simp]
theorem completedCovectorShortComplex_X₂ :
    P.completedCovectorShortComplex.X₂ =
      ModuleCat.of (PowerSeries (ZMod 2)) P.CompletedCovectorChain := (rfl)

/-- The right object of the completed short complex is the module of completed chains. -/
@[simp]
theorem completedCovectorShortComplex_X₃ :
    P.completedCovectorShortComplex.X₃ =
      ModuleCat.of (PowerSeries (ZMod 2)) P.CompletedCovectorChain := (rfl)

/-- The left map of the completed short complex is the completed differential. -/
@[simp]
theorem completedCovectorShortComplex_f :
    HEq P.completedCovectorShortComplex.f (ModuleCat.ofHom P.completedCovectorDifferential) :=
  (HEq.rfl)

/-- The right map of the completed short complex is the completed differential. -/
@[simp]
theorem completedCovectorShortComplex_g :
    HEq P.completedCovectorShortComplex.g (ModuleCat.ofHom P.completedCovectorDifferential) :=
  (HEq.rfl)

/-- Exactness of the completed short complex says that the boundaries of the completed
differential are all of its cycles. -/
theorem completedCovectorShortComplex_exact_iff_range_eq_ker :
    P.completedCovectorShortComplex.Exact ↔
      LinearMap.range P.completedCovectorDifferential =
        LinearMap.ker P.completedCovectorDifferential :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker _

/-- The completed lattice homology: the homology of the completed differential, as a module over
`𝔽₂[[U]]`. -/
noncomputable def completedCovectorHomology : ModuleCat (PowerSeries (ZMod 2)) :=
  P.completedCovectorShortComplex.homology

/-- The completed lattice homology is the homology of the completed short complex. -/
@[simp]
theorem completedCovectorHomology_def :
    P.completedCovectorHomology = P.completedCovectorShortComplex.homology :=
  (rfl)

/-- The linear map sending `φ : 𝔽₂[[U]]` to the completed homology class of `φ • c`, for a
completed cycle `c`. -/
noncomputable def completedCovectorHomologyCycleMap (c : P.CompletedCovectorChain)
    (hc : P.completedCovectorDifferential c = 0) :
    PowerSeries (ZMod 2) →ₗ[PowerSeries (ZMod 2)] P.completedCovectorHomology :=
  P.completedCovectorShortComplex.moduleCatCycleMap ⟨c, hc⟩

/-- A power series maps to zero under `completedCovectorHomologyCycleMap` exactly when its multiple
of the cycle is a completed boundary. -/
@[simp]
theorem completedCovectorHomologyCycleMap_apply_eq_zero_iff (c : P.CompletedCovectorChain)
    (hc : P.completedCovectorDifferential c = 0) (φ : PowerSeries (ZMod 2)) :
    P.completedCovectorHomologyCycleMap c hc φ = 0 ↔
      φ • c ∈ LinearMap.range P.completedCovectorDifferential :=
  P.completedCovectorShortComplex.moduleCatCycleMap_apply_eq_zero_iff ⟨c, hc⟩ φ

/-- A completed cycle whose class generates the completed lattice homology: if every completed
cycle differs from a multiple of `c` by a completed boundary, then
`completedCovectorHomologyCycleMap` is surjective. -/
theorem completedCovectorHomologyCycleMap_surjective (c : P.CompletedCovectorChain)
    (hc : P.completedCovectorDifferential c = 0)
    (hgen : ∀ z : P.CompletedCovectorChain, P.completedCovectorDifferential z = 0 →
      ∃ φ : PowerSeries (ZMod 2), z - φ • c ∈ LinearMap.range P.completedCovectorDifferential) :
    Function.Surjective (P.completedCovectorHomologyCycleMap c hc) :=
  P.completedCovectorShortComplex.moduleCatCycleMap_surjective ⟨c, hc⟩
    fun z => hgen z.val z.property

end PlumbingGraph

end TauCeti
