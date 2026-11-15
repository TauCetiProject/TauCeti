/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.ProfiniteFlat.Pseudobasis

/-!
# Examples and non-examples of profinite flat modules

Over a compact Hausdorff discrete valuation ring `O` (with primary concrete case `ℤ_[p]`), we
exercise `TauCeti.Huber.IsProfiniteFlat` and `TauCeti.Huber.IsProfiniteFlat.iff_exists_pseudobasis`:

* **Formal power series**: `MvPowerSeries (Fin d) ℤ_[p]` carries the maximal-ideal-adic topology
  and is profinite flat over `ℤ_[p]`; `PowerSeries ℤ_[p]` has an explicit pseudobasis indexed by
  `ℕ` sending the standard topological generators `Pi.single n 1` to `X ^ n`.
* **Degenerate and finite-rank cases**: `PUnit` (`I = PEmpty`), `O`, and `Fin n → O`.
* **Non-examples**:
  1. `ℤ_[p] ⧸ maximalIdeal ℤ_[p]` is a compact `ℤ_[p]`-module (compact, Hausdorff, and linearly
     topologized), but is torsion and hence neither flat nor profinite flat.
  2. A rank-`1` free `ℤ_[p]`-module equipped with the discrete topology `⊥` is flat, Hausdorff, and
     linearly topologized, but not compact and hence not profinite flat.
  3. `ℚ_[p]` is a flat, Hausdorff, linearly topologized `ℤ_[p]`-module, but is not compact and
     hence not profinite flat.
  4. A rank-`1` free `ℤ_[p]`-module equipped with the indiscrete topology `⊤` is flat, compact, and
     linearly topologized (`⊤` is the unique open submodule), but is not Hausdorff, is not
     profinite flat, and admits no continuous `ℤ_[p]`-linear equivalence to `I → ℤ_[p]`.

## References

* P. Chojecki, D. Hansen, and C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*, Doc. Math. 22 (2017), §6.1, Definition 6.1 and Proposition 6.2.
-/

open Topology
open TauCeti TauCeti.Huber

section DegenerateAndFinite

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]

-- The zero module PUnit is profinite flat, with empty pseudobasis index PEmpty.
example : IsProfiniteFlat O PUnit ∧ Nonempty (PUnit ≃L[O] (PEmpty → O)) :=
  ⟨.subsingleton, ⟨{
    toFun := fun _ i ↦ i.elim
    map_add' := fun _ _ ↦ funext fun i ↦ i.elim
    map_smul' := fun _ _ ↦ funext fun i ↦ i.elim
    invFun := fun _ ↦ PUnit.unit
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ funext fun i ↦ i.elim
    continuous_toFun := continuous_pi fun i ↦ i.elim
    continuous_invFun := continuous_const }⟩⟩

-- O itself is profinite flat of rank 1.
example : IsProfiniteFlat O O :=
  .self_of_isLocalRing O

-- Finite products Fin n → O are profinite flat and finitely generated.
example (n : ℕ) : IsProfiniteFlat O (Fin n → O) ∧ Module.Finite O (Fin n → O) :=
  ⟨.pi_self (Fin n), inferInstance⟩

end DegenerateAndFinite

section PadicPowerSeries

variable (p : ℕ) [Fact p.Prime]

-- Multivariate formal power series over ℤ_[p] carry the maximal-ideal-adic topology and are
-- profinite flat over ℤ_[p].
open scoped MvPowerSeries.WithPiTopology in
example (d : ℕ) :
    IsAdic (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) ℤ_[p])) ∧
      IsProfiniteFlat ℤ_[p] (MvPowerSeries (Fin d) ℤ_[p]) :=
  ⟨MvPowerSeries.WithPiTopology.isAdic_maximalIdeal (Fin d) ℤ_[p],
    .mvPowerSeries (Fin d) ℤ_[p]⟩

-- Univariate formal power series over ℤ_[p] have an explicit pseudobasis indexed by ℕ sending
-- Pi.single n 1 to X ^ n.
open scoped PowerSeries.WithPiTopology in
example : ∃ e : PowerSeries ℤ_[p] ≃L[ℤ_[p]] (ℕ → ℤ_[p]),
    ∀ n : ℕ, e.symm (Pi.single n 1) = (PowerSeries.X : PowerSeries ℤ_[p]) ^ n :=
  ⟨PowerSeries.WithPiTopology.coeffContinuousLinearEquiv ℤ_[p],
    PowerSeries.WithPiTopology.coeffContinuousLinearEquiv_symm_single_one ℤ_[p]⟩

end PadicPowerSeries

section NonExamples

variable (p : ℕ) [Fact p.Prime]

-- Non-example 1: ℤ_[p] ⧸ maximalIdeal ℤ_[p] is a compact ℤ_[p]-module (compact, Hausdorff, and
-- linearly topologized), but is not flat over ℤ_[p] and hence not profinite flat.
example :
    IsCompactModule ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) ∧
      ¬ Module.Flat ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) ∧
      ¬ IsProfiniteFlat ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := by
  have hopen : IsOpen ((IsLocalRing.maximalIdeal ℤ_[p] : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    simpa [pow_one] using IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p] 1
  have hclosed : IsClosed ((IsLocalRing.maximalIdeal ℤ_[p] : Ideal ℤ_[p]) : Set ℤ_[p]) :=
    (IsLocalRing.maximalIdeal ℤ_[p]).toAddSubgroup.isClosed_of_isOpen hopen
  have hnf : ¬ Module.Flat ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := fun hflat ↦ by
    have : Module.IsTorsionFree ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := inferInstance
    have hp0 : (p : ℤ_[p]) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
    have hreg := IsSMulRegular.of_ne_zero (M := ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) hp0
    let mkQ := (IsLocalRing.maximalIdeal ℤ_[p]).mkQ
    have hp1 : (p : ℤ_[p]) • mkQ 1 =
        (p : ℤ_[p]) • (0 : ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := by
      rw [smul_zero, ← mkQ.map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, _root_.PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    have : Nontrivial (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
    exact one_ne_zero (hreg hp1)
  exact ⟨(IsLocalRing.isCompactModule_self ℤ_[p]).quotient _ hclosed, hnf, fun hpf ↦ hnf hpf.flat⟩

-- Non-example 2: A free rank-1 ℤ_[p]-module (Unit →₀ ℤ_[p] ≃ₗ[ℤ_[p]] ℤ_[p]) with the discrete
-- topology ⊥ is flat, Hausdorff, and linearly topologized, but not compact and not profinite flat.
example :
    let _ : TopologicalSpace (Unit →₀ ℤ_[p]) := ⊥
    Module.Flat ℤ_[p] (Unit →₀ ℤ_[p]) ∧
      IsLinearTopology ℤ_[p] (Unit →₀ ℤ_[p]) ∧
      T2Space (Unit →₀ ℤ_[p]) ∧
      ¬ CompactSpace (Unit →₀ ℤ_[p]) ∧
      ¬ IsProfiniteFlat ℤ_[p] (Unit →₀ ℤ_[p]) := by
  let _ : TopologicalSpace (Unit →₀ ℤ_[p]) := ⊥
  have : DiscreteTopology (Unit →₀ ℤ_[p]) := ⟨rfl⟩
  have : Infinite (Unit →₀ ℤ_[p]) :=
    Infinite.of_injective (fun n : ℕ ↦ Finsupp.single () (n : ℤ_[p])) fun a b hab ↦ by
      simpa using congrArg (fun f : Unit →₀ ℤ_[p] ↦ f ()) hab
  have hnc : ¬ CompactSpace (Unit →₀ ℤ_[p]) := fun hc ↦ by
    have : Finite (Unit →₀ ℤ_[p]) := finite_of_compact_of_discrete
    exact not_finite (Unit →₀ ℤ_[p])
  exact ⟨inferInstance, inferInstance, inferInstance, hnc, fun hpf ↦ hnc hpf.compactSpace⟩

-- Non-example 3: ℚ_[p] is flat, Hausdorff, and linearly topologized over ℤ_[p], but not compact
-- and hence not profinite flat over ℤ_[p].
example :
    Module.Flat ℤ_[p] ℚ_[p] ∧
      IsLinearTopology ℤ_[p] ℚ_[p] ∧
      T2Space ℚ_[p] ∧
      ¬ CompactSpace ℚ_[p] ∧
      ¬ IsProfiniteFlat ℤ_[p] ℚ_[p] := by
  have : ContinuousSMul ℤ_[p] ℚ_[p] :=
    ⟨continuous_subtype_val.fst'.mul continuous_snd⟩
  have hnc : ¬ CompactSpace ℚ_[p] := fun hc ↦ by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff_subset_closedBall (c := (0 : ℚ_[p])).mp
      hc.isCompact_univ.isBounded
    obtain ⟨x, hx⟩ := NormedField.exists_lt_norm ℚ_[p] C
    have hxle : ‖x‖ ≤ C := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hC (Set.mem_univ x)
    exact not_lt_of_ge hxle hx
  exact ⟨inferInstance, inferInstance, inferInstance, hnc, fun hpf ↦ hnc hpf.compactSpace⟩

-- Non-example 4: A free rank-1 ℤ_[p]-module (Unit →₀ ℤ_[p] ≃ₗ[ℤ_[p]] ℤ_[p]) with the indiscrete
-- topology ⊤ is flat, compact, and linearly topologized (⊤ is the unique open submodule), but is
-- not Hausdorff, is not profinite flat, and admits no continuous linear equivalence to I → ℤ_[p].
example :
    let _ : TopologicalSpace (Unit →₀ ℤ_[p]) := ⊤
    Module.Flat ℤ_[p] (Unit →₀ ℤ_[p]) ∧
      CompactSpace (Unit →₀ ℤ_[p]) ∧
      IsLinearTopology ℤ_[p] (Unit →₀ ℤ_[p]) ∧
      ¬ T2Space (Unit →₀ ℤ_[p]) ∧
      ¬ IsProfiniteFlat ℤ_[p] (Unit →₀ ℤ_[p]) ∧
      ∀ I : Type, IsEmpty ((Unit →₀ ℤ_[p]) ≃L[ℤ_[p]] (I → ℤ_[p])) := by
  let _ : TopologicalSpace (Unit →₀ ℤ_[p]) := ⊤
  have : IndiscreteTopology (Unit →₀ ℤ_[p]) := ⟨rfl⟩
  have hlin : IsLinearTopology ℤ_[p] (Unit →₀ ℤ_[p]) :=
    { hasBasis_submodule' := ⟨fun U ↦ by
        rw [IndiscreteTopology.nhds_eq, Filter.mem_top]
        exact ⟨fun hU ↦ ⟨⊤, Filter.univ_mem, fun x _ ↦ hU ▸ Set.mem_univ x⟩,
          fun ⟨_, hN, hNU⟩ ↦ Set.univ_subset_iff.mp ((Filter.mem_top.mp hN) ▸ hNU)⟩⟩ }
  have hnt2 : ¬ T2Space (Unit →₀ ℤ_[p]) := fun ht2 ↦ by
    have hne : (0 : Unit →₀ ℤ_[p]) ≠ Finsupp.single () 1 := fun h ↦
      zero_ne_one' ℤ_[p] (by simpa using congrArg (fun f : Unit →₀ ℤ_[p] ↦ f ()) h)
    exact hne (Inseparable.eq (Inseparable.all 0 (Finsupp.single () 1)))
  refine ⟨inferInstance, inferInstance, hlin, hnt2, fun hpf ↦ hnt2 hpf.t2Space,
    fun I ↦ ⟨fun e ↦ ?_⟩⟩
  exact hnt2 e.symm.toHomeomorph.t2Space

end NonExamples
