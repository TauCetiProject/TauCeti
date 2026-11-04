/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Torus

import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Pair

/-!
# Checks for relative closed polydiscs and tori over Huber pairs

We exercise `Pair.polydisc`, `Pair.polydisc.evalHom`, `Pair.polydisc.closedPolydiscHomeomorph`,
`Pair.torusLocus`, `Pair.polydisc.torusHomEquiv`, and
`Pair.torusLocus_union_preimage_taylorHom_eq_spa` across Tate fields (`ℚ_[p]`), non-Tate integral
bases (`ℤ_[p]`), zero variables (`n = 0`), `(m + n)` iteration via `Pair.iterateSplitHom` and
`Pair.iterateJoinHom`, negative controls separating polydisc evaluations from torus evaluations
(`p` and `0` vs units), and the zero ring `ZMod 1` without a uniform structure.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Examples.PolydiscPair

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Over `ℚ_[p]`, the adic spectrum of `(Pair.powerBounded ℚ_[p]).polydisc n` is homeomorphic to
`closedPolydisc n ℚ_[p]`. -/
noncomputable example (n : ℕ) :
    spa ((Pair.powerBounded ℚ_[p]).polydiscPlus n) ≃ₜ closedPolydisc n ℚ_[p] :=
  Pair.polydisc.closedPolydiscHomeomorph n

/-- Over the non-Tate base `ℤ_[p]`, evaluating `T₀ + T₁` on `(Pair.powerBounded ℤ_[p]).polydisc 2`
at `(p, 1)` yields `p + 1`. -/
example :
    (Pair.polydisc.evalHom (Pair.Hom.id (Pair.powerBounded ℤ_[p]))
        ![⟨(p : ℤ_[p]), natCast_mem _ p⟩, ⟨1, one_mem _⟩]).toRingHom
      (Pair.polydiscVar 2 ℤ_[p] 0 + Pair.polydiscVar 2 ℤ_[p] 1) = (p : ℤ_[p]) + 1 := by
  simp

/-- Evaluating `(Pair.powerBounded ℤ_[p]).polydisc 1` at a unit of `(Pair.powerBounded ℤ_[p]).plus`
sends every point of `Spa(ℤ_[p], ℤ_[p]°)` into `torusLocus`. -/
example (u : ((Pair.powerBounded ℤ_[p]).plus)ˣ)
    (x : spa (Pair.powerBounded ℤ_[p]).plus) :
    (((Pair.polydisc.torusHomEquiv (Pair.Hom.id (Pair.powerBounded ℤ_[p])) 1).symm
        (fun _ ↦ u)).1.spaComap x).1 ∈
      Pair.torusLocus (Pair.powerBounded ℤ_[p]) 1 :=
  (((Pair.polydisc.torusHomEquiv (Pair.Hom.id (Pair.powerBounded ℤ_[p])) 1).symm
    (fun _ ↦ u)).2).2 x

/-- Negative control: evaluating `(Pair.powerBounded ℚ_[p]).polydisc 1` at `p ∈ ℤ_[p] = ℚ_[p]°`
does not land in `torusLocus` at any point of `Spa(ℚ_[p], ℚ_[p]°)`, because `‖p‖ < 1`. -/
example (x : spa (Pair.powerBounded ℚ_[p]).plus) :
    have hp : (p : ℚ_[p]) ∈ (Pair.powerBounded ℚ_[p]).plus := by
      rw [Pair.powerBounded_plus, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
      exact _root_.Padic.norm_p_lt_one.le
    ((Pair.polydisc.evalHom (Pair.Hom.id (Pair.powerBounded ℚ_[p]))
        (fun _ : Fin 1 ↦ ⟨(p : ℚ_[p]), hp⟩)).spaComap x).1 ∉
      Pair.torusLocus (Pair.powerBounded ℚ_[p]) 1 := by
  intro hp hmem
  have h1 := ((Pair.mem_torusLocus_iff_forall_one_vle (Pair.powerBounded ℚ_[p])).mp hmem).2 0
  rw [Pair.Hom.spaComap_val, comap_vle, map_one,
    Pair.polydisc.toRingHom_evalHom_polydiscVar] at h1
  have hx : x.1 ∈ spa (powerBoundedSubring ℚ_[p]) := by
    simpa only [Pair.powerBounded_plus] using x.2
  rw [vle_iff_norm_le_of_mem_spa hx, norm_one] at h1
  exact not_lt_of_ge h1 _root_.Padic.norm_p_lt_one

/-- Over the non-Tate base `ℤ_[p]`, `torusLocus` and its translate by `1` cover the entire
one-variable closed disc. -/
example :
    spa ((Pair.powerBounded ℤ_[p]).polydiscPlus 1) =
      Pair.torusLocus (Pair.powerBounded ℤ_[p]) 1 ∪
        comap (Pair.polydisc.taylorHom (Pair.powerBounded ℤ_[p])
            (fun _ : Fin 1 ↦ (1 : (Pair.powerBounded ℤ_[p]).plus))).toRingHom ⁻¹'
          Pair.torusLocus (Pair.powerBounded ℤ_[p]) 1 :=
  Pair.torusLocus_union_preimage_taylorHom_eq_spa (Pair.powerBounded ℤ_[p])

/-- Over `ℚ_[p]`, the origin section `T ↦ 0` misses `torusLocus` and lands in the translated torus
`comap (T ↦ T + 1) ⁻¹' torusLocus`, showing that `torusLocus` alone does not cover the disc. -/
example (x : spa (Pair.powerBounded ℚ_[p]).plus) :
    let e0 := Pair.polydisc.evalHom (Pair.Hom.id (Pair.powerBounded ℚ_[p]))
      (fun _ : Fin 1 ↦ (0 : (Pair.powerBounded ℚ_[p]).plus))
    (e0.spaComap x).1 ∉ Pair.torusLocus (Pair.powerBounded ℚ_[p]) 1 ∧
      (e0.spaComap x).1 ∈
        comap (Pair.polydisc.taylorHom (Pair.powerBounded ℚ_[p])
            (fun _ : Fin 1 ↦ (1 : (Pair.powerBounded ℚ_[p]).plus))).toRingHom ⁻¹'
          Pair.torusLocus (Pair.powerBounded ℚ_[p]) 1 := by
  intro e0
  have hnot : (e0.spaComap x).1 ∉ Pair.torusLocus (Pair.powerBounded ℚ_[p]) 1 := by
    refine Pair.notMem_torusLocus_of_mem_supp (Pair.powerBounded ℚ_[p]) (i := 0) ?_
    rw [Pair.Hom.spaComap_val, mem_supp_iff, comap_vle]
    simp [e0, Pair.polydisc.toRingHom_evalHom_polydiscVar]
  have hcov := Pair.torusLocus_union_preimage_taylorHom_eq_spa (Pair.powerBounded ℚ_[p])
  exact ⟨hnot, (hcov.subset (e0.spaComap x).2).resolve_left hnot⟩

/-- Degenerate `n = 0` check over `ℤ_[p]`: `zeroInvHom` and `weightedCompletionHom` invert one
another, and `torusLocus` is the full adic spectrum. -/
example :
    (Pair.polydisc.zeroInvHom (Pair.powerBounded ℤ_[p])).comp
        ((Pair.powerBounded ℤ_[p]).weightedCompletionHom isWeightFamily_one_weight) =
      Pair.Hom.id (Pair.powerBounded ℤ_[p]) ∧
    Pair.torusLocus (Pair.powerBounded ℤ_[p]) 0 =
      spa ((Pair.powerBounded ℤ_[p]).polydiscPlus 0) :=
  ⟨Pair.polydisc.zeroInvHom_comp_weightedCompletionHom _, Pair.torusLocus_zero _⟩

/-- Iteration check on `Pair.polydisc`: `Pair.iterateSplitHom` and `Pair.iterateJoinHom` invert one
another between `S.polydisc (m + n)` and `(S.polydisc m).polydisc n`. -/
example (m n : ℕ) :
    ((Pair.powerBounded ℤ_[p]).iterateJoinHom (k := m) (m := n)
        isWeightFamily_one_weight isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ rfl) (fun _ ↦ by simp)).comp
      ((Pair.powerBounded ℤ_[p]).iterateSplitHom (k := m) (m := n)
        isWeightFamily_one_weight isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ rfl) (fun _ ↦ by simp)) =
      Pair.Hom.id ((Pair.powerBounded ℤ_[p]).polydisc (m + n)) :=
  Pair.iterateJoinHom_comp_iterateSplitHom ..

end Padic

section ZeroRing

/-- Discrete topology on the concrete zero ring `ZMod 1` (with no `UniformSpace` instance). -/
local instance zmodOneTopologicalSpace : TopologicalSpace (ZMod 1) := ⊥
local instance : DiscreteTopology (ZMod 1) := ⟨rfl⟩

/-- Degenerate zero-ring check: `Pair.polydisc` and `Pair.torusLocus` instantiate on `ZMod 1`
without nontriviality or uniform-space hypotheses, and its adic spectrum is empty. -/
example (n : ℕ) :
    spa (((Pair.discrete (ZMod 1)).polydisc n).plus) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro _
  let φ := algebraMap (ZMod 1) (restrictedMvPowerSeriesCompletion n (ZMod 1))
  have h10 : (1 : restrictedMvPowerSeriesCompletion n (ZMod 1)) = 0 :=
    (map_one φ).symm.trans ((congrArg φ (Subsingleton.elim 1 0)).trans (map_zero φ))
  exact @TauCeti.ValuativeRel.not_vle_zero_of_isUnit _ _ v.toValuativeRel _ isUnit_one
    (h10 ▸ v.toValuativeRel.vle_refl 1)

end ZeroRing

end TauCeti.Examples.PolydiscPair
