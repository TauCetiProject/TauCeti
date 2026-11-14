/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.TemperleyLieb.Quotient.PathAlgebra
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.Combinatorics.SimpleGraph.Hasse
public import TauCeti.RingTheory.TraceFunctional.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Dimension.Constructions
/-! # Positive path traces and Jones quotients

Over `ℂ` with nonzero self-adjoint weights `r : V → ℂ`, `walkTrace` on `PathAlgebra ℂ G v₀ n` is a
faithful positive tracial functional, identifying `htr.traceRadical n` with the kernel of
`walkStarRep` and descending under an injective unit-step height to
`htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n` (`quotientPathAlgebraEquiv`), yielding multimatrix
decompositions across `δ ∈ jonesLoopParameters`. -/
public section
noncomputable section
open scoped ComplexOrder
namespace TauCeti.TemperleyLieb
namespace IsMarkovTrace
section Radical
variable {R : Type*} [CommRing R] {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  (htr : IsMarkovTrace R δ tr)
/-- The multiplication-pairing radical of a Markov trace at level `n`. -/
@[expose] def traceRadical (n : ℕ) : Ideal (TemperleyLieb R δ n) :=
  (tr n).traceRadical (htr.map_mul_comm n)
theorem mem_traceRadical_iff {n : ℕ} {x : TemperleyLieb R δ n} :
    x ∈ htr.traceRadical n ↔ ∀ y, tr n (x * y) = 0 := (tr n).mem_traceRadical (htr.map_mul_comm n)
instance instIsTwoSidedTraceRadical (n : ℕ) : (htr.traceRadical n).IsTwoSided :=
  inferInstanceAs ((tr n).traceRadical (htr.map_mul_comm n)).IsTwoSided
instance instIsStarTraceRadical [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ) :
    (htr.traceRadical n).IsStar where
  star_mem ha := ((tr n).star_mem_traceRadical_iff (htr.map_mul_comm n) (htr.map_star n)).2 ha
/-- The trace-radical quotient of `TemperleyLieb R δ n` for a Markov trace `htr`. -/
abbrev Quotient (n : ℕ) := TemperleyLieb R δ n ⧸ htr.traceRadical n
end Radical
end IsMarkovTrace
section WalkPositiveTrace
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [G.LocallyFinite] (v₀ : V)
omit [DecidableEq V] in
theorem div_sq_pos_of_isSelfAdjoint {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) (v u : V) : 0 < (r v / r u) ^ 2 := by
  have hsa : star (r v / r u) = r v / r u := by rw [star_div₀, (hrs v).star_eq, (hrs u).star_eq]
  refine lt_of_le_of_ne ?_ (pow_ne_zero 2 (div_ne_zero (hr v) (hr u))).symm
  simpa only [hsa, sq] using star_mul_self_nonneg (r v / r u)
variable {G v₀}
theorem walkTrace_star_mul_self_nonneg {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} (X : PathAlgebra ℂ G v₀ n) :
    0 ≤ walkTrace G v₀ r (star X * X) := by
  rw [walkTrace_apply]
  refine Finset.sum_nonneg fun v _ ↦ mul_nonneg (div_sq_pos_of_isSelfAdjoint hr hrs v.1 v₀).le ?_
  rw [Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose]
  exact (Matrix.posSemidef_conjTranspose_mul_self (X v)).trace_nonneg
@[simp] theorem walkTrace_star_mul_self_eq_zero_iff {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} (X : PathAlgebra ℂ G v₀ n) :
    walkTrace G v₀ r (star X * X) = 0 ↔ X = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [walkTrace_apply, Finset.sum_eq_zero_iff_of_nonneg fun v _ ↦ by
    rw [Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose]
    exact mul_nonneg (div_sq_pos_of_isSelfAdjoint hr hrs v.1 v₀).le
      (Matrix.posSemidef_conjTranspose_mul_self (X v)).trace_nonneg] at h
  funext v; have hv := h v (Finset.mem_univ v)
  rwa [mul_eq_zero, or_iff_right (div_sq_pos_of_isSelfAdjoint hr hrs v.1 v₀).ne',
    Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at hv
variable (G v₀) in
/-- `walkTrace` bundled as a `StarPositiveFunctional` on `PathAlgebra ℂ G v₀ n`. -/
def walkPositiveTrace {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    (n : ℕ) : StarPositiveFunctional (PathAlgebra ℂ G v₀ n) :=
  ⟨walkTrace G v₀ r, walkTrace_star_mul_self_nonneg hr hrs⟩
@[simp] theorem walkPositiveTrace_apply {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} (X : PathAlgebra ℂ G v₀ n) :
    walkPositiveTrace G v₀ hr hrs n X = walkTrace G v₀ r X := (rfl)
@[simp] theorem nullSubmodule_walkPositiveTrace {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) (n : ℕ) :
    (walkPositiveTrace G v₀ hr hrs n).nullSubmodule = ⊥ := by
  ext X; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    walkTrace_star_mul_self_eq_zero_iff hr hrs]
end WalkPositiveTrace
namespace IsMarkovTrace
section GraphModel
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
  {δ : ℂ} [Fact (IsSelfAdjoint δ)] (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ δ tr)
theorem traceRadical_eq_ker_walkStarRep (n : ℕ) :
    htr.traceRadical n = RingHom.ker (walkStarRep G v₀ hr hδ hrs (n := n)) :=
  (tr n).traceRadical_eq_ker_of_nullSubmodule_eq_bot (htr.map_mul_comm n)
    (walkPositiveTrace G v₀ hr hrs n) (nullSubmodule_walkPositiveTrace hr hrs n)
    (walkStarRep G v₀ hr hδ hrs) fun a ↦ by
      rw [walkPositiveTrace_apply, ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs]
      exact (htr.eq_walkTrace_comp_walkRep G v₀ hr hδ n a).symm
/-- `walkStarRep` descended to a `⋆`-homomorphism `htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n`. -/
def quotientToPathAlgebra (n : ℕ) : htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  { Ideal.Quotient.liftₐ (htr.traceRadical n) (walkRep G v₀ hr hδ) fun a ha ↦ by
      rwa [htr.traceRadical_eq_ker_walkStarRep G v₀ hr hrs hδ n, RingHom.mem_ker,
        ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs] at ha with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.star_mk]; exact walkRep_star hr hδ hrs a }
@[simp] theorem quotientToPathAlgebra_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientToPathAlgebra G v₀ hr hrs hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      walkRep G v₀ hr hδ x := (rfl)
theorem quotientToPathAlgebra_injective (n : ℕ) :
    Function.Injective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n) := by
  intro x y hxy; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    htr.traceRadical_eq_ker_walkStarRep G v₀ hr hrs hδ n, RingHom.mem_ker, map_sub, sub_eq_zero,
    ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs]
variable {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
/-- **Multimatrix decomposition of a positive trace quotient** under an injective unit-step height
function from `v₀`. -/
def quotientPathAlgebraEquiv (n : ℕ) : htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  StarAlgEquiv.ofBijective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n)
    ⟨htr.quotientToPathAlgebra_injective G v₀ hr hrs hδ n, fun X ↦
      let ⟨a, ha⟩ := walkRep_surjective hr hδ hf hf₀ hadj n X; ⟨Ideal.Quotient.mk _ a, ha⟩⟩
@[simp] theorem quotientPathAlgebraEquiv_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n
        (Ideal.Quotient.mk (htr.traceRadical n) x) = walkRep G v₀ hr hδ x := (rfl)
@[simp] theorem walkTrace_quotientPathAlgebraEquiv {n : ℕ} (x : htr.Quotient n) :
    walkTrace G v₀ r (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) =
      (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.eq_walkTrace_comp_walkRep G v₀ hr hδ n a).symm.trans
    ((tr n).quotientTrace_mk (htr.map_mul_comm n) a).symm
theorem quotientPathAlgebraEquiv_quotientStrandIncl {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 2)
        (htr.quotientStrandIncl n x) =
      walkExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show htr.quotientStrandIncl n (Ideal.Quotient.mk (htr.traceRadical (n + 1)) a) =
      Ideal.Quotient.mk (htr.traceRadical (n + 2)) (strandIncl a) from
    htr.quotientStrandIncl_mk n a]
  exact walkRep_strandIncl hr hδ a
omit [DecidableRel G.Adj] in
include hr hrs hδ hf hf₀ hadj in
theorem finrank_quotient_eq_sum_card_sq (n : ℕ) : Module.finrank ℂ (htr.Quotient n) =
    ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  classical
  exact (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n
    |>.toAlgEquiv.toLinearEquiv.finrank_eq).trans (PathAlgebra.finrank ℂ G v₀ n)
end GraphModel
end IsMarkovTrace
section Eigenvectors
open Real SimpleGraph
/-- Quantum-integer vertex weight `√[t + 1]` on `A_(m-1)` (`pathGraph (m - 1)`). -/
def discretePathWeight (m : ℕ) (t : Fin (m - 1)) : ℂ :=
  ((√(qInt ℝ (2 * cos (π / m)) (t.val + 1)) : ℝ) : ℂ)
/-- Quantum-integer vertex weight `√[t + 1]` on `A_∞` (`hasse ℕ`). -/
def genericPathWeight (δ : ℝ) (t : ℕ) : ℂ := ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)
theorem discretePathWeight_ne_zero {m : ℕ} (hm : 3 ≤ m) (t : Fin (m - 1)) :
    discretePathWeight m t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_two_mul_cos_pi_div_pos (by omega) (by omega))).ne'
theorem isSelfAdjoint_discretePathWeight (m : ℕ) (t : Fin (m - 1)) :
    IsSelfAdjoint (discretePathWeight m t) := Complex.conj_ofReal _
theorem sum_neighborFinset_discretePathWeight_sq {m : ℕ} (hm : 3 ≤ m) (v : Fin (m - 1)) :
    ∑ u ∈ (pathGraph (m - 1)).neighborFinset v, discretePathWeight m u ^ 2 =
      ((2 * cos (π / m) : ℝ) : ℂ) * discretePathWeight m v ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hsq (t : Fin (k + 1)) :
      discretePathWeight (k + 2) t ^ 2 = (qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t.val + 1) : ℂ) := by
    rw [discretePathWeight, ← Complex.ofReal_pow,
      Real.sq_sqrt (qInt_two_mul_cos_pi_div_pos (Nat.succ_pos _) (by omega)).le]
  simp_rw [hsq]; norm_cast; set δ := 2 * cos (π / (k + 2 : ℕ))
  rw [neighborFinset_eq_filter, Finset.sum_filter]; simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt ℝ δ (j + 1) else 0),
    Finset.sum_congr rfl fun j _ ↦ show (if v.val + 1 = j ∨ j + 1 = v.val then qInt ℝ δ (j + 1)
      else 0) = (if v.val + 1 = j then qInt ℝ δ (j + 1) else 0) +
        (if j + 1 = v.val then qInt ℝ δ (j + 1) else 0) by
          split_ifs <;> first | ring1 | (exfalso; omega),
    Finset.sum_add_distrib, Finset.sum_ite_eq,
    show Finset.range (k + 2 - 1) = Finset.range (k + 1) from rfl]
  have h1 : (if v.val + 1 ∈ Finset.range (k + 1) then qInt ℝ δ (v.val + 1 + 1) else 0) =
      qInt ℝ δ (v.val + 2) := by
    split_ifs with hv; · rfl
    rw [show v.val + 2 = k + 2 by simp at hv; omega]
    exact (qInt_two_mul_cos_pi_div_eq_zero (by omega)).symm
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt ℝ δ (j + 1) else 0) =
      qInt ℝ δ v.val := by
    obtain ⟨_ | w, hw⟩ := v; · simp
    simp only [Nat.add_right_cancel_iff]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h1, h2, qInt_add_two]; ring
theorem genericPathWeight_ne_zero {δ : ℝ} (hδ : 2 ≤ δ) (t : ℕ) : genericPathWeight δ t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_pos_of_two_le hδ (Nat.succ_pos t))).ne'
theorem isSelfAdjoint_genericPathWeight (δ : ℝ) (t : ℕ) :
    IsSelfAdjoint (genericPathWeight δ t) := Complex.conj_ofReal _
theorem sum_neighborFinset_genericPathWeight_sq {δ : ℝ} (hδ : 2 ≤ δ) (v : ℕ) :
    ∑ u ∈ (hasse ℕ).neighborFinset v, genericPathWeight δ u ^ 2 =
      (δ : ℂ) * genericPathWeight δ v ^ 2 := by
  have hsq (t : ℕ) : genericPathWeight δ t ^ 2 = (qInt ℝ δ (t + 1) : ℂ) := by
    rw [genericPathWeight, ← Complex.ofReal_pow,
      Real.sq_sqrt (qInt_pos_of_two_le hδ (Nat.succ_pos t)).le]
  simp_rw [hsq]; norm_cast; cases v with
  | zero =>
    have h := qInt_add_two (R := ℝ) (δ := δ) 0; simp only [zero_add, qInt_zero, qInt_one] at h
    simp [neighborFinset_hasse_nat_zero, h]
  | succ k =>
    rw [neighborFinset_hasse_nat_succ, Finset.sum_pair (by omega), qInt_add_two (R := ℝ) δ (k + 1)]
    ring
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  rcases mem_jonesLoopParameters.1 hδ with ⟨m, hm, rfl⟩ | h2
  · have hle : π / m ≤ π / 3 :=
      div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by exact_mod_cast hm)
    have hcos := cos_le_cos_of_nonneg_of_le_pi (div_nonneg pi_pos.le (Nat.cast_nonneg m))
      (by linarith [pi_pos]) hle
    rw [cos_pi_div_three] at hcos; linarith
  · linarith
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 0 < δ :=
  lt_of_lt_of_le zero_lt_one (one_le_of_mem_jonesLoopParameters hδ)
end Eigenvectors
namespace IsMarkovTrace
section JonesQuotients
open Real SimpleGraph
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
include htr in
theorem isPositive_iff_mem_jonesLoopParameters (hδ : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters := by
  refine ⟨fun h ↦ ?_, fun hJ ↦
    (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hJ)).2 hJ⟩
  have h0 : 0 ≤ δ := Complex.zero_le_real.1 (by simpa [htr.map_one] using h 1 1)
  exact (htr.forall_map_star_mul_self_nonneg_iff (lt_of_le_of_ne h0 hδ.symm)).1 h
/-- **Discrete Jones quotient decomposition** at `δ = 2 cos (π / m)` (`m ≥ 3`) on `A_(m-1)`. -/
def discreteQuotientEquiv {m : ℕ} (hm : 3 ≤ m) (hδ : δ = 2 * cos (π / m)) (n : ℕ) :
    htr.Quotient n ≃⋆ₐ[ℂ]
      PathAlgebra ℂ (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩ n :=
  htr.quotientPathAlgebraEquiv (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
    (discretePathWeight_ne_zero hm) (isSelfAdjoint_discretePathWeight m)
    (fun v ↦ by rw [hδ]; exact sum_neighborFinset_discretePathWeight_sq hm v)
    Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) n
/-- **Generic Jones quotient decomposition** for `δ ≥ 2` on `A_∞` (`hasse ℕ`). -/
def genericQuotientEquiv (hδ : 2 ≤ δ) (n : ℕ) :
    htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ (hasse ℕ) 0 n :=
  htr.quotientPathAlgebraEquiv (hasse ℕ) 0
    (genericPathWeight_ne_zero hδ) (isSelfAdjoint_genericPathWeight δ)
    (sum_neighborFinset_genericPathWeight_sq hδ)
    Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) n
/-- For `δ ∈ jonesLoopParameters`, `tr n` bundled as a `StarPositiveFunctional`. -/
def positiveFunctional (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) :=
  ⟨tr n, (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hδ)).2 hδ n⟩
@[simp] theorem positiveFunctional_apply (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : TemperleyLieb ℂ (δ : ℂ) n) : htr.positiveFunctional hδ n x = tr n x := (rfl)
/-- The faithful positive tracial functional induced on `htr.Quotient n`. -/
def positiveQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (htr.Quotient n) :=
  (htr.positiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)
@[simp] theorem positiveQuotientTrace_mk (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.positiveQuotientTrace hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) = tr n x :=
  (htr.positiveFunctional hδ n).quotientTrace_mk (htr.map_mul_comm n) x
@[simp] theorem positiveQuotientTrace_one (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.positiveQuotientTrace hδ n 1 = (δ : ℂ) ^ n := by
  rw [← _root_.map_one (Ideal.Quotient.mk (htr.traceRadical n)), htr.positiveQuotientTrace_mk,
    htr.map_one]
theorem positiveQuotientTrace_mul_comm (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x y : htr.Quotient n) :
    htr.positiveQuotientTrace hδ n (x * y) = htr.positiveQuotientTrace hδ n (y * x) :=
  (htr.positiveFunctional hδ n).quotientTrace_mul_comm (htr.map_mul_comm n) x y
@[simp] theorem nullSubmodule_positiveQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.positiveQuotientTrace hδ n).nullSubmodule = ⊥ :=
  (htr.positiveFunctional hδ n).nullSubmodule_quotientTrace (htr.map_mul_comm n)
theorem finiteDimensional_quotient (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    FiniteDimensional ℂ (htr.Quotient n) := by
  rcases mem_jonesLoopParameters.1 hδ with ⟨m, hm, hδm⟩ | h2
  · exact (htr.discreteQuotientEquiv hm hδm n).symm.toAlgEquiv.toLinearEquiv.finiteDimensional
  · exact (htr.genericQuotientEquiv h2 n).symm.toAlgEquiv.toLinearEquiv.finiteDimensional
end JonesQuotients
end IsMarkovTrace
theorem exists_positive_markovTrace_iff_mem_jonesLoopParameters {δ : ℝ}
    [Fact (IsSelfAdjoint (δ : ℂ))] (hδ₀ : δ ≠ 0) :
    (∃ tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ, IsMarkovTrace ℂ (δ : ℂ) tr ∧
      ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters := by
  refine ⟨fun ⟨_, htr, hpos⟩ ↦ (htr.isPositive_iff_mem_jonesLoopParameters hδ₀).1 hpos,
    fun hδ ↦ ?_⟩
  rcases mem_jonesLoopParameters.1 hδ with ⟨m, hm, hδm⟩ | h2
  · let htr := isMarkovTrace_walkTrace (δ := (δ : ℂ)) (SimpleGraph.pathGraph (m - 1))
      ⟨0, Nat.sub_pos_of_lt (by omega)⟩ (discretePathWeight_ne_zero hm)
      (fun v ↦ by rw [hδm]; exact sum_neighborFinset_discretePathWeight_sq hm v)
    exact ⟨_, htr, (htr.isPositive_iff_mem_jonesLoopParameters hδ₀).2 hδ⟩
  · let htr := isMarkovTrace_walkTrace (δ := (δ : ℂ)) (SimpleGraph.hasse ℕ) 0
      (genericPathWeight_ne_zero h2) (sum_neighborFinset_genericPathWeight_sq h2)
    exact ⟨_, htr, (htr.isPositive_iff_mem_jonesLoopParameters hδ₀).2 hδ⟩
end TauCeti.TemperleyLieb
