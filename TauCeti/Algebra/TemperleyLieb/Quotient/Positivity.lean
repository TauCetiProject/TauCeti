/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.TemperleyLieb.Quotient.PathAlgebra
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.Algebra.TemperleyLieb.TypeA
public import TauCeti.Combinatorics.SimpleGraph.Hasse
public import TauCeti.RingTheory.TraceFunctional.Positive
import Mathlib.Analysis.Matrix.Order
/-! # Positive path traces and Jones quotients

Over `ℂ` with self-adjoint weights `r : V → ℂ`, `walkTrace` on `PathAlgebra ℂ G v₀ n` is a
positive tracial functional (and faithful when every `r v ≠ 0`), identifying `htr.traceRadical n`
with the kernel of `walkStarRep` and descending under an injective unit-step height to
`htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n` (`quotientPathAlgebraEquiv`), yielding multimatrix
decompositions across `δ = 2 cos (π / m)` (`m ≥ 2`) and `δ ≥ 2`, and the existence classification of
positive semidefinite Markov traces across `δ = 0 ∨ δ ∈ jonesLoopParameters`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25 (positivity of Markov traces
  and the discrete and continuous Jones index spectrum).
* F. M. Goodman, P. de la Harpe, V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*, MSRI
  Publications 14, Springer (1989) (multimatrix path-algebra quotients on `A_(m-1)` and `A_∞`). -/
public section
noncomputable section
open scoped ComplexOrder
namespace TauCeti.TemperleyLieb
section WalkPositiveTrace
variable {V : Type*} {r : V → ℂ}
/-- For self-adjoint complex weights `r`, the squared ratio `(r v / r u) ^ 2` is nonnegative. -/
theorem div_sq_nonneg_of_isSelfAdjoint (hrs : ∀ v, IsSelfAdjoint (r v)) (v u : V) :
    0 ≤ (r v / r u) ^ 2 := by
  have hsa : star (r v / r u) = r v / r u := by rw [star_div₀, (hrs v).star_eq, (hrs u).star_eq]
  simpa only [hsa, sq] using star_mul_self_nonneg (r v / r u)
/-- For nonzero self-adjoint complex weights `r`, `(r v / r u) ^ 2` is strictly positive. -/
theorem div_sq_pos_of_isSelfAdjoint (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    (v u : V) : 0 < (r v / r u) ^ 2 :=
  lt_of_le_of_ne (div_sq_nonneg_of_isSelfAdjoint hrs v u)
    (pow_ne_zero 2 (div_ne_zero (hr v) (hr u))).symm
variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {v₀ : V}
/-- For self-adjoint `r : V → ℂ`, `walkTrace` is positive semidefinite on `PathAlgebra ℂ G v₀ n`. -/
theorem walkTrace_star_mul_self_nonneg (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ}
    (X : PathAlgebra ℂ G v₀ n) : 0 ≤ walkTrace G v₀ r (star X * X) := by
  rw [walkTrace_apply]
  exact Finset.sum_nonneg fun v _ ↦ mul_nonneg (div_sq_nonneg_of_isSelfAdjoint hrs v.val v₀) <| by
    rw [Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose]
    exact (Matrix.posSemidef_conjTranspose_mul_self (X v)).trace_nonneg
/-- For nonzero self-adjoint `r : V → ℂ`, `walkTrace` is faithful on `PathAlgebra ℂ G v₀ n`. -/
@[simp] theorem walkTrace_star_mul_self_eq_zero_iff (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} (X : PathAlgebra ℂ G v₀ n) :
    walkTrace G v₀ r (star X * X) = 0 ↔ X = 0 := by
  refine ⟨fun h ↦ funext fun v ↦ ?_, fun h ↦ by simp [h]⟩
  rw [walkTrace_apply] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ mul_nonneg
    (div_sq_nonneg_of_isSelfAdjoint hrs w.val v₀) <| by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.posSemidef_conjTranspose_mul_self (X w)).trace_nonneg).1 h v (Finset.mem_univ v)
  simpa [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose_mul_self_eq_zero_iff,
    (div_sq_pos_of_isSelfAdjoint hr hrs v.val v₀).ne'] using h0
variable (G v₀) in
/-- `walkTrace` bundled as a `StarPositiveFunctional` for self-adjoint weights `r`. -/
def walkPositiveTrace (hrs : ∀ v, IsSelfAdjoint (r v)) (n : ℕ) :
    StarPositiveFunctional (PathAlgebra ℂ G v₀ n) :=
  ⟨walkTrace G v₀ r, walkTrace_star_mul_self_nonneg hrs⟩
@[simp] theorem walkPositiveTrace_apply (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ}
    (X : PathAlgebra ℂ G v₀ n) : walkPositiveTrace G v₀ hrs n X = walkTrace G v₀ r X := (rfl)
/-- For nonzero self-adjoint weights `r`, `walkPositiveTrace` has trivial null submodule. -/
@[simp] theorem nullSubmodule_walkPositiveTrace (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) (n : ℕ) :
    (walkPositiveTrace G v₀ hrs n).nullSubmodule = ⊥ := by
  ext; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    walkTrace_star_mul_self_eq_zero_iff hr hrs]
end WalkPositiveTrace
/-- Algebraic positivity of `walkExpect`: `walkExpect (star Y * Y)` is a finite sum of squares. -/
theorem exists_sum_star_mul_self_walkExpect_star_mul_self {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [G.LocallyFinite] {v₀ : V} {r : V → ℂ} (hrs : ∀ v, IsSelfAdjoint (r v))
    {δ : ℝ} (hδ₀ : 0 < δ) {n : ℕ} (Y : PathAlgebra ℂ G v₀ (n + 1)) :
    ∃ (m : ℕ) (Z : Fin m → PathAlgebra ℂ G v₀ n),
      walkExpect G v₀ r (δ : ℂ) (star Y * Y) = ∑ i : Fin m, star (Z i) * Z i := by
  classical
  let α (u v : V) : ℂ := ((√(δ⁻¹ * ((r v).re / (r u).re) ^ 2) : ℝ) : ℂ)
  have hα (u v : V) : star (α u v) * α u v = (δ : ℂ)⁻¹ * (r v / r u) ^ 2 := by
    rw [IsSelfAdjoint.star_eq (Complex.conj_ofReal _), ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    push_cast; rw [Complex.conj_eq_iff_re.mp (hrs v), Complex.conj_eq_iff_re.mp (hrs u)]
  let ι := Σ (u : G.walkEndpoints v₀ n) (v : G.neighborFinset u.val),
    G.EndpointWalk v₀ (n + 1) v.val
  let Z₀ (idx : ι) : PathAlgebra ℂ G v₀ n := Pi.single idx.1 <| Matrix.of fun p' q ↦
    if p' = Classical.arbitrary (G.EndpointWalk v₀ n idx.1.val) then
      α idx.1.val idx.2.1.val * PathAlgebra.blockAt idx.2.1.val Y idx.2.2
        (q.snoc ((G.mem_neighborFinset idx.1.val idx.2.1.val).1 idx.2.1.property)) else 0
  refine ⟨Fintype.card ι, fun i ↦ Z₀ ((Fintype.equivFin ι).symm i), ?_⟩
  rw [(Fintype.equivFin ι).symm.sum_comp (g := fun idx ↦ star (Z₀ idx) * Z₀ idx)]
  ext u p q; simp only [walkExpect_apply, Finset.sum_apply, Matrix.sum_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma,
    Finset.sum_eq_single u (fun _ _ hu' ↦ Finset.sum_eq_zero fun _ _ ↦ by
      simp [Z₀, Pi.single_eq_of_ne hu'.symm]) (fun h ↦ (h (Finset.mem_univ _)).elim),
    ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum, Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have hv : v.val ∈ G.walkEndpoints v₀ (n + 1) :=
    (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc ((G.mem_neighborFinset u.val v.val).1 v.property)⟩
  rw [PathAlgebra.blockAt_of_mem hv, Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
  simp only [Z₀, Pi.mul_apply, Pi.star_apply, Pi.single_eq_same, Matrix.star_eq_conjTranspose,
    Matrix.mul_apply]
  rw [Finset.sum_eq_single (Classical.arbitrary (G.EndpointWalk v₀ n u.val))
    (fun _ _ hp' ↦ by simp [hp']) (fun h ↦ (h (Finset.mem_univ _)).elim)]
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, ↓reduceIte, PathAlgebra.blockAt_of_mem hv,
    star_mul]; rw [← mul_assoc, ← hα u.val v.val]; ring
namespace IsMarkovTrace
section GraphModel
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
  {δ : ℂ} [Fact (IsSelfAdjoint δ)] (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ δ tr)
/-- Faithfulness of `walkPositiveTrace` identifies `htr.traceRadical n` with `ker walkStarRep`. -/
theorem traceRadical_eq_ker_walkStarRep (n : ℕ) :
    htr.traceRadical n = RingHom.ker (walkStarRep G v₀ hr hδ hrs (n := n)) :=
  (tr n).traceRadical_eq_ker_of_nullSubmodule_eq_bot (htr.map_mul_comm n)
    (walkPositiveTrace G v₀ hrs n) (nullSubmodule_walkPositiveTrace hr hrs n)
    (walkStarRep G v₀ hr hδ hrs) fun a ↦ by
      rw [walkPositiveTrace_apply, ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs]
      exact (htr.eq_walkTrace_comp_walkRep G v₀ hr hδ n a).symm
/-- `walkStarRep` descended to a `⋆`-homomorphism `htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n`. -/
def quotientToPathAlgebra (n : ℕ) : htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  { Ideal.Quotient.liftₐ (htr.traceRadical n) (walkRep G v₀ hr hδ) fun a ha ↦ by
      rwa [htr.traceRadical_eq_ker_walkStarRep G v₀ hr hrs hδ n, RingHom.mem_ker,
        ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs] at ha with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; rw [Ideal.Quotient.star_mk]
      exact walkRep_star hr hδ hrs a }
@[simp] theorem quotientToPathAlgebra_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientToPathAlgebra G v₀ hr hrs hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      walkRep G v₀ hr hδ x := (rfl)
/-- The descended `⋆`-homomorphism `quotientToPathAlgebra` is injective. -/
theorem quotientToPathAlgebra_injective (n : ℕ) :
    Function.Injective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n) := fun x y hxy ↦ by
  rcases Ideal.Quotient.mk_surjective x, Ideal.Quotient.mk_surjective y with ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    htr.traceRadical_eq_ker_walkStarRep G v₀ hr hrs hδ n, RingHom.mem_ker, map_sub, sub_eq_zero,
    ← StarAlgHom.coe_toAlgHom, walkStarRep_toAlgHom hr hδ hrs]
variable {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
/-- **Multimatrix decomposition of a positive trace quotient** via an injective unit-step height. -/
def quotientPathAlgebraEquiv (n : ℕ) : htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  StarAlgEquiv.ofBijective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n)
    ⟨htr.quotientToPathAlgebra_injective G v₀ hr hrs hδ n, fun X ↦
      let ⟨a, ha⟩ := walkRep_surjective hr hδ hf hf₀ hadj n X; ⟨Ideal.Quotient.mk _ a, ha⟩⟩
@[simp] theorem quotientPathAlgebraEquiv_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n
        (Ideal.Quotient.mk (htr.traceRadical n) x) = walkRep G v₀ hr hδ x := (rfl)
/-- `quotientPathAlgebraEquiv` intertwines `walkTrace` with the quotient trace of `tr n`. -/
@[simp] theorem walkTrace_quotientPathAlgebraEquiv {n : ℕ} (x : htr.Quotient n) :
    walkTrace G v₀ r (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) =
      (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.eq_walkTrace_comp_walkRep G v₀ hr hδ n _).symm.trans
    (LinearMap.quotientTrace_mk _ _ _).symm
/-- `quotientPathAlgebraEquiv` intertwines `quotientStrandIncl` with `walkExtend`. -/
theorem quotientPathAlgebraEquiv_quotientStrandIncl {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 2) (htr.quotientStrandIncl n x) =
      walkExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- `htr.quotientStrandIncl_mk` is stated using `(tr _).traceRadical (htr.map_mul_comm _)`,
  -- which is definitionally equal to `htr.traceRadical _`, so `rw` does not match syntactically.
  rw [quotientPathAlgebraEquiv_mk]
  exact (congrArg (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 2))
    (htr.quotientStrandIncl_mk n a)).trans <|
    (htr.quotientPathAlgebraEquiv_mk G v₀ hr hrs hδ hf hf₀ hadj (strandIncl a)).trans
      (walkRep_strandIncl hr hδ a)
/-- `quotientPathAlgebraEquiv` intertwines `quotientStrandStarAlgHom` with `walkExtend`. -/
theorem quotientPathAlgebraEquiv_quotientStrandStarAlgHom (hδu : IsUnit δ) (n : ℕ)
    (x : htr.Quotient n) : htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1)
      (htr.quotientStrandStarAlgHom hδu n x) =
      walkExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x; simp
omit [DecidableRel G.Adj] in
include hr hrs hδ hf hf₀ hadj in
/-- The dimension of `htr.Quotient n` equals the sum of squared `n`-step walk counts in `G`. -/
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
/-- Every vertex weight `discretePathWeight m t` on `A_(m-1)` is nonzero. -/
theorem discretePathWeight_ne_zero {m : ℕ} (t : Fin (m - 1)) : discretePathWeight m t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_two_mul_cos_pi_div_pos (by omega) (by omega))).ne'
/-- Every vertex weight `discretePathWeight m t` is real (self-adjoint). -/
theorem isSelfAdjoint_discretePathWeight (m : ℕ) (t : Fin (m - 1)) :
    IsSelfAdjoint (discretePathWeight m t) := Complex.conj_ofReal _
private theorem sum_neighborFinset_hasse_qInt (δ : ℝ) :
    ∀ v : ℕ, ∑ u ∈ (hasse ℕ).neighborFinset v, qInt ℝ δ (u + 1) = δ * qInt ℝ δ (v + 1)
  | 0 => by simp [qInt_two]
  | k + 1 => by
    rw [neighborFinset_hasse_nat_succ, Finset.sum_pair (by omega), qInt_add_two (R := ℝ) δ (k + 1)]
    ring
/-- `discretePathWeight m ^ 2` is a `2 cos (π / m)`-eigenvector of `pathGraph (m - 1)`. -/
theorem sum_neighborFinset_discretePathWeight_sq {m : ℕ} (v : Fin (m - 1)) :
    ∑ u ∈ (pathGraph (m - 1)).neighborFinset v, discretePathWeight m u ^ 2 =
      ((2 * cos (π / m) : ℝ) : ℂ) * discretePathWeight m v ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by have := v.isLt; omega⟩
  have hsq (t : Fin (k + 1)) : discretePathWeight (k + 2) t ^ 2 =
      (qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t.val + 1) : ℂ) := by
    rw [discretePathWeight, ← Complex.ofReal_pow,
      Real.sq_sqrt (qInt_two_mul_cos_pi_div_pos (Nat.succ_pos _) (by omega)).le]
  simp_rw [hsq]; exact_mod_cast sum_neighborFinset_pathGraph_qInt (k := k) v
/-- For `δ ≥ 2`, every vertex weight `genericPathWeight δ t` on `A_∞` is nonzero. -/
theorem genericPathWeight_ne_zero {δ : ℝ} (hδ : 2 ≤ δ) (t : ℕ) : genericPathWeight δ t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_pos_of_two_le hδ (Nat.succ_pos t))).ne'
/-- Every vertex weight `genericPathWeight δ t` is real (self-adjoint). -/
theorem isSelfAdjoint_genericPathWeight (δ : ℝ) (t : ℕ) :
    IsSelfAdjoint (genericPathWeight δ t) := Complex.conj_ofReal _
/-- For `δ ≥ 2`, `genericPathWeight δ ^ 2` is a `δ`-eigenvector of `hasse ℕ`. -/
theorem sum_neighborFinset_genericPathWeight_sq {δ : ℝ} (hδ : 2 ≤ δ) (v : ℕ) :
    ∑ u ∈ (hasse ℕ).neighborFinset v, genericPathWeight δ u ^ 2 =
      (δ : ℂ) * genericPathWeight δ v ^ 2 := by
  have hsq (t : ℕ) : genericPathWeight δ t ^ 2 = (qInt ℝ δ (t + 1) : ℂ) := by
    rw [genericPathWeight, ← Complex.ofReal_pow,
      Real.sq_sqrt (qInt_pos_of_two_le hδ (Nat.succ_pos t)).le]
  simp_rw [hsq]; exact_mod_cast sum_neighborFinset_hasse_qInt δ v
end Eigenvectors
namespace IsMarkovTrace
section JonesQuotients
open Real SimpleGraph
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- **Discrete Jones quotient decomposition** at `δ = 2 cos (π / m)` (`m ≥ 2`) on `A_(m-1)`. -/
def discreteQuotientEquiv {m : ℕ} (hm : 2 ≤ m) (hδ : δ = 2 * cos (π / m)) (n : ℕ) :
    htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩ n :=
  htr.quotientPathAlgebraEquiv (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
    discretePathWeight_ne_zero (isSelfAdjoint_discretePathWeight m)
    (fun v ↦ by rw [hδ]; exact sum_neighborFinset_discretePathWeight_sq v)
    Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) n
/-- **Generic Jones quotient decomposition** for `δ ≥ 2` on `A_∞` (`hasse ℕ`). -/
def genericQuotientEquiv (hδ : 2 ≤ δ) (n : ℕ) : htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ (hasse ℕ) 0 n :=
  htr.quotientPathAlgebraEquiv (hasse ℕ) 0 (genericPathWeight_ne_zero hδ)
    (isSelfAdjoint_genericPathWeight δ) (sum_neighborFinset_genericPathWeight_sq hδ)
    Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) n
variable (hδ : δ ∈ jonesLoopParameters)
/-- For `δ ∈ jonesLoopParameters`, `tr n` bundled as a `StarPositiveFunctional`. -/
def positiveFunctional (n : ℕ) : StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) :=
  ⟨tr n, (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hδ)).2 hδ n⟩
@[simp] theorem positiveFunctional_apply {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.positiveFunctional hδ n x = tr n x := (rfl)
/-- The faithful positive tracial functional induced on `htr.Quotient n`. -/
def positiveQuotientTrace (n : ℕ) : StarPositiveFunctional (htr.Quotient n) :=
  (htr.positiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)
@[simp] theorem positiveQuotientTrace_mk {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.positiveQuotientTrace hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) = tr n x :=
  (htr.positiveFunctional hδ n).quotientTrace_mk (htr.map_mul_comm n) x
/-- Unnormalized value of `positiveQuotientTrace` on `1` is `δ ^ n`. -/
@[simp] theorem positiveQuotientTrace_one (n : ℕ) :
    htr.positiveQuotientTrace hδ n 1 = (δ : ℂ) ^ n := by
  rw [← _root_.map_one (Ideal.Quotient.mk _), htr.positiveQuotientTrace_mk, htr.map_one]
/-- `positiveQuotientTrace` is tracial on `htr.Quotient n`. -/
theorem positiveQuotientTrace_mul_comm {n : ℕ} (x y : htr.Quotient n) :
    htr.positiveQuotientTrace hδ n (x * y) = htr.positiveQuotientTrace hδ n (y * x) :=
  (htr.positiveFunctional hδ n).quotientTrace_mul_comm (htr.map_mul_comm n) x y
/-- `positiveQuotientTrace` is faithful on `htr.Quotient n`. -/
@[simp] theorem nullSubmodule_positiveQuotientTrace (n : ℕ) :
    (htr.positiveQuotientTrace hδ n).nullSubmodule = ⊥ :=
  (htr.positiveFunctional hδ n).nullSubmodule_quotientTrace (htr.map_mul_comm n)
include hδ in
/-- For `δ ∈ jonesLoopParameters`, `htr.Quotient n` is finite-dimensional over `ℂ`. -/
theorem finiteDimensional_quotient (n : ℕ) : FiniteDimensional ℂ (htr.Quotient n) := by
  rcases mem_jonesLoopParameters.1 hδ with ⟨m, hm, hδm⟩ | h2
  · exact (htr.discreteQuotientEquiv (by omega) hδm n).symm.toAlgEquiv.toLinearEquiv
      |>.finiteDimensional
  · exact (htr.genericQuotientEquiv h2 n).symm.toAlgEquiv.toLinearEquiv.finiteDimensional
end JonesQuotients
end IsMarkovTrace
/-- **Existence classification of positive semidefinite Markov traces over `ℂ`**: one exists iff
`δ = 0` (`A_1`) or `δ ∈ jonesLoopParameters` (`A_(m-1)` / `A_∞`). -/
theorem exists_isMarkovTrace_forall_nonneg_iff_eq_zero_or_mem_jonesLoopParameters {δ : ℝ}
    [Fact (IsSelfAdjoint (δ : ℂ))] :
    (∃ tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ, IsMarkovTrace ℂ (δ : ℂ) tr ∧
      ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ = 0 ∨ δ ∈ jonesLoopParameters := by
  refine ⟨fun ⟨_, htr, hpos⟩ ↦
    htr.forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem.1 hpos, fun hδ ↦ ?_⟩
  suffices ∃ tr : ∀ n, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ, IsMarkovTrace ℂ (δ : ℂ) tr by
    obtain ⟨_, htr⟩ := this
    exact ⟨_, htr, htr.forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem.2 hδ⟩
  have hcase : (∃ m : ℕ, 2 ≤ m ∧ δ = 2 * Real.cos (Real.pi / m)) ∨ 2 ≤ δ :=
    hδ.elim (fun h0 ↦ Or.inl ⟨2, le_rfl, by simp [h0]⟩) fun hJ ↦
      (mem_jonesLoopParameters.1 hJ).imp (fun ⟨m, _, hm⟩ ↦ ⟨m, by omega, hm⟩) id
  rcases hcase with ⟨m, hm, hδm⟩ | h2
  · exact ⟨_, isMarkovTrace_walkTrace (δ := (δ : ℂ)) (SimpleGraph.pathGraph (m - 1))
      ⟨0, Nat.sub_pos_of_lt (by omega)⟩ discretePathWeight_ne_zero
      fun v ↦ hδm ▸ sum_neighborFinset_discretePathWeight_sq v⟩
  · exact ⟨_, isMarkovTrace_walkTrace (δ := (δ : ℂ)) (SimpleGraph.hasse ℕ) 0
      (genericPathWeight_ne_zero h2) (sum_neighborFinset_genericPathWeight_sq h2)⟩
end TauCeti.TemperleyLieb
