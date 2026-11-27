/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.TemperleyLieb.Quotient.PathAlgebra
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.TypeA
import Mathlib.Analysis.Matrix.Order
/-! # Positive path traces and Jones quotients

Over `ℂ` with self-adjoint weights `r : V → ℂ`, `pathAlgebraTrace` on `PathAlgebra ℂ G v₀ n` is a
positive tracial functional (and faithful when every `r v ≠ 0`), identifying `htr.traceRadical n`
with the kernel of `pathAlgebraStarRep` and descending under an injective unit-step height to
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
variable {V : Type*} {r : V → ℂ} {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {v₀ : V}
/-- For self-adjoint `r : V → ℂ`, `pathAlgebraTrace` is positive semidefinite on
`PathAlgebra ℂ G v₀ n`. -/
theorem pathAlgebraTrace_star_mul_self_nonneg (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ}
    (X : PathAlgebra ℂ G v₀ n) : 0 ≤ pathAlgebraTrace G v₀ r (star X * X) := by
  rw [pathAlgebraTrace_apply]
  exact Finset.sum_nonneg fun v _ ↦ mul_nonneg ((hrs v.val).div (hrs v₀)).sq_nonneg <| by
    rw [Pi.mul_apply, Pi.star_apply, Matrix.star_eq_conjTranspose]
    exact (Matrix.posSemidef_conjTranspose_mul_self (X v)).trace_nonneg
/-- For nonzero self-adjoint `r : V → ℂ`, `pathAlgebraTrace` is faithful on
`PathAlgebra ℂ G v₀ n`. -/
@[simp] theorem pathAlgebraTrace_star_mul_self_eq_zero_iff (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} (X : PathAlgebra ℂ G v₀ n) :
    pathAlgebraTrace G v₀ r (star X * X) = 0 ↔ X = 0 := by
  refine ⟨fun h ↦ funext fun v ↦ ?_, fun h ↦ by simp [h]⟩
  rw [pathAlgebraTrace_apply] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ mul_nonneg
    ((hrs w.val).div (hrs v₀)).sq_nonneg <| by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.posSemidef_conjTranspose_mul_self (X w)).trace_nonneg).1 h v (Finset.mem_univ v)
  simpa [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose_mul_self_eq_zero_iff,
    pow_ne_zero 2 (div_ne_zero (hr v.val) (hr v₀))] using h0
variable (G v₀) in
/-- `pathAlgebraTrace` bundled as a `StarPositiveFunctional` for self-adjoint weights `r`. -/
def pathAlgebraPositiveTrace (hrs : ∀ v, IsSelfAdjoint (r v)) (n : ℕ) :
    StarPositiveFunctional (PathAlgebra ℂ G v₀ n) :=
  ⟨pathAlgebraTrace G v₀ r, pathAlgebraTrace_star_mul_self_nonneg hrs⟩
@[simp] theorem pathAlgebraPositiveTrace_apply (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ}
    (X : PathAlgebra ℂ G v₀ n) :
    pathAlgebraPositiveTrace G v₀ hrs n X = pathAlgebraTrace G v₀ r X := (rfl)
/-- For nonzero self-adjoint weights `r`, `pathAlgebraPositiveTrace` has trivial null submodule. -/
@[simp] theorem nullSubmodule_pathAlgebraPositiveTrace (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) (n : ℕ) :
    (pathAlgebraPositiveTrace G v₀ hrs n).nullSubmodule = ⊥ := by
  ext; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    pathAlgebraTrace_star_mul_self_eq_zero_iff hr hrs]
end WalkPositiveTrace
/-- Algebraic positivity of `pathAlgebraExpect`: `pathAlgebraExpect (star Y * Y)` is a finite sum
of squares. -/
theorem exists_sum_star_mul_self_pathAlgebraExpect_star_mul_self {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [G.LocallyFinite] {v₀ : V} {r : V → ℂ} (hrs : ∀ v, IsSelfAdjoint (r v))
    {δ : ℝ} (hδ₀ : 0 < δ) {n : ℕ} (Y : PathAlgebra ℂ G v₀ (n + 1)) :
    ∃ (m : ℕ) (Z : Fin m → PathAlgebra ℂ G v₀ n),
      pathAlgebraExpect G v₀ r (δ : ℂ) (star Y * Y) = ∑ i : Fin m, star (Z i) * Z i := by
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
  ext u p q; simp only [pathAlgebraExpect_apply, Finset.sum_apply, Matrix.sum_apply]
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
/-- Faithfulness of `pathAlgebraPositiveTrace` identifies `htr.traceRadical n` with
`ker pathAlgebraStarRep`. -/
theorem traceRadical_eq_ker_pathAlgebraStarRep (n : ℕ) :
    htr.traceRadical n = RingHom.ker (pathAlgebraStarRep G v₀ hr hδ hrs (n := n)) :=
  (tr n).traceRadical_eq_ker_of_nullSubmodule_eq_bot (htr.map_mul_comm n)
    (pathAlgebraPositiveTrace G v₀ hrs n) (nullSubmodule_pathAlgebraPositiveTrace hr hrs n)
    (pathAlgebraStarRep G v₀ hr hδ hrs) fun a ↦ by
      rw [pathAlgebraPositiveTrace_apply, ← StarAlgHom.coe_toAlgHom,
        pathAlgebraStarRep_toAlgHom hr hδ hrs]
      exact (htr.apply_eq_pathAlgebraTrace_pathAlgebraRep G v₀ hr hδ n a).symm
/-- `pathAlgebraStarRep` descended to a `⋆`-homomorphism
`htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n`. -/
def quotientToPathAlgebra (n : ℕ) : htr.Quotient n →⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  { Ideal.Quotient.liftₐ (htr.traceRadical n) (pathAlgebraRep G v₀ hr hδ) fun a ha ↦ by
      rwa [htr.traceRadical_eq_ker_pathAlgebraStarRep G v₀ hr hrs hδ n, RingHom.mem_ker,
        ← StarAlgHom.coe_toAlgHom, pathAlgebraStarRep_toAlgHom hr hδ hrs] at ha with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; rw [Ideal.Quotient.star_mk]
      exact pathAlgebraRep_star hr hδ hrs a }
@[simp] theorem quotientToPathAlgebra_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientToPathAlgebra G v₀ hr hrs hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      pathAlgebraRep G v₀ hr hδ x := (rfl)
/-- The descended `⋆`-homomorphism `quotientToPathAlgebra` is injective. -/
theorem quotientToPathAlgebra_injective (n : ℕ) :
    Function.Injective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n) := fun x y hxy ↦ by
  rcases Ideal.Quotient.mk_surjective x, Ideal.Quotient.mk_surjective y with ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    htr.traceRadical_eq_ker_pathAlgebraStarRep G v₀ hr hrs hδ n, RingHom.mem_ker, map_sub,
    sub_eq_zero, ← StarAlgHom.coe_toAlgHom, pathAlgebraStarRep_toAlgHom hr hδ hrs]
variable {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
/-- **Multimatrix decomposition of a positive trace quotient** via an injective unit-step height. -/
def quotientPathAlgebraEquiv (n : ℕ) : htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ G v₀ n :=
  StarAlgEquiv.ofBijective (htr.quotientToPathAlgebra G v₀ hr hrs hδ n)
    ⟨htr.quotientToPathAlgebra_injective G v₀ hr hrs hδ n, fun X ↦
      let ⟨a, ha⟩ := pathAlgebraRep_surjective hr hδ hf hf₀ hadj n X; ⟨Ideal.Quotient.mk _ a, ha⟩⟩
@[simp] theorem quotientPathAlgebraEquiv_mk {n : ℕ} (x : TemperleyLieb ℂ δ n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n
        (Ideal.Quotient.mk (htr.traceRadical n) x) = pathAlgebraRep G v₀ hr hδ x := (rfl)
/-- `quotientPathAlgebraEquiv` intertwines `pathAlgebraTrace` with the quotient trace of `tr n`. -/
@[simp] theorem pathAlgebraTrace_quotientPathAlgebraEquiv {n : ℕ} (x : htr.Quotient n) :
    pathAlgebraTrace G v₀ r (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) =
      (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.apply_eq_pathAlgebraTrace_pathAlgebraRep G v₀ hr hδ n _).symm.trans
    (LinearMap.quotientTrace_mk _ _ _).symm
/-- `quotientPathAlgebraEquiv` intertwines `quotientStrandIncl` with `pathAlgebraExtend`. -/
theorem quotientPathAlgebraEquiv_quotientStrandIncl (n : ℕ) (x : htr.Quotient n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1)
      (htr.quotientStrandIncl n x) =
      pathAlgebraExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x; simp
omit [DecidableRel G.Adj] in
include hr hrs hδ hf hf₀ hadj in
/-- The dimension of `htr.Quotient n` equals the sum of squared `n`-step walk counts in `G`. -/
theorem finrank_quotient_eq_sum_card_sq (n : ℕ) : Module.finrank ℂ (htr.Quotient n) =
    ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  classical
  exact (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n
    |>.toAlgEquiv.toLinearEquiv.finrank_eq).trans (finrank_pathAlgebra ℂ G v₀ n)
end GraphModel
section
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
  {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2)
  {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- `quotientStarPositiveFunctional` computes as `pathAlgebraTrace ∘ quotientPathAlgebraEquiv`. -/
theorem quotientStarPositiveFunctional_eq_pathAlgebraTrace_quotientPathAlgebraEquiv
    (hδloop : δ ∈ jonesLoopParameters) {n : ℕ} (x : htr.Quotient n) :
    htr.quotientStarPositiveFunctional hδloop n x =
      pathAlgebraTrace G v₀ r (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) :=
  (htr.quotientStarPositiveFunctional_apply hδloop n x).trans
    (htr.pathAlgebraTrace_quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj x).symm
end
end IsMarkovTrace
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
/-- Unfolding equation for `discreteQuotientEquiv` as a `quotientPathAlgebraEquiv`. -/
theorem discreteQuotientEquiv_eq {m : ℕ} (hm : 2 ≤ m) (hδ : δ = 2 * cos (π / m)) (n : ℕ) :
    htr.discreteQuotientEquiv hm hδ n =
      htr.quotientPathAlgebraEquiv (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
        discretePathWeight_ne_zero (isSelfAdjoint_discretePathWeight m)
        (fun v ↦ by rw [hδ]; exact sum_neighborFinset_discretePathWeight_sq v)
        Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) n := (rfl)
/-- Evaluating `discreteQuotientEquiv` on a quotient class computes `pathAlgebraRep` on
`A_(m-1)`. -/
@[simp] theorem discreteQuotientEquiv_mk {m : ℕ} (hm : 2 ≤ m) (hδ : δ = 2 * cos (π / m))
    {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.discreteQuotientEquiv hm hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      pathAlgebraRep (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
        discretePathWeight_ne_zero
        (fun v ↦ by rw [hδ]; exact sum_neighborFinset_discretePathWeight_sq v) x := (rfl)
/-- **Generic Jones quotient decomposition** for `δ ≥ 2` on `A_∞` (`hasse ℕ`). -/
def genericQuotientEquiv (hδ : 2 ≤ δ) (n : ℕ) :
    htr.Quotient n ≃⋆ₐ[ℂ] PathAlgebra ℂ (hasse ℕ) 0 n :=
  htr.quotientPathAlgebraEquiv (hasse ℕ) 0 (genericPathWeight_ne_zero hδ)
    (isSelfAdjoint_genericPathWeight δ) (sum_neighborFinset_genericPathWeight_sq hδ)
    Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) n
/-- Unfolding equation for `genericQuotientEquiv` as a `quotientPathAlgebraEquiv`. -/
theorem genericQuotientEquiv_eq (hδ : 2 ≤ δ) (n : ℕ) :
    htr.genericQuotientEquiv hδ n =
      htr.quotientPathAlgebraEquiv (hasse ℕ) 0 (genericPathWeight_ne_zero hδ)
        (isSelfAdjoint_genericPathWeight δ) (sum_neighborFinset_genericPathWeight_sq hδ)
        Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) n := (rfl)
/-- Evaluating `genericQuotientEquiv` on a quotient class computes `pathAlgebraRep` on `A_∞`. -/
@[simp] theorem genericQuotientEquiv_mk (hδ : 2 ≤ δ) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.genericQuotientEquiv hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      pathAlgebraRep (hasse ℕ) 0 (genericPathWeight_ne_zero hδ)
        (sum_neighborFinset_genericPathWeight_sq hδ) x := (rfl)
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
  · exact ⟨_, isMarkovTrace_pathAlgebraTrace (δ := (δ : ℂ)) (SimpleGraph.pathGraph (m - 1))
      ⟨0, Nat.sub_pos_of_lt (by omega)⟩ discretePathWeight_ne_zero
      fun v ↦ hδm ▸ sum_neighborFinset_discretePathWeight_sq v⟩
  · exact ⟨_, isMarkovTrace_pathAlgebraTrace (δ := (δ : ℂ)) (SimpleGraph.hasse ℕ) 0
      (genericPathWeight_ne_zero h2) (sum_neighborFinset_genericPathWeight_sq h2)⟩
end TauCeti.TemperleyLieb
