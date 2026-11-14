/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.TemperleyLieb.Quotient.Positivity
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.CompletelyPositive
public import TauCeti.Analysis.StarAlgebra.GNS.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
/-! # The C⋆-tower of positive Jones quotients and its conditional expectations

For `δ ∈ jonesLoopParameters`, `htr.Quotient n` forms a unital C⋆-algebra tower equipped with
faithful tracial states (`normalizedQuotientTrace`), isometric `⋆`-inclusions (`jonesStrandIncl`),
Jones projections (`jonesProjection`), and unique trace-compatible completely positive conditional
expectations (`quotientExpect`, `cstarConditionalExpectation`). -/
public section
noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace TauCeti.TemperleyLieb
section StrandInclAll
section Semiring
variable {R : Type*} [CommSemiring R] {δ : R}
theorem eq_algebraMap_aug_zero (x : TemperleyLieb R δ 0) :
    x = algebraMap R (TemperleyLieb R δ 0) (aug x) := by
  have h := ((algEquivOfLeOne δ (n := 0) (Nat.zero_le 1)).symm_apply_apply x).symm
  rwa [algEquivOfLeOne_apply, algEquivOfLeOne_symm_apply] at h
/-- Strand inclusion `TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ (n + 1)` for all `n ≥ 0`. -/
def strandInclAll : ∀ n : ℕ, TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ (n + 1)
  | 0 => (Algebra.ofId R _).comp aug
  | _ + 1 => strandIncl
@[simp] theorem strandInclAll_zero (x : TemperleyLieb R δ 0) :
    strandInclAll 0 x = algebraMap R (TemperleyLieb R δ 1) (aug x) := (rfl)
@[simp] theorem strandInclAll_succ (n : ℕ) :
    strandInclAll (R := R) (δ := δ) (n + 1) = strandIncl := (rfl)
@[simp] theorem strandInclAll_star [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ)
    (x : TemperleyLieb R δ n) : strandInclAll n (star x) = star (strandInclAll n x) := by
  cases n with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, algebraMap R _ c = x := ⟨aug x, (eq_algebraMap_aug_zero x).symm⟩
    simp [Algebra.algebraMap_eq_smul_one]
  | succ _ => exact strandIncl_star x
/-- `strandInclAll` bundled as a `⋆`-algebra homomorphism at every level `n ≥ 0`. -/
def strandInclStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ) :
    TemperleyLieb R δ n →⋆ₐ[R] TemperleyLieb R δ (n + 1) :=
  { strandInclAll n with map_star' := strandInclAll_star n }
@[simp] theorem IsMarkovTrace.map_strandInclAll {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (n : ℕ) (x : TemperleyLieb R δ n) :
    tr (n + 1) (strandInclAll n x) = δ * tr n x := by
  cases n with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, algebraMap R _ c = x := ⟨aug x, (eq_algebraMap_aug_zero x).symm⟩
    simp [Algebra.algebraMap_eq_smul_one, htr.map_one, mul_comm]
  | succ n => exact htr.map_strandIncl n x
end Semiring
@[simp] theorem walkRep_strandInclAll {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → K}
    (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    (n : ℕ) (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (strandInclAll n x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) := by
  cases n with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, algebraMap K _ c = x := ⟨aug x, (eq_algebraMap_aug_zero x).symm⟩
    simp [Algebra.algebraMap_eq_smul_one]
  | succ _ => exact walkRep_strandIncl hr hδ x
namespace IsMarkovTrace
section CommRing
variable {R : Type*} [CommRing R] {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  (htr : IsMarkovTrace R δ tr)
@[simp] theorem comap_traceRadical_strandInclAll (hδ : IsUnit δ) (n : ℕ) :
    Ideal.comap (strandInclAll (R := R) (δ := δ) n) (htr.traceRadical (n + 1)) =
      htr.traceRadical n := by
  cases n with
  | zero =>
    ext x; simp only [Ideal.mem_comap, mem_traceRadical_iff]; refine ⟨fun hx _ ↦ ?_, fun hx _ ↦ ?_⟩
    · have h1 := hx 1
      simp only [strandInclAll_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        map_smul, htr.map_one, zero_add, pow_one, smul_eq_mul] at h1
      rw [eq_algebraMap_aug_zero x, hδ.mul_left_eq_zero.mp h1, map_zero, zero_mul, map_zero]
    · have h0 := hx 1
      rw [eq_algebraMap_aug_zero x, Algebra.algebraMap_eq_smul_one, mul_one, map_smul,
        htr.map_one, pow_zero, smul_eq_mul, mul_one] at h0; simp [h0]
  | succ n => exact htr.comap_traceRadical_strandIncl n
/-- Unital `⋆`-algebra strand inclusion `htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` (`n ≥ 0`). -/
def quotientStrandStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ) (n : ℕ) :
    htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1) :=
  let φ := Ideal.quotientMapₐ _ (strandInclAll n) (htr.comap_traceRadical_strandInclAll hδ n).ge
  { φ with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; change φ (star _) = star (φ _)
      dsimp only [φ]
      rw [Ideal.Quotient.star_mk, Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ,
        strandInclAll_star, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.star_mk] }
@[simp] theorem quotientStrandStarAlgHom_mk [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientStrandStarAlgHom hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  Ideal.quotient_map_mkₐ _ _ _
theorem quotientStrandStarAlgHom_injective [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ)
    (n : ℕ) : Function.Injective (htr.quotientStrandStarAlgHom hδ n) :=
  Ideal.quotientMap_injective' (H := (htr.comap_traceRadical_strandInclAll hδ n).ge)
    (htr.comap_traceRadical_strandInclAll hδ n).le
@[simp] theorem quotientTrace_quotientStrandStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)]
    (hδ : IsUnit δ) (n : ℕ) (x : htr.Quotient n) :
    (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (htr.quotientStrandStarAlgHom hδ n x) =
      δ * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; rw [htr.quotientStrandStarAlgHom_mk]
  exact ((tr (n + 1)).quotientTrace_mk (htr.map_mul_comm (n + 1)) (strandInclAll n a)).trans <|
    (htr.map_strandInclAll n a).trans <|
      congrArg (δ * ·) ((tr n).quotientTrace_mk (htr.map_mul_comm n) a).symm
end CommRing
theorem quotientPathAlgebraEquiv_quotientStrandStarAlgHom {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ}
    (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : ℂ} [Fact (IsSelfAdjoint δ)]
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (hδu : IsUnit δ)
    {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ δ tr)
    {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) (n : ℕ) (x : htr.Quotient n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1)
        (htr.quotientStrandStarAlgHom hδu n x) =
      walkExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.quotientStrandStarAlgHom_mk, quotientPathAlgebraEquiv_mk, quotientPathAlgebraEquiv_mk,
    walkRep_strandInclAll]
end IsMarkovTrace
end StrandInclAll
section WalkExpect
open SimpleGraph
section Field
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [G.LocallyFinite] (v₀ : V) (r : V → K) (δ : K)
/-- Conditional expectation `PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n` closing the
final step of walks from `u` across `v ∈ G.neighborFinset u` with weight `δ⁻¹ * (r v / r u) ^ 2`. -/
def walkExpect {n : ℕ} : PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n where
  toFun Y u := Matrix.of fun p q ↦
    δ⁻¹ * ∑ v ∈ (G.neighborFinset u.1).attach, (r v.1 / r u.1) ^ 2 *
      PathAlgebra.blockAt v.1 Y (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
        (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
  map_add' _ _ := by ext u p q; simp [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by
    funext u; ext p q
    simp only [RingHom.id_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, map_smul,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
theorem walkExpect_apply {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1)) (u : G.walkEndpoints v₀ n)
    (p q : G.EndpointWalk v₀ n u.1) : walkExpect G v₀ r δ Y u p q =
      δ⁻¹ * ∑ v ∈ (G.neighborFinset u.1).attach, (r v.1 / r u.1) ^ 2 *
        PathAlgebra.blockAt v.1 Y (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) := (rfl)
variable {G v₀ r δ}
@[simp] theorem walkExpect_one (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkExpect G v₀ r δ (1 : PathAlgebra K G v₀ (n + 1)) = 1 := by
  funext u; ext p q; rw [walkExpect_apply, Pi.one_apply, Matrix.one_apply]
  have hsnoc {v : V} (h : G.Adj u.1 v) : (p.snoc h = q.snoc h) ↔ p = q :=
    ⟨fun hpq ↦ EndpointWalk.ext fun i ↦ by
      simpa using congrFun (congrArg DFunLike.coe hpq) i.castSucc, fun hpq ↦ hpq ▸ rfl⟩
  simp_rw [map_one (PathAlgebra.blockAt _), Matrix.one_apply, hsnoc]; split_ifs with hpq
  · rw [Finset.sum_attach (G.neighborFinset u.1) (fun v ↦ (r v / r u.1) ^ 2 * 1)]
    simp_rw [mul_one, div_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul, hδ u.1]; have := hr u.1; field_simp
  · simp
@[simp] theorem walkExpect_walkExtend_mul {n : ℕ} (X : PathAlgebra K G v₀ n)
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkExpect G v₀ r δ (walkExtend G v₀ X * Y) = X * walkExpect G v₀ r δ Y := by
  ext u p q; rw [walkExpect_apply, Pi.mul_apply, Matrix.mul_apply]
  have hterm (v : {v // v ∈ G.neighborFinset u.1}) :
      PathAlgebra.blockAt v.1 (walkExtend G v₀ X * Y)
          (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) =
        ∑ p' : G.EndpointWalk v₀ n u.1, X u p p' * PathAlgebra.blockAt v.1 Y
          (p'.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) := by
    set hadj := (G.mem_neighborFinset u.1 v.1).1 v.2
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
    have humem : u.1 ∈ G.neighborFinset v.1 := (G.mem_neighborFinset v.1 u.1).2 hadj.symm
    rw [map_mul, PathAlgebra.blockAt_of_mem hv, Matrix.mul_apply, G.sum_endpointWalk_succ v₀ n v.1,
      Finset.sum_eq_single_of_mem ⟨u.1, humem⟩ (Finset.mem_attach _ _) fun u' _ hu' ↦
        Finset.sum_eq_zero fun _ _ ↦ by
          rw [walkExtend_apply_snoc, dite_eq_right fun h ↦ hu' (Subtype.ext h.symm), zero_mul]]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [walkExtend_apply_snoc_same]
  simp_rw [hterm, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [walkExpect_apply, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring
@[simp] theorem walkExpect_mul_walkExtend {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1))
    (X : PathAlgebra K G v₀ n) :
    walkExpect G v₀ r δ (Y * walkExtend G v₀ X) = walkExpect G v₀ r δ Y * X := by
  let trp {m : ℕ} (Z : PathAlgebra K G v₀ m) : PathAlgebra K G v₀ m := fun u ↦ (Z u).transpose
  have hE : walkExtend G v₀ (trp X) = trp (walkExtend G v₀ X) := by
    funext v; simp only [trp, walkExtend_apply, Matrix.transpose_submatrix,
      Matrix.blockDiagonal'_transpose]
    refine congrArg (fun M ↦ (Matrix.blockDiagonal' M).submatrix _ _) (funext fun u ↦ ?_)
    by_cases hu : (u : V) ∈ G.walkEndpoints v₀ n <;>
      simp [PathAlgebra.blockAt_of_mem, PathAlgebra.blockAt_of_notMem, hu]
  have hW {Z : PathAlgebra K G v₀ (n + 1)} :
      walkExpect G v₀ r δ (trp Z) = trp (walkExpect G v₀ r δ Z) := by
    ext u p q; simp only [trp, Matrix.transpose_apply, walkExpect_apply]
    refine congrArg (δ⁻¹ * ·) (Finset.sum_congr rfl fun v _ ↦ congrArg (_ * ·) ?_)
    by_cases hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) <;>
      simp [PathAlgebra.blockAt_of_mem, PathAlgebra.blockAt_of_notMem, hv]
  have h := congrArg trp (walkExpect_walkExtend_mul (G := G) (v₀ := v₀) (r := r) (δ := δ)
    (trp X) (trp Y))
  rw [hE, show trp (walkExtend G v₀ X) * trp Y = trp (Y * walkExtend G v₀ X) from
    funext fun _ ↦ (Matrix.transpose_mul _ _).symm, hW, hW] at h
  exact funext fun u ↦ by simpa [trp] using congrFun h u
@[simp] theorem walkExpect_walkExtend (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) : walkExpect G v₀ r δ (walkExtend G v₀ X) = X := by
  rw [← mul_one (walkExtend G v₀ X), walkExpect_walkExtend_mul, walkExpect_one hr hδ₀ hδ, mul_one]
@[simp] theorem walkTrace_walkExpect (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkTrace G v₀ r (walkExpect G v₀ r δ Y) = δ⁻¹ * walkTrace G v₀ r Y := by
  classical
  let step (v u : V) : K := if h : G.Adj u v then
    ∑ p : G.EndpointWalk v₀ n u, PathAlgebra.blockAt v Y (p.snoc h) (p.snoc h) else 0
  have htrY (v : V) : (PathAlgebra.blockAt v Y).trace = ∑ u ∈ G.neighborFinset v, step v u := by
    rw [Matrix.trace, G.sum_endpointWalk_succ v₀ n v,
      ← (G.neighborFinset v).sum_attach fun u ↦ step v u]
    exact Finset.sum_congr rfl fun u _ ↦ by
      simp only [Matrix.diag_apply, step, dite_eq_left ((G.mem_neighborFinset v u.1).1 u.2).symm]
  have htrE {u : V} (hu : u ∈ G.walkEndpoints v₀ n) :
      (PathAlgebra.blockAt u (walkExpect G v₀ r δ Y)).trace =
        δ⁻¹ * ∑ v ∈ G.neighborFinset u, (r v / r u) ^ 2 * step v u := by
    rw [PathAlgebra.blockAt_of_mem hu, Matrix.trace]
    simp only [Matrix.diag_apply, walkExpect_apply]
    rw [← Finset.mul_sum, Finset.sum_comm,
      ← (G.neighborFinset u).sum_attach fun v ↦ (r v / r u) ^ 2 * step v u]
    refine congrArg (δ⁻¹ * ·) (Finset.sum_congr rfl fun v _ ↦ ?_)
    simp only [step, dite_eq_left ((G.mem_neighborFinset u v.1).1 v.2), Finset.mul_sum]
  rw [walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints, Finset.mul_sum,
    Finset.sum_congr rfl fun u hu ↦ by rw [htrE hu, mul_left_comm, Finset.mul_sum, Finset.mul_sum],
    Finset.sum_congr (s₁ := G.walkEndpoints v₀ (n + 1)) rfl fun v _ ↦ by
      rw [htrY v, Finset.mul_sum, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ δ⁻¹ * ((r v / r v₀) ^ 2 * step v u)) fun v u hu ↦ by
      have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
      simp only [step]; split_ifs <;> simp]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
  have := hr u; have := hr v₀; field_simp
end Field
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
  let ι := Σ (u : G.walkEndpoints v₀ n) (v : G.neighborFinset u.1), G.EndpointWalk v₀ (n + 1) v.1
  let Z₀ (idx : ι) : PathAlgebra ℂ G v₀ n := Pi.single idx.1 <| Matrix.of fun p' q ↦
    if p' = Classical.arbitrary (G.EndpointWalk v₀ n idx.1.1) then
      α idx.1.1 idx.2.1.1 * PathAlgebra.blockAt idx.2.1.1 Y idx.2.2
        (q.snoc ((G.mem_neighborFinset idx.1.1 idx.2.1.1).1 idx.2.1.2))
    else 0
  have hsum : walkExpect G v₀ r (δ : ℂ) (star Y * Y) = ∑ idx : ι, star (Z₀ idx) * Z₀ idx := by
    funext u; ext p q; simp only [walkExpect_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma,
      Finset.sum_eq_single u (fun u' _ hu' ↦ Finset.sum_eq_zero fun x _ ↦ by
        simp [Pi.mul_apply, Z₀, Pi.single_eq_of_ne hu'.symm])
        (fun h ↦ (h (Finset.mem_univ _)).elim),
      ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    set hadj := (G.mem_neighborFinset u.1 v.1).1 v.2
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
    rw [PathAlgebra.blockAt_of_mem hv, Pi.mul_apply, Pi.star_apply,
      Matrix.star_eq_conjTranspose, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Pi.mul_apply, Pi.star_apply]
    simp only [Z₀, Pi.single_eq_same, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Classical.arbitrary (G.EndpointWalk v₀ n u.1))
      (fun _ _ hp' ↦ by simp [hp']) (fun h ↦ (h (Finset.mem_univ _)).elim)]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, ↓reduceIte,
      PathAlgebra.blockAt_of_mem hv, star_mul]
    rw [show ∀ a b c d : ℂ, a * b * (c * d) = (b * c) * (a * d) by intros; ring, hα]; ring
  let eqv := Fintype.equivFin ι
  exact ⟨Fintype.card ι, Z₀ ∘ eqv.symm, by rw [hsum, ← eqv.symm.sum_comp]; rfl⟩
end WalkExpect
namespace IsMarkovTrace
section JonesTower
open Real SimpleGraph
theorem isUnit_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) :
    IsUnit (δ : ℂ) := (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne').isUnit
private structure JonesModel (δ : ℝ) : Type 1 where
  V : Type
  [decEq : DecidableEq V]
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  [locFin : G.LocallyFinite]
  v₀ : V
  r : V → ℂ
  hr : ∀ v, r v ≠ 0
  hrs : ∀ v, IsSelfAdjoint (r v)
  hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2
  f : V → ℕ
  hf : Function.Injective f
  hf₀ : f v₀ = 0
  hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x
attribute [instance] JonesModel.decEq JonesModel.decAdj JonesModel.locFin
private def jonesModel {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : JonesModel δ := by
  classical
  exact if hm : ∃ m : ℕ, 3 ≤ m ∧ δ = 2 * cos (π / m) then
    let m := Classical.choose hm; have hm_spec := Classical.choose_spec hm
    { V := Fin (m - 1), G := pathGraph (m - 1), v₀ := ⟨0, Nat.sub_pos_of_lt (by omega)⟩,
      r := discretePathWeight m, hr := discretePathWeight_ne_zero hm_spec.1,
      hrs := isSelfAdjoint_discretePathWeight m,
      hδ := fun v ↦ by rw [hm_spec.2]; exact sum_neighborFinset_discretePathWeight_sq hm_spec.1 v,
      f := Fin.val, hf := Fin.val_injective, hf₀ := rfl, hadj := fun h ↦ pathGraph_adj.1 h }
  else
    have h2 : 2 ≤ δ := (mem_jonesLoopParameters.1 hδ).resolve_left hm
    { V := ℕ, G := hasse ℕ, v₀ := 0, r := genericPathWeight δ,
      hr := genericPathWeight_ne_zero h2, hrs := isSelfAdjoint_genericPathWeight δ,
      hδ := sum_neighborFinset_genericPathWeight_sq h2,
      f := id, hf := Function.injective_id, hf₀ := rfl, hadj := fun h ↦ hasse_nat_adj.1 h }
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
theorem positiveQuotientTrace_eq_quotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : htr.Quotient n) :
    htr.positiveQuotientTrace hδ n x = (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.positiveQuotientTrace_mk hδ a).trans
    ((tr n).quotientTrace_mk (htr.map_mul_comm n) a).symm
private theorem eq_of_forall_positiveQuotientTrace_mul_eq (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    {a b : htr.Quotient n}
    (h : ∀ x, htr.positiveQuotientTrace hδ n (x * a) = htr.positiveQuotientTrace hδ n (x * b)) :
    a = b := by
  rw [← sub_eq_zero]
  have h0 : a - b ∈ (htr.positiveQuotientTrace hδ n).nullSubmodule := by
    rw [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero, mul_sub, map_sub,
      h, sub_self]
  rwa [htr.nullSubmodule_positiveQuotientTrace hδ n, Submodule.mem_bot] at h0
/-- Unital strand `⋆`-inclusion `htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1)` (`n ≥ 0`). -/
def jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1) :=
  htr.quotientStrandStarAlgHom (isUnit_of_mem_jonesLoopParameters hδ) n
@[simp] theorem jonesStrandIncl_mk (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.jonesStrandIncl hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  htr.quotientStrandStarAlgHom_mk _ n x
theorem jonesStrandIncl_injective (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    Function.Injective (htr.jonesStrandIncl hδ n) := htr.quotientStrandStarAlgHom_injective _ n
@[simp] theorem positiveQuotientTrace_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : htr.Quotient n) : htr.positiveQuotientTrace hδ (n + 1) (htr.jonesStrandIncl hδ n x) =
      (δ : ℂ) * htr.positiveQuotientTrace hδ n x := by
  rw [htr.positiveQuotientTrace_eq_quotientTrace, htr.positiveQuotientTrace_eq_quotientTrace]
  exact htr.quotientTrace_quotientStrandStarAlgHom _ n x
private abbrev jonesEquiv (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :=
  let M := jonesModel hδ
  htr.quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj n
/-- **Trace-preserving conditional expectation on positive Jones quotients**. -/
def quotientExpect (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
  let M := jonesModel hδ
  (htr.jonesEquiv hδ n).symm.toAlgEquiv.toLinearMap.comp <|
    (walkExpect M.G M.v₀ M.r (δ : ℂ)).comp (htr.jonesEquiv hδ (n + 1)).toAlgEquiv.toLinearMap
@[simp] theorem quotientExpect_one (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ n 1 = 1 := by
  have hδc : (δ : ℂ) ≠ 0 := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  simp [quotientExpect, walkExpect_one (jonesModel hδ).hr hδc (jonesModel hδ).hδ]
@[simp] theorem quotientExpect_mul_left (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ n (htr.jonesStrandIncl hδ n x * y) = x * htr.quotientExpect hδ n y := by
  simp only [quotientExpect, jonesEquiv, jonesStrandIncl, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
  rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandStarAlgHom (jonesModel hδ).G,
    walkExpect_walkExtend_mul, map_mul, StarAlgEquiv.symm_apply_apply]
@[simp] theorem quotientExpect_mul_right (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) (x : htr.Quotient n) :
    htr.quotientExpect hδ n (y * htr.jonesStrandIncl hδ n x) = htr.quotientExpect hδ n y * x := by
  simp only [quotientExpect, jonesEquiv, jonesStrandIncl, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
  rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandStarAlgHom (jonesModel hδ).G,
    walkExpect_mul_walkExtend, map_mul, StarAlgEquiv.symm_apply_apply]
@[simp] theorem quotientExpect_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) : htr.quotientExpect hδ n (htr.jonesStrandIncl hδ n x) = x := by
  rw [← mul_one (htr.jonesStrandIncl hδ n x), htr.quotientExpect_mul_left, htr.quotientExpect_one,
    mul_one]
@[simp] theorem positiveQuotientTrace_quotientExpect (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) : htr.positiveQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y := by
  let M := jonesModel hδ
  have hw {k} (z : htr.Quotient k) : htr.positiveQuotientTrace hδ k z =
      walkTrace M.G M.v₀ M.r (htr.jonesEquiv hδ k z) :=
    (htr.positiveQuotientTrace_eq_quotientTrace hδ k z).trans
      (htr.walkTrace_quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj z).symm
  rw [hw, hw]
  simp only [quotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.apply_symm_apply]
  exact walkTrace_walkExpect M.hr _
theorem exists_sum_star_mul_self_quotientExpect_star_mul_self (hδ : δ ∈ jonesLoopParameters)
    {n : ℕ} (y : htr.Quotient (n + 1)) : ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
      htr.quotientExpect hδ n (star y * y) = ∑ i : Fin m, star (z i) * z i := by
  obtain ⟨m, Z, hZ⟩ := exists_sum_star_mul_self_walkExpect_star_mul_self (jonesModel hδ).hrs
    (pos_of_mem_jonesLoopParameters hδ) (htr.jonesEquiv hδ (n + 1) y)
  refine ⟨m, fun i ↦ (htr.jonesEquiv hδ n).symm (Z i), ?_⟩
  simp only [quotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv, map_mul, StarHomClass.map_star]
  exact (congrArg (htr.jonesEquiv hδ n).symm hZ).trans <|
    (map_sum (htr.jonesEquiv hδ n).symm _ _).trans <|
      Finset.sum_congr rfl fun _ _ ↦ by rw [map_mul, StarHomClass.map_star]
theorem quotientExpect_unique (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n)
    (hmul : ∀ (x : htr.Quotient n) (y : htr.Quotient (n + 1)),
      F (htr.jonesStrandIncl hδ n x * y) = x * F y)
    (htrace : ∀ y : htr.Quotient (n + 1),
      htr.positiveQuotientTrace hδ n (F y) = (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y) :
    F = htr.quotientExpect hδ n :=
  LinearMap.ext fun _ ↦ htr.eq_of_forall_positiveQuotientTrace_mul_eq hδ fun _ ↦ by
    rw [← hmul, ← htr.quotientExpect_mul_left, htrace, htr.positiveQuotientTrace_quotientExpect]
@[simp] theorem quotientExpect_mk_e_last (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ (n + 1)
        (Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))) =
      (δ : ℂ)⁻¹ • 1 :=
  htr.eq_of_forall_positiveQuotientTrace_mul_eq hδ fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← htr.quotientExpect_mul_left, htr.positiveQuotientTrace_quotientExpect,
      htr.jonesStrandIncl_mk, strandInclAll_succ, ← map_mul, htr.positiveQuotientTrace_mk,
      htr.map_strandIncl_mul_e_last, mul_smul_comm, mul_one, map_smul,
      htr.positiveQuotientTrace_mk, smul_eq_mul]
theorem quotientExpect_mul_mk_e_last_mul (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (a b : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ (n + 1)
        (htr.jonesStrandIncl hδ (n + 1) a *
          Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n)) *
          htr.jonesStrandIncl hδ (n + 1) b) = (δ : ℂ)⁻¹ • (a * b) := by
  rw [htr.quotientExpect_mul_right, htr.quotientExpect_mul_left, htr.quotientExpect_mk_e_last,
    mul_smul_comm, mul_one, smul_mul_assoc]
/-- The **Jones projection** `p_n = δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`. -/
def jonesProjection (n : ℕ) : htr.Quotient (n + 2) :=
  (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))
theorem isSelfAdjoint_jonesProjection (n : ℕ) : IsSelfAdjoint (htr.jonesProjection n) := by
  rw [IsSelfAdjoint, jonesProjection, star_smul, Ideal.Quotient.star_mk, star_e,
    star_inv₀, IsSelfAdjoint.star_eq (Complex.conj_ofReal _)]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
theorem isIdempotentElem_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsIdempotentElem (htr.jonesProjection n) := by
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ
  rw [IsIdempotentElem, jonesProjection, ← Ideal.Quotient.mkₐ_eq_mk ℂ, smul_mul_smul_comm,
    ← map_mul, e_mul_self, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hδc, mul_one]
@[simp] theorem quotientExpect_jonesProjection (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ (n + 1) (htr.jonesProjection n) = ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  rw [jonesProjection, map_smul, htr.quotientExpect_mk_e_last, smul_smul, sq]
@[simp] theorem positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.positiveQuotientTrace hδ (n + 2)
        (htr.jonesStrandIncl hδ (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.jonesStrandIncl_mk, strandInclAll_succ, jonesProjection, mul_smul_comm, ← map_mul,
    map_smul, htr.positiveQuotientTrace_mk, htr.map_strandIncl_mul_e_last,
    htr.positiveQuotientTrace_mk, smul_eq_mul]
/-- The **normalized faithful positive trace** `δ⁻ⁿ • positiveQuotientTrace` on `htr.Quotient n`. -/
def normalizedQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (htr.Quotient n) where
  toLinearMap := ((δ : ℂ)⁻¹ ^ n) • (htr.positiveQuotientTrace hδ n).toLinearMap
  square_nonneg x := by
    have hpos : 0 ≤ (((δ⁻¹ ^ n : ℝ) : ℂ)) :=
      Complex.zero_le_real.2 (pow_nonneg (inv_nonneg.2 (pos_of_mem_jonesLoopParameters hδ).le) n)
    rw [LinearMap.smul_apply, smul_eq_mul,
      show ((δ : ℂ)⁻¹ ^ n) = ((δ⁻¹ ^ n : ℝ) : ℂ) by push_cast; rfl]
    exact mul_nonneg hpos ((htr.positiveQuotientTrace hδ n).square_nonneg x)
theorem normalizedQuotientTrace_apply (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n x = (δ : ℂ)⁻¹ ^ n * htr.positiveQuotientTrace hδ n x := (rfl)
@[simp] theorem normalizedQuotientTrace_one (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.normalizedQuotientTrace hδ n 1 = 1 := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_one, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n (isUnit_of_mem_jonesLoopParameters hδ).ne_zero)]
theorem normalizedQuotientTrace_mul_comm (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x y : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n (x * y) = htr.normalizedQuotientTrace hδ n (y * x) := by
  simp only [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_mul_comm]
@[simp] theorem nullSubmodule_normalizedQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.normalizedQuotientTrace hδ n).nullSubmodule = ⊥ := by
  ext x; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    normalizedQuotientTrace_apply, (isUnit_of_mem_jonesLoopParameters hδ).ne_zero,
    ← StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero
      (htr.positiveQuotientTrace hδ n), htr.nullSubmodule_positiveQuotientTrace hδ n]
@[simp] theorem normalizedQuotientTrace_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) : htr.normalizedQuotientTrace hδ (n + 1) (htr.jonesStrandIncl hδ n x) =
      htr.normalizedQuotientTrace hδ n x := by
  have := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl,
    normalizedQuotientTrace_apply, pow_succ]; field_simp
@[simp] theorem normalizedQuotientTrace_quotientExpect (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) : htr.normalizedQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      htr.normalizedQuotientTrace hδ (n + 1) y := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_quotientExpect,
    normalizedQuotientTrace_apply, pow_succ]; ring
@[simp] theorem normalizedQuotientTrace_jonesStrandIncl_mul_jonesProjection
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ (n + 2)
        (htr.jonesStrandIncl hδ (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ ^ 2 * htr.normalizedQuotientTrace hδ (n + 1) x := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection,
    normalizedQuotientTrace_apply, pow_succ]; ring
end JonesTower
section CStarTower
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- The C⋆-algebra structure on `htr.Quotient n` (`δ ∈ jonesLoopParameters`) induced by the GNS
representation of `positiveQuotientTrace`. -/
@[expose, implicit_reducible]
def cstarAlgebraQuotient (hδ : δ ∈ jonesLoopParameters) (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  letI := htr.finiteDimensional_quotient hδ n
  (htr.positiveQuotientTrace hδ n).cstarAlgebra (htr.nullSubmodule_positiveQuotientTrace hδ n)
instance instFiniteDimensionalQuotient [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    FiniteDimensional ℂ (htr.Quotient n) := htr.finiteDimensional_quotient hδ.out n
noncomputable instance instCStarAlgebraQuotient [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    CStarAlgebra (htr.Quotient n) := htr.cstarAlgebraQuotient hδ.out n
noncomputable instance instPartialOrderQuotient [Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    PartialOrder (htr.Quotient n) := CStarAlgebra.spectralOrder (htr.Quotient n)
instance instStarOrderedRingQuotient [Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    StarOrderedRing (htr.Quotient n) := CStarAlgebra.spectralOrderedRing (htr.Quotient n)
theorem isometry_jonesStrandIncl [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    Isometry (htr.jonesStrandIncl hδ.out n) :=
  NonUnitalStarAlgHom.isometry _ (htr.jonesStrandIncl_injective hδ.out n)
theorem norm_jonesStrandIncl [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) (x : htr.Quotient n) :
    ‖htr.jonesStrandIncl hδ.out n x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map _ (htr.jonesStrandIncl_injective hδ.out n) x
theorem quotientExpect_nonneg [hδ : Fact (δ ∈ jonesLoopParameters)] {n : ℕ}
    {y : htr.Quotient (n + 1)} (hy : 0 ≤ y) : 0 ≤ htr.quotientExpect hδ.out n y := by
  let _ : NonUnitalContinuousFunctionalCalculus ℝ (htr.Quotient (n + 1)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let _ : NonnegSpectrumClass ℝ (htr.Quotient (n + 1)) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨r, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy
  obtain ⟨m, z, hz⟩ := htr.exists_sum_star_mul_self_quotientExpect_star_mul_self hδ.out r
  rw [hz]; exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg (z i)
/-- **C⋆-conditional expectation on the positive Jones quotient tower.** -/
def cstarConditionalExpectation [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    CStarConditionalExpectation (htr.jonesStrandIncl hδ.out n) where
  toPositiveLinearMap := .mk₀ (htr.quotientExpect hδ.out n) fun _ hy ↦ htr.quotientExpect_nonneg hy
  map_one' := htr.quotientExpect_one hδ.out n
  map_mul_left' := htr.quotientExpect_mul_left hδ.out
  map_mul_right' := htr.quotientExpect_mul_right hδ.out
@[simp] theorem cstarConditionalExpectation_apply [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ)
    (y : htr.Quotient (n + 1)) :
    cstarConditionalExpectation htr n y = htr.quotientExpect hδ.out n y := (rfl)
end CStarTower
end IsMarkovTrace
end TauCeti.TemperleyLieb
