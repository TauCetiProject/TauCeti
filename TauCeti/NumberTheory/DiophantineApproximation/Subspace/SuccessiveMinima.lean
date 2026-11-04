/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ModuleCovolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ReducedBasis
import Mathlib.Analysis.Convex.Measure
import TauCeti.Analysis.Convex.Gauge
import TauCeti.Analysis.Convex.Topology
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Basic
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Successive minima of an `𝓞 K`-module and Minkowski's second theorem over a number field

Let `K` be a number field of degree `d = [K : ℚ]`, let `ι` be a finite type of cardinality `n`,
let `Λ` be a finitely generated `𝓞 K`-submodule of `ι → K` spanning `ι → K` over `K`, and let `B`
be a convex body in the Minkowski space `ι → mixedSpace K`. For `l < n`, the **`l`-th successive
minimum over `K`** (`TauCeti.NumberField.successiveMinimum Λ B l`, indexed from `0`) is the infimum
of the positive dilation factors `t > 0` for which `Λ` contains `l + 1` vectors linearly independent
over `K` whose coordinatewise mixed embeddings lie in `t • B`.

Comparing `successiveMinimum Λ B` with the real successive minima `ZLattice.successiveMin` of the
full `ℤ`-lattice `Λ.mixedImage ⊆ ι → mixedSpace K` of rank `d * n` rests on two linear-algebraic
bridges:

* **Extracting `K`-independent vectors from real minima.** Among the first `d * (l + 1)` real
  minimal vectors of `Λ.mixedImage`, `TauCeti.exists_linearIndependent_comp_finrank_mul` selects
  `l + 1` vectors linearly independent over `K`, with the `j`-th selected by position `d * j`,
  yielding `successiveMinimum Λ B l ≤ ZLattice.successiveMin Λ.mixedImage B ⟨d * l, _⟩`.
* **Multiplying `K`-independent vectors by a reduced integral basis.** Biorthogonal `K`-linear
  forms act on `ι → mixedSpace K` through `sum_mixedEmbedding_mul_mixedEmbedding`, showing that if
  `v 0, …, v l` are linearly independent over `K`, then their products with a family whose mixed
  embeddings are linearly independent over `ℝ` remain linearly independent over `ℝ`
  (`TauCeti.NumberField.linearIndependent_real_mixedEmbedding_mul`). Taking `{1}` gives
  `ZLattice.successiveMin Λ.mixedImage B ⟨l, _⟩ ≤ successiveMinimum Λ B l` without any balancedness
  assumption (so the zeroth minimum over `K` equals the zeroth real minimum); taking
  `reducedIntegralBasis K` when `B` is balanced at every infinite place gives
  `ZLattice.successiveMin Λ.mixedImage B ⟨d * (l + 1) - 1, _⟩ ≤
  integralBasisHouse K * successiveMinimum Λ B l`.

Combining these comparisons across blocks of size `d` with Minkowski's second theorem over `ℝ`
(`ZLattice.prod_successiveMin_mul_measure_le_two_pow_mul_covolume` and
`ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measure`) yields both sides
of **Minkowski's second theorem over `K`**:

```text
2 ^ (d n) / ((d n)! · c_K ^ (d n)) · covolume Λ.mixedImage μ
  ≤ (∏ l, μ_l ^ d) · μ B
  ≤ 2 ^ (d n) · covolume Λ.mixedImage μ,
```

where `c_K = integralBasisHouse K ≤ max 1 (d / 2) * √|discr K|` and `c_ℚ = 1`.

## Main definitions

* `TauCeti.NumberField.successiveMinimum Λ B l`: the `l`-th successive minimum (0-indexed) over `K`
  of `Λ : Submodule (𝓞 K) (ι → K)` with respect to `B : Set (ι → mixedSpace K)`.

## Main results

* `TauCeti.NumberField.linearIndependent_real_mixedEmbedding_mul` and
  `TauCeti.NumberField.linearIndependent_real_mixedEmbedding`: `K`-linear independence of vectors
  in `ι → K` lifts to `ℝ`-linear independence in `ι → mixedSpace K`.
* `TauCeti.NumberField.successiveMinimum_le_successiveMin_mixedImage`,
  `TauCeti.NumberField.successiveMin_mixedImage_le`, and
  `TauCeti.NumberField.successiveMin_mixedImage_le_mul`: comparisons between `successiveMinimum`
  and `ZLattice.successiveMin` of `Λ.mixedImage`.
* `TauCeti.NumberField.isLeast_successiveMinimum` and
  `TauCeti.NumberField.exists_basis_mem_smul_successiveMinimum`: attainment of each minimum and
  simultaneous attainment by a `K`-basis of `ι → K` in `Λ`.
* `TauCeti.NumberField.prod_successiveMinimum_pow_mul_measure_le` and
  `TauCeti.NumberField.covolume_le_prod_successiveMinimum_pow_mul_measure` (together with their
  `measureReal` counterparts): Minkowski's second theorem over `K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Appendix C.2, Definition C.2.9, Remark C.2.10, and Theorem C.2.11.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics **785**, Springer (1980),
  Chapter IV.
-/

public section

noncomputable section

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Submodule
open scoped Pointwise Topology

namespace TauCeti.NumberField

section Basic

variable {K : Type*} [Field K] {ι : Type*}

/-- **The `l`-th successive minimum over `K`** (0-indexed; Bombieri–Gubler Definition C.2.9) of an
`𝓞 K`-submodule `Λ` of `ι → K` with respect to a set `B` in `ι → mixedSpace K`: the infimum of the
positive dilation factors `t > 0` for which `Λ` contains `l + 1` vectors linearly independent over
`K` whose coordinatewise mixed embeddings lie in `t • B`.

When no positive dilate of `B` contains `l + 1` `K`-linearly independent vectors of `Λ` (in
particular whenever `Fintype.card ι ≤ l`), the set of admissible dilation factors is empty and
`successiveMinimum Λ B l` takes the value `sInf ∅ = 0`. -/
def successiveMinimum (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K)) (l : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (l + 1) → ι → K,
    LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (v j i)) ∈ t • B}

theorem successiveMinimum_def (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K))
    (l : ℕ) :
    successiveMinimum Λ B l = sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (l + 1) → ι → K,
      LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (v j i)) ∈ t • B} :=
  (rfl)

/-- Every successive minimum over `K` is nonnegative. -/
theorem successiveMinimum_nonneg (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K))
    (l : ℕ) : 0 ≤ successiveMinimum Λ B l :=
  Real.sInf_nonneg fun _ ht ↦ ht.1.le

/-- Any positive dilate `t • B` containing the mixed embeddings of `l + 1` `K`-linearly independent
vectors of `Λ` bounds `successiveMinimum Λ B l` above by `t`. -/
theorem successiveMinimum_le {Λ : Submodule (𝓞 K) (ι → K)} {B : Set (ι → mixedSpace K)} {l : ℕ}
    {t : ℝ} (ht : 0 < t) {v : Fin (l + 1) → ι → K} (hv : LinearIndependent K v)
    (hvΛ : ∀ j, v j ∈ Λ) (hvB : ∀ j, (fun i ↦ mixedEmbedding K (v j i)) ∈ t • B) :
    successiveMinimum Λ B l ≤ t :=
  csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ⟨ht, v, hv, fun j ↦ ⟨hvΛ j, hvB j⟩⟩

/-- Dilating `B` by `c > 0` divides every successive minimum over `K` by `c`. -/
theorem successiveMinimum_smul (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K))
    {c : ℝ} (hc : 0 < c) (l : ℕ) :
    successiveMinimum Λ (c • B) l = successiveMinimum Λ B l / c := by
  rw [successiveMinimum_def, successiveMinimum_def, div_eq_inv_mul, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le)]
  congr 1
  ext t
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne'), inv_inv, smul_eq_mul,
    Set.mem_ofPred_eq, smul_smul, mul_comm t c, mul_pos_iff_of_pos_left hc]

/-- From `Fintype.card ι` onwards, `ι → K` has no `l + 1` `K`-linearly independent vectors, so
`successiveMinimum Λ B l` vanishes. -/
@[simp]
theorem successiveMinimum_of_card_le [Fintype ι] (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) {l : ℕ} (hl : Fintype.card ι ≤ l) :
    successiveMinimum Λ B l = 0 := by
  suffices {t : ℝ | 0 < t ∧ ∃ v : Fin (l + 1) → ι → K,
      LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (v j i)) ∈ t • B} = ∅ by
    rw [successiveMinimum_def, this, Real.sInf_empty]
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
  intro _ v hv _
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi] at hcard
  omega

end Basic

section LinearIndependence

variable {K : Type*} [Field K] {ι : Type*}

/-- The real dimension of `ι → mixedSpace K` is `[K : ℚ] * card ι`. -/
@[simp]
theorem finrank_pi_mixedSpace [NumberField K] [Fintype ι] :
    finrank ℝ (ι → mixedSpace K) = finrank ℚ K * Fintype.card ι := by
  classical
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm,
    mixedEmbedding.finrank]

/-- **Lifting `K`-linear independence to `ℝ`-linear independence of scalar multiples.** If
`v : κ → ι → K` is linearly independent over `K` and `ω : α → K` has `ℝ`-linearly independent
images in `mixedSpace K`, then the coordinatewise mixed embeddings of `ω a • v j` are linearly
independent over `ℝ` in `ι → mixedSpace K`. -/
theorem linearIndependent_real_mixedEmbedding_mul [Finite ι] {α κ : Type*}
    {ω : α → K} (hω : LinearIndependent ℝ fun a ↦ mixedEmbedding K (ω a))
    {v : κ → ι → K} (hv : LinearIndependent K v) :
    LinearIndependent ℝ fun (p : α × κ) i ↦ mixedEmbedding K (ω p.1 * v p.2 i) := by
  classical
  cases nonempty_fintype ι
  obtain ⟨φ, hφ⟩ := hv.exists_dual_forall_apply_eq_ite
  rw [linearIndependent_iff']
  rintro s c hc ⟨a₀, j₀⟩ hp₀
  let A : Finset α := s.image Prod.fst
  let J : Finset κ := insert j₀ (s.image Prod.snd)
  have hsAJ : s ⊆ A ×ˢ J := fun p hp ↦ Finset.mem_product.2
    ⟨Finset.mem_image_of_mem _ hp, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)⟩
  let c' : α × κ → ℝ := fun p ↦ if p ∈ s then c p else 0
  have hsum : (∑ p ∈ A ×ˢ J, c' p • fun i ↦ mixedEmbedding K (ω p.1 * v p.2 i)) = 0 := by
    rw [← Finset.sum_subset hsAJ fun p _ hp ↦ by simp [c', hp]]
    exact (Finset.sum_congr rfl fun p hp ↦ by simp [c', hp]).trans hc
  have hproj : ∑ a ∈ A, c' (a, j₀) • mixedEmbedding K (ω a) = 0 := by
    calc ∑ a ∈ A, c' (a, j₀) • mixedEmbedding K (ω a)
        = ∑ a ∈ A, ∑ j ∈ J, c' (a, j) •
            (mixedEmbedding K (ω a) * mixedEmbedding K (φ j₀ (v j))) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          have hj₀J : j₀ ∈ J := Finset.mem_insert_self _ _
          simp [hφ, apply_ite (mixedEmbedding K), hj₀J]
      _ = ∑ a ∈ A, ∑ j ∈ J, ∑ i : ι, c' (a, j) •
            (mixedEmbedding K (φ j₀ (Pi.basisFun K ι i)) *
              mixedEmbedding K (ω a * v j i)) := by
          refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← sum_mixedEmbedding_mul_mixedEmbedding (φ j₀) (v j), Finset.mul_sum,
            Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_mul]
          congr 1
          ring
      _ = ∑ i : ι, mixedEmbedding K (φ j₀ (Pi.basisFun K ι i)) *
            ∑ p ∈ A ×ˢ J, c' p • mixedEmbedding K (ω p.1 * v p.2 i) := by
          refine (Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm).trans ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ (mul_smul_comm _ _ _).symm
      _ = 0 := by
          have hsum_i (i : ι) :
              ∑ p ∈ A ×ˢ J, c' p • mixedEmbedding K (ω p.1 * v p.2 i) = 0 := by
            simpa [Finset.sum_apply] using congr_fun hsum i
          simp_rw [hsum_i, mul_zero, Finset.sum_const_zero]
  have ha₀ : a₀ ∈ A := Finset.mem_image.2 ⟨(a₀, j₀), hp₀, rfl⟩
  simpa [c', hp₀] using linearIndependent_iff'.1 hω A (fun a ↦ c' (a, j₀)) hproj a₀ ha₀

/-- Vectors in `ι → K` that are linearly independent over `K` have `ℝ`-linearly independent
coordinatewise mixed embeddings in `ι → mixedSpace K`. -/
theorem linearIndependent_real_mixedEmbedding [NumberField K] [Finite ι] {κ : Type*}
    {v : κ → ι → K} (hv : LinearIndependent K v) :
    LinearIndependent ℝ fun j i ↦ mixedEmbedding K (v j i) := by
  have h1 : LinearIndependent ℝ fun _ : Unit ↦ mixedEmbedding K (1 : K) :=
    .of_subsingleton () (by simp)
  have h := (linearIndependent_real_mixedEmbedding_mul h1 hv).comp
    (Equiv.punitProd κ).symm (Equiv.punitProd κ).symm.injective
  simpa [Function.comp_def] using h

end LinearIndependence

section ComparisonAndAttainment

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
variable {Λ : Submodule (𝓞 K) (ι → K)}

theorem lt_finrank_pi_mixedSpace {l : ℕ} (hl : l < Fintype.card ι) :
    l < finrank ℝ (ι → mixedSpace K) := by
  rw [finrank_pi_mixedSpace]
  exact hl.trans_le (Nat.le_mul_of_pos_left _ Module.finrank_pos)

theorem mul_lt_finrank_pi_mixedSpace {l : ℕ} (hl : l < Fintype.card ι) :
    finrank ℚ K * l < finrank ℝ (ι → mixedSpace K) := by
  rw [finrank_pi_mixedSpace]
  exact Nat.mul_lt_mul_of_pos_left hl Module.finrank_pos

theorem mul_succ_sub_one_lt_finrank_pi_mixedSpace {l : ℕ} (hl : l < Fintype.card ι) :
    finrank ℚ K * (l + 1) - 1 < finrank ℝ (ι → mixedSpace K) := by
  rw [finrank_pi_mixedSpace]
  have hpos : 0 < finrank ℚ K * (l + 1) := Nat.mul_pos Module.finrank_pos (Nat.succ_pos l)
  have hle : finrank ℚ K * (l + 1) ≤ finrank ℚ K * Fintype.card ι :=
    Nat.mul_le_mul_left _ hl
  omega

open Classical in
/-- Extraction of `l + 1` `K`-linearly independent vectors of `Λ` inside the `d * l`-th real
minimum dilate of `B`. -/
private theorem exists_linearIndependent_mem_smul_successiveMin_mixedImage
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) :
    ∃ v : Fin (l + 1) → ι → K, LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧
      (fun i ↦ mixedEmbedding K (v j i)) ∈
        ZLattice.successiveMin Λ.mixedImage B ⟨finrank ℚ K * l,
          mul_lt_finrank_pi_mixedSpace hl⟩ • (B : Set (ι → mixedSpace K)) := by
  obtain ⟨a, ha, haL⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin Λ.mixedImage hB0
  have hle : finrank ℚ K * (l + 1) ≤ finrank ℝ (ι → mixedSpace K) := by
    rw [finrank_pi_mixedSpace]
    exact Nat.mul_le_mul_left _ hl
  choose u huΛ hua using fun m : Fin (finrank ℚ K * (l + 1)) ↦
    Submodule.mem_mixedImage.1 (haL (Fin.castLE hle m)).1
  let f : (ι → K) →ₗ[ℚ] (ι → mixedSpace K) :=
    LinearMap.piMap fun _ ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap
  have hfu : f ∘ u = a ∘ Fin.castLE hle := funext fun m ↦ hua m
  have hlin : LinearIndependent ℝ (f ∘ u) := hfu ▸ ha.comp _ (Fin.castLE_injective hle)
  obtain ⟨s, hs, hs_le⟩ :=
    TauCeti.exists_linearIndependent_comp_finrank_mul (K := K) (f := f) (u := u) hlin
  set idx : Fin (finrank ℝ (ι → mixedSpace K)) :=
    ⟨finrank ℚ K * l, mul_lt_finrank_pi_mixedSpace hl⟩
  have ht : 0 < ZLattice.successiveMin Λ.mixedImage B idx :=
    ZLattice.successiveMin_pos Λ.mixedImage hB0 idx
  refine ⟨u ∘ s, hs, fun j ↦ ⟨huΛ (s j), ?_⟩⟩
  rw [← ConvexBody.gauge_le_iff_mem_smul hB0 ht, Function.comp_apply, hua (s j),
    (haL (Fin.castLE hle (s j))).2]
  refine ZLattice.monotone_successiveMin Λ.mixedImage hB0 (Fin.mk_le_mk.2 ?_)
  exact (hs_le j).trans (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 j.isLt))

open Classical in
/-- **Upper bound by the `(d * l)`-th real successive minimum**: for `l < card ι`, the `l`-th
successive minimum of `Λ` over `K` is at most the `([K : ℚ] * l)`-th real successive minimum of
`Λ.mixedImage`. -/
theorem successiveMinimum_le_successiveMin_mixedImage
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) :
    successiveMinimum Λ B l ≤
      ZLattice.successiveMin Λ.mixedImage B ⟨finrank ℚ K * l,
        mul_lt_finrank_pi_mixedSpace hl⟩ := by
  obtain ⟨v, hv, hvΛB⟩ := exists_linearIndependent_mem_smul_successiveMin_mixedImage (Λ := Λ) hB0 hl
  exact successiveMinimum_le (ZLattice.successiveMin_pos Λ.mixedImage hB0 _) hv
    (fun j ↦ (hvΛB j).1) (fun j ↦ (hvΛB j).2)

open Classical in
/-- **Lower bound by the `l`-th real successive minimum** (without balancedness): for `l < card ι`,
the `l`-th real successive minimum of `Λ.mixedImage` is at most `successiveMinimum Λ B l`. -/
theorem successiveMin_mixedImage_le
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) :
    ZLattice.successiveMin Λ.mixedImage B ⟨l, lt_finrank_pi_mixedSpace hl⟩ ≤
      successiveMinimum Λ B l := by
  obtain ⟨v₀, hv₀, hv₀ΛB⟩ :=
    exists_linearIndependent_mem_smul_successiveMin_mixedImage (Λ := Λ) hB0 hl
  refine le_csInf ⟨_, ZLattice.successiveMin_pos Λ.mixedImage hB0 _, v₀, hv₀, hv₀ΛB⟩ ?_
  rintro t ⟨ht, v, hv, hvΛB⟩
  exact ZLattice.successiveMin_le ht.le (linearIndependent_real_mixedEmbedding hv)
    (fun j ↦ Submodule.mem_mixedImage.2 ⟨v j, (hvΛB j).1, rfl⟩) (fun j ↦ (hvΛB j).2)

open Classical in
/-- **Positivity of the successive minima over `K`** below `card ι`. -/
theorem successiveMinimum_pos
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) :
    0 < successiveMinimum Λ B l :=
  (ZLattice.successiveMin_pos Λ.mixedImage hB0 ⟨l, lt_finrank_pi_mixedSpace hl⟩).trans_le
    (successiveMin_mixedImage_le hB0 hl)

open Classical in
/-- **Bombieri–Gubler Remark C.2.10**: when `ι` is nonempty, the zeroth successive minimum over `K`
equals the zeroth real successive minimum of `Λ.mixedImage`, without symmetry or balancedness. -/
theorem successiveMinimum_zero [Nonempty ι]
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K))) :
    successiveMinimum Λ B 0 =
      ZLattice.successiveMin Λ.mixedImage B ⟨0, lt_finrank_pi_mixedSpace Fintype.card_pos⟩ := by
  refine le_antisymm ?_ (successiveMin_mixedImage_le hB0 Fintype.card_pos)
  simpa using successiveMinimum_le_successiveMin_mixedImage (Λ := Λ) hB0 Fintype.card_pos

open Classical in
/-- **Attainment of each successive minimum over `K`**: for `l < card ι`, the infimum defining
`successiveMinimum Λ B l` is attained. -/
theorem isLeast_successiveMinimum
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) :
    IsLeast {t : ℝ | 0 < t ∧ ∃ v : Fin (l + 1) → ι → K,
      LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧
        (fun i ↦ mixedEmbedding K (v j i)) ∈ t • (B : Set (ι → mixedSpace K))}
      (successiveMinimum Λ B l) := by
  set S := {t : ℝ | 0 < t ∧ ∃ v : Fin (l + 1) → ι → K,
    LinearIndependent K v ∧ ∀ j, v j ∈ Λ ∧
      (fun i ↦ mixedEmbedding K (v j i)) ∈ t • (B : Set (ι → mixedSpace K))}
  obtain ⟨v₀, hv₀, hv₀ΛB⟩ :=
    exists_linearIndependent_mem_smul_successiveMin_mixedImage (Λ := Λ) hB0 hl
  set r := ZLattice.successiveMin Λ.mixedImage B ⟨finrank ℚ K * l, mul_lt_finrank_pi_mixedSpace hl⟩
  have hr : 0 < r := ZLattice.successiveMin_pos Λ.mixedImage hB0 _
  let emb : (ι → K) → (ι → mixedSpace K) := fun x i ↦ mixedEmbedding K (x i)
  have hemb : Function.Injective emb := Function.Injective.piMap fun _ ↦ mixedEmbedding_injective K
  set F : Set (ι → K) := {x | x ∈ Λ ∧ gauge (B : Set (ι → mixedSpace K)) (emb x) ≤ r}
  have hF : F.Finite :=
    ((ZLattice.finite_setOf_gauge_le Λ.mixedImage hB0 r).subset
      (by rintro _ ⟨x, ⟨hxΛ, hxg⟩, rfl⟩; exact ⟨Submodule.mem_mixedImage.2 ⟨x, hxΛ, rfl⟩, hxg⟩)
      ).of_finite_image hemb.injOn
  set T : Set (Fin (l + 1) → ι → K) := {v | LinearIndependent K v ∧ ∀ j, v j ∈ F}
  have hT : T.Finite := (Set.Finite.pi fun _ ↦ hF).subset fun v hv j _ ↦ hv.2 j
  have hv₀T : v₀ ∈ T := ⟨hv₀, fun j ↦ ⟨(hv₀ΛB j).1,
    (ConvexBody.gauge_le_iff_mem_smul hB0 hr).2 (hv₀ΛB j).2⟩⟩
  let g : (Fin (l + 1) → ι → K) → ℝ := fun v ↦
    Finset.univ.sup' Finset.univ_nonempty fun j ↦ gauge (B : Set (ι → mixedSpace K)) (emb (v j))
  obtain ⟨w, hwT, hwmin⟩ := T.exists_min_image g hT ⟨v₀, hv₀T⟩
  have hgw_pos : 0 < g w := by
    have hw0 : emb (w 0) ≠ 0 := fun h ↦ hwT.1.ne_zero 0
      (funext fun i ↦ mixedEmbedding_injective K (by simpa [emb] using congr_fun h i))
    exact ((ConvexBody.gauge_pos_iff hB0).2 hw0).trans_le
      (Finset.le_sup' (fun j ↦ gauge (B : Set (ι → mixedSpace K)) (emb (w j))) (Finset.mem_univ 0))
  have hgwS : g w ∈ S := ⟨hgw_pos, w, hwT.1, fun j ↦ ⟨(hwT.2 j).1,
    (ConvexBody.gauge_le_iff_mem_smul hB0 hgw_pos).1
      (Finset.le_sup' (fun k ↦ gauge (B : Set (ι → mixedSpace K)) (emb (w k)))
        (Finset.mem_univ j))⟩⟩
  have hgw_le_r : g w ≤ r := (hwmin v₀ hv₀T).trans
    (Finset.sup'_le _ _ fun j _ ↦ (hv₀T.2 j).2)
  have hgw_eq : g w = successiveMinimum Λ B l := by
    refine le_antisymm ?_ (csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ hgwS)
    by_contra! hlt
    obtain ⟨t, ⟨ht, u, hu, huΛB⟩, htw⟩ := exists_lt_of_csInf_lt ⟨g w, hgwS⟩ hlt
    have hug (j : Fin (l + 1)) : gauge (B : Set (ι → mixedSpace K)) (emb (u j)) ≤ t :=
      (ConvexBody.gauge_le_iff_mem_smul hB0 ht).2 (huΛB j).2
    have huT : u ∈ T := ⟨hu, fun j ↦ ⟨(huΛB j).1, (hug j).trans (htw.le.trans hgw_le_r)⟩⟩
    exact (Finset.sup'_le _ _ fun j _ ↦ hug j).not_gt (htw.trans_le (hwmin u huT))
  exact ⟨hgw_eq ▸ hgwS, fun _ ht ↦ csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ht⟩

open Classical in
/-- **Threshold characterization of `successiveMinimum`**: for `l < card ι` and `0 < t`,
`successiveMinimum Λ B l ≤ t` holds if and only if `t • B` contains the mixed embeddings of
`l + 1` `K`-linearly independent vectors of `Λ`. -/
theorem successiveMinimum_le_iff
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    {l : ℕ} (hl : l < Fintype.card ι) {t : ℝ} (ht : 0 < t) :
    successiveMinimum Λ B l ≤ t ↔
      ∃ v : Fin (l + 1) → ι → K, LinearIndependent K v ∧
        ∀ j, v j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (v j i)) ∈ t • (B : Set (ι → mixedSpace K)) := by
  refine ⟨fun hle ↦ ?_, fun ⟨v, hv, hvΛB⟩ ↦
    successiveMinimum_le ht hv (fun j ↦ (hvΛB j).1) (fun j ↦ (hvΛB j).2)⟩
  obtain ⟨⟨hμ, v, hv, hvΛB⟩, -⟩ := isLeast_successiveMinimum (Λ := Λ) hB0 hl
  refine ⟨v, hv, fun j ↦ ⟨(hvΛB j).1, ?_⟩⟩
  rw [← ConvexBody.gauge_le_iff_mem_smul hB0 ht]
  exact ((ConvexBody.gauge_le_iff_mem_smul hB0 hμ).2 (hvΛB j).2).trans hle

open Classical in
/-- The successive minima over `K` are nondecreasing on `{l | l < Fintype.card ι}`. -/
theorem monotoneOn_successiveMinimum
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K))) :
    MonotoneOn (successiveMinimum Λ B) {l | l < Fintype.card ι} := by
  intro l₁ hl₁ l₂ hl₂ hl₁₂
  obtain ⟨⟨ht, v, hv, hvΛB⟩, -⟩ := isLeast_successiveMinimum (Λ := Λ) hB0 hl₂
  have hcast : l₁ + 1 ≤ l₂ + 1 := Nat.succ_le_succ hl₁₂
  exact successiveMinimum_le ht (hv.comp _ (Fin.castLE_injective hcast))
    (fun j ↦ (hvΛB (Fin.castLE hcast j)).1) (fun j ↦ (hvΛB (Fin.castLE hcast j)).2)

open Classical in
/-- Enlarging the body or the `𝓞 K`-submodule decreases the successive minima over `K`. -/
theorem successiveMinimum_mono_antitone
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {Λ' : Submodule (𝓞 K) (ι → K)} (hΛ : Λ ≤ Λ')
    {B : ConvexBody (ι → mixedSpace K)} {B' : Set (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    (hBB' : (B : Set (ι → mixedSpace K)) ⊆ B') {l : ℕ} (hl : l < Fintype.card ι) :
    successiveMinimum Λ' B' l ≤ successiveMinimum Λ B l := by
  obtain ⟨⟨ht, v, hv, hvΛB⟩, -⟩ := isLeast_successiveMinimum (Λ := Λ) hB0 hl
  exact successiveMinimum_le ht hv (fun j ↦ hΛ (hvΛB j).1)
    (fun j ↦ Set.smul_set_mono hBB' (hvΛB j).2)

/-- Simultaneous attainment for a compact convex neighbourhood `B` of `0`, proved by induction on
prefix length `m ≤ card ι`. -/
private theorem exists_linearIndependent_mem_smul_successiveMinimum_aux
    {B : Set (ι → mixedSpace K)}
    (hatt : ∀ l < Fintype.card ι, ∃ v : Fin (l + 1) → ι → K, LinearIndependent K v ∧
      ∀ j, v j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (v j i)) ∈ successiveMinimum Λ B l • B)
    (m : ℕ) (hm : m ≤ Fintype.card ι) :
    ∃ a : Fin m → ι → K, LinearIndependent K a ∧
      ∀ j : Fin m, a j ∈ Λ ∧ (fun i ↦ mixedEmbedding K (a j i)) ∈ successiveMinimum Λ B j • B := by
  classical
  induction m with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0⟩
  | succ m ih =>
    obtain ⟨a, ha, haΛB⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨u, hu, huΛB⟩ := hatt m hm
    obtain ⟨k, hk⟩ : ∃ k, u k ∉ Submodule.span K (Set.range a) := by
      by_contra! h
      have hle := Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 h))
      have hcard := finrank_range_le_card (R := K) a
      rw [finrank_span_eq_card hu, Fintype.card_fin] at hle
      rw [Set.finrank, Fintype.card_fin] at hcard
      omega
    refine ⟨Fin.snoc a (u k), ha.finSnoc hk, fun j ↦ ?_⟩
    induction j using Fin.lastCases with
    | last => simpa using huΛB k
    | cast j => simpa using haΛB j

open Classical in
/-- **Simultaneous attainment of all successive minima over `K` by a `K`-basis** (Bombieri–Gubler
Theorem C.2.11, first assertion): for a compact convex neighbourhood `B` of `0`, there exists a
`K`-basis `b` of `ι → K` indexed by `Fin (Fintype.card ι)` consisting of vectors of `Λ` such that
the mixed embedding of `b l` lies in `successiveMinimum Λ B l • B` for every `l`. Neither symmetry
nor balancedness of `B` is needed. -/
theorem exists_basis_mem_smul_successiveMinimum
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B) (hB0 : B ∈ 𝓝 0) :
    ∃ b : Basis (Fin (Fintype.card ι)) K (ι → K),
      (∀ l, b l ∈ Λ) ∧
      ∀ l : Fin (Fintype.card ι),
        (fun i ↦ mixedEmbedding K (b l i)) ∈ successiveMinimum Λ B l • B := by
  let Bbody : ConvexBody (ι → mixedSpace K) :=
    ⟨B, hBc, hBk, ⟨0, mem_of_mem_nhds hB0⟩⟩
  have hBint : (0 : ι → mixedSpace K) ∈ interior (Bbody : Set (ι → mixedSpace K)) :=
    mem_interior_iff_mem_nhds.2 hB0
  obtain ⟨a, ha, haΛB⟩ := exists_linearIndependent_mem_smul_successiveMinimum_aux (Λ := Λ) (B := B)
    (fun l hl ↦ (isLeast_successiveMinimum (Λ := Λ) (B := Bbody) hBint hl).1.2)
    (Fintype.card ι) le_rfl
  let b : Basis (Fin (Fintype.card ι)) K (ι → K) :=
    basisOfLinearIndependentOfCardEqFinrank' a ha (by simp)
  have hb : ⇑b = a := coe_basisOfLinearIndependentOfCardEqFinrank' a ha _
  exact ⟨b, fun l ↦ hb ▸ (haΛB l).1, fun l ↦ hb ▸ (haΛB l).2⟩

open Classical in
/-- **Simultaneous attainment of all successive minima over `K` by a `K`-linearly independent
family**: for a compact convex neighbourhood `B` of `0`, there exist `card ι` `K`-linearly
independent vectors of `Λ` whose `l`-th member has mixed embedding in
`successiveMinimum Λ B l • B`. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B) (hB0 : B ∈ 𝓝 0) :
    ∃ v : Fin (Fintype.card ι) → ι → K, LinearIndependent K v ∧
      ∀ l : Fin (Fintype.card ι), v l ∈ Λ ∧
        (fun i ↦ mixedEmbedding K (v l i)) ∈ successiveMinimum Λ B l • B := by
  obtain ⟨b, hbΛ, hbB⟩ := exists_basis_mem_smul_successiveMinimum (Λ := Λ) hBc hBk hB0
  exact ⟨b, b.linearIndependent, fun l ↦ ⟨hbΛ l, hbB l⟩⟩

open Classical in
/-- **Upper bound on the `(d * (l + 1) - 1)`-th real successive minimum** for a body balanced at
every infinite place: multiplying `l + 1` `K`-independent vectors attaining
`successiveMinimum Λ B l` by `reducedIntegralBasis K` produces `[K : ℚ] * (l + 1)` `ℝ`-independent
vectors in `Λ.mixedImage` inside `(integralBasisHouse K * successiveMinimum Λ B l) • B`. -/
theorem successiveMin_mixedImage_le_mul
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B)
    {l : ℕ} (hl : l < Fintype.card ι) :
    ZLattice.successiveMin Λ.mixedImage B ⟨finrank ℚ K * (l + 1) - 1,
      mul_succ_sub_one_lt_finrank_pi_mixedSpace hl⟩ ≤
      integralBasisHouse K * successiveMinimum Λ B l := by
  obtain ⟨⟨ht, v, hv, hvΛB⟩, -⟩ := isLeast_successiveMinimum (Λ := Λ) hB0 hl
  set cK := integralBasisHouse K
  have hcK : 0 < cK := integralBasisHouse_pos
  have hsub : finrank ℚ K * (l + 1) - 1 + 1 = finrank ℚ K * (l + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos Module.finrank_pos (Nat.succ_pos l))
  let e : Fin (finrank ℚ K * (l + 1) - 1 + 1) ≃ Fin (finrank ℚ K) × Fin (l + 1) :=
    (finCongr hsub).trans finProdFinEquiv.symm
  let w : Fin (finrank ℚ K * (l + 1) - 1 + 1) → ι → mixedSpace K := fun m i ↦
    mixedEmbedding K ((reducedIntegralBasis K (e m).1 : K) * v (e m).2 i)
  have hw_lin : LinearIndependent ℝ w :=
    (linearIndependent_real_mixedEmbedding_mul
      (linearIndependent_real_mixedEmbedding_reducedIntegralBasis K) hv).comp e e.injective
  have hw_mem (m : Fin (finrank ℚ K * (l + 1) - 1 + 1)) : w m ∈ Λ.mixedImage := by
    refine Submodule.mem_mixedImage.2 ⟨reducedIntegralBasis K (e m).1 • v (e m).2,
      Λ.smul_mem _ (hvΛB (e m).2).1, ?_⟩
    ext1 i
    simp [w, Algebra.smul_def]
  have hw_body (m : Fin (finrank ℚ K * (l + 1) - 1 + 1)) :
      w m ∈ (cK * successiveMinimum Λ B l) • (B : Set (ι → mixedSpace K)) := by
    rcases (hvΛB (e m).2).2 with ⟨z, hz, hzv⟩
    set a : mixedSpace K := cK⁻¹ • mixedEmbedding K (reducedIntegralBasis K (e m).1 : K)
    have ha (u : InfinitePlace K) : normAtPlace u a ≤ 1 := by
      rw [normAtPlace_smul, abs_of_pos (inv_pos.2 hcK)]
      have hub := normAtPlace_mixedEmbedding_reducedIntegralBasis_le u (e m).1
      exact (mul_le_mul_of_nonneg_left hub (inv_nonneg.2 hcK.le)).trans_eq
        (inv_mul_cancel₀ hcK.ne')
    refine ⟨fun i ↦ a * z i, hBbal z hz a ha, ?_⟩
    ext1 i
    change (cK * successiveMinimum Λ B l) • (a * z i) =
      mixedEmbedding K ((reducedIntegralBasis K (e m).1 : K) * v (e m).2 i)
    have hzi' : successiveMinimum Λ B l • z i = mixedEmbedding K (v (e m).2 i) := by
      simpa using congr_fun hzv i
    dsimp only [a]
    rw [smul_mul_assoc, smul_smul, mul_right_comm cK _ cK⁻¹, mul_inv_cancel₀ hcK.ne', one_mul,
      ← mul_smul_comm, hzi', ← map_mul]
  exact ZLattice.successiveMin_le (mul_pos hcK ht).le hw_lin hw_mem hw_body

end ComparisonAndAttainment

section MinkowskiSecond

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Equivalence `Fin (card ι) × Fin [K : ℚ] ≃ Fin (finrank ℝ (ι → mixedSpace K))` sending `(l, r)`
to `[K : ℚ] * l + r`. -/
private def blockIndexEquiv :
    Fin (Fintype.card ι) × Fin (finrank ℚ K) ≃ Fin (finrank ℝ (ι → mixedSpace K)) :=
  finProdFinEquiv.trans (finCongr (by rw [mul_comm, finrank_pi_mixedSpace]))

open Classical in
/-- **Minkowski's second theorem over `K`, upper bound** (`ENNReal` measure form; Bombieri–Gubler
Theorem C.2.11, upper inequality): for a full `𝓞 K`-lattice `Λ` in `ι → K`, an additive Haar
measure `μ` on `ι → mixedSpace K`, and a compact symmetric convex set `B`,
`(∏ l, μ_l ^ [K : ℚ]) * μ B ≤ 2 ^ ([K : ℚ] * card ι) * covolume Λ.mixedImage μ`. -/
theorem prod_successiveMinimum_pow_mul_measure_le
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) :
    ENNReal.ofReal (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) * μ B ≤
      2 ^ (finrank ℚ K * Fintype.card ι) *
        ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) := by
  rcases (interior B).eq_empty_or_nonempty with hempty | hne
  · rw [← measure_interior_of_null_frontier (hBc.addHaar_frontier μ), hempty]
    simp
  let Bbody : ConvexBody (ι → mixedSpace K) := ⟨B, hBc, hBk, hne.mono interior_subset⟩
  have hB0 : (0 : ι → mixedSpace K) ∈ interior (Bbody : Set (ι → mixedSpace K)) :=
    hBc.zero_mem_interior_of_symmetric hBs hne
  have hprod : ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K ≤
      ∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m := by
    rw [← Equiv.prod_comp (blockIndexEquiv (K := K) (ι := ι)), Fintype.prod_prod_type]
    refine Finset.prod_le_prod₀ (fun l _ ↦ pow_nonneg (successiveMinimum_nonneg Λ B l) _)
      fun l _ ↦ ?_
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ successiveMinimum_nonneg Λ B l) fun r _ ↦ ?_
    refine (successiveMinimum_le_successiveMin_mixedImage (Λ := Λ) (B := Bbody) hB0 l.isLt).trans
      (ZLattice.monotone_successiveMin Λ.mixedImage hB0 (Fin.mk_le_mk.2 ?_))
    have hval : (finProdFinEquiv (l, r) : ℕ) = finrank ℚ K * (l : ℕ) + (r : ℕ) := by simp [add_comm]
    rw [hval]
    exact Nat.le_add_right _ _
  calc ENNReal.ofReal (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) * μ B
      ≤ ENNReal.ofReal (∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m) * μ B := by gcongr
    _ ≤ 2 ^ finrank ℝ (ι → mixedSpace K) *
          ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) :=
        ZLattice.prod_successiveMin_mul_measure_le_two_pow_mul_covolume Λ.mixedImage μ hBs
    _ = 2 ^ (finrank ℚ K * Fintype.card ι) *
          ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) := by rw [finrank_pi_mixedSpace]

open Classical in
/-- **Minkowski's second theorem over `K`, upper bound** (`ℝ`-valued measure form):
`(∏ l, μ_l ^ [K : ℚ]) * μ.real B ≤ 2 ^ ([K : ℚ] * card ι) * covolume Λ.mixedImage μ`. -/
theorem prod_successiveMinimum_pow_mul_measureReal_le
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) :
    (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) * μ.real B ≤
      2 ^ (finrank ℚ K * Fintype.card ι) * ZLattice.covolume Λ.mixedImage μ := by
  have h := ENNReal.toReal_mono (by finiteness)
    (prod_successiveMinimum_pow_mul_measure_le Λ μ hBc hBk hBs)
  have hnn : 0 ≤ ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K :=
    Finset.prod_nonneg fun l _ ↦ pow_nonneg (successiveMinimum_nonneg Λ B l) _
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos Λ.mixedImage μ).le, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ← measureReal_def] at h

open Classical in
/-- **Minkowski's second theorem over `K`, lower bound** (`ENNReal` measure form; Bombieri–Gubler
Theorem C.2.11, lower inequality): for a full `𝓞 K`-lattice `Λ` in `ι → K`, an additive Haar
measure `μ` on `ι → mixedSpace K`, and a compact symmetric convex neighbourhood `B` of `0` balanced
at every infinite place,
`2 ^ N / (N! · c_K ^ N) * covolume Λ.mixedImage μ ≤ (∏ l, μ_l ^ [K : ℚ]) * μ B`,
where `N = [K : ℚ] * card ι` and `c_K = integralBasisHouse K`. -/
theorem covolume_le_prod_successiveMinimum_pow_mul_measure
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    ENNReal.ofReal ((2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) /
        (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
          integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι)) *
        ZLattice.covolume Λ.mixedImage μ) ≤
      ENNReal.ofReal (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) *
        μ B := by
  let Bbody : ConvexBody (ι → mixedSpace K) := ⟨B, hBc, hBk, ⟨0, mem_of_mem_nhds hB0⟩⟩
  have hBint : (0 : ι → mixedSpace K) ∈ interior (Bbody : Set (ι → mixedSpace K)) :=
    mem_interior_iff_mem_nhds.2 hB0
  set N := finrank ℚ K * Fintype.card ι
  have hN : finrank ℝ (ι → mixedSpace K) = N := finrank_pi_mixedSpace
  have hcK : 0 < integralBasisHouse K ^ N := pow_pos integralBasisHouse_pos N
  have hprod : ∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m ≤
      integralBasisHouse K ^ N *
        ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K := by
    have hpow : integralBasisHouse K ^ N *
        ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K =
        ∏ l : Fin (Fintype.card ι), (integralBasisHouse K * successiveMinimum Λ B l) ^
          finrank ℚ K := by
      simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← pow_mul]
      rfl
    rw [hpow, ← Equiv.prod_comp (blockIndexEquiv (K := K) (ι := ι)), Fintype.prod_prod_type]
    refine Finset.prod_le_prod₀ (fun l _ ↦ Finset.prod_nonneg fun _ _ ↦
      ZLattice.successiveMin_nonneg _ _ _) fun l _ ↦ ?_
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _) fun r _ ↦ ?_
    refine (ZLattice.monotone_successiveMin Λ.mixedImage hBint (Fin.mk_le_mk.2 ?_)).trans
      (successiveMin_mixedImage_le_mul (Λ := Λ) (B := Bbody) hBint hBbal l.isLt)
    have hval : (finProdFinEquiv (l, r) : ℕ) = finrank ℚ K * (l : ℕ) + (r : ℕ) := by simp [add_comm]
    rw [hval]
    have hr : (r : ℕ) + 1 ≤ finrank ℚ K := r.isLt
    have hmul : finrank ℚ K * ((l : ℕ) + 1) = finrank ℚ K * (l : ℕ) + finrank ℚ K :=
      Nat.mul_succ _ _
    omega
  have hmink := ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measure
    Λ.mixedImage μ hBint hBs
  rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hcK).ne' ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (integralBasisHouse K ^ N) *
        ENNReal.ofReal ((2 : ℝ) ^ N / ((N.factorial : ℝ) * integralBasisHouse K ^ N) *
          ZLattice.covolume Λ.mixedImage μ)
      = ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ (ι → mixedSpace K) /
          (finrank ℝ (ι → mixedSpace K)).factorial * ZLattice.covolume Λ.mixedImage μ) := by
          rw [hN, ← ENNReal.ofReal_mul hcK.le]
          congr 1
          field_simp [hcK.ne']
    _ ≤ ENNReal.ofReal (∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m) * μ B := hmink
    _ ≤ ENNReal.ofReal (integralBasisHouse K ^ N *
          ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) * μ B := by gcongr
    _ = ENNReal.ofReal (integralBasisHouse K ^ N) *
          (ENNReal.ofReal (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) *
            μ B) := by
          rw [ENNReal.ofReal_mul hcK.le, mul_assoc]

open Classical in
/-- **Minkowski's second theorem over `K`, lower bound** (`ℝ`-valued measure form):
`2 ^ N / (N! · c_K ^ N) * covolume Λ.mixedImage μ ≤ (∏ l, μ_l ^ [K : ℚ]) * μ.real B`. -/
theorem covolume_le_prod_successiveMinimum_pow_mul_measureReal
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    (2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) /
        (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
          integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι)) *
        ZLattice.covolume Λ.mixedImage μ ≤
      (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K) * μ.real B := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBk.measure_lt_top.ne)
    (covolume_le_prod_successiveMinimum_pow_mul_measure Λ μ hBc hBk hBs hB0 hBbal)
  have hnn : 0 ≤ ∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l ^ finrank ℚ K :=
    Finset.prod_nonneg fun l _ ↦ pow_nonneg (successiveMinimum_nonneg Λ B l) _
  have hcK : 0 < integralBasisHouse K := integralBasisHouse_pos
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn, ENNReal.toReal_ofReal
    (mul_nonneg (by positivity) (ZLattice.covolume_pos Λ.mixedImage μ).le),
    ← measureReal_def] at h

end MinkowskiSecond

section Examples

open Classical in
/-- Over `ℚ`, `integralBasisHouse ℚ = 1`, so the lower bound in Minkowski's second theorem over `ℚ`
recovers the classical constant `2 ^ n / n!` without loss. -/
example {ι : Type*} [Fintype ι] (Λ : Submodule (𝓞 ℚ) (ι → ℚ))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : Set (ι → mixedSpace ℚ)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace ℚ, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    (2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial *
        ZLattice.covolume Λ.mixedImage ≤
      (∏ l : Fin (Fintype.card ι), successiveMinimum Λ B l) * volume.real B := by
  simpa [Module.finrank_self, integralBasisHouse_rat] using
    covolume_le_prod_successiveMinimum_pow_mul_measureReal Λ volume hBc hBk hBs hB0 hBbal

open Classical in
/-- The hypothesis `l < Fintype.card ι` in `successiveMin_mixedImage_le` cannot be weakened to
`l < finrank ℝ (ι → mixedSpace K)`: when `[K : ℚ] ≥ 2` and `ι = Unit`, `successiveMinimum Λ B 1 = 0`
whereas the index-`1` real minimum of `Λ.mixedImage` is strictly positive. -/
example {K : Type*} [Field K] [NumberField K] (hd : 2 ≤ finrank ℚ K)
    (Λ : Submodule (𝓞 K) (Unit → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (B : ConvexBody (Unit → mixedSpace K))
    (hB0 : (0 : Unit → mixedSpace K) ∈ interior (B : Set (Unit → mixedSpace K))) :
    successiveMinimum Λ B 1 = 0 ∧
      0 < ZLattice.successiveMin Λ.mixedImage B
        ⟨1, by rw [finrank_pi_mixedSpace]; simp; omega⟩ :=
  ⟨successiveMinimum_of_card_le Λ B (by simp), ZLattice.successiveMin_pos Λ.mixedImage hB0 _⟩

end Examples

end TauCeti.NumberField
