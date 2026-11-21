/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Geometry.Convex.Cone.Farkas
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Farkas certificates for hives with prescribed boundary

The normalized hives with values in a linearly ordered field `K` and a prescribed clockwise
boundary `B` are the solutions of the finite linear system `rhombusMatrix K n *ᵥ f ≤ 0`,
`eqMatrix K n *ᵥ f = eqRHS B` (`TauCeti.Hive.exists_boundary_eq_iff_mulVec`). Farkas' lemma for
such systems (`Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_eq`,
`Matrix.not_exists_mulVec_le_and_mulVec_eq_iff`) gives the dual description of the boundaries of
hives.

* A linear functional `φ` on boundary triples is nonnegative on the boundary of every hive exactly
  when `φ ∘ boundaryLinear` is a nonnegative combination of unit-rhombus slacks
  (`TauCeti.Hive.forall_map_boundary_nonneg_iff_exists_sum_mul_rhombusSlack`). The certificate is an
  identity of functionals on *all* lattice functions: no multiple of the normalization `f A` is
  needed, because both sides vanish on constants. Since the range of `boundaryLinear` is the
  trace-zero hyperplane (`TauCeti.Hive.exists_boundaryLinear_eq_iff_sum_eq_zero`), two functionals
  have the same pullback, hence the same certificates, exactly when they differ by a multiple of the
  cyclic trace `∑ s, ∑ i, β s i`
  (`TauCeti.Hive.forall_map_boundaryLinear_eq_zero_iff_exists_eq_mul_sum`).
* A boundary triple is the boundary of a hive exactly when every such functional is nonnegative
  on it (`TauCeti.Hive.exists_boundary_eq_iff_forall_dual_nonneg`): the hive boundary cone equals
  its bipolar, with no closure taken.

Since certificates are finite data, the existence of a hive with given boundary is unchanged by
an order-preserving extension of scalars (`TauCeti.Hive.exists_boundary_eq_map_iff`). For an
integral boundary `B` this gives rational witnesses, and clearing their denominators shows that
`B` is the boundary of a real hive exactly when some positive multiple `N • B` is the boundary of
an integer hive (`TauCeti.Hive.exists_boundary_eq_intCast_iff_exists_boundary_eq_nsmul`), by
`Matrix.exists_mulVec_le_and_mulVec_eq_intCast_iff_exists_nsmul`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §6.
* A. Knutson, T. Tao, and C. Woodward, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor
  products II: Puzzles determine facets of the Littlewood–Richardson cone*, J. Amer. Math. Soc.
  **17** (2004), 19–48, §2.
-/

public section

open scoped Matrix

namespace TauCeti.Hive

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A boundary triple is the clockwise edge-difference triple of some lattice function exactly when
its cyclic trace `∑ s, ∑ i, B s i` vanishes. -/
theorem exists_boundaryLinear_eq_iff_sum_eq_zero {R : Type*} [AddCommGroup R]
    (B : Fin 3 → Fin n → R) :
    (∃ f : Vertex n → R, boundaryLinear ℤ n R f = B) ↔ ∑ s : Fin 3, ∑ i : Fin n, B s i = 0 := by
  refine ⟨fun ⟨f, hf⟩ => hf ▸ sum_boundaryLinear f, fun hB => ?_⟩
  -- `P s k` is the sum of the first `k` entries of side `s`.
  let P (s : Fin 3) (k : ℕ) : R := ∑ j ∈ Finset.range k, if h : j < n then B s ⟨j, h⟩ else 0
  have hP (s : Fin 3) (i : Fin n) : P s (i.val + 1) - P s i.val = B s i := by
    simp [P, Finset.sum_range_succ]
  have hPn (s : Fin 3) : P s n = ∑ i, B s i := by
    simp [P, ← Fin.sum_univ_eq_sum_range]
  -- Walk clockwise from `A`, accumulating the boundary entries; interior values are irrelevant.
  let f (p : Vertex n) : R :=
    if p.z = 0 then P 0 p.y else if p.x = 0 then P 0 n + P 1 p.z
    else if p.y = 0 then P 0 n + P 1 n + P 2 p.x else 0
  have hf (s : Fin 3) (k : Fin (n + 1)) :
      f (Vertex.edgePoint n s k) = ![0, P 0 n, P 0 n + P 1 n] s + P s k := by
    rw [Fin.sum_univ_three, ← hPn, ← hPn, ← hPn] at hB
    obtain ⟨k, hk⟩ := k
    fin_cases s
    · simp [f]
    · rcases k with _ | k
      · simp [f, P]
      · simp [f]
    · rcases Nat.lt_or_ge k n with hkn | hkn
      · rcases k with _ | k
        · simp [f, P, hkn.ne']
        · -- This interior point of edge `C → A` has `z`-coordinate `n - (k + 1) ≠ 0`, so `f`
          -- skips its first (`z = 0`) branch and takes the third (`y = 0`) one.
          have hz : n - (k + 1) ≠ 0 := by omega
          simp [f, hz]
      · obtain rfl : k = n := by omega
        simpa [f, P] using hB.symm
  refine ⟨f, ?_⟩
  ext s i
  rw [boundaryLinear_apply, hf, hf, add_sub_add_left_eq_sub]
  exact hP s i

/-- **Functionals determined modulo the cyclic trace.** A linear functional on boundary triples
vanishes on the clockwise edge differences of every lattice function exactly when it is a multiple
of the cyclic trace `∑ s, ∑ i, B s i`. -/
theorem forall_map_boundaryLinear_eq_zero_iff_exists_eq_mul_sum {R : Type*} [CommRing R]
    (φ : Module.Dual R (Fin 3 → Fin n → R)) :
    (∀ f : Vertex n → R, φ (boundaryLinear ℤ n R f) = 0) ↔
      ∃ c : R, ∀ B, φ B = c * ∑ s : Fin 3, ∑ i : Fin n, B s i := by
  refine ⟨fun hφ => ?_, fun ⟨c, hc⟩ f => by rw [hc, sum_boundaryLinear, mul_zero]⟩
  rcases n with _ | n
  · exact ⟨0, fun B => by simp [Subsingleton.elim B 0]⟩
  -- Every coordinate vector differs from the one at `(0, 0)` by a trace-zero triple.
  let e (s : Fin 3) (i : Fin (n + 1)) : Fin 3 → Fin (n + 1) → R :=
    fun s' i' => if s' = s ∧ i' = i then 1 else 0
  have he (s : Fin 3) (i : Fin (n + 1)) : φ (e s i) = φ (e 0 0) := by
    obtain ⟨f, hf⟩ := (exists_boundaryLinear_eq_iff_sum_eq_zero (e s i - e 0 0)).mpr <| by
      simp [e, ite_and, Finset.sum_sub_distrib]
    rw [← sub_eq_zero, ← map_sub, ← hf, hφ]
  refine ⟨φ (e 0 0), fun B => ?_⟩
  have hB : B = ∑ s, ∑ i, B s i • e s i := by
    ext s i; simp [e, ite_and]
  conv_lhs => rw [hB]
  simp only [map_sum, map_smul, he, smul_eq_mul, ← Finset.sum_mul, mul_comm]

/-- **Valid boundary functionals are rhombus certificates.** A linear functional `φ` on cyclic
boundary triples is nonnegative on the boundary of every hive with values in `K` exactly when, for
some nonnegative weights `y` on the unit rhombi, `φ (boundaryLinear ℤ n K f)` equals the weighted
sum of the rhombus slacks of `f` for every lattice function `f`. -/
theorem forall_map_boundary_nonneg_iff_exists_sum_mul_rhombusSlack
    (φ : Module.Dual K (Fin 3 → Fin n → K)) :
    (∀ h : Hive n K, 0 ≤ φ h.boundary) ↔ ∃ y : Rhombus n → K, 0 ≤ y ∧ ∀ f : Vertex n → K,
      φ (boundaryLinear ℤ n K f) =
        ∑ r, y r * rhombusSlack f r.val.1 r.val.2.1 r.val.2.2.1 r.val.2.2.2 := by
  classical
  refine ⟨fun hφ => ?_, fun ⟨y, hy, hφ⟩ h => ?_⟩
  · -- The functional `f ↦ -φ (boundaryLinear ℤ n K f)`, as a vector.
    obtain ⟨c, hc⟩ := (dotProductEquiv K (Vertex n)).surjective (-φ ∘ₗ boundaryLinear K n K)
    have hc' : ∀ f, c ⬝ᵥ f = -φ (boundaryLinear ℤ n K f) := fun f => by
      have hK : boundaryLinear K n K f = boundaryLinear ℤ n K f := by
        ext s i; simp only [boundaryLinear_apply]
      simpa [hK] using LinearMap.congr_fun hc f
    obtain ⟨y, hy, hyc⟩ := (Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_eq
      (rhombusMatrix K n) c).mp fun f hf => by
        have hconc := rhombusMatrix_mulVec_nonpos_iff.mp hf
        have hb : (ofRhombusConcave f hconc).boundary = boundaryLinear ℤ n K f := by
          ext s i; simp [boundary_apply]
        rw [hc', neg_nonpos, ← hb]
        exact hφ _
    refine ⟨y, hy, fun f => ?_⟩
    have h := congrArg (· ⬝ᵥ f) hyc
    simp only [← Matrix.dotProduct_mulVec, hc'] at h
    simp only [dotProduct, rhombusMatrix_mulVec_apply, mul_neg, Finset.sum_neg_distrib] at h
    exact (neg_inj.mp h).symm
  · rw [← boundaryLinear_coe ℤ h, hφ]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hy r) (rhombusSlack_nonneg h r.property)

/-- **Hive boundaries are cut out by their valid functionals.** A boundary triple `B` is the
boundary of a hive with values in `K` exactly when `φ B` is nonnegative for every linear functional
`φ` that is nonnegative on the boundaries of all hives. -/
theorem exists_boundary_eq_iff_forall_dual_nonneg (B : Fin 3 → Fin n → K) :
    (∃ h : Hive n K, h.boundary = B) ↔
      ∀ φ : Module.Dual K (Fin 3 → Fin n → K), (∀ h : Hive n K, 0 ≤ φ h.boundary) → 0 ≤ φ B := by
  refine ⟨fun ⟨h, hB⟩ φ hφ => hB ▸ hφ h, fun hB => ?_⟩
  by_contra hne
  rw [exists_boundary_eq_iff_mulVec] at hne
  obtain ⟨y, hy, z, h0, hlt⟩ := (Matrix.not_exists_mulVec_le_and_mulVec_eq_iff _ _ _ _).mp hne
  -- The boundary part of the equality multipliers is a valid functional that is negative on `B`.
  let φ : Module.Dual K (Fin 3 → Fin n → K) :=
    ∑ s, ∑ i, z (.inr (s, i)) • ((LinearMap.proj i : (Fin n → K) →ₗ[K] K) ∘ₗ
      (LinearMap.proj s : (Fin 3 → Fin n → K) →ₗ[K] Fin n → K))
  have hz : ∀ β, z ⬝ᵥ eqRHS β = φ β := fun β => by
    simp [φ, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
  refine (hB φ fun h => ?_).not_gt ?_
  · obtain ⟨hE, hR⟩ := (mem_fixedBoundary_iff_mulVec h.boundary h).mp
      ⟨h.apply_cornerA, h.isRhombusConcave, boundaryLinear_coe ℤ h⟩
    simpa [h0, hz] using Matrix.vecMul_add_vecMul_dotProduct_le z hy hR hE
  · simpa [hz] using hlt

/-- The existence of a hive with prescribed boundary is unchanged by an order-preserving ring
homomorphism `f : K →+* L` out of a linearly ordered field: a hive over `L` whose boundary is the
image of `B` exists exactly when a hive over `K` with boundary `B` does. -/
theorem exists_boundary_eq_map_iff {L : Type*} [Ring L] [PartialOrder L] [IsOrderedRing L]
    [Nontrivial L] (f : K →+* L) (hf : Monotone f) (B : Fin 3 → Fin n → K) :
    (∃ h : Hive n L, h.boundary = fun s i => f (B s i)) ↔ ∃ h : Hive n K, h.boundary = B := by
  have hR : (rhombusMatrix K n).map f = rhombusMatrix L n := by
    rw [← map_intCast_rhombusMatrix K, Matrix.map_map, ← map_intCast_rhombusMatrix L]
    exact congrArg _ (funext fun m => map_intCast f m)
  have hE : (eqMatrix K n).map f = eqMatrix L n := by
    rw [← map_intCast_eqMatrix K, Matrix.map_map, ← map_intCast_eqMatrix L]
    exact congrArg _ (funext fun m => map_intCast f m)
  have hd : f ∘ eqRHS B = eqRHS fun s i => f (B s i) := by
    ext (⟨⟩ | ⟨s, i⟩) <;> simp
  rw [exists_boundary_eq_iff_mulVec, exists_boundary_eq_iff_mulVec,
    ← Matrix.exists_mulVec_le_and_mulVec_eq_map_iff f hf, hR, hE, hd]
  simp

/-- **Rational witnesses and clearing denominators.** An integral boundary triple `B` is the
boundary of a hive with values in a linearly ordered field `L`, for instance `ℝ`, exactly when some
positive multiple `N • B` is the boundary of an integer hive. -/
theorem exists_boundary_eq_intCast_iff_exists_boundary_eq_nsmul {L : Type*} [Field L]
    [LinearOrder L] [IsStrictOrderedRing L] (B : Fin 3 → Fin n → ℤ) :
    (∃ h : Hive n L, h.boundary = fun s i => (B s i : L)) ↔
      ∃ N : ℕ, 0 < N ∧ ∃ h : IntegerHive n, h.boundary = N • B := by
  have hd : (eqRHS fun s i => (B s i : L)) = Int.cast ∘ eqRHS B := by
    ext (⟨⟩ | ⟨s, i⟩) <;> simp
  have hN (N : ℕ) : N • eqRHS B = eqRHS (N • B) := by
    ext (⟨⟩ | ⟨s, i⟩) <;> simp
  have key := Matrix.exists_mulVec_le_and_mulVec_eq_intCast_iff_exists_nsmul (K := L)
    (rhombusMatrix ℤ n) 0 (eqMatrix ℤ n) (eqRHS B)
  simp only [map_intCast_rhombusMatrix, map_intCast_eqMatrix, ← hd, smul_zero, hN,
    Function.comp_def, Pi.zero_apply, Int.cast_zero] at key
  simp_rw [exists_boundary_eq_iff_mulVec]
  exact key

end TauCeti.Hive
