/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Geometry.Convex.Cone.Farkas
import Mathlib.LinearAlgebra.Matrix.DotProduct
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
  needed, because both sides vanish on constants. Functionals differing by a multiple of the cyclic
  trace `∑ s, ∑ i, β s i` have the same certificate, since the trace of `boundaryLinear f` is zero.
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

/-- **Valid boundary functionals are rhombus certificates.** A linear functional `φ` on cyclic
boundary triples is nonnegative on the boundary of every hive with values in `K` exactly when, for
some nonnegative weights `y` on the unit rhombi, `φ (boundaryLinear ℤ n K f)` equals the weighted
sum of the rhombus slacks of `f` for every lattice function `f`. -/
theorem forall_map_boundary_nonneg_iff_exists_sum_mul_rhombusSlack
    (φ : Module.Dual K (Fin 3 → Fin n → K)) :
    (∀ h : Hive n K, 0 ≤ φ h.boundary) ↔ ∃ y : Rhombus n → K, 0 ≤ y ∧ ∀ f : Vertex n → K,
      φ (boundaryLinear ℤ n K f) = ∑ r, y r * rhombusSlack f r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 := by
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
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hy r) (rhombusSlack_nonneg h r.2)

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
