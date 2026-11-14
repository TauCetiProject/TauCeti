/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Geometry.Convex.Cone.Farkas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Farkas certificates for hives with prescribed boundary

The normalized hives with values in a linearly ordered field `K` and a prescribed clockwise
boundary `B` are the solutions of the finite linear system `rhombusMatrix K n *ᵥ f ≤ 0`,
`eqMatrix K n *ᵥ f = eqRHS B`. Farkas' lemma for such systems
(`Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_add_vecMul_eq`,
`Matrix.not_exists_mulVec_le_and_mulVec_eq_iff`) gives the dual description of the boundaries of
hives.

* A linear functional `φ` on boundary triples is nonnegative on the boundary of every hive exactly
  when `φ ∘ boundaryLinear` is a nonnegative combination of unit-rhombus slacks
  (`TauCeti.Hive.forall_nonneg_boundary_iff_exists_sum_rhombusSlack`). The certificate is an
  identity of functionals on *all* lattice functions: no multiple of the normalization `f A` is
  needed, because both sides vanish on constants. Functionals differing by a multiple of the cyclic
  trace `∑ s, ∑ i, β s i` have the same certificate, since the trace of `boundaryLinear f` is zero.
* A boundary triple is the boundary of a hive exactly when every such functional is nonnegative
  on it (`TauCeti.Hive.exists_boundary_eq_iff_forall_nonneg`): the hive boundary cone equals its
  bipolar, with no closure taken.

Since certificates are finite data, the existence of a hive with given boundary is unchanged by
an order-preserving extension of scalars (`TauCeti.Hive.exists_boundary_eq_map_iff`). For an
integral boundary `B` this gives rational witnesses, and clearing their denominators shows that
`B` is the boundary of a real hive exactly when some positive multiple `N • B` is the boundary of
an integer hive (`TauCeti.Hive.exists_boundary_eq_intCast_iff`).

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

variable {n : ℕ}

/-- A hive with boundary `B` exists exactly when the matrix system of
`TauCeti.Hive.mem_fixedBoundary_iff_mulVec` is feasible. -/
private theorem exists_boundary_eq_iff_mulVec {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] (B : Fin 3 → Fin n → R) :
    (∃ h : Hive n R, h.boundary = B) ↔
      ∃ f, rhombusMatrix R n *ᵥ f ≤ 0 ∧ eqMatrix R n *ᵥ f = eqRHS B := by
  refine ⟨fun ⟨h, hB⟩ => ⟨h, ((mem_fixedBoundary_iff_mulVec B h).mp
    ⟨h.apply_cornerA, h.isRhombusConcave, (boundaryLinear_coe ℤ h).trans hB⟩).symm⟩,
    fun ⟨f, hR, hE⟩ => ?_⟩
  obtain ⟨hA, hconc, hB⟩ := (mem_fixedBoundary_iff_mulVec B f).mpr ⟨hE, hR⟩
  exact ⟨⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩, (boundary_def _).trans hB⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Valid boundary functionals are rhombus certificates.** A linear functional `φ` on cyclic
boundary triples is nonnegative on the boundary of every hive with values in `K` exactly when, for
some nonnegative weights `y` on the unit rhombi, `φ (boundaryLinear ℤ n K f)` equals the weighted
sum of the rhombus slacks of `f` for every lattice function `f`. -/
theorem forall_nonneg_boundary_iff_exists_sum_rhombusSlack
    (φ : Module.Dual K (Fin 3 → Fin n → K)) :
    (∀ h : Hive n K, 0 ≤ φ h.boundary) ↔ ∃ y : Rhombus n → K, 0 ≤ y ∧ ∀ f : Vertex n → K,
      φ (boundaryLinear ℤ n K f) = ∑ r, y r * rhombusSlack f r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 := by
  classical
  refine ⟨fun hφ => ?_, fun ⟨y, hy, hφ⟩ h => ?_⟩
  · -- The functional `f ↦ -φ (boundaryLinear ℤ n K f)`, as a vector.
    set c : Vertex n → K := fun v => -φ (boundaryLinear K n K (Pi.single v 1))
    have hc : ∀ f, c ⬝ᵥ f = -φ (boundaryLinear ℤ n K f) := fun f => by
      have hK : boundaryLinear K n K f = boundaryLinear ℤ n K f := by
        ext s i; simp only [boundaryLinear_apply]
      rw [← hK]
      conv_rhs => rw [pi_eq_sum_univ' f]
      simp [c, dotProduct, mul_comm]
    obtain ⟨y, hy, z, hyz⟩ := (Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_add_vecMul_eq
      (rhombusMatrix K n) (0 : Matrix (Fin 0) (Vertex n) K) c).mp fun f hf _ => by
        have hconc := rhombusMatrix_mulVec_nonpos_iff.mp hf
        have hb : (ofRhombusConcave f hconc).boundary = boundaryLinear ℤ n K f := by
          ext s i; simp [boundary_apply]
        rw [hc, neg_nonpos, ← hb]
        exact hφ _
    refine ⟨y, hy, fun f => ?_⟩
    have h := congrArg (· ⬝ᵥ f) hyz
    simp only [Matrix.vecMul_zero, add_zero, ← Matrix.dotProduct_mulVec, hc] at h
    simp only [dotProduct, rhombusMatrix_mulVec_apply, mul_neg, Finset.sum_neg_distrib] at h
    exact (neg_inj.mp h).symm
  · rw [← boundaryLinear_coe ℤ h, hφ]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hy r) (rhombusSlack_nonneg h r.2)

/-- **Hive boundaries are cut out by their valid functionals.** A boundary triple `B` is the
boundary of a hive with values in `K` exactly when `φ B` is nonnegative for every linear functional
`φ` that is nonnegative on the boundaries of all hives. -/
theorem exists_boundary_eq_iff_forall_nonneg (B : Fin 3 → Fin n → K) :
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
  have hφ : ∀ β, φ β = ∑ s, ∑ i, z (.inr (s, i)) * β s i := fun β => by simp [φ]
  have hz : ∀ f : Vertex n → K, z ⬝ᵥ (eqMatrix K n *ᵥ f) =
      z (.inl ()) * f (Vertex.cornerA n) + φ (boundaryLinear ℤ n K f) := fun f => by
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, hφ]
  refine (hB φ fun h => ?_).not_gt ?_
  · have h' := congrArg (· ⬝ᵥ ⇑h) h0
    simp only [add_dotProduct, ← Matrix.dotProduct_mulVec, hz, apply_cornerA, mul_zero,
      zero_add, zero_dotProduct, ← boundary_def] at h'
    have hle : y ⬝ᵥ (rhombusMatrix K n *ᵥ ⇑h) ≤ y ⬝ᵥ 0 :=
      dotProduct_le_dotProduct_of_nonneg_left
        (rhombusMatrix_mulVec_nonpos_iff.mpr h.isRhombusConcave) hy
    rw [dotProduct_zero] at hle
    linarith
  · simpa [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, hφ] using hlt

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
theorem exists_boundary_eq_intCast_iff {L : Type*} [Field L] [LinearOrder L]
    [IsStrictOrderedRing L] (B : Fin 3 → Fin n → ℤ) :
    (∃ h : Hive n L, h.boundary = fun s i => (B s i : L)) ↔
      ∃ N : ℕ, 0 < N ∧ ∃ h : IntegerHive n, h.boundary = N • B := by
  constructor
  · intro hL
    -- A rational hive with boundary `B`.
    obtain ⟨q, hq⟩ := (exists_boundary_eq_map_iff (Rat.castHom L) Rat.cast_mono
      fun s i => (B s i : ℚ)).mp (by simpa using hL)
    -- Clear the denominators of its values by a positive integer `D`.
    obtain ⟨⟨D, hD⟩, hDq⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) (q : Vertex n → ℚ)
    choose g hg using hDq
    simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at hg
    rw [Submonoid.mem_pos] at hD
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    have hgA : g (Vertex.cornerA n) = 0 := by
      have h := hg (Vertex.cornerA n)
      rw [q.apply_cornerA, mul_zero] at h
      exact_mod_cast h
    refine ⟨D.toNat, by omega, ⟨g, hgA, fun hr => ?_⟩, ?_⟩
    · have h := mul_le_mul_of_nonneg_left (q.le_of_isRhombus hr) hD'.le
      rw [mul_add, mul_add, ← hg, ← hg, ← hg, ← hg] at h
      exact_mod_cast h
    · ext s i
      have hqsi := congrFun (congrFun hq s) i
      rw [boundary_apply] at hqsi
      have hDN : ((D.toNat : ℕ) : ℤ) = D := Int.toNat_of_nonneg hD.le
      apply Int.cast_injective (α := ℚ)
      simp only [boundary_apply, Hive.mk_apply, Pi.smul_apply, nsmul_eq_mul, hDN, Int.cast_sub,
        Int.cast_mul, hg]
      linear_combination (D : ℚ) * hqsi
  · rintro ⟨N, hN, h, hB⟩
    have hN' : (0 : L) < N := by exact_mod_cast hN
    refine ⟨⟨fun p => (h p : L) / N, by simp, fun {a b c d} hr => ?_⟩, ?_⟩
    · rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast h.le_of_isRhombus hr) hN'.le
    · ext s i
      have hsi := congrFun (congrFun hB s) i
      rw [boundary_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul] at hsi
      have hsiL := congrArg (Int.cast : ℤ → L) hsi
      push_cast at hsiL
      simp only [boundary_apply, Hive.mk_apply]
      rw [← sub_div, div_eq_iff hN'.ne']
      linear_combination hsiL

end TauCeti.Hive
