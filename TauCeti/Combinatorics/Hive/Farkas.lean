/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import TauCeti.Combinatorics.Hive.Fibre
import Mathlib.LinearAlgebra.Matrix.Integer
import TauCeti.LinearAlgebra.Matrix.Farkas

/-!
# Farkas certificates for hive fibres

Over a linearly ordered field `K`, pair a boundary `B : Fin 3 → Fin n → K` with a
*boundary functional* `φ : Fin 3 → Fin n → K` by `∑ s, φ s ⬝ᵥ B s`. A functional is *valid* if it
is nonnegative on the boundary of every hive. Every nonnegative combination of unit-rhombus slacks
that factors through the boundary map is valid; Farkas' lemma for the hive cone gives the converse
(`TauCeti.Hive.exists_nonneg_rhombusSlack_combination_iff`): `φ` is valid iff
`∑ s, φ s ⬝ᵥ boundaryLinear f s = ∑ r, y r * rhombusSlack f r` for every lattice function `f`, with
`y ≥ 0`. The identity is between linear functionals on all of `Vertex n → K`, so the normalization
`f A = 0` and the cyclic trace relation of boundaries need not be imposed; correspondingly `φ` is
only determined up to adding a constant, which pairs to zero with every boundary.

Farkas' lemma for the fixed-boundary system (`TauCeti.Hive.eqMatrix`,
`TauCeti.Hive.rhombusMatrix`) gives the witness/certificate alternative: `B` is the boundary of a
hive iff every valid functional is nonnegative on `B` (`TauCeti.Hive.exists_boundary_eq_iff`).

Certificates are finite linear algebra, so they transport along ordered field extensions: a
boundary with entries in `K` is the boundary of a hive with values in an extension `L` iff it is the
boundary of a hive with values in `K` (`TauCeti.Hive.exists_boundary_eq_map_iff`). Applied to
`ℚ → K` and combined with clearing denominators, an integral boundary `B` is the boundary of a
`K`-valued hive iff some dilation `N • B` (`N ≥ 1`) has an integer hive
(`TauCeti.Hive.exists_boundary_eq_intCast_iff`). This is the stretched form of saturation:
the saturation theorem is the further statement that `N = 1` suffices.

## Main results

* `TauCeti.Hive.exists_nonneg_rhombusSlack_combination_iff`: valid boundary functionals are
  exactly the nonnegative combinations of rhombus slacks.
* `TauCeti.Hive.exists_boundary_eq_iff`: witness/certificate alternative for hive fibres.
* `TauCeti.Hive.exists_boundary_eq_map_iff`: fibre nonemptiness is invariant under ordered field
  extension.
* `TauCeti.Hive.exists_boundary_eq_intCast_iff`: real or rational hives with integral boundary
  correspond to integer hives of a dilated boundary.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §§1 and 5.
* A. Knutson, T. Tao, and C. Woodward, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor
  products II: puzzles determine facets of the Littlewood–Richardson cone*, J. Amer. Math. Soc.
  **17** (2004), 19–48, §2.
-/

public section

open Matrix

namespace TauCeti.Hive

variable {n : ℕ} {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-! ### Rhombus-slack combinations -/

/-- A nonnegative combination of the unit-rhombus slacks of a hive is nonnegative. -/
theorem sum_mul_rhombusSlack_nonneg {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {y : Rhombus n → R} (hy : 0 ≤ y) (h : Hive n R) :
    0 ≤ ∑ r : Rhombus n, y r * rhombusSlack h r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 :=
  Finset.sum_nonneg fun r _ => mul_nonneg (hy r) (rhombusSlack_nonneg h r.2)

/-- A solution of the fixed-boundary matrix system for `B` is a hive with boundary `B`. -/
private theorem exists_hive_of_mem_fixedBoundary {B : Fin 3 → Fin n → K} {f : Vertex n → K}
    (heq : eqMatrix K n *ᵥ f = eqRHS B) (hineq : rhombusMatrix K n *ᵥ f ≤ 0) :
    ∃ h : Hive n K, h.boundary = B := by
  obtain ⟨-, hconc, hB⟩ := (mem_fixedBoundary_iff_mulVec B f).mpr ⟨heq, hineq⟩
  exact ⟨ofRhombusConcave f hconc, by rw [boundary_ofRhombusConcave, hB]⟩

/-! ### Valid boundary functionals -/

/-- **Valid boundary functionals.** A boundary functional `φ` is nonnegative on the boundary of
every hive iff, as a linear functional on all lattice functions `f`, `φ ∘ boundaryLinear` is a
nonnegative combination of unit-rhombus slacks. -/
theorem exists_nonneg_rhombusSlack_combination_iff (φ : Fin 3 → Fin n → K) :
    (∃ y : Rhombus n → K, 0 ≤ y ∧ ∀ f : Vertex n → K,
        ∑ s, φ s ⬝ᵥ boundaryLinear ℤ n K f s =
          ∑ r : Rhombus n, y r * rhombusSlack f r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2) ↔
      ∀ h : Hive n K, 0 ≤ ∑ s, φ s ⬝ᵥ h.boundary s := by
  refine ⟨fun ⟨y, hy, hφ⟩ h => ?_, fun H => ?_⟩
  · rw [boundary_def, hφ]
    exact sum_mul_rhombusSlack_nonneg hy h
  -- Apply homogeneous Farkas to the rhombus inequalities, with no equations, and the functional
  -- `c ⬝ᵥ f = -∑ s, φ s ⬝ᵥ boundaryLinear f s`.
  have hc (f : Vertex n → K) :
      (-(eqRHS φ ᵥ* eqMatrix K n)) ⬝ᵥ f = -∑ s, φ s ⬝ᵥ boundaryLinear ℤ n K f s := by
    rw [neg_dotProduct, ← dotProduct_mulVec, dotProduct_comm, dotProduct_eqRHS]
    simp only [eqMatrix_mulVec_inr, dotProduct_comm]
  obtain ⟨y, z, hy, hyz⟩ := (exists_vecMul_add_vecMul_eq_iff (rhombusMatrix K n)
    (0 : Matrix Empty (Vertex n) K) (-(eqRHS φ ᵥ* eqMatrix K n))).mpr fun f hf _ => by
      obtain ⟨h, hh⟩ := exists_hive_of_mem_fixedBoundary (f := f - fun _ => f (Vertex.cornerA n))
        (B := boundaryLinear ℤ n K f) (by ext (⟨⟨⟩⟩ | ⟨s, i⟩) <;> simp) (by
          intro r
          simpa [rhombusMatrix_mulVec_apply, rhombusSlack_sub] using hf r)
      rw [hc, neg_nonpos, ← hh]
      exact H h
  refine ⟨y, hy, fun f => ?_⟩
  have := congrArg (· ⬝ᵥ f) hyz
  simp only [vecMul_zero, add_zero, ← dotProduct_mulVec, dotProduct_rhombusMatrix_mulVec,
    hc, neg_inj] at this
  exact this.symm

/-! ### The witness/certificate alternative -/

/-- **Farkas alternative for hive fibres.** Over a linearly ordered field, `B` is the boundary of
a hive iff `B` pairs nonnegatively with every boundary functional that is nonnegative on all hive
boundaries. By `exists_nonneg_rhombusSlack_combination_iff`, these functionals are the nonnegative
rhombus-slack combinations; a functional negative on `B` is a certificate that the fibre is
empty. -/
theorem exists_boundary_eq_iff (B : Fin 3 → Fin n → K) :
    (∃ h : Hive n K, h.boundary = B) ↔
      ∀ φ : Fin 3 → Fin n → K, (∀ h : Hive n K, 0 ≤ ∑ s, φ s ⬝ᵥ h.boundary s) →
        0 ≤ ∑ s, φ s ⬝ᵥ B s := by
  refine ⟨fun ⟨h, hB⟩ φ hφ => hB ▸ hφ h, fun H => ?_⟩
  obtain ⟨f, hineq, heq⟩ := (exists_mulVec_le_and_mulVec_eq_iff (rhombusMatrix K n) 0
    (eqMatrix K n) (eqRHS B)).mpr fun y z hy hyz => by
      rw [dotProduct_zero, zero_add, dotProduct_eqRHS]
      refine H _ fun h => ?_
      -- On a hive `h`, the relation `y ᵥ* rhombusMatrix + z ᵥ* eqMatrix = 0` reads
      -- `∑ s, z|_s ⬝ᵥ h.boundary s = ∑ r, y r * rhombusSlack h r ≥ 0`.
      have := congrArg (· ⬝ᵥ (h : Vertex n → K)) hyz
      simp only [add_dotProduct, ← dotProduct_mulVec, eqMatrix_mulVec_coe, dotProduct_eqRHS,
        dotProduct_rhombusMatrix_mulVec, zero_dotProduct] at this
      linarith [sum_mul_rhombusSlack_nonneg hy h]
  exact exists_hive_of_mem_fixedBoundary heq hineq

/-! ### Change of ordered field and clearing denominators -/

/-- Hive fibres are nonempty or empty independently of the ordered field: for an ordered field
extension `f : K →+*o L`, a boundary with entries in `K` bounds an `L`-valued hive iff it bounds a
`K`-valued hive. -/
theorem exists_boundary_eq_map_iff (f : K →+*o L) (B : Fin 3 → Fin n → K) :
    (∃ h : Hive n L, h.boundary = fun s i => f (B s i)) ↔ ∃ h : Hive n K, h.boundary = B := by
  refine ⟨fun ⟨h, hB⟩ => ?_, fun ⟨h, hB⟩ => ⟨h.map f, by ext s i; simp [hB]⟩⟩
  have heq := h.eqMatrix_mulVec_coe
  rw [hB, ← map_eqMatrix f, eqRHS_map] at heq
  have hineq' : (rhombusMatrix K n).map f *ᵥ ⇑h ≤ f ∘ (0 : Rhombus n → K) := by
    simpa [map_rhombusMatrix] using h.rhombusMatrix_mulVec_coe_nonpos
  obtain ⟨x, hx, hx'⟩ := (exists_mulVec_le_and_mulVec_eq_map_iff f (rhombusMatrix K n) 0
    (eqMatrix K n) (eqRHS B)).mp ⟨_, hineq', heq⟩
  exact exists_hive_of_mem_fixedBoundary hx' hx

/-- Clearing denominators: a rational hive with integral boundary `B` scales to an integer hive
with boundary `N • B` for some `N ≥ 1`. -/
private theorem exists_hiveCount_pos_of_rat (B : Fin 3 → Fin n → ℤ) (h : Hive n ℚ)
    (hB : h.boundary = fun s i => (B s i : ℚ)) : ∃ N : ℕ, 0 < N ∧ 0 < hiveCount (N • B) := by
  let a : Matrix Unit (Vertex n) ℚ := fun _ p => h p
  have hnum (p : Vertex n) : (a.num () p : ℚ) = a.den * h p := by
    have := (div_eq_iff (Nat.cast_ne_zero.mpr a.den_ne_zero)).mp (a.num_div_den () p)
    rw [this, mul_comm]
  have hden : (0 : ℚ) < a.den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero a.den_ne_zero)
  let g : IntegerHive n :=
    { value := a.num ()
      value_cornerA' := by
        have := hnum (Vertex.cornerA n)
        rw [h.apply_cornerA, mul_zero] at this
        exact_mod_cast this
      le_of_isRhombus' := fun hr => by
        have := mul_le_mul_of_nonneg_left (h.le_of_isRhombus hr) hden.le
        rw [mul_add, mul_add, ← hnum, ← hnum, ← hnum, ← hnum] at this
        exact_mod_cast this }
  refine ⟨a.den, Nat.pos_of_ne_zero a.den_ne_zero, hiveCount_pos_iff.mpr ⟨⟨g, ?_⟩⟩⟩
  ext s i
  have := congrFun (congrFun hB s) i
  rw [boundary_apply] at this ⊢
  refine Int.cast_injective (α := ℚ) ?_
  simp only [Int.cast_sub, g, mk_apply, hnum, ← mul_sub, this, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]

/-- **Rational witnesses and clearing denominators for hives.** Over any linearly ordered field
`K`, an integral boundary `B` is the boundary of a `K`-valued hive iff some dilation `N • B` with
`N ≥ 1` is the boundary of an integer hive. -/
theorem exists_boundary_eq_intCast_iff (B : Fin 3 → Fin n → ℤ) :
    (∃ h : Hive n K, h.boundary = fun s i => (B s i : K)) ↔
      ∃ N : ℕ, 0 < N ∧ 0 < hiveCount (N • B) := by
  refine ⟨fun hK => ?_, fun ⟨N, hN, hcount⟩ => ?_⟩
  · let q : ℚ →+*o K := { Rat.castHom K with monotone' := Rat.cast_mono }
    obtain ⟨h, hB⟩ := (exists_boundary_eq_map_iff q fun s i => (B s i : ℚ)).mp
      (by simpa [q] using hK)
    exact exists_hiveCount_pos_of_rat B h hB
  · obtain ⟨⟨g, hg⟩⟩ := hiveCount_pos_iff.mp hcount
    have hN' : (0 : K) < N := Nat.cast_pos.mpr hN
    refine ⟨(⟨(N : K)⁻¹, inv_nonneg.mpr hN'.le⟩ : Nonneg K) • ofInt K g, ?_⟩
    ext s i
    simp [hg, hN'.ne']

end TauCeti.Hive
