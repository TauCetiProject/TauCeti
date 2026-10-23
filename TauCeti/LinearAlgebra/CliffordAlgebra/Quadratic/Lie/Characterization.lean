/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.Algebra.Lie.Derivation.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# Characterizing quadratic Clifford elements

For a nondegenerate quadratic form on a finite-dimensional vector space over a field in which
`2` is invertible, a Clifford element is quadratic precisely when it is even, reversal negates
it, and its commutator with every generating vector is again a generating vector.

The criterion is phrased entirely in the ambient Clifford algebra, so it can identify candidate
infinitesimal elements as quadratic without first choosing exterior-square coordinates.

## Main results

* `CliffordAlgebra.reverse_eq_neg_of_mem_quadraticLieSubalgebra`: reversal negates quadratic
  elements.
* `CliffordAlgebra.mem_quadraticLieSubalgebra_of_mem_even_of_reverse_eq_neg_of_lie_ι_mem_range_ι`:
  the recognition theorem from the three intrinsic conditions.
* `mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι`:
  the complete characterization.
-/

public section

universe u v

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]

/-- Reversal negates every quadratic Clifford element. -/
@[simp]
theorem reverse_eq_neg_of_mem_quadraticLieSubalgebra
    (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx : x ∈ quadraticLieSubalgebra Q) :
    reverse x = -x := by
  rw [mem_quadraticLieSubalgebra_iff] at hx
  obtain ⟨z, rfl⟩ := hx
  exact reverse_bivectorExterior Q z

end CommRing

section Field

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- An even Clifford element which is negated by reversal and whose commutator preserves the
generating vectors is quadratic. This recognizes intrinsic infinitesimal conditions inside the
ambient Clifford algebra as membership in the canonical quadratic Lie subalgebra. -/
theorem mem_quadraticLieSubalgebra_of_mem_even_of_reverse_eq_neg_of_lie_ι_mem_range_ι
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {x : CliffordAlgebra Q}
    (hx_even : x ∈ even Q) (hx_reverse : reverse x = -x)
    (hx_lie : ∀ v : V, ⁅x, ι Q v⁆ ∈ LinearMap.range (ι Q)) :
    x ∈ quadraticLieSubalgebra Q := by
  -- Reconstruct the endomorphism represented by the commutator action on generators.
  let g : V →ₗ[K] LinearMap.range (ι Q) :=
    { toFun := fun v => ⟨⁅x, ι Q v⁆, hx_lie v⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        simp
      map_smul' := by
        intro c v
        apply Subtype.ext
        simp }
  let f : Module.End K V := (ιRangeEquiv Q).symm.toLinearMap.comp g
  have hf_lie (v : V) : ⁅x, ι Q v⁆ = ι Q (f v) := by
    -- Expose the composition defining `f` so the range equivalence can cancel.
    change ⁅x, ι Q v⁆ = ι Q ((ιRangeEquiv Q).symm (g v))
    rw [ι_ιRangeEquiv_symm_apply]
    rfl
  -- Differentiating the polarized Clifford relation makes `f` skew-adjoint.
  have hf_skew : f ∈ (QuadraticMap.polarBilin Q).skewAdjointSubmodule := by
    rw [LinearMap.mem_skewAdjointSubmodule]
    intro u v
    have hsum :
        algebraMap K (CliffordAlgebra Q)
            (QuadraticMap.polar Q (f u) v + QuadraticMap.polar Q u (f v)) = 0 := by
      have hxu := TauCeti.derivationLieAlgebra.leibniz
        (TauCeti.innerDerivation K x) (ι Q u) (ι Q v)
      have hxv := TauCeti.derivationLieAlgebra.leibniz
        (TauCeti.innerDerivation K x) (ι Q v) (ι Q u)
      simp only [TauCeti.coe_innerDerivation, LieAlgebra.ad_apply] at hxu hxv
      rw [map_add, ← ι_mul_ι_add_swap, ← ι_mul_ι_add_swap]
      calc
        ι Q (f u) * ι Q v + ι Q v * ι Q (f u) +
              (ι Q u * ι Q (f v) + ι Q (f v) * ι Q u) =
            ⁅x, ι Q u * ι Q v + ι Q v * ι Q u⁆ := by
              rw [lie_add, hxu, hxv, hf_lie, hf_lie]
              abel
        _ = ⁅x, algebraMap K (CliffordAlgebra Q) (QuadraticMap.polar Q u v)⁆ := by
              rw [ι_mul_ι_add_swap]
        _ = 0 := by
              rw [Ring.lie_def, Algebra.commutes]
              exact sub_self _
    have hpolar :
        QuadraticMap.polar Q (f u) v + QuadraticMap.polar Q u (f v) = 0 :=
      (algebraMap K (CliffordAlgebra Q)).injective (by simpa using hsum)
    -- Unfold skew-adjointness to its bilinear-form equation.
    change QuadraticMap.polarBilin Q (f u) v =
      QuadraticMap.polarBilin Q u ((-f) v)
    simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.neg_apply, map_neg]
    exact eq_neg_of_add_eq_zero_left hpolar
  -- Compare with the canonical quadratic element realizing the same endomorphism.
  let fs : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) := ⟨f, hf_skew⟩
  let q : CliffordAlgebra Q := soEquivQuadratic Q hQ fs
  have hq_lie (v : V) : ⁅q, ι Q v⁆ = ι Q (f v) :=
    soEquivQuadratic_lie_ι Q hQ fs v
  have hq_mem : q ∈ quadraticLieSubalgebra Q := (soEquivQuadratic Q hQ fs).2
  let d : CliffordAlgebra Q := x - q
  have hd_even : d ∈ even Q := Subalgebra.sub_mem (even Q) hx_even
    (quadraticLieSubalgebra_le_even Q hq_mem)
  have hd_comm (v : V) : Commute d (ι Q v) := by
    rw [Commute, SemiconjBy]
    -- Expose the difference defining `d` in the ambient multiplication equation.
    change (x - q) * ι Q v = ι Q v * (x - q)
    have hxq : ⁅x, ι Q v⁆ = ⁅q, ι Q v⁆ := (hf_lie v).trans (hq_lie v).symm
    simp only [Ring.lie_def] at hxq
    rw [sub_mul, mul_sub]
    calc
      x * ι Q v - q * ι Q v =
          (x * ι Q v - ι Q v * x) + (ι Q v * x - q * ι Q v) := by abel
      _ = (q * ι Q v - ι Q v * q) + (ι Q v * x - q * ι Q v) := by rw [hxq]
      _ = ι Q v * x - ι Q v * q := by abel
  -- The commuting even difference is scalar; reversal then forces that scalar to vanish.
  obtain ⟨r, hr⟩ :=
    exists_eq_algebraMap_of_mem_even_of_commute Q hQ d hd_even hd_comm
  have hq_reverse : reverse q = -q :=
    reverse_eq_neg_of_mem_quadraticLieSubalgebra Q hq_mem
  have hd_reverse : reverse d = -d := by
    simp only [d, map_sub, hx_reverse, hq_reverse]
    abel
  have hd_fixed : reverse d = d := by rw [hr]; simp
  have hd_neg : d = -d := hd_fixed.symm.trans hd_reverse
  have htwo : (2 : K) • d = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hd_neg
  have hd_zero : d = 0 := (isUnit_of_invertible (2 : K)).smul_eq_zero.mp htwo
  have hxq : x = q := sub_eq_zero.mp hd_zero
  rw [hxq]
  exact hq_mem

/-- A Clifford element is quadratic exactly when it is even, reversal negates it, and its
commutator with every generator is again a generating vector. -/
theorem mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {x : CliffordAlgebra Q} :
    x ∈ quadraticLieSubalgebra Q ↔
      x ∈ even Q ∧ reverse x = -x ∧
        ∀ v : V, ⁅x, ι Q v⁆ ∈ LinearMap.range (ι Q) := by
  constructor
  · intro hx
    exact ⟨quadraticLieSubalgebra_le_even Q hx,
      reverse_eq_neg_of_mem_quadraticLieSubalgebra Q hx,
      lie_ι_mem_range_ι_of_mem_quadraticLieSubalgebra Q hx⟩
  · rintro ⟨hx_even, hx_reverse, hx_lie⟩
    exact mem_quadraticLieSubalgebra_of_mem_even_of_reverse_eq_neg_of_lie_ι_mem_range_ι
      Q hQ hx_even hx_reverse hx_lie

end Field

end CliffordAlgebra
