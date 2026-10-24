/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.IntMatrix
-- Proof-only: Minkowski's second theorem against Vaaler's slice of the cube.
import TauCeti.NumberTheory.GeometryOfNumbers.SupNormMinima

/-!
# Independent integral solutions of small sup norm, after Bombieri and Vaaler

A subspace `V` of `ℚ^ι` of dimension `k` contains `k` linearly independent integral points
`z 0, …, z (k - 1)`, each primitive (the gcd of its coordinates is `1`), with

```text
‖z 0‖ ⋯ ‖z (k - 1)‖ ≤ H(V),
```

where `‖z‖ = max_i |z i|` is the sup norm and `H(V)` is the absolute Euclidean height
`Submodule.subspaceHeight V`. For the space of solutions of a system `A x = 0` of `p` independent
linear equations with integer coefficients in `n` unknowns, this is the sup-norm form of
Bombieri and Vaaler's Theorem 2: there are `n - p` linearly independent primitive integral
solutions `x l` with

```text
‖x 0‖ ⋯ ‖x (n - p - 1)‖ ≤ √det (A Aᵀ) / g,
```

where `g` is the greatest common divisor of the maximal minors of `A`. The bound depends on `A`
only through its rational row space. The solutions need not form a `ℤ`-basis of the lattice of
all integral solutions: for `A = (0 0 1)`, the solutions `(1, 1, 0)` and `(1, -1, 0)` meet the
bound `1` and span a sublattice of index `2`.

The lattice of integral points of `V` has covolume `H(V)` in the real span of `V`
(`Submodule.covolume_intLattice`), so the statement is the case of integral lattices of
`ZLattice.exists_linearIndependent_prod_norm_ofLp_le_covolume`, which combines Minkowski's second
theorem with Vaaler's cube-slicing theorem.

## Main results

* `Submodule.exists_linearIndependent_intPoints_prod_norm_le`: independent primitive integral
  points of `V` whose sup norms have product at most `H(V)`.
* `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_norm_le`: Bombieri and Vaaler's
  Theorem 2 over `ℤ`, in the sup norm.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 2.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9.
-/

public section

noncomputable section

open Module TauCeti

namespace Submodule

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Independent integral points of small sup norm** (Bombieri–Vaaler). A subspace `V` of `ℚ^ι`
of dimension `k` contains `k` linearly independent integral points `z l`, each with coprime
coordinates, the product of whose sup norms is at most the absolute Euclidean height of `V`. -/
theorem exists_linearIndependent_intPoints_prod_norm_le (V : Submodule ℚ (ι → ℚ)) :
    ∃ z : Fin (finrank ℚ V) → ι → ℤ, LinearIndependent ℤ z ∧ (∀ l, z l ∈ V.intPoints) ∧
      (∀ l, Finset.univ.gcd (z l) = 1) ∧ ∏ l, ‖z l‖ ≤ V.subspaceHeight := by
  obtain ⟨a, ha, haL, hprim, hle⟩ :=
    ZLattice.exists_linearIndependent_prod_norm_ofLp_le_covolume V.intLattice
  rw [covolume_intLattice] at hle
  -- The integral points of `V` with the coordinates of the lattice vectors `a i`.
  set u : Fin (finrank ℝ V.realSpan) → V.intPoints :=
    fun i ↦ V.intPointsEquivIntLattice.symm ⟨a i, haL i⟩
  have hu (i : Fin (finrank ℝ V.realSpan)) (j : ι) :
      (((u i : ι → ℤ) j : ℤ) : ℝ) = (a i : EuclideanSpace ℝ ι) j :=
    intCast_intPointsEquivIntLattice_symm_apply V ⟨a i, haL i⟩ j
  have hlin : LinearIndependent ℤ fun i ↦ (u i : ι → ℤ) := by
    have h : LinearIndependent ℤ fun i ↦ (⟨a i, haL i⟩ : V.intLattice) :=
      LinearIndependent.of_comp V.intLattice.subtype (ha.restrict_scalars' ℤ)
    exact (h.map' V.intPointsEquivIntLattice.symm.toLinearMap (LinearEquiv.ker _)).map'
      V.intPoints.subtype V.intPoints.ker_subtype
  set e := finCongr (finrank_realSpan V)
  refine ⟨fun l ↦ u (e.symm l), hlin.comp _ e.symm.injective, fun l ↦ (u _).2, fun l ↦ ?_, ?_⟩
  · -- Dividing `u i` by the gcd `g` of its coordinates gives an integral point `y` of `V` with
    -- `g • y = a i`, so `g` is a unit by primitivity of `a i`.
    set i := e.symm l
    choose y hy using fun j ↦ Finset.gcd_dvd (f := (u i : ι → ℤ)) (Finset.mem_univ j)
    set g := Finset.univ.gcd (u i : ι → ℤ)
    have hg : g ≠ 0 := fun h ↦ hlin.ne_zero i (funext fun j ↦ Finset.gcd_eq_zero_iff.1 h j
      (Finset.mem_univ j))
    have hgy : g • y = (u i : ι → ℤ) := funext fun j ↦ (hy j).symm
    have hyV : y ∈ V.intPoints := mem_intPoints_of_smul_mem hg (hgy ▸ (u i).2)
    set w := V.intPointsEquivIntLattice ⟨y, hyV⟩
    have hgw : g • (w : V.realSpan) = a i := by
      ext j
      simp only [w, coe_smul_of_tower, PiLp.smul_apply, coe_intPointsEquivIntLattice_apply,
        zsmul_eq_mul, ← hu, hy j, Int.cast_mul]
    exact Finset.normalize_gcd.symm.trans (normalize_eq_one.2 (hprim i _ w.2 g hgw))
  · refine (Finset.prod_le_prod₀ (fun l _ ↦ norm_nonneg _) fun l _ ↦ ?_).trans
      (((e.symm.prod_comp fun i ↦ ‖WithLp.ofLp (a i : EuclideanSpace ℝ ι)‖)).le.trans hle)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ ?_
    rw [Int.norm_eq_abs, hu, ← Real.norm_eq_abs]
    exact norm_le_pi_norm (WithLp.ofLp (a (e.symm l) : EuclideanSpace ℝ ι)) j

end Submodule

namespace Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ}

/-- **Bombieri and Vaaler's Theorem 2 over `ℤ`, in the sup norm.** Let `A` be a `p × n` integer
matrix with linearly independent rows, and let `g` be the greatest common divisor of its maximal
minors. Then `A x = 0` has `n - p` linearly independent integral solutions `x l`, each with
coprime coordinates, whose sup norms `‖x l‖ = max_i |x l i|` satisfy
`∏ l, ‖x l‖ ≤ √det (A Aᵀ) / g`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_norm_le {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ x : Fin (Fintype.card ι - p) → ι → ℤ, LinearIndependent ℤ x ∧ (∀ l, A *ᵥ x l = 0) ∧
      (∀ l, Finset.univ.gcd (x l) = 1) ∧
      ∏ l, ‖x l‖ ≤ √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  set V := LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
  obtain ⟨z, hz, hzV, hzg, hzle⟩ := V.exists_linearIndependent_intPoints_prod_norm_le
  set e := finCongr (finrank_ker_mulVecLin_map hA)
  refine ⟨fun l ↦ z (e.symm l), hz.comp _ e.symm.injective, fun l ↦ ?_, fun l ↦ hzg _, ?_⟩
  · have hx := hzV (e.symm l)
    rw [intPoints_ker_mulVecLin, LinearMap.mem_ker, mulVecLin_apply] at hx
    exact hx
  · rw [← subspaceHeight_ker_mulVecLin hA, e.symm.prod_comp fun l ↦ ‖z l‖]
    exact hzle

end Matrix

end
