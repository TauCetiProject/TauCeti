/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite matrices over Novikov completions

Matrices with Novikov entries act on finite coordinate modules by ordinary matrix-vector
multiplication. A common lower period bound on the entries gives a uniform filtration shift
for the action. Such bounds exist for every finite matrix, add under composition, and give
explicit finite truncations computing the action to any prescribed cutoff.

A group-ring matrix therefore has a unique continuous extension of its action to Novikov
coordinate modules. The extension is multiplication by the matrix obtained by including each
entry in the completion. Composition uses the native matrix API. When the coefficient and
exponent structures are commutative, that API also supplies Novikov linearity. The cutoff estimates
apply to matrices whose entries are infinite Novikov series, as arise from supported trajectory
counts. No discreteness or injectivity of the period homomorphism is required.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

open TauCeti TauCeti.NovikovSeries
open scoped Matrix

namespace Matrix

variable {R H m n p : Type*}

/-- Every finite Novikov matrix has a common lower period bound, including a matrix with no
entries. Neither the coefficient ring nor the period map needs to be nontrivial. -/
theorem exists_forall_mem_periodFiltration [AddZeroClass H] [AddGroup R] [Finite m] [Finite n]
    {N : H →+ ℝ}
    (A : Matrix m n (NovikovSeries R H N)) :
    ∃ C : ℝ, ∀ i j, A i j ∈ periodFiltration R N C := by
  choose b hb using fun q : m × n => exists_mem_periodFiltration (A q.1 q.2)
  obtain ⟨C, hC⟩ := (Set.finite_range b).bddBelow
  exact ⟨C, fun i j => antitone_periodFiltration (hC (Set.mem_range_self (i, j))) (hb (i, j))⟩

section Estimates

variable [AddZeroClass H] {N : H →+ ℝ} [NonUnitalNonAssocRing R] [Fintype n]

/-- A common lower period bound on matrix entries shifts the coordinatewise filtration by that
bound under matrix-vector multiplication. The output index type need not be finite. -/
theorem mulVec_mem_periodFiltration (A : Matrix m n (NovikovSeries R H N))
    {C D : ℝ} (hA : ∀ i j, A i j ∈ periodFiltration R N C)
    {v : n → NovikovSeries R H N} (hv : ∀ j, v j ∈ periodFiltration R N D) (i : m) :
    (A *ᵥ v) i ∈ periodFiltration R N (C + D) := by
  exact (periodFiltration R N (C + D)).sum_mem fun j _ =>
    NovikovSeries.mul_mem_periodFiltration (hA i j) (hv j)

/-- Lower bounds for two matrices add under composition, uniformly in both outside indices. -/
theorem mul_mem_periodFiltration (A : Matrix m n (NovikovSeries R H N))
    {C D : ℝ} (hA : ∀ i j, A i j ∈ periodFiltration R N C)
    {B : Matrix n p (NovikovSeries R H N)}
    (hB : ∀ j k, B j k ∈ periodFiltration R N D) (i : m) (k : p) :
    (A * B) i k ∈ periodFiltration R N (C + D) := by
  exact (periodFiltration R N (C + D)).sum_mem fun j _ =>
    NovikovSeries.mul_mem_periodFiltration (hA i j) (hB j k)

/-- Perturbing a matrix and an input vector at the indicated cutoffs changes their product only
above the requested output cutoff. The two unperturbed lower bounds are asymmetric, just as in
the scalar identity `a * v - a' * v' = a * (v - v') + (a - a') * v'`. -/
theorem mulVec_sub_mulVec_mem_periodFiltration (A : Matrix m n (NovikovSeries R H N))
    {A' : Matrix m n (NovikovSeries R H N)} {v v' : n → NovikovSeries R H N}
    {C D L : ℝ} (hA : ∀ i j, A i j ∈ periodFiltration R N C)
    (hv' : ∀ j, v' j ∈ periodFiltration R N D)
    (hAA' : ∀ i j, A i j - A' i j ∈ periodFiltration R N (L - D))
    (hvv' : ∀ j, v j - v' j ∈ periodFiltration R N (L - C)) (i : m) :
    (A *ᵥ v) i - (A' *ᵥ v') i ∈ periodFiltration R N L := by
  simp only [mulVec, dotProduct, ← Finset.sum_sub_distrib]
  exact (periodFiltration R N L).sum_mem fun j _ =>
    NovikovSeries.mul_sub_mul_mem_periodFiltration (hA i j) (hv' j) (hAA' i j) (hvv' j)

/-- A matrix action below `L` can be computed using only the finite truncations of its entries
below `L - D` and of its input below `L - C`. This retains every tied exponent even for a dense
or noninjective period map. -/
theorem mulVec_sub_mulVec_trunc_mem_periodFiltration
    (A : Matrix m n (NovikovSeries R H N)) {v : n → NovikovSeries R H N}
    {C D : ℝ} (hA : ∀ i j, A i j ∈ periodFiltration R N C)
    (hv : ∀ j, v j ∈ periodFiltration R N D) (L : ℝ) (i : m) :
    (A *ᵥ v) i -
      ((A.map fun a => ofFinsupp (trunc (L - D) a)) *ᵥ
        (fun j => ofFinsupp (trunc (L - C) (v j)))) i ∈ periodFiltration R N L := by
  simp only [mulVec, dotProduct, map_apply, ← Finset.sum_sub_distrib]
  exact (periodFiltration R N L).sum_mem fun j _ =>
    mul_sub_mul_trunc_mem_periodFiltration (hA i j) (hv j) L

/-- A finite matrix has a single filtration shift that works for all input cutoffs and vectors.
This supplies the uniform support estimate used for completed differentials and homotopies. -/
theorem exists_mulVec_filtration_shift [Finite m]
    (A : Matrix m n (NovikovSeries R H N)) :
    ∃ C : ℝ, ∀ (D : ℝ) (v : n → NovikovSeries R H N),
      (∀ j, v j ∈ periodFiltration R N D) →
        ∀ i, (A *ᵥ v) i ∈ periodFiltration R N (C + D) := by
  obtain ⟨C, hC⟩ := A.exists_forall_mem_periodFiltration
  exact ⟨C, fun _ _ hv i => A.mulVec_mem_periodFiltration hC hv i⟩

end Estimates

section Determinant

variable [AddCommMonoid H] {N : H →+ ℝ} [CommRing R] [Fintype n] [DecidableEq n] {C : ℝ}

/-- A finite product of series `1 + f i` with every `f i ∈ U_C`, `C ≥ 0`, is `1` modulo `U_C`. -/
private theorem prod_one_add_sub_one_mem_periodFiltration (hC : 0 ≤ C) {ι : Type*}
    (s : Finset ι) {f : ι → NovikovSeries R H N} (hf : ∀ i ∈ s, f i ∈ periodFiltration R N C) :
    ∏ i ∈ s, (1 + f i) - 1 ∈ periodFiltration R N C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, add_mul, one_mul, add_sub_right_comm]
    refine add_mem (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) ?_
    have hprod : ∏ i ∈ s, (1 + f i) ∈ periodFiltration R N 0 := by
      simpa using add_mem (antitone_periodFiltration hC
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        (one_mem_periodFiltration_zero (R := R) (N := N))
    simpa only [add_zero] using
      NovikovSeries.mul_mem_periodFiltration (hf a (Finset.mem_insert_self a s)) hprod

/-- **The determinant of a matrix of high period.** Let `X` be a square matrix of Novikov
series whose entry `X i j` lies in `U_(C + w j - w i)` for some weights `w` and some `C ≥ 0`.
Then `det (1 + X)` is `1` modulo `U_C`. The weights cancel along the cycles of every permutation
in the Leibniz expansion. This applies to the matrix of multiplication by a series of `U_C` in a
basis of monomials, with the periods of the basis monomials as weights. -/
theorem det_one_add_sub_one_mem_periodFiltration (hC : 0 ≤ C) (w : n → ℝ)
    {X : Matrix n n (NovikovSeries R H N)}
    (hX : ∀ i j, X i j ∈ periodFiltration R N (C + w j - w i)) :
    (1 + X).det - 1 ∈ periodFiltration R N C := by
  have hdiag (i : n) : X i i ∈ periodFiltration R N C := by simpa using hX i i
  rw [det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), Equiv.Perm.sign_one, one_smul,
    add_sub_right_comm]
  refine add_mem ?_ (sum_mem fun σ hσ => ?_)
  · simpa [Matrix.one_apply_eq] using
      prod_one_add_sub_one_mem_periodFiltration hC Finset.univ fun i _ => hdiag i
  · -- Along `σ ≠ 1`, a factor at a moved index has period at least `C + w i - w (σ i)` and a
    -- factor at a fixed index has nonnegative period; the weights cancel over all indices.
    obtain ⟨j, hj⟩ := not_forall.1 fun h => (Finset.mem_erase.1 hσ).1 (Equiv.ext h)
    rw [Equiv.Perm.one_apply] at hj
    let e : n → ℝ := fun i => (if σ i = i then 0 else C) + (w i - w (σ i))
    have hfactor (i : n) : (1 + X) (σ i) i ∈ periodFiltration R N (e i) := by
      by_cases hi : σ i = i
      · simp only [e, hi, ite_true, sub_self, add_zero, Matrix.add_apply, Matrix.one_apply_eq]
        exact add_mem (one_mem_periodFiltration_zero (R := R) (N := N))
          (antitone_periodFiltration hC (hdiag i))
      · simp only [e, hi, ite_false, Matrix.add_apply, Matrix.one_apply_ne hi, zero_add]
        simpa [add_sub_assoc] using hX (σ i) i
    have hsum : C ≤ ∑ i, e i := by
      have hw : ∑ i, (w i - w (σ i)) = 0 := by
        rw [Finset.sum_sub_distrib, Equiv.sum_comp σ w, sub_self]
      rw [Finset.sum_add_distrib, hw, add_zero]
      calc C = if σ j = j then 0 else C := by simp [hj]
        _ ≤ ∑ i, if σ i = i then 0 else C :=
          Finset.single_le_sum (f := fun i => if σ i = i then 0 else C)
            (fun i _ => by split_ifs <;> simp [hC]) (Finset.mem_univ j)
    rw [Units.smul_def]
    exact zsmul_mem (antitone_periodFiltration hsum
      (prod_mem_periodFiltration Finset.univ fun i _ => hfactor i)) _

end Determinant

section Extension

variable [AddMonoid H] [Ring R] [Fintype n]

/-- A matrix over the group ring has a unique continuous extension of its action to completed
coordinate modules. Its entries are included coefficientwise in the Novikov ring. No topology
on the group ring is needed to state this uniqueness property. -/
theorem continuous_mulVec_extension_iff (A : Matrix m n (AddMonoidAlgebra R H))
    (N : H →+ ℝ) (f : (n → NovikovSeries R H N) → (m → NovikovSeries R H N)) :
    (Continuous f ∧ ∀ v : n → AddMonoidAlgebra R H,
      f (fun j => ofAddMonoidAlgebra (v j)) =
        fun i => ofAddMonoidAlgebra ((A *ᵥ v) i)) ↔
      f = fun v => A.map (ofAddMonoidAlgebra (N := N)) *ᵥ v := by
  let ι : AddMonoidAlgebra R H →+* NovikovSeries R H N := ofAddMonoidAlgebra
  constructor
  · intro hf
    have hd : DenseRange (fun v : n → AddMonoidAlgebra R H =>
        fun j => ι (v j)) :=
      DenseRange.piMap fun _ => denseRange_ofAddMonoidAlgebra
    exact hd.equalizer hf.1 (continuous_const.matrix_mulVec continuous_id)
      (funext fun v => (hf.2 v).trans (funext fun i => ι.map_mulVec A v i))
  · rintro rfl
    exact ⟨continuous_const.matrix_mulVec continuous_id,
      fun v => funext fun i => (ι.map_mulVec A v i).symm⟩

end Extension

end Matrix
