/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
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

For square matrices, row and column period shifts cancel in the determinant. The weighted
determinant and perturbation estimates keep this cancellation explicit, avoiding any loss of
cutoff from the choice of a monomial basis in finite extensions of Novikov rings.

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

section Determinant

variable [AddCommMonoid H] {N : H →+ ℝ} [CommRing R] [Fintype n] [DecidableEq n]

/-- Row and column period shifts cancel in the determinant. Thus an entrywise bound
`D + w j - w i` gives the determinant bound `card n * D`. -/
theorem det_mem_periodFiltration_of_weights (A : Matrix n n (NovikovSeries R H N))
    (w : n → ℝ) {D : ℝ}
    (hA : ∀ i j, A i j ∈ periodFiltration R N (D + w j - w i)) :
    A.det ∈ periodFiltration R N (Fintype.card n * D) := by
  have hsum (σ : Equiv.Perm n) :
      ∑ i, (D + w i - w (σ i)) = Fintype.card n * D := by
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp]
  rw [det_apply]
  apply (periodFiltration R N _).sum_mem
  intro σ _
  have hp := SetLike.prod_mem_graded (periodFiltration R N) (F := Finset.univ)
    (fun i => D + w i - w (σ i)) (fun i => A (σ i) i) (fun i _ => hA (σ i) i)
  rw [hsum] at hp
  exact (periodFiltration R N _).zsmul_mem hp _

/-- A weighted entrywise perturbation changes a determinant only above the corresponding
cutoff. No sign or nonzero-divisor assumption on the coefficients is needed. -/
theorem det_sub_det_mem_periodFiltration_of_weights (A B : Matrix n n (NovikovSeries R H N))
    (w : n → ℝ) {C D : ℝ}
    (hA : ∀ i j, A i j ∈ periodFiltration R N (D + w j - w i))
    (hB : ∀ i j, B i j ∈ periodFiltration R N (D + w j - w i))
    (hAB : ∀ i j, A i j - B i j ∈ periodFiltration R N (C + (D + w j - w i))) :
    A.det - B.det ∈ periodFiltration R N (C + Fintype.card n * D) := by
  have hsum (σ : Equiv.Perm n) :
      ∑ i, (D + w i - w (σ i)) = Fintype.card n * D := by
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp]
  simp only [det_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  apply (periodFiltration R N _).sum_mem
  intro σ _
  have hp := NovikovSeries.prod_sub_prod_mem_periodFiltration_of_bounds Finset.univ
    (fun i _ => hA (σ i) i) (fun i _ => hB (σ i) i) (fun i _ => hAB (σ i) i)
  rw [hsum] at hp
  exact (periodFiltration R N _).zsmul_mem hp _

end Determinant

end Matrix
