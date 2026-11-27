/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# The monomial and Schur bases of the symmetric homogeneous polynomials

Let `σ` be a finite alphabet and `R` a commutative ring.  This file proves that the Schur
polynomials `s_μ` of `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean` form an
`R`-basis of the symmetric polynomials in `σ` that are homogeneous of degree `n`, indexed by the
partitions of `n` with at most `Fintype.card σ` parts.  Taken over `ℤ`, this is the
finite-alphabet, fixed-degree form of "the Schur functions are a `ℤ`-basis of the symmetric
functions"; the stable symmetric-function ring, in which the unqualified statement lives, is not
built here.

## The index set

Both `TauCeti.msymm_eq_zero_of_card_lt` and `TauCeti.schurPoly_eq_zero_iff` say that a partition
with more parts than the alphabet has letters contributes nothing, so neither family is linearly
independent when indexed by *all* partitions of `n`.  The bases below are therefore indexed by the
subtype `{ν : n.Partition // ν.parts.card ≤ Fintype.card σ}`, which is exactly the range in which
`TauCeti.partWeight` records a partition faithfully.

## The route

Everything runs through a single linear map, `TauCeti.partWeightCoeff`, reading a symmetric
homogeneous polynomial at the *sorted* monomials `TauCeti.partWeight σ ν`.  It is bijective: a
symmetric polynomial has the same coefficient at a monomial and at its sorted rearrangement
(`TauCeti.coeff_eq_coeff_partWeight`), so a symmetric homogeneous polynomial is determined by those
coefficients; and the monomial symmetric polynomials, whose coefficients at sorted monomials are
the Kronecker delta (`TauCeti.coeff_msymm_partWeight`), realize every prescription.  Reading that
bijection as a coordinate system is the monomial basis `TauCeti.msymmBasis`.

The Schur basis is the monomial basis transported along the Kostka matrix.  In the monomial basis
the coordinates of `s_μ` are the Kostka numbers `K_{μν}`
(`TauCeti.msymmBasis_repr_schurPoly`), which vanish unless `μ` dominates `ν`
(`TauCeti.kostkaNumber_eq_zero_of_not_dominates`) and equal `1` on the diagonal
(`TauCeti.kostkaNumber_self`).  Since dominance refines the lexicographic linear order on
partitions (`Nat.Partition.lex_le_of_dominates`), the Kostka matrix is triangular with `1`s on the
diagonal for that linear order, so its determinant is `1` and it is a change of basis.  This is
where the ring hypothesis enters: over `ℕ` the transition matrix is not invertible.

## Main definitions

The module being based, `TauCeti.symmetricHomogeneousSubmodule σ R n`, carries no Schur content and
is defined in `TauCeti/RingTheory/MvPolynomial/Symmetric/Homogeneous.lean`.

* `TauCeti.partWeightCoeff`: the coordinates of a symmetric homogeneous polynomial at the sorted
  monomials.
* `TauCeti.msymmBasis`: **the monomial basis**.
* `TauCeti.schurPolyBasis`: **the Schur basis**.
* `TauCeti.partitionEquivSchurIndex`: identifies partitions of `n` with the Schur basis index
  when the alphabet has at least `n` letters.

## Main results

* `TauCeti.coeff_eq_coeff_partWeight`: a symmetric polynomial has the same coefficient at a
  monomial of degree `n` and at the sorted monomial of the partition of its exponents.
* `TauCeti.partWeightCoeff_bijective`: **a symmetric homogeneous polynomial is exactly a
  prescription of coefficients at the sorted monomials**.
* `TauCeti.coe_msymmBasis` and `TauCeti.msymmBasis_repr_apply`: the monomial basis consists of the
  monomial symmetric polynomials, and coordinates in it are coefficients at sorted monomials.
* `TauCeti.msymmBasis_repr_schurPoly`: **the Kostka numbers are the change-of-basis matrix**, the
  coordinates of `s_μ` in the monomial basis.
* `TauCeti.schurPolyBasis` and `TauCeti.coe_schurPolyBasis`: **the Schur polynomials of the
  partitions of `n` with at most `Fintype.card σ` parts are a basis of the symmetric homogeneous
  polynomials of degree `n`.**
* The symmetric homogeneous polynomials of degree `n` are a free and finite module.
* `TauCeti.finrank_symmetricHomogeneousSubmodule`: the dimension in degree `n` is the number of
  partitions of `n` with at most `Fintype.card σ` parts; it is the number of all partitions of `n`
  in at least `n` letters and smaller in fewer.
* `TauCeti.linearIndependent_diagramSchurPoly`: in `N` variables, the Schur polynomials of all the
  Young diagrams with at most `N` rows, of every degree, are linearly independent over any
  additively cancellative commutative semiring.
* `TauCeti.span_symmetricDiagramSchurPoly_eq_top`: the Schur polynomials span the symmetric
  polynomials over a commutative ring, since they span each homogeneous degree.
* `TauCeti.map_mem_of_forall_symmetricDiagramSchurPoly`: a linear map out of the symmetric
  polynomials lands in a submodule once every Schur polynomial does.
* `TauCeti.linearIndependent_schurPoly_of_card_le`, `TauCeti.linearIndependent_schurPoly`,
  `TauCeti.linearIndependent_diagramSchurPoly_of_colLen_le`,
  `TauCeti.eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le`, and
  `TauCeti.eq_of_sum_nsmul_diagramSchurPoly_eq`: linear independence of the Schur polynomials over
  any additively cancellative commutative semiring (both for bounded-row partitions in any number
  of variables and for all partitions of `n` in at least `n` variables), and uniqueness of
  `ℕ`-coefficients over a characteristic-zero commutative semiring.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Sections 2 and 6: the monomial symmetric functions are a basis, the Kostka matrix is
  unitriangular for the dominance order, and hence the Schur functions are a basis.
* R. P. Stanley, *Enumerative Combinatorics*, Volume 2, §7.10.
-/

public section

namespace TauCeti

open Finset MvPolynomial

/-- For an alphabet with at least `n` letters, every partition of `n` indexes a Schur basis
vector: a partition of `n` has at most `n` parts, so the subtype condition always holds. -/
def partitionEquivSchurIndex (σ : Type*) [Fintype σ] (n : ℕ) (h : n ≤ Fintype.card σ) :
    n.Partition ≃ {μ : n.Partition // μ.parts.card ≤ Fintype.card σ} :=
  (Equiv.subtypeUnivEquiv fun μ : n.Partition => μ.card_parts_le.trans h).symm

/-- Reindexing a partition into the Schur basis retains the same underlying partition. -/
@[simp]
theorem partitionEquivSchurIndex_apply (σ : Type*) [Fintype σ] (n : ℕ) (h : n ≤ Fintype.card σ)
    (μ : n.Partition) : (partitionEquivSchurIndex σ n h μ).val = μ := (rfl)

/-- The inverse reindexing from the Schur basis returns the underlying partition. -/
@[simp]
theorem partitionEquivSchurIndex_symm_apply (σ : Type*) [Fintype σ] (n : ℕ)
    (h : n ≤ Fintype.card σ) (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (partitionEquivSchurIndex σ n h).symm μ = μ.val := (rfl)

section CommSemiring

variable {σ : Type*} {R : Type*} [CommSemiring R] {n : ℕ}

/-! ### The symmetric homogeneous polynomials -/

variable [Fintype σ]

/-- **A Schur polynomial is symmetric and homogeneous** of degree the natural number its partition
partitions. -/
theorem schurPoly_mem_symmetricHomogeneousSubmodule (μ : n.Partition) :
    schurPoly σ R μ ∈ symmetricHomogeneousSubmodule σ R n :=
  mem_symmetricHomogeneousSubmodule.mpr ⟨schurPoly_isSymmetric μ, isHomogeneous_schurPoly μ⟩

/-- **A monomial symmetric polynomial is symmetric and homogeneous** of degree the natural number
its partition partitions. -/
theorem msymm_mem_symmetricHomogeneousSubmodule [DecidableEq σ] (ν : n.Partition) :
    msymm σ R ν ∈ symmetricHomogeneousSubmodule σ R n :=
  mem_symmetricHomogeneousSubmodule.mpr ⟨msymm_isSymmetric σ R ν, isHomogeneous_msymm R ν⟩

/-! ### Coordinates at the sorted monomials -/

/-- **A symmetric polynomial does not see the order of the exponents of a monomial**: its
coefficient at a monomial of total degree `n` is its coefficient at the sorted monomial of the
partition of those exponents.  This is what makes the coordinates below complete. -/
theorem coeff_eq_coeff_partWeight [DecidableEq σ] {p : MvPolynomial σ R} (hp : p.IsSymmetric)
    {d : σ →₀ ℕ} (hd : d.degree = n) :
    p.coeff d = p.coeff (partWeight σ (weightPartition d hd)) := by
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d hd
  conv_rhs => rw [← he, ← hp e]
  exact (coeff_rename_mapDomain _ e.injective _ _).symm

variable (σ R n) in
/-- **The coordinates of a symmetric homogeneous polynomial**: its coefficients at the sorted
monomials `TauCeti.partWeight σ ν`, one for each partition `ν` of `n` short enough for the alphabet
to record.  `TauCeti.partWeightCoeff_bijective` says these coordinates determine the polynomial and
may be prescribed arbitrarily, and `TauCeti.msymmBasis` is the resulting basis. -/
noncomputable def partWeightCoeff :
    symmetricHomogeneousSubmodule σ R n →ₗ[R]
      ({ν : n.Partition // ν.parts.card ≤ Fintype.card σ} →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun ν => (lcoeff (R := R) (partWeight σ ν.val)).comp
      (symmetricHomogeneousSubmodule σ R n).subtype

/-- The coordinates of `TauCeti.partWeightCoeff` are the coefficients at the sorted monomials.
The body of `TauCeti.partWeightCoeff` is not exposed, so this is what a consumer rewrites with. -/
@[simp]
theorem partWeightCoeff_apply (p : symmetricHomogeneousSubmodule σ R n)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    partWeightCoeff σ R n p ν = (p : MvPolynomial σ R).coeff (partWeight σ ν.val) := by
  simp [partWeightCoeff]

/-- **A symmetric homogeneous polynomial is determined by its coefficients at the sorted
monomials**: away from them symmetry moves each coefficient to a sorted one, and away from degree
`n` homogeneity kills it. -/
theorem partWeightCoeff_injective : Function.Injective (partWeightCoeff σ R n) := by
  classical
  intro p q hpq
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  by_cases hd : d.degree = n
  · have h := DFunLike.congr_fun hpq ⟨weightPartition d hd, card_parts_weightPartition_le d hd⟩
    rw [partWeightCoeff_apply, partWeightCoeff_apply] at h
    rw [coeff_eq_coeff_partWeight (mem_symmetricHomogeneousSubmodule.mp p.property).1 hd,
      coeff_eq_coeff_partWeight (mem_symmetricHomogeneousSubmodule.mp q.property).1 hd, h]
  · rw [(mem_symmetricHomogeneousSubmodule.mp p.property).2.coeff_eq_zero hd,
      (mem_symmetricHomogeneousSubmodule.mp q.property).2.coeff_eq_zero hd]

/-- **The coefficients at the sorted monomials may be prescribed arbitrarily**: the combination of
the monomial symmetric polynomials with the prescribed coefficients realizes them, each `m_ν` being
the indicator of its own sorted monomial. -/
theorem partWeightCoeff_surjective : Function.Surjective (partWeightCoeff σ R n) := by
  classical
  intro f
  refine ⟨⟨∑ ν, f ν • msymm σ R ν.val, Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ (msymm_mem_symmetricHomogeneousSubmodule ν.val)⟩,
        Finsupp.ext fun ξ => ?_⟩
  rw [partWeightCoeff_apply, coeff_sum]
  refine (Finset.sum_eq_single ξ (fun ν _ hne => ?_) fun hξ => absurd (mem_univ ξ) hξ).trans ?_
  · rw [AddMonoidAlgebra.coeff_smul_apply, coeff_msymm_partWeight R ν.val ξ.val ξ.property,
      ite_eq_right fun h => hne (Subtype.ext h.symm), smul_zero]
  · rw [AddMonoidAlgebra.coeff_smul_apply, coeff_msymm_partWeight R ξ.val ξ.val ξ.property,
      ite_eq_left rfl,
      smul_eq_mul, mul_one]

/-- **A symmetric homogeneous polynomial is exactly a prescription of coefficients at the sorted
monomials.** -/
theorem partWeightCoeff_bijective : Function.Bijective (partWeightCoeff σ R n) :=
  ⟨partWeightCoeff_injective, partWeightCoeff_surjective⟩

/-! ### The monomial basis -/

variable (σ R n) in
/-- **The monomial basis**: the coordinates of `TauCeti.partWeightCoeff` read as a basis of the
symmetric polynomials of degree `n`, indexed by the partitions of `n` with at most `Fintype.card σ`
parts.  Its basis vectors are the monomial symmetric polynomials `m_ν`
(`TauCeti.coe_msymmBasis`), which is what the name records. -/
noncomputable def msymmBasis :
    Module.Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} R
      (symmetricHomogeneousSubmodule σ R n) :=
  .ofRepr (LinearEquiv.ofBijective _ (partWeightCoeff_bijective (σ := σ) (R := R) (n := n)))

/-- **The coordinates in the monomial basis are the coefficients at the sorted monomials**: this is
the normal form of a monomial-basis coordinate, and the elimination rule matching
`TauCeti.coe_msymmBasis`. -/
@[simp]
theorem msymmBasis_repr_apply (p : symmetricHomogeneousSubmodule σ R n)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (msymmBasis σ R n).repr p ν = (p : MvPolynomial σ R).coeff (partWeight σ ν.val) := by
  -- The coordinate map of `TauCeti.msymmBasis` is the map it was built from.
  have h : (msymmBasis σ R n).repr p = partWeightCoeff σ R n p :=
    LinearEquiv.ofBijective_apply (f := partWeightCoeff σ R n)
      (hf := partWeightCoeff_bijective) p
  rw [h, partWeightCoeff_apply]

/-- **The vectors of the monomial basis are the monomial symmetric polynomials**:
`TauCeti.msymmBasis` is defined through its coordinates, and this reads its basis vectors back as
the polynomials `m_ν` the name records. -/
@[simp]
theorem coe_msymmBasis [DecidableEq σ] (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    ((msymmBasis σ R n ν : symmetricHomogeneousSubmodule σ R n) : MvPolynomial σ R)
      = msymm σ R ν.val := by
  have h : (msymmBasis σ R n).repr (msymmBasis σ R n ν)
      = (msymmBasis σ R n).repr
        ⟨msymm σ R ν.val, msymm_mem_symmetricHomogeneousSubmodule ν.val⟩ := by
    refine (Module.Basis.repr_self _ ν).trans (Finsupp.ext fun ξ => ?_).symm
    rw [msymmBasis_repr_apply, coeff_msymm_partWeight R ν.val ξ.val ξ.property,
        Finsupp.single_apply]
    exact if_congr (Subtype.ext_iff.symm.trans eq_comm) rfl rfl
  exact congrArg Subtype.val ((msymmBasis σ R n).repr.injective h)

/-- **The Kostka numbers are the coordinates of a Schur polynomial in the monomial basis**, which
is the monomial expansion `TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm` read as a change of
basis.  It is not a `simp` lemma: `TauCeti.msymmBasis_repr_apply` already puts a coordinate of the
monomial basis into its normal form as a coefficient. -/
theorem msymmBasis_repr_schurPoly (μ : n.Partition)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (msymmBasis σ R n).repr ⟨schurPoly σ R μ, schurPoly_mem_symmetricHomogeneousSubmodule μ⟩ ν
      = (kostkaNumber μ ν.val : R) := by
  rw [msymmBasis_repr_apply]
  exact coeff_schurPoly_partWeight μ ν.val (by rw [YoungDiagram.colLen_zero_ofPartition]; exact
      ν.property)

/-! ### The dimension -/

omit [Fintype σ] in
/-- The symmetric polynomials of degree `n` in a finite alphabet form a free module, with the
monomial basis `TauCeti.msymmBasis`. -/
instance [Finite σ] : Module.Free R (symmetricHomogeneousSubmodule σ R n) :=
  have := Fintype.ofFinite σ
  .of_basis (msymmBasis σ R n)

omit [Fintype σ] in
/-- The symmetric polynomials of degree `n` in a finite alphabet form a finite module, spanned by
the monomial basis `TauCeti.msymmBasis`. -/
instance [Finite σ] : Module.Finite R (symmetricHomogeneousSubmodule σ R n) :=
  have := Fintype.ofFinite σ
  .of_basis (msymmBasis σ R n)

variable (σ R n) in
/-- **The dimension of the symmetric polynomials of degree `n`** in the alphabet `σ` is the number
of partitions of `n` with at most `Fintype.card σ` parts, the index set of the monomial and Schur
bases. -/
theorem finrank_symmetricHomogeneousSubmodule [Nontrivial R] :
    Module.finrank R (symmetricHomogeneousSubmodule σ R n) =
      Fintype.card {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} :=
  Module.finrank_eq_card_basis (msymmBasis σ R n)

/-- **In at least `n` letters the dimension in degree `n` is the number of partitions of `n`.** -/
theorem finrank_symmetricHomogeneousSubmodule_of_le [Nontrivial R] (h : n ≤ Fintype.card σ) :
    Module.finrank R (symmetricHomogeneousSubmodule σ R n) = Fintype.card n.Partition := by
  rw [finrank_symmetricHomogeneousSubmodule, Fintype.card_congr (partitionEquivSchurIndex σ n h)]

/-- **In fewer than `n` letters the dimension in degree `n` is less than the number of partitions
of `n`**, the partition `1ⁿ` having more parts than the alphabet has letters. -/
theorem finrank_symmetricHomogeneousSubmodule_lt [Nontrivial R] (h : Fintype.card σ < n) :
    Module.finrank R (symmetricHomogeneousSubmodule σ R n) < Fintype.card n.Partition := by
  rw [finrank_symmetricHomogeneousSubmodule]
  refine Fintype.card_subtype_lt (x := Nat.Partition.ones n) ?_
  simpa [Nat.Partition.ones_parts] using h

end CommSemiring

section LinearIndependent

variable {R : Type*} [CommSemiring R] {n : ℕ}

open scoped PartitionLex in
/-- The Schur polynomials of the partitions of `n` with at most `Fintype.card σ` parts are
linearly independent over any additively cancellative commutative semiring `R`. -/
theorem linearIndependent_schurPoly_of_card_le {σ : Type*} [Fintype σ] [IsCancelAdd R] :
    LinearIndependent R
      (fun ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} => schurPoly σ R ν.val) := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s g g' hsum μ hμ => ?_
  by_contra hne
  let t := s.filter fun ν => g ν ≠ g' ν
  have ht : t.Nonempty := ⟨μ, Finset.mem_filter.mpr ⟨hμ, hne⟩⟩
  let ξ := t.max' ht
  have hξt : ξ ∈ t := Finset.max'_mem t ht
  have hξne : g ξ ≠ g' ξ := (Finset.mem_filter.mp hξt).2
  have hcoeff := congrArg (fun p : MvPolynomial σ R => p.coeff (partWeight σ ξ.val)) hsum
  simp only [coeff_sum, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hcoeff
  have hterm (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
      (schurPoly σ R ν.val).coeff (partWeight σ ξ.val) = (kostkaNumber ν.val ξ.val : R) :=
    coeff_schurPoly_partWeight ν.val ξ.val
      (by rw [YoungDiagram.colLen_zero_ofPartition]; exact ξ.property)
  simp_rw [hterm] at hcoeff
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ν => g ν ≠ g' ν),
    ← Finset.sum_filter_add_sum_filter_not s (fun ν => g ν ≠ g' ν)] at hcoeff
  have hrest :
      ∑ ν ∈ s.filter (fun ν => ¬(g ν ≠ g' ν)), g ν * (kostkaNumber ν.val ξ.val : R) =
      ∑ ν ∈ s.filter (fun ν => ¬(g ν ≠ g' ν)), g' ν * (kostkaNumber ν.val ξ.val : R) :=
    Finset.sum_congr rfl fun ν hν => by
      rw [not_not.mp (Finset.mem_filter.mp hν).2]
  have htop (f : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} → R) :
      ∑ ν ∈ t, f ν * (kostkaNumber ν.val ξ.val : R) = f ξ := by
    refine (Finset.sum_eq_single ξ (fun ν hν hνξ => ?_) fun hξ' => absurd hξt hξ').trans ?_
    · have hlt : ν.val < ξ.val := lt_of_le_of_ne (Subtype.coe_le_coe.mpr (Finset.le_max' t ν hν))
        (fun h => hνξ (Subtype.ext h))
      rw [kostkaNumber_eq_zero_of_not_dominates fun hdom =>
        absurd (Nat.Partition.lex_le_of_dominates hdom) (not_le.mpr hlt),
        Nat.cast_zero, mul_zero]
    · rw [kostkaNumber_self, Nat.cast_one, mul_one]
  refold_let t at hcoeff
  rw [htop g, htop g', hrest] at hcoeff
  exact hξne (add_right_cancel hcoeff)

/-- Over an additively cancellative commutative semiring, in an alphabet with at least `n` letters,
the Schur polynomials of all partitions of `n` are linearly independent. -/
theorem linearIndependent_schurPoly {σ : Type*} [Fintype σ] [IsCancelAdd R]
    (h : n ≤ Fintype.card σ) :
    LinearIndependent R (schurPoly σ R : n.Partition → MvPolynomial σ R) :=
  linearIndependent_schurPoly_of_card_le.comp (partitionEquivSchurIndex σ n h)
    (partitionEquivSchurIndex σ n h).injective

/-- Over an additively cancellative commutative semiring, in `N` variables, the diagram-indexed
Schur polynomials `s_ν` of the partitions `ν` of `n` with at most `N` rows are linearly
independent. -/
theorem linearIndependent_diagramSchurPoly_of_colLen_le [IsCancelAdd R] {N : ℕ} :
    LinearIndependent R
      (fun ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} =>
        diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) := by
  let e : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} ≃
      {ν : n.Partition // ν.parts.card ≤ Fintype.card (Fin N)} :=
    Equiv.subtypeEquivRight fun ν => by
      rw [YoungDiagram.colLen_zero_ofPartition, Fintype.card_fin]
  have heq :
      (fun ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} =>
        diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) =
      (fun μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card (Fin N)} =>
        schurPoly (Fin N) R μ.val) ∘ e := by
    funext ν
    simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply, schurPoly_eq_rename,
      rename_diagramSchurPoly]
  rw [heq]
  exact (linearIndependent_schurPoly_of_card_le (σ := Fin N) (R := R) (n := n)).comp e
    e.injective

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
diagram Schur polynomials of the partitions of `n` with at most `N` rows in `N` variables determines
its coefficients uniquely. -/
theorem eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le [CharZero R] {N : ℕ}
    {c c' : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} → ℕ}
    (heq :
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν.val) =
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c' ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) :
    c = c' := by
  have hℕ :
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c ν • diagramSchurPoly N ℕ (YoungDiagram.ofPartition ν.val) =
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c' ν • diagramSchurPoly N ℕ (YoungDiagram.ofPartition ν.val) :=
    MvPolynomial.map_injective (Nat.castRingHom R) Nat.cast_injective <| by
      simpa only [map_sum, map_nsmul, map_diagramSchurPoly] using heq
  funext ν
  exact linearIndependent_iff'ₛ.mp
    (linearIndependent_diagramSchurPoly_of_colLen_le (R := ℕ))
    Finset.univ c c' hℕ ν (Finset.mem_univ ν)

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
diagram Schur polynomials of the partitions of `n` in `N ≥ n` variables determines its
coefficients uniquely. -/
theorem eq_of_sum_nsmul_diagramSchurPoly_eq [CharZero R] {N : ℕ} (h : n ≤ N)
    {c c' : n.Partition → ℕ}
    (heq : ∑ ν : n.Partition, c ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν) =
      ∑ ν : n.Partition, c' ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν)) :
    c = c' := by
  rw [sum_nsmul_diagramSchurPoly_eq_sum_colLen_le,
    sum_nsmul_diagramSchurPoly_eq_sum_colLen_le] at heq
  funext ν
  exact congrFun (eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le heq)
    ⟨ν, by rw [YoungDiagram.colLen_zero_ofPartition]; exact ν.card_parts_le.trans h⟩

/-- **The Schur polynomials are linearly independent**: in `N` variables, the Schur polynomials of
the Young diagrams with at most `N` rows are linearly independent over every additively
cancellative commutative semiring. The diagrams with more rows have Schur polynomial zero
(`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`). -/
theorem linearIndependent_diagramSchurPoly [IsCancelAdd R] {N : ℕ} :
    LinearIndependent R fun μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} => diagramSchurPoly N R μ := by
  rw [linearIndependent_iff'ₛ]
  intro s g g' hsum μ hμ
  -- Keep the terms of degree `|μ|`, which are independent by
  -- `linearIndependent_diagramSchurPoly_of_colLen_le`.
  have hc (ν : {μ : YoungDiagram // μ.colLen 0 ≤ N}) :
      homogeneousComponent μ.val.card (diagramSchurPoly N R ν) =
        if ν.val.card = μ.val.card then diagramSchurPoly N R ν else 0 := by
    rw [homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr isHomogeneous_diagramSchurPoly)]
    exact if_congr eq_comm rfl rfl
  have h := congrArg (homogeneousComponent μ.val.card) hsum
  simp only [map_sum, map_smul, hc, smul_ite, smul_zero] at h
  rw [← sum_filter, ← sum_subtype_eq_sum_filter, ← sum_filter, ← sum_subtype_eq_sum_filter] at h
  let e : {ν : {μ : YoungDiagram // μ.colLen 0 ≤ N} // ν.val.card = μ.val.card} ≃
      {ν : μ.val.card.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} :=
    { toFun := fun ν => ⟨ν.val.val.toPartition ν.property, by simpa using ν.val.property⟩
      invFun := fun ν => ⟨⟨YoungDiagram.ofPartition ν.val, ν.property⟩,
        YoungDiagram.card_ofPartition ν.val⟩
      left_inv := fun ν => by ext : 2; simp
      right_inv := fun ν => by ext : 1; simp }
  have hli : LinearIndependent R
      (fun ν : {ν : {μ : YoungDiagram // μ.colLen 0 ≤ N} // ν.val.card = μ.val.card} =>
        diagramSchurPoly N R ν.val.val) := by
    convert (linearIndependent_diagramSchurPoly_of_colLen_le
      (R := R) (n := μ.val.card) (N := N)).comp e e.injective with ν
    simp [e]
  exact linearIndependent_iff'ₛ.mp hli (s.subtype fun ν => ν.val.card = μ.val.card)
    (fun ν => g ν.val) (fun ν => g' ν.val) h ⟨μ, rfl⟩ (by simpa using hμ)

end LinearIndependent

/-! ### The Schur basis -/

section CommRing

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] {n : ℕ}

variable (σ R n) in
/-- The Schur polynomials of the partitions the alphabet records, as elements of the module they
are about to be shown to be a basis of. -/
private noncomputable def schurPolyElem
    (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    symmetricHomogeneousSubmodule σ R n :=
  ⟨schurPoly σ R μ.val, schurPoly_mem_symmetricHomogeneousSubmodule μ.val⟩

open scoped PartitionLex in
/-- **The Kostka matrix is triangular with `1`s on the diagonal**, hence a change of basis:
`K_{μν}` vanishes unless `μ` dominates `ν`, dominance refines the lexicographic linear order, and
`K_{μμ}` is `1`. -/
private theorem isUnit_det_schurPolyElem :
    IsUnit ((msymmBasis σ R n).det (schurPolyElem σ R n)) := by
  have hentry : ∀ ν μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ},
      (msymmBasis σ R n).toMatrix (schurPolyElem σ R n) ν μ = (kostkaNumber μ.val ν.val : R) := by
    intro ν μ
    rw [Module.Basis.toMatrix_apply]
    exact msymmBasis_repr_schurPoly μ.val ν
  have htri : ((msymmBasis σ R n).toMatrix (schurPolyElem σ R n)).IsUpperTriangular := by
    intro ν μ hμν
    have hlt : (μ : n.Partition) < (ν : n.Partition) := Subtype.coe_lt_coe.mpr hμν
    rw [hentry ν μ, kostkaNumber_eq_zero_of_not_dominates fun hdom =>
      absurd (Nat.Partition.lex_le_of_dominates hdom) (not_le.mpr hlt), Nat.cast_zero]
  have hdiag : ∏ ν, (msymmBasis σ R n).toMatrix (schurPolyElem σ R n) ν ν = 1 :=
    Finset.prod_eq_one fun ν _ => by rw [hentry ν ν, kostkaNumber_self, Nat.cast_one]
  rw [Module.Basis.det_apply, Matrix.det_of_isUpperTriangular htri, hdiag]
  exact isUnit_one

variable (σ R n) in
/-- **The Schur basis**: the Schur polynomials `s_μ`, for the partitions `μ` of `n` with at most
`Fintype.card σ` parts, are a basis of the symmetric polynomials in `σ` of degree `n`.  Taken over
`ℤ`, this is the finite-alphabet, fixed-degree form of "the Schur functions are a `ℤ`-basis of the
symmetric functions".  The basis vectors are read off by `TauCeti.coe_schurPolyBasis`.

A commutative *ring* is needed: the transition matrix from the monomial basis is the Kostka matrix,
which is unitriangular and so invertible over any commutative ring, but its inverse has negative
entries, and over a semiring such as `ℕ` the Schur polynomials do not span. -/
noncomputable def schurPolyBasis :
    Module.Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} R
      (symmetricHomogeneousSubmodule σ R n) :=
  .mk ((Module.Basis.is_basis_iff_det _).mpr isUnit_det_schurPolyElem).1
    ((Module.Basis.is_basis_iff_det _).mpr isUnit_det_schurPolyElem).2.ge

/-- **The vectors of the Schur basis are the Schur polynomials**: `TauCeti.schurPolyBasis` is
produced from the invertibility of the Kostka matrix rather than from a formula, and this reads its
basis vectors back as the polynomials `s_μ`.  It is what makes the basis usable: a statement about
`TauCeti.schurPolyBasis` becomes a statement about `TauCeti.schurPoly`. -/
@[simp]
theorem coe_schurPolyBasis (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    ((schurPolyBasis σ R n μ : symmetricHomogeneousSubmodule σ R n) : MvPolynomial σ R)
      = schurPoly σ R μ.val := by
  have h : schurPolyBasis σ R n μ = schurPolyElem σ R n μ := Module.Basis.mk_apply _ _ μ
  rw [h]
  rfl

/-- **The coordinates of a Schur expansion**: if a symmetric homogeneous polynomial is a combination
`∑_λ c_λ s_λ` of the Schur polynomials of *all* partitions of `n`, its coordinate in the Schur
basis at a partition the alphabet records is `c_μ`.  The partitions with more parts than the
alphabet has letters contribute nothing, their Schur polynomials vanishing. -/
theorem schurPolyBasis_repr_of_coe_eq_sum {p : symmetricHomogeneousSubmodule σ R n}
    {c : n.Partition → R} (hp : (p : MvPolynomial σ R) = ∑ l, c l • schurPoly σ R l)
    (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (schurPolyBasis σ R n).repr p μ = c μ.val := by
  have h : p = ∑ ν, c ν.val • schurPolyBasis σ R n ν := by
    refine Subtype.ext ?_
    simp only [hp, Submodule.coe_sum, Submodule.coe_smul, coe_schurPolyBasis]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun l : n.Partition => l.parts.card ≤
      Fintype.card σ), Fintype.sum_eq_zero (fun l : {l : n.Partition // ¬_} => _)
      fun l => by rw [schurPoly_eq_zero_of_card_lt _ (not_le.mp l.property), smul_zero], add_zero]
  rw [h, Module.Basis.repr_sum_self]

/-- **The Schur polynomials span the symmetric polynomials**: every symmetric polynomial in `N`
variables is an `R`-linear combination of Schur polynomials. Each homogeneous component of a
symmetric polynomial is symmetric, so it is a combination of Schur polynomials of its degree by the
Schur basis `TauCeti.schurPolyBasis`. -/
theorem span_symmetricDiagramSchurPoly_eq_top {N : ℕ} :
    Submodule.span R (Set.range (symmetricDiagramSchurPoly N R)) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ => ?_
  -- It suffices to show that `x`, read as a polynomial, is a combination of Schur polynomials.
  have hmap : (Submodule.span R (Set.range (symmetricDiagramSchurPoly N R))).map
      (symmetricSubalgebra (Fin N) R).val.toLinearMap =
        Submodule.span R (Set.range (diagramSchurPoly N R)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    ext μ
    simp
  suffices h : (x : MvPolynomial (Fin N) R) ∈ Submodule.span R (Set.range (diagramSchurPoly N R)) by
    rw [← hmap] at h
    obtain ⟨y, hy, hyx⟩ := h
    rwa [Subtype.ext hyx] at hy
  -- Split `x` into homogeneous components and expand each in the Schur basis of its degree.
  rw [← sum_homogeneousComponent (x : MvPolynomial (Fin N) R)]
  refine sum_mem fun d _ => ?_
  have hd : homogeneousComponent d (x : MvPolynomial (Fin N) R) ∈
      symmetricHomogeneousSubmodule (Fin N) R d :=
    mem_symmetricHomogeneousSubmodule.mpr ⟨fun e => by
      rw [rename_homogeneousComponent, (mem_symmetricSubalgebra _).mp x.property e],
      homogeneousComponent_isHomogeneous d _⟩
  have hsum := congrArg Subtype.val ((schurPolyBasis (Fin N) R d).sum_repr ⟨_, hd⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coe_schurPolyBasis] at hsum
  rw [← hsum]
  refine sum_mem fun ν _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨YoungDiagram.ofPartition ν.val, ?_⟩)
  simp [schurPoly_eq_rename]

/-- A linear map out of the symmetric polynomials in `N` variables takes values in a submodule `T`
once it sends every Schur polynomial into `T`, since the Schur polynomials span
(`TauCeti.span_symmetricDiagramSchurPoly_eq_top`). -/
theorem map_mem_of_forall_symmetricDiagramSchurPoly {N : ℕ} {M : Type*} [AddCommMonoid M]
    [Module R M] (f : symmetricSubalgebra (Fin N) R →ₗ[R] M) {T : Submodule R M}
    (h : ∀ μ, f (symmetricDiagramSchurPoly N R μ) ∈ T) (y : symmetricSubalgebra (Fin N) R) :
    f y ∈ T :=
  (Submodule.map_span_le f (Set.range (symmetricDiagramSchurPoly N R)) T).mpr
    (by rintro _ ⟨μ, rfl⟩; exact h μ) ⟨y, by simp [span_symmetricDiagramSchurPoly_eq_top], rfl⟩

end CommRing

end TauCeti
