/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBivectors

/-!
# Type-D root generators in the quadratic Clifford model

An even polarization identifies the split orthogonal Lie algebra of type `D` with the quadratic
Lie subalgebra of its Clifford algebra. This file evaluates that equivalence on the
Bourbaki-numbered root and coroot generators.

For a chain node, the positive and negative matrix generators become

```text
eᵢ ↦ β(bᵢ, b'ᵢ₊₁),        fᵢ ↦ β(bᵢ₊₁, b'ᵢ),
```

while the fork generators become

```text
e ↦ β(bₙ₋₂, bₙ₋₁),        f ↦ β(b'ₙ₋₁, b'ₙ₋₂).
```

The reversed order in the last formula pins the sign: with these choices, the positive and
negative representatives bracket to the numbered coroot on both sides of the equivalence. Thus
the matrix and Clifford descriptions use the same Chevalley normalization, not merely the same
root weights.

## Main results

* `TauCeti.SpinPolarizationData.typeDQuadraticEquiv_rootGenerator`: the signed family of matrix
  root generators maps to the corresponding Clifford representatives.
* `TauCeti.SpinPolarizationData.typeDQuadraticEquiv_cartanGenerator`: the numbered matrix coroot
  maps to the Clifford simple-coroot representative.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The proof interface follows the matrix-action pattern in
  `TauCeti.RepresentationTheory.Spin.Polarization.TypeB.RootGenerators`.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

/-- Recognize the image of a type-`D` matrix as one Clifford bivector by comparing its action on
the hyperbolic basis. -/
private theorem typeDQuadraticEquiv_eq_bivector (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) (x y : V)
    (h : ∀ c : Fin n ⊕ Fin n,
      Matrix.toLinAlgEquiv (P.typeDBasis b hline) A (P.typeDBasis b hline c) =
        polar Q y (P.typeDBasis b hline c) • x -
          polar Q x (P.typeDBasis b hline c) • y) :
    P.typeDQuadraticEquiv b hline A =
      ⟨bivector Q x y, bivector_mem_quadraticLieSubalgebra Q x y⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  exact quadraticLieSubalgebra_eq_bivector_of_lie_ι Q
    (P.nondegenerate_of_line_eq_bot hline) _ _
    (P.typeDQuadraticEquiv_lie_ι b hline A) (P.typeDBasis b hline) x y h

omit [Invertible (2 : K)] in
private theorem polar_dualVector_left (i j : Fin n) :
    polar Q (P.dualVector b i : V) (b j : V) = if j = i then 1 else 0 := by
  rw [polar_comm, P.polar_dualVector]

private theorem typeDQuadraticEquiv_rootGenerator_inl_of_add_one_lt
    (hn : 4 ≤ n) (hline : P.line = ⊥) {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inl i)) =
      ⟨bivector Q (b i : V) (P.dualVector b (TypeDStd.chainNext n i hi) : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector b hline
  rintro (j | j)
  all_goals rw [TypeDStd.val_rootGenerator_inl,
    TypeDStd.toLinAlgEquiv_raisingMatrix_apply_basis_of_chain n hn
      (P.typeDBasis b hline) hi]
  · simp [P.typeDBasis_inl, P.polar_W_eq_zero, P.polar_dualVector_left, eq_comm]
  · simp [P.typeDBasis_inr, P.polar_W'_eq_zero, P.polar_dualVector, eq_comm]

private theorem typeDQuadraticEquiv_rootGenerator_inl_of_not_add_one_lt
    (hn : 4 ≤ n) (hline : P.line = ⊥) {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inl i)) =
      ⟨bivector Q (b (TypeDStd.forkLeft n hn) : V)
          (b (TypeDStd.forkRight n hn) : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector b hline
  rintro (j | j)
  all_goals rw [TypeDStd.val_rootGenerator_inl,
    TypeDStd.toLinAlgEquiv_raisingMatrix_apply_basis_of_fork n hn
      (P.typeDBasis b hline) hi]
  · simp [P.typeDBasis_inl, P.polar_W_eq_zero, eq_comm]
  · simp [P.typeDBasis_inr, P.polar_dualVector, eq_comm]

private theorem typeDQuadraticEquiv_rootGenerator_inr_of_add_one_lt
    (hn : 4 ≤ n) (hline : P.line = ⊥) {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inr i)) =
      ⟨bivector Q (b (TypeDStd.chainNext n i hi) : V) (P.dualVector b i : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector b hline
  rintro (j | j)
  all_goals rw [TypeDStd.val_rootGenerator_inr,
    TypeDStd.toLinAlgEquiv_loweringMatrix_apply_basis_of_chain n hn
      (P.typeDBasis b hline) hi]
  · simp [P.typeDBasis_inl, P.polar_W_eq_zero, P.polar_dualVector_left, eq_comm]
  · simp [P.typeDBasis_inr, P.polar_W'_eq_zero, P.polar_dualVector, eq_comm]

private theorem typeDQuadraticEquiv_rootGenerator_inr_of_not_add_one_lt
    (hn : 4 ≤ n) (hline : P.line = ⊥) {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inr i)) =
      ⟨bivector Q (P.dualVector b (TypeDStd.forkRight n hn) : V)
          (P.dualVector b (TypeDStd.forkLeft n hn) : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector b hline
  rintro (j | j)
  all_goals rw [TypeDStd.val_rootGenerator_inr,
    TypeDStd.toLinAlgEquiv_loweringMatrix_apply_basis_of_fork n hn
      (P.typeDBasis b hline) hi]
  · simp [P.typeDBasis_inl, P.polar_dualVector_left, eq_comm]
  · simp [P.typeDBasis_inr, P.polar_W'_eq_zero, eq_comm]

/-- **The numbered type-`D` matrix root generators are the corresponding positive and negative
Clifford root representatives.** This fixes all four chain/fork and sign cases at once. -/
@[simp]
theorem typeDQuadraticEquiv_rootGenerator (hn : 4 ≤ n) (hline : P.line = ⊥)
    (k : Fin n ⊕ Fin n) :
    (P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn k) : CliffordAlgebra Q) =
      match k with
      | .inl i => P.typeDSimpleRootBivector b (by omega) i
      | .inr i => P.typeDSimpleNegativeRootBivector b (by omega) i := by
  cases k with
  | inl i =>
      simp only
      by_cases hi : (i : ℕ) + 1 < n
      · have hnext : TypeDStd.chainNext n i hi = ⟨(i : ℕ) + 1, hi⟩ := by
          apply Fin.ext
          simp
        exact (congrArg Subtype.val
          (P.typeDQuadraticEquiv_rootGenerator_inl_of_add_one_lt b hn hline hi)).trans
            ((congrArg (fun j => bivector Q (b i : V) (P.dualVector b j : V)) hnext).trans
              (P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi).symm)
      · have hfork :
            bivector Q (b (TypeDStd.forkLeft n hn) : V)
                (b (TypeDStd.forkRight n hn) : V) =
              P.typeDSimpleRootBivector b (by omega) i := by
          have hleft : TypeDStd.forkLeft n hn = ⟨n - 2, by omega⟩ := by
            apply Fin.ext
            simp
          have hright : TypeDStd.forkRight n hn = ⟨n - 1, by omega⟩ := by
            apply Fin.ext
            simp
          exact (congrArg₂ (fun x y : V => bivector Q x y)
            (congrArg (fun j => (b j : V)) hleft)
            (congrArg (fun j => (b j : V)) hright)).trans
              (P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi).symm
        exact (congrArg Subtype.val
          (P.typeDQuadraticEquiv_rootGenerator_inl_of_not_add_one_lt b hn hline hi)).trans hfork
  | inr i =>
      simp only
      by_cases hi : (i : ℕ) + 1 < n
      · have hnext : TypeDStd.chainNext n i hi = ⟨(i : ℕ) + 1, hi⟩ := by
          apply Fin.ext
          simp
        exact (congrArg Subtype.val
          (P.typeDQuadraticEquiv_rootGenerator_inr_of_add_one_lt b hn hline hi)).trans
            ((congrArg (fun j => bivector Q (b j : V) (P.dualVector b i : V)) hnext).trans
              (P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hi).symm)
      · have hfork :
            bivector Q (P.dualVector b (TypeDStd.forkRight n hn) : V)
                (P.dualVector b (TypeDStd.forkLeft n hn) : V) =
              P.typeDSimpleNegativeRootBivector b (by omega) i := by
          have hleft : TypeDStd.forkLeft n hn = ⟨n - 2, by omega⟩ := by
            apply Fin.ext
            simp
          have hright : TypeDStd.forkRight n hn = ⟨n - 1, by omega⟩ := by
            apply Fin.ext
            simp
          exact (congrArg₂ (fun x y : V => bivector Q x y)
            (congrArg (fun j => (P.dualVector b j : V)) hright)
            (congrArg (fun j => (P.dualVector b j : V)) hleft)).trans
              (P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hi).symm
        exact (congrArg Subtype.val
          (P.typeDQuadraticEquiv_rootGenerator_inr_of_not_add_one_lt b hn hline hi)).trans hfork

/-- **The numbered type-`D` matrix coroot maps to the corresponding Clifford simple-coroot
representative.** In particular, the two root-generator normalizations have the same bracket. -/
@[simp]
theorem typeDQuadraticEquiv_cartanGenerator (hn : 4 ≤ n) (hline : P.line = ⊥)
    (i : Fin n) :
    (P.typeDQuadraticEquiv b hline
        (TypeDStd.cartanGenerator n hn i) : CliffordAlgebra Q) =
      P.typeDSimpleCorootBivector b (by omega) i := by
  have hroot :
      ⁅TypeDStd.rootGenerator (K := K) n hn (.inl i),
          TypeDStd.rootGenerator (K := K) n hn (.inr i)⁆ =
        TypeDStd.cartanGenerator (K := K) n hn i := by
    rw [TypeDStd.lie_rootGenerator_inl_inr (K := K), ite_eq_left rfl]
  have hmap :
      P.typeDQuadraticEquiv b hline (TypeDStd.cartanGenerator n hn i) =
        ⁅P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inl i)),
          P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inr i))⁆ := by
    rw [← hroot, (P.typeDQuadraticEquiv b hline).map_lie]
  calc
    (P.typeDQuadraticEquiv b hline
          (TypeDStd.cartanGenerator n hn i) : CliffordAlgebra Q) =
        (⁅P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inl i)),
            P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inr i))⁆ :
          quadraticLieSubalgebra Q) := congrArg Subtype.val hmap
    _ = ⁅(P.typeDQuadraticEquiv b hline
          (TypeDStd.rootGenerator n hn (.inl i)) : CliffordAlgebra Q),
        (P.typeDQuadraticEquiv b hline
          (TypeDStd.rootGenerator n hn (.inr i)) : CliffordAlgebra Q)⁆ := by
      rw [LieSubalgebra.coe_bracket]
    _ = P.typeDSimpleCorootBivector b (by omega) i := by
      rw [P.typeDQuadraticEquiv_rootGenerator b hn hline (.inl i),
        P.typeDQuadraticEquiv_rootGenerator b hn hline (.inr i)]
      exact P.lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector
        (K := K) b (by omega) i

end TauCeti.SpinPolarizationData
