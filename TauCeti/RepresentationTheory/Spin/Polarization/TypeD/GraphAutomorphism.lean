/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The graph automorphism of the type-`D` spin representation

The Dynkin diagram `Dₙ` has the symmetry that exchanges its two fork nodes, and it is the source
of the twisted family `²Dₙ(q)`. On the split orthogonal Lie algebra that symmetry is conjugation
by an orthogonal transformation of determinant `-1`, and on the spinor module it is therefore
realized by an element of the Clifford algebra rather than of its even part. This file exhibits
that element and proves the intertwining relations it satisfies.

The vector is `TauCeti.SpinPolarizationData.typeDGraphVector`,

```text
v = b_{n-1} - b'_{n-1},
```

the difference of the last basis vector of the first isotropic summand and its polar dual in the
second. It has `Q v = -1`, so `ι v` squares to `-1` in the Clifford algebra and the reflection in
`v` exchanges `b_{n-1}` with `b'_{n-1}` and fixes every other basis or dual basis vector. Since
conjugation by `ι v` is that reflection up to a sign on each generator, and the type-`D` root
representatives of `TauCeti/RepresentationTheory/Spin/Polarization/TypeD/RootBivectors.lean` are
products of two generators, the two signs cancel on each of them and `ι v` intertwines the
representative at a node with the representative at the node's image under
`TauCeti.graphPermD`. That holds for the positive representatives, the negative ones, and the
coroots alike, so the fork exchange is realized uniformly on the whole pinned Serre system rather
than only on the raising operators.

On the spinor module the resulting operator is
`TauCeti.SpinPolarizationData.typeDGraphOperator`: the spin action of `ι v`, that is creation at
the last coordinate minus annihilation at it. It squares to `-1`, hence is invertible, and it
preserves the coordinate integral lattice in both directions because creation and annihilation
operators do.

Nothing here builds a group, a group scheme, or an automorphism of one. What the numbered-symmetry
machinery of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Scheme/NumberedSymmetry.lean`
consumes is a lattice-preserving linear automorphism of the representation intertwining the
numbered generators along a permutation of their index, and the section on the rational Serre
representation supplies exactly that datum for the type-`D` spin representation and the
permutation `TauCeti.graphPermD`.

Over a field in which `2` is invertible, the final section extends the intertwining from the
numbered generators to the whole split matrix Lie algebra `LieAlgebra.Orthogonal.typeD (Fin n) K`,
whose fork exchange is the native involution `TauCeti.typeDGraphLieEquiv` at the last hyperbolic
pair. The reflection in `v` is the swap matrix of that pair in the hyperbolic basis, and moving
`ι v` past a Clifford element applies the grade involution and then that reflection. Quadratic
elements are even, so `ι v` carries the quadratic element of a matrix `A` to that of its fork
conjugate. Since `ι v` reverses exterior parity, the graph operator carries the even half-spin
summand `S⁺` onto the odd one `S⁻` and intertwines the half-spin action of `A` on `S⁺` with the
action of the fork conjugate of `A` on `S⁻`. In other words `S⁻` is the twist of `S⁺` by the fork
automorphism. Since the graph operator also sends the all-coordinate exterior vector to a multiple
of the vector with its last coordinate erased (`typeDGraphOperator_basis_of_mem`), this is the
exchange of the two fork highest weights.

## Main definitions

* `TauCeti.SpinPolarizationData.typeDGraphVector`: the anisotropic vector whose reflection
  exchanges the two fork nodes of `Dₙ`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator`: its spin action on the spinor module, as a
  linear equivalence.
* `TauCeti.SpinPolarizationData.typeDGraphHalfSpinEquiv`: the graph operator restricted to a
  linear equivalence `S⁺ ≃ S⁻` between the two half-spin summands.
* `TauCeti.SpinPolarizationData.typeDGraphHalfSpinLieModuleEquiv`: the same map, as an
  equivalence of Lie modules from the fork twist of `S⁺` to `S⁻`.

## Main results

* `TauCeti.SpinPolarizationData.quadraticForm_typeDGraphVector`: the graph vector has quadratic
  norm `-1`, so its Clifford generator squares to `-1`.
* `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_typeDSimpleRootBivector`, its negative
  counterpart, and
  `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_typeDSimpleCorootBivector`: the Clifford
  generator of the graph vector intertwines the numbered type-`D` representatives along
  `TauCeti.graphPermD`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_eq_wedge_sub_contract`: the operator is
  creation at the last coordinate minus annihilation at it.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_apply_apply`: it squares to `-1`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_basis_of_notMem` and
  `TauCeti.SpinPolarizationData.typeDGraphOperator_basis_of_mem`: it acts on an exterior basis
  vector by inserting or erasing the final coordinate of its index set, up to a sign.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_spinAction_typeDSimpleRootBivector`, its
  negative counterpart, and
  `TauCeti.SpinPolarizationData.typeDGraphOperator_spinAction_typeDSimpleCorootBivector`: the same
  renumbering, read on the spinor module.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_mem_integralLattice_iff`: it preserves the
  coordinate integral lattice, in both directions.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_typeDSpinRep_rootGenerator`: the intertwining
  relation for the numbered generators of the rational type-`D` Serre representation.
* `TauCeti.SpinPolarizationData.map_typeDGraphOperator_spinPlus`: the graph operator carries `S⁺`
  onto `S⁻`.
* `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_typeDQuadraticEquiv`: conjugation by the
  graph generator is the fork involution `TauCeti.typeDGraphLieEquiv` on the quadratic elements
  of every split type-`D` matrix.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_typeDSpinLieRep`: the graph operator
  intertwines the spin representation of the split type-`D` Lie algebra with its fork twist.
* `TauCeti.SpinPolarizationData.typeDGraphHalfSpinEquiv_typeDSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.typeDGraphHalfSpinEquiv_symm_typeDSpinMinusLieRep`: the fork
  exchange intertwines the two half-spin representations.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spinor model and the
  action of the Clifford generators on it.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15, for
  the graph automorphism of a pinned group of Lie type.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV, for the numbering of the
  `Dₙ` diagram whose last two nodes the symmetry exchanges.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

universe u v

section CommRing

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
variable {n : ℕ} (b : Module.Basis (Fin n) K P.W)

/-! ## The graph vector -/

/-- **The vector whose reflection exchanges the two fork nodes of `Dₙ`**: the difference of the
last basis vector of the first isotropic summand and its polar dual in the second. Its quadratic
norm is `-1`, and the reflection in it exchanges those two vectors while fixing every other basis
and dual basis vector, which is the coordinate description of the diagram symmetry. -/
noncomputable def typeDGraphVector (hn : 2 ≤ n) : V :=
  (b ⟨n - 1, by omega⟩ : V) - (P.dualVector b ⟨n - 1, by omega⟩ : V)

/-- The defining difference of the type-`D` graph vector. -/
theorem typeDGraphVector_def (hn : 2 ≤ n) :
    P.typeDGraphVector b hn =
      (b ⟨n - 1, by omega⟩ : V) - (P.dualVector b ⟨n - 1, by omega⟩ : V) :=
  -- `(rfl)`, not `rfl`: the body of `typeDGraphVector` is not `@[expose]`d.
  (rfl)

/-- The graph vector is orthogonal to every basis vector other than the last. -/
theorem isOrtho_typeDGraphVector_basis_of_ne (hn : 2 ≤ n) {j : Fin n} (hj : (j : ℕ) ≠ n - 1) :
    Q.IsOrtho (P.typeDGraphVector b hn) (b j : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply, typeDGraphVector_def, polar_comm,
    polar_sub_right, P.polar_W_eq_zero, P.polar_dualVector]
  simp only [Fin.ext_iff, zero_sub, neg_eq_zero, ite_eq_right_iff]
  omega

/-- The graph vector pairs with the last basis vector to `-1`. -/
theorem polar_typeDGraphVector_basis_last (hn : 2 ≤ n) :
    polar Q (P.typeDGraphVector b hn) (b ⟨n - 1, by omega⟩ : V) = -1 := by
  rw [typeDGraphVector_def, polar_comm, polar_sub_right, P.polar_W_eq_zero,
    P.polar_dualVector_self]
  ring

/-- The graph vector is orthogonal to every dual basis vector other than the last. -/
theorem isOrtho_typeDGraphVector_dualVector_of_ne (hn : 2 ≤ n) {j : Fin n}
    (hj : (j : ℕ) ≠ n - 1) : Q.IsOrtho (P.typeDGraphVector b hn) (P.dualVector b j : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply, typeDGraphVector_def, polar_sub_left,
    P.polar_W'_eq_zero, P.polar_dualVector]
  simp only [Fin.ext_iff, sub_zero, ite_eq_right_iff]
  omega

/-- The graph vector pairs with the last dual basis vector to `1`. -/
theorem polar_typeDGraphVector_dualVector_last (hn : 2 ≤ n) :
    polar Q (P.typeDGraphVector b hn) (P.dualVector b ⟨n - 1, by omega⟩ : V) = 1 := by
  rw [typeDGraphVector_def, polar_sub_left, P.polar_W'_eq_zero, P.polar_dualVector_self]
  ring

/-- **The graph vector is anisotropic of norm `-1`.** Both summands are isotropic, so the norm is
the negative of the pairing of a basis vector with its own polar dual. -/
@[simp]
theorem quadraticForm_typeDGraphVector (hn : 2 ≤ n) : Q (P.typeDGraphVector b hn) = -1 := by
  rw [typeDGraphVector_def, sub_eq_add_neg, QuadraticMap.map_add Q, P.isotropic_W,
    QuadraticMap.map_neg, P.isotropic_W', polar_neg_right, P.polar_dualVector_self]
  ring

/-! ## Conjugation is the fork reflection -/

/-- Conjugating a Clifford generator by the graph generator is the reflection in the graph vector,
up to the sign that twisted conjugation carries on a vector.

The map `m ↦ m + polar Q v m • v` appearing here is `TauCeti.QuadraticMap.reflection Q v` at a
vector of norm `-1`, which is the same map that `CliffordAlgebra.pinToOrthogonal_ι_apply` computes
as the twisted-conjugation action of `ι v`. It is derived here from the Clifford relation instead
of from the Pin group, because that route needs `2` invertible in the base ring while the type-`D`
representatives below are stated over an arbitrary commutative ring. -/
private theorem ι_typeDGraphVector_mul_ι (hn : 2 ≤ n) (u : V) :
    ι Q (P.typeDGraphVector b hn) * ι Q u =
      -(ι Q (u + polar Q (P.typeDGraphVector b hn) u • P.typeDGraphVector b hn) *
        ι Q (P.typeDGraphVector b hn)) := by
  rw [map_add, map_smul, add_mul, smul_mul_assoc, ι_sq_scalar, quadraticForm_typeDGraphVector,
    map_neg, map_one, ι_mul_ι_comm (Q := Q), Algebra.algebraMap_eq_smul_one]
  module

/-- Conjugation carries the last basis vector to its polar dual. -/
private theorem ι_typeDGraphVector_mul_ι_basis_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) * ι Q (b ⟨n - 1, by omega⟩ : V) =
      -(ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) * ι Q (P.typeDGraphVector b hn)) := by
  have hreflect : (b ⟨n - 1, by omega⟩ : V) +
      polar Q (P.typeDGraphVector b hn) (b ⟨n - 1, by omega⟩ : V) • P.typeDGraphVector b hn =
      (P.dualVector b ⟨n - 1, by omega⟩ : V) := by
    rw [polar_typeDGraphVector_basis_last, typeDGraphVector_def]
    module
  rw [P.ι_typeDGraphVector_mul_ι b hn _, hreflect]

/-- Conjugation carries the last dual basis vector to the last basis vector. -/
private theorem ι_typeDGraphVector_mul_ι_dualVector_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) =
      -(ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.typeDGraphVector b hn)) := by
  have hreflect : (P.dualVector b ⟨n - 1, by omega⟩ : V) +
      polar Q (P.typeDGraphVector b hn) (P.dualVector b ⟨n - 1, by omega⟩ : V) •
        P.typeDGraphVector b hn = (b ⟨n - 1, by omega⟩ : V) := by
    rw [polar_typeDGraphVector_dualVector_last, typeDGraphVector_def]
    module
  rw [P.ι_typeDGraphVector_mul_ι b hn _, hreflect]

/-- The two signs of the generator conjugation cancel on a product of two generators. -/
private theorem ι_typeDGraphVector_mul_ι_mul_ι (hn : 2 ≤ n) {x y x' y' : V}
    (hx : ι Q (P.typeDGraphVector b hn) * ι Q x = -(ι Q x' * ι Q (P.typeDGraphVector b hn)))
    (hy : ι Q (P.typeDGraphVector b hn) * ι Q y = -(ι Q y' * ι Q (P.typeDGraphVector b hn))) :
    ι Q (P.typeDGraphVector b hn) * (ι Q x * ι Q y) =
      ι Q x' * ι Q y' * ι Q (P.typeDGraphVector b hn) := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, ← mul_assoc]

/-! ## The fork exchange on the numbered representatives -/

/-! The three intertwining proofs below split on whether a node is the last one, the penultimate
one, or a chain node, so they meet the fork nodes as equations between the *values* `(i : ℕ)`,
`n - 1` and `n - 2` rather than as `Fin n` indices. The index arguments of the representative
equations are stated in that value form, and the following named facts are the recurring
truncated-subtraction identities they need. -/

/-- The successor of the penultimate node is a node. -/
private theorem penultimate_add_one_lt (hn : 2 ≤ n) : n - 2 + 1 < n := by omega

/-- The last node is the successor of the penultimate one. -/
private theorem last_eq_penultimate_add_one (hn : 2 ≤ n) : n - 1 = n - 2 + 1 := by omega

/-- The penultimate node is not the last one. -/
private theorem penultimate_ne_last (hn : 2 ≤ n) : n - 2 ≠ n - 1 := by omega

/-- The last node has no successor, which is what makes it the fork node. -/
private theorem not_last_add_one_lt (hn : 2 ≤ n) : ¬n - 1 + 1 < n := by omega

/-- The last node is the successor of a node whose value is the penultimate one. -/
private theorem last_eq_val_add_one (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) = n - 2) :
    n - 1 = (i : ℕ) + 1 := by omega

/-- The successor of a chain node other than the penultimate one is not the last node. -/
private theorem val_add_one_ne_last (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) ≠ n - 2) :
    (i : ℕ) + 1 ≠ n - 1 := by omega

/-- A positive representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleRootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleRootBivector b hn i = ι Q (b i : V) * ι Q (P.dualVector b j : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleRootBivector_def, dite_eq_left h, hij]

/-- The positive representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleRootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleRootBivector b hn i =
      ι Q (b ⟨n - 2, by omega⟩ : V) * ι Q (b ⟨n - 1, by omega⟩ : V) := by
  rw [typeDSimpleRootBivector_def, dite_eq_right h]

/-- A negative representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleNegativeRootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleNegativeRootBivector b hn i = ι Q (b j : V) * ι Q (P.dualVector b i : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleNegativeRootBivector_def, dite_eq_left h, hij]

/-- The negative representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleNegativeRootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleNegativeRootBivector b hn i =
      ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) *
        ι Q (P.dualVector b ⟨n - 2, by omega⟩ : V) := by
  rw [typeDSimpleNegativeRootBivector_def, dite_eq_right h]

/-- A coroot representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleCorootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleCorootBivector b hn i =
      ι Q (b i : V) * ι Q (P.dualVector b i : V) -
        ι Q (b j : V) * ι Q (P.dualVector b j : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleCorootBivector_def, dite_eq_left h, hij]

/-- The coroot representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleCorootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleCorootBivector b hn i =
      ι Q (b ⟨n - 2, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 2, by omega⟩ : V) +
        ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) - 1 := by
  rw [typeDSimpleCorootBivector_def, dite_eq_right h]

/-- The occupation product at a node other than the last commutes with the graph generator. -/
private theorem ι_typeDGraphVector_mul_occupation_of_ne (hn : 2 ≤ n) {j : Fin n}
    (hj : (j : ℕ) ≠ n - 1) :
    ι Q (P.typeDGraphVector b hn) * (ι Q (b j : V) * ι Q (P.dualVector b j : V)) =
      ι Q (b j : V) * ι Q (P.dualVector b j : V) * ι Q (P.typeDGraphVector b hn) :=
  P.ι_typeDGraphVector_mul_ι_mul_ι b hn
    (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_basis_of_ne b hn hj))
    (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn hj))

/-- Conjugating the occupation product at the last node reverses it, and reversing it subtracts it
from `1`. -/
private theorem ι_typeDGraphVector_mul_occupation_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) *
        (ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V)) =
      (1 - ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V)) *
        ι Q (P.typeDGraphVector b hn) := by
  have hswap : ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) * ι Q (b ⟨n - 1, by omega⟩ : V) =
      1 - ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) := by
    rw [ι_mul_ι_comm (Q := Q), polar_comm, P.polar_dualVector_self, map_one]
  rw [← hswap]
  exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
    (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
    (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)

/-- The graph permutation sends the fork node to the penultimate node. -/
private theorem graphPermD_of_val_eq_last (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) = n - 1) :
    graphPermD n hn i = (⟨n - 2, by omega⟩ : Fin n) := by
  have hlast : i = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hi
  rw [hlast]
  exact graphPermD_apply_right n hn

/-- The graph permutation sends the penultimate node to the fork node. -/
private theorem graphPermD_of_val_eq_penultimate (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) = n - 2) :
    graphPermD n hn i = (⟨n - 1, by omega⟩ : Fin n) := by
  have hpenultimate : i = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hi
  rw [hpenultimate]
  exact graphPermD_apply_left n hn

/-- The basis vector at a node known only through its value `n - 2`. The fork branches of the
proofs below meet the penultimate node as the value equation `(i : ℕ) = n - 2` rather than as an
index, so the equation has to be transported through `b` and the inclusion of the isotropic
summand before it can rewrite the goal. -/
private theorem basis_coe_of_val_eq_penultimate {i : Fin n} (hi : (i : ℕ) = n - 2) :
    (b i : V) = (b ⟨n - 2, by omega⟩ : V) :=
  congrArg _ (congrArg b (Fin.ext hi))

/-- The dual basis vector at a node known only through its value `n - 2`, the polar-dual
counterpart of `basis_coe_of_val_eq_penultimate`. -/
private theorem dualVector_coe_of_val_eq_penultimate {i : Fin n} (hi : (i : ℕ) = n - 2) :
    (P.dualVector b i : V) = (P.dualVector b ⟨n - 2, by omega⟩ : V) :=
  congrArg _ (congrArg (P.dualVector b) (Fin.ext hi))

/-- **The graph generator exchanges the two fork raising operators** and commutes with the others:
multiplying the positive type-`D` representative at a node by the Clifford generator of the graph
vector renumbers that representative by `TauCeti.graphPermD`. -/
theorem ι_typeDGraphVector_mul_typeDSimpleRootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleRootBivector b hn i =
      P.typeDSimpleRootBivector b hn (graphPermD n hn i) * ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleRootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (penultimate_add_one_lt hn) (last_eq_penultimate_add_one hn)]
    exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
      (ι_mul_ι_comm_of_isOrtho
        (P.isOrtho_typeDGraphVector_basis_of_ne b hn (penultimate_ne_last hn)))
      (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (last_eq_val_add_one hn hpen),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleRootBivector_of_fork b hn (not_last_add_one_lt hn),
        P.basis_coe_of_val_eq_penultimate b hpen]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_basis_of_ne b hn (penultimate_ne_last hn)))
        (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_basis_of_ne b hn hfork))
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (val_add_one_ne_last hn hpen)))

/-- **The graph generator exchanges the two fork lowering operators** and commutes with the
others. -/
theorem ι_typeDGraphVector_mul_typeDSimpleNegativeRootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleNegativeRootBivector b hn i =
      P.typeDSimpleNegativeRootBivector b hn (graphPermD n hn i) *
        ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleNegativeRootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (penultimate_add_one_lt hn) (last_eq_penultimate_add_one hn)]
    exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
      (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)
      (ι_mul_ι_comm_of_isOrtho
        (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (penultimate_ne_last hn)))
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (last_eq_val_add_one hn hpen),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleNegativeRootBivector_of_fork b hn (not_last_add_one_lt hn),
        P.dualVector_coe_of_val_eq_penultimate b hpen]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (penultimate_ne_last hn)))
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_basis_of_ne b hn (val_add_one_ne_last hn hpen)))
        (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn hfork))

/-- **The graph generator exchanges the two fork coroots** and commutes with the others. The two
fork coroots differ by the reversal of the occupation product at the last node, which is what
turns the difference of the last two occupation products into their sum less `1`. -/
theorem ι_typeDGraphVector_mul_typeDSimpleCorootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleCorootBivector b hn i =
      P.typeDSimpleCorootBivector b hn (graphPermD n hn i) * ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleCorootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (penultimate_add_one_lt hn) (last_eq_penultimate_add_one hn),
      mul_sub, mul_one, mul_add,
      P.ι_typeDGraphVector_mul_occupation_of_ne b hn (penultimate_ne_last hn),
      P.ι_typeDGraphVector_mul_occupation_last b hn]
    noncomm_ring
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (last_eq_val_add_one hn hpen),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleCorootBivector_of_fork b hn (not_last_add_one_lt hn),
        P.basis_coe_of_val_eq_penultimate b hpen,
        P.dualVector_coe_of_val_eq_penultimate b hpen, mul_sub,
        P.ι_typeDGraphVector_mul_occupation_of_ne b hn (penultimate_ne_last hn),
        P.ι_typeDGraphVector_mul_occupation_last b hn]
      noncomm_ring
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        mul_sub, P.ι_typeDGraphVector_mul_occupation_of_ne b hn hfork,
        P.ι_typeDGraphVector_mul_occupation_of_ne b hn (val_add_one_ne_last hn hpen)]
      noncomm_ring

/-! ## The graph operator on the spinor module -/

/-- **The graph operator of the type-`D` spinor module**: the spin action of the Clifford
generator of the graph vector, that is creation at the last coordinate minus annihilation at it.
It squares to `-1`, hence is a linear equivalence with `-` itself as inverse. -/
noncomputable def typeDGraphOperator (hn : 2 ≤ n) :
    ExteriorAlgebra K P.W ≃ₗ[K] ExteriorAlgebra K P.W :=
  LinearEquiv.ofLinearMap (spinAction Q P (ι Q (P.typeDGraphVector b hn)))
    (-spinAction Q P (ι Q (P.typeDGraphVector b hn)))
    (by
      rw [LinearMap.comp_neg, ← Module.End.mul_eq_comp, ← map_mul]
      simp [Module.End.one_eq_id])
    (by
      rw [LinearMap.neg_comp, ← Module.End.mul_eq_comp, ← map_mul]
      simp [Module.End.one_eq_id])

/-- The graph operator acts by the spin action of the graph generator. -/
-- Not `@[simp]`: the spin action of the graph generator is the implementation, and the equations
-- below are the intended normal forms.
theorem typeDGraphOperator_apply (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn x = spinAction Q P (ι Q (P.typeDGraphVector b hn)) x :=
  -- `(rfl)`, not `rfl`: the body of `typeDGraphOperator` is not `@[expose]`d.
  (rfl)

/-- **The graph operator is creation at the last coordinate minus annihilation at it.** This is
the Fock-model description of the spin action of the graph generator. -/
-- Not `@[simp]`: unfolding the operator into the Fock model takes `typeDGraphOperator_apply_apply`
-- and `typeDGraphOperator_symm_apply`, which are the intended normal forms, out of simp normal
-- form.
theorem typeDGraphOperator_eq_wedge_sub_contract (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn x =
      P.wedge (b ⟨n - 1, by omega⟩) x - P.contract (P.dualVector b ⟨n - 1, by omega⟩) x := by
  rw [typeDGraphOperator_apply, typeDGraphVector_def, map_sub, map_sub, LinearMap.sub_apply,
    spinAction_ι, spinAction_ι, P.cliffordOperator_coe_W, P.cliffordOperator_coe_W']

/-! ### The graph operator on the exterior basis -/

/-- **The graph operator creates the final coordinate in an exterior basis vector that lacks
it**, with the shuffle sign that moves that coordinate to the front. Only the creation half of the
operator contributes, the annihilation half killing a basis vector whose index set misses the
coordinate it annihilates. -/
theorem typeDGraphOperator_basis_of_notMem (hn : 2 ≤ n) {s : Finset (Fin n)}
    (hs : (⟨n - 1, by omega⟩ : Fin n) ∉ s) :
    P.typeDGraphOperator b hn (b.ExteriorAlgebra s) =
      (TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
          (insert (⟨n - 1, by omega⟩ : Fin n) s) : ℤ) •
        b.ExteriorAlgebra (insert (⟨n - 1, by omega⟩ : Fin n) s) := by
  rw [typeDGraphOperator_eq_wedge_sub_contract, P.wedge_apply, P.contract_apply,
    pairingEquiv_dualVector, TauCeti.ExteriorAlgebra.ι_mul_basis,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_right hs, ite_eq_right hs, sub_zero,
    Units.smul_def]

/-- **The graph operator annihilates the final coordinate of an exterior basis vector that
carries it**, with the shuffle sign that moves that coordinate to the front and the minus sign of
the graph vector's second summand. Only the annihilation half of the operator contributes, a
repeated generator squaring to zero. -/
theorem typeDGraphOperator_basis_of_mem (hn : 2 ≤ n) {s : Finset (Fin n)}
    (hs : (⟨n - 1, by omega⟩ : Fin n) ∈ s) :
    P.typeDGraphOperator b hn (b.ExteriorAlgebra s) =
      (-(TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n) s : ℤ)) •
        b.ExteriorAlgebra (s.erase (⟨n - 1, by omega⟩ : Fin n)) := by
  rw [typeDGraphOperator_eq_wedge_sub_contract, P.wedge_apply, P.contract_apply,
    pairingEquiv_dualVector, TauCeti.ExteriorAlgebra.ι_mul_basis,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hs, ite_eq_left hs, zero_sub,
    Units.smul_def, neg_smul]

/-- The graph operator squares to `-1`. -/
@[simp]
theorem typeDGraphOperator_apply_apply (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (P.typeDGraphOperator b hn x) = -x := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply, ← map_mul]
  simp

/-- The inverse of the graph operator is its negative. -/
@[simp]
theorem typeDGraphOperator_symm_apply (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    (P.typeDGraphOperator b hn).symm x = -P.typeDGraphOperator b hn x :=
  (P.typeDGraphOperator b hn).symm_apply_eq.2 (by
    rw [map_neg, typeDGraphOperator_apply_apply, neg_neg])

/-- **The graph operator intertwines the numbered raising operators along `TauCeti.graphPermD`.**
-/
theorem typeDGraphOperator_spinAction_typeDSimpleRootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleRootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleRootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleRootBivector b hn i]

/-- **The graph operator intertwines the numbered lowering operators along `TauCeti.graphPermD`.**
-/
theorem typeDGraphOperator_spinAction_typeDSimpleNegativeRootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleNegativeRootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleNegativeRootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleNegativeRootBivector b hn i]

/-- **The graph operator intertwines the numbered coroots along `TauCeti.graphPermD`.** -/
theorem typeDGraphOperator_spinAction_typeDSimpleCorootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleCorootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleCorootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleCorootBivector b hn i]

/-! ### The graph operator exchanges the two half-spin summands -/

/-- **The graph operator carries the even half-spin summand onto the odd one.** -/
theorem map_typeDGraphOperator_spinPlus (hn : 2 ≤ n) (hline : P.line = ⊥) :
    (spinPlus Q P).map (P.typeDGraphOperator b hn : ExteriorAlgebra K P.W →ₗ[K] _) =
      spinMinus Q P := by
  have hT : (P.typeDGraphOperator b hn : ExteriorAlgebra K P.W →ₗ[K] _) =
      spinAction Q P (ι Q (P.typeDGraphVector b hn)) :=
    LinearMap.ext (P.typeDGraphOperator_apply b hn)
  have hodd := ι_mem_evenOdd_one Q (P.typeDGraphVector b hn)
  refine le_antisymm (hT ▸ map_spinAction_spinPlus_le_spinMinus P hline hodd) fun t ht => ?_
  refine ⟨-P.typeDGraphOperator b hn t, ?_, by simp⟩
  refine neg_mem (map_spinAction_spinMinus_le_spinPlus P hline hodd ⟨t, ht, ?_⟩)
  exact (P.typeDGraphOperator_apply b hn t).symm

/-- **The fork exchange of the half-spin summands**: the graph operator, restricted to a linear
equivalence from the even half-spin summand `S⁺` onto the odd one `S⁻`. It intertwines the
half-spin representations along the fork exchange `typeDGraphLieEquiv` of the split type-`D`
Lie algebra (`typeDGraphHalfSpinEquiv_typeDSpinPlusLieRep`). -/
noncomputable def typeDGraphHalfSpinEquiv (hn : 2 ≤ n) (hline : P.line = ⊥) :
    spinPlus Q P ≃ₗ[K] spinMinus Q P :=
  (P.typeDGraphOperator b hn).ofSubmodules _ _ (P.map_typeDGraphOperator_spinPlus b hn hline)

/-- The fork exchange of the half-spin summands is the graph operator. -/
@[simp]
theorem coe_typeDGraphHalfSpinEquiv_apply (hn : 2 ≤ n) (hline : P.line = ⊥)
    (s : spinPlus Q P) :
    (P.typeDGraphHalfSpinEquiv b hn hline s : ExteriorAlgebra K P.W) =
      P.typeDGraphOperator b hn s :=
  LinearEquiv.ofSubmodules_apply _ _ _

/-- The inverse of the fork exchange of the half-spin summands is minus the graph operator. -/
@[simp]
theorem coe_typeDGraphHalfSpinEquiv_symm_apply (hn : 2 ≤ n) (hline : P.line = ⊥)
    (t : spinMinus Q P) :
    ((P.typeDGraphHalfSpinEquiv b hn hline).symm t : ExteriorAlgebra K P.W) =
      -P.typeDGraphOperator b hn t := by
  rw [typeDGraphHalfSpinEquiv, LinearEquiv.ofSubmodules_symm_apply, typeDGraphOperator_symm_apply]

end CommRing

/-! ## Integrality and the rational Serre representation -/

section Rat

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)

/-- The graph generator acts integrally on the spinor lattice: it is the difference of a creation
and an annihilation operator, and both are integral. -/
theorem ι_typeDGraphVector_mem_integralSpinActionSubring (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) ∈ P.integralSpinActionSubring b := by
  rw [typeDGraphVector_def, map_sub]
  exact sub_mem (P.ι_basis_mem_integralSpinActionSubring b _)
    (P.ι_dualVector_mem_integralSpinActionSubring b _)

/-- The graph operator preserves the coordinate integral lattice in the spinor module. -/
theorem typeDGraphOperator_mem_integralLattice (hn : 2 ≤ n) {x : ExteriorAlgebra ℚ P.W}
    (hx : x ∈ TauCeti.ExteriorAlgebra.integralLattice b) :
    P.typeDGraphOperator b hn x ∈ TauCeti.ExteriorAlgebra.integralLattice b := by
  rw [typeDGraphOperator_apply]
  exact (P.mem_integralSpinActionSubring b).mp
    (P.ι_typeDGraphVector_mem_integralSpinActionSubring b hn) hx

/-- **The graph operator preserves the spinor lattice in both directions**, since its square is
`-1` and the lattice is a subgroup. This is the lattice-invariance datum that the numbered-symmetry
construction of a Chevalley--Demazure carrier consumes. -/
-- Not `@[simp]`: `TauCeti.ExteriorAlgebra.mem_integralLattice_iff` is, and rewrites the membership
-- into its coordinate form, so this left-hand side is not in simp normal form.
theorem typeDGraphOperator_mem_integralLattice_iff (hn : 2 ≤ n) {x : ExteriorAlgebra ℚ P.W} :
    P.typeDGraphOperator b hn x ∈ TauCeti.ExteriorAlgebra.integralLattice b ↔
      x ∈ TauCeti.ExteriorAlgebra.integralLattice b := by
  refine ⟨fun hx => ?_, P.typeDGraphOperator_mem_integralLattice b hn⟩
  have hsq := P.typeDGraphOperator_mem_integralLattice b hn hx
  rw [typeDGraphOperator_apply_apply] at hsq
  exact neg_mem_iff.mp hsq

/-- The graph operator intertwines the represented positive Serre generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreE (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreE ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreE ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreE b hn, P.typeDSpinSerreRepresentation_serreE b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleRootBivector b (by omega) i x

/-- The graph operator intertwines the represented negative Serre generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreF (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreF ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreF ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreF b hn, P.typeDSpinSerreRepresentation_serreF b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleNegativeRootBivector b (by omega) i x

/-- The graph operator intertwines the represented Cartan generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreH (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreH ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreH ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreH b hn, P.typeDSpinSerreRepresentation_serreH b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleCorootBivector b (by omega) i x

/-- **The intertwining datum of the type-`D` fork symmetry.** The graph operator carries the
action of the numbered root generator at `k` to the action of the one at the image of `k` under
the fork exchange, on both the raising and the lowering half of the numbering. Together with
`TauCeti.SpinPolarizationData.typeDGraphOperator_mem_integralLattice_iff` this is exactly the
symmetry datum a numbered Kostant carrier consumes. -/
theorem typeDGraphOperator_typeDSpinRep_rootGenerator (hn : 4 ≤ n) (k : Fin n ⊕ Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) k)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n)
            (Sum.map (graphPermD n (by omega)) (graphPermD n (by omega)) k)))
        (P.typeDGraphOperator b (by omega) x) := by
  cases k with
  | inl i =>
      rw [Sum.map_inl, TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inl]
      exact P.typeDGraphOperator_typeDSpinRep_serreE b hn i x
  | inr i =>
      rw [Sum.map_inr, TauCeti.serreRootGenerator_inr, TauCeti.serreRootGenerator_inr]
      exact P.typeDGraphOperator_typeDSpinRep_serreF b hn i x

end Rat

/-! ## The fork exchange on the whole split Lie algebra -/

section Field

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
variable {n : ℕ} (b : Module.Basis (Fin n) K P.W)

/-- The reflection in the graph vector, as a quadratic isometry. Its norm `-1` is invertible, so
this is `TauCeti.QuadraticMap.reflection`, which sends `x` to `x + polar Q v x • v`. -/
private noncomputable def typeDGraphIsometry (hn : 2 ≤ n) : Q →qᵢ Q :=
  letI : Invertible (Q (P.typeDGraphVector b hn)) :=
    invertibleOfNonzero (by simp)
  { (TauCeti.QuadraticMap.reflection Q (P.typeDGraphVector b hn)).toLinearMap with
    map_app' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q _) }

private theorem typeDGraphIsometry_apply (hn : 2 ≤ n) (x : V) :
    P.typeDGraphIsometry b hn x =
      x + polar Q (P.typeDGraphVector b hn) x • P.typeDGraphVector b hn := by
  let _ : Invertible (Q (P.typeDGraphVector b hn)) :=
    invertibleOfNonzero (by simp)
  have hinv : ⅟(Q (P.typeDGraphVector b hn)) = -1 :=
    invOf_eq_right_inv (by rw [quadraticForm_typeDGraphVector]; norm_num)
  -- The isometry is the reflection, whose coefficient is `⅟(Q v) = -1`.
  change TauCeti.QuadraticMap.reflection Q (P.typeDGraphVector b hn) x = _
  rw [TauCeti.QuadraticMap.reflection_apply, hinv]
  module

/-- The reflection in the graph vector is an involution. -/
private theorem typeDGraphIsometry_apply_apply (hn : 2 ≤ n) (x : V) :
    P.typeDGraphIsometry b hn (P.typeDGraphIsometry b hn x) = x :=
  letI : Invertible (Q (P.typeDGraphVector b hn)) :=
    invertibleOfNonzero (by simp)
  LinearEquiv.congr_fun (TauCeti.QuadraticMap.reflection_mul_self Q _) x

/-- In the hyperbolic basis, the reflection in the graph vector is the swap matrix of the last
hyperbolic pair. -/
private theorem toLinAlgEquiv_typeDGraphMatrix (hn : 2 ≤ n) (hline : P.line = ⊥) :
    Matrix.toLinAlgEquiv (P.typeDBasis b hline)
        (typeDGraphMatrix (⟨n - 1, by omega⟩ : Fin n) K) =
      (P.typeDGraphIsometry b hn).toLinearMap := by
  apply (P.typeDBasis b hline).ext
  intro s
  rw [Matrix.toLinAlgEquiv_self, QuadraticMap.Isometry.coe_toLinearMap, typeDGraphIsometry_apply]
  simp only [typeDGraphMatrix_apply, ite_smul, one_smul, zero_smul,
    ← Equiv.eq_symm_apply, typeDGraphIndex_symm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Only the last hyperbolic pair moves; every other basis vector is orthogonal to `v`.
  rcases s with j | j <;> by_cases hj : j = ⟨n - 1, by omega⟩
  · subst hj
    rw [typeDGraphIndex_inl_self, typeDBasis_inr, typeDBasis_inl,
      polar_typeDGraphVector_basis_last, typeDGraphVector_def]
    module
  · have hj' : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
    rw [typeDGraphIndex_inl_of_ne _ hj, typeDBasis_inl,
      (P.isOrtho_typeDGraphVector_basis_of_ne b hn hj').polar_eq_zero, zero_smul, add_zero]
  · subst hj
    rw [typeDGraphIndex_inr_self, typeDBasis_inr, typeDBasis_inl,
      polar_typeDGraphVector_dualVector_last, typeDGraphVector_def]
    module
  · have hj' : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
    rw [typeDGraphIndex_inr_of_ne _ hj, typeDBasis_inr,
      (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn hj').polar_eq_zero, zero_smul, add_zero]

variable [Invertible (2 : K)]

/-- **Conjugation by the graph generator realizes the fork exchange on the whole split type-`D`
Lie algebra.** Moving the Clifford generator of the graph vector past the quadratic element of a
matrix `A` replaces it by the quadratic element of `typeDGraphLieEquiv A`, the conjugate of `A` by
the swap of the last hyperbolic pair. -/
theorem ι_typeDGraphVector_mul_typeDQuadraticEquiv (hn : 2 ≤ n) (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) :
    ι Q (P.typeDGraphVector b hn) * (P.typeDQuadraticEquiv b hline A : CliffordAlgebra Q) =
      (P.typeDQuadraticEquiv b hline
          (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K A) : CliffordAlgebra Q) *
        ι Q (P.typeDGraphVector b hn) := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  have hq := (P.typeDQuadraticEquiv b hline A).property
  rw [mul_eq_map_involute_mul_of_forall_ι (P.typeDGraphIsometry b hn) (fun x => by
      rw [typeDGraphIsometry_apply]; exact P.ι_typeDGraphVector_mul_ι b hn x),
    involute_eq_of_mem_even (quadraticLieSubalgebra_le_evenOdd_zero Q hq)]
  congr 1
  -- Both sides are quadratic, so it suffices to compare their commutators with generators.
  refine congrArg Subtype.val (quadraticLieSubalgebra_ext Q (P.nondegenerate_of_line_eq_bot hline)
    (a := ⟨_, map_mem_quadraticLieSubalgebra _ hq⟩) fun x => ?_)
  rw [P.typeDQuadraticEquiv_lie_ι b hline, typeDGraphLieEquiv_apply_val, map_mul, map_mul,
    P.toLinAlgEquiv_typeDGraphMatrix b hn hline, Module.End.mul_apply, Module.End.mul_apply,
    QuadraticMap.Isometry.coe_toLinearMap]
  conv_lhs => rw [← P.typeDGraphIsometry_apply_apply b hn x, ← map_apply_ι]
  rw [Subtype.coe_mk, Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, ← Ring.lie_def,
    P.typeDQuadraticEquiv_lie_ι b hline, map_apply_ι]

/-- **The graph operator intertwines the spin representation with its fork twist.** For every
matrix `A` of the split type-`D` Lie algebra, the graph operator carries the action of `A` to the
action of `typeDGraphLieEquiv A`, so the spin representation twisted by the fork exchange is
isomorphic to itself through the graph operator. -/
theorem typeDGraphOperator_typeDSpinLieRep (hn : 2 ≤ n) (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) (s : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (P.typeDSpinLieRep b hline A s) =
      P.typeDSpinLieRep b hline (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K A)
        (P.typeDGraphOperator b hn s) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, typeDSpinLieRep_apply,
    typeDSpinLieRep_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDQuadraticEquiv b hn hline]

/-- **The fork exchange intertwines the two half-spin representations.** The graph operator
carries the action of `A` on `S⁺` to the action of `typeDGraphLieEquiv A` on `S⁻`. -/
theorem typeDGraphHalfSpinEquiv_typeDSpinPlusLieRep (hn : 2 ≤ n) (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) (s : spinPlus Q P) :
    P.typeDGraphHalfSpinEquiv b hn hline (P.typeDSpinPlusLieRep b hline A s) =
      P.typeDSpinMinusLieRep b hline (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K A)
        (P.typeDGraphHalfSpinEquiv b hn hline s) := by
  apply Subtype.ext
  rw [coe_typeDGraphHalfSpinEquiv_apply, coe_typeDSpinPlusLieRep_apply,
    coe_typeDSpinMinusLieRep_apply, coe_typeDGraphHalfSpinEquiv_apply]
  exact P.typeDGraphOperator_typeDSpinLieRep b hn hline A s

/-- The inverse fork exchange carries the action of `A` on `S⁻` to the action of
`typeDGraphLieEquiv A` on `S⁺`. -/
theorem typeDGraphHalfSpinEquiv_symm_typeDSpinMinusLieRep (hn : 2 ≤ n) (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) (t : spinMinus Q P) :
    (P.typeDGraphHalfSpinEquiv b hn hline).symm (P.typeDSpinMinusLieRep b hline A t) =
      P.typeDSpinPlusLieRep b hline (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K A)
        ((P.typeDGraphHalfSpinEquiv b hn hline).symm t) := by
  apply (P.typeDGraphHalfSpinEquiv b hn hline).injective
  rw [LinearEquiv.apply_symm_apply, typeDGraphHalfSpinEquiv_typeDSpinPlusLieRep,
    typeDGraphLieEquiv_typeDGraphLieEquiv, LinearEquiv.apply_symm_apply]

/-- **The odd half-spin module is the fork twist of the even one.** Make `S⁺` a module over the
split type-`D` Lie algebra through the half-spin action precomposed with the fork exchange
`typeDGraphLieEquiv`, and `S⁻` through its own half-spin action. Then the graph operator is an
equivalence of Lie modules between them. -/
noncomputable def typeDGraphHalfSpinLieModuleEquiv (hn : 2 ≤ n) (hline : P.line = ⊥) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ ((P.typeDSpinPlusLieRep b hline).comp
        (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K).toLieHom)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ ((P.typeDSpinPlusLieRep b hline).comp
        (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K).toLieHom)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    spinPlus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD (Fin n) K⁆ spinMinus Q P :=
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ ((P.typeDSpinPlusLieRep b hline).comp
      (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K).toLieHom)
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  { P.typeDGraphHalfSpinEquiv b hn hline with
    map_lie' := fun {A s} => by
      simp only [LieRingModule.compLieHom_apply, LieHom.coe_comp, Function.comp_apply,
        LieEquiv.coe_toLieHom, Module.End.lie_apply, AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
      rw [typeDGraphHalfSpinEquiv_typeDSpinPlusLieRep, typeDGraphLieEquiv_typeDGraphLieEquiv] }

/-- The Lie module form of the fork exchange is the linear fork exchange of the half-spin
summands. -/
@[simp]
theorem typeDGraphHalfSpinLieModuleEquiv_apply (hn : 2 ≤ n) (hline : P.line = ⊥)
    (s : spinPlus Q P) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ ((P.typeDSpinPlusLieRep b hline).comp
        (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K).toLieHom)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ ((P.typeDSpinPlusLieRep b hline).comp
        (typeDGraphLieEquiv (⟨n - 1, by omega⟩ : Fin n) K).toLieHom)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    P.typeDGraphHalfSpinLieModuleEquiv b hn hline s = P.typeDGraphHalfSpinEquiv b hn hline s :=
  (rfl)

end Field

end TauCeti.SpinPolarizationData

