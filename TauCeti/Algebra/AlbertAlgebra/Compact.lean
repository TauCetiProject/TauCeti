/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import TauCeti.Algebra.CayleyDickson.Quaternion

import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# The compact Albert algebra

The **compact Albert algebra** is the Jordan algebra `H₃(𝕆)` of `3 × 3` Hermitian matrices over the
real division octonions `TauCeti.DivisionOctonionReal`,

`⟦d, x⟧ = [[d 0, x 2, star (x 1)], [star (x 2), d 1, x 0], [x 1, star (x 0), d 2]]`,

under the symmetrized product `A ∘ B = ½ (A B + B A)`. It is the exceptional **formally real**
Jordan algebra, the one whose derivation algebra is the compact real form of `F₄`, and it is a
different real form from the split Albert algebra `TauCeti.AlbertAlgebra ℝ` built on the split
octonions.

The construction makes sense over any commutative ring `R` in which `2` is invertible, with the
octonions replaced by the Cayley–Dickson double `CayleyDickson ℍ[R]` of Hamilton's quaternions over
`R`, and it is carried out at that generality as `TauCeti.CompactAlbertAlgebra R`; the compact
Albert algebra is `CompactAlbertAlgebra ℝ`. A Hermitian matrix is recorded by its scalar diagonal
`d : Fin 3 → R` and its three octonion entries `x : Fin 3 → CayleyDickson ℍ[R]`, the entry `x i`
sitting in position `(i + 1, i + 2)`, in the same positions as for `TauCeti.AlbertAlgebra`.

Carrying out `½ (A B + B A)` on that data, every octonion product taken with its two factors
parenthesized, gives the diagonal entries
`d i * e i + ½ (T (x (i + 1) * star (y (i + 1))) + T (x (i + 2) * star (y (i + 2))))`, where `T`
is the octonion trace `TauCeti.CayleyDickson.trace`, and the entries
`½ ((d (i + 1) + d (i + 2)) • y i + (e (i + 1) + e (i + 2)) • x i
  + star (x (i + 1) * y (i + 2) + y (i + 1) * x (i + 2)))`. That expression *is* the definition
below. The product is commutative, `R`-bilinear and unital, and the three diagonal idempotents form
a complete orthogonal frame with the Peirce relations of a Jordan frame. The trace form
`T(A ∘ B)` is associative. The Jordan identity `(A ∘ B) ∘ A² = A ∘ (B ∘ A²)` itself is not proved in
this file.

Over a linearly ordered ring the trace form is positive definite, since
`T(A ∘ A) = ∑ dᵢ² + 2 ∑ N(xᵢ)` with `N` the positive definite octonion norm. Consequently a sum of
squares vanishes only when every term does: `CompactAlbertAlgebra R` is formally real, in the sense
of Mathlib's `IsFormallyReal`. Over `ℝ` this is what distinguishes it from the split Albert algebra,
in which the norm of an octonion can vanish.

## Main definitions

* `TauCeti.CompactAlbertAlgebra`: the Albert algebra of `3 × 3` Hermitian matrices over
  `CayleyDickson ℍ[R]`, with its `NonAssocCommRing` and `Module R` structure and the
  `SMulCommClass` and `IsScalarTower` instances that say the product is `R`-bilinear.
* `TauCeti.CompactAlbertAlgebra.trace`: the trace `d 0 + d 1 + d 2`, an `R`-linear functional.
* `TauCeti.CompactAlbertAlgebra.traceZero`: the trace-zero subspace, the kernel of the trace.
* `TauCeti.CompactAlbertAlgebra.diagIdempotent`: the three diagonal idempotents `E₀`, `E₁`, `E₂`.
* `TauCeti.CompactAlbertAlgebra.offDiagSingle`: the three off-diagonal slots `Fⱼ(a)`, the Hermitian
  matrix whose only nonzero entries are the octonion `a` in position `(j + 1, j + 2)` and its
  conjugate `star a` in position `(j + 2, j + 1)`.

## Main results

* `TauCeti.CompactAlbertAlgebra.finrank_eq_twentySeven` and
  `TauCeti.CompactAlbertAlgebra.finrank_traceZero`: the algebra is `27`-dimensional and its
  trace-zero subspace `26`-dimensional.
* `TauCeti.CompactAlbertAlgebra.mul_self_diag` and `TauCeti.CompactAlbertAlgebra.mul_self_offDiag`:
  the entries of the Jordan square.
* `TauCeti.CompactAlbertAlgebra.trace_mul` and `TauCeti.CompactAlbertAlgebra.trace_mul_assoc`: the
  trace form in coordinates, and its associativity `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`.
* `TauCeti.CompactAlbertAlgebra.trace_mul_self`, `TauCeti.CompactAlbertAlgebra.trace_mul_self_pos`
  and `TauCeti.CompactAlbertAlgebra.trace_mul_self_eq_zero_iff`: **the trace form is positive
  definite** over a linearly ordered ring.
* the `IsFormallyReal (CompactAlbertAlgebra R)` instance: **a sum of squares vanishes only if each
  term does**.
* `TauCeti.CompactAlbertAlgebra.diagIdempotent_mul_diagIdempotent` and
  `TauCeti.CompactAlbertAlgebra.sum_diagIdempotent`: the diagonal idempotents are orthogonal and sum
  to `1`.
* `TauCeti.CompactAlbertAlgebra.diagIdempotent_mul_offDiagSingle`,
  `TauCeti.CompactAlbertAlgebra.offDiagSingle_mul_offDiagSingle` and
  `TauCeti.CompactAlbertAlgebra.offDiagSingle_mul_offDiagSingle_add_one`: the **Peirce relations**
  of the frame with the off-diagonal slots, and the products of the slots.
* `TauCeti.CompactAlbertAlgebra.eq_sum_smul_diagIdempotent_add_sum_offDiagSingle`: the frame and
  the slots span the algebra.

## Implementation notes

The additive and module structures are transported along
`TauCeti.CompactAlbertAlgebra.addEquivProd`, which packages a Hermitian matrix as the pair of its
diagonal and its octonion entries. The multiplication is read through the projection `simp` lemmas
`TauCeti.CompactAlbertAlgebra.mul_diag` and `TauCeti.CompactAlbertAlgebra.mul_offDiag`.

The octonion entries live in `CayleyDickson ℍ[R]` rather than in the split
`TauCeti.Octonion R` of `TauCeti.AlbertAlgebra`, so the diagonal of a product is written with the
octonion trace `T (x * star y)`, twice the symmetric bilinear form of the norm, rather than through
a quadratic-form API.

## References

* P. Jordan, J. von Neumann and E. Wigner, *On an algebraic generalization of the quantum
  mechanical formalism*, Ann. of Math. **35** (1934), 29–64: the formally real Jordan algebras, and
  `H₃(𝕆)` as the exceptional one.
* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §3.4: the coordinate
  form of the product.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), §5.3: Hermitian matrices over a composition algebra and their Peirce
  decomposition.
-/

public section

open scoped Quaternion

namespace TauCeti

/-- The **compact Albert algebra** over `R`: a `3 × 3` Hermitian matrix over the Cayley–Dickson
double `CayleyDickson ℍ[R]` of the quaternions, recorded as its scalar diagonal together with its
three octonion entries. Over `ℝ` the octonions are the division octonions
`TauCeti.DivisionOctonionReal`, and `CompactAlbertAlgebra ℝ` is the formally real Albert algebra. -/
@[ext]
structure CompactAlbertAlgebra (R : Type*) [Zero R] [One R] [Neg R] where
  /-- The scalar diagonal of the Hermitian matrix. -/
  diag : Fin 3 → R
  /-- The octonion entries: `offDiag i` is the entry in position `(i + 1, i + 2)`, and the entry in
  position `(i + 2, i + 1)` is its conjugate. -/
  offDiag : Fin 3 → CayleyDickson ℍ[R]

namespace CompactAlbertAlgebra

variable {R S : Type*} [CommRing R]

/-! ### The additive and module structure -/

instance : Zero (CompactAlbertAlgebra R) := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_diag : (0 : CompactAlbertAlgebra R).diag = 0 := (rfl)
@[simp] theorem zero_offDiag : (0 : CompactAlbertAlgebra R).offDiag = 0 := (rfl)

instance : Inhabited (CompactAlbertAlgebra R) := ⟨0⟩

instance : One (CompactAlbertAlgebra R) := ⟨⟨1, 0⟩⟩

@[simp] theorem one_diag : (1 : CompactAlbertAlgebra R).diag = 1 := (rfl)
@[simp] theorem one_offDiag : (1 : CompactAlbertAlgebra R).offDiag = 0 := (rfl)

instance : Add (CompactAlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag + B.diag, A.offDiag + B.offDiag⟩⟩

@[simp] theorem add_diag (A B : CompactAlbertAlgebra R) : (A + B).diag = A.diag + B.diag := (rfl)
@[simp] theorem add_offDiag (A B : CompactAlbertAlgebra R) :
    (A + B).offDiag = A.offDiag + B.offDiag := (rfl)

instance : Neg (CompactAlbertAlgebra R) := ⟨fun A => ⟨-A.diag, -A.offDiag⟩⟩

@[simp] theorem neg_diag (A : CompactAlbertAlgebra R) : (-A).diag = -A.diag := (rfl)
@[simp] theorem neg_offDiag (A : CompactAlbertAlgebra R) : (-A).offDiag = -A.offDiag := (rfl)

instance : Sub (CompactAlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag - B.diag, A.offDiag - B.offDiag⟩⟩

@[simp] theorem sub_diag (A B : CompactAlbertAlgebra R) : (A - B).diag = A.diag - B.diag := (rfl)
@[simp] theorem sub_offDiag (A B : CompactAlbertAlgebra R) :
    (A - B).offDiag = A.offDiag - B.offDiag := (rfl)

instance [SMul S R] : SMul S (CompactAlbertAlgebra R) :=
  ⟨fun s A => ⟨s • A.diag, s • A.offDiag⟩⟩

@[simp] theorem smul_diag [SMul S R] (s : S) (A : CompactAlbertAlgebra R) :
    (s • A).diag = s • A.diag := (rfl)

@[simp] theorem smul_offDiag [SMul S R] (s : S) (A : CompactAlbertAlgebra R) :
    (s • A).offDiag = s • A.offDiag := (rfl)

variable (R) in
/-- The components of a Hermitian matrix, as an additive isomorphism with the pair of its scalar
diagonal and its octonion entries. The additive and module structures are transported along it, and
`TauCeti.CompactAlbertAlgebra.linearEquivProd` upgrades it to a linear isomorphism. -/
def addEquivProd : CompactAlbertAlgebra R ≃+ (Fin 3 → R) × (Fin 3 → CayleyDickson ℍ[R]) where
  toFun A := (A.diag, A.offDiag)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem addEquivProd_apply (A : CompactAlbertAlgebra R) :
    addEquivProd R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem addEquivProd_symm_apply (p : (Fin 3 → R) × (Fin 3 → CayleyDickson ℍ[R])) :
    (addEquivProd R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance : AddCommGroup (CompactAlbertAlgebra R) := by
  apply (addEquivProd R).injective.addCommGroup <;> intros <;> simp

instance [Semiring S] [Module S R] : Module S (CompactAlbertAlgebra R) :=
  (addEquivProd R).injective.module _ (addEquivProd R).toAddMonoidHom fun _ _ => by simp

instance : AddCommGroupWithOne (CompactAlbertAlgebra R) where
  __ := (inferInstance : AddCommGroup (CompactAlbertAlgebra R))
  one := 1

/-- The components of a Hermitian matrix, as a linear isomorphism with the pair of its scalar
diagonal and its octonion entries, over any semiring acting on the coefficients. -/
def linearEquivProd (S R : Type*) [Semiring S] [CommRing R] [Module S R] :
    CompactAlbertAlgebra R ≃ₗ[S] (Fin 3 → R) × (Fin 3 → CayleyDickson ℍ[R]) :=
  (addEquivProd R).toLinearEquiv fun _ _ => rfl

@[simp] theorem linearEquivProd_apply [Semiring S] [Module S R] (A : CompactAlbertAlgebra R) :
    linearEquivProd S R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem linearEquivProd_symm_apply [Semiring S] [Module S R]
    (p : (Fin 3 → R) × (Fin 3 → CayleyDickson ℍ[R])) :
    (linearEquivProd S R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance : Module.Free R (CompactAlbertAlgebra R) :=
  Module.Free.of_equiv (linearEquivProd R R).symm

instance : Module.Finite R (CompactAlbertAlgebra R) :=
  Module.Finite.equiv (linearEquivProd R R).symm

variable (R) in
/-- **The compact Albert algebra is `27`-dimensional**: three scalars on the diagonal and three
`8`-dimensional octonion entries. -/
theorem finrank_eq_twentySeven [StrongRankCondition R] :
    Module.finrank R (CompactAlbertAlgebra R) = 27 := by
  rw [(linearEquivProd R R).finrank_eq, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_pi_fintype, Finset.sum_const, CayleyDickson.finrank_eq,
    Quaternion.finrank_eq_four]
  simp

/-! ### The symmetrized product -/

section Product

/-- The symmetrized matrix product `A ∘ B = ½ (A B + B A)`, written out on the diagonal and on the
octonion entries of a Hermitian matrix. The octonion trace of `x * star y`, twice the symmetric
bilinear form of the octonion norm, enters on the diagonal, and the conjugate of a symmetrized
octonion product off it. -/
instance [Invertible (2 : R)] : Mul (CompactAlbertAlgebra R) :=
  ⟨fun A B =>
    ⟨fun i => A.diag i * B.diag i
        + ⅟(2 : R) * (CayleyDickson.trace (A.offDiag (i + 1) * star (B.offDiag (i + 1)))
          + CayleyDickson.trace (A.offDiag (i + 2) * star (B.offDiag (i + 2)))),
      fun i =>
        ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
          + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i
          + star (A.offDiag (i + 1) * B.offDiag (i + 2) + B.offDiag (i + 1) * A.offDiag (i + 2)))⟩⟩

variable [Invertible (2 : R)]

@[simp] theorem mul_diag (A B : CompactAlbertAlgebra R) (i : Fin 3) :
    (A * B).diag i = A.diag i * B.diag i
      + ⅟(2 : R) * (CayleyDickson.trace (A.offDiag (i + 1) * star (B.offDiag (i + 1)))
        + CayleyDickson.trace (A.offDiag (i + 2) * star (B.offDiag (i + 2)))) :=
  (rfl)

@[simp] theorem mul_offDiag (A B : CompactAlbertAlgebra R) (i : Fin 3) :
    (A * B).offDiag i =
      ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
        + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i
        + star (A.offDiag (i + 1) * B.offDiag (i + 2) + B.offDiag (i + 1) * A.offDiag (i + 2))) :=
  (rfl)

/-- **The diagonal of the Jordan square**: `(A ∘ A)ᵢᵢ = aᵢ² + N(xᵢ₊₁) + N(xᵢ₊₂)`. -/
theorem mul_self_diag (A : CompactAlbertAlgebra R) (i : Fin 3) :
    (A * A).diag i = A.diag i ^ 2 + CayleyDickson.normSq (A.offDiag (i + 1))
      + CayleyDickson.normSq (A.offDiag (i + 2)) := by
  rw [mul_diag, CayleyDickson.trace_mul_star_self, CayleyDickson.trace_mul_star_self, sq,
    ← mul_add, ← mul_assoc, invOf_mul_self, one_mul, add_assoc]

/-- **The off-diagonal entries of the Jordan square**:
`(A ∘ A)ᵢ = (aᵢ₊₁ + aᵢ₊₂) xᵢ + star (xᵢ₊₁ xᵢ₊₂)`. -/
theorem mul_self_offDiag (A : CompactAlbertAlgebra R) (i : Fin 3) :
    (A * A).offDiag i = (A.diag (i + 1) + A.diag (i + 2)) • A.offDiag i
      + star (A.offDiag (i + 1) * A.offDiag (i + 2)) := by
  simp only [mul_offDiag, star_add, smul_add, invOf_two_smul_add_invOf_two_smul]

instance : NonAssocCommRing (CompactAlbertAlgebra R) where
  __ := (inferInstance : AddCommGroupWithOne (CompactAlbertAlgebra R))
  left_distrib A B C := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add, star_add]
      ring
    · simp [mul_add, add_mul, smul_add, star_add]
      module
  right_distrib A B C := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [add_mul]
      ring
    · simp [mul_add, add_mul, smul_add, star_add]
      module
  zero_mul A := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_zero A := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_comm A B := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [CayleyDickson.trace_mul_star_comm (A.offDiag _), mul_comm]
    · simp only [mul_offDiag]
      rw [add_comm (A.offDiag (i + 1) * B.offDiag (i + 2))]
      congr 1
      abel
  one_mul A := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]
  mul_one A := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]

instance : SMulCommClass R (CompactAlbertAlgebra R) (CompactAlbertAlgebra R) where
  smul_comm r A B := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [CayleyDickson.star_smul, mul_smul_comm, mul_add, mul_left_comm]
    · simp [CayleyDickson.star_smul, mul_smul_comm, smul_mul_assoc, smul_add]
      module

instance : IsScalarTower R (CompactAlbertAlgebra R) (CompactAlbertAlgebra R) where
  smul_assoc r A B := by
    refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [smul_mul_assoc, mul_add, mul_assoc, mul_left_comm]
    · simp [CayleyDickson.star_smul, mul_smul_comm, smul_mul_assoc, smul_add]
      module

end Product

/-! ### The trace -/

section Trace

/-- **The trace** of a Hermitian octonion matrix: the sum of its three scalar diagonal entries. -/
def trace : CompactAlbertAlgebra R →ₗ[R] R where
  toFun A := ∑ i, A.diag i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

@[simp] theorem trace_apply (A : CompactAlbertAlgebra R) : trace A = ∑ i, A.diag i := (rfl)

/-- The trace of the identity matrix is `3`. Not a `simp` lemma, because
`TauCeti.CompactAlbertAlgebra.trace_apply` already takes its left-hand side apart. -/
theorem trace_one : trace (1 : CompactAlbertAlgebra R) = 3 := by
  simp

variable (R) in
/-- **The trace-zero submodule** of the compact Albert algebra, the kernel of the trace. Over a
ring satisfying `StrongRankCondition` it is `26`-dimensional
(`TauCeti.CompactAlbertAlgebra.finrank_traceZero`). -/
def traceZero : Submodule R (CompactAlbertAlgebra R) := LinearMap.ker trace

@[simp] theorem mem_traceZero {A : CompactAlbertAlgebra R} : A ∈ traceZero R ↔ trace A = 0 :=
  LinearMap.mem_ker

/-- The trace-zero matrices are free on the first two diagonal entries and the three octonion
entries: a vanishing trace forces the last diagonal entry. Private: it exists only to transport the
dimension count in `TauCeti.CompactAlbertAlgebra.finrank_traceZero`. -/
private def traceZeroLinearEquivProd :
    traceZero R ≃ₗ[R] (R × R) × (Fin 3 → CayleyDickson ℍ[R]) where
  toFun A := ((A.1.diag 0, A.1.diag 1), A.1.offDiag)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨⟨![p.1.1, p.1.2, -(p.1.1 + p.1.2)], p.2⟩, by simp [Fin.sum_univ_three]⟩
  left_inv A := by
    have h0 : (A : CompactAlbertAlgebra R).diag 0 + (A : CompactAlbertAlgebra R).diag 1
        + (A : CompactAlbertAlgebra R).diag 2 = 0 := by
      simpa [Fin.sum_univ_three] using mem_traceZero.mp A.2
    have h := eq_neg_of_add_eq_zero_right h0
    refine Subtype.ext (CompactAlbertAlgebra.ext (funext fun i => ?_) rfl)
    fin_cases i <;> simp [h]
  right_inv _ := rfl

variable (R) in
/-- **The trace-zero subspace of the compact Albert algebra is `26`-dimensional**: a vanishing
trace pins the last diagonal entry to the negative of the sum of the other two. -/
theorem finrank_traceZero [StrongRankCondition R] :
    Module.finrank R (traceZero R) = 26 := by
  rw [traceZeroLinearEquivProd.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_pi_fintype, Finset.sum_const, CayleyDickson.finrank_eq,
    Quaternion.finrank_eq_four]
  simp

end Trace

/-! ### The trace form -/

section TraceForm

variable [Invertible (2 : R)]

/-- **The trace form** `T(A ∘ B)` is the sum of the products of the diagonal entries and of the
octonion trace pairings `T (xᵢ * star yᵢ)` of the octonion entries. -/
theorem trace_mul (A B : CompactAlbertAlgebra R) :
    trace (A * B) = ∑ i, A.diag i * B.diag i
      + ∑ i, CayleyDickson.trace (A.offDiag i * star (B.offDiag i)) := by
  simp only [trace_apply, mul_diag, Fin.sum_univ_three, Fin.reduceAdd]
  -- Each octonion pairing occurs twice on the diagonal, each time halved.
  linear_combination
    (CayleyDickson.trace (A.offDiag 0 * star (B.offDiag 0))
      + CayleyDickson.trace (A.offDiag 1 * star (B.offDiag 1))
      + CayleyDickson.trace (A.offDiag 2 * star (B.offDiag 2))) *
      (invOf_two_add_invOf_two : (⅟2 : R) + ⅟2 = 1)

/-- **The trace of the Jordan square** is the sum of the squares of the diagonal entries and twice
the norms of the octonion entries. -/
theorem trace_mul_self (A : CompactAlbertAlgebra R) :
    trace (A * A) = ∑ i, A.diag i ^ 2 + 2 * ∑ i, CayleyDickson.normSq (A.offDiag i) := by
  rw [trace_mul]
  simp only [CayleyDickson.trace_mul_star_self, sq, Finset.mul_sum]

/-- **The trace form is associative**: `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`. Together with the
commutativity of the product, `T((A ∘ B) ∘ C)` is a symmetric trilinear form in `A`, `B`, `C`. -/
theorem trace_mul_assoc (A B C : CompactAlbertAlgebra R) :
    trace (A * B * C) = trace (A * (B * C)) := by
  -- In coordinates both sides are the same expression: the scalar terms agree as they stand, and
  -- the octonion triple products agree once each is rotated, by the cyclic invariance of the
  -- octonion trace, to begin with its unique entry in slot `0`.
  rw [trace_mul, trace_mul]
  simp only [mul_diag, mul_offDiag, Fin.sum_univ_three, Fin.reduceAdd, star_add,
    CayleyDickson.star_smul, star_star, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add,
    map_smul, smul_eq_mul, ← star_mul, CayleyDickson.trace_star,
    ← CayleyDickson.trace_mul_assoc,
    CayleyDickson.trace_mul_cycle _ _ (A.offDiag 0),
    CayleyDickson.trace_mul_cycle _ _ (B.offDiag 0),
    CayleyDickson.trace_mul_cycle _ _ (C.offDiag 0),
    fun x y => (CayleyDickson.trace_mul_cycle (A.offDiag 0) y x).symm,
    fun x y => (CayleyDickson.trace_mul_cycle (B.offDiag 0) y x).symm,
    fun x y => (CayleyDickson.trace_mul_cycle (C.offDiag 0) y x).symm]
  ring

end TraceForm

/-! ### Positivity of the trace form and formal reality -/

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Invertible (2 : R)]

/-- The trace form is positive semidefinite: `0 ≤ T(A ∘ A)`. -/
theorem trace_mul_self_nonneg (A : CompactAlbertAlgebra R) : 0 ≤ trace (A * A) := by
  rw [trace_mul_self]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => CayleyDickson.normSq_nonneg))

/-- **The trace form is definite**: `T(A ∘ A) = 0` only for `A = 0`, because the octonion norm
is definite. A pre-order `simp` lemma, so that it fires before
`TauCeti.CompactAlbertAlgebra.trace_apply` expands the trace into coordinates. -/
@[simp↓]
theorem trace_mul_self_eq_zero_iff {A : CompactAlbertAlgebra R} : trace (A * A) = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [trace_mul_self] at h
  obtain ⟨hd, hx⟩ := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => CayleyDickson.normSq_nonneg))).mp h
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hd
  rw [mul_eq_zero, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => CayleyDickson.normSq_nonneg] at hx
  refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
  · simpa using hd i (Finset.mem_univ i)
  · exact CayleyDickson.normSq_eq_zero.mp
      ((hx.resolve_left two_ne_zero) i (Finset.mem_univ i))

/-- **The trace form is positive definite**: `0 < T(A ∘ A)` for `A ≠ 0`. -/
theorem trace_mul_self_pos {A : CompactAlbertAlgebra R} (hA : A ≠ 0) : 0 < trace (A * A) :=
  (trace_mul_self_nonneg A).lt_of_ne fun h => hA (trace_mul_self_eq_zero_iff.mp h.symm)

/-- The trace of a sum of squares is nonnegative. -/
theorem trace_nonneg_of_isSumSq {s : CompactAlbertAlgebra R} (hs : IsSumSq s) : 0 ≤ trace s := by
  induction hs with
  | zero => simp
  | sq_add a _ ih => rw [map_add]; exact add_nonneg (trace_mul_self_nonneg a) ih

/-- **The compact Albert algebra is formally real**: a sum of squares vanishes only when each of
its terms does, because the trace of a square is positive unless the square root vanishes. -/
instance : IsFormallyReal (CompactAlbertAlgebra R) :=
  .of_eq_zero_of_eq_zero_of_mul_self_add fun {_ a} hs h => by
    have h' := congrArg trace h
    rw [map_add, map_zero] at h'
    exact trace_mul_self_eq_zero_iff.mp
      ((add_eq_zero_iff_of_nonneg (trace_mul_self_nonneg a) (trace_nonneg_of_isSumSq hs)).mp h').1

end Ordered

/-! ### The diagonal frame of idempotents -/

variable (R) in
/-- The `i`-th **diagonal idempotent** `Eᵢ`: the Hermitian matrix with a single `1` in
position `(i, i)`. -/
def diagIdempotent (i : Fin 3) : CompactAlbertAlgebra R := ⟨Pi.single i 1, 0⟩

@[simp] theorem diagIdempotent_diag (i : Fin 3) :
    (diagIdempotent R i).diag = Pi.single i 1 := (rfl)
@[simp] theorem diagIdempotent_offDiag (i : Fin 3) :
    (diagIdempotent R i).offDiag = 0 := (rfl)

/-- **The diagonal idempotents are orthogonal**: `Eᵢ ∘ Eⱼ` is `Eᵢ` when `i = j` and `0`
otherwise. -/
@[simp] theorem diagIdempotent_mul_diagIdempotent [Invertible (2 : R)] (i j : Fin 3) :
    diagIdempotent R i * diagIdempotent R j = if i = j then diagIdempotent R i else 0 := by
  rcases eq_or_ne i j with rfl | h
  · refine CompactAlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases eq_or_ne k i with rfl | hk
      · simp
      · simp [hk]
    · simp
  · refine CompactAlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · by_cases hk : k = i <;> simp [Pi.single_apply, hk, h]
    · simp [h]

/-- The diagonal idempotents add up to the identity matrix. -/
@[simp] theorem sum_diagIdempotent : ∑ i, diagIdempotent R i = 1 := by
  apply (addEquivProd R).injective
  simp [map_sum, ← prod_mk_sum, Finset.univ_sum_single]
  rfl

/-- Each diagonal idempotent has trace `1`. -/
theorem trace_diagIdempotent (i : Fin 3) : trace (diagIdempotent R i) = 1 := by
  simp [Pi.single_apply]

/-! ### The off-diagonal slots -/

/-- The Hermitian octonion matrix whose only nonzero entries are the octonion `a`, in position
`(j + 1, j + 2)`, and its conjugate `star a`, in position `(j + 2, j + 1)`: the `j`-th
**off-diagonal slot** `Fⱼ(a)`. It stores `a` as the coordinate `offDiag j`, every other coordinate
being zero. Together with the diagonal frame `TauCeti.CompactAlbertAlgebra.diagIdempotent` these
span the algebra. -/
def offDiagSingle (j : Fin 3) (a : CayleyDickson ℍ[R]) : CompactAlbertAlgebra R :=
  ⟨0, Pi.single j a⟩

@[simp] theorem offDiagSingle_diag (j : Fin 3) (a : CayleyDickson ℍ[R]) :
    (offDiagSingle j a).diag = 0 := (rfl)

@[simp] theorem offDiagSingle_offDiag (j : Fin 3) (a : CayleyDickson ℍ[R]) :
    (offDiagSingle j a).offDiag = Pi.single j a := (rfl)

@[simp] theorem offDiagSingle_zero (j : Fin 3) :
    offDiagSingle j (0 : CayleyDickson ℍ[R]) = 0 :=
  CompactAlbertAlgebra.ext (rfl) (Pi.single_zero j)

@[simp] theorem offDiagSingle_add (j : Fin 3) (a b : CayleyDickson ℍ[R]) :
    offDiagSingle j (a + b) = offDiagSingle j a + offDiagSingle j b :=
  CompactAlbertAlgebra.ext (add_zero (0 : Fin 3 → R)).symm
    (Pi.single_add (f := fun _ : Fin 3 => CayleyDickson ℍ[R]) j a b)

@[simp] theorem offDiagSingle_neg (j : Fin 3) (a : CayleyDickson ℍ[R]) :
    offDiagSingle j (-a) = -offDiagSingle j a :=
  CompactAlbertAlgebra.ext (neg_zero (G := Fin 3 → R)).symm
    (Pi.single_neg (f := fun _ : Fin 3 => CayleyDickson ℍ[R]) j a)

@[simp] theorem offDiagSingle_smul (r : R) (j : Fin 3) (a : CayleyDickson ℍ[R]) :
    offDiagSingle j (r • a) = r • offDiagSingle j a :=
  CompactAlbertAlgebra.ext (smul_zero (A := Fin 3 → R) r).symm
    (Pi.single_smul (f := fun _ : Fin 3 => CayleyDickson ℍ[R]) j r a)

section Peirce

variable [Invertible (2 : R)]

/-- **The Peirce relation between the diagonal frame and the off-diagonal slots**: the `j`-th slot
sits in position `(j + 1, j + 2)`, so `Eⱼ` annihilates it, while the two other idempotents halve
it. -/
@[simp] theorem diagIdempotent_mul_offDiagSingle (i j : Fin 3) (a : CayleyDickson ℍ[R]) :
    diagIdempotent R i * offDiagSingle j a =
      if i = j then 0 else ⅟(2 : R) • offDiagSingle j a := by
  rcases eq_or_ne i j with rfl | h
  · refine CompactAlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_)
    · simp
    · rcases eq_or_ne m i with rfl | hm
      · simp
      · simp [Pi.single_eq_of_ne hm]
  · refine CompactAlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_)
    · simp [h]
    · rcases eq_or_ne m j with rfl | hm
      · rcases eq_add_one_or_eq_add_two_fin_three h with rfl | rfl
        · simp [h]
        · simp [h]
      · simp [h, Pi.single_eq_of_ne hm]

/-- **The product of two octonions in the same off-diagonal slot**: half the octonion trace pairing
`T (a * star b)`, the symmetric bilinear form of the norm, multiplies the sum of the two other
diagonal idempotents. -/
@[simp] theorem offDiagSingle_mul_offDiagSingle (i : Fin 3) (a b : CayleyDickson ℍ[R]) :
    offDiagSingle i a * offDiagSingle i b =
      (⅟(2 : R) * CayleyDickson.trace (a * star b)) •
        (diagIdempotent R (i + 1) + diagIdempotent R (i + 2)) := by
  refine CompactAlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    fin_cases i <;> fin_cases k <;> simp

/-- **The product of two cyclically adjacent off-diagonal slots**: half the remaining slot of
`star (a * b)`. The order of the octonion factors follows the cyclic order of the slots. -/
@[simp] theorem offDiagSingle_mul_offDiagSingle_add_one (i : Fin 3) (a b : CayleyDickson ℍ[R]) :
    offDiagSingle i a * offDiagSingle (i + 1) b =
      ⅟(2 : R) • offDiagSingle (i + 2) (star (a * b)) := by
  refine CompactAlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    fin_cases i <;> fin_cases k <;> simp

end Peirce

/-- **The diagonal frame and the off-diagonal slots span the compact Albert algebra**: a Hermitian
octonion matrix is the combination of the diagonal idempotents read off its diagonal, plus its three
off-diagonal slots. -/
theorem eq_sum_smul_diagIdempotent_add_sum_offDiagSingle (A : CompactAlbertAlgebra R) :
    A = (∑ i, A.diag i • diagIdempotent R i) + ∑ i, offDiagSingle i (A.offDiag i) := by
  refine CompactAlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_) <;>
    simp only [Fin.sum_univ_three, add_diag, add_offDiag, smul_diag, smul_offDiag,
      diagIdempotent_diag, diagIdempotent_offDiag, offDiagSingle_diag, offDiagSingle_offDiag,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_zero, add_zero, zero_add] <;>
    fin_cases m <;> simp

end CompactAlbertAlgebra

end TauCeti
