/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Octonion.Basic

/-!
# The split Albert algebra

The split Albert algebra `H₃(𝕆)` over a commutative ring `R` in which `2` is invertible is the
space of `3 × 3` Hermitian matrices over the split octonions `TauCeti.Octonion R`,

`⟦d, x⟧ = [[d 0, x 2, conj (x 1)], [conj (x 2), d 1, x 0], [x 1, conj (x 0), d 2]]`,

under the symmetrized product `A ∘ B = ½ (A B + B A)`. A Hermitian matrix is recorded here by the
data it consists of — a scalar diagonal `d : Fin 3 → R` and three octonion entries
`x : Fin 3 → Octonion R`, the entry `x i` sitting in position `(i + 1, i + 2)` — rather than as a
`Matrix (Fin 3) (Fin 3) (Octonion R)` cut out by a Hermitian predicate: octonion matrices do not
form a ring (their entries do not associate), so `Matrix.mul` would carry no algebraic structure to
inherit, and the subtype would still have to be given its multiplication by hand.

Carrying out the matrix product `½ (A B + B A)` on that data leaves an expression in the octonion
multiplication and in the symmetric bilinear form of the split-octonion norm. That form is Mathlib's
`β = QuadraticMap.associated (TauCeti.Octonion.normQuadraticForm R)` — half the polar form, and the
scalar `½ (x * conj y + y * conj x)` — so the bilinearity and symmetry the product needs are
Mathlib's. The diagonal of the product is
`d i * e i + β (x (i + 1)) (y (i + 1)) + β (x (i + 2)) (y (i + 2))`, and the entries are
`½ ((d (i + 1) + d (i + 2)) • y i + (e (i + 1) + e (i + 2)) • x i)` corrected by the conjugate of
`½ (x (i + 1) * y (i + 2) + y (i + 1) * x (i + 2))`. That expression *is* the definition below.

The product is commutative, `R`-bilinear, and unital with the identity matrix as its unit, and the
three diagonal idempotents form a complete orthogonal frame. The **Jordan identity**
`(A ∘ B) ∘ A² = A ∘ (B ∘ A²)` — that is, `IsCommJordan (AlbertAlgebra R)` — is **not proved here**;
it is what makes `H₃(𝕆)` an exceptional Jordan algebra rather than merely a commutative one.

The coordinate isomorphism works for any semiring acting on coefficients that form an additive
commutative monoid. The trace and its kernel need only a semiring, while the symmetrized product
needs a commutative ring in which `2` is invertible: over `ℤ` the halved symmetric form of the
split-octonion norm is not integral.
The dimension counts ask for `StrongRankCondition`, over a semiring for `H₃(𝕆)` itself and over a
ring for the trace-zero subspace.

## Main definitions

* `TauCeti.AlbertAlgebra`: the split Albert algebra over `R`, with its `NonAssocCommRing` and
  `Module R` structure and the `SMulCommClass` and `IsScalarTower` instances that say the product
  is `R`-bilinear.
* `TauCeti.AlbertAlgebra.trace`: the trace `d 0 + d 1 + d 2`, an `R`-linear functional.
* `TauCeti.AlbertAlgebra.traceZero`: the trace-zero subspace `J₀`, the kernel of the trace.
* `TauCeti.AlbertAlgebra.diagIdempotent`: the three diagonal idempotents `E₀`, `E₁`, `E₂`.

## Main results

* `TauCeti.AlbertAlgebra.finrank_eq_twentySeven`: `H₃(𝕆)` is `27`-dimensional.
* `TauCeti.AlbertAlgebra.finrank_traceZero`: the trace-zero subspace is `26`-dimensional.
* the `NonAssocCommRing` instance: the product is `R`-bilinear and commutative, and the identity
  matrix is a two-sided unit. It is `NonAssocCommRing` and not `CommRing` because the product is
  not associative.
* `TauCeti.AlbertAlgebra.diagIdempotent_mul_diagIdempotent` and
  `TauCeti.AlbertAlgebra.sum_diagIdempotent`: the diagonal idempotents are orthogonal and sum
  to `1`.

## Implementation notes

The additive and module structures are transported along
`TauCeti.AlbertAlgebra.addEquivProd`, which packages a Hermitian matrix as the pair of its diagonal
and its octonion entries; `TauCeti.AlbertAlgebra.linearEquivProd` upgrades it to a linear
isomorphism over any semiring acting on the coefficients. The `27`-dimensional count uses this
isomorphism with `R` acting on itself; the trace-zero count uses a separate coordinate isomorphism
that drops the last diagonal entry, which a vanishing trace determines.

The multiplication is deliberately left unexposed: its body does not unfold outside this file, and
a product is read through the projection `simp` lemmas `TauCeti.AlbertAlgebra.mul_diag` and
`TauCeti.AlbertAlgebra.mul_offDiag`, which give its two components.

## References

The model is P. Jordan, J. von Neumann and E. Wigner, *On an algebraic generalization of the quantum
mechanical formalism*, Ann. of Math. 35 (1934); see also T. A. Springer and F. D. Veldkamp,
*Octonions, Jordan Algebras and Exceptional Groups*, §5.3, and J. C. Baez, *The octonions*, Bull.
Amer. Math. Soc. 39 (2002), §3.4, from which the coordinate form of the product above is taken.
-/

public section

namespace TauCeti

/-- The **split Albert algebra** `H₃(𝕆)` over `R`: a `3 × 3` Hermitian matrix over the split
octonions, recorded as its scalar diagonal together with its three octonion entries. -/
@[ext]
structure AlbertAlgebra (R : Type*) where
  /-- The scalar diagonal of the Hermitian matrix. -/
  diag : Fin 3 → R
  /-- The octonion entries: `offDiag i` is the entry in position `(i + 1, i + 2)`, and the entry in
  position `(i + 2, i + 1)` is its conjugate. -/
  offDiag : Fin 3 → Octonion R

namespace AlbertAlgebra

variable {R S : Type*}

/-! ### The additive and module structure -/

instance [Zero R] : Zero (AlbertAlgebra R) := ⟨0, 0⟩

@[simp] theorem zero_diag [Zero R] : (0 : AlbertAlgebra R).diag = 0 := (rfl)
@[simp] theorem zero_offDiag [Zero R] : (0 : AlbertAlgebra R).offDiag = 0 := (rfl)

instance [Zero R] : Inhabited (AlbertAlgebra R) := ⟨0⟩

instance [Zero R] [One R] : One (AlbertAlgebra R) := ⟨1, 0⟩

@[simp] theorem one_diag [Zero R] [One R] : (1 : AlbertAlgebra R).diag = 1 := (rfl)
@[simp] theorem one_offDiag [Zero R] [One R] : (1 : AlbertAlgebra R).offDiag = 0 := (rfl)

instance [Add R] : Add (AlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag + B.diag, A.offDiag + B.offDiag⟩⟩

@[simp] theorem add_diag [Add R] (A B : AlbertAlgebra R) : (A + B).diag = A.diag + B.diag := (rfl)
@[simp] theorem add_offDiag [Add R] (A B : AlbertAlgebra R) :
    (A + B).offDiag = A.offDiag + B.offDiag := (rfl)

instance [Neg R] : Neg (AlbertAlgebra R) := ⟨fun A => ⟨-A.diag, -A.offDiag⟩⟩

@[simp] theorem neg_diag [Neg R] (A : AlbertAlgebra R) : (-A).diag = -A.diag := (rfl)
@[simp] theorem neg_offDiag [Neg R] (A : AlbertAlgebra R) : (-A).offDiag = -A.offDiag := (rfl)

instance [Sub R] : Sub (AlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag - B.diag, A.offDiag - B.offDiag⟩⟩

@[simp] theorem sub_diag [Sub R] (A B : AlbertAlgebra R) : (A - B).diag = A.diag - B.diag := (rfl)
@[simp] theorem sub_offDiag [Sub R] (A B : AlbertAlgebra R) :
    (A - B).offDiag = A.offDiag - B.offDiag := (rfl)

instance [SMul S R] : SMul S (AlbertAlgebra R) :=
  ⟨fun s A => ⟨s • A.diag, s • A.offDiag⟩⟩

@[simp] theorem smul_diag [SMul S R] (s : S) (A : AlbertAlgebra R) :
    (s • A).diag = s • A.diag := (rfl)

@[simp] theorem smul_offDiag [SMul S R] (s : S) (A : AlbertAlgebra R) :
    (s • A).offDiag = s • A.offDiag := (rfl)

/-- The components of a Hermitian matrix, as an additive isomorphism with the pair of its scalar
diagonal and its octonion entries. The additive and module structures are transported along it, and
`TauCeti.AlbertAlgebra.linearEquivProd` upgrades it to a linear isomorphism over any semiring
acting on the coefficients. -/
def addEquivProd (R : Type*) [Add R] :
    AlbertAlgebra R ≃+ (Fin 3 → R) × (Fin 3 → Octonion R) where
  toFun A := (A.diag, A.offDiag)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem addEquivProd_apply [Add R] (A : AlbertAlgebra R) :
    addEquivProd R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem addEquivProd_symm_apply [Add R] (p : (Fin 3 → R) × (Fin 3 → Octonion R)) :
    (addEquivProd R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance [AddCommMonoid R] : AddCommMonoid (AlbertAlgebra R) := by
  apply (addEquivProd R).injective.addCommMonoid <;> intros <;> simp

instance [AddCommGroup R] : AddCommGroup (AlbertAlgebra R) := by
  apply (addEquivProd R).injective.addCommGroup <;> intros <;> simp

instance [Monoid S] [AddCommMonoid R] [DistribMulAction S R] :
    DistribMulAction S (AlbertAlgebra R) :=
  (addEquivProd R).injective.distribMulAction (addEquivProd R).toAddMonoidHom fun _ _ => by simp

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (AlbertAlgebra R) :=
  (addEquivProd R).injective.module _ (addEquivProd R).toAddMonoidHom fun _ _ => by simp

instance [AddCommGroup R] [One R] : AddCommGroupWithOne (AlbertAlgebra R) where
  __ := (inferInstance : AddCommGroup (AlbertAlgebra R))
  one := 1

/-- The components of a Hermitian matrix, as a linear isomorphism with the pair of its scalar
diagonal and its octonion entries, over any semiring acting on the coefficients. -/
def linearEquivProd (S R : Type*) [Semiring S] [AddCommMonoid R] [Module S R] :
    AlbertAlgebra R ≃ₗ[S] (Fin 3 → R) × (Fin 3 → Octonion R) :=
  (addEquivProd R).toLinearEquiv fun _ _ => rfl

@[simp] theorem linearEquivProd_apply [Semiring S] [AddCommMonoid R] [Module S R]
    (A : AlbertAlgebra R) : linearEquivProd S R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem linearEquivProd_symm_apply [Semiring S] [AddCommMonoid R] [Module S R]
    (p : (Fin 3 → R) × (Fin 3 → Octonion R)) :
    (linearEquivProd S R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance [Semiring R] : Module.Free R (AlbertAlgebra R) :=
  Module.Free.of_equiv (linearEquivProd R R).symm

instance [Semiring R] : Module.Finite R (AlbertAlgebra R) :=
  Module.Finite.equiv (linearEquivProd R R).symm

/-- **The split Albert algebra is `27`-dimensional**: three scalars on the diagonal and three
`8`-dimensional octonion entries. -/
theorem finrank_eq_twentySeven (R : Type*) [Semiring R] [StrongRankCondition R] :
    Module.finrank R (AlbertAlgebra R) = 27 := by
  rw [(linearEquivProd R R).finrank_eq, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_pi_fintype, Finset.sum_const]
  simp [Octonion.finrank_eq_eight]

/-! ### The symmetrized product -/

section Product

variable [CommRing R]

/-- The symmetrized matrix product `A ∘ B = ½ (A B + B A)`, written out on the diagonal and on the
octonion entries of a Hermitian matrix. The symmetric bilinear form associated with the octonion
norm — Mathlib's `QuadraticMap.associated`, half the polar form — enters on the diagonal, and the
conjugate of a symmetrized octonion product off it. -/
instance [Invertible (2 : R)] : Mul (AlbertAlgebra R) :=
  ⟨fun A B =>
    ⟨fun i => A.diag i * B.diag i
        + QuadraticMap.associated (Octonion.normQuadraticForm R)
            (A.offDiag (i + 1)) (B.offDiag (i + 1))
        + QuadraticMap.associated (Octonion.normQuadraticForm R)
            (A.offDiag (i + 2)) (B.offDiag (i + 2)),
      fun i =>
        ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
            + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i)
          + Octonion.conj
              (⅟(2 : R) • (A.offDiag (i + 1) * B.offDiag (i + 2)
                + B.offDiag (i + 1) * A.offDiag (i + 2)))⟩⟩

@[simp] theorem mul_diag [Invertible (2 : R)] (A B : AlbertAlgebra R) (i : Fin 3) :
    (A * B).diag i = A.diag i * B.diag i
      + QuadraticMap.associated (Octonion.normQuadraticForm R)
          (A.offDiag (i + 1)) (B.offDiag (i + 1))
      + QuadraticMap.associated (Octonion.normQuadraticForm R)
          (A.offDiag (i + 2)) (B.offDiag (i + 2)) :=
  (rfl)

@[simp] theorem mul_offDiag [Invertible (2 : R)] (A B : AlbertAlgebra R) (i : Fin 3) :
    (A * B).offDiag i =
      ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
          + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i)
        + Octonion.conj
            (⅟(2 : R) • (A.offDiag (i + 1) * B.offDiag (i + 2)
              + B.offDiag (i + 1) * A.offDiag (i + 2))) :=
  (rfl)

variable [Invertible (2 : R)]

instance : NonAssocCommRing (AlbertAlgebra R) where
  __ := (inferInstance : AddCommGroupWithOne (AlbertAlgebra R))
  left_distrib A B C := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add]
      abel
    · simp [mul_add, add_mul, smul_add]
      module
  right_distrib A B C := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [add_mul]
      abel
    · simp [mul_add, add_mul, smul_add]
      module
  zero_mul A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_zero A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_comm A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [QuadraticMap.associated_isSymm R (Octonion.normQuadraticForm R) (B.offDiag _), mul_comm]
    · simp
      module
  one_mul A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]
  mul_one A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]

instance : SMulCommClass R (AlbertAlgebra R) (AlbertAlgebra R) where
  smul_comm r A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add, mul_left_comm]
    · simp [mul_smul_comm, smul_mul_assoc]
      module

instance : IsScalarTower R (AlbertAlgebra R) (AlbertAlgebra R) where
  smul_assoc r A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add, mul_assoc]
    · simp [mul_smul_comm, smul_mul_assoc]
      module

end Product

/-! ### The trace -/

section Trace

variable [Semiring R]

/-- **The trace** of a Hermitian octonion matrix: the sum of its three scalar diagonal entries. -/
def trace : AlbertAlgebra R →ₗ[R] R where
  toFun A := ∑ i, A.diag i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

@[simp] theorem trace_apply (A : AlbertAlgebra R) : trace A = ∑ i, A.diag i := (rfl)

/-- The trace of the identity matrix is `3`, one for each diagonal entry. Not a `simp` lemma,
because `TauCeti.AlbertAlgebra.trace_apply` already takes its left-hand side apart. -/
theorem trace_one : trace (1 : AlbertAlgebra R) = 3 := by
  simp

/-- The trace is a surjection onto the base ring: it already is on the first diagonal entry. -/
theorem trace_surjective : Function.Surjective (trace : AlbertAlgebra R →ₗ[R] R) :=
  fun r => ⟨⟨Pi.single 0 r, 0⟩, by simp [Pi.single_apply]⟩

/-- **The trace-zero submodule** `J₀ ⊆ H₃(𝕆)`, the kernel of the trace. Over a ring
satisfying `StrongRankCondition` it is `26`-dimensional
(`TauCeti.AlbertAlgebra.finrank_traceZero`). Over a ring in which `3` is invertible, it
complements the scalar matrices; in characteristic `3`, it contains the identity matrix. -/
def traceZero (R : Type*) [Semiring R] : Submodule R (AlbertAlgebra R) := LinearMap.ker trace

@[simp] theorem mem_traceZero {A : AlbertAlgebra R} : A ∈ traceZero R ↔ trace A = 0 :=
  LinearMap.mem_ker

/-- The trace-zero matrices are free on the first two diagonal entries and the three octonion
entries: a vanishing trace forces the last diagonal entry. Private: it exists only to transport the
dimension count in `TauCeti.AlbertAlgebra.finrank_traceZero`. -/
private def traceZeroLinearEquivProd (R : Type*) [Ring R] :
    traceZero R ≃ₗ[R] (R × R) × (Fin 3 → Octonion R) where
  toFun A := ((A.1.diag 0, A.1.diag 1), A.1.offDiag)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨⟨![p.1.1, p.1.2, -(p.1.1 + p.1.2)], p.2⟩, by simp [Fin.sum_univ_three]⟩
  left_inv A := by
    have h : (A : AlbertAlgebra R).diag 2
        = -((A : AlbertAlgebra R).diag 0 + (A : AlbertAlgebra R).diag 1) := by
      have h0 : (A : AlbertAlgebra R).diag 0 + (A : AlbertAlgebra R).diag 1
          + (A : AlbertAlgebra R).diag 2 = 0 := by
        simpa [Fin.sum_univ_three] using mem_traceZero.mp A.2
      exact eq_neg_of_add_eq_zero_right h0
    refine Subtype.ext (AlbertAlgebra.ext (funext fun i => ?_) rfl)
    fin_cases i <;> simp [h]
  right_inv _ := rfl

end Trace

/-- **The trace-zero subspace of the split Albert algebra is `26`-dimensional**: a vanishing trace
pins the last diagonal entry to the negative of the sum of the other two. -/
theorem finrank_traceZero (R : Type*) [Ring R] [StrongRankCondition R] :
    Module.finrank R (traceZero R) = 26 := by
  rw [(traceZeroLinearEquivProd R).finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_pi_fintype, Finset.sum_const]
  simp [Octonion.finrank_eq_eight]

/-! ### The diagonal frame of idempotents -/

/-- The `i`-th **diagonal idempotent** `Eᵢ` of `H₃(𝕆)`: the Hermitian matrix with a single `1` in
position `(i, i)`. -/
def diagIdempotent (R : Type*) [Zero R] [One R] (i : Fin 3) : AlbertAlgebra R := ⟨Pi.single i 1, 0⟩

@[simp] theorem diagIdempotent_diag [Zero R] [One R] (i : Fin 3) :
    (diagIdempotent R i).diag = Pi.single i 1 := (rfl)
@[simp] theorem diagIdempotent_offDiag [Zero R] [One R] (i : Fin 3) :
    (diagIdempotent R i).offDiag = 0 := (rfl)

/-- **The diagonal idempotents are orthogonal**: `Eᵢ ∘ Eⱼ` is `Eᵢ` when `i = j` and `0`
otherwise. -/
@[simp] theorem diagIdempotent_mul_diagIdempotent [CommRing R] [Invertible (2 : R)] (i j : Fin 3) :
    diagIdempotent R i * diagIdempotent R j = if i = j then diagIdempotent R i else 0 := by
  rcases eq_or_ne i j with rfl | h
  · refine AlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases eq_or_ne k i with rfl | hk
      · simp
      · simp [hk]
    · simp
  · refine AlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · by_cases hk : k = i <;> simp [Pi.single_apply, hk, h]
    · simp [h]

/-- The diagonal idempotents add up to the identity matrix. -/
@[simp] theorem sum_diagIdempotent [AddCommMonoid R] [One R] : ∑ i, diagIdempotent R i = 1 := by
  apply (addEquivProd R).injective
  simp [map_sum, ← prod_mk_sum, Finset.univ_sum_single]
  rfl

/-- Each diagonal idempotent has trace `1`, so the frame accounts for the whole trace of the
identity. Not a `simp` lemma: `TauCeti.AlbertAlgebra.trace_apply` already takes its left-hand side
apart, and `simp` proves it outright. -/
theorem trace_diagIdempotent [Semiring R] (i : Fin 3) : trace (diagIdempotent R i) = 1 := by
  simp [Pi.single_apply]

end AlbertAlgebra

end TauCeti
