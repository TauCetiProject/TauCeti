/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

/-!
# The pinned type-A graph automorphism on matrices

Inverse transpose is an automorphism of `GL_n(A)` over any commutative semiring. Over a
commutative ring, conjugating it by the signed reversal matrix gives the pinned type-`A_r`
graph automorphism

```text
g ↦ Q (g⁻¹)ᵀ Q⁻¹,
```

where `Q` reverses the standard basis and alternates its signs. The sign correction is essential:
it makes the automorphism carry each positive simple-root transvection to the positive
simple-root transvection at the reversed Dynkin node, with the parameter unchanged. Without it,
inverse transpose would introduce a minus sign.

The construction is over an arbitrary commutative ring and is natural under ring homomorphisms.
It is the matrix-points input for the graph automorphism of the full-weight type-`A` Chevalley
carrier.

## Main definitions

* `Matrix.GeneralLinearGroup.inverseTranspose`: the automorphism `g ↦ (g⁻¹)ᵀ`.
* `TauCeti.typeAGraphConjugator`: the signed reversal matrix `Q`.
* `TauCeti.typeAGraphAutomorphism`: the pinned graph automorphism `g ↦ Q (g⁻¹)ᵀ Q⁻¹`.

## Main results

* `TauCeti.typeAGraphAutomorphism_eq_iff_mul_conjugator_mul_transpose_eq` and
  `TauCeti.typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq`: the automorphism carries
  `g` to `h` exactly when `h * Q * gᵀ = Q`, equivalently when `gᵀ * Q * h = Q`.
* `TauCeti.typeAGraphAutomorphism_transvectionUnit`: the sign-free equation on every positive
  simple-root subgroup.
* `TauCeti.typeAGraphAutomorphism_transvectionUnit_lower`: the corresponding equation on every
  negative simple-root subgroup.
* `TauCeti.typeAGraphAutomorphism_transvectionUnit_of_ne`: the equation on the root subgroup of an
  arbitrary root `ε_i - ε_j`, where the parameter is rescaled by the sign `(-1) ^ (i + j + 1)`.
* `TauCeti.typeAGraphAutomorphism_diagGL`: the automorphism reverses and inverts diagonal entries.
* `TauCeti.typeAGraphAutomorphism_apply_apply`: the signed entrywise formula on the inverse matrix.
* `TauCeti.typeAGraphAutomorphism_mem_upperTriangularGroup_iff`: preservation of
  upper triangularity.
* `TauCeti.typeAGraphAutomorphism_mul_self`: the automorphism has order dividing two.
* `TauCeti.map_typeAGraphAutomorphism`: the construction is natural in the coefficient ring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.
-/

public section

open Matrix

namespace TauCeti

universe u

variable {A : Type u}

section Ring

variable [Ring A]

/-- The alternating diagonal signs used to pin the type-`A_r` graph automorphism. -/
private def typeAGraphSign (i : Fin (r + 1)) : Aˣ := (-1 : Aˣ) ^ (i : ℕ)

private theorem typeAGraphSign_inv (i : Fin (r + 1)) :
    (typeAGraphSign (A := A) i)⁻¹ = typeAGraphSign (A := A) i := by
  apply inv_eq_iff_mul_eq_one.mpr
  simp only [typeAGraphSign, ← pow_add, ← two_mul (i : ℕ), pow_mul]
  simp

private theorem coe_typeAGraphSign (i : Fin (r + 1)) :
    ((typeAGraphSign (A := A) i : Aˣ) : A) = (-1 : A) ^ (i : ℕ) := by
  simp [typeAGraphSign]

/-- The signed reversal matrix `Q` used in the pinned type-`A_r` graph automorphism. It first
reverses the standard basis and then applies alternating signs. -/
def typeAGraphConjugator (r : ℕ) (A : Type u) [Ring A] : GL (Fin (r + 1)) A :=
  diagGL (typeAGraphSign (A := A)) * permutationGL (k := A) Fin.revPerm

private theorem permutationGL_rev_inv {A : Type u} [Semiring A] (r : ℕ) :
    (permutationGL (k := A) (Fin.revPerm : Equiv.Perm (Fin (r + 1))))⁻¹ =
      permutationGL (k := A) Fin.revPerm := by
  rw [← map_inv]
  congr 1

/-- The square of the signed reversal matrix is the scalar matrix `(-1)^r I`. -/
theorem typeAGraphConjugator_mul_self (r : ℕ) :
    typeAGraphConjugator r A * typeAGraphConjugator r A =
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) := by
  let d : GL (Fin (r + 1)) A := diagGL (typeAGraphSign (A := A))
  let p : GL (Fin (r + 1)) A := permutationGL (k := A) Fin.revPerm
  have hp : p * p = 1 :=
    inv_eq_iff_mul_eq_one.mp (permutationGL_rev_inv (A := A) r)
  have hpd : p * d * p⁻¹ = diagGL (fun i => typeAGraphSign (A := A) i.rev) := by
    simpa only [p, d, Equiv.Perm.inv_def, Fin.revPerm_symm, Fin.revPerm_apply] using
      permutationGL_mul_diagGL_mul_inv (k := A)
        (Fin.revPerm : Equiv.Perm (Fin (r + 1))) (typeAGraphSign (A := A))
  -- Normalize the public conjugator definition to the local names used in the calculation.
  change (d * p) * (d * p) = _
  calc
    _ = d * (p * d * p⁻¹) * (p * p) := by group
    _ = d * diagGL (fun i => typeAGraphSign (A := A) i.rev) * 1 := by rw [hpd, hp]
    _ = diagGL (fun i =>
        typeAGraphSign (A := A) i * typeAGraphSign (A := A) i.rev) := by
      rw [mul_one, ← map_mul]
      rfl
    _ = diagGL (fun _ : Fin (r + 1) => (-1 : Aˣ) ^ r) := by
      congr 1
      funext i
      simp only [typeAGraphSign, ← pow_add]
      congr 1
      simp [Fin.val_rev]
      omega
    _ = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) := diagGL_const _

/-- Entrywise base change carries the signed reversal matrix to the signed reversal matrix. -/
@[simp]
theorem map_typeAGraphConjugator {B : Type*} [Ring B] (f : A →+* B) (r : ℕ) :
    Units.map (MonoidHom.ofClass (f.mapMatrix (m := Fin (r + 1)))) (typeAGraphConjugator r A) =
      typeAGraphConjugator r B := by
  apply Units.ext
  ext i j
  simp [typeAGraphConjugator, typeAGraphSign, Fin.rev_eq_iff]

end Ring

variable [CommRing A]

/-- **The pinned graph automorphism of the type-`A_r` matrix group.** It is signed reverse
inverse transpose, `g ↦ Q (g⁻¹)ᵀ Q⁻¹`. -/
def typeAGraphAutomorphism (r : ℕ) (A : Type u) [CommRing A] :
    GL (Fin (r + 1)) A ≃* GL (Fin (r + 1)) A :=
  Matrix.GeneralLinearGroup.inverseTranspose.trans (MulAut.conj (typeAGraphConjugator r A))

/-- The type-`A` graph automorphism is conjugated inverse transpose. -/
theorem typeAGraphAutomorphism_apply (r : ℕ) (g : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g =
      typeAGraphConjugator r A * Matrix.GeneralLinearGroup.inverseTranspose g *
        (typeAGraphConjugator r A)⁻¹ :=
  (rfl)

/-- The graph automorphism reverses the two indices of the inverse matrix and multiplies
its entries by the alternating row and column signs. -/
@[simp]
theorem typeAGraphAutomorphism_apply_apply (r : ℕ) (g : GL (Fin (r + 1)) A)
    (i j : Fin (r + 1)) :
    (typeAGraphAutomorphism r A g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j =
      (-1 : A) ^ (i : ℕ) *
        ((g⁻¹ : GL (Fin (r + 1)) A) : Matrix (Fin (r + 1)) (Fin (r + 1)) A) j.rev i.rev *
        (-1 : A) ^ (j : ℕ) := by
  have hmiddle := coe_permutationGL_inv_mul_mul_permutationGL_apply
    Fin.revPerm (Matrix.GeneralLinearGroup.inverseTranspose g) i j
  rw [permutationGL_rev_inv] at hmiddle
  -- Regroup the signed conjugation so diagonal multiplication acts only on the outside.
  rw [typeAGraphAutomorphism_apply, typeAGraphConjugator, _root_.mul_inv_rev,
    ← mul_assoc, mul_assoc (diagGL _), mul_assoc (diagGL _),
    permutationGL_rev_inv, ← map_inv (diagGL (k := A))]
  rw [Units.val_mul, Units.val_mul, diagGL_coe, diagGL_coe,
    Matrix.mul_diagonal, Matrix.diagonal_mul, hmiddle]
  simp [Matrix.GeneralLinearGroup.coe_inverseTranspose, typeAGraphSign]

private theorem inverseTranspose_typeAGraphConjugator (r : ℕ) :
    Matrix.GeneralLinearGroup.inverseTranspose (typeAGraphConjugator r A) =
      typeAGraphConjugator r A := by
  simp only [typeAGraphConjugator, map_mul, inverseTranspose_diagGL,
    inverseTranspose_permutationGL, typeAGraphSign_inv]

private theorem typeAGraphAutomorphism_eq_iff_gl (r : ℕ) (g h : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g = h ↔
      h * typeAGraphConjugator r A * (Matrix.GeneralLinearGroup.inverseTranspose g)⁻¹ =
        typeAGraphConjugator r A := by
  rw [typeAGraphAutomorphism_apply, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

/-- **The pinned type-`A` graph automorphism, read as an invariance equation.** The automorphism
carries `g` to `h` exactly when `h * Q * gᵀ = Q`, with `Q` the signed reversal matrix.

Composing with an entrywise ring endomorphism `σ` and taking `g = σ h` reads the equation as the
invariance of the `σ`-sesquilinear form of Gram matrix `Q` under `h`, in the transposed form
recorded by `TauCeti.typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq`. That is the
shape of a unitarity condition, but not yet that condition: `σ` is only assumed to be a ring
endomorphism, and `Q` is the reversal matrix with alternating signs, so `Qᵀ = (-1) ^ r • Q`.
For involutive `σ`, even `r` gives a Hermitian form and odd `r` gives a skew-Hermitian form,
which is again Hermitian exactly where `-1 = 1`, as in characteristic two. -/
@[simp]
theorem typeAGraphAutomorphism_eq_iff_mul_conjugator_mul_transpose_eq (r : ℕ)
    (g h : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g = h ↔
      (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).transpose =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [typeAGraphAutomorphism_eq_iff_gl, ← Units.val_inj]
  simp only [Units.val_mul, ← map_inv, Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]

-- The square of the signed reversal matrix is a scalar, hence central, so the two outer factors of
-- an invariance equation may be exchanged.
private theorem mul_typeAGraphConjugator_mul_swap (r : ℕ) {a b : GL (Fin (r + 1)) A}
    (h : a * typeAGraphConjugator r A * b = typeAGraphConjugator r A) :
    b * typeAGraphConjugator r A * a = typeAGraphConjugator r A := by
  have hb : b = (a * typeAGraphConjugator r A)⁻¹ * typeAGraphConjugator r A :=
    eq_inv_mul_iff_mul_eq.mpr h
  subst hb
  calc (a * typeAGraphConjugator r A)⁻¹ * typeAGraphConjugator r A *
        typeAGraphConjugator r A * a
      = (a * typeAGraphConjugator r A)⁻¹ *
          (typeAGraphConjugator r A * typeAGraphConjugator r A) * a := by group
    _ = (a * typeAGraphConjugator r A)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) * a) := by
        rw [typeAGraphConjugator_mul_self, mul_assoc]
    _ = (a * typeAGraphConjugator r A)⁻¹ *
          (a * (typeAGraphConjugator r A * typeAGraphConjugator r A)) := by
        rw [Matrix.GeneralLinearGroup.scalar_commute, typeAGraphConjugator_mul_self]
    _ = typeAGraphConjugator r A := by group

/-- **The invariance equation of the pinned type-`A` graph automorphism, transposed.** The
automorphism carries `g` to `h` exactly when `gᵀ * Q * h = Q`.

The two outer factors of `TauCeti.typeAGraphAutomorphism_eq_iff_mul_conjugator_mul_transpose_eq`
may be exchanged because the square of the signed reversal matrix is a scalar. Composing with an
entrywise ring endomorphism `σ` and taking `g = σ h`, this is the equation `h* * Q * h = Q` saying
that `h` is an isometry of the `σ`-sesquilinear form of Gram matrix `Q`, with `h* = (σ h)ᵀ`. It is
the classical unitarity condition only where that form is Hermitian, which needs `σ` an involution,
not assumed here, and needs `Qᵀ = Q`: since `Qᵀ = (-1) ^ r • Q`, even `r` gives that outright,
while odd `r` gives a skew-Hermitian form, again Hermitian exactly where `-1 = 1`, as in
characteristic two. For `σ` the identity the form is bilinear, symmetric for even `r` and
alternating for odd `r`. -/
theorem typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq (r : ℕ)
    (g h : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g = h ↔
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).transpose *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [typeAGraphAutomorphism_eq_iff_gl]
  refine Iff.trans ⟨mul_typeAGraphConjugator_mul_swap r, mul_typeAGraphConjugator_mul_swap r⟩ ?_
  rw [← Units.val_inj]
  simp only [Units.val_mul, ← map_inv, Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]

/-- Applying the pinned type-`A` graph automorphism twice is the identity. -/
@[simp]
theorem typeAGraphAutomorphism_typeAGraphAutomorphism (r : ℕ)
    (g : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A (typeAGraphAutomorphism r A g) = g := by
  rw [typeAGraphAutomorphism_apply, typeAGraphAutomorphism_apply, map_mul, map_mul,
    inverseTranspose_typeAGraphConjugator,
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose, map_inv,
    inverseTranspose_typeAGraphConjugator]
  calc
    typeAGraphConjugator r A *
          (typeAGraphConjugator r A * g * (typeAGraphConjugator r A)⁻¹) *
        (typeAGraphConjugator r A)⁻¹ =
        (typeAGraphConjugator r A * typeAGraphConjugator r A) * g *
          (typeAGraphConjugator r A * typeAGraphConjugator r A)⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) * g *
          (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r))⁻¹ := by
      rw [typeAGraphConjugator_mul_self]
    _ = g := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      group

/-- Signed reverse inverse transpose preserves the upper-triangular subgroup over every
commutative ring. -/
@[simp↓]
theorem typeAGraphAutomorphism_mem_upperTriangularGroup_iff (r : ℕ)
    (g : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g ∈ upperTriangularGroup (Fin (r + 1)) A ↔
      g ∈ upperTriangularGroup (Fin (r + 1)) A := by
  have hpres (h : GL (Fin (r + 1)) A)
      (hh : h ∈ upperTriangularGroup (Fin (r + 1)) A) :
      typeAGraphAutomorphism r A h ∈ upperTriangularGroup (Fin (r + 1)) A := by
    have hinv := (upperTriangularGroup (Fin (r + 1)) A).inv_mem hh
    rw [UpperTriangularGroup.mem_iff] at hinv ⊢
    intro i j hji
    have hz := hinv (i := j.rev) (j := i.rev) (Fin.rev_lt_rev.mpr hji)
    simp only [typeAGraphAutomorphism_apply_apply, hz, mul_zero, zero_mul]
  refine ⟨fun h => ?_, hpres g⟩
  simpa only [typeAGraphAutomorphism_typeAGraphAutomorphism] using
    hpres (typeAGraphAutomorphism r A g) h

/-- The pinned type-`A` graph automorphism has order dividing two. -/
@[simp]
theorem typeAGraphAutomorphism_mul_self (r : ℕ) :
    typeAGraphAutomorphism r A * typeAGraphAutomorphism r A = 1 := by
  apply DFunLike.ext _ _
  intro g
  exact typeAGraphAutomorphism_typeAGraphAutomorphism r g

private theorem typeAGraphAutomorphism_transvectionUnit_aux (r : ℕ)
    {i j : Fin (r + 1)} (hij : i ≠ j) (c : A) :
    typeAGraphAutomorphism r A (transvectionUnit hij c) =
      transvectionUnit (Fin.rev_injective.ne hij.symm)
        ((typeAGraphSign (A := A) j.rev : A) * (-c) *
          ((typeAGraphSign (A := A) i.rev)⁻¹ : Aˣ)) := by
  rw [typeAGraphAutomorphism_apply, inverseTranspose_transvectionUnit]
  let d : GL (Fin (r + 1)) A := diagGL (typeAGraphSign (A := A))
  let p : GL (Fin (r + 1)) A := permutationGL (k := A) Fin.revPerm
  -- Unfold the public conjugator into the local diagonal/reversal factors; rewriting cannot
  -- match this factorization beneath both multiplication and inversion at once.
  change (d * p) * transvectionUnit hij.symm (-c) * (d * p)⁻¹ = _
  calc
    _ = d * (p * transvectionUnit hij.symm (-c) * p⁻¹) * d⁻¹ := by group
    _ = d * transvectionUnit (Fin.rev_injective.ne hij.symm) (-c) * d⁻¹ := by
      congr 2
      simpa only [p, permutationGL_rev_inv, Fin.revPerm_symm, Fin.revPerm_apply] using
        permutationGL_inv_mul_transvectionUnit_mul_permutationGL Fin.revPerm hij.symm (-c)
    _ = _ := by rw [diagGL_mul_transvectionUnit_mul_inv]

/-- **The pinned graph automorphism on an arbitrary root subgroup.** For every root `ε_i - ε_j` of
the type-`A_r` system, that is every pair of distinct matrix indices, the automorphism carries the
elementary transvection `x_{ij}(c)` to `x_{rev j, rev i}(ε c)` with the sign

```text
ε = (-1) ^ (i + j + 1).
```

The reversal of the two indices is the reversal of the Bourbaki numbering, and the sign is the one
produced by the signed conjugator `TauCeti.typeAGraphConjugator` of this construction: it is what
the alternating diagonal signs of `Q` contribute once the reversal has moved the transvection. The
sign is `1` whenever the sum `i + j` is odd, which it is on every simple root, where
`TauCeti.typeAGraphAutomorphism_transvectionUnit` records the sign-free equation; it is `-1` on the
roots with even index sum, for instance on `ε_0 - ε_2` once the rank is at least two, and that value
differs from `1` exactly when `(-1 : A) ≠ 1`. Whether some other parametrization of the root
subgroups makes every sign trivial at once is not addressed here; for that question see
R. W. Carter, *Simple Groups of Lie Type*, §12.2. -/
@[simp]
theorem typeAGraphAutomorphism_transvectionUnit_of_ne (r : ℕ) {i j : Fin (r + 1)}
    (hij : i ≠ j) (c : A) :
    typeAGraphAutomorphism r A (transvectionUnit hij c) =
      transvectionUnit (Fin.rev_injective.ne hij.symm)
        ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * c) := by
  rw [typeAGraphAutomorphism_transvectionUnit_aux, typeAGraphSign_inv]
  congr 1
  rw [coe_typeAGraphSign, coe_typeAGraphSign]
  -- Reversing both indices preserves the parity of the total exponent.
  have hmod : ((j.rev : ℕ) + (i.rev : ℕ) + 1) % 2 = ((i : ℕ) + (j : ℕ) + 1) % 2 := by
    have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.val_rev]
    omega
  calc ((-1 : A) ^ (j.rev : ℕ)) * (-c) * ((-1 : A) ^ (i.rev : ℕ))
      = (-1 : A) ^ ((j.rev : ℕ) + (i.rev : ℕ) + 1) * c := by
        rw [pow_add, pow_add, pow_one]
        ring
    _ = (-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * c := by
        rw [neg_one_pow_eq_pow_mod_two ((j.rev : ℕ) + (i.rev : ℕ) + 1),
          neg_one_pow_eq_pow_mod_two ((i : ℕ) + (j : ℕ) + 1), hmod]

/-- **The pinned graph automorphism reverses the positive simple-root subgroups without changing
their parameters.** In Bourbaki numbering, the node `i` is carried to `i.rev`. The sign that
`TauCeti.typeAGraphAutomorphism_transvectionUnit_of_ne` attaches to a general root is trivial here,
the two matrix indices `i` and `i + 1` of a simple root having odd sum. That general equation is
the `@[simp]` form, and `simp` reaches this one through it, so this lemma is not itself `simp`. -/
theorem typeAGraphAutomorphism_transvectionUnit (r : ℕ) (i : Fin r) (c : A) :
    typeAGraphAutomorphism r A
        (transvectionUnit (Fin.castSucc_lt_succ (i := i)).ne c) =
      transvectionUnit (Fin.castSucc_lt_succ (i := i.rev)).ne c := by
  have hsign : (-1 : A) ^ ((i.castSucc : ℕ) + ((i.succ : Fin (r + 1)) : ℕ) + 1) = 1 :=
    Even.neg_one_pow ⟨(i : ℕ) + 1, by simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩
  simpa only [Fin.rev_succ, Fin.rev_castSucc, hsign, one_mul] using
    typeAGraphAutomorphism_transvectionUnit_of_ne r (Fin.castSucc_lt_succ (i := i)).ne c

/-- The pinned graph automorphism reverses the negative simple-root subgroups without changing
their parameters. As for the positive simple roots,
`TauCeti.typeAGraphAutomorphism_transvectionUnit_of_ne` is the `@[simp]` form that `simp` uses to
reach this one. -/
theorem typeAGraphAutomorphism_transvectionUnit_lower (r : ℕ) (i : Fin r) (c : A) :
    typeAGraphAutomorphism r A
        (transvectionUnit (Fin.castSucc_lt_succ (i := i)).ne' c) =
      transvectionUnit (Fin.castSucc_lt_succ (i := i.rev)).ne' c := by
  have hsign : (-1 : A) ^ (((i.succ : Fin (r + 1)) : ℕ) + (i.castSucc : ℕ) + 1) = 1 :=
    Even.neg_one_pow ⟨(i : ℕ) + 1, by simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩
  simpa only [Fin.rev_castSucc, Fin.rev_succ, hsign, one_mul] using
    typeAGraphAutomorphism_transvectionUnit_of_ne r (Fin.castSucc_lt_succ (i := i)).ne' c

/-- On the diagonal torus, the pinned graph automorphism reverses and inverts the diagonal
entries. -/
@[simp]
theorem typeAGraphAutomorphism_diagGL (r : ℕ) (d : Fin (r + 1) → Aˣ) :
    typeAGraphAutomorphism r A (diagGL d) =
      diagGL (fun i => (d i.rev)⁻¹) := by
  rw [typeAGraphAutomorphism_apply, inverseTranspose_diagGL]
  let s : Fin (r + 1) → Aˣ := typeAGraphSign (A := A)
  let p : GL (Fin (r + 1)) A := permutationGL (k := A) Fin.revPerm
  have hp : p * diagGL (fun i => (d i)⁻¹) * p⁻¹ =
      diagGL (fun i => (d i.rev)⁻¹) := by
    simpa only [p, Equiv.Perm.inv_def, Fin.revPerm_symm, Fin.revPerm_apply] using
      permutationGL_mul_diagGL_mul_inv (k := A)
        (Fin.revPerm : Equiv.Perm (Fin (r + 1))) (fun i => (d i)⁻¹)
  -- Normalize the public conjugator definition to the local signed diagonal and reversal.
  change (diagGL s * p) * diagGL (fun i => (d i)⁻¹) * (diagGL s * p)⁻¹ = _
  calc
    _ = diagGL s * (p * diagGL (fun i => (d i)⁻¹) * p⁻¹) * (diagGL s)⁻¹ := by
      group
    _ = diagGL s * diagGL (fun i => (d i.rev)⁻¹) * (diagGL s)⁻¹ := by rw [hp]
    _ = diagGL (fun i => (d i.rev)⁻¹) := by
      rw [← map_inv]
      simp only [← map_mul]
      congr 1
      funext i
      simp [mul_assoc]

/-- The pinned type-`A` graph automorphism is natural in the coefficient ring. -/
@[simp]
theorem map_typeAGraphAutomorphism {B : Type*} [CommRing B] (f : A →+* B) (r : ℕ)
    (g : GL (Fin (r + 1)) A) :
    Matrix.GeneralLinearGroup.map f (typeAGraphAutomorphism r A g) =
      typeAGraphAutomorphism r B (Matrix.GeneralLinearGroup.map f g) := by
  rw [typeAGraphAutomorphism_apply, typeAGraphAutomorphism_apply]
  simp only [Matrix.GeneralLinearGroup.map, RingHom.toMonoidHom_eq_coe, map_mul, map_inv,
    Matrix.GeneralLinearGroup.map_inverseTranspose, map_typeAGraphConjugator]

end TauCeti
