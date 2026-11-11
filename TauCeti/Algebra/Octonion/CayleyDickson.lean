/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import TauCeti.Algebra.CayleyDickson.Basic
public import TauCeti.Algebra.Octonion.Basic

/-!
# The split octonions as a Cayley–Dickson double

The split octonions `TauCeti.Octonion R` are built in `TauCeti/Algebra/Octonion/Basic.lean` as Zorn
vector matrices. This file identifies them with the Cayley–Dickson double
`TauCeti.CayleyDickson ℍ[R,0,1,1]` of a split quaternion algebra, by an explicit `R`-linear
equivalence that preserves the unit, the product, the conjugation, the trace and the norm. It is a
comparison of nonassociative algebras, so it is bundled as a linear equivalence together with its
multiplicativity, the form consumed by `TauCeti.derivationLieAlgebraCongr`.

## The split quaternions

In the quaternion algebra `ℍ[R,0,1,1]` the generators satisfy `i * i = i`, `j * j = 1` and
`k = i * j`. Over every commutative ring it is the matrix algebra `M₂(R)`, through

`q ↦ [[q.re + q.imI, q.imJ + q.imK], [q.imJ, q.re]]`,

which sends `i` to the matrix unit `E₁₁`, `j` to `E₁₂ + E₂₁` and `k` to `E₁₂`. Its conjugation
`star q = ⟨q.re + q.imI, -q.imI, -q.imJ, -q.imK⟩` is then the adjugate, its norm `q * star q` is the
determinant `(q.re + q.imI) * q.re - q.imJ * (q.imJ + q.imK)`, and its trace `q + star q` is
`2 * q.re + q.imI`. Unlike the more familiar `ℍ[R,1,0,1]`, this normalization needs no
hypothesis on `2`, which is why it is used here: the comparison below holds over every commutative
ring, as the Zorn model does.

## The comparison

Inside the Zorn vector matrices, the matrices `[[a, (s, 0, 0)], [(t, 0, 0), b]]` form a copy of
`M₂(R)`, compatibly with conjugation, and the element `ℓ = [[0, (0, 1, 0)], [(0, -1, 0), 0]]` is
orthogonal to it with `ℓ * ℓ = -1`. The doubling `⟨x, y⟩ ↦ x + y * ℓ` along `ℓ` is the equivalence
`TauCeti.Octonion.cayleyDicksonEquiv`; in coordinates, `⟨x, y⟩` goes to the Zorn vector matrix with
diagonal entries `x.re + x.imI` and `x.re` and vector entries

`v = (x.imJ + x.imK, y.re + y.imI, y.imJ)`, `w = (x.imJ, -y.re, y.imJ + y.imK)`.

## Main definitions

* `TauCeti.Octonion.cayleyDicksonEquiv`: the linear equivalence
  `CayleyDickson ℍ[R,0,1,1] ≃ₗ[R] Octonion R`.

## Main results

* `TauCeti.Octonion.cayleyDicksonEquiv_one` and `TauCeti.Octonion.cayleyDicksonEquiv_mul`: it is
  unital and multiplicative, with `TauCeti.Octonion.cayleyDicksonEquiv_symm_one` and
  `TauCeti.Octonion.cayleyDicksonEquiv_symm_mul` for its inverse.
* `TauCeti.Octonion.cayleyDicksonEquiv_star` and `TauCeti.Octonion.cayleyDicksonEquiv_symm_conj`:
  it carries the involution of the double to octonion conjugation.
* `TauCeti.Octonion.trace_cayleyDicksonEquiv` and `TauCeti.Octonion.norm_cayleyDicksonEquiv`: it
  carries the trace of the double, the trace of its first quaternion coordinate, and the norm of
  the double, the sum of the norms of its two quaternion coordinates, to the octonion trace and
  norm.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), §1.5 (the doubling process) and §1.8 (the split octonions and Zorn's vector
  matrices).
* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §2.2.
-/

public section

namespace TauCeti.Octonion

open Matrix Quaternion

variable (R : Type*) [CommRing R]

/-- **The split octonions as a Cayley–Dickson double**: the `R`-linear equivalence between the
Cayley–Dickson double of the split quaternion algebra `ℍ[R,0,1,1]` and the Zorn vector matrices,
sending `⟨x, y⟩` to `x + y * ℓ` for the copy of `ℍ[R,0,1,1] ≅ M₂(R)` on the diagonal and first
vector coordinates and the doubling element `ℓ = [[0, (0, 1, 0)], [(0, -1, 0), 0]]`, the image of
`⟨0, 1⟩`. It preserves the unit, the product, the conjugation, the trace and the norm
(`TauCeti.Octonion.cayleyDicksonEquiv_one`,
`TauCeti.Octonion.cayleyDicksonEquiv_mul`, `TauCeti.Octonion.cayleyDicksonEquiv_star`,
`TauCeti.Octonion.trace_cayleyDicksonEquiv`, `TauCeti.Octonion.norm_cayleyDicksonEquiv`). -/
def cayleyDicksonEquiv : CayleyDickson ℍ[R,0,1,1] ≃ₗ[R] Octonion R where
  toFun x := ⟨x.fst.re + x.fst.imI, x.fst.re, ![x.fst.imJ + x.fst.imK, x.snd.re + x.snd.imI,
    x.snd.imJ], ![x.fst.imJ, -x.snd.re, x.snd.imJ + x.snd.imK]⟩
  invFun z :=
    ⟨⟨z.b, z.a - z.b, z.w 0, z.v 0 - z.w 0⟩, ⟨-z.w 1, z.v 1 + z.w 1, z.v 2, z.w 2 - z.v 2⟩⟩
  map_add' x y := by
    ext i
    · simp only [Octonion.add_a, CayleyDickson.add_fst, QuaternionAlgebra.re_add,
        QuaternionAlgebra.imI_add]
      ring
    · simp
    · fin_cases i <;> simp <;> ring
    · fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    · simp [mul_add]
    · simp
    · fin_cases i <;> simp [mul_add]
    · fin_cases i <;> simp [mul_add]
  left_inv x := by
    ext <;> simp
  right_inv z := by
    ext i
    · simp
    · simp
    · fin_cases i <;> simp
    · fin_cases i <;> simp

variable {R}

@[simp]
theorem cayleyDicksonEquiv_apply_a (x : CayleyDickson ℍ[R,0,1,1]) :
    (cayleyDicksonEquiv R x).a = x.fst.re + x.fst.imI :=
  (rfl)

@[simp]
theorem cayleyDicksonEquiv_apply_b (x : CayleyDickson ℍ[R,0,1,1]) :
    (cayleyDicksonEquiv R x).b = x.fst.re :=
  (rfl)

@[simp]
theorem cayleyDicksonEquiv_apply_v (x : CayleyDickson ℍ[R,0,1,1]) :
    (cayleyDicksonEquiv R x).v = ![x.fst.imJ + x.fst.imK, x.snd.re + x.snd.imI, x.snd.imJ] :=
  (rfl)

@[simp]
theorem cayleyDicksonEquiv_apply_w (x : CayleyDickson ℍ[R,0,1,1]) :
    (cayleyDicksonEquiv R x).w = ![x.fst.imJ, -x.snd.re, x.snd.imJ + x.snd.imK] :=
  (rfl)

@[simp]
theorem cayleyDicksonEquiv_symm_apply_fst (z : Octonion R) :
    ((cayleyDicksonEquiv R).symm z).fst = ⟨z.b, z.a - z.b, z.w 0, z.v 0 - z.w 0⟩ :=
  (rfl)

@[simp]
theorem cayleyDicksonEquiv_symm_apply_snd (z : Octonion R) :
    ((cayleyDicksonEquiv R).symm z).snd = ⟨-z.w 1, z.v 1 + z.w 1, z.v 2, z.w 2 - z.v 2⟩ :=
  (rfl)

/-- The comparison sends the unit of the double to the unit of the split octonions. -/
@[simp]
theorem cayleyDicksonEquiv_one : cayleyDicksonEquiv R 1 = 1 := by
  ext i
  · simp
  · simp
  · fin_cases i <;> simp
  · fin_cases i <;> simp

/-- **The comparison is multiplicative**: the Cayley–Dickson product
`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩` goes to the Zorn vector-matrix
product. -/
@[simp]
theorem cayleyDicksonEquiv_mul (x y : CayleyDickson ℍ[R,0,1,1]) :
    cayleyDicksonEquiv R (x * y) = cayleyDicksonEquiv R x * cayleyDicksonEquiv R y := by
  ext i
  · simp [dotProduct, Fin.sum_univ_three]
    ring
  · simp [dotProduct, Fin.sum_univ_three]
    ring
  · fin_cases i <;> simp [cross_apply] <;> ring
  · fin_cases i <;> simp [cross_apply] <;> ring

/-- The inverse comparison is multiplicative as well. -/
@[simp]
theorem cayleyDicksonEquiv_symm_mul (z z' : Octonion R) :
    (cayleyDicksonEquiv R).symm (z * z') =
      (cayleyDicksonEquiv R).symm z * (cayleyDicksonEquiv R).symm z' :=
  (cayleyDicksonEquiv R).injective <| by simp [cayleyDicksonEquiv_mul]

/-- The comparison carries the involution `star ⟨a, b⟩ = ⟨star a, -b⟩` of the double to octonion
conjugation. -/
@[simp]
theorem cayleyDicksonEquiv_star (x : CayleyDickson ℍ[R,0,1,1]) :
    cayleyDicksonEquiv R (star x) = conj (cayleyDicksonEquiv R x) := by
  ext i
  · simp
  · simp
  · fin_cases i <;> simp [add_comm]
  · fin_cases i <;> simp [add_comm]

/-- The inverse comparison sends the unit of the split octonions to the unit of the double. -/
@[simp]
theorem cayleyDicksonEquiv_symm_one : (cayleyDicksonEquiv R).symm 1 = 1 :=
  (cayleyDicksonEquiv R).symm_apply_eq.mpr cayleyDicksonEquiv_one.symm

/-- The inverse comparison carries octonion conjugation to the involution of the double. -/
@[simp]
theorem cayleyDicksonEquiv_symm_conj (z : Octonion R) :
    (cayleyDicksonEquiv R).symm (conj z) = star ((cayleyDicksonEquiv R).symm z) :=
  (cayleyDicksonEquiv R).symm_apply_eq.mpr <| by simp

/-- The trace of `cayleyDicksonEquiv R x` is the trace `2 * x.fst.re + x.fst.imI` of the first
coordinate, the scalar `x + star x` of the double. -/
theorem trace_cayleyDicksonEquiv (x : CayleyDickson ℍ[R,0,1,1]) :
    trace (cayleyDicksonEquiv R x) = 2 * x.fst.re + x.fst.imI := by
  simp only [trace_apply, cayleyDicksonEquiv_apply_a, cayleyDicksonEquiv_apply_b]
  ring

/-- The norm of `cayleyDicksonEquiv R x` is the sum of the norms of the two quaternion coordinates,
the scalar `x * star x` of the double. -/
@[simp]
theorem norm_cayleyDicksonEquiv (x : CayleyDickson ℍ[R,0,1,1]) :
    norm (cayleyDicksonEquiv R x) = (x.fst * star x.fst).re + (x.snd * star x.snd).re := by
  simp [norm_def, dotProduct, Fin.sum_univ_three]
  ring

end TauCeti.Octonion
