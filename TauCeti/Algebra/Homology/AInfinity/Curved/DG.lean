/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Curved.Algebra
public import TauCeti.Algebra.Homology.Curved.Algebra.Defs

/-!
# Curved differential graded algebras as curved `A∞` algebras

A curved differential graded algebra `(A, d, w)` is a curved `A∞` algebra with curvature
`m₀ = w`, `m₁ = d`, `m₂` the product, and `m n = 0` for `n ≥ 3`. The curved Stasheff identities
of arities zero to three are `d w = 0`, the curvature equation `d (d a) = a * w - w * a`, the
graded Leibniz rule and associativity; in arity at least two the curvature terms vanish, because
they have outer arity at least three, and every identity of arity at least four vanishes term by
term.

The arity-one identity `m₁(m₁(a)) = m₂(a, m₀) - m₂(m₀, a)` of a curved `A∞` algebra thus matches
the right-module convention `d (d a) = a * w - w * a` of `TauCeti.IsCurvedDGAlgebra` on the nose,
with no change of sign of the curvature. The unit of the algebra is a strict unit, so a scalar
curvature `w = c • 1` gives `d² = 0`.

Conversely, a curved `A∞` algebra structure on a graded algebra whose binary operation is the
product and whose ternary operation vanishes makes its unary operation and its curvature a curved
differential graded algebra. If all its higher operations vanish, it is the curved `A∞` algebra of
that curved differential graded algebra. For curvature zero the construction is the one of
`TauCeti/Algebra/Homology/AInfinity/Algebra/DG.lean`.

## Main definitions

* `TauCeti.IsCurvedDGAlgebra.toCurvedAInfinityAlgebra`: the curved `A∞` algebra of a curved
  differential graded algebra.

## Main results

* `TauCeti.IsCurvedDGAlgebra.curvature_toCurvedAInfinityAlgebra`,
  `TauCeti.IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_one_apply`,
  `TauCeti.IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_two_apply` and
  `TauCeti.IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_of_three_le`: its curvature and
  operations are the curvature, the differential, the product, and zero.
* `TauCeti.IsCurvedDGAlgebra.strictUnit_one`: the unit is a strict unit.
* `TauCeti.CurvedAInfinityAlgebra.isCurvedDGAlgebra`: the unary operation and the curvature of a
  curved `A∞` algebra whose binary operation is the product and whose ternary operation vanishes
  form a curved differential graded algebra.
* `TauCeti.CurvedAInfinityAlgebra.eq_toCurvedAInfinityAlgebra`: such a curved `A∞` algebra with
  vanishing higher operations is the curved `A∞` algebra of that curved differential graded
  algebra.
* `TauCeti.IsDGAlgebra.isCurvedDGAlgebra_zero_toCurvedAInfinityAlgebra`: for curvature zero, the
  construction agrees with the uncurved one.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 3.2.
-/

public section

open _root_.MultilinearMap

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

namespace IsCurvedDGAlgebra

open AInfinity

/-- The operations of a curved differential graded algebra satisfy every curved Stasheff identity
on homogeneous inputs. -/
private theorem curvedStasheffSum_operation (h : IsCurvedDGAlgebra 𝒜 d w) (n : ℕ) (e : ℕ → ℤ)
    (x : ℕ → A) (hx : ∀ i < n, x i ∈ 𝒜 (e i)) :
    AInfinity.curvedStasheffSum (dgOperation d w) e x n = 0 := by
  match n, hx with
  | 0, _ => simpa [dgOperation_zero_apply, dgOperation_one_apply] using h.map_curvature
  | 1, _ =>
    rw [AInfinity.curvedStasheffSum_one]
    simp [dgOperation_zero_apply, dgOperation_one_apply, dgOperation_two_apply, h.sq_eq]
  | n + 2, hx =>
    rw [AInfinity.curvedStasheffSum_eq_stasheffSum_of_m_succ_eq_zero _ _ _
      (dgOperation_of_three_le d w (by omega))]
    match n, hx with
    | 0, hx =>
      rw [AInfinity.stasheffSum_two_eq_zero_iff]
      simpa [dgOperation_one_apply, dgOperation_two_apply, ← negOnePow_smul_eq_negOnePowCast_smul]
        using h.leibniz (hx 0 (by omega)) (x 1)
    | 1, _ =>
      rw [AInfinity.stasheffSum_three_eq_zero_iff_of_m_three_eq_zero _ _ _
        (dgOperation_of_three_le d w le_rfl)]
      simp [dgOperation_two_apply, mul_assoc]
    | n + 2, _ =>
      exact AInfinity.stasheffSum_eq_zero_of_m_eq_zero_of_three_le _ _ _ (by omega)
        fun _ ↦ dgOperation_of_three_le d w

/-- The curved `A∞` algebra of a curved differential graded algebra: `m₀ = w`, `m₁ = d`, `m₂` is
the product, and `m n = 0` for `n ≥ 3`. -/
noncomputable def toCurvedAInfinityAlgebra (h : IsCurvedDGAlgebra 𝒜 d w) :
    CurvedAInfinityAlgebra R A where
  grading := InternalGrading.ofDecomposition 𝒜
  m := dgOperation d w
  m_degree n := by
    rw [InternalGrading.ofDecomposition_piece]
    exact isHomogeneous_dgOperation h.map_mem h.curvature_mem n
  stasheff n e x hx := by
    rw [InternalGrading.ofDecomposition_piece] at hx
    exact curvedStasheffSum_operation h n e x hx

/-- The curved `A∞` algebra of a curved differential graded algebra carries the grading of the
algebra. -/
@[simp]
theorem toCurvedAInfinityAlgebra_grading (h : IsCurvedDGAlgebra 𝒜 d w) :
    h.toCurvedAInfinityAlgebra.grading = InternalGrading.ofDecomposition 𝒜 := (rfl)

/-- The curvature of the curved `A∞` algebra of a curved differential graded algebra is its
curvature. -/
@[simp]
theorem curvature_toCurvedAInfinityAlgebra (h : IsCurvedDGAlgebra 𝒜 d w) :
    h.toCurvedAInfinityAlgebra.curvature = w :=
  (h.toCurvedAInfinityAlgebra.m_zero_apply ![]).symm.trans (dgOperation_zero_apply d w ![])

/-- The unary operation of the curved `A∞` algebra of a curved differential graded algebra is the
differential. -/
@[simp]
theorem toCurvedAInfinityAlgebra_m_one_apply (h : IsCurvedDGAlgebra 𝒜 d w) (x : Fin 1 → A) :
    h.toCurvedAInfinityAlgebra.m 1 x = d (x 0) :=
  dgOperation_one_apply d w x

/-- The binary operation of the curved `A∞` algebra of a curved differential graded algebra is
the product. -/
@[simp]
theorem toCurvedAInfinityAlgebra_m_two_apply (h : IsCurvedDGAlgebra 𝒜 d w) (x : Fin 2 → A) :
    h.toCurvedAInfinityAlgebra.m 2 x = x 0 * x 1 :=
  dgOperation_two_apply d w x

/-- The operations of arity at least three of the curved `A∞` algebra of a curved differential
graded algebra vanish. -/
theorem toCurvedAInfinityAlgebra_m_of_three_le (h : IsCurvedDGAlgebra 𝒜 d w) {n : ℕ}
    (hn : 3 ≤ n) : h.toCurvedAInfinityAlgebra.m n = 0 :=
  dgOperation_of_three_le d w hn

/-- The simp-normal form of `toCurvedAInfinityAlgebra_m_of_three_le`. -/
@[simp]
theorem toCurvedAInfinityAlgebra_m_add_three (h : IsCurvedDGAlgebra 𝒜 d w) (n : ℕ) :
    h.toCurvedAInfinityAlgebra.m (n + 3) = 0 :=
  h.toCurvedAInfinityAlgebra_m_of_three_le (by omega)

/-- The differential of the curved `A∞` algebra of a curved differential graded algebra is its
differential. -/
@[simp]
theorem differential_toCurvedAInfinityAlgebra (h : IsCurvedDGAlgebra 𝒜 d w) :
    h.toCurvedAInfinityAlgebra.differential = d := by
  ext x
  simp

/-- The unit of a curved differential graded algebra is a strict unit of its curved `A∞`
algebra. -/
theorem strictUnit_one (h : IsCurvedDGAlgebra 𝒜 d w) :
    h.toCurvedAInfinityAlgebra.StrictUnit 1 where
  degree_zero := by simpa using SetLike.one_mem_graded 𝒜
  binary_left x := by simp
  binary_right x := by simp
  higher n hn x := by
    rintro ⟨i, hi⟩
    rcases n with _ | _ | _ | n
    · exact i.elim0
    · rw [Fin.fin_one_eq_zero i] at hi
      rw [toCurvedAInfinityAlgebra_m_one_apply, hi, h.map_one_eq_zero]
    · exact absurd rfl hn
    · simp

end IsCurvedDGAlgebra

/-- For curvature zero, the curved `A∞` algebra of a differential graded algebra is its uncurved
`A∞` algebra. -/
theorem IsDGAlgebra.isCurvedDGAlgebra_zero_toCurvedAInfinityAlgebra (h : IsDGAlgebra 𝒜 d) :
    h.isCurvedDGAlgebra_zero.toCurvedAInfinityAlgebra =
      h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toCurvedAInfinityAlgebra := by
  refine CurvedAInfinityAlgebra.ext (by simp) (funext fun n ↦ ?_)
  rcases n with _ | _ | _ | n <;> ext x <;> simp

namespace CurvedAInfinityAlgebra

/-- **The differential graded truncation.** If the binary operation of a curved `A∞` algebra
structure on a graded algebra is the product and its ternary operation vanishes, its unary
operation and its curvature form a curved differential graded algebra. -/
theorem isCurvedDGAlgebra (𝒜' : CurvedAInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b)
    (hm₃ : 𝒜'.m 3 = 0) :
    IsCurvedDGAlgebra 𝒜 𝒜'.differential 𝒜'.curvature where
  map_mem {p a} ha := by
    simpa [hG] using 𝒜'.differential_mem_piece (p := p) (by simpa [hG] using ha)
  leibniz {p a} ha b := by
    have := 𝒜'.stasheff_arity_two_of_m_three_eq_zero hm₃ a b p (by simpa [hG] using ha)
    simpa [hm₂, ← negOnePow_smul_eq_negOnePowCast_smul] using this
  curvature_mem := by simpa [hG] using 𝒜'.curvature_mem
  sq_eq a := by rw [differential_differential, hm₂, hm₂]
  map_curvature := 𝒜'.differential_curvature

/-- A curved `A∞` algebra structure on a graded algebra whose binary operation is the product and
whose higher operations vanish is the curved `A∞` algebra of the curved differential graded
algebra given by its unary operation and its curvature. -/
theorem eq_toCurvedAInfinityAlgebra (𝒜' : CurvedAInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b)
    (hm : ∀ n, 3 ≤ n → 𝒜'.m n = 0) :
    𝒜' = (𝒜'.isCurvedDGAlgebra hG hm₂ (hm 3 le_rfl)).toCurvedAInfinityAlgebra := by
  refine ext (hG.trans (IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_grading _).symm)
    (funext fun n ↦ ?_)
  rcases n with _ | _ | _ | n
  · ext x
    simp
  · ext x
    rw [IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_one_apply, differential_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  · ext x
    rw [IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_two_apply, ← hm₂]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [IsCurvedDGAlgebra.toCurvedAInfinityAlgebra_m_add_three]
    exact hm (n + 3) (by omega)

end CurvedAInfinityAlgebra

end TauCeti
