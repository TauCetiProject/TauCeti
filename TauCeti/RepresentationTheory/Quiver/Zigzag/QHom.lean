/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Hom

/-!
# The projective q-Hom form of a zigzag algebra

For a finite simple graph without isolated vertices, this file packages the homogeneous
homomorphisms between zigzag vertex projectives into Laurent polynomials.  With the internal
shift convention `M{d}_p = M_{p-d}`, the value

```text
qHom(P_i, P_j) = ∑_d dim_k Hom(P_i, P_j{d}) q⁻ᵈ
```

has finite support: target shifts outside `[-2, 0]` vanish.  It is the Laurent image of the
graded Cartan entry, hence its matrix is `(1 + q²)I + qA_G`.

The matrix also defines a sesquilinear form on the free Laurent module with basis the vertices.
The Laurent involution `q ↦ q⁻¹` acts in the first variable, as shifting the source of a Hom
space reverses the shift.  This is the coordinate form of the projective q-Hom pairing; it does
not assert a presentation of the full graded Grothendieck group.

## Main definitions

* `TauCeti.zigzagProjectiveQHom`: the Laurent-valued graded dimension of
  `Hom(P_i, P_j{d})`.
* `TauCeti.zigzagProjectiveQHomMatrix`: its matrix in the vertex-projective basis.
* `TauCeti.zigzagProjectiveQHomForm`: the resulting sesquilinear form on vertex coordinates.

## Main results

* `TauCeti.zigzagProjectiveQHom_eq_toLaurent`: q-Hom is the Laurent image of the graded Cartan
  entry.
* `TauCeti.zigzagProjectiveQHomMatrix_apply`: its entries are `1 + q²` on the diagonal, `q`
  on edges, and zero elsewhere.
* `TauCeti.zigzagProjectiveQHomForm_single`: the form on two vertex basis vectors is the
  corresponding projective q-Hom value.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2, for the quantum Cartan
matrix of a zigzag algebra.
-/

public section

namespace TauCeti

open LaurentPolynomial Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### Finite support and the q-Hom polynomial -/

/-- The target-shifted homomorphism spaces between two zigzag vertex projectives have finite
Laurent support.  More precisely, only shifts `-2`, `-1`, and `0` can contribute. -/
theorem zigzagProjectiveTargetShiftHomFiniteSupport
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    HasFiniteLaurentSupport k (fun d : ℤ => zigzagProjectiveTargetShiftHom k G i j d) := by
  let _ : Finite G.Dart :=
    Finite.of_injective _ (SimpleGraph.Dart.toProd_injective (G := G))
  let _ : Module.Finite k (nonisolatedZigzagQuotient k G) :=
    Module.Finite.of_basis (zigzagBasis k G hns)
  refine HasFiniteLaurentSupport.of_finset (fun d => ?_) ({0, -1, -2} : Finset ℤ) ?_
  · exact Module.Finite.equiv
      (zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner k G i j d).symm
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    rcases lt_or_gt_of_ne hd.1 with hneg | hpos
    · have hlt : d < -2 := by omega
      rw [zigzagProjectiveTargetShiftHom_eq_bot_of_lt_neg_two k G i j hlt]
      infer_instance
    · have hpos' : 0 < d := by omega
      rw [zigzagProjectiveTargetShiftHom_eq_bot_of_pos k G i j hpos']
      infer_instance

/-- The **projective q-Hom value** between the zigzag vertex projectives `P_i` and `P_j`:
the Laurent polynomial `∑_d dim_k Hom(P_i, P_j{d}) q⁻ᵈ`. -/
noncomputable def zigzagProjectiveQHom (hns : ∀ i : V, ∃ j, G.Adj i j)
    (i j : V) : LaurentPolynomial ℤ :=
  targetShiftGradedDimension k (fun d : ℤ => zigzagProjectiveTargetShiftHom k G i j d)
    (zigzagProjectiveTargetShiftHomFiniteSupport k G hns i j)

/-- The coefficient of `qⁿ` in projective q-Hom is the dimension of the target-shifted Hom
space with shift `-n`. -/
@[simp]
theorem coeff_zigzagProjectiveQHom (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) (n : ℤ) :
    (zigzagProjectiveQHom k G hns i j).coeff n =
      Module.finrank k (zigzagProjectiveTargetShiftHom k G i j (-n)) := by
  rw [zigzagProjectiveQHom, coeff_targetShiftGradedDimension]

/-- At a nonnegative exponent, projective q-Hom records the degree-raising Hom space
`Hom(P_i{n}, P_j)`. -/
@[simp]
theorem coeff_zigzagProjectiveQHom_ofNat (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) (n : ℕ) :
    (zigzagProjectiveQHom k G hns i j).coeff n =
      Module.finrank k (zigzagProjectiveHomOfDegree k G i j n) := by
  rw [coeff_zigzagProjectiveQHom, zigzagProjectiveTargetShiftHom_neg_ofNat]

/-- **Projective q-Hom is the Laurent image of the graded Cartan entry.** -/
theorem zigzagProjectiveQHom_eq_toLaurent (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    zigzagProjectiveQHom k G hns i j =
      Polynomial.toLaurent (zigzagGradedCartanMatrix k G i j) := by
  rw [zigzagProjectiveQHom,
    targetShiftGradedDimension_eq_sum _ ({0, -1, -2} : Finset ℤ)]
  · rw [zigzagGradedCartanMatrix_eq_sum_finrank_zigzagProjectiveHomOfDegree]
    norm_num [zigzagProjectiveTargetShiftHom_neg_ofNat, Finset.sum_insert,
      Finset.sum_range_succ]
    let H := zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j
    have hzero : Module.finrank k (zigzagProjectiveTargetShiftHom k G i j 0) =
        Module.finrank k (zigzagProjectiveHomOfDegree k G i j 0) := by
      have h := congrArg (fun S : Submodule k H => Module.finrank k S)
        (zigzagProjectiveTargetShiftHom_neg_ofNat k G i j 0)
      exact h
    have hone : Module.finrank k (zigzagProjectiveTargetShiftHom k G i j (-1)) =
        Module.finrank k (zigzagProjectiveHomOfDegree k G i j 1) := by
      have h := congrArg (fun S : Submodule k H => Module.finrank k S)
        (zigzagProjectiveTargetShiftHom_neg_ofNat k G i j 1)
      exact h
    have htwo : Module.finrank k (zigzagProjectiveTargetShiftHom k G i j (-2)) =
        Module.finrank k (zigzagProjectiveHomOfDegree k G i j 2) := by
      have h := congrArg (fun S : Submodule k H => Module.finrank k S)
        (zigzagProjectiveTargetShiftHom_neg_ofNat k G i j 2)
      exact h
    rw [hzero, hone, htwo]
    ring
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    rcases lt_or_gt_of_ne hd.1 with hneg | hpos
    · rw [zigzagProjectiveTargetShiftHom_eq_bot_of_lt_neg_two k G i j (by omega)]
      infer_instance
    · rw [zigzagProjectiveTargetShiftHom_eq_bot_of_pos k G i j (by omega)]
      infer_instance

/-! ### Matrix and sesquilinear form -/

/-- The matrix of projective q-Hom values in the vertex-projective basis. -/
noncomputable def zigzagProjectiveQHomMatrix (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Matrix V V (LaurentPolynomial ℤ) :=
  Matrix.of fun i j => zigzagProjectiveQHom k G hns i j

/-- An entry of the projective q-Hom matrix is the q-Hom value of the corresponding pair of
vertex projectives. -/
@[simp]
theorem zigzagProjectiveQHomMatrix_apply_eq_qHom (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    zigzagProjectiveQHomMatrix k G hns i j = zigzagProjectiveQHom k G hns i j :=
  by rw [zigzagProjectiveQHomMatrix, Matrix.of_apply]

/-- The q-Hom matrix is the entrywise Laurent image of the graded Cartan matrix. -/
theorem zigzagProjectiveQHomMatrix_eq_map_toLaurent (hns : ∀ i : V, ∃ j, G.Adj i j) :
    zigzagProjectiveQHomMatrix k G hns =
      (zigzagGradedCartanMatrix k G).map Polynomial.toLaurent := by
  ext i j
  rw [zigzagProjectiveQHomMatrix_apply_eq_qHom, Matrix.map_apply,
    zigzagProjectiveQHom_eq_toLaurent]

section Nonisolated

variable (hns : ∀ i : V, ∃ j, G.Adj i j)

variable [DecidableEq V] [DecidableRel G.Adj]

/-- **The entrywise projective q-Hom formula.** It is `1 + q²` on the diagonal, `q` on an
edge, and zero otherwise. -/
theorem zigzagProjectiveQHomMatrix_apply (i j : V) :
    zigzagProjectiveQHomMatrix k G hns i j =
      (if i = j then 1 + T 2 else 0) + if G.Adj i j then T 1 else 0 := by
  rw [zigzagProjectiveQHomMatrix_apply_eq_qHom, zigzagProjectiveQHom_eq_toLaurent,
    zigzagGradedCartanMatrix_apply k G hns, map_add]
  split_ifs <;> simp

/-- **The projective q-Hom matrix is `(1 + q²)I + qA_G`.** -/
theorem zigzagProjectiveQHomMatrix_eq :
    zigzagProjectiveQHomMatrix k G hns =
      (1 + T 2 : LaurentPolynomial ℤ) • (1 : Matrix V V (LaurentPolynomial ℤ)) +
        (T 1 : LaurentPolynomial ℤ) • G.adjMatrix (LaurentPolynomial ℤ) := by
  ext i j
  rw [zigzagProjectiveQHomMatrix_apply k G hns, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

variable [Fintype V]

/-- The **projective q-Hom form** on Laurent-polynomial vertex coordinates.  It is semilinear in
the first variable for `q ↦ q⁻¹` and linear in the second. -/
noncomputable def zigzagProjectiveQHomForm :
    (V → LaurentPolynomial ℤ) →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      (V → LaurentPolynomial ℤ) →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  Matrix.toLinearMapₛₗ₂' (LaurentPolynomial ℤ)
    (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom (RingHom.id _)
      (zigzagProjectiveQHomMatrix k G hns)

omit [DecidableRel G.Adj] in
/-- On vertex basis vectors, the projective q-Hom form is the q-Hom value of the corresponding
vertex projectives. -/
@[simp]
theorem zigzagProjectiveQHomForm_single (i j : V) :
    zigzagProjectiveQHomForm k G hns (Pi.single i 1) (Pi.single j 1) =
      zigzagProjectiveQHom k G hns i j := by
  rw [zigzagProjectiveQHomForm, Matrix.toLinearMapₛₗ₂'_single,
    zigzagProjectiveQHomMatrix_apply_eq_qHom]

end Nonisolated

end TauCeti
