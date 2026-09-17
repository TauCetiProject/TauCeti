/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ArrowIdealPresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix

/-!
# The zigzag algebra of `A₂`

The one-edge graph `A₂` is one of the two low-rank exceptions of zigzag theory. Its doubled quiver
has two vertices and one arrow in each direction, so it has no length-two path with distinct
endpoints and only one backtrack at each vertex: every quadratic zigzag relator vanishes. The
zigzag algebra of `A₂` is therefore not a quadratic algebra. It is instead the
**arrow-ideal-cube-zero** quotient

```text
Z(A₂) = k DQ / R³,
```

of the path algebra of the doubled quiver `DQ` by the cube of its arrow ideal `R`, and the cubic
relations cannot be omitted: the quotient by the quadratic relations alone is the whole path
algebra of the doubled quiver, which is infinite-dimensional because the doubled quiver has
oriented cycles.

The graph is read from the Bourbaki-numbered Cartan matrix of `A₂`, and the general theorems then
give the remaining invariants: dimension `6` (a basis of two idempotents, two arrows and two
volume classes), centre of dimension `3`, and graded Cartan matrix

```text
C_A₂(q) = [1 + q²    q   ]
          [   q    1 + q²].
```

## Main definitions

* `TauCeti.nonisolatedZigzagQuotientEquivA2` and `TauCeti.zigzagAlgebraEquivA2`: the relation
  quotient and the public zigzag algebra of `A₂` are the quotient `k DQ / R³`.

## Main results

* `TauCeti.quadraticZigzagIdeal_A2_eq_bot`: every quadratic zigzag relator of `A₂` vanishes.
* `TauCeti.zigzagIdeal_A2_eq_arrowIdeal_pow_three`: the zigzag ideal of `A₂` is `R³`.
* `TauCeti.jacobson_pow_three_zigzagAlgebra_A2_eq_bot`: the Jacobson radical of the zigzag algebra
  of `A₂` has cube zero.
* `TauCeti.not_module_finite_quotient_quadraticZigzagIdeal_A2`: the quotient by the quadratic
  relations alone is not a finite module.
* `TauCeti.quadraticZigzagIdeal_A2_ne_zigzagIdeal_A2`: the quadratic relators do not generate the
  zigzag ideal.
* `TauCeti.finrank_zigzagAlgebra_A2`, `TauCeti.finrank_center_zigzagAlgebra_A2` and
  `TauCeti.zigzagGradedCartanMatrix_A2_eq`: the dimension, the centre dimension and the graded
  Cartan matrix.

## References

The low-rank convention for `A₂` follows Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3, and Liu--Wang, *A-infinity deformations of zigzag algebras via
Ginzburg dg algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe w

/-! ### The arrow-ideal-cube-zero presentation -/

variable (k : Type w) [CommRing k]

/-- In `A₂` every vertex has at most one neighbour. -/
theorem subsingleton_neighborSet_A2 (i : Fin 2) :
    (zigzagA2Graph.neighborSet i).Subsingleton := by
  intro j hj j' hj'
  rw [SimpleGraph.mem_neighborSet, zigzagA2Graph_adj] at hj hj'
  omega

/-- **The quadratic zigzag relators of `A₂` all vanish**: there is no length-two path between the
two distinct nodes, and each node carries a single backtrack. -/
theorem quadraticZigzagIdeal_A2_eq_bot : quadraticZigzagIdeal k zigzagA2Graph = ⊥ :=
  quadraticZigzagIdeal_eq_bot k subsingleton_neighborSet_A2

/-- **The zigzag ideal of `A₂` is the cube of the arrow ideal**: the zigzag algebra of `A₂` is
the quotient of its doubled path algebra by the cube of the arrow ideal. -/
theorem zigzagIdeal_A2_eq_arrowIdeal_pow_three :
    (zigzagIdeal k zigzagA2Graph).asIdeal = arrowIdeal k (DoubledQuiver zigzagA2Graph) ^ 3 :=
  asIdeal_zigzagIdeal_eq_arrowIdeal_pow k subsingleton_neighborSet_A2

/-- The zigzag relation quotient of `A₂` is the quotient of its doubled path algebra by the cube
of the arrow ideal. -/
noncomputable def nonisolatedZigzagQuotientEquivA2 :
    nonisolatedZigzagQuotient k zigzagA2Graph ≃ₐ[k]
      pathAlgebra k (DoubledQuiver zigzagA2Graph) ⧸
        arrowIdeal k (DoubledQuiver zigzagA2Graph) ^ 3 :=
  nonisolatedZigzagQuotientEquivArrowIdealPow k subsingleton_neighborSet_A2

/-- The cubic-quotient comparison fixes the class of every element of the path algebra. -/
@[simp]
theorem nonisolatedZigzagQuotientEquivA2_zigzagMk
    (x : pathAlgebra k (DoubledQuiver zigzagA2Graph)) :
    nonisolatedZigzagQuotientEquivA2 k (zigzagMk k zigzagA2Graph x) = Ideal.Quotient.mk _ x := by
  simpa only [nonisolatedZigzagQuotientEquivA2] using
    nonisolatedZigzagQuotientEquivArrowIdealPow_zigzagMk k subsingleton_neighborSet_A2 x

/-- **The public zigzag algebra of `A₂`** is the quotient `k DQ / R³` of the path algebra of its
doubled quiver. -/
noncomputable def zigzagAlgebraEquivA2 :
    zigzagAlgebra k zigzagA2Graph ≃ₐ[k]
      pathAlgebra k (DoubledQuiver zigzagA2Graph) ⧸
        arrowIdeal k (DoubledQuiver zigzagA2Graph) ^ 3 :=
  (zigzagAlgebraEquivNonisolated k zigzagA2Graph connected_zigzagA2Graph).trans
    (nonisolatedZigzagQuotientEquivA2 k)

/-- The `A₂` comparison evaluates through the unique connected-component factor. -/
@[simp]
theorem zigzagAlgebraEquivA2_apply (x : zigzagAlgebra k zigzagA2Graph) :
    zigzagAlgebraEquivA2 k x =
      nonisolatedZigzagQuotientEquivA2 k
        (let _ := nontrivial_connectedComponent zigzagA2Graph connected_zigzagA2Graph default
        nonisolatedZigzagQuotientEquiv k
          (connectedComponentGraphIso zigzagA2Graph connected_zigzagA2Graph default)
          (zigzagComponentAlgebraEquivNonisolated k zigzagA2Graph default
            (zigzagComponentProjection k zigzagA2Graph default x))) := by
  rw [zigzagAlgebraEquivA2, AlgEquiv.trans_apply,
    zigzagAlgebraEquivNonisolated_apply k zigzagA2Graph connected_zigzagA2Graph x default]

/-- The inverse `A₂` comparison is computed componentwise by the inverse quotient and component
equivalences. -/
@[simp]
theorem zigzagAlgebraEquivA2_symm_apply_component
    (x : pathAlgebra k (DoubledQuiver zigzagA2Graph) ⧸
      arrowIdeal k (DoubledQuiver zigzagA2Graph) ^ 3)
    (C : zigzagA2Graph.ConnectedComponent) :
    zigzagComponentProjection k zigzagA2Graph C ((zigzagAlgebraEquivA2 k).symm x) =
      let _ := nontrivial_connectedComponent zigzagA2Graph connected_zigzagA2Graph C
      (zigzagComponentAlgebraEquivNonisolated k zigzagA2Graph C).symm
        ((nonisolatedZigzagQuotientEquiv k
          (connectedComponentGraphIso zigzagA2Graph connected_zigzagA2Graph C)).symm
            ((nonisolatedZigzagQuotientEquivA2 k).symm x)) := by
  rw [zigzagAlgebraEquivA2, AlgEquiv.symm_trans_apply]
  exact zigzagAlgebraEquivNonisolated_symm_apply_component k zigzagA2Graph
    connected_zigzagA2Graph ((nonisolatedZigzagQuotientEquivA2 k).symm x) C

/-- The inverse `A₂` presentation sends the class of a path-algebra element through the public
comparison with the zigzag relation quotient. -/
@[simp]
theorem zigzagAlgebraEquivA2_symm_mk (x : pathAlgebra k (DoubledQuiver zigzagA2Graph)) :
    (zigzagAlgebraEquivA2 k).symm
        (Ideal.Quotient.mk (arrowIdeal k (DoubledQuiver zigzagA2Graph) ^ 3) x) =
      (zigzagAlgebraEquivNonisolated k zigzagA2Graph connected_zigzagA2Graph).symm
        (zigzagMk k zigzagA2Graph x) := by
  rw [AlgEquiv.symm_apply_eq, zigzagAlgebraEquivA2, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply, nonisolatedZigzagQuotientEquivA2_zigzagMk]

/-- **The Jacobson radical of the zigzag algebra of `A₂` has cube zero.** -/
theorem jacobson_pow_three_zigzagAlgebra_A2_eq_bot (k : Type w) [Field k] :
    Ring.jacobson (zigzagAlgebra k zigzagA2Graph) ^ 3 = ⊥ := by
  let e := zigzagAlgebraEquivNonisolated k zigzagA2Graph connected_zigzagA2Graph
  let _ : RingHomSurjective e.toRingEquiv.toRingHom := ⟨e.surjective⟩
  have he : Submodule.map e.toAlgHom.toLinearMap
      (Submodule.restrictScalars k (Ring.jacobson (zigzagAlgebra k zigzagA2Graph))) =
      Submodule.restrictScalars k
        (Ring.jacobson (nonisolatedZigzagQuotient k zigzagA2Graph)) := by
    ext y
    exact SetLike.ext_iff.mp
      (Ring.map_jacobson_of_ker_le (f := e.toRingEquiv.toRingHom) (by simp)) y
  apply (Submodule.restrictScalars_eq_bot_iff k _ _).mp
  rw [Submodule.restrictScalars_pow (by omega),
    ← Submodule.map_eq_bot_iff (e := e.toLinearEquiv), ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow, he, ← Submodule.restrictScalars_pow (by omega),
    jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot exists_adj_zigzagA2Graph,
    Submodule.restrictScalars_bot]

/-- **The cubic relations of `A₂` cannot be omitted.** Over a nonzero ring, the quotient of the
doubled path algebra of `A₂` by the quadratic zigzag relations alone is not a finite module: those
relations all vanish, and the doubled quiver has oriented cycles. -/
theorem not_module_finite_quotient_quadraticZigzagIdeal_A2 [Nontrivial k] :
    ¬ Module.Finite k (pathAlgebra k (DoubledQuiver zigzagA2Graph) ⧸
      (quadraticZigzagIdeal k zigzagA2Graph).asIdeal) :=
  not_module_finite_quotient_quadraticZigzagIdeal k subsingleton_neighborSet_A2
    (i := 0) (j := 1) (by simp)

/-- **The quadratic relators do not generate the zigzag ideal of `A₂`**: the quotient by the
zigzag ideal is a finitely generated module, while the quotient by the quadratic relators is not. -/
theorem quadraticZigzagIdeal_A2_ne_zigzagIdeal_A2 [Nontrivial k] :
    quadraticZigzagIdeal k zigzagA2Graph ≠ zigzagIdeal k zigzagA2Graph :=
  fun h => not_module_finite_quotient_quadraticZigzagIdeal_A2 k <| by
    rw [h]
    exact Module.Finite.equiv (zigzagAlgebraEquivNonisolated k zigzagA2Graph
      connected_zigzagA2Graph).toLinearEquiv

/-! ### Dimensions and the graded Cartan matrix -/

/-- **The zigzag algebra of `A₂` has dimension `6`**: two idempotents, two arrows and two volume
classes. -/
theorem finrank_zigzagAlgebra_A2 [Nontrivial k] :
    Module.finrank k (zigzagAlgebra k zigzagA2Graph) = 6 := by
  rw [finrank_zigzagAlgebra]
  simp

/-- The vertex, arrow and volume basis of the zigzag relation quotient of `A₂` has six
elements. -/
theorem card_zigzagBasisIndex_A2 : Fintype.card (ZigzagBasisIndex zigzagA2Graph) = 6 := by
  simp [ZigzagBasisIndex, zigzagA2Graph.dart_card_eq_twice_card_edges]

/-- **The centre of the zigzag algebra of `A₂` has dimension `3`**, spanned by `1` and the two
volume classes. -/
@[simp high]
theorem finrank_center_zigzagAlgebra_A2 [Nontrivial k] :
    Module.finrank k (Subalgebra.center k (zigzagAlgebra k zigzagA2Graph)) = 3 := by
  rw [finrank_center_zigzagAlgebra_of_connected k zigzagA2Graph connected_zigzagA2Graph]
  simp

/-- **The graded Cartan matrix of the `A₂` zigzag algebra.** -/
theorem zigzagGradedCartanMatrix_A2_eq (k : Type w) [Field k] :
    zigzagGradedCartanMatrix k zigzagA2Graph = !![1 + X ^ 2, X; X, 1 + X ^ 2] := by
  ext i j
  rw [zigzagGradedCartanMatrix_apply k zigzagA2Graph exists_adj_zigzagA2Graph]
  fin_cases i <;> fin_cases j <;> simp

end TauCeti
