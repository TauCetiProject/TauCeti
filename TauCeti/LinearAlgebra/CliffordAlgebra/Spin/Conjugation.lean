/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection

/-!
# Conjugation of Spin root subgroups

The functoriality comparisons in `TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map` show that
the isometry induced by a Spin element `g` acts on its Clifford algebra by conjugation by `g`.
Consequently its induced Spin automorphism is the inner automorphism `MulAut.conj g`.
Equality of the orthogonal projections alone would not identify these automorphisms, because
the projection can have a nontrivial scalar kernel.

For the canonical Eichler lifts `L_{u,w} = 1 + ι w * ι u`, this gives
`g * L_{u,w} * g⁻¹ = L_{g u,g w}`. The same law holds for the whole homomorphism out of
`u^⊥ / K ∙ u`, and conjugation carries its image onto the root subgroup attached to `g u`.
These comparisons let one manipulate the lifted root subgroups inside Spin itself.

The canonical transvection lifts require a nondegenerate form over a field with `2` invertible;
finite dimensionality is not needed. The proofs use the existing isometric transport of
`spinTransvectionHom`.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia (1954), Chapter II.
-/

public section

open TauCeti QuadraticMap

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V} {u w : V}

/-- Conjugating the canonical Spin lift transports both vectors by the Spin vector action. -/
theorem spinTransvection_conj (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (huw : polar Q u w = 0) (g : spinGroup Q) :
    g * spinTransvection hQ hu huw * g⁻¹ =
      spinTransvection (u := spinVectorAction Q g u) (w := spinVectorAction Q g w) hQ
        (by simpa using hu)
        (by
          rw [← coe_spinToOrthogonal_apply Q g u, ← coe_spinToOrthogonal_apply Q g w,
            TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (spinToOrthogonal Q g).2]
          exact huw) := by
  let e := TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q (spinToOrthogonal Q g)
  have h := e.spinGroupEquiv_spinTransvection hQ hu huw
  rw [spinGroup.spinGroupEquiv_vectorAction g] at h
  simpa only [e, MulAut.conj_apply,
    TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv,
    coe_spinToOrthogonal_apply] using h

/-- Inner conjugation transports the entire lifted Eichler root-subgroup homomorphism,
with parameters transported by the vector action on the quotient. -/
theorem conj_comp_spinTransvectionHom (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (g : spinGroup Q) :
    (MulAut.conj g).toMonoidHom.toAdditive.comp (spinTransvectionHom hQ hu) =
      (spinTransvectionHom hQ
        (((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
          (spinToOrthogonal Q g)).map_app u).trans hu)).comp
        ((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
          (spinToOrthogonal Q g)).transvectionParameterEquiv u).toLinearMap.toAddMonoidHom := by
  rw [← spinGroup.spinGroupEquiv_vectorAction g]
  exact (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
    (spinToOrthogonal Q g)).spinGroupEquiv_comp_spinTransvectionHom hQ hu

/-- Conjugation carries the lifted Eichler root subgroup onto the root subgroup attached
to the transported isotropic vector. -/
theorem map_spinTransvectionHom_range_conj (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (g : spinGroup Q) :
    (spinTransvectionHom hQ hu).range.map (MulAut.conj g).toMonoidHom.toAdditive =
      (spinTransvectionHom hQ
        (((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
          (spinToOrthogonal Q g)).map_app u).trans hu)).range := by
  rw [AddMonoidHom.map_range, conj_comp_spinTransvectionHom, AddMonoidHom.range_comp]
  have hsurj : Function.Surjective
      ((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
        (spinToOrthogonal Q g)).transvectionParameterEquiv u).toLinearMap.toAddMonoidHom :=
    ((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
      (spinToOrthogonal Q g)).transvectionParameterEquiv u).surjective
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddMonoidHom.range_eq_map]

end CliffordAlgebra
