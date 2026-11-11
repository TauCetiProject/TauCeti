/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Triple-bond Weyl normalization in the Geck representation

The numbered Weyl unit at node `i` conjugates the raising operator at node `j` to one sixth
of its third bracket with the raising operator at `i`, when the root-row Cartan entry
`(j,i)` is minus three. This is the normalization at the triple bond of G₂. It identifies
the operator, including its scalar, not only its root label.

The result is a rational operator identity. It makes no division by six in a specialized
coefficient ring and asserts neither an integral root-subgroup comparison nor an identification
of the carrier with a pinned group scheme.

The operators and Weyl units come from `DynkinType.geckRepresentation` and
`DynkinType.isSl2Triple_geckRepresentation`. The proof transports the existing numbered Serre
system, whose matrix is the transpose of the root-row Cartan matrix.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233–3247.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-- At a directed Cartan entry minus three, the pinned Geck Weyl unit sends the raising
operator to its third raising bracket divided by six. The Cartan matrix has roots as rows,
so the hypothesis is on `(j,i)`, not `(i,j)`. -/
theorem weylUnit_conj_geckRepresentation_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hij : t.cartanMatrix j i = -3) :
    let E := fun k => t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inl k)))
    let n := weylUnit (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
      (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
    (n : Module.End ℚ (t.GeckIndex ht → ℚ)) * E j *
        (↑n⁻¹ : Module.End ℚ (t.GeckIndex ht → ℚ)) =
      (6⁻¹ : ℚ) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆ := by
  -- Compose the enveloping-algebra representation with its canonical Lie map, so that the
  -- existing Serre transport theorem applies directly to the represented generators.
  let φ := (t.geckRepresentation ht).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let S := (t.isSerreSystem_lieBasis ht).map φ
  have hne : i ≠ j := by
    rintro rfl
    have := t.cartanMatrix_apply_same i
    omega
  have hh := S.lie_H_E i j
  have hf := S.lie_E_F_of_ne j i hne.symm
  -- Remove the composed Lie-map wrappers before using the operator-level normalization.
  simp only [Matrix.transpose_apply, hij, Function.comp_apply, φ, LieHom.comp_apply,
    AlgHom.toLieHom_apply] at hh hf
  -- Normalize the signed-generator triple using its characteristic equations, rather than
  -- unfolding the opaque root-generator definition.
  have triple := t.isSl2Triple_geckRepresentation ht i
  have hE := t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i)
  have hF := t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i)
  simp only [LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr]
    at triple hE hF ⊢
  exact triple.weylUnit_conj_of_weight_neg_three hE hF
    (y := t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).e j)))
    (by
      norm_num at hh ⊢
      exact hh)
    (by rw [← lie_skew, hf, neg_zero])

end TauCeti.DynkinType
