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
theorem geckWeylUnit_conj_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
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
  have he := S.ad_pow_lie_E_E i j
  simp only [Matrix.transpose_apply, hij] at hh he
  norm_num at he
  -- Normalize the signed-generator triple using its characteristic equations, rather than
  -- unfolding the opaque root-generator definition.
  have triple : IsSl2Triple (φ ((t.lieBasis ht).h i))
      (φ ((t.lieBasis ht).e i)) (φ ((t.lieBasis ht).f i)) := by
    simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
      t.isSl2Triple_geckRepresentation ht i
  have result := triple.weylUnit_conj_of_weight_neg_three
    (by simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl] using
      t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (by simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inr] using
      t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
    (y := φ ((t.lieBasis ht).e j))
    (by
      norm_num [Function.comp_apply] at hh ⊢
      exact hh)
    (by
      simp only [Function.comp_apply] at hf
      rw [← lie_skew, hf, neg_zero])
    (by simpa only [Function.comp_apply, pow_succ, pow_zero, mul_apply_eq_comp,
      one_apply_eq_self, LieAlgebra.ad_apply] using he)
  simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using result

end TauCeti.DynkinType
