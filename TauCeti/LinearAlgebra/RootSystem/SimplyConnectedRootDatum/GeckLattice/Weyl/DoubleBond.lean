/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightTwo
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Double-bond Weyl normalization in the Geck representation

If the simple root at `j` pairs to minus two with the simple coroot at `i`, conjugation by the
pinned Weyl unit at `i` carries the represented raising generator at `j` to its divided second
raising bracket. The factor one half is essential: the reflected root is `αⱼ + 2αᵢ`, and its
normalized vector is not the unscaled iterated bracket. This computes the rational operator
underlying Weyl transport of the corresponding root subgroup; it does not divide by two in a
specialized coefficient ring or identify arbitrary Weyl presentations.

The Cartan matrix here has roots as rows, so the hypothesis is on entry `(j, i)`, not `(i, j)`.
Only this directed entry is needed. In particular the result applies to the double bond of F₄.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups* (2017).
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.

The representation and pinned Weyl unit are those of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic`.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- At a directed Cartan entry minus two, the pinned Geck Weyl unit carries the raising
operator to one half of its second raising bracket. The Cartan convention uses roots as rows. -/
theorem weylUnit_geckRepresentation_conj_of_cartan_eq_neg_two (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -2) :
    (weylUnit (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
        (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i)) :
        Module.End ℚ (t.GeckIndex ht → ℚ)) *
      t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e j)) *
      ↑(weylUnit (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
        (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i)))⁻¹ =
    (2⁻¹ : ℚ) •
      ⁅t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e i)),
        ⁅t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e i)),
          t.geckRepresentation ht
            (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e j))⁆⁆ := by
  let ρ := (t.geckRepresentation ht).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  have hs := (t.isSerreSystem_lieBasis ht).map ρ
  have hij : i ≠ j := by
    intro h
    subst j
    have hd := t.cartanMatrix_apply_same i
    omega
  have hweight : ⁅ρ ((t.lieBasis ht).h i), ρ ((t.lieBasis ht).e j)⁆ =
      (-2 : ℚ) • ρ ((t.lieBasis ht).e j) := by
    have hw := hs.lie_H_E i j
    simp only [Function.comp_apply, Matrix.transpose_apply, hji] at hw
    rw [← Int.cast_smul_eq_zsmul ℚ] at hw
    norm_num at hw
    exact hw.trans (by module)
  have hlower : ⁅ρ ((t.lieBasis ht).f i), ρ ((t.lieBasis ht).e j)⁆ = 0 := by
    have hz := hs.lie_E_F_of_ne j i hij.symm
    simp only [Function.comp_apply] at hz
    rw [← lie_skew, hz, neg_zero]
  have hthird : ⁅ρ ((t.lieBasis ht).e i),
      ⁅ρ ((t.lieBasis ht).e i), ⁅ρ ((t.lieBasis ht).e i), ρ ((t.lieBasis ht).e j)⁆⁆⁆ = 0 := by
    have hz := hs.ad_pow_lie_E_E i j
    norm_num [Function.comp_apply, Matrix.transpose_apply, hji] at hz
    simpa only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp, LieAlgebra.ad_apply] using hz
  have h := (t.isSl2Triple_geckRepresentation ht i).weylUnit_conj_of_lie_eq_neg_two_smul
    (Y := ρ ((t.lieBasis ht).e j))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
  simp only [LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] at h
  -- Expand the local representation composite and the signed-simple generator adapters.
  simpa only [ρ, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
    h hweight hlower hthird

end

end TauCeti.DynkinType
