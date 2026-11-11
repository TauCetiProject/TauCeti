/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre.DoubleBond
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
  -- Expand the representation composite and signed generators; the Serre matrix is transposed.
  simpa only [Function.comp_apply, ρ, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
    ((t.isSerreSystem_lieBasis ht).map ρ).weylUnit_conj_of_cartan_eq_neg_two
      (t.cartanMatrix_apply_same i) hji
      (by simpa only [Function.comp_apply, ρ, LieHom.comp_apply, AlgHom.toLieHom_apply,
          LieAlgebra.Basis.rootGenerator_inl] using
        t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
      (by simpa only [Function.comp_apply, ρ, LieHom.comp_apply, AlgHom.toLieHom_apply,
          LieAlgebra.Basis.rootGenerator_inr] using
        t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))

end

end TauCeti.DynkinType
