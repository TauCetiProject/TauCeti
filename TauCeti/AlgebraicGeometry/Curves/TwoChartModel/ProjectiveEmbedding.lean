/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.SectionRing
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# The two-chart model as a closed subscheme of a projective space

Let `F / k` be an algebraic function field, let `z ∈ Fˣ`, and write `D = (z)_∞` for its pole
divisor. The two-chart model of `F` built from `z` is `Proj` of the section ring
`⨁ₙ L(nD)` (`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso`). Suppose that this
section ring is generated in degree one, that is, `L(nD) ⊆ L(D)ⁿ` for every `n`. Then the
graded lift `Sym_k L(D) → ⨁ₙ L(nD)` of the identification of `L(D)` with the degree-one part is
surjective, so `Proj` of the section ring is a closed subscheme of the projective space
`Proj (Sym_k L(D))` (`AlgebraicGeometry.Proj.isClosedImmersion_map_gradedLift`). This file
assembles these into a closed immersion of the two-chart model into `Proj (Sym_k L(D))` over `k`:
the embedding of the curve by the complete linear system of `D`. Since `L(D)` is
finite-dimensional, `Proj (Sym_k L(D))` is a projective space over `k`.

Generation in degree one is a genuine condition on `z`. It holds for every `z` when `F` has genus
zero and `k` is the exact constant field of `F`
(`TauCeti.riemannRochSpace_nsmul_poles_le_pow_of_genus_eq_zero`), for instance for the rational
function field `k(X)`; for `z = X` the space `L(D)` is spanned by `1` and `X`, so the target is the
projective line. For arbitrary genus and exact constants, it holds after replacing `z` by a
suitable power `z ^ e` whenever the section ring is finitely generated
(`TauCeti.Divisor.exists_riemannRochSpace_mul_eq_pow`), since the pole divisor of `z ^ e` is
`e D`.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra`: the morphism from the
  two-chart model built from `z` to `Proj (Sym_k L((z)_∞))`, when the section ring of `(z)_∞` is
  generated in degree one.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra_def`: its defining formula.
* `TauCeti.AlgebraicGeometry.twoChartModel.isClosedImmersion_toProjSymmetricAlgebra`: it is a
  closed immersion.
* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra_projToSpec`: it lies over
  `Spec k`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise II.3.12 and
  Section IV.3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

namespace AlgebraicGeometry.twoChartModel

open Divisor

variable (hF : IsFunctionField k F) (z : Fˣ)
  (hgen : ∀ n : ℕ, riemannRochSpace (n • poles hF z) ≤ riemannRochSpace (poles hF z) ^ n)

/-- **The embedding of the two-chart model by the sections of the pole divisor.** If the section
ring of `D = (z)_∞` is generated in degree one, `L(nD) ⊆ L(D)ⁿ` for every `n`, the two-chart model
built from `z`, identified with `Proj` of the section ring, maps to the projective space
`Proj (Sym_k L(D))` by the graded lift of the identification of `L(D)` with the degree-one part of
the section ring. -/
noncomputable def toProjSymmetricAlgebra :
    twoChartModel hF z.ne_zero ⟶
      Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace (poles hF z))) :=
  (sectionRingProjIso hF z).inv ≫
    Proj.map (SymmetricAlgebra.gradedLift k (sectionRingGrade (poles hF z))
        (sectionRingGradeOneEquiv (poles hF z)).toLinearMap)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _
        (SymmetricAlgebra.gradedLift_surjective k _
          (adjoin_range_sectionRingGradeOneEquiv_eq_top_iff.mpr hgen)))

/-- The embedding by the sections of `(z)_∞` is the inverse of the identification of the
two-chart model with `Proj` of the section ring, followed by the morphism of projective spectra
induced by the graded lift `Sym_k L((z)_∞) → ⨁ₙ L(n (z)_∞)`. -/
theorem toProjSymmetricAlgebra_def :
    toProjSymmetricAlgebra hF z hgen = (sectionRingProjIso hF z).inv ≫
      Proj.map (SymmetricAlgebra.gradedLift k (sectionRingGrade (poles hF z))
          (sectionRingGradeOneEquiv (poles hF z)).toLinearMap)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          (SymmetricAlgebra.gradedLift_surjective k _
            (adjoin_range_sectionRingGradeOneEquiv_eq_top_iff.mpr hgen))) :=
  (rfl)

/-- **The two-chart model is a closed subscheme of a projective space**: when the section ring of
`(z)_∞` is generated in degree one, the embedding by the sections of `(z)_∞` is a closed
immersion. -/
instance isClosedImmersion_toProjSymmetricAlgebra :
    IsClosedImmersion (toProjSymmetricAlgebra hF z hgen) := by
  have := Proj.isClosedImmersion_map_gradedLift (sectionRingGrade (poles hF z))
    (adjoin_range_sectionRingGradeOneEquiv_eq_top_iff.mpr hgen)
  rw [toProjSymmetricAlgebra_def]
  infer_instance

/-- The embedding by the sections of `(z)_∞` lies over `Spec k`: followed by the coefficient
morphism of the projective space, it is the structure morphism of the two-chart model. -/
@[reassoc (attr := simp)]
theorem toProjSymmetricAlgebra_projToSpec :
    toProjSymmetricAlgebra hF z hgen ≫
        TauCeti.SymmetricAlgebra.projToSpec k (riemannRochSpace (poles hF z)) =
      twoChartModel hF z.ne_zero ↘ Spec (.of k) := by
  rw [toProjSymmetricAlgebra_def, Category.assoc, TauCeti.SymmetricAlgebra.projToSpec_def,
    ← Proj.toSpecCoeff_def,
    Proj.map_toSpecCoeff _ _ _ (SymmetricAlgebra.gradedLift_gradedZeroRingHom_algebraMap k _ _),
    Iso.inv_comp_eq, sectionRingProjIso_hom_over]

instance : (toProjSymmetricAlgebra hF z hgen).IsOver (Spec (.of k)) :=
  ⟨toProjSymmetricAlgebra_projToSpec hF z hgen⟩

end AlgebraicGeometry.twoChartModel

end TauCeti
