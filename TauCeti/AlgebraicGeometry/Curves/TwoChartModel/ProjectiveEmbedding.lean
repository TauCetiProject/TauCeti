/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.SectionRing
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Pencil

/-!
# The two-chart model as a closed subscheme of a projective space

Let `F / k` be an algebraic function field, let `z ∈ Fˣ`, and write `D = (z)_∞` for its pole
divisor. The two-chart model of `F` built from `z` is `Proj` of the section ring
`⨁ₙ L(nD)` (`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso`). Suppose that every
positive degree of this section ring is generated in degree one, that is, `L(nD) ⊆ L(D)ⁿ` for
every `n ≠ 0`. Then the graded lift `Sym_k L(D) → ⨁ₙ L(nD)` of the identification of `L(D)` with
the degree-one part is surjective in positive degrees, so `Proj` of the section ring is a closed
subscheme of the projective space `Proj (Sym_k L(D))`
(`AlgebraicGeometry.Proj.isClosedImmersion_map_gradedLift`). Degree zero does not matter, which
is why no exactness of the constants is needed here: `L(0)` is the full constant field of `F`.
This file assembles these into a closed immersion of the two-chart model into `Proj (Sym_k L(D))`
over `k`: the embedding of the curve by the complete linear system of `D`. Since `L(D)` is
finite-dimensional, `Proj (Sym_k L(D))` is a projective space over `k`.

Generation in degree one is a genuine condition on `z`. It holds for every `z` when `F` has genus
zero and `k` is the exact constant field of `F`
(`TauCeti.riemannRochSpace_nsmul_poles_le_pow_of_genus_eq_zero`), for instance for the rational
function field `k(X)`; for `z = X` the space `L(D)` is spanned by `1` and `X`, so the target is the
projective line. In every genus and over any constant field, it holds in positive degrees after
replacing a transcendental `z` by a power `z ^ e` with `e ≥ 1` and `e ≥ 2g`, where `g` is the genus
of `F` over its full constant field (`TauCeti.riemannRochSpace_nsmul_poles_pow_le_pow_of_ne_zero`),
since the pole divisor of `z ^ e` is `e D`.

Since the two-chart model does not depend on the transcendental function it is built from
(`TauCeti.AlgebraicGeometry.twoChartModel.isoOfAlgEquiv`), **every two-chart model is
projective**: it is a closed subscheme over `k` of a projective space `Proj (Sym_k V)` with `V`
finite-dimensional. Every regular proper curve over `k` is the two-chart model of its function
field (`AlgebraicGeometry.Scheme.isoTwoChartModel`), so every regular proper curve is projective
as well. Mathlib has no
class of projective morphisms, so projectivity is stated as the existence of such a closed
immersion over `k`; properness of `Proj (Sym_k V)` over `k` is
`TauCeti.SymmetricAlgebra.instIsProperProjToSpec`.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra`: the morphism from the
  two-chart model built from `z` to `Proj (Sym_k L((z)_∞))`, when the section ring of `(z)_∞` is
  generated in degree one in every positive degree.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra_def`: its defining formula.
* `TauCeti.AlgebraicGeometry.twoChartModel.isClosedImmersion_toProjSymmetricAlgebra`: it is a
  closed immersion.
* `TauCeti.AlgebraicGeometry.twoChartModel.toProjSymmetricAlgebra_projToSpec`: it lies over
  `Spec k`.
* `TauCeti.AlgebraicGeometry.twoChartModel.exists_isClosedImmersion_proj`: **the two-chart
  model of a function field is projective**.
* `AlgebraicGeometry.Scheme.exists_isClosedImmersion_proj`: **a regular proper curve is
  projective**.

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
  (hgen : ∀ n ≠ 0, riemannRochSpace (n • poles hF z) ≤ riemannRochSpace (poles hF z) ^ n)

/-- **The embedding of the two-chart model by the sections of the pole divisor.** If the section
ring of `D = (z)_∞` is generated in degree one in every positive degree, `L(nD) ⊆ L(D)ⁿ` for every
`n ≠ 0`, the two-chart model built from `z`, identified with `Proj` of the section ring, maps to
the projective space `Proj (Sym_k L(D))` by the graded lift of the identification of `L(D)` with
the degree-one part of the section ring. -/
noncomputable def toProjSymmetricAlgebra :
    twoChartModel hF z.ne_zero ⟶
      Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace (poles hF z))) :=
  (sectionRingProjIso hF z).inv ≫
    Proj.map (SymmetricAlgebra.gradedLift k (sectionRingGrade (poles hF z))
        (sectionRingGradeOneEquiv (poles hF z)).toLinearMap)
      (HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range _ fun i hi ↦
        (sectionRingGrade_subset_adjoin_range_sectionRingGradeOneEquiv_iff.mpr
          (hgen i hi.ne')).trans (SymmetricAlgebra.adjoin_range_subset_range_gradedLift k _ _))

/-- The embedding by the sections of `(z)_∞` is the inverse of the identification of the
two-chart model with `Proj` of the section ring, followed by the morphism of projective spectra
induced by the graded lift `Sym_k L((z)_∞) → ⨁ₙ L(n (z)_∞)`. -/
theorem toProjSymmetricAlgebra_def :
    toProjSymmetricAlgebra hF z hgen = (sectionRingProjIso hF z).inv ≫
      Proj.map (SymmetricAlgebra.gradedLift k (sectionRingGrade (poles hF z))
          (sectionRingGradeOneEquiv (poles hF z)).toLinearMap)
        (HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range _ fun i hi ↦
          (sectionRingGrade_subset_adjoin_range_sectionRingGradeOneEquiv_iff.mpr
            (hgen i hi.ne')).trans (SymmetricAlgebra.adjoin_range_subset_range_gradedLift k _ _)) :=
  (rfl)

/-- **The two-chart model is a closed subscheme of a projective space**: when the section ring of
`(z)_∞` is generated in degree one in every positive degree, the embedding by the sections of
`(z)_∞` is a closed immersion. -/
instance isClosedImmersion_toProjSymmetricAlgebra :
    IsClosedImmersion (toProjSymmetricAlgebra hF z hgen) := by
  have := Proj.isClosedImmersion_map_gradedLift (sectionRingGrade (poles hF z)) fun i hi ↦
    sectionRingGrade_subset_adjoin_range_sectionRingGradeOneEquiv_iff.mpr (hgen i hi.ne')
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

/-- **The two-chart model is projective.** Over any field `k`, the two-chart model built from any
transcendental `x` is a closed subscheme, over `k`, of the projective space `Proj (Sym_k V)` of a
finite-dimensional `k`-vector space `V`. -/
theorem exists_isClosedImmersion_proj {x : F} (hx : Transcendental k x) :
    ∃ (V : Submodule k F) (_ : FiniteDimensional k V)
      (f : twoChartModel hF hx.ne_zero ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k V)),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of k)) := by
  -- Embed the model built from `z = x ^ e`, with `e ≥ 1` and `e ≥ 2g` for the genus `g` over the
  -- full constant field, by the sections of `(z)_∞`, and identify it with the model built from `x`.
  let e := 2 * genus (algebraicClosure k F) F + 1
  let z := Units.mk0 x hx.ne_zero ^ e
  have hzt : Transcendental k (z : F) := by
    simpa [z] using hx.pow (Nat.succ_pos _)
  have hgen : ∀ n ≠ 0, riemannRochSpace (n • poles hF z) ≤ riemannRochSpace (poles hF z) ^ n :=
    fun _ hn ↦ riemannRochSpace_nsmul_poles_pow_le_pow_of_ne_zero hF
      (z := Units.mk0 x hx.ne_zero) (by simpa using hx) (Nat.succ_pos _) (Nat.le_succ _) hn
  have := finiteDimensional_riemannRochSpace hF (poles hF z)
  let i := isoOfAlgEquiv hF hF z.ne_zero hx.ne_zero AlgEquiv.refl (hxt := hzt) (hx't := hx)
  have : i.hom.IsOver (Spec (.of k)) := by
    rw [isoOfAlgEquiv_hom]
    infer_instance
  exact ⟨_, inferInstance, i.hom ≫ toProjSymmetricAlgebra hF z hgen, inferInstance,
    inferInstance⟩

end AlgebraicGeometry.twoChartModel

end TauCeti

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **A regular proper curve is projective**: if `X` is a curve over `k` whose codimension-one
local rings are discrete valuation rings, then `X` is a closed subscheme, over `k`, of the
projective space `Proj (Sym_k V)` of a finite-dimensional `k`-vector space `V`. No hypothesis on
the constants of the function field `k(X)` is needed. -/
theorem exists_isClosedImmersion_proj :
    ∃ (V : Submodule k X.functionField) (_ : FiniteDimensional k V)
      (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k V)),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of k)) := by
  have hF := IsCurveOver.isFunctionField (k := k) (X := X)
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  obtain ⟨V, hV, f, hf, hfk⟩ := twoChartModel.exists_isClosedImmersion_proj hF hx
  exact ⟨V, hV, (X.isoTwoChartModel hx.ne_zero hx).hom ≫ f, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
