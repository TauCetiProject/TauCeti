/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.FinitePresentation
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap

/-!
# The projective compactification of the affine line

The standard chart `D₊(X₀)` realizes `Spec R[X]` as a schematically dense open subscheme of
`ℙ¹_R` for every commutative ring `R`. Together with the proper structure morphism this gives
`projectiveLine.denseCompactification`, retaining the scheme structure over nonreduced bases.

The infinity-section and boundary geometry are in
`TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine`. This module supplies the
compactification, the equations identifying its ambient scheme, interior map and proper map, and
its behaviour under change of base ring. Since `ℙ¹_R` is smooth over `R`, the compactification is
finitely presented (`projectiveLine.fpCompactificationProperty_denseCompactification`). Along
`Spec S ⟶ Spec R`, for any `R`-algebra `S`, it pulls back to the compactification of the affine
line over `S` (`projectiveLine.denseCompactificationBaseChangeIso`): the base change keeps the
chart `D₊(X₀)` as its interior.

The construction uses the polynomial chart equivalences of
`TauCeti.AlgebraicGeometry.projectiveLine` and the homogeneous-nonzerodivisor criterion
`AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

/-- The projective line compactifies the affine line over any commutative base ring. -/
-- The selected ambient carrier must reduce to use its two maps without transports.
@[expose, implicit_reducible]
noncomputable def denseCompactification :
    DenseCompactification (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) :=
  ⟨Compactification.ofHom (polynomialChartι R 0) (projectiveLine R ↘ Spec (.of R))
    (polynomialChartι_over R 0), (denseCompactificationProperty_iff _ _).mpr inferInstance⟩

/-- The ambient scheme of the affine-line compactification is the projective line. -/
@[simp]
theorem denseCompactification_Xbar : (denseCompactification R).obj.Xbar = projectiveLine R :=
  (rfl)

/-- The interior map of the affine-line compactification is the zeroth polynomial chart. -/
@[simp]
theorem denseCompactification_j :
    (denseCompactification R).obj.j = polynomialChartι R 0 :=
  (rfl)

/-- The proper map of the affine-line compactification is the projective structure map. -/
@[simp]
theorem denseCompactification_p :
    (denseCompactification R).obj.p = (projectiveLine R ↘ Spec (.of R)) :=
  (rfl)

/-- The projective line is a finitely presented compactification of the affine line. -/
theorem fpCompactificationProperty_denseCompactification :
    fpCompactificationProperty _ (denseCompactification R).obj :=
  (fpCompactificationProperty_iff _ _).mpr (by rw [denseCompactification_p]; infer_instance)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- **Base change of the affine-line compactification**: along `Spec S ⟶ Spec R`, the
compactification `𝔸¹_R ⊂ ℙ¹_R` pulls back to `𝔸¹_S ⊂ ℙ¹_S`. The ambient schemes are identified
by `ℙ¹_S = ℙ¹_R ×_{Spec R} Spec S` and the sources by `Spec S[X] = Spec R[X] ×_{Spec R} Spec S`. -/
noncomputable def denseCompactificationBaseChangeIso :
    (denseCompactification R).obj.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      (denseCompactification S).obj.precomp (isPullback_SpecMap_polynomial R S).isoPullback.inv
        (IsPullback.isoPullback_inv_snd _) :=
  Compactification.isoMk (isPullback_baseChangeProjection R S).isoPullback.symm
    (by
      -- The base-changed ambient scheme is the pullback of `(denseCompactification R).obj.p`,
      -- which unfolds to the structure map `projectiveLine R ↘ Spec R` of that square.
      apply (isPullback_baseChangeProjection R S).hom_ext
      · rw [Category.assoc, Iso.symm_hom, IsPullback.isoPullback_inv_fst]
        refine ((denseCompactification R).obj.baseChange_j_fst _).trans ?_
        simp only [Compactification.precomp_j, denseCompactification_j, Category.assoc,
          polynomialChartι_comp_baseChangeProjection, IsPullback.isoPullback_inv_fst_assoc]
      · rw [Category.assoc, Iso.symm_hom, IsPullback.isoPullback_inv_snd]
        refine ((denseCompactification R).obj.baseChange_j_snd _).trans ?_
        simp only [Compactification.precomp_j, denseCompactification_j, Category.assoc,
          polynomialChartι_over, IsPullback.isoPullback_inv_snd])
    (IsPullback.isoPullback_inv_snd _)

@[simp]
theorem denseCompactificationBaseChangeIso_hom_hom_h :
    (denseCompactificationBaseChangeIso R S).hom.hom.h =
      (isPullback_baseChangeProjection R S).isoPullback.inv :=
  Compactification.isoMk_hom_hom_h _ _ _

@[simp]
theorem denseCompactificationBaseChangeIso_inv_hom_h :
    (denseCompactificationBaseChangeIso R S).inv.hom.h =
      (isPullback_baseChangeProjection R S).isoPullback.hom :=
  Compactification.isoMk_inv_hom_h _ _ _

end TauCeti.AlgebraicGeometry.projectiveLine
