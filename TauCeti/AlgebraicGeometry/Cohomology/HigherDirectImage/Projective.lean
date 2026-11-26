/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Linear
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType

/-!
# Coherence of higher direct images along projective morphisms

Let `R` be a Noetherian ring and `X` a scheme projective over `Spec R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R`). For every quasi-coherent `𝒪_X`-module `F` of
finite type and every `q : ℕ`, the higher direct image `R^q (X ↘ Spec R)_* F` is finitely presented
(`AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`): it is
associated to the finite `R`-module `H^q(X, F)` by Serre's finiteness theorem
(`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`) and the affine comparison
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_iff_finite`).

The result localizes directly to the target: for a morphism `f : X ⟶ Y` into a locally Noetherian
scheme `Y` covered by affine opens `U i` over which `f ⁻¹ᵁ U i` is projective over `Γ(Y, U i)`,
every higher direct image `R^q f_* F` of a quasi-coherent `F` of finite type is finitely presented
(`AlgebraicGeometry.Scheme.Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver`).
The localization combines `Scheme.Hom.higherDirectImageRestrictIso` with the isomorphism-comparison
`Scheme.Hom.higherDirectImageCompRestrictIso` (in `HigherDirectImage/Restrict.lean`).

## Main declarations

* `AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`:
  higher direct images of coherent sheaves on a scheme projective over a Noetherian ring `R` are
  finitely presented.
* `AlgebraicGeometry.Scheme.Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver`:
  higher direct images of coherent sheaves along a morphism locally projective over a locally
  Noetherian base are finitely presented.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2, Theorem III.8.8,
  and Remark III.8.8.1.
* [Stacks, Proposition 30.19.1 (02O5)](https://stacks.math.columbia.edu/tag/02O5) and
  [Lemma 30.19.2 (02O6)](https://stacks.math.columbia.edu/tag/02O6).
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- **Coherence of higher direct images for a projective scheme over `Spec R`.** Let `R` be a
Noetherian ring and `X` a scheme projective over `Spec R`. For every quasi-coherent `𝒪_X`-module
`F` of finite type and every `q : ℕ`, the higher direct image `R^q (X ↘ Spec R)_* F` is finitely
presented. -/
theorem IsProjectiveOver.isFinitePresentation_higherDirectImage (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFinitePresentation :=
  (isFinitePresentation_higherDirectImage_iff_finite R F q).mpr inferInstance

/-- **Coherence of higher direct images for locally projective morphisms.** Let `f : X ⟶ Y` be a
morphism to a locally Noetherian scheme `Y`, covered by affine opens `U i` over which each
preimage `f ⁻¹ᵁ U i` is projective over `Γ(Y, U i)`. Then for every quasi-coherent `𝒪_X`-module
`F` of finite type and every `q : ℕ`, the higher direct image `R^q f_* F` is finitely presented. -/
theorem Hom.isFinitePresentation_higherDirectImage_of_locally_isProjectiveOver
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hUa : ∀ i, IsAffineOpen (U i)) (hU : ⨆ i, U i = ⊤)
    (hproj : ∀ i, @Scheme.IsProjectiveOver Γ(Y, U i) _ (f ⁻¹ᵁ U i).toScheme
      ⟨(f ∣_ U i) ≫ (hUa i).isoSpec.hom⟩)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    ((f.higherDirectImage q).obj F).IsFinitePresentation := by
  refine isFinitePresentation_of_isFinitePresentation_restrict _ U hU fun i ↦ ?_
  have : IsNoetherianRing Γ(Y, U i) := IsLocallyNoetherian.component_noetherian ⟨U i, hUa i⟩
  let _ : (f ⁻¹ᵁ U i).toScheme.Over (Spec (.of Γ(Y, U i))) :=
    ⟨(f ∣_ U i) ≫ (hUa i).isoSpec.hom⟩
  have : (f ⁻¹ᵁ U i).toScheme.IsProjectiveOver Γ(Y, U i) := hproj i
  let G : (f ⁻¹ᵁ U i).toScheme.Modules := F.restrict (f ⁻¹ᵁ U i).ι
  have : G.IsQuasicoherent := isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U i).ι F
  have hspec : ((((f ∣_ U i) ≫ (hUa i).isoSpec.hom).higherDirectImage q).obj
      G).IsFinitePresentation :=
    IsProjectiveOver.isFinitePresentation_higherDirectImage Γ(Y, U i) G q
  have hres : ((((f ∣_ U i).higherDirectImage q).obj G).restrict
      (hUa i).isoSpec.inv).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(Y, U i)).ringCatSheaf).prop_of_iso
      ((Hom.higherDirectImageCompRestrictIso (f ∣_ U i) (hUa i).isoSpec q).app G).symm hspec
  have hUi : (((f ∣_ U i).higherDirectImage q).obj G).IsFinitePresentation :=
    (isFinitePresentation_restrict_iff_of_isIso _ (hUa i).isoSpec.inv).mp hres
  exact (SheafOfModules.isFinitePresentation (U i).toScheme.ringCatSheaf).prop_of_iso
    ((f.higherDirectImageRestrictIso (U i) q).app F).symm hUi

end AlgebraicGeometry.Scheme
