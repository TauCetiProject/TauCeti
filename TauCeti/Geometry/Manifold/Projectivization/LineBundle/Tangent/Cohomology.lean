/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent.Basic

/-!
# The first cohomology of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line

The pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line `ℓ` is
`𝒪(2) ⊕ 𝒪(1)ᵐ` (`Projectivization.coordLineTangentDiffeomorph`), and the first Čech cohomology of
a split bundle on `ℂℙ¹` vanishes when every twist is at least `-1`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`), so
`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`. This is the case of the coordinate line of the vanishing of
`H¹(C, u* TℂPⁿ)` on the line component `u` of a genus-zero stable map in the class of a line, on
which the regularity of such maps rests (Fulton–Pandharipande, Lemma 10). The splitting along
every line is `Projectivization.lineTangentDiffeomorph`
(`Projectivization.exists_continuousLinearEquiv_pullback_map_tangentSpace_twistSumCore_lineTwist`);
this file states the vanishing only for the coordinate line.

## Main declarations

* `Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`:
  `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0` for the coordinate line `ℓ`.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the regularity of lines.
-/

public section

open CategoryTheory CategoryTheory.Limits
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

/-- **`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.** The first Čech cohomology of the sheaf of holomorphic sections
of the pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line
`ℓ : ℂℙ¹ → ℂPᵐ⁺¹` vanishes: `ℓ* TℂPᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ`
(`Projectivization.coordLineTangentDiffeomorph`), and `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace (m : ℕ) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m) 1) := by
  refine (isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    (k := lineTwist m) fun l ↦ ?_).of_iso
    ((Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) 1).mapIso
      ((sheafToPresheaf _ _).mapIso (holomorphicSectionSheaf.isoOfLinearEquiv
        (fun x ↦ (coordLineTangentEquiv x).toLinearEquiv) contMDiff_coordLineTangentEquiv
        ((coordLineTangentDiffeomorph ω).symm.contMDiff.congr fun q ↦
          (coordLineTangentDiffeomorph_symm_apply ω q).symm))))
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · rw [lineTwist_zero]
    norm_num
  · rw [lineTwist_succ]
    norm_num

end Projectivization
