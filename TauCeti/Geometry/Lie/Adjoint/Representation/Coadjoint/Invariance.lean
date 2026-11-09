/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Symplectic.Coadjoint

/-!
# Adjoint invariance of the Kirillov–Kostant–Souriau form

Let `G` be a Lie group over a nontrivially normed field `𝕜`, with Lie algebra
`𝔤 = GroupLieAlgebra I G`, acting on `𝔤*` by the coadjoint representation `Ad*_g ν = ν ∘ Ad_{g⁻¹}`.
Each adjoint map `Ad_g` is a Lie algebra automorphism of `𝔤` (`TauCeti.Lie.tangentAd`), and the
translate `Ad*_g ν` pulls back along it to `ν`
(`TauCeti.Lie.coadjointRepresentation_apply_comp_tangentAd`). The naturality of the
Kirillov–Kostant–Souriau form under surjective Lie algebra maps
(`Module.Dual.quotientLieAnnihilatorEquiv`) therefore gives, at the level of the algebraic tangent
models of the coadjoint orbit:

* the infinitesimal stabilizer of the translate is the translate of the infinitesimal stabilizer,
  `𝔤_{Ad*_g ν} = Ad_g 𝔤_ν` (`TauCeti.Lie.lieAnnihilator_coadjointRepresentation_apply`), the
  infinitesimal form of `G_{Ad*_g ν} = g G_ν g⁻¹` (`Representation.stabilizer_conj`);
* for a real Lie group, `[ξ] ↦ [Ad_g ξ]` is a symplectomorphism from `(𝔤 ⧸ 𝔤_ν, ω_ν)` to
  `(𝔤 ⧸ 𝔤_{Ad*_g ν}, ω_{Ad*_g ν})`
  (`TauCeti.Lie.isSymplectomorphism_quotientLieAnnihilatorEquiv_tangentAd`).

On the homogeneous coadjoint orbit `G / G_ν`, the map `[ξ] ↦ [Ad_g ξ]` is the differential at `ν`
of the action of `g`, read in the orbit derivatives at `ν` and at `Ad*_g ν`. So the second item is
the pointwise statement that `G` acts on its coadjoint orbits by symplectomorphisms of the KKS form.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §14.3 (the coadjoint orbit symplectic structure).
-/

public section

noncomputable section

namespace TauCeti.Lie

open Module
open scoped ContDiff

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness 𝕜 3) G]

local instance : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- **The infinitesimal stabilizer of a translate.** `ξ` stabilizes `Ad*_g ν` exactly when
`Ad_{g⁻¹} ξ` stabilizes `ν`, that is, `𝔤_{Ad*_g ν} = Ad_g 𝔤_ν`. -/
theorem lieAnnihilator_coadjointRepresentation_apply (g : G)
    (ν : Dual 𝕜 (GroupLieAlgebra I G)) :
    lieAnnihilator 𝕜 (GroupLieAlgebra I G) (coadjointRepresentation 𝕜 I G g ν) =
      (lieAnnihilator 𝕜 (GroupLieAlgebra I G) ν).comap (tangentAd (I := I) g⁻¹ :
        GroupLieAlgebra I G →ₗ⁅𝕜⁆ GroupLieAlgebra I G) := by
  refine Dual.lieAnnihilator_eq_comap (tangentAd (I := I) g⁻¹).surjective ?_
  ext X
  simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, tangentAd_apply,
    coadjointRepresentation_apply]

end Field

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]

local instance : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- **The Kirillov–Kostant–Souriau form is invariant under the adjoint action.** The equivalence
`[ξ] ↦ [Ad_g ξ]` from the algebraic tangent model `𝔤 ⧸ 𝔤_ν` of the coadjoint orbit through `ν` to
that through `Ad*_g ν` is a symplectomorphism from `ω_ν` to `ω_{Ad*_g ν}`. -/
theorem isSymplectomorphism_quotientLieAnnihilatorEquiv_tangentAd (g : G)
    (ν : Dual ℝ (GroupLieAlgebra I G)) :
    SymplecticForm.IsSymplectomorphism ν.kksSymplecticForm
      (coadjointRepresentation ℝ I G g ν).kksSymplecticForm
      (Dual.quotientLieAnnihilatorEquiv (coadjointRepresentation ℝ I G g ν)
        (tangentAd (I := I) g).surjective (coadjointRepresentation_apply_comp_tangentAd g ν)) :=
  Dual.isSymplectomorphism_quotientLieAnnihilatorEquiv _ _ _

end Real

end TauCeti.Lie
