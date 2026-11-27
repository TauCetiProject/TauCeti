/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Sphere.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Covering.LoopSpace
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# The contractible loops of real projective space

For `n ≥ 2` the projection `Sⁿ → ℝPⁿ` is a covering map out of a simply connected space, so its
loop map identifies the loop space `ΩSⁿ` with the space `Ω₀ℝPⁿ` of contractible loops of `ℝPⁿ`,
the path component of the constant loop in `ΩℝPⁿ`
(`TauCeti.RealProjectiveSpace.loopSpaceSphereHomeomorph`), and likewise for the Moore loops
(`TauCeti.RealProjectiveSpace.mooreLoopSpaceSphereHomeomorph`). The homology of `ΩSⁿ`
(`TauCeti.singularHomologyLoopSpaceSphereIso`) then computes that of `Ω₀ℝPⁿ` with coefficients in
any ring `R`: it is `R` in the degrees divisible by `n - 1`
(`TauCeti.RealProjectiveSpace.singularHomologyPathComponentLoopSpaceIso`) and zero in the others
(`TauCeti.RealProjectiveSpace.isZero_singularHomology_pathComponent_loopSpace`).

This is the check, in the proof of Theorem C of Barraud–Damian–Humilière–Oancea, that the mod-two
vanishing theorem is applied to `Ω₀Q` and not to `Q`. For the non-orientable `Q = ℝP⁴`, which is
not simply connected, `Ω₀ℝP⁴` is homeomorphic to `ΩS⁴`, and its mod-two homology in degree `3`
is `𝔽₂`, not zero (`TauCeti.RealProjectiveSpace.nontrivial_singularHomology_pathComponent_loopSpace`
with `n = 4` and `R = ZMod 2`): the reduced mod-two homology of the contractible loops does not
vanish, as Theorem C requires.

The whole loop space `ΩℝPⁿ` is not a loop space of `Sⁿ`: a loop of `ℝPⁿ` whose lift from `x` ends
at `-x` is not in the image of the loop map, and `ΩℝPⁿ` has two path components, one for each
element of `π₁(ℝPⁿ) = ℤ/2`.

## Main results

* `TauCeti.RealProjectiveSpace.loopSpaceSphereHomeomorph`,
  `TauCeti.RealProjectiveSpace.mooreLoopSpaceSphereHomeomorph`: `ΩSⁿ ≃ₜ Ω₀ℝPⁿ` for `n ≥ 2`.
* `TauCeti.RealProjectiveSpace.singularHomologyPathComponentLoopSpaceIso`,
  `TauCeti.RealProjectiveSpace.singularHomologyPathComponentMooreLoopSpaceIso`:
  `H_{j(n-1)}(Ω₀ℝPⁿ; R) ≅ R`.
* `TauCeti.RealProjectiveSpace.isZero_singularHomology_pathComponent_loopSpace`,
  `TauCeti.RealProjectiveSpace.isZero_singularHomology_pathComponent_mooreLoopSpace`: the
  homology of `Ω₀ℝPⁿ` vanishes in the degrees not divisible by `n - 1`.
* `TauCeti.RealProjectiveSpace.nontrivial_singularHomology_pathComponent_loopSpace`,
  `TauCeti.RealProjectiveSpace.nontrivial_singularHomology_pathComponent_mooreLoopSpace`:
  `H_{n-1}(Ω₀ℝPⁿ; R)` is nonzero for a nontrivial ring `R`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Theorem 5.15.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 1.43 and
  Proposition 4.1.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module AlgebraicTopology
open scoped Topology.Homotopy

namespace TauCeti

namespace RealProjectiveSpace

variable {n : ℕ} (hn : 2 ≤ n) (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- **The contractible loops of `ℝPⁿ` are the loops of `Sⁿ`**: for `n ≥ 2`, the loop map of the
projection `Sⁿ → ℝPⁿ` is a homeomorphism from the loop space of `Sⁿ` at `x` onto the path component
of the constant loop in the loop space of `ℝPⁿ` at the image of `x`. -/
def loopSpaceSphereHomeomorph :
    Ω (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃ₜ pathComponent (Path.refl (mk n x)) :=
  have := pathConnectedSpace_loopSpace_sphere finrank_euclideanSpace_fin hn x
  (isCoveringMap_mk n).loopSpaceHomeomorph x

@[simp]
theorem coe_loopSpaceSphereHomeomorph_apply
    (γ : Ω (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :
    (loopSpaceSphereHomeomorph hn x γ : Ω (RealProjectiveSpace n) (mk n x)) =
      γ.map (continuous_mk n) :=
  have := pathConnectedSpace_loopSpace_sphere finrank_euclideanSpace_fin hn x
  (isCoveringMap_mk n).coe_loopSpaceHomeomorph_apply x γ

/-- The inverse of `loopSpaceSphereHomeomorph` lifts a contractible loop of `ℝPⁿ` to `Sⁿ`: the
lift lies over it. -/
@[simp]
theorem map_loopSpaceSphereHomeomorph_symm_apply (δ : pathComponent (Path.refl (mk n x))) :
    ((loopSpaceSphereHomeomorph hn x).symm δ).map (continuous_mk n) = δ :=
  have := pathConnectedSpace_loopSpace_sphere finrank_euclideanSpace_fin hn x
  (isCoveringMap_mk n).map_loopSpaceHomeomorph_symm_apply x δ

/-- **The contractible Moore loops of `ℝPⁿ` are the Moore loops of `Sⁿ`**: for `n ≥ 2`, the Moore
loop map of the projection `Sⁿ → ℝPⁿ` is a homeomorphism from the Moore loop space of `Sⁿ` at `x`
onto the path component of the unit in the Moore loop space of `ℝPⁿ` at the image of `x`. -/
def mooreLoopSpaceSphereHomeomorph :
    MooreLoopSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃ₜ
      pathComponent (1 : MooreLoopSpace (RealProjectiveSpace n) (mk n x)) :=
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  IsCoveringMap.mooreLoopSpaceHomeomorph (p := ⟨mk n, continuous_mk n⟩) (isCoveringMap_mk n) x

@[simp]
theorem coe_mooreLoopSpaceSphereHomeomorph_apply
    (γ : MooreLoopSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :
    (mooreLoopSpaceSphereHomeomorph hn x γ : MooreLoopSpace (RealProjectiveSpace n) (mk n x)) =
      MooreLoopSpace.map ⟨mk n, continuous_mk n⟩ rfl γ :=
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  IsCoveringMap.coe_mooreLoopSpaceHomeomorph_apply (p := ⟨mk n, continuous_mk n⟩)
    (isCoveringMap_mk n) x γ

/-- The inverse of `mooreLoopSpaceSphereHomeomorph` lifts a contractible Moore loop of `ℝPⁿ` to
`Sⁿ`: the lift lies over it. -/
@[simp]
theorem map_mooreLoopSpaceSphereHomeomorph_symm_apply
    (δ : pathComponent (1 : MooreLoopSpace (RealProjectiveSpace n) (mk n x))) :
    MooreLoopSpace.map ⟨mk n, continuous_mk n⟩ (rfl : _ = mk n x)
      ((mooreLoopSpaceSphereHomeomorph hn x).symm δ) = δ :=
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  IsCoveringMap.map_mooreLoopSpaceHomeomorph_symm_apply (p := ⟨mk n, continuous_mk n⟩)
    (isCoveringMap_mk n) x δ

variable (R : Type) [Ring R]

/-- **The homology of the contractible loops of `ℝPⁿ` in the degrees divisible by `n - 1`**:
`H_{j(n-1)}(Ω₀ℝPⁿ; R) ≅ R` for `n ≥ 2`, every `j` and every ring `R`. -/
def singularHomologyPathComponentLoopSpaceIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) (j * (n - 1))).obj (ModuleCat.of R R)).obj
        (TopCat.of (pathComponent (Path.refl (mk n x)))) ≅ ModuleCat.of R R :=
  (((singularHomologyFunctor (ModuleCat.{0} R) (j * (n - 1))).obj (ModuleCat.of R R)).mapIso
      (TopCat.isoOfHomeo (loopSpaceSphereHomeomorph hn x))).symm ≪≫
    singularHomologyLoopSpaceSphereIso finrank_euclideanSpace_fin hn x R j

include hn in
/-- **The homology of the contractible loops of `ℝPⁿ` vanishes in the degrees not divisible by
`n - 1`**, with coefficients in any ring, for `n ≥ 2`. -/
theorem isZero_singularHomology_pathComponent_loopSpace {k : ℕ} (hk : ¬(n - 1) ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (pathComponent (Path.refl (mk n x))))) :=
  (isZero_singularHomology_loopSpace_sphere finrank_euclideanSpace_fin hn x R hk).of_iso
    (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).mapIso
      (TopCat.isoOfHomeo (loopSpaceSphereHomeomorph hn x))).symm

include hn in
/-- **The contractible loops of `ℝPⁿ` have nonzero homology in degree `n - 1`** with coefficients
in a nontrivial ring, for `n ≥ 2`. For `n = 4` and `R = ZMod 2` this is the nonvanishing of
`H₃(Ω₀ℝP⁴; 𝔽₂) ≅ H₃(ΩS⁴; 𝔽₂) = 𝔽₂` used in the proof of Theorem C of
Barraud–Damian–Humilière–Oancea. -/
theorem nontrivial_singularHomology_pathComponent_loopSpace [Nontrivial R] :
    Nontrivial (((singularHomologyFunctor (ModuleCat.{0} R) (n - 1)).obj
      (ModuleCat.of R R)).obj (TopCat.of (pathComponent (Path.refl (mk n x))))) := by
  have e := singularHomologyPathComponentLoopSpaceIso hn x R 1
  rw [one_mul] at e
  exact (e.toLinearEquiv.toEquiv.nontrivial_congr).2 inferInstance

/-- **The homology of the contractible Moore loops of `ℝPⁿ` in the degrees divisible by
`n - 1`**: `H_{j(n-1)}(Ω₀ℝPⁿ; R) ≅ R` for `n ≥ 2`, every `j` and every ring `R`. -/
def singularHomologyPathComponentMooreLoopSpaceIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) (j * (n - 1))).obj (ModuleCat.of R R)).obj
        (TopCat.of (pathComponent (1 : MooreLoopSpace (RealProjectiveSpace n) (mk n x)))) ≅
      ModuleCat.of R R :=
  (((singularHomologyFunctor (ModuleCat.{0} R) (j * (n - 1))).obj (ModuleCat.of R R)).mapIso
      (TopCat.isoOfHomeo (mooreLoopSpaceSphereHomeomorph hn x))).symm ≪≫
    singularHomologyMooreLoopSpaceSphereIso finrank_euclideanSpace_fin hn x R j

include hn in
/-- **The homology of the contractible Moore loops of `ℝPⁿ` vanishes in the degrees not divisible
by `n - 1`**, with coefficients in any ring, for `n ≥ 2`. -/
theorem isZero_singularHomology_pathComponent_mooreLoopSpace {k : ℕ} (hk : ¬(n - 1) ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (pathComponent (1 : MooreLoopSpace (RealProjectiveSpace n) (mk n x))))) :=
  (isZero_singularHomology_mooreLoopSpace_sphere finrank_euclideanSpace_fin hn x R hk).of_iso
    (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).mapIso
      (TopCat.isoOfHomeo (mooreLoopSpaceSphereHomeomorph hn x))).symm

include hn in
/-- **The contractible Moore loops of `ℝPⁿ` have nonzero homology in degree `n - 1`** with
coefficients in a nontrivial ring, for `n ≥ 2`. -/
theorem nontrivial_singularHomology_pathComponent_mooreLoopSpace [Nontrivial R] :
    Nontrivial (((singularHomologyFunctor (ModuleCat.{0} R) (n - 1)).obj
      (ModuleCat.of R R)).obj
        (TopCat.of (pathComponent (1 : MooreLoopSpace (RealProjectiveSpace n) (mk n x))))) := by
  have e := singularHomologyPathComponentMooreLoopSpaceIso hn x R 1
  rw [one_mul] at e
  exact (e.toLinearEquiv.toEquiv.nontrivial_congr).2 inferInstance

end RealProjectiveSpace

end TauCeti
