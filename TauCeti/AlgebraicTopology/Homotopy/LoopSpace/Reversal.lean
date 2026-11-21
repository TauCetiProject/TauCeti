/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Cubical
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# Reversal of loops on the homology of a loop space

Reversing Moore loops, `γ ↦ γ.symm` (`TauCeti.MooreLoopSpace.symm`), inverts the positive
homotopy groups of the Moore loop space `ΩX` (`TauCeti.MooreLoopSpace.homotopyGroup_map_symm`). By
naturality of the Hurewicz map, it therefore acts as `-1` on Hurewicz classes, with any
coefficients (`TauCeti.MooreLoopSpace.singularHomologyMap_symm_cubicalHurewiczHom`). When `ΩX` is
`(d - 1)`-connected, `d ≥ 1`, its integral homology in degree `d` consists of Hurewicz classes, so
reversal acts as `-1` on all of `H_d(ΩX; ℤ)`
(`TauCeti.MooreLoopSpace.singularHomologyMap_symm_of_subsingleton` for `d ≥ 2`,
`TauCeti.MooreLoopSpace.singularHomologyMap_symm_one` for `d = 1`). By functoriality, for a
family of loops `λ : A → ΩX` the family of reversed loops then induces `-λ_*` in degree `d`.

For the sphere `Sⁿ`, `n ≥ 2`, the loop space is `(n - 2)`-connected, so reversal acts as `-1` on
`H_{n-1}(ΩSⁿ; ℤ)` (`TauCeti.MooreLoopSpace.singularHomologyMap_symm_sphere`). In the proof of
Proposition 6.17 of Barraud–Damian–Humilière–Oancea this is the step showing that the class of
the family of loops reversed from those defining the generator `x` of `H_{n-1}(ΩSⁿ; ℤ)` is `-x`.

## Main results

* `TauCeti.MooreLoopSpace.singularHomologyMap_symm_cubicalHurewiczHom`: reversal negates Hurewicz
  classes.
* `TauCeti.MooreLoopSpace.singularHomologyMap_symm_of_subsingleton`,
  `TauCeti.MooreLoopSpace.singularHomologyMap_symm_one`: reversal acts as `-1` on the first
  possibly nonzero positive-degree integral homology of a Moore loop space.
* `TauCeti.MooreLoopSpace.singularHomologyMap_symm_sphere`: reversal acts as `-1` on
  `H_{n-1}(ΩSⁿ; ℤ)`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proof of Proposition 6.17.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup Metric Module
open scoped Topology Topology.Homotopy

namespace TauCeti.MooreLoopSpace

variable {X : Type} [TopologicalSpace X] {x : X}

/-- **Reversal of Moore loops negates Hurewicz classes.** With coefficients in any ring `k`, the
map induced on singular homology by `γ ↦ γ.symm` sends the Hurewicz class of `a ∈ π_{n+1}(ΩX)` to
its negative. -/
theorem singularHomologyMap_symm_cubicalHurewiczHom (k : Type) [Ring k] (n : ℕ)
    (a : Additive (π_ (n + 1) (MooreLoopSpace X x) 1)) :
    HomologicalComplex.homologyMap
        ((singularChains k).map (TopCat.ofHom ⟨symm, continuous_symm⟩)) (n + 1)
        ((singularCubicalHomologyIso k (TopCat.of (MooreLoopSpace X x)) (n + 1)).inv
          (cubicalHurewiczHom k n a)) =
      -(singularCubicalHomologyIso k (TopCat.of (MooreLoopSpace X x)) (n + 1)).inv
        (cubicalHurewiczHom k n a) := by
  rw [singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality k _ symm_one,
    homotopyGroup_map_symm, ofMul_inv, ofMul_toMul, map_neg, map_neg]

/-- **Reversal of Moore loops acts as `-1` on the first possibly nonzero homology group.** If the
Moore loop space is `(n + 1)`-connected, then `γ ↦ γ.symm` acts as `-1` on its integral homology
in degree `n + 2`. -/
theorem singularHomologyMap_symm_of_subsingleton {n : ℕ}
    (hX : ∀ k < n + 2, Subsingleton (π_ k (MooreLoopSpace X x) 1))
    (c : ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology (n + 2)) :
    HomologicalComplex.homologyMap
        ((singularChains ℤ).map (TopCat.ofHom ⟨symm, continuous_symm⟩)) (n + 2) c = -c := by
  obtain ⟨a, rfl⟩ := (cubicalHurewiczSingularHomologyAddEquiv hX).surjective c
  rw [cubicalHurewiczSingularHomologyAddEquiv_apply]
  exact singularHomologyMap_symm_cubicalHurewiczHom ℤ (n + 1) a

/-- **Reversal of Moore loops acts as `-1` on the first homology** of a path-connected Moore loop
space, with integer coefficients. -/
theorem singularHomologyMap_symm_one [PathConnectedSpace (MooreLoopSpace X x)]
    (c : ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology 1) :
    HomologicalComplex.homologyMap
        ((singularChains ℤ).map (TopCat.ofHom ⟨symm, continuous_symm⟩)) 1 c = -c := by
  -- every class is minus a Hurewicz class, by degree-one Hurewicz
  obtain ⟨a, rfl⟩ := (HurewiczOne.hurewiczHomologyAddEquiv
    (X := TopCat.of (MooreLoopSpace X x)) 1).surjective c
  -- the abelianization map is the quotient map
  obtain ⟨g, hg⟩ : ∃ g, Group.Abelianization.of g = a.toMul := QuotientGroup.mk_surjective _
  obtain ⟨b, hb⟩ :=
    EquivLike.surjective (homotopyGroupOfUniqueMulEquivFundamentalGroup (Fin 1)) g
  have h := hurewiczHom_hom_one_eq_neg_hurewiczHomologyAddEquiv (Additive.ofMul b)
  rw [toMul_ofMul, hb, hg, ofMul_toMul, ← singularCubicalHomologyIso_inv_cubicalHurewiczHom] at h
  rw [← neg_eq_iff_eq_neg.2 h]
  exact (map_neg _ _).trans (congrArg Neg.neg (singularHomologyMap_symm_cubicalHurewiczHom ℤ 0 _))

/-- **Reversal of loops acts as `-1` on `H_{n-1}(ΩSⁿ; ℤ)`.** For the unit sphere `Sⁿ⁺²` of an
`(n + 3)`-dimensional real normed space, `γ ↦ γ.symm` acts as `-1` on the integral homology of
its Moore loop space in degree `n + 1`, the first positive degree in which it can be nonzero. -/
theorem singularHomologyMap_symm_sphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hE : finrank ℝ E = n + 3) (x : sphere (0 : E) 1)
    (c : ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace (sphere (0 : E) 1) x))).homology
      (n + 1)) :
    HomologicalComplex.homologyMap
        ((singularChains ℤ).map (TopCat.ofHom ⟨symm, continuous_symm⟩)) (n + 1) c = -c := by
  cases n with
  | zero =>
    have := (pathConnectedSpace_iff_subsingleton_pi1 x).2
      (subsingleton_homotopyGroup_sphere_of_lt hE (by simp) x)
    exact singularHomologyMap_symm_one c
  | succ n =>
    exact singularHomologyMap_symm_of_subsingleton
      (fun _ hk ↦ subsingleton_homotopyGroup_mooreLoopSpace_sphere hE x (by omega)) c

end TauCeti.MooreLoopSpace
