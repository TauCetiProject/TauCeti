/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.Antipodal

/-!
# Maps into even-dimensional spheres with a normal field

Let `S` be the unit sphere of a real inner product space `E` of dimension `n + 2`, so that `S` has
dimension `n + 1`. The antipodal map of `S` acts on `Hₙ₊₁(S)` by `(-1) ^ (n + 2)`
(`TauCeti.singularHomologyFunctor_map_sphere_neg`, in `TauCeti.AlgebraicTopology.Singular.Sphere`),
so by `-1` when the dimension of `S` is even.

A continuous map `f : Y → S` with a nowhere-vanishing field orthogonal to it is homotopic to its
antipode `-f` (`ContinuousMap.homotopic_neg_of_ne_zero_of_inner_eq_zero`). When `S` has even
dimension, the map induced by `f` on the top homology of `S` is therefore its own negative
(`TauCeti.singularHomologyFunctor_map_eq_neg_of_inner_eq_zero`), for coefficients in any abelian
category. For a class `a` of `πₖ(S)`, `k ≥ 2` even, represented by a map out of the sphere `Sᵏ`
that admits such a field, the Hurewicz class of `a` is its own negative, so `a ^ 2` lies in the
kernel of the Hurewicz isomorphism; since `πₖ(S) ≅ ℤ` has no torsion, `a` is trivial
(`GenLoop.mk_eq_one_of_inner_eq_zero`).

For the identity of `S` this is the hairy ball theorem. Another instance is the first vector of a
family of orthonormal two-frames, whose second vector is a normal field along it: a sphere of
orthonormal two-frames projects to a nullhomotopic sphere in an even-dimensional sphere
(`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`, proved through
`ContinuousMap.homotopyGroupMap_eq_one_of_homotopic_neg`).

## Main results

* `TauCeti.singularHomologyFunctor_map_eq_neg_of_inner_eq_zero`: a map into an even-dimensional
  sphere with a nowhere-vanishing normal field induces its own negative on top homology.
* `GenLoop.mk_eq_one_of_inner_eq_zero`: a class of `πₙ₊₂(Sⁿ⁺²)`, `n` even, whose sphere
  map has a nowhere-vanishing normal field is trivial.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, Theorem 1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.2, properties of degree
  (the antipodal map has degree `(-1) ^ (n + 1)`), and §4.2, Corollary 4.25.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module
open scoped InnerProductSpace Topology Topology.Homotopy

universe w v u

namespace TauCeti

section Homology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

variable {Y : Type w} [TopologicalSpace Y]

/-- **A map into an even-dimensional sphere with a normal field induces its own negative on top
homology.** Let `S` be the unit sphere of a real inner product space of dimension `n + 2`, with
`n` odd, so that `S` has even dimension `n + 1`. If `v : Y → E` is continuous, vanishes nowhere
and is orthogonal to `f : Y → S` at every point, then `f_* = -f_*` on `Hₙ₊₁`: the map `f` is
homotopic to its antipode, and the antipodal map acts by `-1`. -/
theorem singularHomologyFunctor_map_eq_neg_of_inner_eq_zero (hE : finrank ℝ E = n + 2)
    (hn : Odd n) {f : C(Y, sphere (0 : E) 1)} {v : Y → E} (hv : Continuous v)
    (h0 : ∀ y, v y ≠ 0) (ht : ∀ y, ⟪v y, (f y : E)⟫_ℝ = 0) :
    ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) =
      -((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) := by
  obtain ⟨H⟩ := f.homotopic_neg_of_ne_zero_of_inner_eq_zero hv h0 ht
  -- The pointwise negation `-f` is `f` followed by the antipodal map.
  have hneg : TopCat.ofHom (-f) = TopCat.ofHom f ≫
      (TopCat.ofHom ⟨Neg.neg, continuous_neg⟩ : TopCat.of (sphere (0 : E) 1) ⟶ _) := by
    ext; simp
  have hH := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom (-f)) H R (n + 1)
  -- The homotopy invariance is stated for the homology of the singular chain complex functor,
  -- which is the singular homology functor applied to `R` by definition.
  change ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) =
    ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom (-f)) at hH
  conv_lhs => rw [hH, hneg, Functor.map_comp, singularHomologyFunctor_map_sphere_neg R hE,
    (hn.add_even even_two).neg_one_pow]
  simp

end Homology

end TauCeti

namespace GenLoop

open TauCeti

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **A sphere map with a nowhere-vanishing normal field is nullhomotopic in even dimensions.** Let
`S` be the unit sphere of a real inner product space of dimension `n + 3`, with `n` even, so that
`S` has even dimension `n + 2`. If the map `Sⁿ⁺² → S` of a generalized loop `p` at `x` admits a
continuous nowhere-vanishing field `v` orthogonal to it, then the class of `p` in `πₙ₊₂(S, x)` is
trivial. -/
theorem mk_eq_one_of_inner_eq_zero (hE : finrank ℝ E = n + 3) (hn : Even n)
    {x : sphere (0 : E) 1} (p : Ω^ (Fin (n + 2)) (sphere (0 : E) 1) x)
    {v : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1 → E} (hv : Continuous v)
    (h0 : ∀ y, v y ≠ 0) (ht : ∀ y, ⟪v y, (GenLoop.toSphere p y : E)⟫_ℝ = 0) :
    (⟦p⟧ : π_ (n + 2) (sphere (0 : E) 1) x) = (1 : π_ (n + 2) (sphere (0 : E) 1) x) := by
  set a : π_ (n + 2) (sphere (0 : E) 1) x := ⟦p⟧
  -- The Hurewicz class of `a` is its own negative.
  have hneg : HomotopyGroup.hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a =
      -HomotopyGroup.hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a := by
    have key := singularHomologyFunctor_map_eq_neg_of_inner_eq_zero (ModuleCat.of ℤ ℤ) hE
      hn.add_one hv h0 ht
    rw [HomotopyGroup.hurewicz_mk, GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp,
      ← Preadditive.comp_neg, ← key]
  -- So `a ^ 2` has the Hurewicz class of `1`, and the Hurewicz map is injective.
  have hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) x) :=
    fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) hE (by simpa using hk) x
  have h2' : (HomotopyGroup.hurewicz (ModuleCat.of ℤ ℤ) (n + 1) (a ^ 2)).hom 1 =
      (HomotopyGroup.hurewicz (ModuleCat.of ℤ ℤ) (n + 1)
        (1 : π_ (n + 2) (sphere (0 : E) 1) x)).hom 1 := by
    rw [HomotopyGroup.hurewicz_pow, HomotopyGroup.hurewicz_one, two_nsmul,
      add_eq_zero_iff_eq_neg.2 hneg]
  have h2 : a ^ 2 = 1 := (HomotopyGroup.bijective_hurewicz hX).1 h2'
  -- `πₙ₊₂(S, x) ≅ ℤ` has no torsion.
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  let φ := homotopyGroupSphereAddEquiv ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)) x
  have h2a : (2 : ℤ) • Additive.ofMul a = 0 := by
    rw [two_zsmul, ← ofMul_mul, ← sq, h2, ofMul_one]
  have hφ : 2 * φ (Additive.ofMul a) = 0 := by
    rw [← smul_eq_mul, ← map_zsmul, h2a, map_zero]
  have ha : Additive.ofMul a = 0 :=
    φ.map_eq_zero_iff.1 ((mul_eq_zero.1 hφ).resolve_left two_ne_zero)
  exact Additive.ofMul.injective ha

end GenLoop
