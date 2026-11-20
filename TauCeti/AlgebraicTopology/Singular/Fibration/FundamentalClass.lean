/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

/-!
# The shriek of a fundamental class of the total space of a fibration

Let `p : E → B` be a Serre fibration over a `T₁` space, let `b` be a point of `B` in the source of
a chart of dimension `r`, and let `F = p⁻¹(b)` be the fibre. The shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ(F)` of the inclusion of `b` is the localization `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F)`
at the fibre followed by the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` of
`TauCeti.TopCat.singularHomologyComplFiberIso`.

When `E` and `F` are closed oriented manifolds of dimensions `n + r` and `n`, Barraud, Damian,
Humilière and Oancea use that `j_!` sends the fundamental class of `E` to the fundamental class of
`F`, up to sign; this is what makes the fundamental class of a fibre bundle of closed oriented
manifolds live over the fundamental class of the base. This file proves it in the following form,
with coefficients in a module `N` over a commutative ring `k`. Suppose that `Hₙ(F; N)` is free of
rank one over `k`, and that the local homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at some point `y ∈ F` is
free of rank one too, as at every point of an `(n + r)`-manifold. Then for every fundamental class
`μ` of `E` (`TauCeti.IsFundamentalClass`):

* the localization of `μ` at the fibre generates `Hₙ₊ᵣ(E, E ∖ F; N)`
  (`TauCeti.IsFundamentalClass.span_fiberLocalization_eq_top`);
* the shriek `j_! μ` generates `Hₙ(F; N)`
  (`TauCeti.IsFundamentalClass.span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top`),
  so it is a unit multiple of any generator, for instance of a fundamental class of `F` when `F`
  is a closed connected manifold (`TauCeti.IsFundamentalClass.exists_linearEquiv_isUnit`);
* for a map `f : E → E'` over `B` to a second Serre fibration, `f_* μ` lives over the fundamental
  class at `b` as soon as the restriction of `f` to the fibres does not kill a generator of
  `Hₙ(F; N)` (`TauCeti.IsFundamentalClass.livesOverFundamentalClass_homologyMap`). This is the
  source's Corollary 2.13, through the naturality of the shriek map
  (`TauCeti.livesOverFundamentalClass_homologyMap_iff`).

No local triviality of `p` and no orientation is needed. The localization of `μ` at `y` factors
through its localization at the fibre, by the restriction `Hₙ₊ᵣ(E, E ∖ F) → Hₙ₊ᵣ(E, E ∖ {y})`.
Both groups are copies of `k`, the first through `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)`, and the localization
at `y` generates the second, since `μ` is a fundamental class. A linear map between two copies of
`k` sends an element to a generator only if that element is itself a generator
(`LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top`).

## Main results

* `TauCeti.IsFundamentalClass.span_fiberLocalization_eq_top`: the localization at the fibre of a
  fundamental class generates the local homology along the fibre.
* `TauCeti.IsFundamentalClass.span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top`:
  the shriek of a fundamental class generates the top homology of the fibre.
* `TauCeti.IsFundamentalClass.livesOverFundamentalClass_homologyMap`: the image of a fundamental
  class under a map of fibrations that is nonzero on the fibres lives over the fundamental class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Definition 2.3, Proposition 2.12,
  Corollary 2.13) and §6.4.2 (Proposition 6.15).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, local homology and fundamental classes.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe u

namespace TauCeti

namespace IsFundamentalClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {k : Type u} [CommRing k]
  {N : ModuleCat.{u} k} (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {n m : ℕ} (h : n + finrank ℝ V = m)
  {μ : ((_root_.TopCat.toSSet.obj E).homology N m : ModuleCat.{u} k)} {y : E} (hy : p y = b)

include hb h hy in
/-- **The localization at the fibre of a fundamental class generates.** Let `p : E ⟶ B` be a Serre
fibration over a `T₁` space, with a chart `e` of dimension `r` at `b`, and let `μ ∈ Hₙ₊ᵣ(E; N)` be a
fundamental class. If the homology `Hₙ(p⁻¹(b); N)` of the fibre and the local homology
`Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the commutative ring `k`,
then the localization of `μ` at the fibre generates `Hₙ₊ᵣ(E, E ∖ p⁻¹(b); N)`. -/
theorem span_fiberLocalization_eq_top
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hμ : IsFundamentalClass μ) :
    Submodule.span k {(fiberLocalization N p b m).hom μ} = ⊤ := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  have hyF : ({y} : Set E) ⊆ p ⁻¹' {b} := singleton_subset_iff.2 hy
  -- The localization along the fibre is a copy of `k`, through the homology of the fibre.
  let eF : (localHomology N (p ⁻¹' {b}) m : ModuleCat.{u} k) ≃ₗ[k] k :=
    (TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).toLinearEquiv.trans ψ
  refine LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top
    (localHomologyRestriction N hyF m).hom eF φ ?_
  -- Restricting the localization at the fibre to `y` gives the localization at `y`.
  have hres : (localHomologyRestriction N hyF m).hom ((fiberLocalization N p b m).hom μ) =
      singularHomologyToLocalHomology N y m μ := by
    rw [singularHomologyToLocalHomology_eq_singularHomologyπ]
    exact singularHomologyπ_localHomologyRestriction_apply N hyF m μ
  rw [hres]
  exact (isFundamentalClass_iff μ).1 hμ y

include hy in
/-- **The shriek of a fundamental class generates the homology of the fibre.** Let `p : E ⟶ B` be
a Serre fibration over a `T₁` space, with a chart `e` of dimension `r` at `b`, and let
`μ ∈ Hₙ₊ᵣ(E; N)` be a fundamental class. If the homology `Hₙ(p⁻¹(b); N)` of the fibre and the
local homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the
commutative ring `k`, then the image `j_! μ` of `μ` under the shriek map
`Hₙ₊ᵣ(E; N) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b); N) ≅ Hₙ(p⁻¹(b); N)` generates `Hₙ(p⁻¹(b); N)`. For closed
oriented manifolds this is `j_! [E] = ±[p⁻¹(b)]`. -/
theorem span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top {ε : ℝ}
    (hε : Metric.ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hμ : IsFundamentalClass μ) :
    Submodule.span k
        {(TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).hom.hom
          ((fiberLocalization N p b m).hom μ)} = ⊤ := by
  rw [← (TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).toLinearEquiv_apply,
    LinearEquiv.span_singleton_apply_eq_top_iff]
  exact span_fiberLocalization_eq_top e hb h hy φ ψ hp hμ

include hb h hy in
/-- **The image of a fundamental class under a map of fibrations** (Barraud–Damian–Humilière–Oancea,
Corollary 2.13). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a
chart `e` of dimension `r` at `b`, and let `f : E ⟶ E'` be a map over `B`. Let `μ ∈ Hₙ₊ᵣ(E; N)` be
a fundamental class, and suppose that the homology `Hₙ(p⁻¹(b); N)` of the fibre and the local
homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the commutative
ring `k`. If the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` does not kill a generator `ν` of
`Hₙ(p⁻¹(b); N)`, for instance a fundamental class of the fibre, then `f_* μ` lives over the
fundamental class at `b`. -/
theorem livesOverFundamentalClass_homologyMap {E' : _root_.TopCat.{u}} {p' : E' ⟶ B}
    {f : E ⟶ E'} (hf : f ≫ p' = p)
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hp' : TopCat.serreFibrations p') (hμ : IsFundamentalClass μ)
    {ν : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k)} (hν : Submodule.span k {ν} = ⊤)
    (hfν : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).map
      (f.preimageMap hf {b})).hom ν ≠ 0) :
    LivesOverFundamentalClass N p' b
      ((SSet.homologyMap (_root_.TopCat.toSSet.map f) N m).hom μ) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  rw [livesOverFundamentalClass_homologyMap_iff e hb hε hε₀ hp hp' hf h μ]
  -- The shriek of `μ` is a unit multiple of `ν`.
  obtain ⟨u, hu⟩ := ψ.exists_units_smul_eq_of_span_singleton_eq_top hν
    (span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top e hb h hy hε hε₀ φ ψ hp hμ)
  rw [← hu, map_smul]
  exact fun h0 ↦ hfν (u.isUnit.smul_eq_zero.1 h0)

end IsFundamentalClass

end TauCeti
