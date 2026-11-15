/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension

/-!
# Manifolds abundant with two-spheres

Let `Q` be a closed connected oriented `n`-manifold and let `ev : Map(S², Q) → Q` be evaluation
at the north pole of `S²`, the evaluation fibration with fibre `Ω²Q` over a base point `b`.
Barraud, Damian, Humilière and Oancea call `Q` **abundant with 2-spheres** (their Definition 6.11
and Definition 1.7) if some class `α ∈ Hₖ(Map(S², Q); ℤ)` satisfies:

1. `α` lives over the fundamental class of `Q`, that is its shriek `j_! α ∈ Hₖ₋ₙ(Ω²Q)` under the
   inclusion `j` of `b` is nonzero;
2. either `k > n`, or `k = n` and the image of `j_! α` in `H₀(Ω²Q, pt)` is nonzero.

Their Theorem 6.12 (Theorem H of the introduction) shows that the `π₁`-sensitive
Hofer–Zehnder capacity of the unit codisc bundle `D*Q` of such a manifold is finite.

This file states the definition in the chart-free form of
`TauCeti.LivesOverFundamentalClass` (`TauCeti.IsAbundantWithTwoSpheres`). The shriek map is the
localization `Hₖ(E) → Hₖ(E, E ∖ F)` at the fibre `F = ev⁻¹(b)` followed by an identification
`Hₖ(E, E ∖ F) ≅ Hₖ₋ₙ(F)` that depends on a chart at `b`
(`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), so the
first condition is that the localization of `α` is nonzero. For the second condition in degree
`n`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)` is spanned by the class of the constant sphere at `b`.
The constant spheres `c : Q → Map(S², Q)` are a section of `ev`, so they map the pair
`(Q, Q ∖ {b})` to `(E, E ∖ F)`, and the local homology `Hₙ(Q, Q ∖ {b}) ≅ H₀(pt)` goes under the
chart identifications onto that span: this is the square of the source's proof of Theorem 6.12,
the naturality of the shriek map (their Proposition 2.12) for the map of fibrations `c` from the
identity of `Q` to `ev`. So the second condition in degree `n` says that the localization of `α`
does not lie in the image of `c_* : Hₙ(Q, Q ∖ {b}) → Hₙ(E, E ∖ F)`.

The definition only uses the space `Q`, a point `b` and the dimension `n`; it is meant for closed
connected oriented `n`-manifolds, where it is the source's definition. Coefficients are the
integers, written `ULift ℤ` as for the integral fundamental classes of
`TauCeti.HomologicalOrientation`.

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres Q n b`: `Q` is abundant with 2-spheres at `b`, in
  dimension `n`, characterized by `TauCeti.isAbundantWithTwoSpheres_iff`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_of_lt`: a class of degree above `n` living over the
  fundamental class witnesses abundance.
* `TauCeti.isAbundantWithTwoSpheres_of_eq`: so does a class of degree `n` living over the
  fundamental class whose localization is not that of a constant sphere class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.7, 2.3 and 6.11,
  Proposition 2.12 and Theorem 6.12.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

variable (Q : Type) [TopologicalSpace Q]

/-- A space `Q` is **abundant with 2-spheres** at `b`, in dimension `n`
(Barraud–Damian–Humilière–Oancea, Definition 6.11), if some integral class
`α ∈ Hₖ(Map(S², Q); ℤ)` lives over the fundamental class of `Q` at `b` for evaluation at the
north pole, and either `n < k`, or `k = n` and the localization of `α` at the fibre over `b` is
not in the image of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres.

For a closed connected oriented `n`-manifold this is the source's definition: the localization
at the fibre is the chart-free form of their shriek map `j_! : Hₖ(Map(S², Q)) → Hₖ₋ₙ(Ω²Q)`, and
in degree `n` the image of the local homology is the span of the class of the constant sphere in
`H₀(Ω²Q)`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)`. -/
def IsAbundantWithTwoSpheres (n : ℕ) (b : Q) : Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
        α ∧
      (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
        (mappingSpaceEval Sphere2.north) b k).hom α ∉
          LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
            (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom)

/-- Unfolding `IsAbundantWithTwoSpheres`: some class of `Hₖ(Map(S², Q); ℤ)` lives over the
fundamental class at `b`, and either `n < k`, or `k = n` and its localization at the fibre over `b`
is not in the image of the local homology of `Q` at `b` under the constant spheres. -/
theorem isAbundantWithTwoSpheres_iff (n : ℕ) (b : Q) :
    IsAbundantWithTwoSpheres Q n b ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
        LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b α ∧
          (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b k).hom α ∉
              LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
                ContinuousMap.const'
                  (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom) :=
  Iff.rfl

variable {Q}

/-- **Abundance from a class of degree above the dimension.** If a class
`α ∈ Hₖ(Map(S², Q); ℤ)` with `n < k` lives over the fundamental class at `b`, then `Q` is
abundant with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_lt {n k : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α) (hk : n < k) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨k, α, hα, Or.inl hk⟩

/-- **Abundance from a class in the dimension.** If a class `α ∈ Hₙ(Map(S², Q); ℤ)` lives over
the fundamental class at `b` and its localization at the fibre over `b` is not the image of a
class of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres, then `Q` is abundant
with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_eq {n : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α)
    (hc : ∀ β, (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) n).hom β ≠
        (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
          n).hom α) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨n, α, hα, Or.inr ⟨rfl, fun ⟨β, hβ⟩ ↦ hc β hβ⟩⟩

end TauCeti
