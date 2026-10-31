/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic

/-!
# Intersection numbers over a tower of base fields

Let `κ / k` be an extension of fields and let `C` be a scheme over `κ`, regarded as a scheme over
`k` through `Spec κ ⟶ Spec k`. The Euler-characteristic degree of a line bundle on `C` over `k` is
`[κ : k]` times its degree over `κ` (`LineBundleClass.eulerDegree_eq_finrank_mul`), because every
cohomology dimension over `k` is `[κ : k]` times the corresponding dimension over `κ`
(`Scheme.Modules.finrank_cohomology_eq_finrank_mul`). Hence the intersection number of a
line-bundle class with a curve `ι : C ⟶ X` over `k` is `[κ : k]` times the intersection number
over `κ`, and in particular `[κ : k]` divides it.

This is the divisibility axiom of the numerical type of a regular model. Let `Cᵢ` be a component
of the special fibre of a regular model of a curve over a discrete valuation ring with residue
field `k`, and let `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` be its constant field, so that `Cᵢ` is a curve over `κᵢ`
compatibly with its structure over `k`. Its weight is `wᵢ = [κᵢ : k]` and the intersection numbers
`aᵢⱼ = (Cⱼ · Cᵢ)` are degrees over `k` of line bundles on `Cᵢ`, so `wᵢ ∣ aᵢⱼ`. This is the condition
`TauCeti.NumericalType.weight_dvd` of an abstract numerical type.

## Main results

* `LineBundleClass.intersectionNumber_eq_finrank_mul`: the intersection number over `k` is
  `[κ : k]` times the intersection number over `κ`.
* `LineBundleClass.finrank_dvd_intersectionNumber`: `[κ : k]` divides every intersection number
  with a curve over `κ`.

## References

* [The Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), where the
  numerical type of a regular model has the weights `wᵢ = [κᵢ : k]` of the components of its
  special fibre, and these divide the intersection numbers.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, on intersection numbers of
  divisors with vertical curves on arithmetic surfaces.
-/

public section

open CategoryTheory AlgebraicGeometry Scheme.Modules
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ]

namespace LineBundleClass

section IntersectionNumber

variable {X C : Scheme.{u}} [C.Over (Spec (.of k))] [C.Over (Spec (.of κ))] (ι : C ⟶ X)

/-- **Intersection numbers over a tower of fields.** If the curve `C` lies over `κ`, compatibly
with its structure over `k`, then the intersection number over `k` of a line-bundle class with
`ι : C ⟶ X` is `[κ : k]` times the intersection number over `κ`. -/
theorem intersectionNumber_eq_finrank_mul
    (h : (C ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      (C ↘ Spec (.of k))) (a : LineBundleClass X) :
    intersectionNumber k ι a = finrank k κ * intersectionNumber κ ι a := by
  rw [intersectionNumber_def, intersectionNumber_def, eulerDegree_eq_finrank_mul h]

/-- **The weight of a curve divides its intersection numbers.** If the curve `C` lies over `κ`,
compatibly with its structure over `k`, then `[κ : k]` divides the intersection number over `k` of
every line-bundle class with `ι : C ⟶ X`. For a component `Cᵢ` of the special fibre of a regular
model and its constant field `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})`, this is the divisibility `wᵢ ∣ aᵢⱼ` of the
intersection numbers by the weight. -/
theorem finrank_dvd_intersectionNumber
    (h : (C ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      (C ↘ Spec (.of k))) (a : LineBundleClass X) :
    (finrank k κ : ℤ) ∣ intersectionNumber k ι a :=
  ⟨_, intersectionNumber_eq_finrank_mul ι h a⟩

end IntersectionNumber

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
