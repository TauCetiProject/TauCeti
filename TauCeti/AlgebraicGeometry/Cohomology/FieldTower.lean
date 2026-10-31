/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic

/-!
# Cohomology over a tower of base fields

Let `κ / k` be an extension of fields and let `X` be a scheme over `κ`, regarded as a scheme over
`k` through `Spec κ ⟶ Spec k`. The cohomology groups `Hⁱ(X, M)` of a sheaf of modules on `X` are
then vector spaces over both fields, and the `k`-structure is the restriction of the
`κ`-structure (`Scheme.Modules.isScalarTower_cohomology_of_comp_eq`, in
`TauCeti.AlgebraicGeometry.Cohomology.Module.Base`). By the tower law,

`dim_k Hⁱ(X, M) = [κ : k] · dim_κ Hⁱ(X, M)`,

and the same factor relates the truncated Euler characteristics over the two fields.

The main case is that of the constant field: a proper curve `C` over `k` whose ring of global
functions `κ = H⁰(C, 𝒪_C)` is a field is a curve over `κ`. Its dimensions over `k` are those over
`κ` multiplied by `[κ : k]`. For the components `Cᵢ` of the special fibre of a regular model of a
curve over a discrete valuation ring, these are the weights `wᵢ = [κᵢ : k]` and the genera
`gᵢ = dim_{κᵢ} H¹(Cᵢ, 𝒪_{Cᵢ})` of the associated numerical type, so that
`dim_k H¹(Cᵢ, 𝒪_{Cᵢ}) = wᵢ gᵢ`.

The tower law holds with no finiteness hypothesis, because both sides use Mathlib's `finrank`,
which is zero on an infinite-dimensional space.

## Main results

* `Scheme.Modules.finrank_cohomology_eq_finrank_mul`: `dim_k Hⁱ = [κ : k] · dim_κ Hⁱ`.
* `Scheme.Modules.eulerCharBelow_eq_finrank_mul`: the same relation for truncated Euler
  characteristics.

## References

* [The Stacks Project, Section 55.8](https://stacks.math.columbia.edu/tag/0C6Y), for the weights
  and genera of the components of a numerical type.
-/

public section

open CategoryTheory AlgebraicGeometry Scheme.Modules
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.Over (Spec (.of κ))]

/-- **The tower law for cohomology.** If the structure morphism of `X` to `Spec k` factors through
`Spec κ`, then `dim_k Hⁱ(X, M) = [κ : k] · dim_κ Hⁱ(X, M)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_finrank_mul
    (h : (X ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      (X ↘ Spec (.of k))) (M : X.Modules) (i : ℕ) :
    finrank k (Cohomology M i) = finrank k κ * finrank κ (Cohomology M i) :=
  have := isScalarTower_cohomology_of_comp_eq h M i
  (Module.finrank_mul_finrank k κ (Cohomology M i)).symm

/-- **The tower law for Euler characteristics.** If the structure morphism of `X` to `Spec k`
factors through `Spec κ`, then the truncated Euler characteristic of a sheaf of modules over `k`
is `[κ : k]` times its truncated Euler characteristic over `κ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_eq_finrank_mul
    (h : (X ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      (X ↘ Spec (.of k))) (M : X.Modules) (n : ℕ) :
    eulerCharBelow k X M n = finrank k κ * eulerCharBelow κ X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih, finrank_cohomology_eq_finrank_mul h,
      Nat.cast_mul]
    ring

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
