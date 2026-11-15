/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Content
public import TauCeti.RingTheory.Grassmannian.Basic

/-!
# Closed conditions on the Grassmannian

Let `M` be a module over a commutative ring `R`, and `N` a point of the Grassmannian functor
`A ↦ G(k, A ⊗[R] M; A)`, or more generally any `A`-submodule of `A ⊗[R] M`. Many conditions on the
base change of `N` along an `R`-algebra map `A → B` have the form: a `B`-linear map `Φ` out of
`B ⊗[R] M` vanishes on the base change of `N`. When, on the image of `A ⊗[R] M`, the map `Φ` is the
base change of an `A`-linear map `Ψ` to a projective `A`-module, such a condition holds exactly when
`A → B` kills the content (`Submodule.minorsIdeal 1`) of `Ψ(N)`, so it is a closed condition. This
follows from `IsBaseChange.minorsIdeal_one_le_ker_iff`.

## Main results

* `Module.Grassmannian.ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le`: a linear condition on the
  base change of a point of the Grassmannian, which is the base change of a condition on the
  point, is cut out by a content ideal.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {A B : Type w} [CommRing A] [Algebra R A] [CommRing B]
  [Algebra R B] {M : Type v} [AddCommGroup M] [Module R M] [Algebra A B] [IsScalarTower R A B]

/-- **Closed conditions on the base change of a submodule.** Let `N ≤ A ⊗[R] M` and let `Φ` be a
`B`-linear map out of `B ⊗[R] M` which, on the image of `A ⊗[R] M`, is the base change `g ∘ Ψ` of
an `A`-linear map `Ψ` to a projective module `X`. Then `Φ` vanishes on the kernel of
`baseChangeMkQ B N`, the base change of `N` to `B`, exactly when `A → B` kills the content of
`Ψ(N)`. -/
theorem ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le (N : Submodule A (A ⊗[R] M))
    {X Y : Type*} [AddCommGroup X] [Module A X] [Module.Projective A X] [AddCommGroup Y]
    [Module B Y] [Module A Y] [IsScalarTower A B Y] (Φ : B ⊗[R] M →ₗ[B] Y)
    (Ψ : A ⊗[R] M →ₗ[A] X) {g : X →ₗ[A] Y} (hg : IsBaseChange B g)
    (hΦ : ∀ x, Φ ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x) = g (Ψ x)) :
    LinearMap.ker (baseChangeMkQ B N) ≤ LinearMap.ker Φ ↔
      (N.map Ψ).minorsIdeal 1 ≤ RingHom.ker (algebraMap A B) := by
  simp [ker_baseChangeMkQ_le_ker_iff, hΦ, hg.minorsIdeal_one_le_ker_iff]

end Module.Grassmannian
