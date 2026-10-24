/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Translation of polynomial functions on the dual

Let `M` be a module over a commutative ring `R`. An element `p` of the symmetric algebra
`SymmetricAlgebra R M` is a polynomial function on the dual of `M`, its value at a linear form `g`
being `SymmetricAlgebra.lift g p`. Translating the argument by a fixed linear form `f`,
`g ↦ p (g + f)`, is again such a function, and it is induced by an algebra automorphism of the
symmetric algebra: the one sending each generator `m` to `m + f m`. This file constructs it,
`SymmetricAlgebra.translation f`, and proves its evaluation formula
`p ↦ (g ↦ p (g + f))` (`SymmetricAlgebra.lift_translation`), its group laws in `f`, and its
interaction with the degree filtration.

The degree filtration is the word filtration `TauCeti.Algebra.wordFiltration` of the generator map,
whose step `n` is spanned by the products of at most `n` generators. A translation sends a
generator to itself plus a scalar, so it preserves every step; and on an element homogeneous of
degree `n` it changes nothing in degree `n`, the difference `translation f p - p` lying in degree
strictly less than `n` (`SymmetricAlgebra.translation_sub_self_mem_wordFiltrationPrevious`).
That is, a translation is unipotent for the filtration, with identity associated graded map.

For a Cartan subalgebra `H` of a semisimple Lie algebra, `S(H)` is the algebra of polynomial
functions on the weights, and translation by the Weyl vector `ρ` is what relates the
Harish-Chandra projection to its linear normalization and the dot action of the Weyl group to the
linear one.

## Main definitions

* `SymmetricAlgebra.translation f`: the algebra automorphism of `SymmetricAlgebra R M`
  sending each generator `m` to `m + f m`.

## Main results

* `SymmetricAlgebra.translation_ι`: its value on a generator.
* `SymmetricAlgebra.lift_translation`: evaluation after translating by `f` is evaluation at
  the translated linear form.
* `SymmetricAlgebra.translation_zero`, `SymmetricAlgebra.translation_trans` and
  `SymmetricAlgebra.translation_symm`: translation is a homomorphism from the additive
  group of linear forms to the automorphisms.
* `SymmetricAlgebra.translation_mem_wordFiltration_iff`: translation preserves every step
  of the degree filtration.
* `SymmetricAlgebra.translation_sub_self_mem_wordFiltrationPrevious`: on a homogeneous
  element of degree `n` it agrees with the identity up to degree strictly less than `n`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3, where
  the translation by `ρ` of polynomial functions on the weights appears in the Harish-Chandra
  homomorphism.
-/

public section

namespace SymmetricAlgebra

open TauCeti.Algebra TauCeti.SymmetricAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

/-- **Translation by a linear form** `f`: the algebra automorphism of the symmetric algebra sending
each generator `m` to `m + f m` (`SymmetricAlgebra.translation_ι`). Reading an element `p`
of `SymmetricAlgebra R M` as a polynomial function on the dual of `M`, `translation f p` is the
function `g ↦ p (g + f)` (`SymmetricAlgebra.lift_translation`). Its inverse is translation
by `-f` (`SymmetricAlgebra.translation_symm`). -/
noncomputable def translation (f : M →ₗ[R] R) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R M :=
  AlgEquiv.ofAlgHom (lift (ι R M + Algebra.linearMap R (SymmetricAlgebra R M) ∘ₗ f))
    (lift (ι R M - Algebra.linearMap R (SymmetricAlgebra R M) ∘ₗ f))
    (algHom_ext <| LinearMap.ext fun m ↦ by simp)
    (algHom_ext <| LinearMap.ext fun m ↦ by simp)

/-- **Translation on a generator**: `translation f` sends the generator `m` to `m + f m`. -/
@[simp]
theorem translation_ι (f : M →ₗ[R] R) (m : M) :
    translation f (ι R M m) = ι R M m + algebraMap R (SymmetricAlgebra R M) (f m) := by
  simp [translation]

/-- **Evaluation of a translate**: evaluating `translation f p` at a linear form `g` is evaluating
`p` at `g + f`. The linear form `g` may take values in any commutative `R`-algebra `A`, the
translation `f` entering through the structure map `R → A`. -/
@[simp]
theorem lift_translation {A : Type w} [CommSemiring A] [Algebra R A] (g : M →ₗ[R] A)
    (f : M →ₗ[R] R) (p : SymmetricAlgebra R M) :
    lift g (translation f p) = lift (g + Algebra.linearMap R A ∘ₗ f) p := by
  have h : (lift g).comp (translation f).toAlgHom = lift (g + Algebra.linearMap R A ∘ₗ f) :=
    algHom_ext <| LinearMap.ext fun m ↦ by simp
  exact DFunLike.congr_fun h p

/-- **Translations compose additively**: translating by `g` and then by `f` is translating by
`g + f`. -/
@[simp]
theorem translation_translation (f g : M →ₗ[R] R) (p : SymmetricAlgebra R M) :
    translation f (translation g p) = translation (g + f) p := by
  have h :
      (translation f).toAlgHom.comp (translation g).toAlgHom = (translation (g + f)).toAlgHom :=
    algHom_ext <| LinearMap.ext fun m ↦ by
      simp
      abel
  exact DFunLike.congr_fun h p

/-- Translation by the zero linear form is the identity. -/
@[simp]
theorem translation_zero : translation (0 : M →ₗ[R] R) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| algHom_ext <| LinearMap.ext fun m ↦ by simp

/-- The bundled form of `SymmetricAlgebra.translation_translation`: translating by `f` and
then by `g` is translating by `f + g`. -/
@[simp]
theorem translation_trans (f g : M →ₗ[R] R) :
    (translation f).trans (translation g) = translation (f + g) :=
  AlgEquiv.ext fun p ↦ by rw [AlgEquiv.trans_apply, translation_translation]

/-- **The inverse of a translation** is the translation by the negated linear form. -/
@[simp]
theorem translation_symm (f : M →ₗ[R] R) : (translation f).symm = translation (-f) :=
  AlgEquiv.ext fun p ↦ (AlgEquiv.symm_apply_eq _).2 <| by
    rw [translation_translation, neg_add_cancel, translation_zero]
    rfl

/-! ### The degree filtration -/

/-- The image of a generator under a translation lies in the first step of the degree
filtration. -/
private theorem translation_ι_mem_wordFiltration_one (f : M →ₗ[R] R) (m : M) :
    translation f (ι R M m) ∈ wordFiltration (ι R M) 1 := by
  rw [translation_ι]
  exact add_mem (apply_mem_wordFiltration_one _ m) (algebraMap_mem_wordFiltration _ _ 1)

/-- **Translation preserves the degree filtration**: `translation f p` has degree at most `n`
exactly when `p` does. -/
@[simp]
theorem translation_mem_wordFiltration_iff (f : M →ₗ[R] R) {n : ℕ} {p : SymmetricAlgebra R M} :
    translation f p ∈ wordFiltration (ι R M) n ↔ p ∈ wordFiltration (ι R M) n := by
  have hmem (f : M →ₗ[R] R) {p : SymmetricAlgebra R M} (hp : p ∈ wordFiltration (ι R M) n) :
      translation f p ∈ wordFiltration (ι R M) n :=
    map_mem_wordFiltration (ι R M) (translation f : _ →ₐ[R] _) (ι R M)
      (translation_ι_mem_wordFiltration_one f) hp
  refine ⟨fun h ↦ ?_, hmem f⟩
  simpa using hmem (-f) h

/-- **A translation is unipotent for the degree filtration**: on an element `p` homogeneous of
degree `n`, `translation f p - p` has degree strictly less than `n`. In degree zero this says that
a translation fixes the scalars. -/
theorem translation_sub_self_mem_wordFiltrationPrevious (f : M →ₗ[R] R) {n : ℕ}
    {p : SymmetricAlgebra R M} (hp : p ∈ homogeneousSubmodule R M n) :
    translation f p - p ∈ wordFiltrationPrevious (ι R M) n := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ hx hy =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    -- `(a + f a) τ(x) - a x = a (τ(x) - x) + f a • τ(x)`
    have hsplit : translation f (ι R M a * x) - ι R M a * x =
        ι R M a * (translation f x - x) + f a • translation f x := by
      rw [map_mul, translation_ι, Algebra.smul_def]
      ring
    have hτx : translation f x ∈ wordFiltration (ι R M) i :=
      (translation_mem_wordFiltration_iff f).2 (range_pow_le_wordFiltration _ i hx)
    rw [hsplit, Nat.succ_eq_add_one, wordFiltrationPrevious_succ]
    refine add_mem ?_ (Submodule.smul_mem _ _ hτx)
    have h := mul_mem_wordFiltrationPrevious_right (ι R M)
      (apply_mem_wordFiltration_one (ι R M) a) ih
    rwa [Nat.add_comm, wordFiltrationPrevious_succ] at h

end SymmetricAlgebra
