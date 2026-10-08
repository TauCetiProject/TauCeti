/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.KrullSchmidt.AdicComplete
import TauCeti.Algebra.Module.Projective.Schanuel

/-!
# Krull-Schmidt cancellation over finite `p`-adic group algebras

For a finite monoid `G`, in particular a finite group, finitely generated modules over the group
algebra `ℤ_p[G]` cancel from direct sums: `M × P ≃ N × P` with `P` finitely generated gives
`M ≃ N`. This is the specialization to `R = ℤ_p` and `A = ℤ_p[G]` of
`TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete`; a finitely generated
`ℤ_p[G]`-module is finitely generated over `ℤ_p` because `ℤ_p[G]` is.

⚠ The corresponding statement over `ℤ[G]` fails in general: Swan's stably free, non-free modules
over the integral group rings of generalized quaternion groups. The completeness of `ℤ_p` is what
makes the endomorphism rings of indecomposable `ℤ_p[G]`-modules local.

Together with Schanuel's lemma, cancellation shows that two maps with the same range from a
finitely generated projective `ℤ_p[G]`-module have isomorphic kernels. In particular the kernel of
a surjection from `ℤ_p[G]^n` onto a module depends only on `n` and the module, not on the
surjection.

## Main results

* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv`: finitely generated `ℤ_p[G]`-modules cancel.
* `TauCeti.nonempty_ker_linearEquiv_of_range_eq`: maps with the same range from a finitely
  generated projective `ℤ_p[G]`-module have isomorphic kernels.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(i).
-/

public section

namespace TauCeti

universe u v w x

variable (p : ℕ) [Fact p.Prime] (G : Type u) [Monoid G] [Finite G]

/-- **Krull-Schmidt cancellation over `ℤ_p[G]`** (NSW (5.6.10)(i)). For a finite monoid `G`, in
particular a finite group, a finitely generated `ℤ_p[G]`-module `P` cancels from direct sums: a
linear equivalence `M × P ≃ N × P` induces a linear equivalence `M ≃ N`. No hypothesis is placed
on `M` and `N`. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv (M : Type v) (N : Type w) (P : Type x)
    [AddCommGroup M] [Module (MonoidAlgebra ℤ_[p] G) M]
    [AddCommGroup N] [Module (MonoidAlgebra ℤ_[p] G) N]
    [AddCommGroup P] [Module (MonoidAlgebra ℤ_[p] G) P]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) P]
    (h : Nonempty ((M × P) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N × P))) :
    Nonempty (M ≃ₗ[MonoidAlgebra ℤ_[p] G] N) := by
  -- Give `P` the `ℤ_p`-module structure restricted from `ℤ_p[G]`; then `P` is finite over `ℤ_p`.
  let _ : Module ℤ_[p] P := .compHom P (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P :=
    IsScalarTower.of_compHom ℤ_[p] (MonoidAlgebra ℤ_[p] G) P
  have : Module.Finite ℤ_[p] P := .trans (MonoidAlgebra ℤ_[p] G) P
  exact nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete ℤ_[p] h

variable {p G}

open LinearMap

/-- **Kernels of maps with the same range.** Two `ℤ_p[G]`-linear maps `a b : P → E` with the same
range, from a finitely generated projective `ℤ_p[G]`-module `P`, have isomorphic kernels. In
particular two surjections from `ℤ_p[G]^n` onto the same module have isomorphic kernels. -/
theorem nonempty_ker_linearEquiv_of_range_eq {P : Type v} {E : Type w}
    [AddCommGroup P] [Module (MonoidAlgebra ℤ_[p] G) P]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) P] [Module.Projective (MonoidAlgebra ℤ_[p] G) P]
    [AddCommGroup E] [Module (MonoidAlgebra ℤ_[p] G) E]
    {a b : P →ₗ[MonoidAlgebra ℤ_[p] G] E} (h : LinearMap.range a = LinearMap.range b) :
    Nonempty (LinearMap.ker a ≃ₗ[MonoidAlgebra ℤ_[p] G] LinearMap.ker b) := by
  -- Schanuel's lemma: an automorphism `e` of `P × P` with `a ∘ fst = b ∘ snd ∘ e`.
  obtain ⟨e, he⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp h
  -- `e` carries `ker (a ∘ fst) = ker a × P` onto `ker (b ∘ snd) = P × ker b`.
  have hmap : Submodule.map e.toLinearMap ((ker a).prod ⊤) = (⊤ : Submodule _ P).prod (ker b) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa [Submodule.mem_map_equiv] using congr($(LinearMap.congr_fun he x) = 0)
  have hl : range ((ker a).subtype.prodMap (LinearMap.id : P →ₗ[_] P)) = (ker a).prod ⊤ := by
    rw [range_prodMap, Submodule.range_subtype, range_id]
  have hr : range ((LinearMap.id : P →ₗ[_] P).prodMap (ker b).subtype) = (⊤ : Submodule _ P).prod
      (ker b) := by
    rw [range_prodMap, Submodule.range_subtype, range_id]
  let l := LinearEquiv.ofInjective ((ker a).subtype.prodMap (LinearMap.id : P →ₗ[_] P))
    ((ker a).injective_subtype.prodMap Function.injective_id)
  let r := LinearEquiv.ofInjective ((LinearMap.id : P →ₗ[_] P).prodMap (ker b).subtype)
    (Function.injective_id.prodMap (ker b).injective_subtype)
  -- So `ker a × P ≃ P × ker b ≃ ker b × P`, and `P` cancels.
  exact nonempty_linearEquiv_of_prod_linearEquiv p G _ _ P
    ⟨l ≪≫ₗ .ofEq _ _ hl ≪≫ₗ e.ofSubmodules _ _ hmap ≪≫ₗ .ofEq _ _ hr.symm ≪≫ₗ r.symm ≪≫ₗ
      .prodComm _ _ _⟩

end TauCeti
