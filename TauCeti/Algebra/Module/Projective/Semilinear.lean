/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Lifting semilinear maps out of a projective module

Let `σ : R →+* S` be a ring homomorphism, `P` a projective `R`-module and `F : M → N` a
surjective `S`-linear map. Then every `σ`-semilinear map `P → N` lifts through `F` to a
`σ`-semilinear map `P → M`. This is Mathlib's lifting property
`Module.projective_lifting_property` applied to `M` and `N` with scalars restricted along `σ`,
since a `σ`-semilinear map out of `P` is an `R`-linear map into the restricted module.

It is the form of the lifting property used to show that extension of scalars along a ring
homomorphism of possibly noncommutative rings preserves projectivity: an `S`-linear map out of
`S ⊗_R P` is the same as a `σ`-semilinear map out of `P`.

## Main results

* `Module.projective_lifting_property_semilinear`: semilinear maps out of a projective module lift
  along surjective linear maps.
* `Module.exists_surjective_projective_ker_of_semilinearEquiv`: a presentation with projective
  kernel transports along a semilinear equivalence.
-/

public section

namespace Module

variable {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {P : Type*} [AddCommMonoid P] [Module R P]
  {M N : Type*} [AddCommMonoid M] [Module S M] [AddCommMonoid N] [Module S N]

/-- **The lifting property of a projective module, for semilinear maps.** If `P` is a projective
`R`-module and `F : M →ₗ[S] N` is surjective, then every `σ`-semilinear map `g : P → N` factors
as `F ∘ h` for a `σ`-semilinear map `h : P → M`. -/
theorem projective_lifting_property_semilinear [Module.Projective R P] (F : M →ₗ[S] N)
    (hF : Function.Surjective F) (g : P →ₛₗ[σ] N) : ∃ h : P →ₛₗ[σ] M, F.comp h = g := by
  -- Restrict the scalars of `M` and `N` along `σ`, so that `F` and `g` become `R`-linear.
  let : Module R M := Module.compHom M σ
  let : Module R N := Module.compHom N σ
  obtain ⟨h, hh⟩ := projective_lifting_property
    ({ F.toAddMonoidHom with map_smul' := fun r m ↦ F.map_smul (σ r) m } : M →ₗ[R] N)
    ({ g.toAddMonoidHom with map_smul' := g.map_smulₛₗ } : P →ₗ[R] N) hF
  exact ⟨{ h.toAddMonoidHom with map_smul' := h.map_smul },
    LinearMap.ext fun p ↦ LinearMap.congr_fun hh p⟩

/-- **A presentation with projective kernel transports along a semilinear equivalence.** Let
`Φ : R ≃+* R'` be a ring isomorphism and `e : M ≃ₛₗ[Φ] M'` a `Φ`-semilinear equivalence. If `M'` is
a quotient `(ι → R') → M'` by a projective kernel, then so is `M` as a quotient of
`ι → R`. -/
theorem exists_surjective_projective_ker_of_semilinearEquiv {R R' : Type*} [Semiring R]
    [Semiring R'] {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M']
    [Module R' M'] (Φ : R ≃+* R') [RingHomInvPair (Φ : R →+* R') (Φ.symm : R' →+* R)]
    [RingHomInvPair (Φ.symm : R' →+* R) (Φ : R →+* R')] (e : M ≃ₛₗ[(Φ : R →+* R')] M') {ι : Type*}
    (f' : (ι → R') →ₗ[R'] M') (hf' : Function.Surjective f')
    (hker : Module.Projective R' (LinearMap.ker f')) :
    ∃ f : (ι → R) →ₗ[R] M, Function.Surjective f ∧ Module.Projective R (LinearMap.ker f) := by
  let PΦ : (ι → R) ≃ₛₗ[(Φ : R →+* R')] (ι → R') :=
    { toFun v i := Φ (v i)
      invFun v i := Φ.symm (v i)
      map_add' _ _ := funext fun _ ↦ map_add Φ _ _
      map_smul' _ _ := funext fun _ ↦ map_mul Φ _ _
      left_inv _ := funext fun _ ↦ Φ.symm_apply_apply _
      right_inv _ := funext fun _ ↦ Φ.apply_symm_apply _ }
  let f : (ι → R) →ₗ[R] M := e.symm.toLinearMap.comp (f'.comp PΦ.toLinearMap)
  have hker' : (LinearMap.ker f).map (PΦ : (ι → R) →ₛₗ[(Φ : R →+* R')] (ι → R')) =
      LinearMap.ker f' := by
    ext v
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    -- Unfold the local definitions of `f` and of the inverse of `PΦ`.
    change e.symm (f' (PΦ (PΦ.symm v))) = 0 ↔ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_eq_zero_iff]
  exact ⟨f, e.symm.surjective.comp (hf'.comp PΦ.surjective),
    .of_equiv (σ := (Φ.symm : R' →+* R)) (σ' := (Φ : R →+* R'))
      (PΦ.ofSubmodules _ _ hker').symm⟩

end Module
