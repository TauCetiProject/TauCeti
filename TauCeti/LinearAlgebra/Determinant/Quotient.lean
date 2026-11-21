/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Projective

/-!
# The determinant of an endomorphism induced on a quotient

An endomorphism `f` of a module `M` that preserves a submodule `p` induces an endomorphism
`Submodule.mapQ p p f _` of `M ⧸ p`. Given a complement `q` of `p`, the determinant of that
induced endomorphism equals the determinant of the **compression** of `f` to `q`: inclusion into
`M`, then `f`, then projection onto `q` along `p`. This gives a basis-free handle on the quotient
determinant inside `M` itself, where it can be computed and varies continuously with `f`.

The same block-triangular computation, Mathlib's `LinearMap.det_eq_det_mul_det`, is restated for
a short exact sequence `0 → M' → M → M'' → 0` of free modules and compatible endomorphisms of its
three terms: the determinant on `M` is the product of the determinants on `M'` and `M''`. This is
the form in which it is applied to sequences of modules with an action, where the submodule and
the quotient are given as modules in their own right rather than as `range i` and `M ⧸ range i`.

## Main results

* `LinearMap.det_mapQ_of_isCompl`: the determinant of the endomorphism induced on `M ⧸ p` is the
  determinant of the compression to a complement of `p`.
* `LinearMap.det_eq_det_mul_det_of_exact`: the determinant is multiplicative along a short exact
  sequence of free modules.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The determinant of a quotient endomorphism is that of its compression to a complement.** -/
theorem det_mapQ_of_isCompl {p q : Submodule R M} (hpq : IsCompl p q) (f : M →ₗ[R] M)
    (hf : p ≤ p.comap f) :
    LinearMap.det (Submodule.mapQ p p f hf) =
      LinearMap.det (q.projectionOnto p hpq.symm ∘ₗ f ∘ₗ q.subtype) := by
  rw [← LinearMap.det_conj (Submodule.mapQ p p f hf) (Submodule.quotientEquivOfIsCompl p q hpq)]
  refine congrArg LinearMap.det (LinearMap.ext fun x => ?_)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype,
    Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk]

section Exact

variable {M' M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- **The determinant is multiplicative along a short exact sequence.** Let
`0 → M' → M → M'' → 0` be a short exact sequence, given by an injective `i`, a surjective `p` and
`Function.Exact i p`, with `M` finite and `M'`, `M''` free. If endomorphisms `f'`, `f` and `f''`
of the three terms are intertwined by `i` and `p`, then `det f = det f' * det f''`. -/
theorem det_eq_det_mul_det_of_exact [Module.Finite R M] [Module.Free R M'] [Module.Free R M'']
    {i : M' →ₗ[R] M} {p : M →ₗ[R] M''} (hi : Function.Injective i) (hip : Function.Exact i p)
    (hp : Function.Surjective p) {f : M →ₗ[R] M} {f' : M' →ₗ[R] M'} {f'' : M'' →ₗ[R] M''}
    (hf' : f ∘ₗ i = i ∘ₗ f') (hf'' : p ∘ₗ f = f'' ∘ₗ p) :
    f.det = f'.det * f''.det := by
  -- The sequence splits because `M''` is projective, so `M'` is a quotient of the finite `M`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have e := (hip.splitSurjectiveEquiv hi ⟨s, hs⟩).1
  have : Module.Finite R M' := .of_surjective (fst R M' M'' ∘ₗ e.toLinearMap)
    (Prod.fst_surjective.comp e.surjective)
  -- Identify `M'` with `range i` and `M''` with `M ⧸ range i`, and apply Mathlib's block form.
  let W := LinearMap.range i
  have hW : W ≤ W.comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f' x, (congr($hf' x)).symm⟩
  let e' : M' ≃ₗ[R] W := LinearEquiv.ofInjective i hi
  let e'' : (M ⧸ W) ≃ₗ[R] M'' :=
    (Submodule.quotEquivOfEq _ _ hip.linearMap_ker_eq.symm).trans (p.quotKerEquivOfSurjective hp)
  have : Module.Free R W := .of_equiv e'
  have : Module.Finite R W := .equiv e'
  have : Module.Free R (M ⧸ W) := .of_equiv e''.symm
  rw [LinearMap.det_eq_det_mul_det W f hW, ← LinearMap.det_conj f' e',
    ← LinearMap.det_conj f'' e''.symm]
  congr 2
  · ext x
    obtain ⟨y, rfl⟩ := e'.surjective x
    simp only [restrict_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, Submodule.coe_mk, e']
    exact congr($hf' y)
  · ext x
    apply e''.injective
    simpa [e''] using congr($hf'' x)

end Exact

end LinearMap
