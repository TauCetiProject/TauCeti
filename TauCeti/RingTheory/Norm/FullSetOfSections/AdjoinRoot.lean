/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.FullSetOfSections.Basic
public import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Full sets of sections of `A[X]/(g)`

Let `g ∈ A[X]` be monic, so that `Z = Spec A[X]/(g)` is a finite free scheme over `Spec A`: it is
the closed subscheme of the affine line cut out by `g`, a relative effective Cartier divisor of
degree `deg g`. A section `s` of `Z → Spec A` is determined by the root `s(X) ∈ A` of `g` at which
it sits. This file proves that a family of sections `sᵢ` is a full set of sections of `Z` in the
sense of Katz–Mazur (`TauCeti.IsFullSetOfSections`) exactly when

  `g = ∏ i, (X - sᵢ(X))`,

that is, when the divisor `Z` is the sum of the divisors `[sᵢ]` of the sections. This is the
affine-line case of the comparison between full sets of sections and sums of section divisors,
and it is how one checks in practice that given points of a finite flat group scheme cut out by a
single monic equation, such as `μ_N = Spec A[X]/(X ^ N - 1)`, form a full set of sections.

Over a field with `g` separable this just says that the roots of `g` are listed once each. The
interest is in the other cases: in characteristic `p`, the single section `X = 1`, taken `p`
times, is a full set of sections of `Spec A[X]/(X ^ p - 1)`, because `X ^ p - 1 = (X - 1) ^ p`.

The proof computes norms on the base changes `T ⊗[A] A[X]/(g) ≅ T[X]/(g)`
(`AdjoinRoot.algebraTensorAlgEquiv`): the norm of the class of `p ∈ T[X]` is the resultant of `g`
and `p`, which is `∏ i, p(sᵢ(X))` when `g` splits as above (`AdjoinRoot.norm_mk_eq_prod_eval`).
Conversely the norm of `X - θ` over `A[X]`, for `θ` the class of `X`, recovers `g` itself.

## Main results

* `TauCeti.isFullSetOfSections_iff_eq_prod_X_sub_C`: for monic `g`, the sections `sᵢ` of
  `Spec A[X]/(g)` form a full set of sections if and only if `g = ∏ i, (X - sᵢ(X))`.
* `AlgHom.sectionBaseChange_algebraTensorAlgEquiv_symm_mk`: the base change of a section `s` to
  `T`, read on `T[X]/(g)`, evaluates a polynomial at the image of `s(X)`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §1.8.
-/

public section

open Polynomial AdjoinRoot TensorProduct

variable {A : Type*} [CommRing A] {g : A[X]}

namespace AlgHom

/-- The base change of a section `s` of `A[X]/(g)` to `T`, read through
`T ⊗[A] A[X]/(g) ≅ T[X]/(g)` (`AdjoinRoot.algebraTensorAlgEquiv`), evaluates a polynomial at the
image of the root `s(X)`. -/
@[simp]
theorem sectionBaseChange_algebraTensorAlgEquiv_symm_mk (s : AdjoinRoot g →ₐ[A] A)
    (T : Type*) [CommRing T] [Algebra A T] (p : T[X]) :
    s.sectionBaseChange T ((algebraTensorAlgEquiv T g).symm (AdjoinRoot.mk _ p)) =
      p.eval (algebraMap A T (s (root g))) := by
  exact (algHom_mk ((s.sectionBaseChange T).comp (algebraTensorAlgEquiv T g).symm.toAlgHom)
    p).trans (by simp [AlgHom.sectionBaseChange_tmul])

end AlgHom

namespace TauCeti

/-- **Full sets of sections of `A[X]/(g)`.** For a monic `g ∈ A[X]`, a family `s` of sections of
`Spec A[X]/(g) → Spec A` is a full set of sections if and only if `g` is the product of the linear
factors `X - sᵢ(X)` given by the roots `sᵢ(X)` of `g` at which the sections sit. -/
theorem isFullSetOfSections_iff_eq_prod_X_sub_C {ι : Type*} [Fintype ι] (hg : g.Monic)
    {s : ι → AdjoinRoot g →ₐ[A] A} :
    IsFullSetOfSections s ↔ g = ∏ i, (X - C (s i (root g))) := by
  refine ⟨fun h ↦ ?_, fun h ↦ isFullSetOfSections_iff.mpr fun T _ _ _ f ↦ ?_⟩
  · -- the norm of `X - θ` over `A[X]` is `g`, and its value at the `i`th section is `X - sᵢ(X)`
    have : Module.Free A (AdjoinRoot g) := .of_basis (powerBasis' hg).basis
    have : Module.Finite A (AdjoinRoot g) := .of_basis (powerBasis' hg).basis
    have hn := h.norm_eq A[X] ((algebraTensorAlgEquiv A[X] g).symm (mk _ (C X - X)))
    have hnorm : Algebra.norm A[X] (mk (g.map (algebraMap A A[X])) (C X - X)) = g := by
      rw [map_sub, mk_C, mk_X, norm_algebraMap_sub_root (hg.map _), eval_map,
        Polynomial.algebraMap_eq, eval₂_C_X]
    rw [Algebra.norm_eq_of_algEquiv, hnorm] at hn
    refine hn.trans (Finset.prod_congr rfl fun i _ ↦ ?_)
    rw [AlgHom.sectionBaseChange_algebraTensorAlgEquiv_symm_mk]
    simp
  · -- over `T`, the mapped `g` still splits, and the norm of a class `p` is `∏ i, p(sᵢ(X))`
    have hmap : g.map (algebraMap A T) = ∏ i, (X - C (algebraMap A T (s i (root g)))) := by
      conv_lhs => rw [h]
      simp [Polynomial.map_prod]
    obtain ⟨p, hp⟩ := mk_surjective (algebraTensorAlgEquiv T g f)
    rw [← (algebraTensorAlgEquiv T g).symm_apply_apply f, ← hp, Algebra.norm_eq_of_algEquiv,
      norm_mk_eq_prod_eval hmap]
    exact Finset.prod_congr rfl fun i _ ↦
      (AlgHom.sectionBaseChange_algebraTensorAlgEquiv_symm_mk _ _ _).symm

end TauCeti
