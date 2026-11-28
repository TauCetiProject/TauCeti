/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Finitely generated models of finitely presented algebras

A finitely presented algebra over `A` is obtained by base change from a finitely presented
algebra over a finitely generated `R`-subalgebra of `A`. This is the affine approximation
step for spreading out finitely presented algebras. For `R = ℤ`, finite generation makes
the coefficient subalgebra Noetherian by the Hilbert basis theorem.

The coefficient-model argument adapts
`Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg` from
`Mathlib.RingTheory.Smooth.NoetherianDescent` (Judith Ludwig and Christian Merten) to
finitely presented algebras. It uses `Algebra.Presentation.ModelOfHasCoeffs` and
`Algebra.Presentation.tensorModelOfHasCoeffsEquiv`.

## References

* The Stacks Project, Tags 00R0 and 05N9.
-/

public noncomputable section

universe u

open TensorProduct MvPolynomial

namespace Algebra.FinitePresentation

/-- A finitely presented algebra and any finite set of its elements descend to a finitely
 generated coefficient subalgebra. The selected elements lie in the image of the model. -/
theorem exists_subalgebra_fg_isPushout_of_finset
    (R : Type*) [CommRing R] (A : Type u) (B : Type*) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra.FinitePresentation A B] (s : Finset B) :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B ∧
        (s : Set B) ⊆ Set.range (algebraMap B₀ B) := by
  classical
  let P := Presentation.ofFinitePresentation A B
  choose Q hQ using P.aeval_val_surjective
  let T : Finset A := s.biUnion fun b ↦ (Q b).coeffs
  let A₀ : Subalgebra R A := Algebra.adjoin R (P.coeffs ∪ (T : Set A))
  have hA₀ : A₀.FG := Subalgebra.fg_def.mpr
    ⟨_, P.finite_coeffs.union T.finite_toSet, rfl⟩
  have : P.HasCoeffs A₀ := ⟨by
    rw [Subalgebra.setRange_algebraMap]
    exact (Set.subset_union_left).trans Algebra.subset_adjoin⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let e := P.tensorModelOfHasCoeffsEquiv A₀
  let f : B₀ →ₐ[A₀] B :=
    (e.toAlgHom.restrictScalars A₀).comp Algebra.TensorProduct.includeRight
  let _ : Algebra B₀ B := f.toRingHom.toAlgebra
  have : IsScalarTower A₀ B₀ B := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  refine ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl⟩, ?_⟩
  intro b hb
  have hcoeff : ((Q b).coeffs : Set A) ⊆ A₀ := by
    intro a ha
    exact Algebra.subset_adjoin (Or.inr (Finset.mem_biUnion.mpr ⟨b, hb, ha⟩))
  obtain ⟨q, hq⟩ : Q b ∈ Set.range (MvPolynomial.map (algebraMap A₀ A)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    exact fun a ha ↦ ⟨⟨a, hcoeff ha⟩, rfl⟩
  refine ⟨Ideal.Quotient.mk _ q, ?_⟩
  -- The model algebra map is the right tensor inclusion followed by `e`.
  change e (1 ⊗ₜ Ideal.Quotient.mk _ q) = b
  rw [← hQ b, ← hq, MvPolynomial.aeval_map_algebraMap,
    ← P.tensorModelOfHasCoeffsEquiv_symm_tmul A₀]
  exact e.apply_symm_apply _

/-- A finitely presented `A`-algebra descends to a finitely generated `R`-subalgebra
`A₀` of `A`, with a finitely presented model `B₀` and a pushout square.
Taking `R = ℤ` makes `A₀` Noetherian by finite generation and the Hilbert basis theorem. -/
theorem exists_subalgebra_fg_isPushout
    (R : Type*) [CommRing R] (A : Type u) (B : Type*) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  obtain ⟨A₀, B₀, _, _, _, _, hA₀, hB₀, hpush, -⟩ :=
    exists_subalgebra_fg_isPushout_of_finset R A B ∅
  exact ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀, hB₀, hpush⟩

/-- A finitely presented algebra with two specified elements descends to a noetherian model. -/
theorem exists_noetherian_model {A : Type u} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (f t : B) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ A)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Algebra.FiniteType R₀ S₀)
      (e : A ⊗[R₀] S₀ ≃ₐ[A] B) (f₀ t₀ : S₀), e (1 ⊗ₜ f₀) = f ∧ e (1 ⊗ₜ t₀) = t := by
  classical
  obtain ⟨R₀, S₀, _, _, _, _, hR₀, _, _, hmem⟩ :=
    exists_subalgebra_fg_isPushout_of_finset ℤ A B {f, t}
  have : Algebra.FiniteType ℤ R₀ := (Subalgebra.fg_iff_finiteType R₀).mp hR₀
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨f₀, hf₀⟩ := hmem (by simp : f ∈ ({f, t} : Finset B))
  obtain ⟨t₀, ht₀⟩ := hmem (by simp : t ∈ ({f, t} : Finset B))
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, S₀, inferInstance, inferInstance,
    inferInstance, Algebra.IsPushout.equiv R₀ A S₀ B, f₀, t₀, ?_, ?_⟩
  · simpa only [Algebra.IsPushout.equiv_tmul, map_one, one_mul] using hf₀
  · simpa only [Algebra.IsPushout.equiv_tmul, map_one, one_mul] using ht₀

end Algebra.FinitePresentation
