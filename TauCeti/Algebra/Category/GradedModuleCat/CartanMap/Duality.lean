/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Projective/simple duality for the q-Euler pairing

For a finite-dimensional graded algebra, suppose the classes of the degree-zero idempotent
projectives `Aeᵢ` form a Laurent basis, and the idempotents cut out an exhaustive family of
graded simples `Sᵢ` with `gdim(eᵢ Sⱼ) = δᵢⱼ`. The projective/module q-Euler pairing then
identifies the projective Grothendieck group semilinearly with the linear dual of the module
Grothendieck group. In the other direction it identifies the module Grothendieck group linearly
with the semilinear dual of the projective group.

The projective basis maps to the usual dual basis of the simple-class basis. Coordinates in the
projective basis are recovered by pairing against simples and applying `LaurentPolynomial.invert`.
Thus both radicals vanish, and every functional on either side has a unique representing class.
No finite-global-dimension hypothesis is needed: only projectives occur in the first argument.
The finite index hypothesis is needed for surjectivity onto the full dual.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Sections 2.2 and
  3.1--3.2, for q-antilinearity and the distinction between left and right duals.

The Kronecker pairing is `TauCeti.gradedProjectiveExtEuler_basis`; dual bases use Mathlib's
`Module.Basis.dualBasis`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Finite I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include S he he₀ hI hne hself hS bP hbP

/-- The projective basis vectors are the linear dual basis of the graded simple classes
under the q-Euler pairing. -/
theorem gradedProjectiveExtEuler_basis_eq_dualBasis (i : I) :
    gradedProjectiveExtEuler 𝒜 (bP i) =
      (open scoped Classical in
        (gradedSimpleClassBasis S he he₀ hne hself hS).dualBasis i) := by
  classical
  apply LinearMap.ext
  intro y
  rw [hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_repr S he he₀ hI hne hself hS,
    Module.Basis.dualBasis_apply]

omit hS in
/-- Pairing a projective class against a simple class conjugates its projective coordinate. -/
@[simp]
theorem gradedProjectiveExtEuler_simple_eq_invert_repr
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (i : I) :
    gradedProjectiveExtEuler 𝒜 x (LaurentK0.of.{uA} _ (S i)) = invert (bP.repr x i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hpair (j : I) : gradedProjectiveExtEuler 𝒜 (bP j) (LaurentK0.of.{uA} _ (S i)) =
      if j = i then 1 else 0 := by
    rw [hbP]
    exact gradedProjectiveExtEuler_basis S he he₀ hI hne hself j i
  conv_lhs => rw [← bP.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair]
  simp

/-- The q-Euler pairing represents every linear functional on the module Grothendieck group
by exactly one projective class. -/
theorem gradedProjectiveExtEuler_bijective :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro x y hxy
    apply bP.ext_elem
    intro i
    apply (invert (R := ℤ)).injective
    simpa only [gradedProjectiveExtEuler_simple_eq_invert_repr S he he₀ hI hne hself bP hbP]
      using DFunLike.congr_fun hxy (LaurentK0.of.{uA} _ (S i))
  · intro f
    refine ⟨∑ i, invert (f (LaurentK0.of.{uA} _ (S i))) • bP i, ?_⟩
    apply (gradedSimpleClassBasis S he he₀ hne hself hS).ext
    intro j
    rw [gradedSimpleClassBasis_apply]
    rw [gradedProjectiveExtEuler_simple_eq_invert_repr S he he₀ hI hne hself bP hbP]
    simp [Finsupp.single_apply, involutive_invert (R := ℤ) _]

/-- Every `q ↦ q⁻¹` semilinear functional on the projective Grothendieck group is represented
by exactly one module class in the second argument of the q-Euler pairing. -/
theorem gradedProjectiveExtEuler_flip_bijective :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro x y hxy
    apply (gradedSimpleClassBasis S he he₀ hne hself hS).ext_elem
    intro i
    simpa only [LinearMap.flip_apply,
      gradedProjectiveExtEuler_basis_eq_dualBasis S he he₀ hI hne hself hS bP hbP,
      Module.Basis.dualBasis_apply] using DFunLike.congr_fun hxy (bP i)
  · intro f
    refine ⟨∑ i, f (bP i) • LaurentK0.of.{uA} _ (S i), ?_⟩
    apply bP.ext
    intro j
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.flip_apply,
      gradedProjectiveExtEuler_basis_eq_dualBasis S he he₀ hI hne hself hS bP hbP]
    have hpair (i : I) :
        (gradedSimpleClassBasis S he he₀ hne hself hS).dualBasis j
          (LaurentK0.of.{uA} _ (S i)) = if j = i then 1 else 0 := by
      rw [← gradedSimpleClassBasis_apply S he he₀ hne hself hS i]
      simpa only [eq_comm] using
        (gradedSimpleClassBasis S he he₀ hne hself hS).dualBasis_apply_self j i
    simp only [hpair]
    simp

/-- Both radicals of the projective/module q-Euler pairing vanish under the dual-basis
hypotheses. This does not identify the two Grothendieck groups with one another. -/
theorem gradedProjectiveExtEuler_nondegenerate :
    (gradedProjectiveExtEuler 𝒜).Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_bijective S he he₀ hI hne hself hS bP hbP).injective
  · rw [LinearMap.separatingRight_iff_flip_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_flip_bijective S he he₀ hI hne hself hS bP hbP).injective

end TauCeti
