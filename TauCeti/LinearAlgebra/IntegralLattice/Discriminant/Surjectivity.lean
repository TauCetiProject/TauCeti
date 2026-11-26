/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.ModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.HyperbolicPlaneModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.CharTwo

/-!
# Surjectivity of `O(M(2)) → O(q_{M(2)})` for `M = U ⊕ E₈(-1)`

Let `M` be an even unimodular lattice and `M(2) = 2 • M` its rescaling by two. The discriminant
form of `M(2)` is the quadratic space `M / 2M` over `𝔽₂` with the form `Q₂(x mod 2) = B(x, x) / 2
mod 2`, whose polar form is nondegenerate, and an isometry of `M` acts on it by reduction modulo
two (`TauCeti.IntegralLattice.IsUnimodular.discriminantOrthogonalGroupEquivModTwo`). The reflection
in a vector of norm `±2` reduces to the orthogonal transvection in its class. By Dieudonné's theorem
the transvections generate the orthogonal group of `M / 2M` unless it is the sum of two hyperbolic
planes, which can only happen in rank four. So when `M` has rank other than four and every class
of `M / 2M` with `Q₂ = 1` contains a vector of norm `±2`, every isometry of the discriminant form
of `M(2)` is induced by an integral isometry of `M(2)`.

For `M = U ⊕ N` with `N` even unimodular, every class with `Q₂ = 1` contains a vector of norm `-2`
(`TauCeti.IntegralLattice.mk_mem_normClassesModTwo_neg_two_hyperbolicPlane_orthogonalSum_iff`).
In particular `O(S) → O(q_S)` is surjective for every even lattice `S` isometric to
`U(2) ⊕ E₈(-2) = (U ⊕ E₈(-1))(2)`, the invariant lattice of the involution of the K3 lattice whose
quotients are the Enriques surfaces. For such `S` the group `O(q_S)` is therefore the quotient of
`O(S)` by its discriminant kernel, the kernel of `O(S) → O(q_S)`
(`TauCeti.IntegralLattice.Isometry.ker_discriminantOrthogonalHom`).

## Main results

* `TauCeti.IntegralLattice.IsUnimodular.discriminantOrthogonalHom_smul_two_surjective`: for an
  even unimodular `M` of rank other than four whose classes with `Q₂ = 1` all contain vectors of
  norm `±2`, `O(M(2)) → O(q_{M(2)})` is surjective.
* `discriminantOrthogonalHom_smul_two_hyperbolicPlane_orthogonalSum_surjective`: the
  same for `M = U ⊕ N` with `N` even unimodular of rank other than two.
* `TauCeti.IntegralLattice.discriminantOrthogonalHom_surjective_of_isometry_scale_two`:
  `O(S) → O(q_S)` is surjective for every even nondegenerate `S` isometric to `U(2) ⊕ E₈(-2)`.

## References

* V. Gritsenko and K. Hulek, *Moduli of polarized Enriques surfaces*, §2.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Theorem 3.6.3.
* A. Hunnell, J. Hutchens and N. Schwartz, *On involutions of type O(q,k) over a field of
  characteristic two*, arXiv:1903.09904v3, §3.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **Discriminant surjectivity for `M(2)`.** Let `L` be an even unimodular lattice of rank other
than four such that every class of `L / 2L` on which `Q₂(x mod 2) = B(x, x) / 2 mod 2` is `1`
contains a vector of norm `2` or `-2`. Then every isometry of the discriminant quadratic form of
`L(2)` is induced by an isometry of `L(2)`: the reflections in these vectors already induce all of
them. -/
theorem IsUnimodular.discriminantOrthogonalHom_smul_two_surjective (hu : L.IsUnimodular)
    (hL : L.IsEven) [((2 : ℤ) • L).IsNondegenerate] (hrank : finrank ℤ L ≠ 4)
    (hroot : ∀ c : QuotSMulTop (2 : ℤ) L, (L.quadraticForm hL).reduceModTwo c = 1 →
      c ∈ L.normClassesModTwo 2 ∨ c ∈ L.normClassesModTwo (-2)) :
    Function.Surjective (Isometry.discriminantOrthogonalHom ((2 : ℤ) • L) (hL.smul 2)) := by
  set E := hu.discriminantOrthogonalGroupEquivModTwo hL
  have hH : (Isometry.discriminantOrthogonalHom ((2 : ℤ) • L) (hL.smul 2)).range.map
      E.toMonoidHom = ⊤ := by
    refine QuadraticMap.subgroup_eq_top_of_reflection_mem_of_nondegenerate_polarBilin
      (L.quadraticForm hL).reduceModTwo (nondegenerate_polarBilin_reduceModTwo_quadraticForm hL hu)
      ?_ _ fun v _ ↦ ?_
    · -- the exceptional space of Dieudonné's theorem, two hyperbolic planes, has dimension four
      rintro - ⟨e⟩
      apply hrank
      rw [← finrank_zmod_quotSMulTop_two, e.toLinearEquiv.finrank_eq]
      simp [finrank_pi_fintype]
    have hv : (L.quadraticForm hL).reduceModTwo v = 1 := by
      have := Invertible.ne_zero ((L.quadraticForm hL).reduceModTwo v)
      generalize (L.quadraticForm hL).reduceModTwo v = t at this ⊢
      revert t
      decide
    obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ :=
      (hroot v hv).imp L.mem_normClassesModTwo.mp L.mem_normClassesModTwo.mp
    · have hx : L.integralNorm x = 2 := by
        exact_mod_cast (L.integralNorm_cast x).trans (mem_vectorsOfNorm.mp hx)
      refine ⟨_, ⟨(rootReflection x hx).smul 2, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom,
        discriminantOrthogonalGroupEquivModTwo_discriminantOrthogonalHom_smul,
        Isometry.reductionModTwoHom_rootReflection]
    · have hx : L.integralNorm x = -2 := by
        exact_mod_cast (L.integralNorm_cast x).trans (mem_vectorsOfNorm.mp hx)
      refine ⟨_, ⟨(negRootReflection x hx).smul 2, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom,
        discriminantOrthogonalGroupEquivModTwo_discriminantOrthogonalHom_smul,
        Isometry.reductionModTwoHom_negRootReflection]
  intro σ
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Subgroup.mem_map.mp (hH ▸ Subgroup.mem_top (E σ))
  exact ⟨g, E.injective hg⟩

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {N : IntegralLattice W}

/-- **Discriminant surjectivity for `(U ⊕ N)(2)`.** For an even unimodular lattice `N` of rank
other than two, every isometry of the discriminant quadratic form of `(U ⊕ N)(2)` is induced by an
isometry of `(U ⊕ N)(2)`, namely by a product of reflections in vectors of norm `-2` of `U ⊕ N`. -/
theorem discriminantOrthogonalHom_smul_two_hyperbolicPlane_orthogonalSum_surjective
    (hN : N.IsEven) (hNu : N.IsUnimodular) (hrank : finrank ℤ N ≠ 2)
    [((2 : ℤ) • hyperbolicPlane.orthogonalSum N).IsNondegenerate] :
    Function.Surjective (Isometry.discriminantOrthogonalHom
      ((2 : ℤ) • hyperbolicPlane.orthogonalSum N)
      (((isEven_orthogonalSum_iff _ _).mpr ⟨isEven_hyperbolicPlane, hN⟩).smul 2)) := by
  have hM := (isEven_orthogonalSum_iff _ _).mpr ⟨isEven_hyperbolicPlane, hN⟩
  refine ((isUnimodular_orthogonalSum_iff _ _).mpr ⟨isUnimodular_hyperbolicPlane, hNu⟩)
    |>.discriminantOrthogonalHom_smul_two_surjective hM ?_ fun c hc ↦ Or.inr ?_
  · rw [finrank_orthogonalSum, finrank_carrier, finrank_fin_fun]
    omega
  · induction c using Submodule.Quotient.induction_on with
    | _ x =>
      exact (mk_mem_normClassesModTwo_neg_two_hyperbolicPlane_orthogonalSum_iff hN hNu x).mpr hc

/-- **Discriminant surjectivity for `U(2) ⊕ E₈(-2)`.** For every even nondegenerate lattice `S`
isometric to the rescaling by two of `U ⊕ E₈(-1)`, every isometry of the discriminant quadratic
form of `S` is induced by an integral isometry of `S`: the homomorphism `O(S) → O(q_S)` is
surjective. Gritsenko–Hulek, *Moduli of polarized Enriques surfaces*, §2, as a consequence of
Nikulin's Theorem 3.6.3. -/
theorem discriminantOrthogonalHom_surjective_of_isometry_scale_two (S : IntegralLattice V)
    [S.IsNondegenerate] (hS : S.IsEven)
    (e : S.Isometry ((2 : ℤ) • hyperbolicPlane.orthogonalSum (-typeE₈RootLattice))) :
    Function.Surjective (Isometry.discriminantOrthogonalHom S hS) := by
  have := e.isNondegenerate
  rw [Isometry.discriminantOrthogonalHom_surjective_iff hS (e.isEven_iff.mp hS) e]
  refine discriminantOrthogonalHom_smul_two_hyperbolicPlane_orthogonalSum_surjective
    ((isEven_neg_iff _).mpr isEven_typeE₈RootLattice) ?_ ?_
  · rw [isUnimodular_iff_discriminant_eq_one, discriminant_neg,
      ← isUnimodular_iff_discriminant_eq_one]
    exact isUnimodular_typeE₈RootLattice
  · rw [finrank_neg, finrank_carrier, finrank_fin_fun]
    decide

end TauCeti.IntegralLattice
