/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Finite
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.GeometricallyReduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.Algebra.CharP.Reduced

/-!
# The exceptional F₄ endomorphism is an isogeny

The exceptional endomorphism of the short-root F₄ carrier over `𝔽₂` is finite and faithfully
flat. Its Frobenius-square identity already gives finiteness and an involution on the prime
spectrum. Smoothness of the carrier makes its coordinate ring geometrically reduced, so the
finite dominant homomorphism criterion supplies faithful flatness.

The result is stated both on coordinate Hopf algebras and on the actual carrier group scheme.
On points, the exceptional endomorphism is injective over every reduced coefficient algebra
and bijective over every perfect coefficient algebra over `𝔽₂`. These pointwise
statements do not assert that the group-scheme endomorphism is an isomorphism: infinitesimal
points of its kernel can persist over nonreduced algebras.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.

The coordinate endomorphism and its Frobenius square are constructed in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny`; the finiteness and
dominance inputs are from `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Finite`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.F4ShortRoot.PrimeField

universe u

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "Q" => CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
  (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- The exceptional coordinate endomorphism is finite and faithfully flat. -/
theorem isIsogeny_quotientIsogeny : CommHopfAlgCat.IsIsogeny quotientIsogeny := by
  have hsmooth : Algebra.Smooth 𝔽₂ Q := by
    rw [← definingIdeal_def]
    infer_instance
  let _ : Algebra.IsGeometricallyReduced 𝔽₂ Q :=
    @isGeometricallyReduced_of_smooth 𝔽₂ Q _ _ _ hsmooth
  exact (CommHopfAlgCat.isIsogeny_iff_finite_and_dominant quotientIsogeny).2
    ⟨finite_quotientIsogeny, comap_quotientIsogeny_involutive.surjective.denseRange⟩

/-- The exceptional endomorphism of the prime-field F₄ carrier group scheme is an isogeny. -/
theorem isIsogeny_specialIsogenyHom : GroupScheme.IsIsogeny specialIsogenyHom := by
  rw [specialIsogenyHom_eq_map_quotientIsogeny]
  apply GroupScheme.IsIsogeny.comp
  · exact GroupScheme.isIsogeny_of_isIso _
  · apply GroupScheme.IsIsogeny.comp
    · exact (CommHopfAlgCat.isIsogeny_iff_isIsogeny_hopfSpec_map quotientIsogeny).1
        isIsogeny_quotientIsogeny
    · exact GroupScheme.isIsogeny_of_isIso _

/-- Over a reduced coefficient algebra over `𝔽₂`, the exceptional endomorphism is injective
on points. -/
theorem specialIsogeny_injective (A : Type u) [CommRing A] [Algebra 𝔽₂ A] [IsReduced A] :
    Function.Injective (specialIsogeny A) := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact fun _ _ _ => Subsingleton.elim _ _
  | inr h =>
    let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap 𝔽₂ A).injective 2
    intro g h heq
    have hfrob := congrArg (specialIsogeny A) heq
    simp only [specialIsogeny_specialIsogeny] at hfrob
    apply Subtype.ext
    ext i j
    apply frobenius_inj A 2
    have hentry := congrArg (fun p : points A =>
      ((p : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) i j) hfrob
    simpa only [coe_frobenius_apply, pow_one, _root_.frobenius_def] using hentry

/-- Over every perfect coefficient algebra, the exceptional endomorphism is surjective on
the matrix-valued carrier points. In particular this applies to finite and algebraically
closed fields of characteristic two. -/
theorem specialIsogeny_surjective (A : Type u) [CommRing A] [Algebra 𝔽₂ A] [PerfectRing A 2] :
    Function.Surjective (specialIsogeny A) := by
  let e : A ≃ₐ[𝔽₂] A := AlgEquiv.ofBijective (FiniteField.frobeniusAlgHom 𝔽₂ A)
    (by simpa only [FiniteField.coe_frobeniusAlgHom, ZMod.card] using
      (PerfectRing.bijective_frobenius (R := A) (p := 2)))
  intro g
  refine ⟨specialIsogeny A (pointsMap e.symm.toAlgHom g), ?_⟩
  have hcomp : (FiniteField.frobeniusAlgHom 𝔽₂ A).comp e.symm.toAlgHom = AlgHom.id 𝔽₂ A :=
    e.comp_symm
  rw [specialIsogeny_specialIsogeny]
  apply Subtype.ext
  rw [coe_frobenius, pow_one, coe_pointsMap]
  rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
    ← AlgHom.comp_toRingHom, hcomp]
  simp

/-- The exceptional endomorphism is bijective on points over a perfect coefficient algebra
over `𝔽₂`, although its group-scheme kernel need not be trivial. -/
theorem specialIsogeny_bijective (A : Type u) [CommRing A] [Algebra 𝔽₂ A] [PerfectRing A 2] :
    Function.Bijective (specialIsogeny A) := by
  let _ : IsReduced A := (isReduced_iff_pow_one_lt 2 one_lt_two).2 fun x hx =>
    (PerfectRing.bijective_frobenius (R := A) (p := 2)).1 (by simpa using hx)
  exact ⟨specialIsogeny_injective A, specialIsogeny_surjective A⟩

end

end TauCeti.F4ShortRoot.PrimeField
