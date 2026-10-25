/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Blowup.Submodule

/-!
# Examples: the blowup of a submodule

For `C = B = ℤ` and `F = {2}`, the graded ring `R(J)` contains `2 T` but not `T`: its degree one
coefficients are even, so `R(J)` is not all of `ℤ[T]`. For `F = {0, 1}`, which generates the unit
ideal, the morphism `Spec ℤ ⟶ Proj R(J)` pulls `D₊(0 T)` back to the empty set and `D₊(1 T)`
back to all of `Spec ℤ`.

The affine charts `Spec C[F/S] ≅ D₊(t T^{#S})` are tested through the chart-to-base map
`Spec C[F/S] ⟶ Proj R(J) ⟶ Spec C`, which is the spectrum of `C → C[F/S]`. For `C = B` and
`F = S = {1}` it is an isomorphism. For `F = S = {x}` with `x` nilpotent in a nonzero ring, the
chart is empty, so the chart-to-base map is not surjective.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, (1.1) and (1.2)(i),(ii).
-/

open CategoryTheory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry submoduleBlowup

-- For `F = {2}` the degree one piece of `R(J)` contains `2 T`.
example : ((monomialDegreeOne ℤ (Set.mem_singleton (2 : ℤ)) :
    coeffSubalgebra fun n ↦ Submodule.span ℤ {(2 : ℤ)} ^ n) : Polynomial ℤ) =
      Polynomial.monomial 1 2 :=
  coe_monomialDegreeOne ℤ _

-- For `F = {2}` the variable `T` itself does not lie in `R(J)`.
example : Polynomial.monomial 1 (1 : ℤ) ∉
    coeffSubalgebra fun n ↦ Submodule.span ℤ {(2 : ℤ)} ^ n := by
  rw [monomial_mem_coeffSubalgebra_iff, pow_one, Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  rw [smul_eq_mul] at ha
  omega

-- For `F = {0, 1}` the standard open `D₊(0 T)` pulls back to the empty set.
example : fromSpec ℤ (F := {0, 1})
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem 0 rfl)) isUnit_one) ⁻¹ᵁ
    Proj.basicOpen (gradedRing ℤ {0, 1}) (monomialDegreeOne ℤ (Set.mem_insert (0 : ℤ) {1})) =
      ⊥ :=
  (fromSpec_preimage_basicOpen ℤ _ _).trans PrimeSpectrum.basicOpen_zero

-- For `F = {0, 1}` the standard open `D₊(1 T)` pulls back to all of `Spec ℤ`.
example : fromSpec ℤ (F := {0, 1})
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem 0 rfl)) isUnit_one) ⁻¹ᵁ
    Proj.basicOpen (gradedRing ℤ {0, 1}) (monomialDegreeOne ℤ (Set.mem_insert_of_mem (0 : ℤ) rfl)) =
      ⊤ :=
  (fromSpec_preimage_basicOpen ℤ _ _).trans PrimeSpectrum.basicOpen_one

-- For `C = B` and `F = S = {1}`, the chart is an isomorphism onto `Spec C`.
example (R : Type) [CommRing R] :
    IsIso ((basicOpenIsoSpec R (Localization.Away (∏ g ∈ ({1} : Finset R), g))
        (F := {(1 : R)}) (Finset.coe_singleton (1 : R)).le (Finset.singleton_nonempty 1)).inv ≫
      (Proj.basicOpen _ _).ι ≫ toSpec R {(1 : R)}) := by
  rw [basicOpenIsoSpec_inv_comp]
  set L := Localization.Away (∏ g ∈ ({1} : Finset R), g)
  have hbij : Function.Bijective
      (algebraMap R (fractionSubalgebra R ({1} : Set R) {1} L)) := by
    refine ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists
        (Submonoid.powers (∏ g ∈ ({1} : Finset R), g)) L).mp (congr_arg Subtype.val h)
      simpa using hc
    · obtain ⟨n, y, -, hy⟩ := (mem_fractionSubalgebra_iff (Finset.coe_singleton (1 : R)).le).mp z.2
      exact ⟨y, Subtype.ext (by simpa using hy.symm)⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (fractionSubalgebra R ({1} : Set R) {1} L))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

-- For `F = S = {x}` with `x` nilpotent in a nonzero ring, the chart `D₊(x T)` is empty, so the
-- chart-to-base map is not surjective.
example (R : Type) [CommRing R] [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    IsEmpty (Proj.basicOpen (gradedRing R {x}) (monomialProd R (Finset.coe_singleton x).le)) ∧
      ¬ Function.Surjective ((basicOpenIsoSpec R (Localization.Away (∏ g ∈ ({x} : Finset R), g))
        (Finset.coe_singleton x).le (Finset.singleton_nonempty x)).inv ≫
          (Proj.basicOpen _ _).ι ≫ toSpec R {x}) := by
  set L := Localization.Away (∏ g ∈ ({x} : Finset R), g)
  obtain ⟨n, hn⟩ := hx
  have : Subsingleton L := IsLocalization.subsingleton (M := Submonoid.powers (∏ g ∈ {x}, g))
    ⟨n, by simpa using hn⟩
  -- The chart ring `C[F/S]` is a subring of the zero ring `L`, so its spectrum is empty.
  have : IsEmpty (Spec (.of (fractionSubalgebra R ({x} : Set R) {x} L))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  refine ⟨Function.isEmpty
    (basicOpenIsoSpec R L (Finset.coe_singleton x).le (Finset.singleton_nonempty x)).hom.base,
    fun h ↦ ?_⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
  obtain ⟨y, -⟩ := h p
  exact isEmptyElim y
