/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Basic
public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.Derivation.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.TensorProduct.Finite

import TauCeti.RingTheory.Derivation.Ideal

/-!
# Presentations of universally finite differentials

For a quotient `B = A ⧸ I`, the universally finite differentials of `B` are the quotient of
`B ⊗[A] Omega R A` by the relations `1 ⊗ d f`, for `f ∈ I`, provided `A` is noetherian and
`Omega R A` is finite. In particular, the differentials of every dagger algebra are finite.
This gives presentations by the partial derivatives of the defining equations, without imposing
smoothness, reducedness or a characteristic-zero hypothesis.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §4.1.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
-/

public section

namespace TauCeti.Dagger.Omega

open TensorProduct

-- Restriction of scalars is local: globally registering it would make scalar-ring search loop.
private noncomputable local instance (priority := low) {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R B] [Algebra A B] : Module A (Omega R B) :=
  Module.restrictScalars A B _

private local instance (priority := low) {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] [Algebra A B] : IsScalarTower A B (Omega R B) :=
  IsScalarTower.restrictScalars A B _

private local instance (priority := low) {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    IsScalarTower R A (Omega R B) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    calc
      algebraMap R A r • x = algebraMap A B (algebraMap R A r) • x := rfl
      _ = algebraMap R B r • x := by rw [IsScalarTower.algebraMap_apply R A B]
      _ = r • x := algebraMap_smul B r x

section Finite

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Finiteness of universally finite differentials descends along a surjective algebra map. -/
theorem finite_of_surjective [Module.Finite A (Omega R A)]
    (h : Function.Surjective (algebraMap A B)) : Module.Finite B (Omega R B) := by
  let f := (ofKaehler R B).restrictScalars A ∘ₗ KaehlerDifferential.map R R A B
  have hf : Function.Surjective f := (ofKaehler_surjective R B).comp
    (KaehlerDifferential.map_surjective_of_surjective R R A B h)
  have hker : LinearMap.ker (ofKaehler R A) ≤ LinearMap.ker f := by
    intro x hx
    apply ofKaehler_eq_zero_iff.mpr
    intro N hN
    -- A finite quotient over `B` stays finite over the surjecting ring `A`.
    have : Module.Finite A B := (RingHom.finite_algebraMap).mp (.of_surjective _ h)
    have : Module.Finite A (Ω[B⁄R] ⧸ N) := Module.Finite.trans B _
    let g := (N.mkQ.restrictScalars A).comp (KaehlerDifferential.map R R A B)
    have hg : Function.Surjective g := N.mkQ_surjective.comp
      (KaehlerDifferential.map_surjective_of_surjective R R A B h)
    have : Module.Finite A (Ω[A⁄R] ⧸ LinearMap.ker g) :=
      Module.Finite.equiv (g.quotKerEquivOfSurjective hg).symm
    exact (Submodule.Quotient.mk_eq_zero N).mp <|
      LinearMap.mem_ker.mp <|
        (ofKaehler_eq_zero_iff.mp (LinearMap.mem_ker.mp hx)) (LinearMap.ker g) this
  let g := (ofKaehler R A).liftOfSurjective (ofKaehler_surjective R A) ⟨f, hker⟩
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨ofKaehler R A x, by simp only [g, LinearMap.equivOfSurjective_apply]⟩
  have : Module.Finite A (Omega R B) := Module.Finite.of_surjective g hg
  exact Module.Finite.of_restrictScalars_finite A B _

end Finite

section Quotient

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing A] [Module.Finite A (Omega R A)] (I : Ideal A)

local notation "B" => A ⧸ I
local notation "T" => B ⊗[A] Omega R A

instance : Module.Finite B (Omega R B) :=
  finite_of_surjective (R := R) (Ideal.Quotient.mk_surjective (I := I))

/-- The relations on differentials imposed by the quotient: the span of `1 ⊗ d f`, `f ∈ I`. -/
noncomputable def quotientRelations : Submodule B T :=
  Submodule.span B (Set.range fun f : I ↦ (1 : B) ⊗ₜ[A] d R A f)

omit [IsNoetherianRing A] [Module.Finite A (Omega R A)] in
/-- Relations need only be imposed on a set of generators of the defining ideal. -/
theorem quotientRelations_eq_span (S : Set A) (hS : Ideal.span S = I) :
    quotientRelations R A I = Submodule.span B ((fun f ↦ (1 : B) ⊗ₜ[A] d R A f) '' S) := by
  let N := Submodule.span B ((fun f ↦ (1 : B) ⊗ₜ[A] d R A f) '' S)
  let D := (N.mkQ.restrictScalars A).compDer
    ((TensorProduct.mk A B (Omega R A) 1).compDer (d R A))
  apply le_antisymm
  · rw [quotientRelations, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero N).mp
    exact D.apply_eq_zero_of_mem_span (S := S) (fun a ha m ↦ by
      have haI : a ∈ I := hS ▸ Ideal.subset_span ha
      rw [← algebraMap_smul B a m, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr haI, zero_smul])
      (fun a ha ↦ (Submodule.Quotient.mk_eq_zero N).mpr
        (Submodule.subset_span ⟨a, ha, rfl⟩)) (hS.symm ▸ f.property)
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨⟨f, hS ▸ Ideal.subset_span hf⟩, rfl⟩

/-- Base change of differentials along the quotient map, sending `b ⊗ d a` to `b • d [a]`. -/
noncomputable def quotientMap : T →ₗ[B] Omega R B := by
  letI : Module.Finite A (Omega R B) := Module.Finite.trans B _
  exact (lift ((d R B).compAlgebraMap A)).liftBaseChange B

/-- The quotient map on exact differentials. -/
@[simp]
theorem quotientMap_tmul_d (b : B) (a : A) :
    quotientMap R A I (b ⊗ₜ[A] d R A a) = b • d R B (Ideal.Quotient.mk I a) := by
  simp [quotientMap]

/-- Every differential on the quotient is a base-changed differential. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap R A I) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_d R B, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨1 ⊗ₜ[A] d R A a, by simp⟩

private theorem quotientRelations_le_ker :
    quotientRelations R A I ≤ LinearMap.ker (quotientMap R A I) := by
  rw [quotientRelations, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr f.property]

private noncomputable def quotientDerivation :
    Derivation R B (T ⧸ quotientRelations R A I) :=
  (((quotientRelations R A I).mkQ.restrictScalars A).compDer
    ((TensorProduct.mk A B (Omega R A) 1).compDer (d R A))).liftQuotient I <| by
      intro f hf
      simp only [Derivation.coe_comp]
      exact (Submodule.Quotient.mk_eq_zero _).mpr <|
        Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩

omit [IsNoetherianRing A] [Module.Finite A (Omega R A)] in
private theorem quotientDerivation_mk (a : A) :
    quotientDerivation R A I (Ideal.Quotient.mk I a) =
      (quotientRelations R A I).mkQ (1 ⊗ₜ[A] d R A a) := by
  rw [quotientDerivation, Derivation.liftQuotient_mk]
  rfl

/-- The relations `d f`, for `f ∈ I`, are exactly the kernel of base change to `A ⧸ I`. -/
theorem ker_quotientMap :
    LinearMap.ker (quotientMap R A I) = quotientRelations R A I := by
  refine le_antisymm ?_ (quotientRelations_le_ker R A I)
  have hid : (lift (quotientDerivation R A I)).comp (quotientMap R A I) =
      (quotientRelations R A I).mkQ := by
    apply (LinearMap.liftBaseChangeEquiv B).symm.injective
    apply hom_ext
    intro a
    simp [LinearMap.liftBaseChangeEquiv_symm_apply, quotientDerivation_mk]
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).mp
  simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero,
    Submodule.mkQ_apply] using (LinearMap.congr_fun hid x).symm

/-- The presentation formula for universally finite differentials:
`Ω¹_{(A/I)/R} ≃ ((A/I) ⊗[A] Ω¹_{A/R}) / ⟨1 ⊗ d f : f ∈ I⟩`. -/
noncomputable def quotientEquiv :
    (T ⧸ quotientRelations R A I) ≃ₗ[B] Omega R B :=
  (Submodule.quotEquivOfEq _ _ (ker_quotientMap R A I).symm) ≪≫ₗ
    (quotientMap R A I).quotKerEquivOfSurjective (quotientMap_surjective R A I)

/-- The presentation isomorphism is induced by the base-change map on every tensor. -/
@[simp]
theorem quotientEquiv_mk (x : T) :
    quotientEquiv R A I (Submodule.Quotient.mk x) = quotientMap R A I x := by
  simp [quotientEquiv]

/-- The inverse presentation isomorphism takes the differential of `[a]` to `[1 ⊗ d a]`. -/
@[simp]
theorem quotientEquiv_symm_d_mk (a : A) :
    (quotientEquiv R A I).symm (d R B (Ideal.Quotient.mk I a)) =
      Submodule.Quotient.mk (1 ⊗ₜ[A] d R A a) := by
  apply (quotientEquiv R A I).injective
  simp

end Quotient

end TauCeti.Dagger.Omega

namespace TauCeti.Dagger.IsDaggerAlgebra

variable (K A : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The universally finite differentials of every dagger algebra form a finite module. -/
instance (priority := low) finite_omega : Module.Finite A (Omega K A) := by
  let W := Dagger.washnitzerAlgebra (Fin (presentationDim K A)) K
  let : Algebra W A := (presentation K A).toRingHom.toAlgebra
  have : IsScalarTower K W A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((presentation K A).commutes r).symm
  exact Omega.finite_of_surjective (R := K) (presentation_surjective K A)

end TauCeti.Dagger.IsDaggerAlgebra
