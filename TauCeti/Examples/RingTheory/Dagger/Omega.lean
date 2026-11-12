/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Quotient
public import TauCeti.RingTheory.Dagger.Omega.Kaehler
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Unramified.Field

/-!
# Differentials of a doubled dagger origin

The quotient presentation retains the relation `d(X²) = 2X dX`, not `dX = 0`.
In characteristic two the relation vanishes entirely: the differentials of the doubled origin
are the base change of the free differential module of the disc. The same finiteness instance
also applies to the zero algebra.

For finite algebras the comparison with algebraic Kähler differentials is an isomorphism.
The tests below include scalar compatibility, finite separable extensions, the zero algebra,
and dual numbers with a nonzero differential of their nilpotent coordinate.
-/

public section

open TensorProduct
open TauCeti.Dagger

namespace TauCeti.Examples

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra (Fin 1) K
local notation "x" => washnitzerAlgebra.X (Fin 1) K 0
local notation "I" => Ideal.span ({x ^ 2} : Set W)
local notation "B" => W ⧸ I

-- Finiteness includes a nonreduced quotient and the zero algebra.
example : Module.Finite B (Omega K B) := inferInstance

example : Module.Finite (W ⧸ (⊤ : Ideal W)) (Omega K (W ⧸ (⊤ : Ideal W))) := inferInstance

-- The tensor relation remembers the multiplicity two.
example : (1 : B) ⊗ₜ[W] ((2 : W) • (x • Omega.d K W x)) ∈
    Omega.quotientRelations K W I := by
  rw [Omega.quotientRelations_eq_span K W I {x ^ 2} rfl]
  have hd : Omega.d K W (x ^ 2) = (2 : W) • (x • Omega.d K W x) := by
    rw [pow_two, (Omega.d K W).leibniz, two_smul W]
  exact hd ▸ Submodule.subset_span ⟨x ^ 2, Set.mem_singleton _, rfl⟩

-- Both directions of the presentation preserve exact differentials.
example (a : W) :
    Omega.quotientEquiv K W I (Submodule.Quotient.mk (1 ⊗ₜ[W] Omega.d K W a)) =
      Omega.d K B (Ideal.Quotient.mk I a) := by simp

example (a : W) :
    (Omega.quotientEquiv K W I).symm (Omega.d K B (Ideal.Quotient.mk I a)) =
      Submodule.Quotient.mk ((1 : B) ⊗ₜ[W] Omega.d K W a) := by simp

/-- In characteristic two, quotienting the dagger disc by `X²` imposes no differential relation. -/
theorem injective_quotientMap_doubledOrigin_of_charTwo [CharP K 2] :
    Function.Injective (Omega.quotientMap K W I) := by
  rw [← LinearMap.ker_eq_bot, Omega.ker_quotientMap,
    Omega.quotientRelations_eq_span K W I {x ^ 2} rfl]
  have hK : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have htwo : (2 : W) = 0 := by
    calc
      (2 : W) = algebraMap K W (2 : K) := (map_ofNat (algebraMap K W) 2).symm
      _ = 0 := (congrArg (algebraMap K W) hK).trans (map_zero _)
  have hd : Omega.d K W (x ^ 2) = 0 := by
    simp [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul W, htwo]
  simp [hd]

end TauCeti.Examples

section KaehlerComparison

open TauCeti.Dagger
open scoped DualNumber

-- No norm, completeness, separability or reducedness is required for the comparison.
example (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    Function.Bijective (Omega.ofKaehler R A) :=
  ⟨Omega.ofKaehler_injective R A, Omega.ofKaehler_surjective R A⟩

example (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (a b : A) :
    (Omega.ofKaehlerEquiv R A).symm (a • Omega.d R A b) =
      a • KaehlerDifferential.D R A b := by simp

example (R : Type*) [CommRing R] : Subsingleton (Omega R R) := inferInstance

-- Separable extensions have no differentials; no such assertion is made for inseparable ones.
example (K L : Type*) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L] :
    Subsingleton (Omega K L) := by
  have := Algebra.FormallyUnramified.of_isSeparable K L
  infer_instance

-- The comparison also includes the zero algebra, not just nonzero field extensions.
example (R : Type*) [CommRing R] :
    Function.Bijective (Omega.ofKaehler R (R ⧸ (⊤ : Ideal R))) :=
  ⟨Omega.ofKaehler_injective R _, Omega.ofKaehler_surjective R _⟩

-- The differential of a nilpotent is not generally zero, in any characteristic.
example (R : Type*) [CommRing R] [Nontrivial R] :
    Omega.d R R[ε] ε ≠ 0 := by
  -- R[ε] is TrivSqZeroExt R R, whose underlying R-module is R × R.
  -- inferInstanceAs exposes the product so instance search can use its finiteness instance.
  have : Module.Finite R R[ε] := inferInstanceAs (Module.Finite R (R × R))
  let D : Derivation R R[ε] R[ε] :=
    { toLinearMap := (TrivSqZeroExt.inrHom R R).comp (TrivSqZeroExt.sndHom R R)
      map_one_eq_zero' := by simp
      leibniz' a b := by
        ext <;> simp [smul_eq_mul, TrivSqZeroExt.snd_mul, mul_comm] }
  have hD_eps : D.liftKaehlerDifferential (KaehlerDifferential.D R R[ε] ε) = ε := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
    -- D applies inr to the second coordinate, and ε is definitionally inr 1.
    rfl
  intro h
  have hD := congrArg D.liftKaehlerDifferential ((Omega.d_eq_zero_iff R R[ε] ε).mp h)
  have heps : (ε : R[ε]) ≠ 0 := by
    intro hzero
    have := congrArg TrivSqZeroExt.snd hzero
    simp at this
  apply heps
  simpa only [hD_eps, map_zero] using hD

end KaehlerComparison
