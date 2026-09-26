/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
-- Proof-only: the general Kummer character, and `F` integrally closed in `F(W)`.
import TauCeti.FieldTheory.Kummer.Character
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus

/-!
# The Kummer character of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`, and `g` a nonzero function on
`W₁` whose `n`-th power is pulled back along `φ`. The translations by the points of `ker φ` fix
every pulled-back function, so each of them moves `g` by an `n`-th root of unity, and these roots
of unity are constants because `F` is integrally closed in `F(W₁)`. The resulting homomorphism
`S ↦ τ_S g / g` from `ker φ` to the `n`-th roots of unity of `F` is the Kummer character of `g`.

## Main definitions

* `TauCeti.Isogeny.kummerCharacter`: the character `S ↦ τ_S g / g` of `ker φ`.

## Main results

* `TauCeti.Isogeny.algebraMap_kummerCharacter`: its value at `S`, read in `F(W₁)`, is
  `τ_S g / g`.
* `TauCeti.Isogeny.kummerCharacter_mul`: it is multiplicative in `g`.
* `TauCeti.Isogeny.kummerCharacter_eq_one_iff`: it is trivial exactly when `g` is fixed by the
  translations by `ker φ`; in particular it is trivial on a pulled-back function
  (`TauCeti.Isogeny.kummerCharacter_eq_one_of_mem_fieldRange`).
* `TauCeti.Isogeny.kummerCharacter_eq_of_principal_eq`: it depends on `g` only through its
  divisor, two functions with the same divisor differing by a constant.

In Silverman's construction (AEC III.8.1), for `T ∈ E[N]` one takes `g_T` with
`g_T^N = [N]^* f_T`, where `div f_T = N (T) - N (O)`, and sets `e_N(S, T) = τ_S g_T / g_T`. That is
this character, at `φ = [N]`, `n = N` and `g = g_T`, evaluated at `S`; its multiplicativity in `S`
is the bilinearity of the pairing in its first variable.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  (φ : Isogeny W₁ W₂) (n : ℕ) [NeZero n]

attribute [local instance] isIntegrallyClosedIn_functionField

-- The translations by the points of `ker φ`, as automorphisms of `F(W₁)`.
private noncomputable def kerTranslationHom :
    Multiplicative φ.ker →* (W₁.FunctionField ≃ₐ[F] W₁.FunctionField) :=
  (translationHom W₁).comp (AddMonoidHom.toMultiplicative φ.ker.subtype)

@[simp]
private theorem kerTranslationHom_apply (S : Multiplicative φ.ker) :
    kerTranslationHom φ S = translation W₁ (Multiplicative.toAdd S : φ.ker) := by
  simp [kerTranslationHom]

/-- **The Kummer character of an isogeny**: for a unit `g` of `F(W₁)` whose `n`-th power is pulled
back along `φ`, the homomorphism `S ↦ τ_S g / g` from `ker φ` to the `n`-th roots of unity of
`F`. -/
noncomputable def kummerCharacter (g : W₁.FunctionFieldˣ)
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange) :
    Multiplicative φ.ker →* rootsOfUnity n F :=
  -- The kernel translations fix every pulled-back function, in particular `gⁿ`.
  TauCeti.kummerCharacter (kerTranslationHom φ) n g fun S ↦ by
    rw [kerTranslationHom_apply]
    exact mem_ker_iff.mp (Multiplicative.toAdd S).2 _ hg

variable {φ n}

/-- **The value of the Kummer character**, read in `F(W₁)`: `τ_S g / g`. -/
@[simp]
theorem algebraMap_kummerCharacter {g : W₁.FunctionFieldˣ}
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange) (S : Multiplicative φ.ker) :
    algebraMap F W₁.FunctionField (φ.kummerCharacter n g hg S : Fˣ) =
      translation W₁ (Multiplicative.toAdd S : φ.ker) g / g := by
  rw [kummerCharacter, TauCeti.algebraMap_kummerCharacter, kerTranslationHom_apply]

/-- **The Kummer character is multiplicative in `g`.** -/
theorem kummerCharacter_mul {g h : W₁.FunctionFieldˣ}
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange)
    (hh : (h : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange)
    (hgh : ((g * h : W₁.FunctionFieldˣ) : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange) :
    φ.kummerCharacter n (g * h) hgh = φ.kummerCharacter n g hg * φ.kummerCharacter n h hh :=
  TauCeti.kummerCharacter_mul _ _ _

/-- **The Kummer character is trivial exactly when the kernel translations fix `g`.** -/
theorem kummerCharacter_eq_one_iff {g : W₁.FunctionFieldˣ}
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange) :
    φ.kummerCharacter n g hg = 1 ↔ (g : W₁.FunctionField) ∈ translationFixedField W₁ φ.ker := by
  rw [kummerCharacter, TauCeti.kummerCharacter_eq_one_iff, mem_translationFixedField_iff]
  simp only [kerTranslationHom_apply]
  exact ⟨fun h S hS ↦ h (Multiplicative.ofAdd ⟨S, hS⟩), fun h S ↦ h _ (Multiplicative.toAdd S).2⟩

/-- **The Kummer character of a pulled-back function is trivial**: the kernel translations fix
every pullback. -/
theorem kummerCharacter_eq_one_of_mem_fieldRange {g : W₁.FunctionFieldˣ}
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange)
    (hmem : (g : W₁.FunctionField) ∈ φ.fieldPullback.fieldRange) :
    φ.kummerCharacter n g hg = 1 :=
  (kummerCharacter_eq_one_iff hg).mpr
    ((mem_translationFixedField_iff _ _).mpr fun _ hS ↦ mem_ker_iff.mp hS _ hmem)

/-- **The Kummer character depends on `g` only through its divisor**: two functions with the same
divisor differ by a constant, which every translation fixes. -/
theorem kummerCharacter_eq_of_principal_eq {g g' : W₁.FunctionFieldˣ}
    (hg : (g : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange)
    (hg' : (g' : W₁.FunctionField) ^ n ∈ φ.fieldPullback.fieldRange)
    (h : Divisor.principal W₁.isFunctionField g = Divisor.principal W₁.isFunctionField g') :
    φ.kummerCharacter n g hg = φ.kummerCharacter n g' hg' := by
  obtain ⟨c, hc⟩ := Divisor.exists_units_algebraMap_mul_of_principal_eq _
    (isIntegrallyClosedIn_functionField W₁) h
  obtain rfl : g = Units.map (algebraMap F W₁.FunctionField : F →* W₁.FunctionField) c * g' :=
    Units.ext (by simpa using hc)
  exact TauCeti.kummerCharacter_algebraMap_mul c _ _

end TauCeti.Isogeny

end
