/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic
public import TauCeti.Algebra.Lie.Derivation.OuterCenter
public import TauCeti.RingTheory.Derivation.TrivSqZeroExt

/-!
# Central characters of derivation self-extensions

For an associative `R`-algebra `A`, a derivation `δ` and a central character `χ`, the central
character deforms to the dual-number character `z ↦ χ(z) + ε χ(δ(z))`. On a module with strict
character `χ`, the center acts on `E_δ(M)` by the matrix with diagonal entries `χ(z)` and upper
right entry `χ(δ(z))`. Consequently this extension stays in the strict character fiber exactly
when all the infinitesimal scalar actions vanish. For a faithful scalar action this is
equivalent to the deformed character being constant.

The character uses `derivationLieAlgebra.restrictCenter` and the existing
`derivationToTrivSqZeroExtEquivLift` dictionary. No commutativity of `A` or continuity of its
derivation is needed for this algebraic calculation. For continuous derivations on topological
algebras, `DerivationExtension.discreteShortComplex` supplies the corresponding extension in
the category of discrete modules. The character deformation depends only on the continuous
outer class, through `ContinuousOuterDerivation.restrictCenter`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), for infinitesimal motion
  of central characters of modules at the critical level.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

namespace derivationLieAlgebra

/-- The first-order motion of a central character in the direction of a derivation. -/
noncomputable def characterDeformation (δ : derivationLieAlgebra R A)
    (χ : Subalgebra.center R A →ₐ[R] R) : Subalgebra.center R A →ₐ[R] DualNumber R := by
  letI := χ.toRingHom.toAlgebra
  exact (derivationToTrivSqZeroExtEquivLift R (Subalgebra.center R A) R
    ((Algebra.linearMap (Subalgebra.center R A) R).compDer (restrictCenter R A δ))).val

/-- The classical component is the original character. -/
@[simp]
theorem fst_characterDeformation (δ : derivationLieAlgebra R A)
    (χ : Subalgebra.center R A →ₐ[R] R) (z : Subalgebra.center R A) :
    TrivSqZeroExt.fst (characterDeformation δ χ z) = χ z := by
  simp only [characterDeformation, derivationToTrivSqZeroExtEquivLift_apply_fst]
  simp [RingHom.algebraMap_toAlgebra]

/-- The infinitesimal component is evaluation of the restricted derivation. -/
@[simp]
theorem snd_characterDeformation (δ : derivationLieAlgebra R A)
    (χ : Subalgebra.center R A →ₐ[R] R) (z : Subalgebra.center R A) :
    TrivSqZeroExt.snd (characterDeformation δ χ z) = χ (restrictCenter R A δ z) := by
  simp only [characterDeformation, derivationToTrivSqZeroExtEquivLift_apply_snd]
  simp [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]

/-- The deformed character is constant precisely when its infinitesimal component vanishes. -/
theorem characterDeformation_eq_inl_comp_iff (δ : derivationLieAlgebra R A)
    (χ : Subalgebra.center R A →ₐ[R] R) :
    characterDeformation δ χ = (TrivSqZeroExt.inlAlgHom R R R).comp χ ↔
      ∀ z, χ (restrictCenter R A δ z) = 0 := by
  constructor
  · intro h z
    have := congrArg (fun f : Subalgebra.center R A →ₐ[R] DualNumber R =>
      TrivSqZeroExt.snd (f z)) h
    simpa using this
  · intro h
    ext z <;> simp [h]

/-- The zero derivation gives the constant lift of the character. -/
@[simp]
theorem characterDeformation_zero (χ : Subalgebra.center R A →ₐ[R] R) :
    characterDeformation (0 : derivationLieAlgebra R A) χ =
      (TrivSqZeroExt.inlAlgHom R R R).comp χ := by
  rw [characterDeformation_eq_inl_comp_iff]
  simp

/-- Inner changes of representative do not change the infinitesimal central character. -/
@[simp]
theorem characterDeformation_add_innerDerivation (δ : derivationLieAlgebra R A)
    (χ : Subalgebra.center R A →ₐ[R] R) (b : A) :
    characterDeformation (δ + innerDerivation R b) χ = characterDeformation δ χ := by
  ext z <;> simp

end derivationLieAlgebra

namespace continuousDerivationLieAlgebra

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [SeparatelyContinuousMul A]
  [ContinuousConstSMul R A]

/-- The infinitesimal motion of a central character depends only on the continuous outer
class, through its canonical action on the center. -/
theorem characterDeformation_eq_of_mkQ_eq (D E : continuousDerivationLieAlgebra R A)
    (h : (LieIdeal.mkQ _ D : ContinuousOuterDerivation R A) = LieIdeal.mkQ _ E)
    (χ : Subalgebra.center R A →ₐ[R] R) :
    derivationLieAlgebra.characterDeformation (D : derivationLieAlgebra R A) χ =
      derivationLieAlgebra.characterDeformation (E : derivationLieAlgebra R A) χ := by
  have hcenter := congrArg (ContinuousOuterDerivation.restrictCenter R A) h
  simp only [ContinuousOuterDerivation.restrictCenter_mkQ] at hcenter
  ext z <;> simp [hcenter]

end continuousDerivationLieAlgebra

namespace DerivationExtension

open derivationLieAlgebra

variable (δ : derivationLieAlgebra R A) (χ : Subalgebra.center R A →ₐ[R] R)
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
    (hχ : ∀ (z : Subalgebra.center R A) (v : M), (z : A) • v = χ z • v)

include hχ

/-- The action of the center on the self-extension has diagonal character `χ` and off-diagonal
character `χ ∘ δ`. The two coefficients are the components of the deformed character. -/
theorem center_smul (z : Subalgebra.center R A) (x : DerivationExtension δ M) :
    (z : A) • x =
      ⟨TrivSqZeroExt.fst (characterDeformation δ χ z) • x.fst +
        TrivSqZeroExt.snd (characterDeformation δ χ z) • x.snd,
        TrivSqZeroExt.fst (characterDeformation δ χ z) • x.snd⟩ := by
  ext
  · simpa only [fst_smul, fst_characterDeformation, snd_characterDeformation,
      ← coe_restrictCenter_apply] using
      congrArg₂ (· + ·) (hχ z x.fst) (hχ (restrictCenter R A δ z) x.snd)
  · simpa only [snd_smul, fst_characterDeformation] using hχ z x.snd

/-- The extension has the original strict character exactly when every infinitesimal
coefficient annihilates the module. This includes the zero module. -/
theorem center_smul_eq_iff :
    (∀ (z : Subalgebra.center R A) (x : DerivationExtension δ M),
      (z : A) • x = ⟨χ z • x.fst, χ z • x.snd⟩) ↔
      ∀ (z : Subalgebra.center R A) (v : M), χ (restrictCenter R A δ z) • v = 0 := by
  constructor
  · intro h z v
    have hx := congrArg fst (h z ⟨0, v⟩)
    rw [center_smul δ χ hχ] at hx
    simpa using hx
  · intro h z x
    rw [center_smul δ χ hχ]
    simp [h]

/-- With faithful scalar action, staying in the strict character fiber is equivalent to the
dual-number character being the constant lift of `χ`. -/
theorem center_smul_eq_iff_characterDeformation_eq [FaithfulSMul R M] :
    (∀ (z : Subalgebra.center R A) (x : DerivationExtension δ M),
      (z : A) • x = ⟨χ z • x.fst, χ z • x.snd⟩) ↔
      characterDeformation δ χ = (TrivSqZeroExt.inlAlgHom R R R).comp χ := by
  rw [center_smul_eq_iff δ χ hχ, characterDeformation_eq_inl_comp_iff]
  exact forall_congr' fun z =>
    ⟨fun h => eq_of_smul_eq_smul (α := M) fun v => by simpa only [zero_smul] using h v,
      fun h v => by simp [h]⟩

end DerivationExtension

end TauCeti
