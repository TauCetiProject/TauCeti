/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.Nakayama
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Auslander–Reiten translate as a kernel

For an arrow `f : P₁ → P₀`, dualizing the quotient defining its transpose gives the exact
sequence `0 → D Tr(f) → ν(P₁) → ν(P₀)`, where `ν(P) = D Hom_A(P, A)` is the Nakayama module.
`LinearMap.auslanderReitenTranslateEquivKerNakayama` identifies the translate with this kernel,
with forward and inverse evaluation formulas.

When the arrow belongs to a finite projective presentation over an algebra over a field,
both Nakayama modules are injective. Thus this sequence gives an injective copresentation of
the translate, used to compute morphisms into it and to establish Auslander–Reiten duality.
No minimality, exactness, or projectivity is needed for the kernel identification itself.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.

The exactness proof uses Mathlib's
`LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective` and
`LinearMap.ker_dualMap_eq_dualAnnihilator_range`, applied to the transpose quotient.
-/

public section

namespace LinearMap

open TauCeti

universe u v w z

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]
  {P₀ : Type w} {P₁ : Type z} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]

/-- The canonical embedding of `D Tr(f)` into `ν(P₁)`, obtained by dualizing the
quotient onto the transpose. -/
def auslanderReitenTranslateToNakayama (f : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranslate k f →ₗ[A] NakayamaModule k A P₁ where
  toFun φ := (NakayamaModule.equivDual k A P₁).symm
    (((AuslanderReitenTranspose.mk f).restrictScalars k).dualMap φ)
  map_add' := fun _ _ ↦ by ext; simp
  map_smul' := fun _ _ ↦ by
    ext
    simp [AuslanderReitenTranslate.smul_apply, NakayamaModule.smul_apply]

/-- The embedding evaluates a translate functional on the class of the inner functional. -/
@[simp]
theorem auslanderReitenTranslateToNakayama_apply (f : P₁ →ₗ[A] P₀)
    (φ : AuslanderReitenTranslate k f) (ψ : Module.Dual A P₁) :
    NakayamaModule.equivDual k A P₁ (auslanderReitenTranslateToNakayama f φ) ψ =
      φ (AuslanderReitenTranspose.mk f ψ) := by
  simp [auslanderReitenTranslateToNakayama]

/-- Dualizing the transpose quotient is injective. -/
theorem auslanderReitenTranslateToNakayama_injective (f : P₁ →ₗ[A] P₀) :
    Function.Injective (auslanderReitenTranslateToNakayama (k := k) f) := by
  intro φ χ h
  apply LinearMap.dualMap_injective_of_surjective
    (f := (AuslanderReitenTranspose.mk f).restrictScalars k)
    (AuslanderReitenTranspose.mk_surjective f)
  ext ψ
  simpa only [auslanderReitenTranslateToNakayama_apply, LinearMap.dualMap_apply,
    LinearMap.coe_restrictScalars] using
    congrArg (fun χ ↦ NakayamaModule.equivDual k A P₁ χ ψ) h

/-- The image of the translate in `ν(P₁)` is exactly the kernel of `ν(f)`. -/
theorem exact_auslanderReitenTranslateToNakayama_nakayamaMap (f : P₁ →ₗ[A] P₀) :
    Function.Exact (auslanderReitenTranslateToNakayama (k := k) f) f.nakayamaMap := by
  let q := (AuslanderReitenTranspose.mk f).restrictScalars k
  let d := (f.lcomp Aᵐᵒᵖ A).restrictScalars k
  have hqd : LinearMap.ker q = LinearMap.range d := by
    simp [q, d, LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
  have hd : LinearMap.range q.dualMap = LinearMap.ker d.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective q
      (AuslanderReitenTranspose.mk_surjective f), hqd,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  intro φ
  constructor
  · intro hφ
    have hker : NakayamaModule.equivDual k A P₁ φ ∈ LinearMap.ker d.dualMap := by
      apply LinearMap.mem_ker.mpr
      ext ψ
      simpa [d, LinearMap.lcomp_apply'] using
        congrArg (fun χ ↦ NakayamaModule.equivDual k A P₀ χ ψ) hφ
    obtain ⟨χ, hχ⟩ := hd ▸ hker
    refine ⟨χ, (NakayamaModule.equivDual k A P₁).injective (LinearMap.ext fun ψ ↦ ?_)⟩
    simpa [q] using LinearMap.congr_fun hχ ψ
  · rintro ⟨χ, rfl⟩
    ext ψ
    simp only [LinearMap.nakayamaMap_apply, auslanderReitenTranslateToNakayama_apply, map_zero,
      LinearMap.zero_apply]
    simpa only [LinearMap.lcomp_apply', map_zero] using
      congrArg χ (AuslanderReitenTranspose.mk_lcomp f ψ)

/-- The canonical algebra-linear identification of `D Tr(f)` with the kernel of `ν(f)`. -/
noncomputable def auslanderReitenTranslateEquivKerNakayama (f : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranslate k f ≃ₗ[A] LinearMap.ker (f.nakayamaMap (k := k)) :=
  LinearEquiv.ofBijective
    ((auslanderReitenTranslateToNakayama f).codRestrict (LinearMap.ker f.nakayamaMap) fun φ ↦
      LinearMap.mem_ker.mpr
        ((exact_auslanderReitenTranslateToNakayama_nakayamaMap f).apply_apply_eq_zero φ))
    ⟨fun _ _ h ↦ auslanderReitenTranslateToNakayama_injective f (congrArg Subtype.val h), fun φ ↦ by
      obtain ⟨χ, hχ⟩ :=
        (exact_auslanderReitenTranslateToNakayama_nakayamaMap f φ.val).mp
          (LinearMap.mem_ker.mp φ.property)
      exact ⟨χ, Subtype.ext hχ⟩⟩

/-- Forward kernel transport evaluates on transpose classes. -/
@[simp]
theorem auslanderReitenTranslateEquivKerNakayama_apply (f : P₁ →ₗ[A] P₀)
    (φ : AuslanderReitenTranslate k f) (ψ : Module.Dual A P₁) :
    NakayamaModule.equivDual k A P₁ (auslanderReitenTranslateEquivKerNakayama f φ).val ψ =
      φ (AuslanderReitenTranspose.mk f ψ) :=
  auslanderReitenTranslateToNakayama_apply f φ ψ

/-- Inverse kernel transport descends a Nakayama functional to the transpose quotient. -/
@[simp]
theorem auslanderReitenTranslateEquivKerNakayama_symm_apply_mk (f : P₁ →ₗ[A] P₀)
    (φ : LinearMap.ker (f.nakayamaMap (k := k))) (ψ : Module.Dual A P₁) :
    (auslanderReitenTranslateEquivKerNakayama f).symm φ (AuslanderReitenTranspose.mk f ψ) =
      NakayamaModule.equivDual k A P₁ φ.val ψ := by
  simpa only [auslanderReitenTranslateEquivKerNakayama_apply] using
    congrArg (fun χ ↦ NakayamaModule.equivDual k A P₁ χ.val ψ)
      ((auslanderReitenTranslateEquivKerNakayama f).apply_symm_apply φ)

end LinearMap
