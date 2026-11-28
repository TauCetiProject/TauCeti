/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalReduction

/-!
# Residue matrices of integral adelic unitary points

In the integral coordinates of the finite adelic unitary group, reduction at a finite place
is a group homomorphism to a general linear group. Principal level at any ideal divisible by
the prime of that place reduces to the identity there.
-/

public section

open IsDedekindDomain Matrix NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.integralAdelicUnitaryGroup

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise reduction at `w` of a unitary matrix in integral finite adelic coordinates. -/
noncomputable def residue (w : HeightOneSpectrum (𝓞 E)) :
    integralAdelicUnitaryGroup E ι →*
      GL ι (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  (GeneralLinearGroup.map w.integralAdelesResidue).comp
    ((unitarySubgroup _).subtype.comp (integralAdelicUnitaryGroupEquiv E ι).symm.toMonoidHom)

/-- An integral matrix representing `g` computes its reduction by reducing its entries. -/
theorem residue_eq_map_of_integralGL (w : HeightOneSpectrum (𝓞 E))
    {g : integralAdelicUnitaryGroup E ι} {h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)}
    (hh : FiniteAdeleRing.integralGL E ι h = ((g : finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E])) :
    residue w g = GeneralLinearGroup.map w.integralAdelesResidue h := by
  let h' := (integralAdelicUnitaryGroupEquiv E ι).symm g
  have hval : (h' : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) = h := by
    apply FiniteAdeleRing.integralGL_injective E ι
    rw [← coe_integralAdelicUnitaryGroupEquiv, MulEquiv.apply_symm_apply, ← hh]
  exact congrArg (GeneralLinearGroup.map w.integralAdelesResidue) hval

/-- A principal-level point reduces to the identity at each place dividing the level ideal. -/
theorem residue_eq_one_of_mem_principalUnitaryLevel (w : HeightOneSpectrum (𝓞 E))
    {N : Ideal (𝓞 E)} (hN : N ≤ w.asIdeal) {g : integralAdelicUnitaryGroup E ι}
    (hg : (g : finiteAdelicUnitaryGroup E ι) ∈ principalUnitaryLevel E ι N) : residue w g = 1 := by
  obtain ⟨h, hh, hcong⟩ := mem_principalUnitaryLevel_iff.mp hg
  rw [residue_eq_map_of_integralGL w hh]
  apply GeneralLinearGroup.ext
  intro i j
  have hz := w.integralAdelesResidue_eq_zero_of_mem_completedIdeal hN (hcong i j)
  simpa [GeneralLinearGroup.map_apply, Matrix.one_apply, sub_eq_zero] using hz

end TauCeti.integralAdelicUnitaryGroup
