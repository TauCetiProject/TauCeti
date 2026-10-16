/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Projective
public import TauCeti.CategoryTheory.Exact.Biproduct

/-!
# The positive horseshoe step for complete resolutions

A map into a finitely generated projective module extends across a monomorphism whose cokernel
is Gorenstein-projective. Consequently, copresentations of the ends of a short exact sequence
can be combined into a copresentation of its middle term, with middle module the direct sum of
the prescribed copresenting modules. Only the left copresenting module must be finite
projective. The cokernel is an extension of the two prescribed cokernels.

This is the positive-degree step of the complete horseshoe construction. Unlike an injective
horseshoe, it does not require projective modules to be injective among all modules. Only the
original quotient is assumed Gorenstein-projective. Iteration of this step, together with the
projective horseshoe in negative degrees, constructs extensions of complete resolutions.
The results here do not yet assert that Gorenstein-projective modules are extension closed.

The prescribed horseshoe allows independent ring and module universes. The iteratable
specialization requires the ring to be small in the module universe, so categorical
projectivity implies module projectivity. Taking `A = Rᵐᵒᵖ` gives right modules. No noetherian
or self-injectivity hypothesis is needed.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.

The pushout and Noether argument is dual to
`ExactStructure.exists_conflation_biprod_of_conflation_of_projective`. It replaces ambient
injectivity by the splitting theorem `IsGorensteinProjective.nonempty_splitting_of_projective`.
-/

public section

open CategoryTheory Limits ZeroObject

universe v u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- **The positive horseshoe step.** Copresentations of the two ends of a short exact sequence
with Gorenstein-projective quotient combine to a copresentation of the middle term. The left
copresenting module is finite projective; no injectivity or projectivity is required of the
right copresenting module. The new cokernel is an extension of the prescribed cokernels, and
all four squares of the horseshoe commute. -/
theorem IsGorensteinProjective.exists_copresentation_horseshoe
    {S : ShortComplex (ModuleCat.{v} A)} (hN : IsGorensteinProjective A S.X₃)
    (hS : S.ShortExact) {PX KX PZ KZ : ModuleCat.{v} A}
    {iX : S.X₁ ⟶ PX} {pX : PX ⟶ KX} {hX : iX ≫ pX = 0}
    (hTX : (ShortComplex.mk iX pX hX).ShortExact)
    {iZ : S.X₃ ⟶ PZ} {pZ : PZ ⟶ KZ} {hZ : iZ ≫ pZ = 0}
    (hTZ : (ShortComplex.mk iZ pZ hZ).ShortExact)
    [Module.Finite A PX] [Module.Projective A PX] :
    ∃ (K : ModuleCat.{v} A) (i : S.X₂ ⟶ PX ⊞ PZ) (p : PX ⊞ PZ ⟶ K)
      (hip : i ≫ p = 0) (a : KX ⟶ K) (b : K ⟶ KZ) (hab : a ≫ b = 0),
      (ShortComplex.mk i p hip).ShortExact ∧ (ShortComplex.mk a b hab).ShortExact ∧
        S.f ≫ i = iX ≫ biprod.inl ∧ i ≫ biprod.snd = S.g ≫ iZ ∧
        biprod.inl ≫ p = pX ≫ a ∧ p ≫ b = biprod.snd ≫ pZ := by
  let E := ExactStructure.abelian (ModuleCat.{v} A)
  let TX := ShortComplex.mk iX pX hX
  -- The same pushout has a split row with quotient `S.X₃` and a row with cokernel `KX`.
  let sq := IsPushout.of_hasPushout iX S.f
  have hsplit := E.conflation_cobaseChange
    ((ExactStructure.abelian_conflation S).mpr hS) sq.flip
  have hmiddle := E.conflation_cobaseChange
    ((ExactStructure.abelian_conflation TX).mpr hTX) sq
  rw [cobaseChange_def] at hsplit
  have hsplit' := (ExactStructure.abelian_conflation _).mp hsplit
  obtain ⟨r, hr⟩ := IsGorensteinProjective.exists_extend
    (S := ShortComplex.mk (pushout.inl iX S.f) (cobaseChangeπ S sq.flip) (by simp))
    hN hsplit' PX (𝟙 PX)
  let sp := ShortComplex.Splitting.ofExactOfRetraction _ hsplit'.exact r hr hsplit'.epi_g
  have hinl : pushout.inl iX S.f ≫ sp.isoBinaryBiproduct.hom = biprod.inl := by
    apply biprod.hom_ext <;> simp [sp.f_r]
  have hsnd : sp.isoBinaryBiproduct.hom ≫ biprod.snd = cobaseChangeπ S sq.flip := by
    simp
  -- After splitting the pushout, insert the prescribed copresentation of the right end.
  have hz : biprod.map (𝟙 PX) iZ ≫ biprod.map (0 : PX ⟶ 0) pZ = 0 := by
    apply biprod.hom_ext' <;> simp [reassoc_of% hZ]
  have hbip : E.Conflation (ShortComplex.mk (biprod.map (𝟙 PX) iZ)
      (biprod.map (0 : PX ⟶ 0) pZ) hz) :=
    E.conflation_biprod (E.conflation_id_zero PX)
      ((ExactStructure.abelian_conflation _).mpr hTZ)
  have hzero : (sp.isoBinaryBiproduct.hom ≫ biprod.map (𝟙 PX) iZ) ≫
      biprod.map (0 : PX ⟶ 0) pZ = 0 := by
    rw [Category.assoc, hz, comp_zero]
  have hnext : E.Conflation (ShortComplex.mk
      (sp.isoBinaryBiproduct.hom ≫ biprod.map (𝟙 PX) iZ)
      (biprod.map (0 : PX ⟶ 0) pZ) hzero) := by
    refine E.conflation_of_iso ?_ hbip
    exact ShortComplex.isoMk sp.isoBinaryBiproduct.symm (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Iso.inv_hom_id_assoc, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
  rw [cobaseChange_def] at hmiddle
  -- Noether's conflations give the middle copresentation and the extension of cokernels.
  obtain ⟨K, p, a, b, hip, hab, hK, hC, hcomm, hright⟩ :=
    E.exists_conflation_comp hmiddle hnext
  let e : (0 : ModuleCat.{v} A) ⊞ KZ ≅ KZ := (isoZeroBiprod (isZero_zero _)).symm
  refine ⟨K, _, p, hip, a, b ≫ e.hom, by rw [← Category.assoc, hab, zero_comp],
    (ExactStructure.abelian_conflation _).mp hK, ?_, ?_, ?_, ?_, ?_⟩
  · apply (ExactStructure.abelian_conflation _).mp
    refine E.conflation_of_iso ?_ hC
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
  · rw [← Category.assoc, ← sq.w]
    simp only [Category.assoc]
    rw [reassoc_of% hinl]
    simp
  · simp only [Category.assoc, biprod.map_snd]
    rw [reassoc_of% hsnd, inl_cobaseChangeπ_assoc]
  · have h := pushout.inl iX S.f ≫= hcomm
    simp only [Category.assoc] at h
    rw [reassoc_of% hinl, reassoc_of% (inl_cobaseChangeπ TX sq)] at h
    simpa only [biprod.inl_map_assoc, Category.id_comp] using h
  · rw [← Category.assoc, hright]
    apply biprod.hom_ext' <;> simp [e]

/-- An extension of Gorenstein-projective modules embeds in a finite projective module, with
cokernel again an extension of Gorenstein-projective modules. The ring must be small in the
module universe. This is an iteratable positive horseshoe step, not yet a claim that the middle
term or its cokernel is Gorenstein-projective. -/
theorem IsGorensteinProjective.exists_projectiveCopresentation_of_shortExact
    [Small.{v} A] {S : ShortComplex (ModuleCat.{v} A)} (hL : IsGorensteinProjective A S.X₁)
    (hN : IsGorensteinProjective A S.X₃) (hS : S.ShortExact) :
    ∃ (T U : ShortComplex (ModuleCat.{v} A)), T.ShortExact ∧ Nonempty (T.X₁ ≅ S.X₂) ∧
      Module.Finite A T.X₂ ∧ Projective T.X₂ ∧ U.ShortExact ∧ Nonempty (U.X₂ ≅ T.X₃) ∧
      IsGorensteinProjective A U.X₁ ∧ IsGorensteinProjective A U.X₃ := by
  obtain ⟨TX, hTX, ⟨eX⟩, hPX, hprojX, hKX⟩ := hL.exists_projectiveCopresentation
  obtain ⟨TZ, hTZ, ⟨eZ⟩, hPZ, hprojZ, hKZ⟩ := hN.exists_projectiveCopresentation
  let iX := eX.inv ≫ TX.f
  let iZ := eZ.inv ≫ TZ.f
  have hX : iX ≫ TX.g = 0 := by simp [iX]
  have hZ : iZ ≫ TZ.g = 0 := by simp [iZ]
  have hTX' : (ShortComplex.mk iX TX.g hX).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk eX (Iso.refl _) (Iso.refl _) (by simp [iX]) (by simp)) hTX
  have hTZ' : (ShortComplex.mk iZ TZ.g hZ).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk eZ (Iso.refl _) (Iso.refl _) (by simp [iZ]) (by simp)) hTZ
  have := hPX
  have := hPZ
  have := hprojX
  have := hprojZ
  obtain ⟨K, i, p, hip, a, b, hab, hT, hU, _⟩ :=
    hN.exists_copresentation_horseshoe hS hTX' hTZ'
  refine ⟨ShortComplex.mk i p hip, ShortComplex.mk a b hab,
    hT, ⟨Iso.refl _⟩, ?_, inferInstance, hU, ⟨Iso.refl _⟩, hKX, hKZ⟩
  exact Module.Finite.equiv (ModuleCat.biprodIsoProd TX.X₂ TZ.X₂).symm.toLinearEquiv

end TauCeti
