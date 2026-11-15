/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Kernel
public import TauCeti.Algebra.Module.Nakayama.Hom
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.LinearAlgebra.Dual.Annihilator

/-!
# Injectively trivial maps into the Auslander–Reiten translate

For an arrow `f : P₁ → P₀` between finite projectives, a map `g : N → D Tr(f)`
determines a scalar functional on `Hom_A(P₁,N)` by the Nakayama Hom pairing.
This functional is in the image of dual restriction to `ker f` exactly when `g`
extends across an embedding of `N` into an injective module.

Equivalently, the functional vanishes on maps `P₁ → N` killing `ker f` exactly
when `g` factors through that embedding. These maps are the Hom cocycles of a
projective presentation. The criterion identifies the injectively trivial maps
that must be quotiented out in Auslander–Reiten duality, without identifying a
general presentation's Hom cokernel with `Ext¹`.

No minimality, finite-dimensionality of the algebra, or exactness assumption on
`f` is required. The injective module can have a different universe from the
presenting modules; `Small` is the hypothesis used by Mathlib's injective extension
property across universes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.

The comparison uses `nakayamaHomEquiv` and
`LinearMap.auslanderReitenTranslateEquivKerNakayama`.
-/

public section

namespace LinearMap

open TauCeti

universe u v w z t s

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {P₀ : Type w} {P₁ : Type z} {N : Type t} {I : Type s}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup I] [Module A I] [Module k I] [IsScalarTower k A I]
  [Small.{s} A] [Module.Injective A I]

/-- Under Nakayama Hom duality, dual restriction to the kernel of a presenting map
detects exactly the maps into its translate that extend across an injective embedding. -/
theorem auslanderReitenTranslate_exists_extension_iff
    (f : P₁ →ₗ[A] P₀) (j : N →ₗ[A] I) (hj : Function.Injective j)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    (∃ h : I →ₗ[A] AuslanderReitenTranslate k f, h.comp j = g) ↔
      (nakayamaHomEquiv k A P₁ N).symm ((auslanderReitenTranslateToNakayama f).comp g) ∈
        range (((ker f).subtype.lcomp k N).dualMap) := by
  let r := (ker f).subtype.lcomp k N
  let d := f.lcomp k I
  let b := j.compRight k (M := P₁)
  -- Compute the inverse image of the coboundaries using injectivity of the coefficient module.
  have hb : (range d).comap b = ker r := comap_range_lcomp_compRight f j hj
  -- Dualizing this equality makes the extension problem a statement about annihilators.
  have hann : (range d).dualAnnihilator.map b.dualMap = range r.dualMap := by
    rw [Submodule.dualAnnihilator_map_dualMap_eq, hb,
      range_dualMap_eq_dualAnnihilator_ker]
  constructor
  · rintro ⟨h, rfl⟩
    let H := (auslanderReitenTranslateToNakayama f).comp h
    let χ := (nakayamaHomEquiv k A P₁ I).symm H
    have hχ : χ ∈ (range d).dualAnnihilator := by
      rw [← ker_dualMap_eq_dualAnnihilator_range, mem_ker]
      apply (nakayamaHomEquiv k A P₀ I).injective
      rw [nakayamaHomEquiv_dualMap_lcomp]
      ext n ψ
      simp [χ, H, (exact_auslanderReitenTranslateToNakayama_nakayamaMap f).apply_apply_eq_zero]
    rw [← hann]
    refine ⟨χ, hχ, ?_⟩
    apply (nakayamaHomEquiv k A P₁ N).injective
    simp [b, χ, H, nakayamaHomEquiv_dualMap_compRight, LinearMap.comp_assoc]
  · intro hg
    rw [← hann] at hg
    obtain ⟨χ, hχ, hχg⟩ := hg
    let H := nakayamaHomEquiv k A P₁ I χ
    have hH : f.nakayamaMap.comp H = 0 := by
      have hdχ : d.dualMap χ = 0 := by
        rw [← ker_dualMap_eq_dualAnnihilator_range] at hχ
        exact mem_ker.mp hχ
      simpa only [d, nakayamaHomEquiv_dualMap_lcomp, map_zero] using
        congrArg (nakayamaHomEquiv k A P₀ I) hdχ
    let h := (auslanderReitenTranslateEquivKerNakayama f).symm.toLinearMap.comp
      (H.codRestrict (ker f.nakayamaMap) fun n ↦
        mem_ker.mpr (LinearMap.congr_fun hH n))
    refine ⟨h, ?_⟩
    have hHj : H.comp j = (auslanderReitenTranslateToNakayama f).comp g := by
      simpa only [b, nakayamaHomEquiv_dualMap_compRight,
        LinearEquiv.apply_symm_apply] using
        congrArg (nakayamaHomEquiv k A P₁ N) hχg
    apply LinearMap.ext
    intro n
    apply auslanderReitenTranslateToNakayama_injective f
    apply (NakayamaModule.equivDual k A P₁).injective
    ext ψ
    simpa [h, auslanderReitenTranslateToNakayama_apply] using
      congrArg (fun F ↦ NakayamaModule.equivDual k A P₁ (F n) ψ) hHj

end LinearMap
