/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Splitting
public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Extensions of totally acyclic complexes

Total acyclicity is preserved by a short exact sequence of complexes which splits in every
degree. The splitting makes the middle terms finite projective. It also makes the dual sequence
exact, while the ordinary long exact homology sequence gives acyclicity of the middle complex.

This is the homological part of the complete horseshoe argument: once an extension of
Gorenstein-projective modules has been lifted to a degreewise split sequence of complete
resolutions, its middle resolution is again complete.

## Main result

* `CochainComplex.IsTotallyAcyclic.of_degreewise_split`: the middle complex in a degreewise split
  extension of totally acyclic complexes is totally acyclic.
* `CochainComplex.IsTotallyAcyclic.isExtensionClosed`: totally acyclic complexes form an
  extension-closed property for the componentwise split exact structure.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

open CategoryTheory Limits

universe v u

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A]
  {S : ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ)}

/-- The middle complex in a degreewise split extension of totally acyclic complexes is totally
acyclic. The chosen splittings need not commute with the differentials. -/
theorem of_degreewise_split (h₁ : S.X₁.IsTotallyAcyclic) (h₃ : S.X₃.IsTotallyAcyclic)
    (s : ∀ n, (ShortComplex.mk (S.f.f n) (S.g.f n)
      (by rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f])).Splitting) :
    S.X₂.IsTotallyAcyclic where
  finite n := by
    have := h₁.finite n
    have := h₃.finite n
    exact Module.Finite.equiv
      (((s n).isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv)
  projective n := by
    have := h₁.projective n
    have := h₃.projective n
    exact Projective.of_iso ((s n).isoBinaryBiproduct).symm inferInstance
  acyclic := by
    let hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S fun n ↦
      { exact := (s n).exact, mono_f := (s n).mono_f, epi_g := (s n).epi_g }
    exact hS.acyclic_X₂ h₁.acyclic h₃.acyclic
  exact_dual i j k hij hjk := by
    let sᵢ := s i
    let sⱼ := s j
    let sₖ := s k
    have f_r (n : ℤ) : S.f.f n ≫ (s n).r = 𝟙 _ := (s n).f_r
    have s_g (n : ℤ) : (s n).s ≫ S.g.f n = 𝟙 _ := (s n).s_g
    intro φ
    constructor
    · intro hφ
      -- Extend the left primitive across the split inclusion.
      let φ₁ : S.X₁.X j →ₗ[A] A := φ.comp (S.f.f j).hom
      have hφ₁ : φ₁.comp (S.X₁.d i j).hom = 0 := by
        ext x
        have hcomm := congrArg ModuleCat.Hom.hom (S.f.comm i j)
        have hx := LinearMap.congr_fun hcomm x
        have hz := congrArg (fun f ↦ f ((S.f.f i).hom x)) hφ
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx ⊢
        simp only [LinearMap.lcomp_apply, LinearMap.zero_apply] at hz
        simp only [φ₁, LinearMap.comp_apply, LinearMap.zero_apply]
        rw [← hx, hz]
      obtain ⟨ψ₁, hψ₁⟩ := (h₁.exact_dual i j k hij hjk φ₁).mp hφ₁
      let ψ₀ : S.X₂.X k →ₗ[A] A := ψ₁.comp sₖ.r.hom
      -- Descend the residual functional through the split projection.
      let ρ : S.X₂.X j →ₗ[A] A := φ - ψ₀.comp (S.X₂.d j k).hom
      have hρf : ρ.comp (S.f.f j).hom = 0 := by
        ext x
        have hcomm := congrArg ModuleCat.Hom.hom (S.f.comm j k)
        have hx := LinearMap.congr_fun hcomm x
        have hr := congrArg ModuleCat.Hom.hom (f_r k)
        have hrx := LinearMap.congr_fun hr ((S.X₁.d j k).hom x)
        have hrx' : sₖ.r.hom ((S.f.f k).hom ((S.X₁.d j k).hom x)) =
            (S.X₁.d j k).hom x := by
          simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
            LinearMap.id_apply] using hrx
        have hψx := congrArg (fun f ↦ f x) hψ₁
        simp only [ρ, ψ₀, φ₁, LinearMap.sub_apply, LinearMap.comp_apply,
          ModuleCat.hom_comp, LinearMap.zero_apply] at hx hψx ⊢
        simp only [LinearMap.lcomp_apply] at hψx
        rw [hx, hrx', hψx]
        simp
      let ρ₃ : S.X₃.X j →ₗ[A] A := ρ.comp sⱼ.s.hom
      have hρ_eq : ρ₃.comp (S.g.f j).hom = ρ :=
        sⱼ.comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero ρ hρf
      have hρ : ρ.comp (S.X₂.d i j).hom = 0 := by
        ext x
        have hd := congrArg ModuleCat.Hom.hom (S.X₂.d_comp_d i j k)
        have hdx := LinearMap.congr_fun hd x
        have hφx := congrArg (fun f ↦ f x) hφ
        simp only [ρ, ψ₀, LinearMap.sub_apply, LinearMap.comp_apply,
          ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.zero_apply] at hdx ⊢
        simp only [LinearMap.lcomp_apply, LinearMap.zero_apply] at hφx
        rw [hφx, hdx]
        simp
      have hρ₃ : ρ₃.comp (S.X₃.d i j).hom = 0 := by
        apply LinearMap.ext
        intro x
        have hcomm := congrArg ModuleCat.Hom.hom (S.g.comm i j)
        have hx := LinearMap.congr_fun hcomm (sᵢ.s.hom x)
        have hs := congrArg ModuleCat.Hom.hom (s_g i)
        have hsx := LinearMap.congr_fun hs x
        have hsx' : (S.g.f i).hom (sᵢ.s.hom x) = x := by
          simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
            LinearMap.id_apply] using hsx
        have hz := LinearMap.congr_fun hρ (sᵢ.s.hom x)
        have hx' : (S.X₃.d i j).hom ((S.g.f i).hom (sᵢ.s.hom x)) =
            (S.g.f j).hom ((S.X₂.d i j).hom (sᵢ.s.hom x)) := by
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx
        simp only [ρ₃, LinearMap.comp_apply, LinearMap.zero_apply] at hz ⊢
        rw [← hsx', hx']
        have hρ_eqx := LinearMap.congr_fun hρ_eq
          ((S.X₂.d i j).hom (sᵢ.s.hom x))
        simpa only [ρ₃, LinearMap.comp_apply] using hρ_eqx.trans hz
      -- Lift the right primitive and combine it with the extended left primitive.
      obtain ⟨ψ₃, hψ₃⟩ := (h₃.exact_dual i j k hij hjk ρ₃).mp hρ₃
      refine ⟨ψ₀ + ψ₃.comp (S.g.f k).hom, ?_⟩
      apply LinearMap.ext
      intro x
      have hcomm := congrArg ModuleCat.Hom.hom (S.g.comm j k)
      have hx := LinearMap.congr_fun hcomm x
      have hx' : (S.g.f k).hom ((S.X₂.d j k).hom x) =
          (S.X₃.d j k).hom ((S.g.f j).hom x) := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx.symm
      have hψx := congrArg (fun f ↦ f ((S.g.f j).hom x)) hψ₃
      have hρx := LinearMap.congr_fun hρ_eq x
      simp only [LinearMap.lcomp_apply] at hψx
      simp only [LinearMap.lcomp_apply, LinearMap.add_apply, LinearMap.comp_apply] at hρx ⊢
      rw [hx', hψx, hρx]
      simp only [ρ, LinearMap.sub_apply, LinearMap.comp_apply]
      abel
    · rintro ⟨ψ, rfl⟩
      ext x
      have hd := congrArg ModuleCat.Hom.hom (S.X₂.d_comp_d i j k)
      have hdx := LinearMap.congr_fun hd x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, ModuleCat.hom_comp,
        ModuleCat.hom_zero, LinearMap.zero_apply] at hdx ⊢
      rw [hdx]
      exact map_zero ψ

/-- Totally acyclic complexes are extension closed for the componentwise split exact structure
on cochain complexes. -/
theorem isExtensionClosed :
    TauCeti.ExactStructure.IsExtensionClosed
      ((TauCeti.ExactStructure.split (ModuleCat.{v} A)).homologicalComplex (ComplexShape.up ℤ))
      (fun P ↦ CochainComplex.IsTotallyAcyclic P) where
  prop_X₂ hS h₁ h₃ := by
    apply of_degreewise_split h₁ h₃
    intro n
    have hSn := (TauCeti.ExactStructure.homologicalComplex_conflation_iff
      (TauCeti.ExactStructure.split (ModuleCat.{v} A)) (ComplexShape.up ℤ) _).mp hS n
    exact ((TauCeti.ExactStructure.split_conflation _).mp hSn).some

end CochainComplex.IsTotallyAcyclic
