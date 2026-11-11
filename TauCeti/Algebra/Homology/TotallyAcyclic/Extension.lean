/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.DegreewiseSplit
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

/-- The forward direction of exactness of the dual of the middle complex of a degreewise split
extension of totally acyclic complexes. -/
private theorem exists_dual_primitive
    (s : ∀ n, (ShortComplex.mk (S.f.f n) (S.g.f n)
      (by rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f])).Splitting)
    (h₁ : S.X₁.IsTotallyAcyclic) (h₃ : S.X₃.IsTotallyAcyclic)
    {i j k : ℤ} (hij : i + 1 = j) (hjk : j + 1 = k) {φ : S.X₂.X j →ₗ[A] A}
    (hφ : φ.comp (S.X₂.d i j).hom = 0) :
    ∃ ψ : S.X₂.X k →ₗ[A] A, ψ.comp (S.X₂.d j k).hom = φ := by
  -- Extend the left primitive across the split inclusion.
  obtain ⟨ψ₁, hψ₁⟩ := (h₁.exact_dual i j k hij hjk (φ.comp (S.f.f j).hom)).mp
    (ShortComplex.comp_f_comp_d_eq_zero hφ)
  let ψ₀ : S.X₂.X k →ₗ[A] A := ψ₁.comp (s k).r.hom
  -- Descend the residual functional through the split projection.
  have hρf := ShortComplex.residual_comp_f_eq_zero (s k) hψ₁
  have hρ := ShortComplex.residual_comp_d_eq_zero hφ ψ₀
  set ρ : S.X₂.X j →ₗ[A] A := φ - ψ₀.comp (S.X₂.d j k).hom with hρdef
  have hρ_eq := (s j).comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero ρ hρf
  -- Lift the right primitive and combine it with the extended left primitive.
  obtain ⟨ψ₃, hψ₃⟩ := (h₃.exact_dual i j k hij hjk (ρ.comp (s j).s.hom)).mp
    (ShortComplex.comp_s_comp_d_eq_zero (s i) (s j) hρf hρ)
  refine ⟨ψ₀ + ψ₃.comp (S.g.f k).hom, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (S.g.comm j k)) x
  have hx' : (S.g.f k).hom ((S.X₂.d j k).hom x) = (S.X₃.d j k).hom ((S.g.f j).hom x) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx.symm
  have hψx := LinearMap.congr_fun hψ₃ ((S.g.f j).hom x)
  have hρx := LinearMap.congr_fun hρ_eq x
  simp only [LinearMap.lcomp_apply, LinearMap.comp_apply] at hψx
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at hρx ⊢
  rw [hx', hψx, hρx]
  simp only [hρdef, LinearMap.sub_apply, LinearMap.comp_apply]
  abel

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
    intro φ
    constructor
    · exact fun hφ ↦ exists_dual_primitive s h₁ h₃ hij hjk hφ
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
