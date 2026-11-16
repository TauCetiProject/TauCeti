/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Composition
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Uniqueness

/-!
# Spectral mapping and composition for the holomorphic functional calculus

For an element `a` of a complex Banach algebra `A` and a holomorphic germ `g` near `spectrum ℂ a`,
the **spectral mapping theorem** states that `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`
(equivalently `f '' spectrum ℂ a` for any holomorphic representative `f` of `g`).

Combining spectral mapping with uniqueness of the holomorphic functional calculus yields the
**composition theorem** (`g(f(a)) = (g ∘ f)(a)`), both at the germ level (`holomorphicCalculus_comp`
and `holomorphicCalculus_comp_ofFun`) and on open domains (`holomorphicCalculusOn_comp` and
`holomorphicCalculusOn_comp_restrict`), together with the existence of a single open restriction
neighbourhood `U' ≤ U` of `spectrum ℂ a` mapped by `f` into `V` valid for all `ψ` on `V`.

No normalization of `‖(1 : A)‖` or nontriviality of `A` is assumed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Theorems VII.4.8 and VII.4.10.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

section SpectralMapping

/-- **Spectral mapping theorem for the holomorphic germ calculus.** For every `a : A` and every
`g : holomorphicGerms (spectrum ℂ a)`, `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`. -/
@[simp]
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g := by
  refine Subset.antisymm (AlgHom.spectrum_apply_subset (holomorphicCalculus a) g) ?_
  intro c hc
  rw [holomorphicGerms.spectrum_eq] at hc
  obtain ⟨z₀, hz₀, hval⟩ := hc
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  have hf_z₀ : extend f z₀ = c := by
    rw [extend_apply f ⟨z₀, ha hz₀⟩, ← eval_toGerm ha z₀ hz₀ f, hval]
  -- Factor `extend f z - c = (z - z₀) * dslope (extend f) z₀ z` holomorphically on `U`.
  have hq_diff : DifferentiableOn ℂ (dslope (extend f) z₀) U :=
    (Complex.differentiableOn_dslope (U.isOpen.mem_nhds (ha hz₀))).mpr (differentiableOn_extend f)
  let q : holomorphicFunctions U := of U (dslope (extend f) z₀) hq_diff
  let lin : holomorphicFunctions U :=
    of U (fun z ↦ (Polynomial.C z₀ - Polynomial.X).eval z)
      (Polynomial.C z₀ - Polynomial.X).differentiable.differentiableOn
  have hfac : algebraMap ℂ (holomorphicFunctions U) c = f + lin * q := by
    apply Subtype.ext
    ext z
    have hsl := sub_smul_dslope (extend f) z₀ (z : ℂ)
    rw [smul_eq_mul, extend_apply f z, hf_z₀] at hsl
    simp [lin, q]
    linear_combination hsl
  have hfac' : algebraMap ℂ (holomorphicFunctions U) c = f + q * lin := by
    rw [hfac, mul_comm lin q]
  have hA₁ : algebraMap ℂ A c - holomorphicCalculusOn a U ha f =
      (algebraMap ℂ A z₀ - a) * holomorphicCalculusOn a U ha q := by
    have h := congrArg (holomorphicCalculusOn a U ha) hfac
    simp only [lin, AlgHom.commutes, map_add, map_mul, holomorphicCalculusOn_polynomial,
      map_sub, Polynomial.aeval_C, Polynomial.aeval_X] at h
    exact sub_eq_of_eq_add' h
  have hA₂ : algebraMap ℂ A c - holomorphicCalculusOn a U ha f =
      holomorphicCalculusOn a U ha q * (algebraMap ℂ A z₀ - a) := by
    have h := congrArg (holomorphicCalculusOn a U ha) hfac'
    simp only [lin, AlgHom.commutes, map_add, map_mul, holomorphicCalculusOn_polynomial,
      map_sub, Polynomial.aeval_C, Polynomial.aeval_X] at h
    exact sub_eq_of_eq_add' h
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  have hleft :
      (algebraMap ℂ A z₀ - a) * (holomorphicCalculusOn a U ha q * ↑u⁻¹) = 1 := by
    rw [← mul_assoc, ← hA₁, ← hu, Units.mul_inv]
  have hright :
      (↑u⁻¹ * holomorphicCalculusOn a U ha q) * (algebraMap ℂ A z₀ - a) = 1 := by
    rw [mul_assoc, ← hA₂, ← hu, Units.inv_mul]
  exact spectrum.notMem_iff.mpr
    (spectrum.mem_resolventSet_of_left_right_inverse hleft hright) hz₀

/-- **Spectral mapping theorem for represented germs.** For `f` analytic near `spectrum ℂ a`,
`spectrum ℂ (holomorphicCalculus a (ofFun f hf)) = f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a := by
  rw [spectrum_holomorphicCalculus, holomorphicGerms.spectrum_ofFun]

/-- **Spectral mapping theorem on open neighbourhoods.** For `f : holomorphicFunctions U` with
`spectrum ℂ a ⊆ U`, `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a`. -/
@[simp]
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm,
    toGerm_eq_ofFun ha f (extend f) (analyticOnNhd_extend ha f) (fun z ↦ (extend_apply f z).symm),
    spectrum_holomorphicCalculus_ofFun]

/-- Membership form of `spectrum_holomorphicCalculusOn` written directly in terms of `f.val`. -/
theorem mem_spectrum_holomorphicCalculusOn_iff (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) {c : ℂ} :
    c ∈ spectrum ℂ (holomorphicCalculusOn a U ha f) ↔
      ∃ (z : ℂ) (hz : z ∈ spectrum ℂ a), f.val ⟨z, ha hz⟩ = c := by
  rw [spectrum_holomorphicCalculusOn]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (extend_apply f ⟨z, ha hz⟩).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, extend_apply f ⟨z, ha hz⟩⟩

end SpectralMapping

section Composition

/-- **Composition theorem for the holomorphic germ calculus.** For `g : holomorphicGerms (spectrum
ℂ a)` and `k : holomorphicGerms (spectrum ℂ (holomorphicCalculus a g))`, evaluating `k` at
`holomorphicCalculus a g` coincides with evaluating the pulled-back germ
`holomorphicGerms.comap g _ k` at `a`. -/
@[simp]
theorem holomorphicCalculus_comp (a : A) (g : holomorphicGerms (spectrum ℂ a))
    (k : holomorphicGerms (spectrum ℂ (holomorphicCalculus a g))) :
    holomorphicCalculus (holomorphicCalculus a g) k =
      holomorphicCalculus a
        (holomorphicGerms.comap g (spectrum_holomorphicCalculus a g).ge k) := by
  let b : A := holomorphicCalculus a g
  have hg : spectrum ℂ g ⊆ spectrum ℂ b := (spectrum_holomorphicCalculus a g).ge
  let Ψ : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A :=
    (holomorphicCalculus a).comp (holomorphicGerms.comap g hg)
  have hΨ_id : Ψ (holomorphicGerms.ofFun id analyticOnNhd_id) = b := by
    simp [Ψ, b]
  have hΨ_cont : ∀ (V : Opens ℂ) (hbV : spectrum ℂ b ⊆ V), Continuous (Ψ.comp (toGerm hbV)) := by
    intro V hbV
    obtain ⟨U, haU, f, hfg⟩ := holomorphicGerms.exists_toGerm_eq g
    have hgf : spectrum ℂ (toGerm haU f) ⊆ spectrum ℂ b := hfg.symm ▸ hg
    let U' : Opens ℂ := preimageOpens f V
    have haU' : spectrum ℂ a ⊆ U' :=
      holomorphicGerms.subset_preimageOpens_of_spectrum_subset hgf hbV
    have hle : U' ≤ U := preimageOpens_le f V
    have hfU' : toGerm haU' (restrict hle f) = g := (toGerm_restrict haU' hle f).trans hfg
    have hgU' : spectrum ℂ (toGerm haU' (restrict hle f)) ⊆ spectrum ℂ b := hfU'.symm ▸ hg
    have hfun : (Ψ.comp (toGerm hbV) : holomorphicFunctions V → A) =
        (holomorphicCalculusOn a U' haU').comp
          (HolomorphicFunctions.comap (restrict hle f) (restrict_preimageOpens_mem f V)) := by
      ext ψ
      simp only [Ψ, AlgHom.coe_comp, Function.comp_apply,
        holomorphicGerms.comap_congr_left hfU'.symm (hg₂ := hgU'),
        holomorphicGerms.comap_toGerm haU' hbV (restrict hle f) (restrict_preimageOpens_mem f V)
          hgU' ψ,
        holomorphicCalculus_toGerm]
    rw [hfun]
    exact (continuous_holomorphicCalculusOn a U' haU').comp
      (continuous_comap (restrict hle f) (restrict_preimageOpens_mem f V))
  have huniq : Ψ = holomorphicCalculus b := holomorphicCalculus_unique b Ψ hΨ_id hΨ_cont
  exact congrFun (congrArg DFunLike.coe huniq.symm) k

/-- **Composition theorem for represented germs.** If `f` is analytic near `spectrum ℂ a` and `ψ`
is analytic near `f '' spectrum ℂ a`, then `ψ(f(a)) = (ψ ∘ f)(a)`. -/
theorem holomorphicCalculus_comp_ofFun (a : A) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (f '' spectrum ℂ a)) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
      (holomorphicGerms.ofFun ψ (hψ.mono (spectrum_holomorphicCalculus_ofFun a f hf).le)) =
      holomorphicCalculus a
        (holomorphicGerms.ofFun (ψ ∘ f) (hψ.comp hf (mapsTo_image f (spectrum ℂ a)))) := by
  rw [holomorphicCalculus_comp, holomorphicGerms.comap_ofFun]

/-- If `f : holomorphicFunctions U` maps `spectrum ℂ a` into `V`, then the spectrum of
`holomorphicCalculusOn a U ha f` is contained in `V`. -/
theorem spectrum_holomorphicCalculusOn_subset (a : A) {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hfV : ∀ (z : ℂ) (hz : z ∈ spectrum ℂ a), f.val ⟨z, ha hz⟩ ∈ V) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) ⊆ V := by
  intro c hc
  obtain ⟨z, hz, rfl⟩ := (mem_spectrum_holomorphicCalculusOn_iff a U ha f).mp hc
  exact hfV z hz

/-- **Open-domain composition of the holomorphic calculus.** When `f : holomorphicFunctions U` maps
`U` into `V` and `ψ : holomorphicFunctions V`, evaluating `ψ` at `holomorphicCalculusOn a U ha f`
agrees with evaluating `HolomorphicFunctions.comap f hfV ψ` at `a`. -/
@[simp]
theorem holomorphicCalculusOn_comp (a : A) {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hfV : ∀ z : U, f.val z ∈ V) (ψ : holomorphicFunctions V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V
      (spectrum_holomorphicCalculusOn_subset a ha f fun z hz ↦ hfV ⟨z, ha hz⟩) ψ =
      holomorphicCalculusOn a U ha (HolomorphicFunctions.comap f hfV ψ) := by
  have hbV : spectrum ℂ (holomorphicCalculus a (toGerm ha f)) ⊆ V := by
    rw [holomorphicCalculus_toGerm]
    exact spectrum_holomorphicCalculusOn_subset a ha f fun z hz ↦ hfV ⟨z, ha hz⟩
  have h := holomorphicCalculus_comp a (toGerm ha f) (toGerm hbV ψ)
  rw [holomorphicGerms.comap_toGerm ha hbV f hfV
    (spectrum_holomorphicCalculus a (toGerm ha f)).ge ψ,
    holomorphicCalculus_toGerm _ V hbV ψ,
    holomorphicCalculus_toGerm a U ha (HolomorphicFunctions.comap f hfV ψ),
    holomorphicCalculusOn_congr (holomorphicCalculus_toGerm a U ha f)
      (hb := spectrum_holomorphicCalculusOn_subset a ha f fun z hz ↦ hfV ⟨z, ha hz⟩)] at h
  exact h

/-- **Open-domain composition on a smaller neighbourhood `U' ≤ U`.** When `f` is holomorphic on `U`
with `f(σ(a)) ⊆ V` and `U' ≤ U` is an open neighbourhood of `spectrum ℂ a` mapped by `f` into `V`,
evaluating `ψ : holomorphicFunctions V` at `holomorphicCalculusOn a U ha f` equals evaluating the
restricted pullback `HolomorphicFunctions.comap (restrict hU' f) hfV ψ` on `U'`. -/
theorem holomorphicCalculusOn_comp_restrict (a : A) {U V U' : Opens ℂ}
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U)
    (ha' : spectrum ℂ a ⊆ U') (hU' : U' ≤ U)
    (hfV : ∀ z : U', (restrict hU' f).val z ∈ V) (ψ : holomorphicFunctions V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V
      (spectrum_holomorphicCalculusOn_subset a ha f fun z hz ↦ by
        simpa only [HolomorphicFunctions.restrict_apply, Set.inclusion] using hfV ⟨z, ha' hz⟩) ψ =
      holomorphicCalculusOn a U' ha' (HolomorphicFunctions.comap (restrict hU' f) hfV ψ) := by
  have heq : holomorphicCalculusOn a U ha f = holomorphicCalculusOn a U' ha' (restrict hU' f) :=
    (holomorphicCalculusOn_restrict a ha' hU' f).symm
  rw [holomorphicCalculusOn_congr heq
    (hb := spectrum_holomorphicCalculusOn_subset a ha' (restrict hU' f) fun z hz ↦
      hfV ⟨z, ha' hz⟩)]
  exact holomorphicCalculusOn_comp a ha' (restrict hU' f) hfV ψ

/-- **Open-domain composition with domain shrinking.** Whenever `f : holomorphicFunctions U` maps
`spectrum ℂ a` into an open set `V`, there exists an open neighbourhood `U' ≤ U` of `spectrum ℂ a`
mapped by `f` into `V` on which `(ψ ∘ f)(a) = ψ(f(a))` for every `ψ : holomorphicFunctions V`. -/
theorem exists_opens_le_holomorphicCalculusOn_comp (a : A) {U V : Opens ℂ}
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U)
    (hfV : ∀ (z : ℂ) (hz : z ∈ spectrum ℂ a), f.val ⟨z, ha hz⟩ ∈ V) :
    ∃ (U' : Opens ℂ) (ha' : spectrum ℂ a ⊆ U') (hU' : U' ≤ U)
      (hfV' : ∀ z : U', (restrict hU' f).val z ∈ V),
      ∀ ψ : holomorphicFunctions V,
        holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V
          (spectrum_holomorphicCalculusOn_subset a ha f hfV) ψ =
          holomorphicCalculusOn a U' ha' (HolomorphicFunctions.comap (restrict hU' f) hfV' ψ) :=
  ⟨preimageOpens f V, subset_preimageOpens ha f hfV, preimageOpens_le f V,
    restrict_preimageOpens_mem f V, fun ψ ↦
    holomorphicCalculusOn_comp_restrict a ha f (subset_preimageOpens ha f hfV)
      (preimageOpens_le f V) (restrict_preimageOpens_mem f V) ψ⟩

end Composition

end TauCeti
