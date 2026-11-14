/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Unique

/-!
# Composition for the holomorphic functional calculus

If `f` is a holomorphic germ near `spectrum ℂ a` and `g` is a holomorphic germ near
`spectrum ℂ (holomorphicCalculus a f)` (which equals `spectrum ℂ f` by the spectral mapping
theorem), then evaluating `holomorphicCalculus` of `holomorphicCalculus a f` at `g` agrees with
evaluating `holomorphicCalculus a` at the composite germ `g ∘ f`.

Rather than computing iterated nested contour integrals, the proof deduces composition directly from
the uniqueness theorem (`eq_holomorphicCalculus_of_forall_continuous`), the spectral mapping
theorem (`spectrum_holomorphicCalculus`), and compact-open continuity of postcomposition on algebras
of holomorphic functions (`HolomorphicFunctions.continuous_comp`).

## Main results

* `TauCeti.holomorphicCalculus_comp` and `TauCeti.holomorphicCalculus_comp_restrict`: germ-level
  composition `g(f(a)) = (g ∘ f)(a)`.
* `TauCeti.holomorphicCalculus_ofFun_comp`: represented analytic germ form.
* `TauCeti.holomorphicCalculusOn_comp`, `TauCeti.holomorphicCalculusOn_comp_restrict`, and
  `TauCeti.holomorphicCalculusOn_of_comp`: open-domain forms.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.9.
* N. Bourbaki, *Théories spectrales*, Ch. I, §4, No. 4, Proposition 5.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Theorem VII.4.7.
-/

public noncomputable section

open Set TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Composition theorem for the holomorphic germ calculus.** For every Banach-algebra element `a`,
holomorphic germ `f` near `spectrum ℂ a`, and holomorphic germ `g` near
`spectrum ℂ (holomorphicCalculus a f)`, `g(f(a)) = (g ∘ f)(a)`. -/
@[simp]
theorem holomorphicCalculus_comp (a : A) (f : holomorphicGerms (spectrum ℂ a))
    (g : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f))) :
    holomorphicCalculus (holomorphicCalculus a f) g =
      holomorphicCalculus a (holomorphicGerms.comp f (spectrum_holomorphicCalculus a f).ge g) := by
  let b := holomorphicCalculus a f
  let Φ : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A :=
    (holomorphicCalculus a).comp (holomorphicGerms.comp f (spectrum_holomorphicCalculus a f).ge)
  suffices hΦ : Φ = holomorphicCalculus b from (DFunLike.congr_fun hΦ g).symm
  refine eq_holomorphicCalculus_of_forall_continuous Φ ?_ ?_
  · simp [Φ, b]
  · intro V hbV
    obtain ⟨U, haU, f₀, hf₀⟩ := holomorphicGerms.exists_toGerm_eq f
    have hmaps_σ : MapsTo (extend f₀) (spectrum ℂ a) V := by
      rw [mapsTo_iff_image_subset, ← holomorphicGerms.spectrum_ofFun (extend f₀)
        (analyticOnNhd_extend haU f₀), ← toGerm_apply haU f₀, hf₀,
        ← spectrum_holomorphicCalculus a f]
      exact hbV
    obtain ⟨U', haU', hU'U, hf₀V⟩ := exists_le_mapsTo_extend haU f₀ hmaps_σ
    let f₁ : holomorphicFunctions U' := HolomorphicFunctions.restrict hU'U f₀
    have hf₁ : toGerm haU' f₁ = f := (toGerm_restrict haU' hU'U f₀).trans hf₀
    have hf₁V : MapsTo (extend f₁) U' V := fun z hz ↦ by
      rw [extend_apply f₁ ⟨z, hz⟩, HolomorphicFunctions.restrict_apply,
        ← extend_apply f₀ ⟨z, hU'U hz⟩]
      exact hf₀V hz
    have heq : Φ ∘ toGerm hbV = holomorphicCalculusOn a U' haU' ∘ comp f₁ hf₁V := by
      ext k
      simp only [Function.comp_apply, AlgHom.comp_apply, Φ]
      -- Rewrite `f` as `toGerm haU' f₁` to evaluate `holomorphicGerms.comp` on open domains.
      have hcomp : holomorphicGerms.comp f (spectrum_holomorphicCalculus a f).ge (toGerm hbV k) =
          toGerm haU' (comp f₁ hf₁V k) := by
        subst hf₁
        exact comp_toGerm haU' hbV f₁ hf₁V _ k
      rw [hcomp, holomorphicCalculus_toGerm]
    rw [heq]
    exact (continuous_holomorphicCalculusOn a U' haU').comp (continuous_comp f₁ hf₁V)

/-- Germ composition when the outer germ is given on a set `t` containing `spectrum ℂ f`. -/
theorem holomorphicCalculus_comp_restrict (a : A) (f : holomorphicGerms (spectrum ℂ a))
    {t : Set ℂ} (ht : spectrum ℂ f ⊆ t) (g : holomorphicGerms t) :
    holomorphicCalculus (holomorphicCalculus a f)
        (holomorphicGerms.restrict ((spectrum_holomorphicCalculus a f).trans_subset ht) g) =
      holomorphicCalculus a (holomorphicGerms.comp f ht g) := by
  rw [holomorphicCalculus_comp, holomorphicGerms.comp_restrict]

/-- **Composition theorem (represented analytic germ form).** If `f` is analytic near `spectrum ℂ a`
and `g` is analytic near a set `t` containing `f '' spectrum ℂ a`, then `g(f(a)) = (g ∘ f)(a)`. -/
theorem holomorphicCalculus_ofFun_comp (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) {t : Set ℂ} (ht : f '' spectrum ℂ a ⊆ t)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g t) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
        (holomorphicGerms.ofFun g
          (hg.mono ((spectrum_holomorphicCalculus_ofFun a f hf).trans_subset ht))) =
      holomorphicCalculus a
        (holomorphicGerms.ofFun (g ∘ f) (hg.comp hf (mapsTo_iff_image_subset.mpr ht))) := by
  have hst : spectrum ℂ (holomorphicGerms.ofFun f hf) ⊆ t := by
    rwa [holomorphicGerms.spectrum_ofFun]
  rw [← holomorphicGerms.restrict_ofFun
      ((spectrum_holomorphicCalculus a (holomorphicGerms.ofFun f hf)).trans_subset hst) g hg,
    holomorphicCalculus_comp_restrict a (holomorphicGerms.ofFun f hf) hst,
    holomorphicGerms.comp_ofFun]

/-- **Composition theorem on open domains.** If `f : holomorphicFunctions U` maps `U` into `V`, then
for `g : holomorphicFunctions V`, `g(f(a)) = (g ∘ f)(a)`. -/
@[simp]
theorem holomorphicCalculusOn_comp (a : A) {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hfV : MapsTo (extend f) U V)
    (hb : spectrum ℂ (holomorphicCalculusOn a U ha f) ⊆ V) (g : holomorphicFunctions V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V hb g =
      holomorphicCalculusOn a U ha (comp f hfV g) := by
  have hb' : spectrum ℂ (holomorphicCalculus a (toGerm ha f)) ⊆ V := by
    rwa [holomorphicCalculus_toGerm]
  calc holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V hb g
      = holomorphicCalculus (holomorphicCalculus a (toGerm ha f)) (toGerm hb' g) := by
          simp_rw [← holomorphicCalculus_toGerm a U ha f] at hb ⊢
          exact (holomorphicCalculus_toGerm _ V hb g).symm
    _ = holomorphicCalculus a (holomorphicGerms.comp (toGerm ha f)
          (spectrum_holomorphicCalculus a (toGerm ha f)).ge (toGerm hb' g)) :=
          holomorphicCalculus_comp a (toGerm ha f) (toGerm hb' g)
    _ = holomorphicCalculus a (toGerm ha (comp f hfV g)) := by
          rw [comp_toGerm ha hb' f hfV _ g]
    _ = holomorphicCalculusOn a U ha (comp f hfV g) :=
          holomorphicCalculus_toGerm a U ha (comp f hfV g)

/-- Open-domain composition when `f : holomorphicFunctions U` maps only a smaller neighbourhood
`U' ≤ U` of `spectrum ℂ a` into `V`. -/
theorem holomorphicCalculusOn_comp_restrict (a : A) {U U' V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (ha' : spectrum ℂ a ⊆ U') (hU'U : U' ≤ U) (f : holomorphicFunctions U)
    (hfV : MapsTo (extend (HolomorphicFunctions.restrict hU'U f)) U' V)
    (hb : spectrum ℂ (holomorphicCalculusOn a U ha f) ⊆ V) (g : holomorphicFunctions V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V hb g =
      holomorphicCalculusOn a U' ha' (comp (HolomorphicFunctions.restrict hU'U f) hfV g) := by
  have heq : holomorphicCalculusOn a U ha f =
      holomorphicCalculusOn a U' ha' (HolomorphicFunctions.restrict hU'U f) := by
    rw [holomorphicCalculusOn_restrict]
  revert hb
  rw [heq]
  intro hb
  exact holomorphicCalculusOn_comp a ha' (HolomorphicFunctions.restrict hU'U f) hfV hb g

/-- **Composition theorem on open domains (ambient differentiable representatives).** -/
theorem holomorphicCalculusOn_of_comp (a : A) {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hfV : MapsTo f U V)
    (hb : spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) ⊆ V)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha (of U f hf)) V hb (of V g hg) =
      holomorphicCalculusOn a U ha (of U (g ∘ f) (hg.comp hf hfV)) := by
  have hfV' : MapsTo (extend (of U f hf)) U V := fun z hz ↦ by
    rw [extend_apply _ ⟨z, hz⟩, of_apply]
    exact hfV hz
  rw [holomorphicCalculusOn_comp a ha (of U f hf) hfV' hb (of V g hg), comp_of]
  congr 1
  apply Subtype.ext
  ext z
  simp [Function.comp_apply]

end TauCeti
