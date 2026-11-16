/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyRiemannSum
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Composition
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.SpectralMapping

/-!
# Uniqueness and composition for the holomorphic functional calculus

This file proves the uniqueness characterization of `holomorphicCalculus a` and deduces the
composition theorem `g(f(a)) = (g ∘ f)(a)` for an element `a` of a complex Banach algebra `A`.

* **Cauchy Riemann sums:** given a compact subset `K` of an open set `U ⊆ ℂ` and a smaller open
  neighbourhood `V ≤ U` of `K` disjoint from a balanced family `E` of oriented segments in `U`
  whose cycle is null-homologous in `U` and winds once around `V`, the Cauchy Riemann sums
  `HolomorphicFunctions.cauchyRiemannSum hEV f n` converge in `holomorphicFunctions V` to
  `restrict hVU f` (`HolomorphicFunctions.tendsto_cauchyRiemannSum`), and every unital
  complex-algebra homomorphism sending the coordinate germ to `a` maps them to the corresponding
  Riemann sums of resolvents (`HolomorphicFunctions.algHom_toGerm_cauchyRiemannSum`).
* **Uniqueness:** `holomorphicCalculus a` is the unique unital complex-algebra homomorphism
  `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a` whose
  restriction `Φ.comp (toGerm ha)` to `holomorphicFunctions U` is continuous for every open
  neighbourhood `U` of `spectrum ℂ a` (`eq_holomorphicCalculus`,
  `existsUnique_holomorphicCalculus`).
* **Composition:** for `φ : holomorphicGerms (spectrum ℂ a)` and
  `ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))`,
  `holomorphicCalculus (holomorphicCalculus a φ) ψ` equals
  `holomorphicCalculus a (φ.compAlgHom _ ψ)`, with corresponding statements for analytic
  representatives (`holomorphicCalculus_ofFun_comp`) and open neighbourhoods
  (`holomorphicCalculusOn_comp`).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter Metric Set TopologicalSpace Topology
open scoped Finset Real

namespace TauCeti

open Contour HolomorphicFunctions

/-! ### Action of homomorphisms on Cauchy kernels and Cauchy Riemann sums -/

/-- On an open neighbourhood `U` of `spectrum ℂ a` avoiding `w`, `holomorphicCalculusOn` evaluates
the Cauchy kernel `cauchyKernel U w hw` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_cauchyKernel {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (w : ℂ)
    (hw : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha (cauchyKernel U w hw) = resolvent a w := by
  rw [← holomorphicCalculus_toGerm, toGerm_cauchyKernel, holomorphicCalculus_sub_inv_left]

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` maps each Cauchy Riemann sum to the corresponding Riemann sum of
resolvents in `A`. -/
theorem HolomorphicFunctions.algHom_toGerm_cauchyRiemannSum {A : Type*} [Ring A] [Algebra ℂ A]
    {a : A} {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ V) {E : Finset (ℂ × ℂ)}
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (f : holomorphicFunctions U) (n : ℕ) :
    Φ (toGerm ha (cauchyRiemannSum hEV f n)) =
      ((2 * π * I)⁻¹ * (n : ℂ)⁻¹) •
        ∑ e ∈ E, ∑ k ∈ Finset.range n,
          (extend f (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) * (e.2 - e.1)) •
            resolvent a (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) :=
  map_cauchyRiemannSum (Φ.comp (toGerm ha)) hEV f n fun w hw => by
    rw [AlgHom.comp_apply, toGerm_cauchyKernel]
    exact algHom_ofFun_sub_inv_left hΦ w _

/-! ### Uniqueness of the holomorphic functional calculus -/

section Uniqueness

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Any unital complex-algebra homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending
the coordinate germ to `a` whose restrictions to open neighbourhoods of `spectrum ℂ a` are
continuous agrees with `holomorphicCalculusOn a U ha` on every open neighbourhood `U`. -/
theorem eq_holomorphicCalculusOn (a : A) {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (V : Opens ℂ) (ha : spectrum ℂ a ⊆ V), Continuous (Φ.comp (toGerm ha)))
    (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Φ (toGerm ha f) = holomorphicCalculusOn a U ha f := by
  obtain ⟨V, hKV, hVU, E, hEV, hconv⟩ :=
    (spectrum.isCompact (𝕜 := ℂ) a).exists_opens_tendsto_cauchyRiemannSum ha
  have h₁ :
      Tendsto (fun n => Φ (toGerm hKV (cauchyRiemannSum hEV f n))) atTop
        (𝓝 (Φ (toGerm hKV (restrict hVU f)))) :=
    ((hΦ_cont V hKV).tendsto (restrict hVU f)).comp (hconv f)
  have h₂ :
      Tendsto (fun n => holomorphicCalculusOn a V hKV (cauchyRiemannSum hEV f n)) atTop
        (𝓝 (holomorphicCalculusOn a V hKV (restrict hVU f))) :=
    ((continuous_holomorphicCalculusOn a V hKV).tendsto (restrict hVU f)).comp (hconv f)
  have heq :
      (fun n => Φ (toGerm hKV (cauchyRiemannSum hEV f n))) =
        fun n => holomorphicCalculusOn a V hKV (cauchyRiemannSum hEV f n) := by
    ext n
    rw [← holomorphicCalculus_toGerm, algHom_toGerm_cauchyRiemannSum hΦ_id,
      algHom_toGerm_cauchyRiemannSum (holomorphicCalculus_id a)]
  have hlim : Φ (toGerm hKV (restrict hVU f)) = holomorphicCalculusOn a V hKV (restrict hVU f) :=
    tendsto_nhds_unique h₁ (heq ▸ h₂)
  rwa [toGerm_restrict hKV hVU f, holomorphicCalculusOn_restrict a hKV hVU f] at hlim

/-- **Uniqueness of the holomorphic functional calculus.** Any unital complex-algebra homomorphism
on `holomorphicGerms (spectrum ℂ a)` sending the coordinate germ to `a` whose restrictions to all
open neighbourhoods of `spectrum ℂ a` are continuous equals `holomorphicCalculus a`. -/
theorem eq_holomorphicCalculus (a : A) {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha))) :
    Φ = holomorphicCalculus a := by
  apply holomorphicGerms.algHom_ext
  intro U ha f
  rw [holomorphicCalculus_toGerm]
  exact eq_holomorphicCalculusOn a hΦ_id hΦ_cont U ha f

/-- Existence and uniqueness characterization of `holomorphicCalculus a`. -/
theorem existsUnique_holomorphicCalculus (a : A) :
    ∃! Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A,
      Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha)) :=
  ⟨holomorphicCalculus a,
    ⟨holomorphicCalculus_id a, fun U ha => by
      have h : (holomorphicCalculus a).comp (toGerm ha) = holomorphicCalculusOn a U ha := by
        ext f
        exact holomorphicCalculus_toGerm a U ha f
      rw [h]
      exact continuous_holomorphicCalculusOn a U ha⟩,
    fun _ ⟨hΦ_id, hΦ_cont⟩ => eq_holomorphicCalculus a hΦ_id hΦ_cont⟩

end Uniqueness

/-! ### Composition theorem -/

section Composition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Evaluating a holomorphic germ `φ` at any spectral value of `a` produces a spectral value of
`holomorphicCalculus a φ`. -/
theorem eval_mem_spectrum_holomorphicCalculus (a : A) (φ : holomorphicGerms (spectrum ℂ a))
    (z : ℂ) (hz : z ∈ spectrum ℂ a) :
    holomorphicGerms.eval z hz φ ∈ spectrum ℂ (holomorphicCalculus a φ) := by
  rw [spectrum_holomorphicCalculus]
  exact ⟨z, hz, rfl⟩

/-- **Composition theorem for holomorphic germs:** `ψ(φ(a)) = (ψ ∘ φ)(a)` for any
`φ : holomorphicGerms (spectrum ℂ a)` and
`ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))`. -/
theorem holomorphicCalculus_comp (a : A) (φ : holomorphicGerms (spectrum ℂ a))
    (ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))) :
    holomorphicCalculus (holomorphicCalculus a φ) ψ =
      holomorphicCalculus a
        (holomorphicGerms.compAlgHom φ (eval_mem_spectrum_holomorphicCalculus a φ) ψ) := by
  let b := holomorphicCalculus a φ
  have hφ := eval_mem_spectrum_holomorphicCalculus a φ
  let Ψ : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A :=
    (holomorphicCalculus a).comp (holomorphicGerms.compAlgHom φ hφ)
  have hΨ_id : Ψ (holomorphicGerms.ofFun id analyticOnNhd_id) = b := by
    simp [Ψ, b]
  have hΨ_cont : ∀ (V : Opens ℂ) (hb : spectrum ℂ b ⊆ V), Continuous (Ψ.comp (toGerm hb)) := by
    intro V hb
    obtain ⟨U, haU, f, hfφ⟩ := holomorphicGerms.exists_toGerm_eq φ
    obtain ⟨U', haU', hU'U, hfV⟩ := exists_opens_mapsTo haU f V fun z hz => by
      rw [← eval_toGerm haU z hz f, hfφ]
      exact hb (hφ z hz)
    have hcomp :
        Ψ.comp (toGerm hb) =
          (holomorphicCalculusOn a U' haU').comp (compAlgHom (restrict hU'U f) hfV) := by
      ext g
      simp only [Ψ, AlgHom.comp_apply]
      rw [holomorphicGerms.compAlgHom_toGerm φ hφ haU f hfφ hb g haU' hU'U hfV,
        holomorphicCalculus_toGerm]
    rw [hcomp]
    exact (continuous_holomorphicCalculusOn a U' haU').comp (continuous_compAlgHom _ hfV)
  have hΨ : Ψ = holomorphicCalculus b := eq_holomorphicCalculus b hΨ_id hΨ_cont
  exact (congrArg (fun H : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A => H ψ) hΨ).symm

/-- **Composition theorem for analytic representatives:** if `f` is analytic near `spectrum ℂ a`
and maps `spectrum ℂ a` into `t`, and `g` is analytic near `t`, then `g(f(a)) = (g ∘ f)(a)`. -/
theorem holomorphicCalculus_ofFun_comp (a : A) {t : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hft : MapsTo f (spectrum ℂ a) t)
    (hg : AnalyticOnNhd ℂ g t) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
        (holomorphicGerms.ofFun g
          (hg.mono (by rw [spectrum_holomorphicCalculus_ofFun]; exact image_subset_iff.2 hft))) =
      holomorphicCalculus a (holomorphicGerms.ofFun (g ∘ f) (hg.comp hf hft)) := by
  rw [holomorphicCalculus_comp, holomorphicGerms.compAlgHom_ofFun]

/-- **Composition theorem on open neighbourhoods:** if `f ∈ O(U)` (`σ(a) ⊆ U`), `g ∈ O(V)`
(`σ(f(a)) ⊆ V`), and `U' ≤ U` is an open neighbourhood of `σ(a)` mapped by `f` into `V`, then
`holomorphicCalculusOn (holomorphicCalculusOn a U haU f) V hbV g` agrees with
`holomorphicCalculusOn a U' haU'` applied to `g ∘ (f|_{U'})`. -/
theorem holomorphicCalculusOn_comp (a : A) {U V U' : Opens ℂ} (haU : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hbV : spectrum ℂ (holomorphicCalculusOn a U haU f) ⊆ V)
    (g : holomorphicFunctions V) (haU' : spectrum ℂ a ⊆ U') (hU'U : U' ≤ U)
    (hfV : ∀ z : U', (restrict hU'U f).val z ∈ V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U haU f) V hbV g =
      holomorphicCalculusOn a U' haU' (compAlgHom (restrict hU'U f) hfV g) := by
  have key : ∀ (b : A) (hb : b = holomorphicCalculus a (toGerm haU f))
      (hbV : spectrum ℂ b ⊆ V),
      holomorphicCalculusOn b V hbV g =
        holomorphicCalculus a
          (holomorphicGerms.compAlgHom (toGerm haU f)
            (eval_mem_spectrum_holomorphicCalculus a (toGerm haU f))
            (toGerm (hb ▸ hbV) g)) := by
    rintro _ rfl hbV
    rw [← holomorphicCalculus_toGerm, holomorphicCalculus_comp]
  rw [key _ (holomorphicCalculus_toGerm a U haU f).symm hbV,
    holomorphicGerms.compAlgHom_toGerm (toGerm haU f)
      (eval_mem_spectrum_holomorphicCalculus a (toGerm haU f)) haU f rfl _ g haU' hU'U hfV,
    holomorphicCalculus_toGerm]

end Composition

end TauCeti
