/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Algebra

/-!
# Pullback of holomorphic germs

Any holomorphic germ `g : holomorphicGerms s` whose spectrum `spectrum ℂ g` (its set of values on
`s`) is contained in `t` tends along `𝓝ˢ s` to `𝓝ˢ t` and therefore induces a contravariant
pullback algebra homomorphism `holomorphicGerms.comap g hg : holomorphicGerms t →ₐ[ℂ]
holomorphicGerms s` via `Filter.Germ.compTendsto'`.

This pullback agrees with ordinary composition on represented analytic functions (`comap_ofFun`),
commutes with point evaluation and set restriction on both sides, identifies the spectrum of a
pulled-back germ with that of the restricted outer germ (`spectrum_comap`), and is functorial under
iterated pullback (`comap_comap`). These operations provide the germ-level input to the composition
theorem for the holomorphic functional calculus.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology

namespace TauCeti.holomorphicGerms

variable {r s t u : Set ℂ}

private theorem germ_tendsto_nhdsSet (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t) :
    g.val.Tendsto (𝓝ˢ t) := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rw [coe_ofFun, Germ.coe_tendsto]
  exact ContinuousOn.tendsto_nhdsSet (s' := {z | AnalyticAt ℂ f z})
    (fun _ hz ↦ hz.continuousAt.continuousWithinAt)
    ((isOpen_analyticAt ℂ f).mem_nhdsSet.mpr hf)
    (mapsTo_iff_image_subset.mpr ((spectrum_ofFun f hf).symm ▸ hg))

/-- Contravariant pullback of holomorphic germs near `t` along a holomorphic germ `g` near `s`
whose spectrum is contained in `t`. -/
def comap (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t) :
    holomorphicGerms t →ₐ[ℂ] holomorphicGerms s :=
  ((Germ.compTendsto'AlgHom (R := ℂ) g.val (germ_tendsto_nhdsSet g hg)).comp
    (holomorphicGerms t).val).codRestrict (holomorphicGerms s) fun k ↦ by
    obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
    rw [AlgHom.comp_apply, Subalgebra.coe_val, Germ.compTendsto'AlgHom_apply, coe_ofFun,
      Germ.coe_compTendsto']
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    rw [coe_ofFun, Germ.map_coe]
    exact coe_mem_holomorphicGerms_iff.mpr
      (hψ.comp hf (mapsTo_iff_image_subset.mpr ((spectrum_ofFun f hf).symm ▸ hg)))

/-- Pulling back germs along equal inner germs gives the same algebra homomorphism regardless of
the spectrum-inclusion proof. -/
theorem comap_congr_left {g₁ g₂ : holomorphicGerms s} (h : g₁ = g₂)
    {hg₁ : spectrum ℂ g₁ ⊆ t} {hg₂ : spectrum ℂ g₂ ⊆ t} :
    comap g₁ hg₁ = comap g₂ hg₂ := by
  subst h
  rfl

/-- Germ pullback on ambient analytic functions is ordinary function composition. -/
@[simp]
theorem comap_ofFun {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hg : spectrum ℂ (ofFun f hf) ⊆ t) (ψ : ℂ → ℂ) (hψ : AnalyticOnNhd ℂ ψ t) :
    comap (ofFun f hf) hg (ofFun ψ hψ) =
      ofFun (ψ ∘ f)
        (hψ.comp hf (mapsTo_iff_image_subset.mpr ((spectrum_ofFun f hf).symm ▸ hg))) := by
  apply Subtype.ext
  rw [comap, AlgHom.coe_codRestrict, AlgHom.comp_apply, Subalgebra.coe_val,
    Germ.compTendsto'AlgHom_apply, coe_ofFun ψ hψ, Germ.coe_compTendsto', coe_ofFun, coe_ofFun,
    Germ.map_coe]

/-- Pulling back the coordinate germ along `g` recovers `g`. -/
@[simp]
theorem comap_ofFun_id (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t) :
    comap g hg (ofFun id analyticOnNhd_id) = g := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rw [comap_ofFun]
  simp only [Function.id_comp]

/-- Evaluating a pulled-back germ at a point of `s` evaluates the outer germ at `eval x hx g`. -/
@[simp]
theorem eval_comap (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) (x : ℂ) (hx : x ∈ s) :
    eval x hx (comap g hg k) =
      eval (eval x hx g) (hg (by rw [spectrum_eq]; exact ⟨x, hx, rfl⟩)) k := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  simp

/-- Pulling back a restricted germ is pullback along the ambient inclusion. -/
@[simp]
theorem comap_restrict (htu : t ⊆ u) (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms u) :
    comap g hg (restrict htu k) = comap g (hg.trans htu) k := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  simp

/-- Restricting a pulled-back germ to a subset `r ⊆ s` is pullback along the restricted inner
germ. -/
@[simp]
theorem restrict_comap (hrs : r ⊆ s) (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) :
    restrict hrs (comap g hg k) =
      comap (restrict hrs g) ((AlgHom.spectrum_apply_subset (restrict hrs) g).trans hg) k := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  simp

/-- Pulling back germs along the coordinate germ on `s` is the identity algebra homomorphism. -/
@[simp]
theorem comap_id (hg : spectrum ℂ (ofFun id (analyticOnNhd_id (s := s))) ⊆ s) :
    comap (ofFun id analyticOnNhd_id) hg = AlgHom.id ℂ (holomorphicGerms s) := by
  refine AlgHom.ext fun k ↦ ?_
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  rw [comap_ofFun]
  simp only [Function.comp_id, AlgHom.id_apply]

/-- The spectrum of `comap g hg k` equals the spectrum of `k` restricted to `spectrum ℂ g`. -/
theorem spectrum_comap (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) :
    spectrum ℂ (comap g hg k) = spectrum ℂ (restrict hg k) := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  rw [comap_ofFun, restrict_ofFun, spectrum_ofFun, spectrum_ofFun, spectrum_ofFun, Set.image_comp]

/-- Contravariant pullback of holomorphic germs is functorial under composition. -/
@[simp]
theorem comap_comap (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) (hk : spectrum ℂ k ⊆ u) (m : holomorphicGerms u) :
    comap g hg (comap k hk m) =
      comap (comap g hg k) ((AlgHom.spectrum_apply_subset (comap g hg) k).trans hk) m := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  obtain ⟨θ, hθ, rfl⟩ := exists_ofFun_eq m
  simp [Function.comp_def]

end TauCeti.holomorphicGerms
