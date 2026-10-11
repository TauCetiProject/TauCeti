/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Factors of a product diffeomorphism

If a diffeomorphism between nonempty products has underlying map `Prod.map f g`, then
both `f` and `g` are diffeomorphisms. No smoothness of the factor maps or their inverses
is assumed: each is recovered as a slice of the product diffeomorphism or its inverse.
This lets one promote separation of a smooth map into separation by bundled equivalences.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- The factors of a diffeomorphism whose underlying map separates are themselves
`C^n` diffeomorphisms. Nonemptiness excludes an empty product hiding an arbitrary factor. -/
theorem exists_factors_of_eq_prodMap
    (Q : (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ (M' × N'))
    [Nonempty M] [Nonempty N] (f : M → M') (g : N → N')
    (hQ : ⇑Q = Prod.map f g) :
    ∃ (φ : M ≃ₘ^n⟮I, I'⟯ M') (ψ : N ≃ₘ^n⟮J, J'⟯ N'), ⇑φ = f ∧ ⇑ψ = g := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  have hbij : Function.Bijective (Prod.map f g) := hQ ▸ Q.bijective
  obtain ⟨hf, hg⟩ := Prod.map_bijective.mp hbij
  let e := Equiv.ofBijective f hf
  let d := Equiv.ofBijective g hg
  have hleft : ∀ u, e.symm u = (Q.symm (u, g y₀)).1 := by
    intro u
    apply e.injective
    have h := congrArg Prod.fst (Q.apply_symm_apply (u, g y₀))
    simpa only [hQ, Prod.map_fst, Equiv.apply_symm_apply, Equiv.ofBijective_apply, e] using h.symm
  have hright : ∀ v, d.symm v = (Q.symm (f x₀, v)).2 := by
    intro v
    apply d.injective
    have h := congrArg Prod.snd (Q.apply_symm_apply (f x₀, v))
    simpa only [hQ, Prod.map_snd, Equiv.apply_symm_apply, Equiv.ofBijective_apply, d] using h.symm
  have hfd : ContMDiff I I' n f := by
    have h := (Q.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := y₀)))).fst
    simpa only [hQ, Function.comp_def, Prod.map_fst, id_eq] using h
  have hgd : ContMDiff J J' n g := by
    have h := (Q.contMDiff.comp ((contMDiff_const (c := x₀)).prodMk contMDiff_id)).snd
    simpa only [hQ, Function.comp_def, Prod.map_snd, id_eq] using h
  have he : ContMDiff I' I n e.symm := by
    have h := (Q.symm.contMDiff.comp
      (contMDiff_id.prodMk (contMDiff_const (c := g y₀)))).fst
    exact h.congr hleft
  have hd : ContMDiff J' J n d.symm := by
    have h := (Q.symm.contMDiff.comp
      ((contMDiff_const (c := f x₀)).prodMk contMDiff_id)).snd
    exact h.congr hright
  exact ⟨⟨e, hfd, he⟩, ⟨d, hgd, hd⟩, rfl, rfl⟩

end Diffeomorph
