/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold

/-!
# Smooth affine actions on a family of tori

For a `C^n` family of full period lattices `P : Y → (Λ →ₗ[ℤ] E)`, fibrewise translation
`v +ᵥ [y, w] = [y, v + w]` is jointly `C^n` for the quotient atlas on `(Y × E)/Λ`
(`TauCeti.contMDiffVAdd_torusFamilyTranslationAddAction`). Consequently the affine map
`[y, v] ↦ R g y v +ᵥ b g y` is `C^n` whenever the evaluation `(y, v) ↦ R g y v` and the
section `b g` are `C^n` (`TauCeti.contMDiff_torusFamilyAffineMap`). The section is valued in
the torus family itself: it is not required to admit a global vector-space lift.

For cocycles defining an action, `TauCeti.contMDiffConstSMul_torusFamilyAffineMulAction`
provides Mathlib's pointwise regularity class. For a group, installing this class makes
`Diffeomorph.constSmul` available, with inverse given by the inverse group element. In particular,
over `ℂ` with holomorphic periods, linear-part evaluations and translation sections, every
affine action map is biholomorphic. No freeness of the action on the base is required.

The regularity statements use any normed scalar field `𝕜`; the real structure of `E` is used
only for the full-lattice hypotheses. Smoothness is checked before taking the period quotient,
using its surjective local diffeomorphism, rather than through a real period frame (which need
not be holomorphic).

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- Fibrewise translation is jointly `C^n` for the quotient manifold structure of a `C^n`
family of full lattices. For holomorphic periods over `ℂ`, it is jointly holomorphic. -/
theorem contMDiffVAdd_torusFamilyTranslationAddAction :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyTranslationAddAction P
    ContMDiffVAdd 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n E
      (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyTranslationAddAction P
  have hq := isLocalDiffeomorph_torusFamily_mk P hinj hP
  refine ⟨(hq.contMDiff_comp_prodMap_iff Quotient.mk_surjective le_rfl).1 ?_⟩
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Pi.add_apply,
    torusFamilyTranslationAddAction_vadd_mk] using
    hq.contMDiff.comp (contMDiff_snd.fst.prodMk (contMDiff_fst.add contMDiff_snd.snd))

section Affine

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- The affine map of `g` is `C^n` if its linear-part evaluation and its torus-valued translation
section are `C^n`. No global vector-space lift of the section is needed. -/
theorem contMDiff_torusFamilyAffineMap {g : Γ}
    (hR : ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (torusFamilyAffineMap R P ρ hequiv b hb g) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyTranslationAddAction P
  have := contMDiffVAdd_torusFamilyTranslationAddAction P hinj hP
  refine ((isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl).1 ?_
  simpa only [Function.comp_def, torusFamilyAffineMap_mk] using
    (contMDiff_vadd (I := 𝓘(𝕜, E)) (I' := I.prod 𝓘(𝕜, E))).comp
      (hR.prodMk (hbc.comp contMDiff_fst))

variable (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- A `C^n` affine cocycle acts by `C^n` maps on the torus family. For a group, this class
also supplies `C^n` inverses through `Diffeomorph.constSmul`; over `ℂ` with holomorphic data,
these are biholomorphisms. Neither a free base action nor global vector lifts are required. -/
theorem contMDiffConstSMul_torusFamilyAffineMulAction
    (hR : ∀ g : Γ,
      ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    ContMDiffConstSMul (I.prod 𝓘(𝕜, E)) n Γ
      (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  refine ⟨fun g ↦ ?_⟩
  simpa only [torusFamilyAffineMulAction_smul] using
    contMDiff_torusFamilyAffineMap P hinj hP R ρ hequiv b hb (hR g) (hbc g)

end Affine

end TauCeti
