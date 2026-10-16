/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Transfer

/-!
# The continuous functional calculus of a closed star subalgebra

Let `B` be a Banach `⋆`-algebra over `𝕜 = ℝ` or `ℂ` carrying a continuous functional calculus
for the elements satisfying a predicate `q`, and let `S` be a closed star subalgebra of `B`.
Mathlib's `cfc_mem` says that `cfc f x` lies in `S` whenever `x` does. This file draws the two
consequences of that fact.

* **Spectral permanence.** For `x ∈ S` with `q x`, the spectrum of `x` in `S` equals its
  spectrum in `B` (`StarSubalgebra.spectrum_eq_of_predicate`): if `r - x` is invertible in `B`,
  its inverse is `cfc (fun t ↦ (r - t)⁻¹) x`, which lies in `S`. This needs no norm on `B`.
* **The calculus restricts.** `S` carries a continuous functional calculus for the elements
  satisfying `q` in `B` (`StarSubalgebra.continuousFunctionalCalculus`), computed by the
  calculus of `B` (`StarSubalgebra.coe_cfc`).

Transferring the second statement along a star algebra isomorphism onto the range gives the form
used in practice: a unital `⋆`-homomorphism `φ : A →⋆ₐ[𝕜] B` that is a closed embedding pulls the
continuous functional calculus of `B` back to `A`
(`StarAlgHom.continuousFunctionalCalculus_of_isClosedEmbedding`), and then commutes with it
(`StarAlgHom.map_cfc`). The motivating instance is a real `C⋆`-algebra embedded isometrically in
a complex one, such as the bounded operators on a real Hilbert space inside the bounded operators
on its complexification: the self-adjoint elements of the real algebra acquire a real continuous
functional calculus, which Mathlib constructs only for complex `C⋆`-algebras.

Mathlib's `StarSubalgebra.spectrum_eq` is the analogous spectral permanence statement for closed
complex star subalgebras of a complex `C⋆`-algebra, where it holds for every element. Here only the
calculus of `B` is used, so the statement covers real subalgebras, but it is restricted to the
elements on which that calculus is defined.

## Main declarations

* `StarSubalgebra.spectrum_eq_of_predicate`: spectral permanence for the elements of a closed star
  subalgebra satisfying the predicate of the calculus.
* `StarSubalgebra.continuousFunctionalCalculus`: a closed star subalgebra inherits the continuous
  functional calculus.
* `StarSubalgebra.coe_cfc`: the inherited calculus is computed in the ambient algebra.
* `StarAlgHom.spectrum_apply_eq_of_isClosedEmbedding`: spectral permanence along a closed
  embedding of `⋆`-algebras.
* `StarAlgHom.continuousFunctionalCalculus_of_isClosedEmbedding`: a closed embedding of
  `⋆`-algebras pulls the continuous functional calculus back.
-/

public section

open Topology

section Spectrum

variable {𝕜 B : Type*} {q : B → Prop} [RCLike 𝕜] [Ring B] [StarRing B] [Algebra 𝕜 B]
  [TopologicalSpace B] [IsTopologicalRing B] [StarModule 𝕜 B] [ContinuousStar B]
  [ContinuousFunctionalCalculus 𝕜 B q]

namespace StarSubalgebra

/-- **Spectral permanence** for a closed star subalgebra `S`: an element `x ∈ S` on which the
continuous functional calculus of the ambient algebra is defined has the same spectrum in `S` as
in the ambient algebra. -/
theorem spectrum_eq_of_predicate (S : StarSubalgebra 𝕜 B) [IsClosed (S : Set B)] {x : S}
    (hx : q x) : spectrum 𝕜 x = spectrum 𝕜 (x : B) := by
  refine (Set.Subset.antisymm (spectrum.subset_subalgebra x) fun r hr ↦ ?_).symm
  contrapose! hr
  have hne : ∀ t ∈ spectrum 𝕜 (x : B), r - t ≠ 0 := fun t ht h ↦ hr (sub_eq_zero.1 h ▸ ht)
  rw [spectrum.notMem_iff] at hr ⊢
  let u := cfcUnits (fun t ↦ r - t) (x : B) hne
  have hu : (u : B) = algebraMap 𝕜 B r - x := by
    simp only [u, val_cfcUnits]
    rw [cfc_sub (fun _ ↦ r) (fun t ↦ t) (x : B), cfc_const r (x : B) hx, cfc_id' 𝕜 (x : B) hx]
  have hmem : ((u⁻¹ : Bˣ) : B) ∈ S := cfc_mem (𝕜' := 𝕜) _ x.2
  refine ⟨⟨algebraMap 𝕜 S r - x, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩ <;> ext
  · simp [hu]
  · simp [hu]

end StarSubalgebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra 𝕜 A] [TopologicalSpace A]

/-- **Spectral permanence** along a unital `⋆`-homomorphism `φ` which is a closed embedding: if the
continuous functional calculus of `B` is defined at `φ a`, then `φ a` has the same spectrum as
`a`. -/
theorem StarAlgHom.spectrum_apply_eq_of_isClosedEmbedding (φ : A →⋆ₐ[𝕜] B)
    (hφ : IsClosedEmbedding φ) {a : A} (ha : q (φ a)) : spectrum 𝕜 (φ a) = spectrum 𝕜 a := by
  have : IsClosed (φ.range : Set B) := hφ.isClosed_range
  let e := StarAlgEquiv.ofInjective φ hφ.injective
  rw [← AlgEquiv.spectrum_eq e a]
  exact (φ.range.spectrum_eq_of_predicate (x := e a) ha).symm

end Spectrum

section Banach

variable {𝕜 A B : Type*} {p : A → Prop} {q : B → Prop} [RCLike 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕜 A] [TopologicalSpace A]
  [NormedRing B] [StarRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarModule 𝕜 B]
  [ContinuousStar B] [ContinuousFunctionalCalculus 𝕜 B q]

namespace StarSubalgebra

variable (S : StarSubalgebra 𝕜 B) [hS : IsClosed (S : Set B)]

/-- A closed star subalgebra `S` inherits the continuous functional calculus of the ambient
algebra, for the elements satisfying the same predicate there: the calculus of `x ∈ S` is the
ambient calculus of `x`, which takes values in `S` by `cfc_mem`. -/
theorem continuousFunctionalCalculus : ContinuousFunctionalCalculus 𝕜 S (fun x ↦ q x) where
  predicate_zero := by simpa using ContinuousFunctionalCalculus.predicate_zero (R := 𝕜) (A := B)
  compactSpace_spectrum x := by
    have : CompleteSpace S := hS.completeSpace_coe
    exact isCompact_iff_compactSpace.1 (spectrum.isCompact x)
  spectrum_nonempty x hx := by
    have : Nontrivial B := Function.Injective.nontrivial (f := ((↑) : S → B)) Subtype.val_injective
    rw [S.spectrum_eq_of_predicate hx]
    exact ContinuousFunctionalCalculus.spectrum_nonempty _ hx
  exists_cfc_of_predicate x hx := by
    have hsp := S.spectrum_eq_of_predicate hx
    let e : C(spectrum 𝕜 x, 𝕜) →⋆ₐ[𝕜] C(spectrum 𝕜 (x : B), 𝕜) :=
      ContinuousMap.compStarAlgHom' 𝕜 𝕜 ⟨Set.inclusion hsp.symm.subset, by fun_prop⟩
    have he : Function.Injective e := fun f g hfg ↦ by
      ext ⟨t, ht⟩
      simpa [e] using congr($hfg ⟨t, hsp ▸ ht⟩)
    have hmem (f) : cfcHom hx (e f) ∈ S := by
      simpa [cfcHom_eq_cfc_extend 0 hx] using cfc_mem (𝕜' := 𝕜) _ x.2
    let ψ := ((cfcHom hx).comp e).codRestrict S hmem
    have hψ (f) : (ψ f : B) = cfcHom hx (e f) := StarAlgHom.coe_codRestrict _ S hmem f
    refine ⟨ψ, ?_, ?_, ?_, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ((cfcHom_continuous hx).comp (ContinuousMap.continuous_precomp _)).subtype_mk _
    · exact (StarAlgHom.injective_codRestrict _ _ _).2 ((cfcHom_injective hx).comp he)
    · exact Subtype.ext ((hψ _).trans (cfcHom_id hx))
    · have hf : q (ψ f : B) := (hψ f).symm ▸ cfcHom_predicate hx _
      rw [S.spectrum_eq_of_predicate hf, hψ, cfcHom_map_spectrum]
      ext t
      exact ⟨fun ⟨s, hs⟩ ↦ ⟨_, hs⟩, fun ⟨s, hs⟩ ↦ ⟨⟨s, hsp ▸ s.2⟩, hs⟩⟩
    · exact (hψ f).symm ▸ cfcHom_predicate hx _

/-- The continuous functional calculus that a closed star subalgebra inherits is computed in the
ambient algebra. -/
@[simp]
theorem coe_cfc [ContinuousMap.UniqueHom 𝕜 B] (f : 𝕜 → 𝕜) (x : S) :
    letI := S.continuousFunctionalCalculus
    ((cfc f x : S) : B) = cfc f (x : B) := by
  let := S.continuousFunctionalCalculus
  by_cases hx : q x
  · by_cases hf : ContinuousOn f (spectrum 𝕜 x)
    · exact S.subtype.map_cfc f x hf continuous_subtype_val hx hx
    · rw [cfc_apply_of_not_continuousOn _ hf,
        cfc_apply_of_not_continuousOn _ (by rwa [← S.spectrum_eq_of_predicate hx]),
        ZeroMemClass.coe_zero]
  · rw [cfc_apply_of_not_predicate (p := fun x : S ↦ q x) _ hx,
      cfc_apply_of_not_predicate _ hx, ZeroMemClass.coe_zero]

end StarSubalgebra

/-- A unital `⋆`-homomorphism `φ : A →⋆ₐ[𝕜] B` which is a closed embedding pulls the continuous
functional calculus of `B` back to `A`, for elements `a` such that `φ a` satisfies the predicate
of the calculus of `B`. The calculus of `A` is then intertwined with that of `B` by
`StarAlgHom.map_cfc`. -/
theorem StarAlgHom.continuousFunctionalCalculus_of_isClosedEmbedding (φ : A →⋆ₐ[𝕜] B)
    (hφ : IsClosedEmbedding φ) (hpq : ∀ a, p a ↔ q (φ a)) : ContinuousFunctionalCalculus 𝕜 A p :=
  have : IsClosed (φ.range : Set B) := hφ.isClosed_range
  have := φ.range.continuousFunctionalCalculus
  let e := StarAlgEquiv.ofInjective φ hφ.injective
  have he (y : φ.range) : φ (e.symm y) = y := congr_arg Subtype.val (e.apply_symm_apply y)
  .transfer e.symm (hφ.isInducing.continuous_iff.2 <| by
      simpa [Function.comp_def, he] using continuous_subtype_val)
    fun y ↦ by rw [hpq, he]

end Banach
