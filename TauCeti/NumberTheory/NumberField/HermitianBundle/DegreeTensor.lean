/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree
public import TauCeti.NumberTheory.NumberField.HermitianBundle.TensorProduct
public import TauCeti.RingTheory.PicardGroup.CardQuot
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Arakelov degree of a tensor product of hermitian lines

For hermitian metrics `h` on `E` and `h'` on `F` over the ring of integers `𝓞 K` of a number
field, with `E` flat and `F` invertible, the degree of `E ⊗ F` computed with a pure tensor
`s ⊗ t` of nonzero sections is the sum of the degrees computed with `s` and with `t`
(`TauCeti.HermitianMetric.sectionDegree_tmul`):

`deg(s ⊗ t) = deg(s) + deg(t)`.

Both terms of the degree are additive: the norms by `‖s ⊗ t‖_σ = ‖s‖_σ ‖t‖_σ`
(`TauCeti.HermitianMetric.norm_tmul_tmul`), and the lattice index by
`#((E ⊗ F) / 𝓞 K (s ⊗ t)) = #(E / 𝓞 K s) · #(F / 𝓞 K t)` (`Submodule.cardQuot_span_tmul`). For
hermitian line bundles this is `deg(L ⊗ M) = deg L + deg M`, the additivity of the Arakelov degree
on tensor products of the roadmap ArakelovGeometryAndAbelianHeights, §1.5.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- **The degree is additive on tensor products of hermitian lines.** For `E` flat and `F`
invertible, and nonzero sections `s` of `E` and `t` of `F` spanning sublattices of finite index,
the degree of `E ⊗ F` computed with `s ⊗ t` is the degree of `E` computed with `s` plus the degree
of `F` computed with `t`. -/
theorem sectionDegree_tmul [Module.Flat (𝓞 K) E] [Module.Invertible (𝓞 K) F] {s : E}
    (hs : s ≠ 0) {t : F} (ht : t ≠ 0) [Finite (E ⧸ Submodule.span (𝓞 K) {s})]
    [Finite (F ⧸ Submodule.span (𝓞 K) {t})] :
    (h.tmul h').sectionDegree (s ⊗ₜ t) = h.sectionDegree s + h'.sectionDegree t := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton (𝓞 K) E s) := by
    refine (injective_iff_map_eq_zero _).2 fun r hr ↦ ?_
    rw [LinearMap.toSpanSingleton_apply] at hr
    exact (smul_eq_zero.1 hr).resolve_right hs
  -- Both lattice indices are nonzero, since the quotients are finite and nonempty.
  have hcs : ((Submodule.span (𝓞 K) {s}).cardQuot : ℝ) ≠ 0 := Nat.cast_ne_zero.2
    ((Submodule.cardQuot_apply _).trans_ne (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩))
  have hct : ((Submodule.span (𝓞 K) {t}).cardQuot : ℝ) ≠ 0 := Nat.cast_ne_zero.2
    ((Submodule.cardQuot_apply _).trans_ne (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩))
  have hsσ (σ : K →+* ℂ) : h.norm σ (1 ⊗ₜ s) ≠ 0 :=
    (h.norm_pos (Codomain.one_tmul_ne_zero σ hs)).ne'
  have htσ (σ : K →+* ℂ) : h'.norm σ (1 ⊗ₜ t) ≠ 0 :=
    (h'.norm_pos (Codomain.one_tmul_ne_zero σ ht)).ne'
  simp only [sectionDegree_def, norm_tmul_tmul, Submodule.cardQuot_span_tmul hinj t,
    Nat.cast_mul]
  rw [Real.log_mul hcs hct]
  simp only [Real.log_mul (hsσ _) (htσ _), Finset.sum_add_distrib]
  ring

end TauCeti.HermitianMetric
