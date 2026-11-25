/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Basic
public import TauCeti.NumberTheory.NumberField.HermitianBundle.TensorProduct
public import TauCeti.RingTheory.PicardGroup.CardQuot
public import TauCeti.Algebra.Module.Torsion.GenericRankOne
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
`#((E ⊗ F) / 𝓞 K (s ⊗ t)) = #(E / 𝓞 K s) · #(F / 𝓞 K t)`
(`Submodule.cardQuot_span_singleton_tmul`).
Together with the independence of the degree from the chosen section, this gives the additivity
`deg(L ⊗ M) = deg L + deg M` of the Arakelov degree on tensor products of hermitian line bundles.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- **The degree is additive on tensor products of hermitian lines.** For `E` flat and `F`
invertible, a nonzero section `s` of `E` spanning a sublattice of finite index and a nonzero
section `t` of `F`, the degree of `E ⊗ F` computed with `s ⊗ t` is the degree of `E` computed
with `s` plus the degree of `F` computed with `t`. -/
theorem sectionDegree_tmul [Module.Flat (𝓞 K) E] [Module.Invertible (𝓞 K) F] {s : E}
    (hs : s ≠ 0) {t : F} (ht : t ≠ 0) [Finite (E ⧸ Submodule.span (𝓞 K) {s})] :
    (h.tmul h').sectionDegree (s ⊗ₜ t) = h.sectionDegree s + h'.sectionDegree t := by
  -- `F` is a line, so `t` spans a sublattice of finite index.
  have : Finite (F ⧸ Submodule.span (𝓞 K) {t}) :=
    Module.finite_quotient_span_singleton_of_finrank_eq_one (F := K)
      (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] F)) ht
  have hinj : Function.Injective (LinearMap.toSpanSingleton (𝓞 K) E s) :=
    smul_left_injective (𝓞 K) hs
  -- Both lattice indices are nonzero, since the quotients are finite.
  have hcs : ((Submodule.span (𝓞 K) {s}).cardQuot : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Submodule.cardQuot_ne_zero _)
  have hct : ((Submodule.span (𝓞 K) {t}).cardQuot : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Submodule.cardQuot_ne_zero _)
  have hsσ (σ : K →+* ℂ) : h.norm σ (1 ⊗ₜ s) ≠ 0 :=
    (h.norm_pos (Codomain.one_tmul_ne_zero σ hs)).ne'
  have htσ (σ : K →+* ℂ) : h'.norm σ (1 ⊗ₜ t) ≠ 0 :=
    (h'.norm_pos (Codomain.one_tmul_ne_zero σ ht)).ne'
  simp only [sectionDegree_def, norm_tmul_tmul, Submodule.cardQuot_span_singleton_tmul hinj t,
    Nat.cast_mul]
  rw [Real.log_mul hcs hct]
  simp only [Real.log_mul (hsσ _) (htσ _), Finset.sum_add_distrib]
  ring

end TauCeti.HermitianMetric
