/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Arakelov.HermitianVectorBundle

/-!
# The lattice index term of the Arakelov degree

Let `E ⊆ F` be hermitian vector bundles over `Spec 𝓞 K` with the same metrics, given by an
`𝓞 K`-linear map `f : E → F` preserving the norms at every embedding `σ : K →+* ℂ`. For a
section `s` of `E`, `#(F / 𝓞 K • f s) = #(F / f E) · #(E / 𝓞 K • s)`, so the degree of `F`
computed with `f s` is the degree of `E` computed with `s` plus `log #(F / f E)`.

## Main statements

* `TauCeti.HermitianVectorBundle.sectionDegree_map_eq_add_log_cardQuot_range`: the lattice
  index term `deg F = deg E + log #(F / E)`, computed with a common section.
* `TauCeti.HermitianVectorBundle.sectionDegree_rescale_trivial_log_two_two`: for `ℤ ⊂ ½ ℤ` with
  the absolute value metric, the degree of `½ ℤ` is `log 2`.

## References

* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616
  (1983/84), §2.1, p. 36.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.2, Corollaire, p. 14.
* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795 (1994/95), Appendice A.3, p. 147.
-/

public noncomputable section

open NumberField

namespace TauCeti.HermitianVectorBundle

variable {K : Type*} [Field K] [NumberField K] {E F : HermitianVectorBundle K}

/-- Lattice index term: let `f : E → F` be an `𝓞 K`-linear map preserving the norms at every
embedding, so that `E` is a sublattice of `F` with the same metrics. For a section `s` of `E`
generating a sublattice of finite index, and `F / f E` finite, the degree of `F` computed with
`f s` is the degree of `E` computed with `s` plus `log #(F / f E)`. -/
theorem sectionDegree_map_eq_add_log_cardQuot_range (f : E →ₗ[𝓞 K] F)
    (hnorm : ∀ σ x, F.norm σ (f x) = E.norm σ x) (s : E)
    [Finite (E ⧸ Submodule.span (𝓞 K) {s})] [Finite (F ⧸ LinearMap.range f)] :
    F.sectionDegree (f s) = E.sectionDegree s + Real.log (LinearMap.range f).cardQuot := by
  have hf : Function.Injective f := by
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra h
    exact (E.norm_pos σ h).ne' (by rw [← hnorm σ, hx, HermitianVectorBundle.norm_zero])
  rw [sectionDegree_eq_sectionDegreeOfNorms, sectionDegree_eq_sectionDegreeOfNorms]
  exact sectionDegreeOfNorms_map_eq_add_log_cardQuot_range f hf hnorm s

/-- The lattices `ℤ ⊂ ½ ℤ` with the absolute value metric, modelled as multiplication by `2` from
`Ō_ℚ` to `Ō_ℚ(log 2)`, whose norm is `|x| / 2`: the degree of `½ ℤ` computed with the section `1`
(the element `2` of `Ō_ℚ(log 2)`) is `log 2 = 0 + log #((½ ℤ) / ℤ)`. -/
theorem sectionDegree_rescale_trivial_log_two_two :
    ((trivial ℚ).rescale (Real.log 2)).sectionDegree (show 𝓞 ℚ from 2) = Real.log 2 := by
  let g : 𝓞 ℚ →ₗ[𝓞 ℚ] 𝓞 ℚ := (2 : 𝓞 ℚ) • LinearMap.id
  -- The carriers of `trivial ℚ` and of its rescaling are `𝓞 ℚ` by definition, with the same
  -- module structure, so `g` is also a map between the two bundles.
  let f : trivial ℚ →ₗ[𝓞 ℚ] (trivial ℚ).rescale (Real.log 2) := g
  have hrange : LinearMap.range g = Ideal.span {(2 : 𝓞 ℚ)} := by
    ext x
    simp [g, Ideal.mem_span_singleton', eq_comm, mul_comm]
  have hcard : (LinearMap.range f).cardQuot = 2 := by
    -- `f` is `g` at the bundle types, so `rw [hrange]` cannot match `LinearMap.range f`;
    -- `change` restates the goal in terms of `g`.
    change (LinearMap.range g).cardQuot = 2
    rw [hrange, ← Ideal.absNorm_apply]
    simpa [NumberField.RingOfIntegers.rank] using Ideal.absNorm_span_natCast (S := 𝓞 ℚ) 2
  have hnorm : ∀ σ x, ((trivial ℚ).rescale (Real.log 2)).norm σ (f x) = (trivial ℚ).norm σ x := by
    intro σ x
    refine (rescale_norm (E := trivial ℚ) _ σ (2 * x)).trans ?_
    simp only [trivial_norm, Real.exp_neg, Real.exp_log two_pos, map_mul, norm_mul,
      map_ofNat, Complex.norm_ofNat]
    field_simp
  have : Finite (trivial ℚ ⧸ Submodule.span (𝓞 ℚ) {(1 : 𝓞 ℚ)}) := by
    -- The carrier of `trivial ℚ` is `𝓞 ℚ` by definition; `change` restates the span as an ideal.
    change Finite (𝓞 ℚ ⧸ Ideal.span {(1 : 𝓞 ℚ)})
    rw [Ideal.span_singleton_one]
    infer_instance
  have : Finite ((trivial ℚ).rescale (Real.log 2) ⧸ LinearMap.range f) :=
    Nat.finite_of_card_ne_zero (by rw [← Submodule.cardQuot_apply, hcard]; norm_num)
  have h := sectionDegree_map_eq_add_log_cardQuot_range f hnorm 1
  -- By definition `f 1` is `2 * 1` in `𝓞 ℚ`.
  have h1 : f 1 = (show 𝓞 ℚ from 2) := show (2 : 𝓞 ℚ) * 1 = 2 from mul_one _
  rw [sectionDegree_trivial_one, hcard, h1] at h
  simpa using h

end TauCeti.HermitianVectorBundle
