/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.UnitaryCongruence
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Unitary matrices over a CM field congruent to one modulo a large ideal

Let `E` be a CM field, with complex conjugation `NumberField.IsCMField.complexConj E` as its star
operation, and `γ` a square matrix over `E` of size `n` with `γᴴ γ = 1`, where `γᴴ` is the
conjugate transpose. Every complex embedding `φ` of `E` commutes with conjugation, so `φ(γ)` is
a complex unitary matrix. The results of `TauCeti.NumberTheory.NumberField.UnitaryCongruence`
then show: if `tr (γ - 1)` lies in an integral ideal `I` of norm `N(I) > (2n)^[E:ℚ]`, or if
`x⁻¹ γ x ≡ 1` modulo `IÔ` for some `x ∈ GL_n(𝔸_f)`, then `γ = 1`. Consequently the unitary group
of `E` meets every conjugate `g L g⁻¹`, `g ∈ GL_n(𝔸_f)`, of a subgroup `L` of `GL_n(𝔸_f)` of
matrices congruent to `1` modulo `IÔ` only in `1`. The ideal `I` may be any integral ideal of
large norm, for instance a product of distinct primes `w_i` with `∏ N(w_i) > (2n)^[E:ℚ]`.

The bound `N(I) > (2n)^[E:ℚ]` is sharp: for `E = ℚ(i)`, `n = 1`, `γ = -1` and `I = (2)`, the
trace `tr (γ - 1) = -2` lies in `I` and `N(I) = 4 = (2 · 1)²`.

## Main results

* `NumberField.IsCMField.map_mem_unitaryGroup`: a matrix with `γᴴ γ = 1` is unitary at every
  complex embedding.
* `NumberField.IsCMField.eq_one_of_trace_sub_one_mem`,
  `NumberField.IsCMField.eq_one_of_conj_sub_one_mem_completedIdeal`: `γ = 1` when `tr (γ - 1)`
  lies in `I`, or when `x⁻¹ γ x ≡ 1` modulo `IÔ`.
* `NumberField.IsCMField.comap_map_conj_eq_bot`: the unitary group of `E` meets every conjugate
  of a subgroup of `GL_n(𝔸_f)` congruent to `1` modulo `IÔ` trivially.
* `NumberField.IsCMField.comap_map_conj_eq_bot_of_isMaximal`: the same for subgroups congruent to
  `1` modulo `wÔ` at finitely many places `w` with `∏ N(w) > (2n)^[E:ℚ]`.

## References

* A version of this result, for subgroups of the finite adelic unitary group, is
  `New.Variety.classAut_eq_bot` (`Lib/Shimura/HeckeTower/HeckeData`) in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open Module Matrix IsDedekindDomain
open scoped IsDedekindDomain.FiniteAdeleRing

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n]

/-- Over a CM field `E`, a matrix `γ` with `γᴴ γ = 1` is unitary at every complex embedding,
since complex embeddings commute with complex conjugation. -/
theorem map_mem_unitaryGroup {γ : Matrix n n E} (hγ : γᴴ * γ = 1) (φ : E →+* ℂ) :
    γ.map φ ∈ unitaryGroup n ℂ :=
  map_mem_unitary φ (fun x ↦ complexEmbedding_complexConj E φ x)
    (mem_unitaryGroup_iff'.mpr hγ)

/-- **A unitary matrix congruent to one modulo a large ideal is one.** Over a CM field `E`, let
`γ` be a square matrix of size `n` with `γᴴ γ = 1`. If `tr (γ - 1)` is an element `t` of an
integral ideal `I` with `N(I) > (2n)^[E:ℚ]`, then `γ = 1`. -/
theorem eq_one_of_trace_sub_one_mem {γ : Matrix n n E} (hγ : γᴴ * γ = 1) {I : Ideal (𝓞 E)}
    (hI : (2 * Fintype.card n) ^ finrank ℚ E < Ideal.absNorm I) {t : 𝓞 E} (ht : t ∈ I)
    (htr : (t : E) = (γ - 1).trace) : γ = 1 :=
  eq_one_of_trace_sub_one_mem_of_archimedean_unitary
    (fun φ ↦ ⟨1, by simpa using map_mem_unitaryGroup hγ φ⟩) hI ht htr

/-- **Adelic form.** Over a CM field `E`, let `γ` be a square matrix of size `n` with
`γᴴ γ = 1`, and `I` an integral ideal with `N(I) > (2n)^[E:ℚ]`. If `x⁻¹ γ x ≡ 1` modulo `IÔ` for
some `x ∈ GL_n(𝔸_f)`, that is, every entry of `x⁻¹ γ x - 1` is an element of the completion
`IÔ` of `I` in the integral finite adeles, then `γ = 1`. -/
theorem eq_one_of_conj_sub_one_mem_completedIdeal {γ : Matrix n n E} (hγ : γᴴ * γ = 1)
    {I : Ideal (𝓞 E)} (hI : (2 * Fintype.card n) ^ finrank ℚ E < Ideal.absNorm I)
    (x : GL n 𝔸ᶠ[𝓞 E, E])
    (hx : ∀ i j, ∃ c ∈ FiniteAdeleRing.completedIdeal E I, (c : 𝔸ᶠ[𝓞 E, E]) =
      (((x⁻¹ : GL n 𝔸ᶠ[𝓞 E, E]) : Matrix n n 𝔸ᶠ[𝓞 E, E]) *
        γ.map (algebraMap E 𝔸ᶠ[𝓞 E, E]) * (x : Matrix n n 𝔸ᶠ[𝓞 E, E]) - 1) i j) :
    γ = 1 :=
  eq_one_of_conj_sub_one_mem_completedIdeal_of_archimedean_unitary
    (fun φ ↦ ⟨1, by simpa using map_mem_unitaryGroup hγ φ⟩) hI x hx

/-- **Trivial intersections.** Over a CM field `E`, let `I` be an integral ideal with
`N(I) > (2n)^[E:ℚ]` and `L` a subgroup of `GL_n(𝔸_f)` all of whose elements are congruent to `1`
modulo `IÔ`. For every `g ∈ GL_n(𝔸_f)`, the unitary group `{γ : γᴴ γ = 1}` of `E`, embedded
diagonally in `GL_n(𝔸_f)`, meets `g L g⁻¹` only in `1`. -/
theorem comap_map_conj_eq_bot {I : Ideal (𝓞 E)}
    (hI : (2 * Fintype.card n) ^ finrank ℚ E < Ideal.absNorm I) {L : Subgroup (GL n 𝔸ᶠ[𝓞 E, E])}
    (hL : ∀ k ∈ L, ∀ i j, ∃ c ∈ FiniteAdeleRing.completedIdeal E I,
      (c : 𝔸ᶠ[𝓞 E, E]) = ((k : Matrix n n 𝔸ᶠ[𝓞 E, E]) - 1) i j) (g : GL n 𝔸ᶠ[𝓞 E, E]) :
    (L.map (MulAut.conj g).toMonoidHom).comap
      ((GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[𝓞 E, E])).comp Unitary.toUnits) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun γ hγ ↦ ?_
  obtain ⟨k, hk, hkγ⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hγ)
  refine Subtype.ext (eq_one_of_conj_sub_one_mem_completedIdeal
    (Matrix.UnitaryGroup.star_mul_self γ) hI g fun i j ↦ ?_)
  have hgk : ((g⁻¹ : GL n 𝔸ᶠ[𝓞 E, E]) : Matrix n n 𝔸ᶠ[𝓞 E, E]) *
      (γ : Matrix n n E).map (algebraMap E 𝔸ᶠ[𝓞 E, E]) * (g : Matrix n n 𝔸ᶠ[𝓞 E, E]) = k := by
    have h := congrArg (fun y : GL n 𝔸ᶠ[𝓞 E, E] ↦ ((g⁻¹ * y * g : GL n 𝔸ᶠ[𝓞 E, E]) :
      Matrix n n 𝔸ᶠ[𝓞 E, E])) hkγ
    simpa [mul_assoc] using h.symm
  rw [hgk]
  exact hL k hk i j

/-- **Trivial intersections, at finitely many places.** Over a CM field `E`, let `s` be a finite
set of maximal ideals (finite places) `w` of `𝓞 E` with `∏_{w ∈ s} N(w) > (2n)^[E:ℚ]`, and `L` a
subgroup of `GL_n(𝔸_f)` all of whose elements are congruent to `1` modulo `wÔ` for every
`w ∈ s`. For every `g ∈ GL_n(𝔸_f)`, the unitary group `{γ : γᴴ γ = 1}` of `E`, embedded
diagonally in `GL_n(𝔸_f)`, meets `g L g⁻¹` only in `1`. -/
theorem comap_map_conj_eq_bot_of_isMaximal {s : Finset (Ideal (𝓞 E))}
    (hs : ∀ w ∈ s, w.IsMaximal)
    (hI : (2 * Fintype.card n) ^ finrank ℚ E < ∏ w ∈ s, Ideal.absNorm w)
    {L : Subgroup (GL n 𝔸ᶠ[𝓞 E, E])}
    (hL : ∀ k ∈ L, ∀ w ∈ s, ∀ i j, ∃ c ∈ FiniteAdeleRing.completedIdeal E w,
      (c : 𝔸ᶠ[𝓞 E, E]) = ((k : Matrix n n 𝔸ᶠ[𝓞 E, E]) - 1) i j) (g : GL n 𝔸ᶠ[𝓞 E, E]) :
    (L.map (MulAut.conj g).toMonoidHom).comap
      ((GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[𝓞 E, E])).comp Unitary.toUnits) = ⊥ := by
  have hcop : (s : Set (Ideal (𝓞 E))).Pairwise (Function.onFun IsCoprime fun w ↦ w) :=
    fun v hv w hw hvw ↦ haveI := hs v hv; haveI := hs w hw; Ideal.isCoprime_of_isMaximal hvw
  refine comap_map_conj_eq_bot (I := ∏ w ∈ s, w) (by rwa [map_prod]) (fun k hk i j ↦ ?_) g
  rcases s.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · -- With no places, `hI` says `(2 * card n) ^ [E:ℚ] < 1`, impossible since `i : n` exists.
    have hn : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Finset.prod_empty] at hI
    exact absurd hI (Nat.one_le_pow _ _ (by omega)).not_gt
  obtain ⟨c, -, hc⟩ := hL k hk w₀ hw₀ i j
  refine ⟨c, ?_, hc⟩
  rw [FiniteAdeleRing.completedIdeal_prod_eq_iInf E hcop]
  simp only [Submodule.mem_iInf]
  intro w hw
  obtain ⟨c', hc'I, hc'⟩ := hL k hk w hw i j
  exact Subtype.ext (hc.trans hc'.symm) ▸ hc'I

end NumberField.IsCMField
