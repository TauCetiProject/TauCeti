/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence

/-!
# The critical-band spectral sequence of real projective space

On `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` the moment function with the standard weights,

`f [v] = (∑ i, i * v i ^ 2) / ∑ i, v i ^ 2`,

is a Morse function with one critical point `[eₖ]` of each index `k ≤ N`, at the value `k`
(`TauCeti.criticalPoints_projectiveMomentFunction`,
`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast`). The values `q - 1/2`, `q : ℤ`, cut
it into critical bands (`TauCeti.isCriticalBandCut_projectiveMomentFunction_natCast`), and this file
computes the spectral sequence of the filtration of `ℝℙᴺ` by the sublevels `{f ≤ q - 1/2}`
(`TauCeti.realProjectiveMorseSpectralSequence`). As in `TauCeti.filteredSpaceSpectralSequence`, it
is indexed cohomologically: singular chains of degree `n` sit in degree `-n`, the object at
`(p, q)` lives in the `q`th band and total degree `p + q = -n`, and the first page is the page `2`.

* **First page.** The first page is the relative homology of the bands, which is free on the
  critical points: the object at `(-2k, k)`, in the `k`th band and degree `k`, is the coefficient
  object for `k ≤ N`
  (`TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso`), and every other object
  vanishes (`TauCeti.isZero_realProjectiveMorseSpectralSequence_page_two_X`).
* **Degeneration.** A differential of the page `r` lowers the band by `r - 1` and the degree by
  one, so from the second page on it joins two nonzero objects only for `r = 2`: every later
  differential vanishes (`TauCeti.realProjectiveMorseSpectralSequence_page_d_eq_zero`).
* **The second page is the homology.** Since the filtration is finite and every degree is
  concentrated in one band, from the second page on the object at `(-2k, k)` is the singular
  homology `H_k(ℝℙᴺ)`, for every coefficient object
  (`TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology`).

With integer coefficients the first page is `ℤ` in each degree `k ≤ N`, but for `N ≥ 2` the first
differential is not zero: it is `0` out of odd degrees
(`TauCeti.realProjectiveMorseSpectralSequence_page_two_d_eq_zero_int_of_odd`) and injective with
cokernel `ℤ/2` out of positive even degrees
(`TauCeti.mono_realProjectiveMorseSpectralSequence_page_two_d_int_of_even`,
`TauCeti.nonempty_cokernel_realProjectiveMorseSpectralSequence_page_two_d_int_iso_zmod_of_even`),
as for the cellular chains `ℤ ← ℤ ← ℤ ← ⋯` of `ℝℙᴺ` with differentials `0, 2, 0, 2, …`. So the
second page differs from the first: it is `ℤ` in degree `0`
(`TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_X_zero_int_iso`), `ℤ/2` in odd
degrees below `N`
(`TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_X_int_iso_zmod_of_odd`), `0` in positive
even degrees (`TauCeti.isZero_realProjectiveMorseSpectralSequence_page_X_int_of_even`), and `ℤ` in
degree `N` when `N` is odd
(`TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_X_top_int_iso_of_odd`). For `ℝℙ²`
the first page is `ℤ, ℤ, ℤ` in degrees `0, 1, 2`, the differential from degree `2` to degree `1` is
multiplication by `±2`, and the second page is `ℤ, ℤ/2, 0`: the relative homology of the bands is
not yet the homology of `ℝℙ²`.

## Main results

* `TauCeti.isCriticalBandCut_projectiveMomentFunction_natCast`: the values `q - 1/2` cut the moment
  function with the standard weights into critical bands, over `ℝ` and over `ℂ`.
* `TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso` and
  `TauCeti.isZero_realProjectiveMorseSpectralSequence_page_two_X`: the first page.
* `TauCeti.realProjectiveMorseSpectralSequence_page_d_eq_zero`: degeneration from the second page.
* `TauCeti.nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology`: from the
  second page on, the object at `(-2k, k)` is `H_k(ℝℙᴺ)`.
* `TauCeti.realProjectiveMorseSpectralSequence_page_two_d_eq_zero_int_of_odd`,
  `TauCeti.mono_realProjectiveMorseSpectralSequence_page_two_d_int_of_even` and
  `TauCeti.nonempty_cokernel_realProjectiveMorseSpectralSequence_page_two_d_int_iso_zmod_of_even`:
  the first differential with integer coefficients.

## Implementation notes

The first differentials are not computed geometrically. The second page is the homology of
`ℝℙᴺ`, which is known from its cellular chains (`TauCeti.RealProjectiveSpace`), and a map
`ℤ ⟶ ℤ` is determined up to sign by its kernel and cokernel.

## References

* R. L. Cohen, K. Iga, P. Norbury, *Topics in Morse theory*, lecture notes, Stanford, 2006,
  Theorems 15.6 and 15.7 (the spectral sequence of the critical-band filtration).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42 (the cellular
  chains of `ℝℙᴺ`).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set
open scoped LinearAlgebra.Projectivization Manifold

universe u v

namespace TauCeti

/-! ### The critical bands of the moment function -/

section Bands

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- A critical point of the moment function with the standard weights whose value lies within
`1/2` of an integer `q` is the coordinate point `[eₖ]` with `k = q`. -/
private theorem exists_eq_mk_single_of_mem_criticalPoints {x : ℙ 𝕜 (Fin (N + 1) → 𝕜)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin N → 𝕜)
      (projectiveMomentFunction 𝕜 fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))) {q : ℤ}
    (hq : projectiveMomentFunction 𝕜 (fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) x ∈
      Icc ((q : ℝ) - 2⁻¹) ((q + 1 : ℤ) - 2⁻¹)) :
    ∃ k : Fin (N + 1), x = Projectivization.mk 𝕜 (Pi.single k 1) (by simp) ∧ ((k : ℕ) : ℤ) = q := by
  rw [criticalPoints_projectiveMomentFunction (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))
    (Nat.cast_injective.comp Fin.val_injective)] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [projectiveMomentFunction_mk_single] at hq
  have h₁ : ((q - 1 : ℤ) : ℝ) < (((k : ℕ) : ℤ) : ℝ) := by push_cast; linarith [hq.1]
  have h₂ : (((k : ℕ) : ℤ) : ℝ) < ((q + 1 : ℤ) : ℝ) := by push_cast at hq ⊢; linarith [hq.2]
  exact ⟨k, rfl, by have := Int.cast_lt.1 h₁; have := Int.cast_lt.1 h₂; lia⟩

/-- **The critical bands of the moment function.** The values `q - 1/2`, `q : ℤ`, cut the moment
function `[v] ↦ (∑ i, i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2` on `ℙ 𝕜 (Fin (N + 1) → 𝕜)` into critical
bands: the band between `q - 1/2` and `q + 1/2` contains no critical value other than `q`. -/
theorem isCriticalBandCut_projectiveMomentFunction_natCast :
    IsCriticalBandCut 𝓘(ℝ, Fin N → 𝕜)
      (projectiveMomentFunction 𝕜 fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))
      fun q : ℤ ↦ (q : ℝ) - 2⁻¹ := by
  refine ⟨fun q ↦ ⟨(isClosed_Icc.preimage
    (contMDiff_projectiveMomentFunction (r := 0) _).continuous).isCompact, q,
    ⟨by linarith, by push_cast; linarith⟩, fun x hx hq ↦ ?_⟩⟩
  obtain ⟨k, rfl, hk⟩ := exists_eq_mk_single_of_mem_criticalPoints hx hq
  rw [projectiveMomentFunction_mk_single, ← hk, Int.cast_natCast]

end Bands

/-! ### The spectral sequence -/

variable {N : ℕ} {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{0} A] (R : A)

variable (N) in
/-- **The critical-band spectral sequence of `ℝℙᴺ`.** The spectral sequence, with coefficients
`R`, of the filtration of `ℙ ℝ (Fin (N + 1) → ℝ)` by the sublevels `{f ≤ q - 1/2}` of the moment
function `f [v] = (∑ i, i * v i ^ 2) / ∑ i, v i ^ 2`, indexed as
`TauCeti.filteredSpaceSpectralSequence`. -/
abbrev realProjectiveMorseSpectralSequence :=
  filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))).comp
      (isCriticalBandCut_projectiveMomentFunction_natCast (N := N) (𝕜 := ℝ)).monotone)

/-- The moment function with the standard weights is a Morse function. -/
private theorem isMorse_projectiveMomentFunction_natCast :
    IsMorse 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) :=
  isMorse_projectiveMomentFunction (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))
    (Nat.cast_injective.comp Fin.val_injective)

/-- **The first page off the diagonal.** On the first page of the critical-band spectral sequence
of `ℝℙᴺ`, the object at `(p, q)` vanishes unless `(p, q) = (-2k, k)` for some `k ≤ N`: the `q`th
band contains only the critical point `[e_q]`, of index `q`. -/
theorem isZero_realProjectiveMorseSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (hpq : ∀ k : ℕ, k ≤ N → pq ≠ (-(2 * k : ℤ), (k : ℤ))) :
    IsZero (((realProjectiveMorseSpectralSequence N R).page 2).X pq) := by
  by_cases hpos : 0 < pq.1 + pq.2
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos
  have hcut := isCriticalBandCut_projectiveMomentFunction_natCast (N := N) (𝕜 := ℝ)
  refine isMorse_projectiveMomentFunction_natCast.isZero_filteredSpaceSpectralSequence_page_two_X
    R hcut.monotone (hcut.isCriticalBand pq.2) pq rfl
    (-(pq.1 + pq.2)).toNat (by lia) fun x hx hfx hidx ↦ ?_
  obtain ⟨k, rfl, hk⟩ := exists_eq_mk_single_of_mem_criticalPoints hx (Ioc_subset_Icc_self hfx)
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, finrank_self, one_mul] at hidx
  exact hpq k (Nat.lt_succ_iff.1 k.2) (Prod.ext (by lia) (by lia))

/-- A nonzero object on the first page lies at `(-2k, k)` for some `k ≤ N`. -/
private theorem exists_eq_of_not_isZero_page_two_X {pq : ℤ × ℤ}
    (h : ¬IsZero (((realProjectiveMorseSpectralSequence N R).page 2).X pq)) :
    ∃ k : ℕ, k ≤ N ∧ pq = (-(2 * k : ℤ), (k : ℤ)) := by
  by_contra hne
  push Not at hne
  exact h (isZero_realProjectiveMorseSpectralSequence_page_two_X R pq hne)

/-- **The first page on the diagonal.** On the first page of the critical-band spectral sequence
of `ℝℙᴺ`, the object at `(-2k, k)`, the relative homology in degree `k` of the `k`th band, is the
coefficient object `R` for `k ≤ N`: the band contains the single critical point `[eₖ]`, of
index `k`. -/
theorem nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso {k : ℕ} (hk : k ≤ N) :
    Nonempty
      (((realProjectiveMorseSpectralSequence N R).page 2).X (-(2 * k : ℤ), (k : ℤ)) ≅ R) := by
  set f := projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)
  have hcut := isCriticalBandCut_projectiveMomentFunction_natCast (N := N) (𝕜 := ℝ)
  obtain ⟨e⟩ := IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma
    R isMorse_projectiveMomentFunction_natCast hcut.monotone (hcut.isCriticalBand k)
    (-(2 * k : ℤ), (k : ℤ)) rfl k (by push_cast; ring)
  -- The band contains a single critical point of index `k`, namely `[eₖ]`.
  let k' : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hmem : Projectivization.mk ℝ (Pi.single k' 1) (by simp) ∈
      criticalPoints 𝓘(ℝ, Fin N → ℝ) f ∩ f ⁻¹' Ioc ((k : ℤ) - 2⁻¹ : ℝ) ((k + 1 : ℤ) - 2⁻¹) := by
    refine ⟨mk_single_mem_criticalPoints_projectiveMomentFunction _ k', ?_⟩
    simp only [mem_preimage, f, projectiveMomentFunction_mk_single, mem_Ioc, k']
    push_cast
    constructor <;> linarith
  have : Subsingleton {x : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ) f ∩
      f ⁻¹' Ioc ((k : ℤ) - 2⁻¹ : ℝ) ((k + 1 : ℤ) - 2⁻¹)) //
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) f x = k} := by
    refine ⟨fun x y ↦ Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨i, hi, hik⟩ := exists_eq_mk_single_of_mem_criticalPoints x.1.2.1
      (Ioc_subset_Icc_self x.1.2.2)
    obtain ⟨j, hj, hjk⟩ := exists_eq_mk_single_of_mem_criticalPoints y.1.2.1
      (Ioc_subset_Icc_self y.1.2.2)
    rw [hi, hj, Fin.ext (by lia : (i : ℕ) = j)]
  have := uniqueOfSubsingleton (α := {x : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ) f ∩
      f ⁻¹' Ioc ((k : ℤ) - 2⁻¹ : ℝ) ((k + 1 : ℤ) - 2⁻¹)) //
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) f x = k})
    ⟨⟨_, hmem⟩, by simp [f, k', manifoldMorseIndex_projectiveMomentFunction_natCast]⟩
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- Two positions on the diagonal are never joined by a differential of the page `s ≥ 3`: such a
differential lowers the band by `s - 1` and the degree by one. -/
private theorem not_rel_diagonal {s : ℤ} (hs : 3 ≤ s) (k k' : ℕ) :
    ¬(ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel (-(2 * k : ℤ), (k : ℤ))
      (-(2 * k' : ℤ), (k' : ℤ)) := by
  intro h
  simp only [ComplexShape.up'_Rel, Prod.mk_add_mk, Prod.mk.injEq] at h
  lia

/-- On the page `r ≥ 2`, every object joined to a position by a differential of a page `s ≥ 3`
vanishes, unless the position is off the diagonal. -/
private theorem isZero_page_X_of_rel {r s : ℤ} (hr : 2 ≤ r) (hs : 3 ≤ s) {pq pq' : ℤ × ℤ}
    (hrel : (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq pq' ∨
      (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq' pq) :
    IsZero (((realProjectiveMorseSpectralSequence N R).page r).X pq) ∨
      IsZero (((realProjectiveMorseSpectralSequence N R).page r).X pq') := by
  set E := realProjectiveMorseSpectralSequence N R
  by_contra h
  rw [not_or] at h
  obtain ⟨k, -, rfl⟩ := exists_eq_of_not_isZero_page_two_X R
    fun h₀ ↦ h.1 (E.isZero_page_X_of_le le_rfl h₀ r hr)
  obtain ⟨k', -, rfl⟩ := exists_eq_of_not_isZero_page_two_X R
    fun h₀ ↦ h.2 (E.isZero_page_X_of_le le_rfl h₀ r hr)
  rcases hrel with hrel | hrel
  exacts [not_rel_diagonal hs k k' hrel, not_rel_diagonal hs k' k hrel]

/-- **Degeneration from the second page.** In the critical-band spectral sequence of `ℝℙᴺ`, every
differential of every page `r ≥ 3` vanishes: from the second page on the spectral sequence has
collapsed. -/
theorem realProjectiveMorseSpectralSequence_page_d_eq_zero {r : ℤ} (hr : 3 ≤ r)
    (pq pq' : ℤ × ℤ) :
    ((realProjectiveMorseSpectralSequence N R).page r).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
  · exact SpectralSequence.page_d_eq_zero_of_le _ (r := 2) le_rfl
      (isZero_page_X_of_rel R le_rfl hr (Or.inl hrel)) r (by lia)
  · exact HomologicalComplex.shape _ _ _ hrel

/-- The filtration of `ℝℙᴺ` by the sublevels `{f ≤ q - 1/2}` is empty at `q = 0`. -/
private theorem sublevel_zero_eq_empty :
    ((fun c ↦ {x | projectiveMomentFunction ℝ (fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) x ≤ c}) ∘
      fun q : ℤ ↦ (q : ℝ) - 2⁻¹) 0 = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := (projectiveMomentFunction_mem_Icc
      (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) (fun _ _ h ↦ Nat.cast_le.2 h) x).1
    simp only [Fin.val_zero, Nat.cast_zero] at this
    simp only [Function.comp_apply, Int.cast_zero, zero_sub, mem_ofPred_eq] at hx
    linarith

/-- The filtration of `ℝℙᴺ` by the sublevels `{f ≤ q - 1/2}` is everything from `q = N + 1` on. -/
private theorem sublevel_eq_univ {b : ℤ} (hb : N + 1 ≤ b) :
    ((fun c ↦ {x | projectiveMomentFunction ℝ (fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) x ≤ c}) ∘
      fun q : ℤ ↦ (q : ℝ) - 2⁻¹) b = univ :=
  eq_univ_of_forall fun x ↦ by
    have := (projectiveMomentFunction_mem_Icc
      (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) (fun _ _ h ↦ Nat.cast_le.2 h) x).2
    simp only [Fin.val_last] at this
    have : ((N + 1 : ℤ) : ℝ) ≤ b := Int.cast_le.2 hb
    simp only [Function.comp_apply, mem_ofPred_eq]
    push_cast at this
    linarith

/-- From the page `r ≥ 3` on, the object at `(-2k, k)` does not change: every differential at it
joins it to an object off the diagonal. -/
private theorem nonempty_page_X_iso_page_X {r r' : ℤ} (hr : 3 ≤ r) (hrr' : r ≤ r') (k : ℕ) :
    Nonempty (((realProjectiveMorseSpectralSequence N R).page r').X (-(2 * k : ℤ), (k : ℤ)) ≅
      ((realProjectiveMorseSpectralSequence N R).page r).X (-(2 * k : ℤ), (k : ℤ))) :=
  ⟨SpectralSequence.pageXIsoOfLEOfIsZero _ (r := r) (by lia) (pq := (-(2 * k : ℤ), (k : ℤ)))
    (fun s hs pq' hpq' ↦ by
      by_contra h
      obtain ⟨j, -, rfl⟩ := exists_eq_of_not_isZero_page_two_X R fun h₀ ↦
        h (SpectralSequence.isZero_page_X_of_le _ le_rfl h₀ r (by lia))
      rcases hpq' with hpq' | hpq'
      exacts [not_rel_diagonal (by lia) k j hpq', not_rel_diagonal (by lia) j k hpq'])
    r' hrr'⟩

/-- **The second page is the homology of `ℝℙᴺ`.** In the critical-band spectral sequence of
`ℝℙᴺ` with coefficients `R`, on every page `r ≥ 3`, that is from the second page on, the object
at `(-2k, k)` is the singular homology `H_k(ℝℙᴺ; R)`. The filtration is finite, every degree `k`
is concentrated in the `k`th band, and the spectral sequence has collapsed. -/
theorem nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology {r : ℤ}
    (hr : 3 ≤ r) (k : ℕ) :
    Nonempty (((realProjectiveMorseSpectralSequence N R).page r).X (-(2 * k : ℤ), (k : ℤ)) ≅
      ((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
        (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))) := by
  set E := realProjectiveMorseSpectralSequence N R
  have hX := (sublevel_mono (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))).comp
    (isCriticalBandCut_projectiveMomentFunction_natCast (N := N) (𝕜 := ℝ)).monotone
  -- The filtration starts empty at `0` and is everything from `b` on.
  set b : ℤ := k + N + 1
  have hXb := sublevel_eq_univ (N := N) (b := b) (by lia)
  -- On the page `r'` the objects are the graded pieces of the homology of `ℝℙᴺ`.
  set r' := max r (b + 1)
  have hgr (q : ℤ) (hq₀ : 0 ≤ q) (hqb : q < b) (pq : ℤ × ℤ) (hpq : pq.2 = q) :=
    filteredSpaceSpectralSequencePageXIsoGradedOfFinite (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))
      R hX sublevel_zero_eq_empty hXb r' (by lia) pq (by lia) (by lia)
  -- Every graded piece in degree `k` outside the `k`th band vanishes.
  set X := CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    (monotone_singularChainFiltration (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R hX))
  have hzero (q : ℤ) (hq₀ : 0 ≤ q) (hqb : q < b) (hqk : q ≠ k) :
      IsZero (cokernel (X.abutmentFiltrationMap q (-(k : ℤ)))) := by
    have h := (hgr q hq₀ hqb (-(k : ℤ) - q, q) rfl).isZero_iff.1
      (E.isZero_page_X_of_le le_rfl (isZero_realProjectiveMorseSpectralSequence_page_two_X R _
        fun j _ h ↦ hqk (by simp only [Prod.mk.injEq] at h; lia)) r' (by lia))
    rwa [sub_add_cancel] at h
  -- So the graded piece in the `k`th band is the whole homology.
  have eX := X.cokernelAbutmentFiltrationMapIsoAbutment (a := 0) (b := b) (q₀ := k)
    (by lia) (by lia)
    (CochainComplex.isZero_filtrationAbutmentFiltration _ _
      (singularChainFiltration_eq_bot R sublevel_zero_eq_empty) _)
    (CochainComplex.isIso_filtrationAbutmentFiltrationι _ _
      (singularChainFiltration_eq_top R hXb) _) hzero
  obtain ⟨e⟩ := nonempty_page_X_iso_page_X R hr (le_max_left r (b + 1)) k
  obtain ⟨e'⟩ : Nonempty (cokernel (X.abutmentFiltrationMap (k : ℤ)
      ((-(2 * k : ℤ), (k : ℤ)).1 + (-(2 * k : ℤ), (k : ℤ)).2)) ≅
        cokernel (X.abutmentFiltrationMap (k : ℤ) (-(k : ℤ)))) := by
    rw [show (-(2 * k : ℤ), (k : ℤ)).1 + (-(2 * k : ℤ), (k : ℤ)).2 = -(k : ℤ) by dsimp; ring]
    exact ⟨Iso.refl _⟩
  exact ⟨e.symm ≪≫ hgr k (by lia) (by lia) _ rfl ≪≫ e' ≪≫ eX ≪≫ filteredSpaceAbutmentIso R hX k⟩

/-! ### Integer coefficients -/

section Int

/-- The singular homology of `ℙ ℝ (Fin (N + 1) → ℝ)` is that of `RPᴺ`. -/
private def singularHomologyProjectivizationIso (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (RealProjectiveSpace N)) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo (X := TopCat.of (RealProjectiveSpace N))
      (RealProjectiveSpace.homeomorphProjectivization N))).symm

/-- **The second page in degree `0`.** With integer coefficients, on every page `r ≥ 2` of the
critical-band spectral sequence of `ℝℙᴺ` the object at `(0, 0)` is `ℤ`: on the first page it is
the relative homology of the band of the minimum, and from the second page on it is
`H₀(ℝℙᴺ; ℤ) ≅ ℤ`. -/
theorem nonempty_realProjectiveMorseSpectralSequence_page_X_zero_int_iso {r : ℤ}
    (hr : 2 ≤ r) :
    Nonempty (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page r).X (0, 0) ≅
      ModuleCat.of ℤ ℤ) := by
  have h0 : ((-(2 * ((0 : ℕ) : ℤ)), ((0 : ℕ) : ℤ)) : ℤ × ℤ) = (0, 0) := by simp
  rcases hr.eq_or_lt with rfl | hr
  · obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso
      (ModuleCat.of ℤ ℤ) (Nat.zero_le N)
    rw [h0] at e
    exact ⟨e⟩
  obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology
    (N := N) (ModuleCat.of ℤ ℤ) hr 0
  rw [h0] at e
  exact ⟨e ≪≫ singularHomologyProjectivizationIso 0 ≪≫
    (RealProjectiveSpace.singularHomologyZeroLinearEquiv ℤ).toModuleIso⟩

/-- **The second page in odd degrees.** With integer coefficients, on every page `r ≥ 3` of the
critical-band spectral sequence of `ℝℙᴺ` the object at `(-2k, k)` for odd `k < N` is
`H_k(ℝℙᴺ; ℤ) ≅ ℤ/2`, although the first page is `ℤ` there. -/
theorem nonempty_realProjectiveMorseSpectralSequence_page_X_int_iso_zmod_of_odd {r : ℤ}
    (hr : 3 ≤ r) {k : ℕ} (hk : Odd k) (hkN : k < N) :
    Nonempty (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page r).X
      (-(2 * k : ℤ), (k : ℤ)) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology
    (N := N) (ModuleCat.of ℤ ℤ) hr k
  exact ⟨e ≪≫ (RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd hk
    hkN).toModuleIso⟩

/-- **The second page in positive even degrees.** With integer coefficients, on every page
`r ≥ 3` of the critical-band spectral sequence of `ℝℙᴺ` the object at `(-2k, k)` for even
`k > 0` vanishes, although the first page is `ℤ` there for `k ≤ N`. -/
theorem isZero_realProjectiveMorseSpectralSequence_page_X_int_of_even {r : ℤ} (hr : 3 ≤ r)
    {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) :
    IsZero (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page r).X
      (-(2 * k : ℤ), (k : ℤ))) := by
  obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology
    (N := N) (ModuleCat.of ℤ ℤ) hr k
  exact e.isZero_iff.2 (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even ℤ
    (isRegular_iff_ne_zero.2 two_ne_zero).right hk hk0)

/-- **The second page in the top degree.** With integer coefficients, for odd `N`, on every page
`r ≥ 2` of the critical-band spectral sequence of `ℝℙᴺ` the object at `(-2N, N)` is `ℤ`: on the
first page it is the relative homology of the band of the maximum, and from the second page on it
is `H_N(ℝℙᴺ; ℤ) ≅ ℤ`. -/
theorem nonempty_realProjectiveMorseSpectralSequence_page_X_top_int_iso_of_odd {r : ℤ}
    (hr : 2 ≤ r) (hN : Odd N) :
    Nonempty (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page r).X
      (-(2 * N : ℤ), (N : ℤ)) ≅ ModuleCat.of ℤ ℤ) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso _ le_rfl
  obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_iso_singularHomology
    (N := N) (ModuleCat.of ℤ ℤ) hr N
  exact ⟨e ≪≫ singularHomologyProjectivizationIso N ≪≫
    (RealProjectiveSpace.singularHomologyTopLinearEquivOfOdd ℤ hN).toModuleIso⟩

/-- The page `2` objects on the diagonal, with integer coefficients. -/
private theorem nonempty_page_two_X_int_iso {k : ℕ} (hk : k ≤ N) (pq : ℤ × ℤ)
    (hpq : pq = (-(2 * k : ℤ), (k : ℤ))) :
    Nonempty (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).X pq ≅
      ModuleCat.of ℤ ℤ) := by
  subst hpq
  exact nonempty_realProjectiveMorseSpectralSequence_page_two_X_iso _ hk

/-- With integer coefficients, the first differential out of `(-2k, k)` for `0 < k ≤ N` is a map
`ℤ ⟶ ℤ`, so it is zero or injective. -/
private theorem page_two_d_eq_zero_or_mono {k : ℕ} (hk0 : k ≠ 0) (hkN : k ≤ N) :
    ((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
        (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1) = 0 ∨
      Mono (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
        (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) := by
  obtain ⟨eX⟩ := nonempty_page_two_X_int_iso (N := N) hkN _ rfl
  have hk1 : ((k - 1 : ℕ) : ℤ) = k - 1 := by lia
  obtain ⟨eY⟩ := nonempty_page_two_X_int_iso (N := N) (k := k - 1) (by lia)
    (-(2 * k : ℤ) + 2, (k : ℤ) - 1) (Prod.ext (by dsimp; rw [hk1]; ring) (by dsimp; rw [hk1]))
  -- Transported to `ℤ ⟶ ℤ`, the differential is multiplication by its value at `1`.
  set d := ((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
    (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)
  set g := eX.inv ≫ d ≫ eY.hom
  have hd : d = eX.hom ≫ g ≫ eY.inv := by simp [g]
  have hg : g.hom = LinearMap.toSpanSingleton ℤ ℤ (g.hom 1) := LinearMap.ext_ring (by simp)
  by_cases hg1 : g.hom 1 = 0
  · left
    rw [hd, ModuleCat.hom_injective (hg.trans (by
      rw [hg1, LinearMap.toSpanSingleton_zero, ModuleCat.hom_zero]) :
        g.hom = (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ).hom)]
    simp
  · right
    have hinj : Function.Injective g.hom := by
      rw [hg]
      exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℤ hg1)
    have : Mono g := (ModuleCat.mono_iff_injective g).2 hinj
    rw [hd]
    infer_instance

/-- **The first differential out of odd degrees.** With integer coefficients, in the critical-band
spectral sequence of `ℝℙᴺ`, the first differential out of `(-2k, k)`, from the `k`th band to the
`(k - 1)`st, vanishes for odd `k`. -/
theorem realProjectiveMorseSpectralSequence_page_two_d_eq_zero_int_of_odd {k : ℕ}
    (hk : Odd k) :
    ((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
      (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1) = 0 := by
  set E := realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)
  -- Above `N` the source vanishes.
  rcases le_or_gt k N with hkN | hkN
  swap
  · exact (isZero_realProjectiveMorseSpectralSequence_page_two_X _ _ fun j hj h ↦ by
      simp only [Prod.mk.injEq] at h; lia).eq_of_src _ _
  refine (page_two_d_eq_zero_or_mono hk.pos.ne' hkN).resolve_right fun hmono ↦ ?_
  -- Otherwise the cycles, and so the second page, would vanish at `(-2k, k)`, where the second
  -- page is `ℤ/2` or `ℤ`.
  have hcycles : IsZero ((E.page 2 le_rfl).cycles (-(2 * k : ℤ), (k : ℤ))) :=
    IsZero.of_mono_eq_zero ((E.page 2 le_rfl).iCycles _) ((cancel_mono ((E.page 2 le_rfl).d
      (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1))).1 (by simp))
  have hzero := (E.iso 2 3 (-(2 * k : ℤ), (k : ℤ))).isZero_iff.1
    (IsZero.of_epi ((E.page 2 le_rfl).homologyπ _) hcycles)
  rcases hkN.lt_or_eq with hkN | rfl
  · obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_int_iso_zmod_of_odd le_rfl
      hk hkN
    exact not_subsingleton (ZMod 2) (ModuleCat.isZero_iff_subsingleton.1 (e.isZero_iff.1 hzero))
  · obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_top_int_iso_of_odd
      (r := 3) (by norm_num) hk
    exact not_subsingleton ℤ (ModuleCat.isZero_iff_subsingleton.1 (e.isZero_iff.1 hzero))

/-- The first differential out of a positive even degree `k ≤ N` is injective, with cokernel the
second page at `(-2k + 2, k - 1)`, which is `ℤ/2`. -/
private theorem mono_and_nonempty_cokernel_page_two_d_iso_zmod {k : ℕ} (hk : Even k)
    (hk0 : k ≠ 0) (hkN : k ≤ N) :
    Mono (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
        (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) ∧
      Nonempty (cokernel (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
        (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  set E := realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)
  set K := E.page 2
  set j := k - 1
  have hjk : (j : ℤ) = k - 1 := by lia
  have hjodd : Odd j := Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 hk0) hk odd_one
  have hpq' : (-(2 * j : ℤ), (j : ℤ)) = (-(2 * k : ℤ) + 2, (k : ℤ) - 1) := by
    rw [hjk]; ext <;> simp; ring
  -- The second page at `(-2k + 2, k - 1)` is `ℤ/2`, and it is the cokernel of the differential.
  obtain ⟨e⟩ := nonempty_realProjectiveMorseSpectralSequence_page_X_int_iso_zmod_of_odd (N := N)
    le_rfl hjodd (by lia)
  have hd := realProjectiveMorseSpectralSequence_page_two_d_eq_zero_int_of_odd (N := N) hjodd
  have hnext : (-(2 * j : ℤ) + 2, (j : ℤ) - 1) = (-(2 * k : ℤ) + 2 + 2, (k : ℤ) - 1 - 1) := by
    rw [hjk]; ext <;> simp; ring
  rw [hpq'] at e hd
  rw [hnext] at hd
  have hcok := K.opcyclesIsCokernel _ _ ((ComplexShape.up' _).prev_eq'
    (by simp only [ComplexShape.up'_Rel, Prod.mk_add_mk, Prod.mk.injEq]; lia :
      (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).Rel (-(2 * k : ℤ), (k : ℤ))
        (-(2 * k : ℤ) + 2, (k : ℤ) - 1)))
  have ec : cokernel (K.d (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) ≅
      ModuleCat.of ℤ (ZMod 2) :=
    (hcok.coconePointUniqueUpToIso (colimit.isColimit _)).symm ≪≫
    (K.isoHomologyι _ _ ((ComplexShape.up' _).next_eq'
      (by simp only [ComplexShape.up'_Rel, Prod.mk_add_mk, Prod.mk.injEq]; lia)) hd).symm ≪≫
    E.iso 2 3 _ ≪≫ e
  refine ⟨(page_two_d_eq_zero_or_mono hk0 hkN).resolve_left fun h0 ↦ ?_, ⟨ec⟩⟩
  -- A zero differential would have cokernel `ℤ`, which is infinite, unlike `ℤ/2`.
  obtain ⟨eY⟩ := nonempty_page_two_X_int_iso (N := N) (k := j) (by lia) _ hpq'.symm
  have := Finite.of_equiv _ (eY.symm ≪≫ (cokernelIsoOfEq h0 ≪≫ cokernelZeroIsoTarget).symm ≪≫
    ec).toLinearEquiv.toEquiv.symm
  exact not_finite ℤ

/-- **The first differential out of positive even degrees is injective.** With integer
coefficients, in the critical-band spectral sequence of `ℝℙᴺ`, the first differential out of
`(-2k, k)`, from the `k`th band to the `(k - 1)`st, is injective for even `k > 0`: for `k ≤ N` it
is multiplication by `±2` between two copies of `ℤ`, and above `N` its source vanishes. -/
theorem mono_realProjectiveMorseSpectralSequence_page_two_d_int_of_even {k : ℕ} (hk : Even k)
    (hk0 : k ≠ 0) :
    Mono (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
      (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) := by
  rcases le_or_gt k N with hkN | hkN
  · exact (mono_and_nonempty_cokernel_page_two_d_iso_zmod hk hk0 hkN).1
  · exact mono_of_source_iso_zero _ (isZero_realProjectiveMorseSpectralSequence_page_two_X _ _
      fun j hj h ↦ by simp only [Prod.mk.injEq] at h; lia).isoZero

/-- **The cokernel of the first differential out of positive even degrees.** With integer
coefficients, in the critical-band spectral sequence of `ℝℙᴺ`, the first differential out of
`(-2k, k)` has cokernel `ℤ/2` for even `k` with `0 < k ≤ N`. -/
theorem nonempty_cokernel_realProjectiveMorseSpectralSequence_page_two_d_int_iso_zmod_of_even
    {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) (hkN : k ≤ N) :
    Nonempty (cokernel (((realProjectiveMorseSpectralSequence N (ModuleCat.of ℤ ℤ)).page 2).d
      (-(2 * k : ℤ), (k : ℤ)) (-(2 * k : ℤ) + 2, (k : ℤ) - 1)) ≅ ModuleCat.of ℤ (ZMod 2)) :=
  (mono_and_nonempty_cokernel_page_two_d_iso_zmod hk hk0 hkN).2

end Int

end TauCeti
