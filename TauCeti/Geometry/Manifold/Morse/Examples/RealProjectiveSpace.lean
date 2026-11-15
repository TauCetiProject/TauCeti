/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.Sublevel

/-!
# The critical-band spectral sequence of real projective space

The standard moment function `f[v] = (∑ i, i * v i ^ 2) / ∑ i, v i ^ 2` on
`ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)` is a Morse function whose critical points are the coordinate points
`[e_q]`, of value `q` and index `q`, for `0 ≤ q ≤ n`. The values `q - 1 / 2` cut it into critical
bands (`TauCeti.isCriticalBandCut_projectiveMomentFunction_natCast`), each containing at most one
critical point, and the sublevels `X q = {f ≤ q - 1 / 2}` form its critical-band filtration. This
file computes the beginning of the spectral sequence of that filtration
(`TauCeti.realProjectiveSpaceSpectralSequence`), in the convention of
`TauCeti.filteredSpaceSpectralSequence`: the first page, numbered `2`, has at `(p, q)` the
relative homology `Hₘ(X (q + 1), X q)` of the `q`th band, `p + q = -m`.

* **The first page.** It is the coefficient object at `(-2q, q)` for `0 ≤ q ≤ n`, one copy for the
  critical point `[e_q]` of index `q`, and zero elsewhere.
* **The first differential of `ℝℙ²`.** With integer coefficients the first page of `ℝℙ²` is `ℤ` in
  the three bands, in degrees `0`, `1` and `2`. Its differential from the band of the maximum to
  the band of the saddle is multiplication by `2`, and its differential from the saddle to the
  minimum vanishes.
* **The second page of `ℝℙ²`.** It is `ℤ`, `ℤ/2` and `0` in degrees `0`, `1` and `2`, which is the
  integral homology of `ℝℙ²`. So the relative homology of the bands is not yet the second page:
  the first differential of a critical-band filtration can be nonzero, here because the top cell
  of `ℝℙ²` is attached along a map of degree `±2` onto the core circle.

The first differential of `ℝℙ²` is the connecting map `δ : H₂(X 3, X 2) ⟶ H₁(X 2, X 1)` of the
triple `X 1 ⊆ X 2 ⊆ X 3` (`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), where
`X 0 = ∅` and `X 3 = ℝℙ²`. It is computed from the long exact sequences of the triples
`X 1 ⊆ X 2 ⊆ X 3` and `X 0 ⊆ X 1 ⊆ X 3` and from the integral homology of `ℝℙ²`
(`TauCeti.RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd` and
`TauCeti.RealProjectiveSpace.isZero_singularHomology_projectivization_of_even`): `δ` is injective
since `H₂(X 3, X 1) = H₂(ℝℙ²) = 0`, and its cokernel is `H₁(X 3, X 1) ≅ H₁(ℝℙ²) = ℤ/2`. A map
`ℤ ⟶ ℤ` with cokernel of order two is multiplication by `±2`.

## Main declarations

* `TauCeti.realProjectiveSpaceSpectralSequence`: the spectral sequence of this critical-band
  filtration.
* `TauCeti.nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso` and
  `TauCeti.isZero_realProjectiveSpaceSpectralSequence_page_two_X`: its first page.
* `TauCeti.exists_linearEquiv_realProjectiveSpaceSpectralSequence_page_two_d_two_mul` and
  `TauCeti.realProjectiveSpaceSpectralSequence_page_two_d_eq_zero`: the first differentials of `ℝℙ²`
  with integer coefficients.
* `TauCeti.isZero_realProjectiveSpaceSpectralSequence_page_three_X_neg_four_two`,
  `TauCeti.nonempty_linearEquiv_realProjectiveSpaceSpectralSequence_page_three_X_neg_two_one` and
  `TauCeti.nonempty_linearEquiv_realProjectiveSpaceSpectralSequence_page_three_X_zero_zero`: its
  second page.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42, the cellular
  chain complex `ℤ ⟶ ℤ ⟶ ℤ` of `ℝℙ²`, with differentials `2` and `0`.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, the cells attached across the critical levels of a Morse function.
-/

public section

noncomputable section

open CategoryTheory Limits Set Function Projectivization
open scoped LinearAlgebra.Projectivization Manifold

universe v w

namespace TauCeti

variable {n : ℕ}

/-! ### The first page -/

variable {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{0} A] (R : A)

variable (n) in
/-- The spectral sequence of the critical-band filtration of `ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)`, with
coefficients in `R`: the spectral sequence of a filtered space
(`TauCeti.filteredSpaceSpectralSequence`) for the sublevels `{f ≤ q - 1 / 2}`, `q ∈ ℤ`, of the
standard moment function `f[v] = (∑ i, i * v i ^ 2) / ∑ i, v i ^ 2`. -/
abbrev realProjectiveSpaceSpectralSequence :=
  filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (n + 1) → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ))).comp
      (isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := n)).monotone)

/-- **The first page of the critical-band spectral sequence of `ℝℙⁿ`.** For `0 ≤ q ≤ n`, the
object at `(-2q, q)` on the first page (numbered `2`) of
`TauCeti.realProjectiveSpaceSpectralSequence` is the coefficient object `R`, one copy for the
critical point `[e_q]` of index `q` in the `q`th band. -/
theorem nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso {q : ℕ} (hq : q ≤ n) :
    Nonempty (((realProjectiveSpaceSpectralSequence n R).page 2).X (-(2 * q : ℕ), q) ≅ R) := by
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ)
    (w := fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ)) (Nat.cast_injective.comp Fin.val_injective)
  have ha := isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := n)
  obtain ⟨e⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha.monotone
    (ha.isCriticalBand q) (-(2 * q : ℕ), q) rfl q (by push_cast; ring)
  -- The only critical point of the `q`th band is `[e_q]`, of index `q`.
  have hidx (k : Fin (n + 1)) : manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ)
      (projectiveMomentFunction ℝ fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ))
      (mk ℝ (Pi.single k 1) (by simp)) = k := by
    rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul]
  refine ⟨e ≪≫ @coproductUniqueIso _ _ _
    ⟨⟨⟨⟨mk ℝ (Pi.single ⟨q, Nat.lt_succ_of_le hq⟩ 1) (by simp),
      mk_single_mem_criticalPoints_projectiveMomentFunction _ _, ?_⟩, hidx _⟩⟩, fun y ↦ ?_⟩ _⟩
  · obtain ⟨⟨x, hx, hxq⟩, -⟩ := y
    obtain ⟨k, rfl, hk⟩ :=
      exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast hx
        (Ioc_subset_Icc_self hxq)
    obtain rfl : k = ⟨q, Nat.lt_succ_of_le hq⟩ := Fin.ext (by exact_mod_cast hk)
    rfl
  · rw [mem_preimage, projectiveMomentFunction_mk_single]
    constructor <;> push_cast <;> linarith

/-- **The first page of the critical-band spectral sequence of `ℝℙⁿ` vanishes elsewhere.** The
object at `(p, q)` on the first page (numbered `2`) of
`TauCeti.realProjectiveSpaceSpectralSequence` is zero unless `p = -2q` and `0 ≤ q ≤ n`. -/
theorem isZero_realProjectiveSpaceSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (hpq : ¬(pq.1 = -2 * pq.2 ∧ 0 ≤ pq.2 ∧ pq.2 ≤ n)) :
    IsZero (((realProjectiveSpaceSpectralSequence n R).page 2).X pq) := by
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ)
    (w := fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ)) (Nat.cast_injective.comp Fin.val_injective)
  have ha := isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := n)
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos
  obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hle
  refine hf.isZero_filteredSpaceSpectralSequence_page_two_X R ha.monotone (ha.isCriticalBand _) pq
    rfl m hm fun x hx hxq hxm ↦ hpq ?_
  obtain ⟨k, rfl, hk⟩ := exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast
    hx (Ioc_subset_Icc_self hxq)
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul] at hxm
  have hkn := k.2
  lia

/-! ### The first differential of `ℝℙ²` with integer coefficients -/

section Integral

/-- The sublevel filtration `q ↦ {f ≤ q - 1 / 2}` of the standard moment function on `ℝℙ²`. -/
private abbrev rp2Sublevel : ℤ → Set (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) :=
  (fun b ↦ {x | projectiveMomentFunction ℝ (fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) x ≤ b}) ∘
    fun q : ℤ ↦ (q : ℝ) - 1 / 2

private theorem monotone_rp2Sublevel : Monotone rp2Sublevel :=
  (sublevel_mono _).comp
    (isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := 2)).monotone

/-- The relative homology `Hₘ(X i, X j; ℤ)` of two stages of the sublevel filtration of `ℝℙ²`. -/
private abbrev rp2H (j i : ℤ) (h : j ≤ i) (m : ℕ) : ModuleCat.{0} ℤ :=
  (TopPair.ofInclusion (monotone_rp2Sublevel h)).singularHomology (ModuleCat.of ℤ ℤ) m

/-- The spectral sequence of the sublevel filtration of `ℝℙ²`, with integer coefficients. -/
private abbrev rp2E := realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)

/-- The first page of `rp2E` at `(p, q)` is `Hₘ(X (q + 1), X q; ℤ)`, `p + q = -m`. -/
private def rp2FirstPageIso (p q : ℤ) (m : ℕ) (h : p + q = -m) :
    (rp2E.page 2).X (p, q) ≅ rp2H q (q + 1) (by lia) m :=
  filteredSpaceSpectralSequenceFirstPageXIso _ monotone_rp2Sublevel (p, q) q (q + 1) rfl rfl
    (p + q) rfl m h

private theorem nonempty_rp2H_linearEquiv (q : ℕ) (hq : q ≤ 2) :
    Nonempty (rp2H q (q + 1) (by lia) q ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso
    (n := 2) (ModuleCat.of ℤ ℤ) hq
  exact ⟨((rp2FirstPageIso _ _ q (by push_cast; ring)).symm ≪≫ e).toLinearEquiv⟩

private theorem isZero_rp2H (q : ℤ) (m : ℕ) (h : ¬(m = q ∧ 0 ≤ q ∧ q ≤ 2)) :
    IsZero (rp2H q (q + 1) (by lia) m) :=
  (isZero_realProjectiveSpaceSpectralSequence_page_two_X (n := 2)
    (ModuleCat.of ℤ ℤ) (-m - q, q) (by push_cast; lia)).of_iso
      (rp2FirstPageIso (-m - q) q m (by ring)).symm

/-- `ℝℙ²` is the stage `X 3` of the filtration, relative to the empty stage `X 0`. -/
private def rp2HomologyIso (m : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) ≅ rp2H 0 3 (by norm_num) m :=
  have hf (x : ℙ ℝ (Fin 3 → ℝ)) := projectiveMomentFunction_mem_Icc (a := 0) (b := 2)
    (fun i : Fin 3 ↦ Nat.cast_nonneg (i : ℕ)) (fun i ↦ by exact_mod_cast Nat.lt_succ_iff.1 i.2) x
  singularHomologyIsoSublevelPair (f := projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ))
    (a := ((0 : ℤ) : ℝ) - 1 / 2) (b := ((3 : ℤ) : ℝ) - 1 / 2) (by norm_num)
    (fun x ↦ by
      have := (hf x).1
      push_cast at this ⊢
      linarith)
    (fun x ↦ by
      have := (hf x).2
      push_cast at this ⊢
      linarith)
    _ m

/-- The triple `X 1 ⊆ X 2 ⊆ X 3` of the critical-band filtration of `ℝℙ²`. -/
private abbrev rp2T₁₂₃ : TopTriple :=
  TopTriple.ofInclusions (monotone_rp2Sublevel (by norm_num : (1 : ℤ) ≤ 2))
    (monotone_rp2Sublevel (by norm_num : (2 : ℤ) ≤ 3))

/-- The triple `X 0 ⊆ X 1 ⊆ X 3` of the critical-band filtration of `ℝℙ²`. -/
private abbrev rp2T₀₁₃ : TopTriple :=
  TopTriple.ofInclusions (monotone_rp2Sublevel (by norm_num : (0 : ℤ) ≤ 1))
    (monotone_rp2Sublevel (by norm_num : (1 : ℤ) ≤ 3))

/-- `H₂(X 3, X 1; ℤ) = 0`: the bands of `X 0 ⊆ X 1` carry no homology in degree `1`, and
`H₂(ℝℙ²; ℤ) = 0`. -/
private theorem isZero_rp2H_one_three_two : IsZero (rp2H 1 3 (by norm_num) 2) := by
  have h03₂ : IsZero (rp2H 0 3 (by norm_num) 2) :=
    (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := 2) ℤ
      (isRegular_iff_ne_zero.2 two_ne_zero).right even_two two_ne_zero).of_iso
      (rp2HomologyIso 2).symm
  exact (rp2T₀₁₃.singularHomology_exact_outer (ModuleCat.of ℤ ℤ) 2 1).isZero_of_both_isZero h03₂
    (isZero_rp2H 0 1 (by norm_num))

/-- The connecting map `H₂(X 3, X 2) ⟶ H₁(X 2, X 1)` of the triple `X 1 ⊆ X 2 ⊆ X 3` is
injective. -/
private theorem injective_rp2_singularHomologyδ :
    Function.Injective (rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact (rp2T₁₂₃.singularHomology_exact_outer _ 2 1).mono_g
    (isZero_rp2H_one_three_two.eq_of_src _ _)

/-- The map `H₁(X 2, X 1) ⟶ H₁(X 3, X 1)` of the triple `X 1 ⊆ X 2 ⊆ X 3` is onto, with kernel
the image of the connecting map. -/
private theorem surjective_rp2_innerToTotal :
    Function.Surjective
      (TopPair.singularHomologyMap (TopTriple.innerToTotal.app rp2T₁₂₃) (ModuleCat.of ℤ ℤ) 1).hom ∧
    LinearMap.range (rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom =
      LinearMap.ker
        (TopPair.singularHomologyMap (TopTriple.innerToTotal.app rp2T₁₂₃) (ModuleCat.of ℤ ℤ) 1).hom
    := by
  refine ⟨?_, (rp2T₁₂₃.singularHomology_exact_inner _ 2 1).moduleCat_range_eq_ker⟩
  rw [← ModuleCat.epi_iff_surjective]
  exact (rp2T₁₂₃.singularHomology_exact_total _ 1).epi_f
    ((isZero_rp2H 2 1 (by norm_num)).eq_of_tgt _ _)

/-- The connecting map `H₁(X 3, X 1) ⟶ H₀(X 1, X 0)` of the triple `X 0 ⊆ X 1 ⊆ X 3` vanishes:
its composite with the epimorphism `H₁(X 2, X 1) ⟶ H₁(X 3, X 1)` is a map between two groups
isomorphic to `ℤ` killing the nonzero image of the connecting map of `X 1 ⊆ X 2 ⊆ X 3`. -/
private theorem rp2_singularHomologyδ_one_zero_eq_zero :
    rp2T₀₁₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 = 0 := by
  obtain ⟨Φ₂⟩ : Nonempty (((TopTriple.outerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 2 :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := nonempty_rp2H_linearEquiv 2 le_rfl
  obtain ⟨Φ₁⟩ : Nonempty (((TopTriple.innerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 1 :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := nonempty_rp2H_linearEquiv 1 (by norm_num)
  obtain ⟨Φ₀⟩ : Nonempty (((TopTriple.innerPair.obj rp2T₀₁₃).singularHomology (ModuleCat.of ℤ ℤ) 0 :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := nonempty_rp2H_linearEquiv 0 (by norm_num)
  let δ := rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1
  let ι := TopPair.singularHomologyMap (TopTriple.innerToTotal.app rp2T₁₂₃) (ModuleCat.of ℤ ℤ) 1
  let δ' : (TopTriple.totalPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 1 ⟶
      (TopTriple.innerPair.obj rp2T₀₁₃).singularHomology (ModuleCat.of ℤ ℤ) 0 :=
    rp2T₀₁₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0
  have hu : δ.hom (Φ₂.symm 1) ≠ 0 := fun h ↦ Φ₂.symm.map_ne_zero_iff.2 one_ne_zero
    (injective_rp2_singularHomologyδ (h.trans (map_zero _).symm))
  have : Module.IsTorsionFree ℤ
      ((TopTriple.innerPair.obj rp2T₀₁₃).singularHomology (ModuleCat.of ℤ ℤ) 0 : ModuleCat ℤ) :=
    Φ₀.injective.moduleIsTorsionFree _ Φ₀.map_smul
  have h : (ι ≫ δ').hom = 0 := Φ₁.linearMap_eq_zero_of_apply_eq_zero (ι ≫ δ').hom hu (by
    have h0 : δ ≫ ι = 0 := rp2T₁₂₃.singularHomologyδ_comp _ 2 1
    calc (ι ≫ δ').hom (δ.hom (Φ₂.symm 1)) = ((δ ≫ ι) ≫ δ').hom (Φ₂.symm 1) := by
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      _ = 0 := by rw [h0, zero_comp, ModuleCat.hom_zero, LinearMap.zero_apply])
  have : Epi ι := by
    rw [ModuleCat.epi_iff_surjective]
    exact surjective_rp2_innerToTotal.1
  have h' : ι ≫ δ' = 0 := ModuleCat.hom_ext (h.trans ModuleCat.hom_zero.symm)
  exact (cancel_epi ι).1 (h'.trans comp_zero.symm)

/-- `H₁(X 3, X 1; ℤ) ≅ ℤ/2`: the quotient map from `H₁(X 3, X 0) = H₁(ℝℙ²; ℤ) ≅ ℤ/2` is an
isomorphism, since the band of `X 0 ⊆ X 1` has no homology in degree `1` and the connecting map
out of `H₁(X 3, X 1)` vanishes. -/
private theorem nonempty_rp2H_one_three_linearEquiv :
    Nonempty (((TopTriple.totalPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 1 :
      ModuleCat ℤ) ≃ₗ[ℤ] ZMod 2) := by
  let π₁ := TopPair.singularHomologyMap (TopTriple.totalToOuter.app rp2T₀₁₃) (ModuleCat.of ℤ ℤ) 1
  have : Mono π₁ := (rp2T₀₁₃.singularHomology_exact_total _ 1).mono_g
    ((isZero_rp2H 0 1 (by norm_num)).eq_of_src _ _)
  have : Epi π₁ := (rp2T₀₁₃.singularHomology_exact_outer _ 1 0).epi_f
    rp2_singularHomologyδ_one_zero_eq_zero
  have : IsIso π₁ := isIso_of_mono_of_epi _
  exact ⟨(asIso π₁).symm.toLinearEquiv ≪≫ₗ (rp2HomologyIso 1).symm.toLinearEquiv ≪≫ₗ
    RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd (N := 2) odd_one
      (by norm_num)⟩

/-- **The integral computation behind the first differential of `ℝℙ²`.** With integer
coefficients, the connecting map `δ : H₂(X 3, X 2) ⟶ H₁(X 2, X 1)` of the triple
`X 1 ⊆ X 2 ⊆ X 3` is multiplication by `2` between two copies of `ℤ`. -/
private theorem exists_rp2_singularHomologyδ :
    ∃ (Φ₂ : ((TopTriple.outerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 2 :
        ModuleCat ℤ) ≃ₗ[ℤ] ℤ)
      (Φ₁ : ((TopTriple.innerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 1 :
        ModuleCat ℤ) ≃ₗ[ℤ] ℤ),
      ∀ x, Φ₁ ((rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom x) = 2 * Φ₂ x := by
  obtain ⟨Φ₂⟩ : Nonempty (((TopTriple.outerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 2 :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := nonempty_rp2H_linearEquiv 2 le_rfl
  obtain ⟨Φ₁⟩ : Nonempty (((TopTriple.innerPair.obj rp2T₁₂₃).singularHomology (ModuleCat.of ℤ ℤ) 1 :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := nonempty_rp2H_linearEquiv 1 (by norm_num)
  obtain ⟨Ψ⟩ := nonempty_rp2H_one_three_linearEquiv
  obtain ⟨hι, hker⟩ := surjective_rp2_innerToTotal
  set δ := rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1
  set ι := TopPair.singularHomologyMap (TopTriple.innerToTotal.app rp2T₁₂₃) (ModuleCat.of ℤ ℤ) 1
  -- `δ` is multiplication by `m = Φ₁ (δ (Φ₂.symm 1))` in the two copies of `ℤ`.
  set m := Φ₁ (δ.hom (Φ₂.symm 1))
  have hm (x) : Φ₁ (δ.hom x) = m * Φ₂ x := by
    rw [Φ₂.linearMap_apply_eq_smul δ.hom x, Φ₁.map_smul, smul_eq_mul]
    exact mul_comm _ _
  -- `m` divides `2`, since twice the generator of `H₁(X 2, X 1)` dies in `H₁(X 3, X 1) ≅ ℤ/2`.
  have hdvd : m ∣ 2 := by
    have h2 : Φ₁.symm 2 ∈ LinearMap.ker ι.hom := by
      rw [LinearMap.mem_ker, ← Ψ.map_eq_zero_iff, (by norm_num : (2 : ℤ) = 1 + 1), map_add,
        map_add, map_add]
      exact (by decide : ∀ z : ZMod 2, z + z = 0) _
    obtain ⟨x, hx⟩ := hker ▸ h2
    exact ⟨Φ₂ x, by rw [← hm, hx, LinearEquiv.apply_symm_apply]⟩
  -- `m` is not a unit, since otherwise `δ` would be onto and `H₁(X 3, X 1)` would vanish.
  have hunit : ¬IsUnit m := by
    rintro ⟨u, hu⟩
    obtain ⟨z, hz⟩ := hι (Ψ.symm 1)
    have : z ∈ LinearMap.ker ι.hom := by
      rw [← hker]
      refine ⟨Φ₂.symm (↑u⁻¹ * Φ₁ z), Φ₁.injective ?_⟩
      rw [hm, LinearEquiv.apply_symm_apply, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [LinearMap.mem_ker, hz] at this
    exact one_ne_zero (Ψ.symm.injective (this.trans (map_zero _).symm))
  have hm2 : m = 2 ∨ m = -2 := by
    have h1 : m.natAbs ≠ 1 := fun h ↦ hunit (Int.isUnit_iff_natAbs_eq.2 h)
    rcases (Nat.dvd_prime Nat.prime_two).1 (Int.natAbs_dvd_natAbs.2 hdvd) with h | h
    · exact absurd h h1
    · exact Int.natAbs_eq_iff.1 h
  rcases hm2 with h | h
  · exact ⟨Φ₂, Φ₁, fun x ↦ by rw [hm, h]⟩
  · refine ⟨Φ₂.trans (LinearEquiv.neg ℤ), Φ₁, fun x ↦ ?_⟩
    rw [LinearEquiv.trans_apply, hm, h]
    simp

end Integral

/-! ### The first two pages for `ℝℙ²` with integer coefficients -/

/-- The first differentials go from `pq` to `pq + (2, -1)`. -/
private theorem prev_page_two {pq pq' : ℤ × ℤ} (h : pq + (2, -1) = pq') :
    (ComplexShape.up' ((2 : ℤ), (1 : ℤ) - 2)).prev pq' = pq :=
  ComplexShape.prev_eq' _ (ComplexShape.up'_mk _ _ _ (by rw [← h]; norm_num))

/-- The first differentials go from `pq` to `pq + (2, -1)`. -/
private theorem next_page_two {pq pq' : ℤ × ℤ} (h : pq + (2, -1) = pq') :
    (ComplexShape.up' ((2 : ℤ), (1 : ℤ) - 2)).next pq = pq' :=
  ComplexShape.next_eq' _ (ComplexShape.up'_mk _ _ _ (by rw [← h]; norm_num))

/-- The first differential of `rp2E` from `(-4, 2)` to `(-2, 1)` is the connecting map of the
triple `X 1 ⊆ X 2 ⊆ X 3`. -/
private theorem rp2E_page_two_d_neg_four_two :
    (rp2E.page 2).d (-4, 2) (-2, 1) = (rp2FirstPageIso (-4) 2 2 (by norm_num)).hom ≫
      rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1 ≫
        (rp2FirstPageIso (-2) 1 1 (by norm_num)).inv :=
  filteredSpaceSpectralSequence_first_page_d_eq _ monotone_rp2Sublevel 2 (-4) 1 (by norm_num)

/-- **The first differential of `ℝℙ²` is multiplication by `2`.** With integer coefficients, the
objects at `(-4, 2)` and `(-2, 1)` on the first page (numbered `2`) of
`TauCeti.realProjectiveSpaceSpectralSequence` for `ℝℙ²` are copies of `ℤ`, and in suitable
identifications with `ℤ` the differential `(-4, 2) ⟶ (-2, 1)` between them is multiplication by
`2`. -/
theorem exists_linearEquiv_realProjectiveSpaceSpectralSequence_page_two_d_two_mul :
    ∃ (e₂ : (((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-4, 2) :
        ModuleCat ℤ) ≃ₗ[ℤ] ℤ)
      (e₁ : (((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-2, 1) :
        ModuleCat ℤ) ≃ₗ[ℤ] ℤ),
      ∀ x, e₁ ((((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
        (-4, 2) (-2, 1)).hom x) = 2 * e₂ x := by
  obtain ⟨Φ₂, Φ₁, hΦ⟩ := exists_rp2_singularHomologyδ
  let ε₂ := (rp2FirstPageIso (-4) 2 2 (by norm_num)).toLinearEquiv
  let ε₁ := (rp2FirstPageIso (-2) 1 1 (by norm_num)).toLinearEquiv
  refine ⟨ε₂ ≪≫ₗ Φ₂, ε₁ ≪≫ₗ Φ₁, fun x ↦ ?_⟩
  -- The underlying linear map of a composite in `ModuleCat` is the composite of linear maps, by
  -- definition, and `ε₁ ≪≫ₗ Φ₁` applies `ε₁` and then `Φ₁`.
  have hx : ((rp2E.page 2).d (-4, 2) (-2, 1)).hom x =
      ε₁.symm ((rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom (ε₂ x)) := by
    rw [rp2E_page_two_d_neg_four_two]
    rfl
  calc (ε₁ ≪≫ₗ Φ₁) (((rp2E.page 2).d (-4, 2) (-2, 1)).hom x)
      = Φ₁ (ε₁ (ε₁.symm ((rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom (ε₂ x)))) := by
        rw [hx]
        rfl
    _ = Φ₁ ((rp2T₁₂₃.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1).hom (ε₂ x)) :=
        congrArg Φ₁ (ε₁.apply_symm_apply _)
    _ = 2 * (ε₂ ≪≫ₗ Φ₂) x := hΦ _

/-- **The first differential of `ℝℙ²` out of the saddle vanishes.** With integer coefficients, the
differential `(-2, 1) ⟶ (0, 0)` on the first page (numbered `2`) of
`TauCeti.realProjectiveSpaceSpectralSequence` for `ℝℙ²` is zero. -/
theorem realProjectiveSpaceSpectralSequence_page_two_d_eq_zero :
    ((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d (-2, 1) (0, 0) = 0 := by
  -- The composite with the injective differential `(-4, 2) ⟶ (-2, 1)` vanishes, and the source and
  -- target are copies of `ℤ`.
  obtain ⟨e₂, e₁, he⟩ := exists_linearEquiv_realProjectiveSpaceSpectralSequence_page_two_d_two_mul
  obtain ⟨e₀⟩ := nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso (n := 2)
    (ModuleCat.of ℤ ℤ) (q := 0) (Nat.zero_le _)
  have hu : ((rp2E.page 2).d (-4, 2) (-2, 1)).hom (e₂.symm 1) ≠ 0 := fun h ↦ by
    have := he (e₂.symm 1)
    rw [h, map_zero, LinearEquiv.apply_symm_apply] at this
    norm_num at this
  have : Module.IsTorsionFree ℤ ((rp2E.page 2).X (0, 0) : ModuleCat ℤ) :=
    e₀.toLinearEquiv.injective.moduleIsTorsionFree _ e₀.toLinearEquiv.map_smul
  refine ModuleCat.hom_ext (e₁.linearMap_eq_zero_of_apply_eq_zero _ hu ?_)
  have h := congrArg (fun φ ↦ φ.hom (e₂.symm 1)) ((rp2E.page 2).d_comp_d (-4, 2) (-2, 1) (0, 0))
  rwa [ModuleCat.hom_zero, LinearMap.zero_apply] at h

/-- The first differential `(-4, 2) ⟶ (-2, 1)` of `rp2E` is injective. -/
private theorem injective_rp2E_page_two_d :
    Function.Injective ((rp2E.page 2).d (-4, 2) (-2, 1)).hom := by
  obtain ⟨e₂, e₁, he⟩ := exists_linearEquiv_realProjectiveSpaceSpectralSequence_page_two_d_two_mul
  intro x y hxy
  have h := he x
  rw [hxy, he y] at h
  exact e₂.injective (by lia)

/-- **The second page of `ℝℙ²` vanishes in degree `2`.** With integer coefficients, the object at
`(-4, 2)` on the second page (numbered `3`) of `TauCeti.realProjectiveSpaceSpectralSequence` for
`ℝℙ²` is zero. -/
theorem isZero_realProjectiveSpaceSpectralSequence_page_three_X_neg_four_two :
    IsZero (((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (-4, 2)) := by
  -- The first differential out of `(-4, 2)` is injective, and nothing maps into `(-4, 2)`.
  have hzero : IsZero ((rp2E.page 2).X (-6, 3)) :=
    isZero_realProjectiveSpaceSpectralSequence_page_two_X (n := 2) _ (-6, 3) (by norm_num)
  have hmono : Mono ((rp2E.page 2).d (-4, 2) (-2, 1)) :=
    (ModuleCat.mono_iff_injective _).2 injective_rp2E_page_two_d
  have hexact : (rp2E.page 2).ExactAt (-4, 2) := by
    rw [(rp2E.page 2).exactAt_iff' (-6, 3) (-4, 2) (-2, 1) (prev_page_two (by norm_num))
      (next_page_two (by norm_num))]
    exact (ShortComplex.exact_iff_mono _ (hzero.eq_of_src _ _)).2 hmono
  exact (((rp2E.page 2).exactAt_iff_isZero_homology _).1 hexact).of_iso
    (rp2E.iso 2 3 (-4, 2)).symm

/-- **The second page of `ℝℙ²` is `ℤ/2` in degree `1`.** With integer coefficients, the object at
`(-2, 1)` on the second page (numbered `3`) of `TauCeti.realProjectiveSpaceSpectralSequence` for
`ℝℙ²` is `ℤ/2`, while on the first page it is `ℤ`
(`TauCeti.nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso`). -/
theorem nonempty_linearEquiv_realProjectiveSpaceSpectralSequence_page_three_X_neg_two_one :
    Nonempty ((((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (-2, 1) :
      ModuleCat ℤ) ≃ₗ[ℤ] ZMod 2) := by
  obtain ⟨e₂, e₁, he⟩ := exists_linearEquiv_realProjectiveSpaceSpectralSequence_page_two_d_two_mul
  -- The second page at `(-2, 1)` is the cokernel of `d : (-4, 2) ⟶ (-2, 1)`, since the first
  -- differential out of `(-2, 1)` vanishes.
  let i₁ : (rp2E.page 2).homology (-2, 1) ≅ (rp2E.page 2).opcycles (-2, 1) :=
    (rp2E.page 2).isoHomologyι (-2, 1) (0, 0) (next_page_two (by norm_num))
      realProjectiveSpaceSpectralSequence_page_two_d_eq_zero
  let i₂ : (rp2E.page 2).opcycles (-2, 1) ≅ cokernel ((rp2E.page 2).d (-4, 2) (-2, 1)) :=
    ((rp2E.page 2).opcyclesIsCokernel (-4, 2) (-2, 1)
      (prev_page_two (by norm_num))).coconePointUniqueUpToIso (colimit.isColimit _)
  -- The quotient of `ℤ` by the image of multiplication by `2` is `ℤ/2`.
  let φ : ((rp2E.page 2).X (-2, 1) : ModuleCat ℤ) →ₗ[ℤ] ZMod 2 :=
    LinearMap.toSpanSingleton ℤ (ZMod 2) 1 ∘ₗ e₁.toLinearMap
  have hφ (y) : φ y = 0 ↔ (2 : ℤ) ∣ e₁ y := by
    simp [φ, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective φ := fun z ↦ by
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨e₁.symm k, by simp [φ]⟩
  have hker : LinearMap.range ((rp2E.page 2).d (-4, 2) (-2, 1)).hom = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_ker, hφ]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e₂ x, he x⟩
    · rintro ⟨k, hk⟩
      exact ⟨e₂.symm k, e₁.injective (by rw [he, LinearEquiv.apply_symm_apply, hk])⟩
  exact ⟨((rp2E.iso 2 3 (-2, 1)).symm ≪≫ i₁ ≪≫ i₂ ≪≫
    ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker ≪≫ₗ φ.quotKerEquivOfSurjective hsurj⟩

/-- **The second page of `ℝℙ²` is `ℤ` in degree `0`.** With integer coefficients, the object at
`(0, 0)` on the second page (numbered `3`) of `TauCeti.realProjectiveSpaceSpectralSequence` for
`ℝℙ²` is `ℤ`. -/
theorem nonempty_linearEquiv_realProjectiveSpaceSpectralSequence_page_three_X_zero_zero :
    Nonempty ((((realProjectiveSpaceSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (0, 0) :
      ModuleCat ℤ) ≃ₗ[ℤ] ℤ) := by
  -- Both first differentials at `(0, 0)` vanish.
  obtain ⟨e₀⟩ := nonempty_realProjectiveSpaceSpectralSequence_page_two_X_iso (n := 2)
    (ModuleCat.of ℤ ℤ) (q := 0) (Nat.zero_le _)
  have hzero : IsZero ((rp2E.page 2).X (2, -1)) :=
    isZero_realProjectiveSpaceSpectralSequence_page_two_X (n := 2) _ (2, -1) (by norm_num)
  exact ⟨((rp2E.iso 2 3 (0, 0)).symm ≪≫
    ((rp2E.page 2).isoHomologyπ (-2, 1) (0, 0) (prev_page_two (by norm_num))
      realProjectiveSpaceSpectralSequence_page_two_d_eq_zero).symm ≪≫
    (rp2E.page 2).iCyclesIso (0, 0) (2, -1) (next_page_two (by norm_num))
      (hzero.eq_of_tgt _ _) ≪≫ e₀).toLinearEquiv⟩

end TauCeti
