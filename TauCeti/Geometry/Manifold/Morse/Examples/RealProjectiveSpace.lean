/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence
import TauCeti.Algebra.Category.ModuleCat.Int

/-!
# The critical-band spectral sequence of real projective space

The moment function `f[x] = (∑ i, i xᵢ²) / ∑ i, xᵢ²` on `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`
(`TauCeti.projectiveMomentFunction` with the weights `0, 1, …, N`) is a Morse function whose
critical points are the coordinate points `[eₖ]`, at the level `k` and of index `k`. Its sublevels
`{f ≤ q - 1 / 2}` cut `ℝℙᴺ` between these levels, and
`TauCeti.realProjectiveMomentSpectralSequence N` is the spectral sequence of this critical-band
filtration with integer coefficients (`TauCeti.filteredSpaceSpectralSequence`). This file computes
its first two pages. They show that the first page is the relative homology of the bands, not yet
the homology of `ℝℙᴺ`: its differential can be nonzero. For `ℝℙ²` (`N = 2`) the first page is
`ℤ` in the degrees `0`, `1`, `2`, the differential from degree `2` to degree `1` is `2`, and the
second page is `ℤ`, `ℤ / 2`, `0`.

Pages are numbered as in `CochainComplex.spectralSequence`: the first page is the page `2` and the
second page is the page `3`, and singular chains of degree `n` sit in total degree `p + q = -n`, so
the `k`th band in degree `k` sits at `(-2k, k)`.

* **The first page** is `ℤ` at `(-2k, k)` for `0 ≤ k ≤ N`, one copy for the critical point of the
  `k`th band (`TauCeti.nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso`), and zero
  everywhere else (`TauCeti.isZero_realProjectiveMomentSpectralSequence_page_two_X`).
* **The second page** at `(-2k, k)` is `Hₖ(ℝℙᴺ; ℤ)`
  (`TauCeti.realProjectiveMomentSpectralSequencePageThreeXIso`): `ℤ` for `k = 0`
  (`TauCeti.realProjectiveMomentSpectralSequencePageThreeXZeroIso`) and for odd `k = N`
  (`TauCeti.realProjectiveMomentSpectralSequencePageThreeXTopIsoOfOdd`), `ℤ / 2` for odd `k < N`
  (`TauCeti.realProjectiveMomentSpectralSequencePageThreeXIsoOfOdd`), and `0` for even `k > 0`
  (`TauCeti.isZero_realProjectiveMomentSpectralSequence_page_three_X_of_even`). It vanishes off
  these positions (`TauCeti.isZero_realProjectiveMomentSpectralSequence_page_three_X`).
* **The first differential** out of an odd band vanishes
  (`TauCeti.realProjectiveMomentSpectralSequence_page_two_d_eq_zero_of_odd`), and out of an even
  band `2 ≤ k ≤ N` it is multiplication by `±2` in any identification with `ℤ`
  (`TauCeti.realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul_or_neg_two_smul`), and by
  `2` in a suitable one
  (`TauCeti.exists_realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul`). So the first
  page is a copy of the cellular chain complex of `ℝℙᴺ`.

The differentials are not computed from attaching maps. Every nonzero object of the first page
lies on the line `p = -2q`, while a differential of a page `s ≥ 3` has bidegree `(s, 1 - s)` and
leaves that line, so the positions `(-2k, k)` admit no differential on the later pages. So the
second page at `(-2k, k)` is the graded piece of the filtration of
`Hₖ(ℝℙᴺ; ℤ)` by the images of the sublevels, which is all of `Hₖ(ℝℙᴺ; ℤ)`, the other graded
pieces in degree `k` vanishing. The second page is also the homology of the first, a complex
`ℤ ⟵ ℤ ⟵ ⋯ ⟵ ℤ`, and the known homology of `ℝℙᴺ`
(`TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd`) forces its differentials. A
nonzero endomorphism of `ℤ` is injective, so a differential out of an odd band, where the second
page does not vanish, is zero. The cokernel of an endomorphism `n ≠ 0` of `ℤ` has `|n|` elements,
and that of `0` is the infinite group `ℤ`, so a differential out of an even band, whose cokernel is
`ℤ / 2`, is `±2`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.5, the cell structure of a Morse function).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42 (the cellular
  chain complex of `ℝℙᴺ`, with differentials alternately `0` and `2`).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits Set Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable (N : ℕ)

/-- The moment function `f[x] = (∑ i, i xᵢ²) / ∑ i, xᵢ²` on `ℝℙᴺ`. -/
local notation "𝔣[" N "]" => projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)

private theorem injective_weights : Function.Injective fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ) :=
  Nat.cast_injective.comp Fin.val_injective

private theorem mem_Icc_projectiveMomentFunction (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    𝔣[N] x ∈ Icc 0 (N : ℝ) :=
  projectiveMomentFunction_mem_Icc (fun i ↦ ⟨by positivity, by exact_mod_cast i.is_le⟩) x

variable {N} in
/-- The critical points of the moment function are the coordinate points `[eₖ]`, at the level `k`
and of index `k`. -/
private theorem exists_eq_of_mem_criticalPoints {x : ℙ ℝ (Fin (N + 1) → ℝ)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin N → ℝ) 𝔣[N]) :
    ∃ k : Fin (N + 1), x = mk ℝ (Pi.single k 1) (by simp) ∧ 𝔣[N] x = (k : ℕ) ∧
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) 𝔣[N] x = k := by
  rw [criticalPoints_projectiveMomentFunction (injective_weights N)] at hx
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k, rfl, by rw [projectiveMomentFunction_mk_single], ?_⟩
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul]

/-- The cut values `q - 1 / 2` are monotone. -/
private theorem monotone_cut : Monotone fun q : ℤ ↦ (q : ℝ) - 1 / 2 :=
  fun _ _ h ↦ sub_le_sub_right (Int.cast_le.2 h) _

/-- The cut `q ↦ q - 1 / 2` is a critical-band cut of the moment function. -/
private theorem isCriticalBandCut :
    IsCriticalBandCut 𝓘(ℝ, Fin N → ℝ) 𝔣[N] fun q : ℤ ↦ (q : ℝ) - 1 / 2 := by
  refine ⟨fun q ↦ ⟨(isClosed_Icc.preimage
    (contMDiff_projectiveMomentFunction (r := 0) _).continuous).isCompact, q, ?_, ?_⟩⟩
  · push_cast
    constructor <;> linarith
  · intro x hx hxq
    obtain ⟨k, -, hk, -⟩ := exists_eq_of_mem_criticalPoints hx
    rw [hk] at hxq ⊢
    push_cast at hxq
    have h₁ : ((q : ℤ) : ℝ) < (k : ℕ) + 1 := by linarith [hxq.1]
    have h₂ : ((k : ℕ) : ℝ) < q + 1 := by linarith [hxq.2]
    have : (k : ℤ) = q := by
      have h₁' : (q : ℤ) < (k : ℕ) + 1 := by exact_mod_cast h₁
      have h₂' : ((k : ℕ) : ℤ) < q + 1 := by exact_mod_cast h₂
      lia
    exact_mod_cast this

/-- **The spectral sequence of the critical-band filtration of `ℝℙᴺ`.** The sublevels
`{f ≤ q - 1 / 2}` of the moment function `f[x] = (∑ i, i xᵢ²) / ∑ i, xᵢ²` filter
`ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`, and this is the spectral sequence of the induced filtration of the
singular chains with integer coefficients. -/
abbrev realProjectiveMomentSpectralSequence :=
  filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) (ModuleCat.of ℤ ℤ)
    ((sublevel_mono 𝔣[N]).comp fun _ _ h ↦ sub_le_sub_right (Int.cast_le.2 h) (1 / 2 : ℝ))

local notation "𝔈[" N "]" => realProjectiveMomentSpectralSequence N

/-! ### The first page -/

/-- **The first page vanishes off the diagonal.** On the first page (numbered `2`) of
`TauCeti.realProjectiveMomentSpectralSequence N`, only the positions `(-2k, k)` with `0 ≤ k ≤ N`
can be nonzero. -/
theorem isZero_realProjectiveMomentSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (h : ¬(pq.1 = -2 * pq.2 ∧ 0 ≤ pq.2 ∧ pq.2 ≤ N)) :
    IsZero (((𝔈[N]).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  refine (isMorse_projectiveMomentFunction
    (injective_weights N)).isZero_filteredSpaceSpectralSequence_page_two_X _ monotone_cut
    ((isCriticalBandCut N).isCriticalBand pq.2) pq rfl n hn ?_
  intro x hx hfx hidx
  obtain ⟨k, -, hk, hki⟩ := exists_eq_of_mem_criticalPoints hx
  rw [hk] at hfx
  rw [hki] at hidx
  have h₁ : (pq.2 : ℝ) < (k : ℕ) + 1 / 2 := by linarith [hfx.1]
  have h₂ : ((k : ℕ) : ℝ) < pq.2 + 1 := by push_cast at hfx; linarith [hfx.2]
  have h₁' : pq.2 < ((k : ℕ) : ℤ) + 1 := by
    have : (pq.2 : ℝ) < ((k : ℕ) : ℤ) + 1 := by push_cast; linarith
    exact_mod_cast this
  have h₂' : ((k : ℕ) : ℤ) < pq.2 + 1 := by exact_mod_cast h₂
  apply h
  lia

/-- **The first page on the diagonal.** For `0 ≤ k ≤ N`, the object at `(-2k, k)` on the first
page (numbered `2`) of `TauCeti.realProjectiveMomentSpectralSequence N` is `ℤ`. -/
theorem nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso {k : ℤ} (h₀ : 0 ≤ k)
    (hk : k ≤ N) : Nonempty (((𝔈[N]).page 2).X (-2 * k, k) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
  obtain ⟨e⟩ := (isMorse_projectiveMomentFunction
    (injective_weights N)).nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma
    (ModuleCat.of ℤ ℤ) monotone_cut ((isCriticalBandCut N).isCriticalBand k) (-2 * k, k) rfl k
    (by ring)
  let k' : Fin (N + 1) := ⟨k, by lia⟩
  have hx₀ : mk ℝ (Pi.single k' 1) (by simp) ∈ criticalPoints 𝓘(ℝ, Fin N → ℝ) 𝔣[N] :=
    mk_single_mem_criticalPoints_projectiveMomentFunction _ _
  -- The index type of the coproduct has exactly one element, `[eₖ]`.
  refine ⟨e ≪≫ @coproductUniqueIso _ _ _ ?_ fun _ ↦ ModuleCat.of ℤ ℤ⟩
  refine ⟨⟨⟨⟨_, hx₀, ?_⟩, ?_⟩⟩, ?_⟩
  · rw [mem_preimage, projectiveMomentFunction_mk_single]
    simp only [k', mem_Ioc]
    push_cast
    constructor <;> linarith
  · rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul]
  · rintro ⟨⟨x, hx, hxb⟩, hxi⟩
    obtain ⟨j, rfl, hj, hji⟩ := exists_eq_of_mem_criticalPoints hx
    have : j = k' := Fin.ext (by rw [hji] at hxi; exact hxi)
    subst this
    rfl

/-! ### The second page -/

/-- The spectral object of the filtration, whose abutment is the homology of `ℝℙᴺ`. -/
local notation "𝔄[" N "]" => CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
  (monotone_singularChainFiltration (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) (ModuleCat.of ℤ ℤ)
    (Monotone.comp (sublevel_mono 𝔣[N]) monotone_cut)))

private theorem sublevel_cut_zero :
    ((fun b ↦ {x | 𝔣[N] x ≤ b}) ∘ fun q : ℤ ↦ (q : ℝ) - 1 / 2) 0 = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := (mem_Icc_projectiveMomentFunction N x).1
    simp only [Function.comp_apply, mem_ofPred_eq, Int.cast_zero] at hx
    linarith

private theorem sublevel_cut_top :
    ((fun b ↦ {x | 𝔣[N] x ≤ b}) ∘ fun q : ℤ ↦ (q : ℝ) - 1 / 2) (N + 1) = univ :=
  eq_univ_of_forall fun x ↦ by
    have := (mem_Icc_projectiveMomentFunction N x).2
    simp only [Function.comp_apply, mem_ofPred_eq]
    push_cast
    linarith

/-- On a late enough page `r`, the position `pq` carries a graded piece of the homology of
`ℝℙᴺ`. -/
private def pageXIsoCokernelAbutmentFiltrationMap (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (h₀ : pq.2 + 2 ≤ r) (hN : N + 2 ≤ pq.2 + r) :
    ((𝔈[N]).page r).X pq ≅ cokernel ((𝔄[N]).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  filteredSpaceSpectralSequencePageXIsoGradedOfFinite (a := 0) (b := N + 1) _ _
    (sublevel_cut_zero N) (sublevel_cut_top N) r hr pq (by lia) (by lia)

/-- Off the diagonal, the graded pieces of the homology of `ℝℙᴺ` vanish. -/
private theorem isZero_cokernel_abutmentFiltrationMap {j m : ℤ} (h₀ : 0 ≤ j) (hN : j ≤ N)
    (hm : m ≠ -j) : IsZero (cokernel ((𝔄[N]).abutmentFiltrationMap j m)) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + j := ⟨m - j, by lia⟩
  exact ((𝔈[N]).isZero_page_X_of_le le_rfl
    (isZero_realProjectiveMomentSpectralSequence_page_two_X N (p, j) (by simp only; lia))
    (N + 3) (by lia)).of_iso
      (pageXIsoCokernelAbutmentFiltrationMap N (N + 3) (by lia) (p, j) (by simp only; lia)
        (by simp only; lia)).symm

/-- On the diagonal, the graded piece of `Hₖ(ℝℙᴺ)` is everything. -/
private def cokernelAbutmentFiltrationMapIsoSingularHomology (k : ℕ) :
    cokernel ((𝔄[N]).abutmentFiltrationMap k (-k)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) :=
  (𝔄[N]).cokernelAbutmentFiltrationMapIsoAbutment (a := 0) (b := N + 1) (n := -k)
    (CochainComplex.isZero_filtrationAbutmentFiltration _ _
      (singularChainFiltration_eq_bot _ (sublevel_cut_zero N)) _)
    (CochainComplex.isIso_filtrationAbutmentFiltrationι _ _
      (singularChainFiltration_eq_top _ (sublevel_cut_top N)) _)
    (fun j hj₀ hjN hjk ↦ isZero_cokernel_abutmentFiltrationMap N hj₀ (by lia) (by lia)) ≪≫
  filteredSpaceAbutmentIso _ (Monotone.comp (sublevel_mono 𝔣[N]) monotone_cut) k

/-- On the second page (numbered `3`), every position joined to `(-2k, k)` by a differential of a
page `s ≥ 3` vanishes. -/
private theorem isZero_page_three_X_of_rel (k : ℤ) (s : ℤ) (hs : 3 ≤ s) (pq' : ℤ × ℤ)
    (h : (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel (-2 * k, k) pq' ∨
      (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq' (-2 * k, k)) :
    IsZero (((𝔈[N]).page 3).X pq') := by
  refine (𝔈[N]).isZero_page_X_of_le le_rfl
    (isZero_realProjectiveMomentSpectralSequence_page_two_X N pq' ?_) 3 (by norm_num)
  rintro ⟨h₁, -⟩
  rcases h with h | h <;> simp only [ComplexShape.up'_Rel, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add] at h <;> lia

/-- **The second page is the homology of `ℝℙᴺ`.** The object at `(-2k, k)` on the second page
(numbered `3`) of `TauCeti.realProjectiveMomentSpectralSequence N` is `Hₖ(ℝℙᴺ; ℤ)`: it is the
object at `(-2k, k)` on the page `k + N + 3`, which is the `k`th graded piece of the filtration
of `Hₖ(ℝℙᴺ; ℤ)` by the images of the sublevels, and that graded piece is all of
`Hₖ(ℝℙᴺ; ℤ)`. -/
def realProjectiveMomentSpectralSequencePageThreeXIso (k : ℕ) :
    ((𝔈[N]).page 3).X (-2 * k, k) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) :=
  ((𝔈[N]).pageXIsoOfLEOfIsZero (r := 3) (by norm_num)
      (fun s hs pq' h ↦ isZero_page_three_X_of_rel N k s hs pq' h) (k + N + 3) (by lia)).symm ≪≫
    pageXIsoCokernelAbutmentFiltrationMap N (k + N + 3) (by lia) _ (by simp only; lia)
      (by simp only; lia) ≪≫
    eqToIso (congrArg (fun m ↦ cokernel ((𝔄[N]).abutmentFiltrationMap k m)) (by simp; ring)) ≪≫
    cokernelAbutmentFiltrationMapIsoSingularHomology N k

/-- **The second page in degree `0`.** The object at `(0, 0)` on the second page (numbered `3`)
of `TauCeti.realProjectiveMomentSpectralSequence N` is `H₀(ℝℙᴺ; ℤ) = ℤ`. -/
def realProjectiveMomentSpectralSequencePageThreeXZeroIso :
    ((𝔈[N]).page 3).X (0, 0) ≅ ModuleCat.of ℤ ℤ :=
  realProjectiveMomentSpectralSequencePageThreeXIso N 0 ≪≫
    (RealProjectiveSpace.singularHomologyIsoProjectivization N (ModuleCat.of ℤ ℤ) 0).symm ≪≫
    (RealProjectiveSpace.singularHomologyZeroLinearEquiv ℤ).toModuleIso

/-- **The second page in odd degrees below `N`.** For odd `k < N`, the object at `(-2k, k)` on
the second page (numbered `3`) of `TauCeti.realProjectiveMomentSpectralSequence N` is
`Hₖ(ℝℙᴺ; ℤ) = ℤ / 2`. -/
def realProjectiveMomentSpectralSequencePageThreeXIsoOfOdd {k : ℕ} (hk : Odd k) (hkN : k < N) :
    ((𝔈[N]).page 3).X (-2 * k, k) ≅ ModuleCat.of ℤ (ZMod 2) :=
  realProjectiveMomentSpectralSequencePageThreeXIso N k ≪≫
    (RealProjectiveSpace.singularHomologyIsoProjectivization N (ModuleCat.of ℤ ℤ) k).symm ≪≫
    (RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd hk hkN).toModuleIso

/-- **The second page in the top degree.** For odd `N`, the object at `(-2N, N)` on the second
page (numbered `3`) of `TauCeti.realProjectiveMomentSpectralSequence N` is `H_N(ℝℙᴺ; ℤ) = ℤ`. -/
def realProjectiveMomentSpectralSequencePageThreeXTopIsoOfOdd (hN : Odd N) :
    ((𝔈[N]).page 3).X (-2 * N, N) ≅ ModuleCat.of ℤ ℤ :=
  realProjectiveMomentSpectralSequencePageThreeXIso N N ≪≫
    (RealProjectiveSpace.singularHomologyIsoProjectivization N (ModuleCat.of ℤ ℤ) N).symm ≪≫
    (RealProjectiveSpace.singularHomologyTopLinearEquivOfOdd ℤ hN).toModuleIso

/-- **The second page in even positive degrees.** For even `k > 0`, the object at `(-2k, k)` on
the second page (numbered `3`) of `TauCeti.realProjectiveMomentSpectralSequence N` is
`Hₖ(ℝℙᴺ; ℤ) = 0`. -/
theorem isZero_realProjectiveMomentSpectralSequence_page_three_X_of_even {k : ℕ} (hk : Even k)
    (hk0 : k ≠ 0) : IsZero (((𝔈[N]).page 3).X (-2 * k, k)) :=
  (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even ℤ
    (isRegular_iff_ne_zero.2 two_ne_zero).right hk hk0).of_iso
    (realProjectiveMomentSpectralSequencePageThreeXIso N k)

/-- **The second page vanishes off the diagonal.** On the second page (numbered `3`) of
`TauCeti.realProjectiveMomentSpectralSequence N`, only the positions `(-2k, k)` with `0 ≤ k ≤ N`
can be nonzero. -/
theorem isZero_realProjectiveMomentSpectralSequence_page_three_X (pq : ℤ × ℤ)
    (h : ¬(pq.1 = -2 * pq.2 ∧ 0 ≤ pq.2 ∧ pq.2 ≤ N)) :
    IsZero (((𝔈[N]).page 3).X pq) :=
  (𝔈[N]).isZero_page_X_of_le le_rfl (isZero_realProjectiveMomentSpectralSequence_page_two_X N pq h)
    3 (by norm_num)

/-! ### The first differential -/

/-- In an odd degree `k ≤ N` the second page at `(-2k, k)` does not vanish: it is `ℤ / 2` for
`k < N` and `ℤ` for `k = N`. -/
private theorem not_isZero_page_three_X_of_odd {k : ℕ} (hk : Odd k) (hkN : k ≤ N) :
    ¬IsZero (((𝔈[N]).page 3).X (-2 * k, k)) := by
  rcases hkN.lt_or_eq with hkN | rfl
  · rw [(realProjectiveMomentSpectralSequencePageThreeXIsoOfOdd N hk hkN).isZero_iff,
      ModuleCat.isZero_iff_subsingleton]
    exact fun h ↦ not_subsingleton (ZMod 2) h
  · rw [(realProjectiveMomentSpectralSequencePageThreeXTopIsoOfOdd k hk).isZero_iff,
      ModuleCat.isZero_iff_subsingleton]
    exact fun h ↦ not_subsingleton ℤ h

/-- The positions `(-2j, j)` and `(-2(j - 1), j - 1)` are joined by a differential of the first
page. -/
private theorem rel_two (j : ℤ) : ((-2 * j, j) : ℤ × ℤ) + (2, 1 - 2) = (-2 * (j - 1), j - 1) := by
  ext <;> simp <;> ring

/-- **The first differential out of an odd band vanishes.** On the first page (numbered `2`) of
`TauCeti.realProjectiveMomentSpectralSequence N`, every differential out of a position `(p, j)`
with odd `j` is zero. For `p = -2j` this is the differential to `(-2(j - 1), j - 1)`, the
connecting map `Hⱼ(M_{j+1/2}, M_{j-1/2}) ⟶ Hⱼ₋₁(M_{j-1/2}, M_{j-3/2})` of the sublevels
`M_c = {f ≤ c}`. -/
theorem realProjectiveMomentSpectralSequence_page_two_d_eq_zero_of_odd {pq pq' : ℤ × ℤ}
    (hj : Odd pq.2) : ((𝔈[N]).page 2).d pq pq' = 0 := by
  obtain ⟨p, j⟩ := pq
  change Odd j at hj
  by_cases hrel : (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).Rel (p, j) pq'
  swap
  · exact ((𝔈[N]).page 2).shape _ _ hrel
  obtain rfl : (p, j) + (2, 1 - 2) = pq' := hrel
  by_cases hp : p = -2 * j
  swap
  · exact (isZero_realProjectiveMomentSpectralSequence_page_two_X N _
      (by simp only; tauto)).eq_of_src _ _
  subst hp
  rw [rel_two]
  obtain ⟨i, rfl⟩ := hj
  by_cases hjN : 0 ≤ i ∧ 2 * i + 1 ≤ N
  swap
  · exact (isZero_realProjectiveMomentSpectralSequence_page_two_X N _
      (by simp only; lia)).eq_of_src _ _
  obtain ⟨e⟩ := nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso N
    (k := 2 * i + 1) (by lia) hjN.2
  obtain ⟨e'⟩ := nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso N
    (k := 2 * i + 1 - 1) (by lia) (by lia)
  set d := ((𝔈[N]).page 2).d (-2 * (2 * i + 1), 2 * i + 1) (-2 * (2 * i + 1 - 1), 2 * i + 1 - 1)
  by_contra hd
  -- Read in `ℤ`, the differential is multiplication by a nonzero integer, so it is injective.
  have hφ : e.inv ≫ d ≫ e'.hom = (e.inv ≫ d ≫ e'.hom).hom 1 • 𝟙 _ := by ext; simp
  have hm : (e.inv ≫ d ≫ e'.hom).hom 1 ≠ 0 := fun hm ↦ hd (by
    rw [hm, zero_smul] at hφ
    simpa using congrArg (fun φ ↦ e.hom ≫ φ ≫ e'.inv) hφ)
  have : Mono (e.inv ≫ d ≫ e'.hom) := by
    rw [hφ, ModuleCat.mono_iff_injective]
    exact fun x y hxy ↦ mul_right_injective₀ hm (by simpa [mul_comm] using hxy)
  have : Mono d := by
    rw [show d = e.hom ≫ (e.inv ≫ d ≫ e'.hom) ≫ e'.inv by simp]
    infer_instance
  -- So the cycles at `(-2j, j)` vanish, and with them the second page there.
  have hcycles : IsZero (((𝔈[N]).page 2).cycles (-2 * (2 * i + 1), 2 * i + 1)) :=
    (isZero_kernel_of_mono d).of_iso ((((𝔈[N]).page 2).cyclesIsKernel _ _
      (ComplexShape.next_eq' _ (rel_two _))).conePointUniqueUpToIso (limit.isLimit _))
  have hz := (IsZero.of_epi (((𝔈[N]).page 2).homologyπ _) hcycles).of_iso ((𝔈[N]).iso 2 3 _).symm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * i + 1 = k := ⟨(2 * i + 1).toNat, by lia⟩
  rw [hk] at hz
  exact not_isZero_page_three_X_of_odd N (k := k) ⟨i.toNat, by lia⟩ (by lia) hz

/-- **The first differential out of an even band is `±2`.** On the first page (numbered `2`) of
`TauCeti.realProjectiveMomentSpectralSequence N`, for even `j` with `2 ≤ j ≤ N`, the differential
from `(-2j, j)` to `(-2(j - 1), j - 1)` is multiplication by `2` or by `-2` in any identification of
the two objects with `ℤ`. -/
theorem realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul_or_neg_two_smul {j : ℤ}
    (hj : Even j) (h₂ : 2 ≤ j) (hjN : j ≤ N)
    (e : ((𝔈[N]).page 2).X (-2 * j, j) ≅ ModuleCat.of ℤ ℤ)
    (e' : ((𝔈[N]).page 2).X (-2 * (j - 1), j - 1) ≅ ModuleCat.of ℤ ℤ) :
    e.inv ≫ ((𝔈[N]).page 2).d (-2 * j, j) (-2 * (j - 1), j - 1) ≫ e'.hom = (2 : ℤ) • 𝟙 _ ∨
      e.inv ≫ ((𝔈[N]).page 2).d (-2 * j, j) (-2 * (j - 1), j - 1) ≫ e'.hom =
        (-2 : ℤ) • 𝟙 _ := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, j - 1 = k := ⟨(j - 1).toNat, by lia⟩
  have hkodd : Odd k := by
    obtain ⟨r, hr⟩ := hj
    exact ⟨(r - 1).toNat, by lia⟩
  -- The second page at `(-2(j - 1), j - 1)` is `ℤ / 2`.
  obtain ⟨z⟩ : Nonempty (((𝔈[N]).page 3).X (-2 * (j - 1), j - 1) ≅ ModuleCat.of ℤ (ZMod 2)) := by
    rw [hk]
    exact ⟨realProjectiveMomentSpectralSequencePageThreeXIsoOfOdd N hkodd (by lia)⟩
  -- It is also the cokernel of the differential, since the next differential vanishes.
  set φ := e.inv ≫ ((𝔈[N]).page 2).d (-2 * j, j) (-2 * (j - 1), j - 1) ≫ e'.hom with hφ
  let i := z.symm ≪≫ (𝔈[N]).pageXIsoCokernel le_rfl 3 (by norm_num)
    (ComplexShape.prev_eq' _ (rel_two j)) (ComplexShape.next_eq' _ (rel_two (j - 1)))
    (realProjectiveMomentSpectralSequence_page_two_d_eq_zero_of_odd N
      (by change Odd (j - 1); rw [hk]; exact_mod_cast hkodd)) ≪≫
    cokernel.mapIso _ φ e e' (by simp [hφ])
  have hcard := Nat.card_congr i.toLinearEquiv.toEquiv
  rw [ModuleCat.natCard_cokernel_int, ModuleCat.coe_of, Nat.card_zmod] at hcard
  have hφ' : φ = φ.hom 1 • 𝟙 _ := by ext; simp
  rcases Int.natAbs_eq_iff.1 hcard.symm with h | h
  · exact .inl (by rw [hφ', h, Nat.cast_ofNat])
  · exact .inr (by rw [hφ', h, Nat.cast_ofNat])

/-- **The first differential out of an even band is `2`.** For even `j` with `2 ≤ j ≤ N`, there
are identifications of the objects at `(-2j, j)` and `(-2(j - 1), j - 1)` on the first page of
`TauCeti.realProjectiveMomentSpectralSequence N` with `ℤ` in which the differential between them
is multiplication by `2`. -/
theorem exists_realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul {j : ℤ} (hj : Even j)
    (h₂ : 2 ≤ j) (hjN : j ≤ N) :
    ∃ (e : ((𝔈[N]).page 2).X (-2 * j, j) ≅ ModuleCat.of ℤ ℤ)
      (e' : ((𝔈[N]).page 2).X (-2 * (j - 1), j - 1) ≅ ModuleCat.of ℤ ℤ),
      ((𝔈[N]).page 2).d (-2 * j, j) (-2 * (j - 1), j - 1) = e.hom ≫ ((2 : ℤ) • 𝟙 _) ≫ e'.inv := by
  obtain ⟨e⟩ := nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso N (k := j)
    (by lia) hjN
  obtain ⟨e'⟩ := nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso N (k := j - 1)
    (by lia) (by lia)
  /- The negation of `ℤ`, to correct the sign. -/
  let ν : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ :=
    { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
  rcases realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul_or_neg_two_smul N hj h₂ hjN
    e e' with h | h
  · refine ⟨e, e', ?_⟩
    rw [← h]
    simp
  · refine ⟨e, e' ≪≫ ν, ?_⟩
    have : ((𝔈[N]).page 2).d (-2 * j, j) (-2 * (j - 1), j - 1) =
        e.hom ≫ ((-2 : ℤ) • 𝟙 _) ≫ e'.inv := by
      rw [← h]
      simp
    rw [this]
    simp [ν]

end TauCeti
