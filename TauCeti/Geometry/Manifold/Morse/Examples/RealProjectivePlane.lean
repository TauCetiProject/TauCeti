/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.End
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Cell.Band
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence
public import TauCeti.LinearAlgebra.LinearEquiv.Basic

/-!
# The critical-band spectral sequence of `ℝP²`

On `ℝP² = ℙ ℝ (Fin 3 → ℝ)` consider the moment function
`f [x : y : z] = (y² + 2 z²) / (x² + y² + z²)`, the function
`TauCeti.projectiveMomentFunction` with weights `0, 1, 2`. It is a Morse function with one critical
point `[eₖ]` of each index `k = 0, 1, 2`, at the value `k`. The cut `q ↦ q - 1/2`
(`TauCeti.realProjPlaneMorseCut`) is a critical-band cut of `f`
(`TauCeti.isCriticalBandCut_realProjPlaneMorseCut`), and this file computes the spectral sequence of
the filtration of `ℝP²` by the sublevels `{f ≤ q - 1/2}`, with integer coefficients
(`TauCeti.realProjPlaneMorseSpectralSequence`), up to its second page. In the cohomological indexing
of `TauCeti.filteredSpaceSpectralSequence` the first page is numbered `2`, the second `3`, and the
relative homology `Hₙ({f ≤ q + 1/2}, {f ≤ q - 1/2})` of the `q`th band sits at `(-n - q, q)`.

* **First page.** The object at `(-2k, k)` is `ℤ` for `k = 0, 1, 2`, the relative homology across
  the critical point of index `k`
  (`TauCeti.nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso`), and every other object
  vanishes (`TauCeti.isZero_realProjPlaneMorseSpectralSequence_page_two_X`).
* **First differential.** The differential from the cell of the maximum at `(-4, 2)` to the cell of
  the saddle at `(-2, 1)` is multiplication by `±2` in any identifications with `ℤ`
  (`TauCeti.realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul`), and by
  `2` in suitable ones (`TauCeti.exists_realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul`).
  Every other differential of the first page vanishes, in particular the one from `(-2, 1)` to
  `(0, 0)` (`TauCeti.realProjPlaneMorseSpectralSequence_page_two_d_eq_zero`).
* **Second page.** The objects at `(0, 0)`, `(-2, 1)` and `(-4, 2)` are `ℤ`, `ℤ/2` and `0`, the
  integral homology of `ℝP²` in degrees `0, 1, 2`
  (`TauCeti.nonempty_realProjPlaneMorseSpectralSequence_page_three_X_zero_zero_iso`,
  `TauCeti.nonempty_realProjPlaneMorseSpectralSequence_page_three_X_neg_two_one_iso`), and every
  object other than those at `(0, 0)` and `(-2, 1)` vanishes
  (`TauCeti.isZero_realProjPlaneMorseSpectralSequence_page_three_X`).

So the relative homology of the critical bands is the first page but not yet the second: the
differential of the critical-band spectral sequence of a Morse function can be nonzero. The first
differential is the connecting map of the triple `(ℝP², {f ≤ 3/2}, {f ≤ 1/2})`
(`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), and it is computed from the integral
homology of real projective space
(`TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd`) through the long exact sequences
of the sublevel filtration.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.5) and §5.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42 (the cellular
  chain complex `ℤ ⟵ ℤ ⟵ ℤ` of `ℝP²`, with differentials `0` and `2`).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits Set Projectivization
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti

/-- The cut `q ↦ q - 1/2` of the values of the moment function
`[x : y : z] ↦ (y² + 2 z²) / (x² + y² + z²)` on `ℝP²`: its critical values `0, 1, 2` lie in the
middle of the bands `[q - 1/2, q + 1/2]`. -/
def realProjPlaneMorseCut (q : ℤ) : ℝ := q - 2⁻¹

@[simp]
theorem realProjPlaneMorseCut_apply (q : ℤ) : realProjPlaneMorseCut q = q - 2⁻¹ := (rfl)

/-- The moment function `[x : y : z] ↦ (y² + 2 z²) / (x² + y² + z²)` on `ℝP²`, with weights
`0, 1, 2`. -/
private abbrev realProjPlaneMomentFunction : ℙ ℝ (Fin 3 → ℝ) → ℝ :=
  projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ)

/-- The preimage of a closed interval under the moment function is compact. -/
private theorem isCompact_realProjPlaneMomentFunction_preimage_Icc (a b : ℝ) :
    IsCompact (realProjPlaneMomentFunction ⁻¹' Icc a b) :=
  (isClosed_Icc.preimage (contMDiff_projectiveMomentFunction (r := 0) _).continuous).isCompact

/-- The critical points of the moment function with weights `0, 1, 2` on `ℝP²` are the coordinate
points `[eₖ]`, at the value `k`, of Morse index `k`. -/
private theorem exists_of_mem_criticalPoints {x : ℙ ℝ (Fin 3 → ℝ)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction) :
    ∃ k : Fin 3, x = mk ℝ (Pi.single k 1) (by simp) ∧
      realProjPlaneMomentFunction x = (k : ℕ) ∧
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction x = k := by
  rw [criticalPoints_projectiveMomentFunction fun i j h ↦ Fin.ext (by exact_mod_cast h)] at hx
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k, rfl, projectiveMomentFunction_mk_single _ k, ?_⟩
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul]

/-- A critical point with value in `[a - 1/2, b - 1/2]` has index in `[a, b)`. -/
private theorem manifoldMorseIndex_mem_Ico_of_mem_criticalPoints {x : ℙ ℝ (Fin 3 → ℝ)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction) {a b : ℤ}
    (h : realProjPlaneMomentFunction x ∈ Icc (realProjPlaneMorseCut a) (realProjPlaneMorseCut b)) :
    (manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction x : ℤ) ∈ Ico a b := by
  obtain ⟨k, -, hk, hind⟩ := exists_of_mem_criticalPoints hx
  rw [hind, mem_Ico]
  rw [hk] at h
  simp only [realProjPlaneMorseCut_apply, mem_Icc] at h
  have h₁ : a < ((k : ℕ) : ℤ) + 1 := by
    exact_mod_cast (by linarith [h.1] : (a : ℝ) < ((k : ℕ) : ℝ) + 1)
  have h₂ : ((k : ℕ) : ℤ) < b := by exact_mod_cast (by linarith [h.2] : ((k : ℕ) : ℝ) < b)
  omega

/-- A critical value in the band `[q - 1/2, q + 1/2]` is `q`, and it is the index of the critical
point. -/
private theorem apply_eq_of_mem_criticalPoints {x : ℙ ℝ (Fin 3 → ℝ)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction) {q : ℤ}
    (h : realProjPlaneMomentFunction x ∈
      Icc (realProjPlaneMorseCut q) (realProjPlaneMorseCut (q + 1))) :
    realProjPlaneMomentFunction x = q ∧
      (manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction x : ℤ) = q := by
  have hq := manifoldMorseIndex_mem_Ico_of_mem_criticalPoints hx h
  obtain ⟨k, -, hk, hind⟩ := exists_of_mem_criticalPoints hx
  rw [hind, mem_Ico] at hq
  rw [hk, hind]
  have hkq : ((k : ℕ) : ℤ) = q := by omega
  exact ⟨by exact_mod_cast hkq, hkq⟩

/-- The cut values `q - 1/2` are regular values. -/
private theorem isRegularValue_realProjPlaneMorseCut (q : ℤ) :
    IsRegularValue 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) realProjPlaneMomentFunction (realProjPlaneMorseCut q) := by
  refine isRegularValue_iff_notMem_image_criticalPoints.2 ?_
  rintro ⟨x, hx, hfx⟩
  obtain ⟨k, -, hk, -⟩ := exists_of_mem_criticalPoints hx
  rw [hk, realProjPlaneMorseCut_apply] at hfx
  have h : ((2 * ((k : ℕ) : ℤ) : ℤ) : ℝ) = ((2 * q - 1 : ℤ) : ℝ) := by push_cast; linarith
  have := Int.cast_injective (α := ℝ) h
  omega

/-- **The cut `q ↦ q - 1/2` is a critical-band cut** of the moment function
`[x : y : z] ↦ (y² + 2 z²) / (x² + y² + z²)` on `ℝP²`: each band `[q - 1/2, q + 1/2]` is compact
and its only possible critical value is `q`. -/
theorem isCriticalBandCut_realProjPlaneMorseCut :
    IsCriticalBandCut 𝓘(ℝ, Fin 2 → ℝ)
      (projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) realProjPlaneMorseCut where
  isCriticalBand q :=
    ⟨isCompact_realProjPlaneMomentFunction_preimage_Icc _ _,
      q, by simp only [realProjPlaneMorseCut_apply, mem_Ioo]; push_cast; constructor <;> linarith,
      fun _ hx h ↦ (apply_eq_of_mem_criticalPoints hx h).1⟩

/-- **The critical-band spectral sequence of `ℝP²`.** The spectral sequence, with integer
coefficients, of the filtration of `ℝP²` by the sublevels `{f ≤ q - 1/2}` of the moment function
`f [x : y : z] = (y² + 2 z²) / (x² + y² + z²)`. Its first page is numbered `2` and its second page
`3`, in the cohomological indexing of `TauCeti.filteredSpaceSpectralSequence`, with singular
chains of degree `n` in degree `-n`. -/
abbrev realProjPlaneMorseSpectralSequence :=
  filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) (ModuleCat.of ℤ ℤ)
    ((sublevel_mono (projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ))).comp
      isCriticalBandCut_realProjPlaneMorseCut.monotone)

/-- The moment function with weights `0, 1, 2` is a Morse function. -/
private theorem isMorse_realProjPlane :
    IsMorse 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction :=
  isMorse_projectiveMomentFunction fun i j h ↦ Fin.ext (by exact_mod_cast h)

/-- A band `[q - 1/2, q + 1/2]` contains at most one critical point. -/
private theorem subsingleton_criticalPoints_inter_preimage_Ioc (q : ℤ) :
    Subsingleton ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction ∩
      realProjPlaneMomentFunction ⁻¹'
        Ioc (realProjPlaneMorseCut q) (realProjPlaneMorseCut (q + 1))) := by
  refine ⟨fun ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩ ↦ Subtype.ext ?_⟩
  obtain ⟨j, rfl, hj, -⟩ := exists_of_mem_criticalPoints hx
  obtain ⟨k, rfl, hk, -⟩ := exists_of_mem_criticalPoints hy
  have hjq := (apply_eq_of_mem_criticalPoints hx (Ioc_subset_Icc_self hxq)).1
  have hkq := (apply_eq_of_mem_criticalPoints hy (Ioc_subset_Icc_self hyq)).1
  rw [hj] at hjq
  rw [hk] at hkq
  obtain rfl : j = k := Fin.ext (by exact_mod_cast hjq.trans hkq.symm)
  rfl

/-- **The first page of the critical-band spectral sequence of `ℝP²`, in the cell positions.** For
`k ≤ 2`, the object at `(-2k, k)` on the first page is `ℤ`: the relative homology
`Hₖ({f ≤ k + 1/2}, {f ≤ k - 1/2})` across the critical point `[eₖ]` of index `k`. -/
theorem nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso {k : ℕ} (hk : k ≤ 2) :
    Nonempty ((realProjPlaneMorseSpectralSequence.page 2).X (-(2 * k : ℤ), k) ≅
      ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := isMorse_realProjPlane.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma
    (ModuleCat.of ℤ ℤ) isCriticalBandCut_realProjPlaneMorseCut.monotone
    (isCriticalBandCut_realProjPlaneMorseCut.isCriticalBand k) (-(2 * k : ℤ), k) rfl k
    (by push_cast; ring)
  have := subsingleton_criticalPoints_inter_preimage_Ioc k
  -- The critical point `[eₖ]` is the only point of the band, and it has index `k`.
  let x₀ : Fin 3 := ⟨k, by omega⟩
  have hx₀ := mk_single_mem_criticalPoints_projectiveMomentFunction (𝕜 := ℝ)
    (fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) x₀
  have hval := projectiveMomentFunction_mk_single (𝕜 := ℝ) (fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) x₀
  have hind := manifoldMorseIndex_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := 2) x₀
  rw [Module.finrank_self, one_mul] at hind
  have : Nonempty {x : ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction ∩
      realProjPlaneMomentFunction ⁻¹'
        Ioc (realProjPlaneMorseCut k) (realProjPlaneMorseCut (k + 1))) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) realProjPlaneMomentFunction x = k} :=
    ⟨⟨⟨_, hx₀, by
      simp only [mem_preimage, hval, mem_Ioc, realProjPlaneMorseCut_apply, x₀]
      push_cast
      constructor <;> linarith⟩, hind⟩⟩
  have : Unique _ := uniqueOfSubsingleton (Classical.choice this)
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- **The first page of the critical-band spectral sequence of `ℝP²` vanishes off the cell
positions.** The object at `(p, q)` on the first page is zero unless `(p, q) = (-2k, k)` for some
`k ≤ 2`. -/
theorem isZero_realProjPlaneMorseSpectralSequence_page_two_X {pq : ℤ × ℤ}
    (h : ∀ k : ℕ, k ≤ 2 → pq ≠ (-(2 * k : ℤ), (k : ℤ))) :
    IsZero ((realProjPlaneMorseSpectralSequence.page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  refine isMorse_realProjPlane.isZero_filteredSpaceSpectralSequence_page_two_X (ModuleCat.of ℤ ℤ)
    isCriticalBandCut_realProjPlaneMorseCut.monotone
    (isCriticalBandCut_realProjPlaneMorseCut.isCriticalBand pq.2) pq rfl n hn
    fun x hx hfx hidx ↦ ?_
  obtain ⟨k, -, -, hk⟩ := exists_of_mem_criticalPoints hx
  have hq := (apply_eq_of_mem_criticalPoints hx (Ioc_subset_Icc_self hfx)).2
  rw [hidx] at hk hq
  exact h n (by have := k.2; omega) (Prod.ext (by dsimp only; omega) hq.symm)

/-! ### The long exact sequences of the sublevel filtration -/

/-- The sublevels `{f ≤ q - 1/2}` increase with `q`. -/
private theorem monotone_realProjPlaneSublevel :
    Monotone fun q : ℤ ↦
      {x : ℙ ℝ (Fin 3 → ℝ) | realProjPlaneMomentFunction x ≤ realProjPlaneMorseCut q} :=
  (sublevel_mono _).comp isCriticalBandCut_realProjPlaneMorseCut.monotone

/-- The pair `({f ≤ b - 1/2}, {f ≤ a - 1/2})` of sublevels, for `a ≤ b`. -/
private abbrev realProjPlaneBandPair {a b : ℤ} (h : a ≤ b) : TopPair :=
  TopPair.ofInclusion (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) (monotone_realProjPlaneSublevel h)

/-- The relative homology `Hₙ({f ≤ b - 1/2}, {f ≤ a - 1/2})` vanishes unless `a ≤ n < b`: the
band has no critical point of index `n`. -/
private theorem isZero_singularHomology_realProjPlaneBandPair {a b : ℤ} (h : a ≤ b) {n : ℕ}
    (hn : (n : ℤ) < a ∨ b ≤ n) :
    IsZero ((realProjPlaneBandPair h).singularHomology (ModuleCat.of ℤ ℤ) n) :=
  isMorse_realProjPlane.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_ne
    (isCriticalBandCut_realProjPlaneMorseCut.monotone h)
    (isCompact_realProjPlaneMomentFunction_preimage_Icc _ _)
    (isRegularValue_realProjPlaneMorseCut a) (isRegularValue_realProjPlaneMorseCut b)
    (fun _ hp hpn ↦ by
      have := manifoldMorseIndex_mem_Ico_of_mem_criticalPoints hp.1 hp.2
      rw [mem_Ico] at this
      omega) _

/-- The relative homology `Hₖ({f ≤ k + 1/2}, {f ≤ k - 1/2})` across the critical point of index
`k ≤ 2` is `ℤ`. -/
private theorem nonempty_singularHomology_realProjPlaneBandPair_iso {k : ℕ} (hk : k ≤ 2) :
    Nonempty ((realProjPlaneBandPair (Int.le_add_one (le_refl (k : ℤ)))).singularHomology
      (ModuleCat.of ℤ ℤ) k ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso hk
  exact ⟨(filteredSpaceSpectralSequenceFirstPageXIso _ _ (-(2 * k : ℤ), (k : ℤ)) k (k + 1) rfl rfl
    _ rfl k (by push_cast; ring)).symm ≪≫ e⟩

/-- The homology of `ℝP²` is the relative homology of `({f ≤ 5/2}, {f ≤ -1/2}) = (ℝP², ∅)`. -/
private def realProjPlaneTotalIso (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (RealProjectiveSpace 2)) ≅
      (realProjPlaneBandPair (by norm_num : (0 : ℤ) ≤ 3)).singularHomology (ModuleCat.of ℤ ℤ) n :=
  have hf := projectiveMomentFunction_mem_Icc (𝕜 := ℝ) (w := fun i : Fin 3 ↦ ((i : ℕ) : ℝ))
    (a := 0) (b := 2) fun i ↦ ⟨by positivity, by norm_cast; omega⟩
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo (RealProjectiveSpace.homeomorphProjectivization 2)) ≪≫
    singularHomologyIsoSublevelPair (isCriticalBandCut_realProjPlaneMorseCut.monotone (by norm_num))
      (fun x ↦ by simp only [realProjPlaneMorseCut_apply]; norm_num; linarith [(hf x).1])
      (fun x ↦ by simp only [realProjPlaneMorseCut_apply]; norm_num; linarith [(hf x).2]) _ n

/-- `H₁(ℝP², {f ≤ 1/2}) ≅ ℤ/2`. In the long exact sequence of the triple `(ℝP², {f ≤ 1/2}, ∅)`,
the sublevel `{f ≤ 1/2}` around the minimum has the homology of a point, and the map
`H₀({f ≤ 1/2}) ⟶ H₀(ℝP²)` is a surjection `ℤ ⟶ ℤ`, hence injective; so `H₁(ℝP²) ≅ ℤ/2` maps
isomorphically onto `H₁(ℝP², {f ≤ 1/2})`. -/
private theorem nonempty_singularHomology_one_realProjPlaneBandPair_linearEquiv :
    Nonempty (↥((realProjPlaneBandPair (by norm_num : (1 : ℤ) ≤ 3)).singularHomology
      (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ZMod 2) := by
  let T := TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (monotone_realProjPlaneSublevel (by norm_num : (0 : ℤ) ≤ 1))
    (monotone_realProjPlaneSublevel (by norm_num : (1 : ℤ) ≤ 3))
  let ι := TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) (ModuleCat.of ℤ ℤ) 0
  -- `H₀({f ≤ 1/2}) ⟶ H₀(ℝP²)` is onto, since `H₀(ℝP², {f ≤ 1/2}) = 0`.
  have hsurj : Function.Surjective ι.hom := (ModuleCat.epi_iff_surjective _).1
    ((T.singularHomology_exact_total _ 0).epi_f
      ((isZero_singularHomology_realProjPlaneBandPair (by norm_num : (1 : ℤ) ≤ 3) (n := 0)
        (by norm_num)).eq_of_tgt _ _))
  -- Read in copies of `ℤ`, a surjective endomorphism of `ℤ` is injective.
  obtain ⟨e₀⟩ : Nonempty ((TopTriple.innerPair.obj T).singularHomology (ModuleCat.of ℤ ℤ) 0 ≅
      ModuleCat.of ℤ ℤ) :=
    nonempty_singularHomology_realProjPlaneBandPair_iso (k := 0) (by norm_num)
  let e₃ : ↥((TopTriple.totalPair.obj T).singularHomology (ModuleCat.of ℤ ℤ) 0) ≃ₗ[ℤ] ℤ :=
    (realProjPlaneTotalIso 0).symm.toLinearEquiv.trans
      (RealProjectiveSpace.singularHomologyZeroLinearEquiv ℤ (N := 2))
  have hinj : Function.Injective ι.hom := by
    have h := OrzechProperty.injective_of_surjective_of_injective e₀.toLinearEquiv.toLinearMap
      (e₃.toLinearMap ∘ₗ ι.hom) e₀.toLinearEquiv.injective (e₃.surjective.comp hsurj)
    rw [LinearMap.coe_comp] at h
    exact h.of_comp
  have : Mono ι := (ModuleCat.mono_iff_injective _).2 hinj
  -- So the connecting map `H₁(ℝP², {f ≤ 1/2}) ⟶ H₀({f ≤ 1/2})` vanishes, and
  -- `H₁(ℝP²) ⟶ H₁(ℝP², {f ≤ 1/2})` is bijective since `H₁({f ≤ 1/2}) = 0`.
  have hδ : T.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 = 0 :=
    (cancel_mono ι).1 (by simp [ι])
  let π := TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) (ModuleCat.of ℤ ℤ) 1
  have : Mono π := (T.singularHomology_exact_total _ 1).mono_g
    ((isZero_singularHomology_realProjPlaneBandPair (by norm_num : (0 : ℤ) ≤ 1) (n := 1)
      (by norm_num)).eq_of_src _ _)
  have : Epi π := (T.singularHomology_exact_outer _ 1 0).epi_f hδ
  have : IsIso π := isIso_of_mono_of_epi π
  exact ⟨(asIso π).symm.toLinearEquiv ≪≫ₗ (realProjPlaneTotalIso 1).symm.toLinearEquiv ≪≫ₗ
    RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd odd_one (by norm_num)⟩

/-- The triple `({f ≤ 5/2}, {f ≤ 3/2}, {f ≤ 1/2}) = (ℝP², {f ≤ 3/2}, {f ≤ 1/2})`. -/
private abbrev realProjPlaneTopTriple : TopTriple :=
  TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (monotone_realProjPlaneSublevel (by norm_num : (1 : ℤ) ≤ 2))
    (monotone_realProjPlaneSublevel (by norm_num : (2 : ℤ) ≤ 3))

/-- The connecting map `H₂(ℝP², {f ≤ 3/2}) ⟶ H₁({f ≤ 3/2}, {f ≤ 1/2})` of the triple
`(ℝP², {f ≤ 3/2}, {f ≤ 1/2})`, read in any identifications of both groups with `ℤ`, is
multiplication by `2` or `-2`. In the long exact sequence of the triple it is followed by the
surjection onto `H₁(ℝP², {f ≤ 1/2}) ≅ ℤ/2`, since `H₁(ℝP², {f ≤ 3/2}) = 0`; so its cokernel is
`ℤ/2`. -/
private theorem realProjPlane_singularHomologyδ_eq
    (e₂ : (TopTriple.outerPair.obj realProjPlaneTopTriple).singularHomology
      (ModuleCat.of ℤ ℤ) 2 ≅ ModuleCat.of ℤ ℤ)
    (e₁ : (TopTriple.innerPair.obj realProjPlaneTopTriple).singularHomology
      (ModuleCat.of ℤ ℤ) 1 ≅ ModuleCat.of ℤ ℤ) :
    e₂.inv ≫ realProjPlaneTopTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1 ≫ e₁.hom =
        (2 : ℤ) • 𝟙 _ ∨
      e₂.inv ≫ realProjPlaneTopTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1 ≫ e₁.hom =
        (-2 : ℤ) • 𝟙 _ := by
  let T := realProjPlaneTopTriple
  set δ := T.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1
  set g := e₂.inv ≫ δ ≫ e₁.hom
  let ι := TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) (ModuleCat.of ℤ ℤ) 1
  -- The cokernel of `δ` is `H₁(ℝP², {f ≤ 1/2}) ≅ ℤ/2`.
  have hrange : LinearMap.range δ.hom = LinearMap.ker ι.hom :=
    (T.singularHomology_exact_inner _ 2 1).moduleCat_range_eq_ker
  have hsurj : Function.Surjective ι.hom := (ModuleCat.epi_iff_surjective _).1
    ((T.singularHomology_exact_total _ 1).epi_f
      ((isZero_singularHomology_realProjPlaneBandPair (by norm_num : (2 : ℤ) ≤ 3) (n := 1)
        (by norm_num)).eq_of_tgt _ _))
  obtain ⟨ψ⟩ := nonempty_singularHomology_one_realProjPlaneBandPair_linearEquiv
  have hcomp : (e₁.toLinearEquiv : _ →ₗ[ℤ] ℤ) ∘ₗ δ.hom =
      g.hom ∘ₗ (e₂.toLinearEquiv : _ →ₗ[ℤ] ℤ) := by
    rw [Iso.toLinearMap_toLinearEquiv, Iso.toLinearMap_toLinearEquiv, ← ModuleCat.hom_comp,
      ← ModuleCat.hom_comp]
    -- `g` is `e₂.inv ≫ δ ≫ e₁.hom` by definition.
    exact congrArg ModuleCat.Hom.hom (e₂.hom_inv_id_assoc _).symm
  let q : (ℤ ⧸ LinearMap.range g.hom) ≃ₗ[ℤ] ZMod 2 :=
    (LinearMap.cokerEquivOfComp _ _ hcomp).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hrange ≪≫ₗ ι.hom.quotKerEquivOfSurjective hsurj ≪≫ₗ ψ
  simpa only [Nat.cast_ofNat] using
    ModuleCat.eq_natCast_smul_id_or_eq_neg_natCast_smul_id g (n := 2) q.toEquiv

/-! ### The first differential and the second page -/

/-- **The first differential of the critical-band spectral sequence of `ℝP²` is `±2`.** The
differential of the first page from `(-4, 2)` to `(-2, 1)`, the connecting map
`H₂(ℝP², {f ≤ 3/2}) ⟶ H₁({f ≤ 3/2}, {f ≤ 1/2})` from the cell of the maximum to the cell of the
saddle, is multiplication by `2` or by `-2` in any identifications of both groups with `ℤ`. -/
theorem realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul
    (e : (realProjPlaneMorseSpectralSequence.page 2).X (-4, 2) ≅ ModuleCat.of ℤ ℤ)
    (e' : (realProjPlaneMorseSpectralSequence.page 2).X (-2, 1) ≅ ModuleCat.of ℤ ℤ) :
    e.inv ≫ (realProjPlaneMorseSpectralSequence.page 2).d (-4, 2) (-2, 1) ≫ e'.hom =
        (2 : ℤ) • 𝟙 _ ∨
      e.inv ≫ (realProjPlaneMorseSpectralSequence.page 2).d (-4, 2) (-2, 1) ≫ e'.hom =
        (-2 : ℤ) • 𝟙 _ := by
  -- The differential is the connecting map of the triple `(ℝP², {f ≤ 3/2}, {f ≤ 1/2})`. The
  -- upstream equation is stated at `(p, q) ⟶ (p + 2, q - 1)` for the triple of sublevels
  -- `q - 1 ≤ q ≤ q + 1`; with `(p, q) = (-4, 2)` its integer indices `-4 + 2`, `2 - 1`, `2 + 1`
  -- reduce by evaluation to the literals `-2`, `1`, `3` used here and in `realProjPlaneTopTriple`.
  obtain ⟨A, B, hd⟩ : ∃ (A : (realProjPlaneMorseSpectralSequence.page 2).X (-4, 2) ≅
        (TopTriple.outerPair.obj realProjPlaneTopTriple).singularHomology (ModuleCat.of ℤ ℤ) 2)
      (B : (realProjPlaneMorseSpectralSequence.page 2).X (-2, 1) ≅
        (TopTriple.innerPair.obj realProjPlaneTopTriple).singularHomology (ModuleCat.of ℤ ℤ) 1),
      (realProjPlaneMorseSpectralSequence.page 2).d (-4, 2) (-2, 1) =
        A.hom ≫ realProjPlaneTopTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1 ≫ B.inv :=
    ⟨_, _, filteredSpaceSpectralSequence_first_page_d_eq _ _ 2 (-4) 1 (by norm_num)⟩
  rw [hd]
  simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc] using
    realProjPlane_singularHomologyδ_eq (A.symm ≪≫ e) (B.symm ≪≫ e')

/-- **The first differential of the critical-band spectral sequence of `ℝP²` is `2`.** There are
identifications of the first page at `(-4, 2)` and `(-2, 1)` with `ℤ` in which the differential
between them is multiplication by `2`. -/
theorem exists_realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul :
    ∃ (e : (realProjPlaneMorseSpectralSequence.page 2).X (-4, 2) ≅ ModuleCat.of ℤ ℤ)
      (e' : (realProjPlaneMorseSpectralSequence.page 2).X (-2, 1) ≅ ModuleCat.of ℤ ℤ),
      (realProjPlaneMorseSpectralSequence.page 2).d (-4, 2) (-2, 1) =
        e.hom ≫ ((2 : ℤ) • 𝟙 _) ≫ e'.inv := by
  obtain ⟨e⟩ := nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso (k := 2) le_rfl
  obtain ⟨e'⟩ := nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso (k := 1) (by norm_num)
  -- Composing the second identification with `-1` if necessary, the differential reads as `2`.
  obtain ⟨e', h⟩ : ∃ e' : (realProjPlaneMorseSpectralSequence.page 2).X (-2, 1) ≅
      ModuleCat.of ℤ ℤ, e.inv ≫ (realProjPlaneMorseSpectralSequence.page 2).d (-4, 2) (-2, 1) ≫
        e'.hom = (2 : ℤ) • 𝟙 _ := by
    rcases realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul e e' with
      h | h
    · exact ⟨e', h⟩
    · refine ⟨e' ≪≫ (LinearEquiv.neg ℤ).toModuleIso, ?_⟩
      rw [Iso.trans_hom, ← Category.assoc, ← Category.assoc, Category.assoc e.inv, h]
      ext
      simp
  exact ⟨e, e', by rw [← Category.assoc, ← h]; simp⟩

/-- The differential of the first page from `(-2, 1)` to `(0, 0)`, the connecting map
`H₁({f ≤ 3/2}, {f ≤ 1/2}) ⟶ H₀({f ≤ 1/2})`, is zero: its composite with the differential `2` into
`(-2, 1)` vanishes, and `ℤ` has no `2`-torsion. -/
private theorem realProjPlaneMorseSpectralSequence_page_two_d_neg_two_one_eq_zero :
    (realProjPlaneMorseSpectralSequence.page 2).d (-2, 1) (0, 0) = 0 := by
  obtain ⟨e, e', h⟩ := exists_realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul
  obtain ⟨e''⟩ := nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso (k := 0) (by norm_num)
  set φ := e'.inv ≫ (realProjPlaneMorseSpectralSequence.page 2).d (-2, 1) (0, 0) ≫ e''.hom
  have h2 : (2 : ℤ) • φ = 0 := by
    have hdd := (realProjPlaneMorseSpectralSequence.page 2).d_comp_d (-4, 2) (-2, 1) (0, 0)
    rw [h] at hdd
    simpa [φ] using congrArg (fun ψ ↦ e.inv ≫ ψ ≫ e''.hom) hdd
  have hφ : φ = 0 := (cancel_mono ((2 : ℤ) • 𝟙 _)).1 (by simpa using h2)
  have hd : (realProjPlaneMorseSpectralSequence.page 2).d (-2, 1) (0, 0) =
      e'.hom ≫ φ ≫ e''.inv := by
    simp [φ]
  rw [hd, hφ]
  simp

/-- **The other first differentials vanish.** Every differential of the first page other than the
one from `(-4, 2)` to `(-2, 1)` is zero. The differential out of the cell of the saddle, from
`(-2, 1)` to `(0, 0)`, vanishes since its composite with the differential `2` into `(-2, 1)` does
and `ℤ` has no `2`-torsion; every other differential has a zero source or target. -/
theorem realProjPlaneMorseSpectralSequence_page_two_d_eq_zero {pq pq' : ℤ × ℤ}
    (h : pq ≠ (-4, 2) ∨ pq' ≠ (-2, 1)) :
    (realProjPlaneMorseSpectralSequence.page 2).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).Rel pq pq'
  swap
  · exact (realProjPlaneMorseSpectralSequence.page 2).shape _ _ hrel
  by_cases hX : ∀ k : ℕ, k ≤ 2 → pq ≠ (-(2 * k : ℤ), (k : ℤ))
  · exact (isZero_realProjPlaneMorseSpectralSequence_page_two_X hX).eq_of_src _ _
  push Not at hX
  obtain ⟨k, hk, rfl⟩ := hX
  -- `hrel` says that `pq' = (-2k + 2, k - 1)`.
  obtain rfl : pq' = (-(2 * k : ℤ) + 2, (k : ℤ) - 1) := by
    rw [← hrel]
    ext <;> simp [sub_eq_add_neg]
  interval_cases k
  · exact (isZero_filteredSpaceSpectralSequence_page_two_X _ _ _ (by norm_num)).eq_of_tgt _ _
  · -- The indices `(-(2 * 1), 1)` and `(-(2 * 1) + 2, 1 - 1)` evaluate to `(-2, 1)` and `(0, 0)`.
    exact realProjPlaneMorseSpectralSequence_page_two_d_neg_two_one_eq_zero
  · exact absurd h (by norm_num)

/-- **The second page at the cell of the minimum is `ℤ`.** The object at `(0, 0)` of the second
page is the object `ℤ` of the first page, since both differentials at `(0, 0)` vanish. -/
theorem nonempty_realProjPlaneMorseSpectralSequence_page_three_X_zero_zero_iso :
    Nonempty ((realProjPlaneMorseSpectralSequence.page 3).X (0, 0) ≅ ModuleCat.of ℤ ℤ) := by
  set K := realProjPlaneMorseSpectralSequence.page 2
  obtain ⟨e⟩ := nonempty_realProjPlaneMorseSpectralSequence_page_two_X_iso (k := 0) (by norm_num)
  have hin : K.d (-2, 1) (0, 0) = 0 :=
    realProjPlaneMorseSpectralSequence_page_two_d_eq_zero (Or.inl (by decide))
  have hout : K.d (0, 0) (2, -1) = 0 :=
    realProjPlaneMorseSpectralSequence_page_two_d_eq_zero (Or.inl (by decide))
  exact ⟨(realProjPlaneMorseSpectralSequence.iso 2 3 (0, 0)).symm ≪≫
    (K.isoHomologyπ (-2, 1) (0, 0) (ComplexShape.prev_eq' _ (by decide)) hin).symm ≪≫
    K.iCyclesIso (0, 0) (2, -1) (ComplexShape.next_eq' _ (by decide)) hout ≪≫ e⟩

/-- **The second page at the cell of the saddle is `ℤ/2`.** The object at `(-2, 1)` of the second
page is the cokernel of the differential `2 : ℤ ⟶ ℤ` of the first page, since the differential
out of `(-2, 1)` vanishes. In particular the first page is not already the second page. -/
theorem nonempty_realProjPlaneMorseSpectralSequence_page_three_X_neg_two_one_iso :
    Nonempty ((realProjPlaneMorseSpectralSequence.page 3).X (-2, 1) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  set K := realProjPlaneMorseSpectralSequence.page 2
  obtain ⟨e, e', h⟩ := exists_realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul
  let S := K.sc' (-4, 2) (-2, 1) (0, 0)
  have hout : K.d (-2, 1) (0, 0) = 0 :=
    realProjPlaneMorseSpectralSequence_page_two_d_eq_zero (Or.inl (by decide))
  -- Read through `e` and `e'`, the differential is `2`, with image `2ℤ`.
  have hcomp : (e'.toLinearEquiv : _ →ₗ[ℤ] ℤ) ∘ₗ (K.d (-4, 2) (-2, 1)).hom =
      ((2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)).hom ∘ₗ (e.toLinearEquiv : _ →ₗ[ℤ] ℤ) := by
    rw [h]
    ext
    simp
  have hrange : LinearMap.range ((2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)).hom =
      Ideal.span {((2 : ℕ) : ℤ)} := by
    rw [ModuleCat.range_hom_smul_id_eq_span, Nat.cast_ofNat]
  exact ⟨(realProjPlaneMorseSpectralSequence.iso 2 3 (-2, 1)).symm ≪≫
    K.homologyIsoSc' (-4, 2) (-2, 1) (0, 0) (ComplexShape.prev_eq' _ (by decide))
      (ComplexShape.next_eq' _ (by decide)) ≪≫
    S.asIsoHomologyι hout ≪≫
    S.moduleCatOpcyclesIso ≪≫
    (LinearMap.cokerEquivOfComp _ _ hcomp ≪≫ₗ Submodule.quotEquivOfEq _ _ hrange ≪≫ₗ
      (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv).toModuleIso⟩

/-- The object at `(-4, 2)` of the second page is the kernel of the injective differential
`2 : ℤ ⟶ ℤ` of the first page, so it vanishes. -/
private theorem isZero_realProjPlaneMorseSpectralSequence_page_three_X_neg_four_two :
    IsZero ((realProjPlaneMorseSpectralSequence.page 3).X (-4, 2)) := by
  set K := realProjPlaneMorseSpectralSequence.page 2
  obtain ⟨e, e', h⟩ := exists_realProjPlaneMorseSpectralSequence_page_two_d_eq_two_smul
  have hin : K.d (-6, 3) (-4, 2) = 0 :=
    realProjPlaneMorseSpectralSequence_page_two_d_eq_zero (Or.inl (by decide))
  have : Mono (K.d (-4, 2) (-2, 1)) := by
    rw [h]
    infer_instance
  -- The cycles at `(-4, 2)` vanish, since the differential out of `(-4, 2)` is a monomorphism.
  have hcycles : IsZero (K.cycles (-4, 2)) :=
    IsZero.of_mono_eq_zero (K.iCycles (-4, 2)) ((cancel_mono (K.d (-4, 2) (-2, 1))).1 (by simp))
  exact (hcycles.of_iso (K.isoHomologyπ (-6, 3) (-4, 2) (ComplexShape.prev_eq' _ (by decide))
    hin).symm).of_iso (realProjPlaneMorseSpectralSequence.iso 2 3 (-4, 2)).symm

/-- **The second page vanishes off the cells of the minimum and the saddle.** The object at
`(p, q)` of the second page is zero unless `(p, q)` is `(0, 0)` or `(-2, 1)`. At the cell of the
maximum `(-4, 2)` it is the kernel of the injective differential `2 : ℤ ⟶ ℤ` of the first page;
elsewhere the first page already vanishes. -/
theorem isZero_realProjPlaneMorseSpectralSequence_page_three_X {pq : ℤ × ℤ} (h₀ : pq ≠ (0, 0))
    (h₁ : pq ≠ (-2, 1)) : IsZero ((realProjPlaneMorseSpectralSequence.page 3).X pq) := by
  by_cases h₂ : pq = (-4, 2)
  · subst h₂
    exact isZero_realProjPlaneMorseSpectralSequence_page_three_X_neg_four_two
  refine realProjPlaneMorseSpectralSequence.isZero_page_X_of_le (r := 2) le_rfl ?_ 3 (by norm_num)
  refine isZero_realProjPlaneMorseSpectralSequence_page_two_X fun k hk hpq ↦ ?_
  interval_cases k <;> simp_all

end TauCeti
