/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.SpectralSequence
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative

/-!
# The critical-band spectral sequence of real projective space

The moment function `f [v] = (∑ i, i vᵢ²) / ∑ i, vᵢ²` on `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` is a Morse
function whose critical points are the coordinate points `[eₖ]`, with value `k` and Morse index `k`
(`TauCeti.criticalPoints_projectiveMomentFunction`,
`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast`). The half-integers `q - 1/2` cut
it into critical bands (`TauCeti.isCriticalBandCut_projectiveMomentFunction_natCast`), and this
file studies the spectral sequence of the resulting critical-band filtration of `ℝℙᴺ` by the
sublevels `{f ≤ q - 1/2}` (`TauCeti.realProjectiveMomentSpectralSequence`).

Its first page (numbered `2`, as in `CochainComplex.spectralSequence`) has at `(p, q)` the
relative homology `Hₙ({f ≤ q + 1/2}, {f ≤ q - 1/2})`, `p + q = -n`, of the cell attached at the
critical point `[e_q]`. So it is a copy of the coefficients at each position `(-2k, k)`, `k ≤ N`,
and zero elsewhere.

On `ℝℙ²` with integer coefficients the first page is therefore `ℤ` at the positions `(0, 0)`,
`(-2, 1)` and `(-4, 2)` of the minimum, the saddle and the maximum. Its differentials need not
vanish: the differential from the maximum to the saddle is multiplication by `±2`, for any
identifications of both objects with `ℤ`. It is the connecting map of the triple
`({f ≤ 5/2}, {f ≤ 3/2}, {f ≤ 1/2})`, and the contractible disc `{f ≤ 1/2}`
(`TauCeti.contractibleSpace_sublevel_projectiveMomentFunction_natCast`) identifies its cokernel
with `H₁(ℝℙ²; ℤ) ≅ ℤ/2` and shows it is injective since `H₂(ℝℙ²; ℤ) = 0`. The differential from
the saddle to the minimum vanishes. So the relative homology of the attached cells is not yet the
second page: the second page (numbered `3`) is `ℤ`, `ℤ/2` and `0` at the minimum, the saddle and
the maximum, the integral homology groups `H₀`, `H₁` and `H₂` of `ℝℙ²`.

## Main results

* `TauCeti.nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso` and
  `TauCeti.isZero_realProjectiveMomentSpectralSequence_page_two_X`: the first page.
* `TauCeti.mono_realProjectiveMomentSpectralSequence_page_two_d`,
  `TauCeti.nonempty_cokernel_realProjectiveMomentSpectralSequence_page_two_d_iso` and
  `TauCeti.realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul`: on
  `ℝℙ²`, the first differential from the maximum to the saddle is injective with cokernel `ℤ/2`,
  and is multiplication by `±2`.
* `TauCeti.isZero_realProjectiveMomentSpectralSequence_page_three_X_neg_four_two`,
  `TauCeti.nonempty_realProjectiveMomentSpectralSequence_page_three_X_neg_two_one_iso` and
  `TauCeti.nonempty_realProjectiveMomentSpectralSequence_page_three_X_zero_zero_iso`: the second
  page of `ℝℙ²`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 and §5.
* R. Bott, *Nondegenerate critical manifolds*, Ann. of Math. 60 (1954), 248–261, the filtration of
  a manifold by the sublevels of a function cut between its critical values.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42, the homology
  of real projective space.
-/

public noncomputable section

open Set Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ}

/-- The critical points with value in the band `(q - 1/2, q + 1/2]` and of Morse index `k` form a
singleton when `k = q ≤ N`. -/
private noncomputable abbrev uniqueBand (k : ℕ) (hk : k ≤ N) :
    Unique {x : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ)
        (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) ∩
      (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) ⁻¹'
        Ioc (((k : ℤ) : ℝ) - 1 / 2) ((((k : ℤ) + 1 : ℤ) : ℝ) - 1 / 2)) //
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ)
        (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) x = k} where
  default := ⟨⟨mk ℝ (Pi.single (⟨k, by omega⟩ : Fin (N + 1)) 1) (by simp),
      mk_single_mem_criticalPoints_projectiveMomentFunction _ _, by
        rw [mem_preimage, projectiveMomentFunction_mk_single]
        push_cast
        constructor <;> linarith⟩,
    manifoldMorseIndex_projectiveMomentFunction_natCast_real _⟩
  uniq := by
    rintro ⟨⟨x, hx, hfx⟩, -⟩
    obtain ⟨j, hj, rfl⟩ :=
      exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast hx
        (Ioc_subset_Icc_self hfx)
    replace hj : (j : ℕ) = k := by exact_mod_cast hj
    rcases j with ⟨j, hjN⟩
    simp only at hj
    subst hj
    rfl

section SpectralSequence

open CategoryTheory Limits

variable {A : Type*} [Category A] [Abelian A] [HasCoproducts.{0} A] (R : A) (N)

/-- The spectral sequence of the critical-band filtration of `ℝℙᴺ` by the sublevels
`{f ≤ q - 1/2}`, `q : ℤ`, of the moment function `f [v] = (∑ i, i vᵢ²) / ∑ i, vᵢ²`, with
coefficients in `R`. Its first page (numbered `2`) has at `(p, q)` the relative homology
`Hₙ({f ≤ q + 1/2}, {f ≤ q - 1/2}; R)`, `p + q = -n`, of the band around the critical value `q`. -/
noncomputable abbrev realProjectiveMomentSpectralSequence :=
  filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ))).comp
      (isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := N)).monotone)

variable {N}

/-- **The first page on the critical points.** On the first page of the spectral sequence of the
critical-band filtration of `ℝℙᴺ`, the object at `(-2k, k)`, `k ≤ N`, is the relative homology
`Hₖ` of the band around the critical point `[eₖ]` of index `k`, a copy of the coefficients. -/
theorem nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso (k : ℕ) (hk : k ≤ N) :
    Nonempty (((realProjectiveMomentSpectralSequence N R).page 2).X
      ((-(2 * k : ℤ), (k : ℤ)) : ℤ × ℤ) ≅ R) := by
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ)
    (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) (Nat.cast_injective.comp Fin.val_injective)
  have ha := isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := N)
  obtain ⟨e⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha.monotone
    (ha.isCriticalBand k) (-(2 * k : ℤ), (k : ℤ)) rfl k (by push_cast; ring)
  have := uniqueBand k hk
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- **The first page off the critical points.** On the first page of the spectral sequence of
the critical-band filtration of `ℝℙᴺ`, every object outside the positions `(-2k, k)`, `k ≤ N`,
is zero. -/
theorem isZero_realProjectiveMomentSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (h : ∀ k : ℕ, k ≤ N → pq ≠ (-(2 * k : ℤ), (k : ℤ))) :
    IsZero (((realProjectiveMomentSpectralSequence N R).page 2).X pq) := by
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ)
    (w := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℝ)) (Nat.cast_injective.comp Fin.val_injective)
  have ha := isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := N)
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  refine hf.isZero_filteredSpaceSpectralSequence_page_two_X R ha.monotone (ha.isCriticalBand _)
    pq rfl n hn fun x hx hfx hidx ↦ ?_
  obtain ⟨j, hj, rfl⟩ :=
    exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast hx
      (Ioc_subset_Icc_self hfx)
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast_real] at hidx
  refine h j (by omega) (Prod.ext ?_ hj.symm)
  simp only
  omega

end SpectralSequence

section Plane

open CategoryTheory Limits

/-- The critical-band filtration `q ↦ {f ≤ q - 1/2}` of `ℝℙ²`. -/
private abbrev filt : ℤ → Set (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) :=
  (fun b ↦ {x | projectiveMomentFunction ℝ (fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) x ≤ b}) ∘
    fun q : ℤ ↦ (q : ℝ) - 1 / 2

/-- The critical-band filtration of `ℝℙ²` is increasing. -/
private theorem monotone_filt : Monotone filt :=
  (sublevel_mono _).comp
    (isCriticalBandCut_projectiveMomentFunction_natCast (𝕜 := ℝ) (n := 2)).monotone

/-- The disc `{f ≤ 1/2}` around the minimum is contractible. -/
private theorem contractibleSpace_filt_one : ContractibleSpace (filt 1) :=
  contractibleSpace_sublevel_projectiveMomentFunction_natCast (n := 2)
    (c := ((1 : ℤ) : ℝ) - 1 / 2) (by norm_num) (by norm_num)

/-- The last stage `{f ≤ 5/2}` of the filtration is all of `ℝℙ²`. -/
private def filtThreeHomeomorph : filt 3 ≃ₜ RealProjectiveSpace 2 :=
  (Homeomorph.setCongr (eq_univ_of_forall fun x ↦
      (projectiveMomentFunction_le (c := 2) (fun i ↦ by exact_mod_cast Nat.le_of_lt_succ i.2)
        x).trans (by norm_num))).trans
    ((Homeomorph.Set.univ _).trans (RealProjectiveSpace.homeomorphProjectivization 2).symm)

/-- The homology of the pair `({f ≤ 5/2}, {f ≤ 1/2})` is the homology of `ℝℙ²` in positive
degrees. -/
private def singularHomologyFiltPairIso (k : ℕ) :
    (TopPair.ofInclusion (monotone_filt (by norm_num : (1 : ℤ) ≤ 3))).singularHomology
        (ModuleCat.of ℤ ℤ) (k + 1) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (RealProjectiveSpace 2)) :=
  have : ContractibleSpace
      (TopPair.ofInclusion (monotone_filt (by norm_num : (1 : ℤ) ≤ 3))).snd :=
    contractibleSpace_filt_one
  have := TopPair.isIso_singularHomologyπ_of_contractibleSpace
    (TopPair.ofInclusion (monotone_filt (by norm_num : (1 : ℤ) ≤ 3))) (ModuleCat.of ℤ ℤ) k
  (asIso (TopPair.singularHomologyπ _ _ (k + 1))).symm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo filtThreeHomeomorph)

/-- `H₂(ℝℙ², {f ≤ 1/2}; ℤ) = 0`. -/
private theorem isZero_singularHomology_filtPair_two :
    IsZero ((TopPair.ofInclusion (monotone_filt (by norm_num : (1 : ℤ) ≤ 3))).singularHomology
      (ModuleCat.of ℤ ℤ) 2) :=
  (RealProjectiveSpace.isZero_singularHomology_int_of_even (N := 2) (k := 2) (by decide)
    (by decide)).of_iso (singularHomologyFiltPairIso 1)

/-- `H₁(ℝℙ², {f ≤ 1/2}; ℤ) ≅ ℤ/2`. -/
private def singularHomologyFiltPairOneIso :
    (TopPair.ofInclusion (monotone_filt (by norm_num : (1 : ℤ) ≤ 3))).singularHomology
      (ModuleCat.of ℤ ℤ) 1 ≅ ModuleCat.of ℤ (ZMod 2) :=
  singularHomologyFiltPairIso 0 ≪≫
    (RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd (N := 2) (k := 1) odd_one
      (by norm_num)).toModuleIso

/-- `H₁({f ≤ 5/2}, {f ≤ 3/2}; ℤ) = 0`: the band around the maximum has no critical point of
index `1`. -/
private theorem isZero_singularHomology_filtPair_upper_one :
    IsZero ((TopPair.ofInclusion (monotone_filt (by norm_num : (2 : ℤ) ≤ 3))).singularHomology
      (ModuleCat.of ℤ ℤ) 1) :=
  (isZero_realProjectiveMomentSpectralSequence_page_two_X (ModuleCat.of ℤ ℤ) (-3, 2)
    fun k _ h ↦ by simp only [Prod.ext_iff] at h; omega).of_iso
    (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of ℤ ℤ) monotone_filt (-3, 2) 2 3 rfl
      rfl (-1) rfl 1 rfl).symm

/-- The triple `({f ≤ 5/2}, {f ≤ 3/2}, {f ≤ 1/2})` of the first differential from the maximum to
the saddle. -/
private abbrev upperTriple : TopTriple :=
  TopTriple.ofInclusions (monotone_filt (by norm_num : (1 : ℤ) ≤ 2))
    (monotone_filt (by norm_num : (2 : ℤ) ≤ 3))

/-- The connecting map `H₂({f ≤ 5/2}, {f ≤ 3/2}) ⟶ H₁({f ≤ 3/2}, {f ≤ 1/2})` is injective, since
`H₂(ℝℙ², {f ≤ 1/2}) = 0`. -/
private theorem mono_singularHomologyδ_upperTriple :
    Mono (upperTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1) :=
  (upperTriple.singularHomology_exact_outer (ModuleCat.of ℤ ℤ) 2 1).mono_g
    (isZero_singularHomology_filtPair_two.eq_of_src _ _)

/-- The map `H₁({f ≤ 3/2}, {f ≤ 1/2}) ⟶ H₁({f ≤ 5/2}, {f ≤ 1/2})` is surjective, since
`H₁({f ≤ 5/2}, {f ≤ 3/2}) = 0`. -/
private theorem epi_singularHomologyMap_innerToTotal_upperTriple :
    Epi (TopPair.singularHomologyMap (TopTriple.innerToTotal.app upperTriple)
      (ModuleCat.of ℤ ℤ) 1) :=
  (upperTriple.singularHomology_exact_total (ModuleCat.of ℤ ℤ) 1).epi_f
    (isZero_singularHomology_filtPair_upper_one.eq_of_tgt _ _)

/-- The cokernel of the connecting map `H₂({f ≤ 5/2}, {f ≤ 3/2}) ⟶ H₁({f ≤ 3/2}, {f ≤ 1/2})` is
`H₁(ℝℙ², {f ≤ 1/2}) ≅ ℤ/2`. -/
private def cokernelSingularHomologyδUpperTripleIso :
    cokernel (upperTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1) ≅ ModuleCat.of ℤ (ZMod 2) :=
  have := epi_singularHomologyMap_innerToTotal_upperTriple
  (cokernelIsCokernel _).coconePointUniqueUpToIso
      (upperTriple.singularHomology_exact_inner (ModuleCat.of ℤ ℤ) 2 1).gIsCokernel ≪≫
    singularHomologyFiltPairOneIso

/-- The object of the maximum on the first page is `H₂({f ≤ 5/2}, {f ≤ 3/2})`. -/
private def maxFirstPageXIso :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-4, 2) ≅
      (TopTriple.outerPair.obj upperTriple).singularHomology (ModuleCat.of ℤ ℤ) 2 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of ℤ ℤ) monotone_filt (-4, 2) 2 3 rfl rfl
    (-2) rfl 2 rfl

/-- The object of the saddle on the first page is `H₁({f ≤ 3/2}, {f ≤ 1/2})`. -/
private def saddleFirstPageXIso :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-2, 1) ≅
      (TopTriple.innerPair.obj upperTriple).singularHomology (ModuleCat.of ℤ ℤ) 1 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of ℤ ℤ) monotone_filt (-2, 1) 1 2 rfl rfl
    (-1) rfl 1 rfl

/-- The first differential from the maximum to the saddle is the connecting map of the triple
`({f ≤ 5/2}, {f ≤ 3/2}, {f ≤ 1/2})`. The general identification
`filteredSpaceSpectralSequence_first_page_d_eq` is stated at the positions `(p, q)` and
`(p + 2, q - 1)`, in degrees `n + 1` and `n`; here these integers are numerals, and the statement
agrees with it by evaluating the arithmetic on numerals. -/
private theorem page_two_d_eq :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d (-4, 2) (-2, 1) =
      maxFirstPageXIso.hom ≫ upperTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 2 1 ≫
        saddleFirstPageXIso.inv :=
  filteredSpaceSpectralSequence_first_page_d_eq (ModuleCat.of ℤ ℤ) monotone_filt 2 (-4) 1
    (by norm_num)

/-- **The first differential from the maximum to the saddle is injective.** On the first page of
the spectral sequence of the critical-band filtration of `ℝℙ²` with integer coefficients, the
differential from `(-4, 2)`, the copy of `ℤ` of the maximum, to `(-2, 1)`, the copy of `ℤ` of the
saddle, is a monomorphism. -/
theorem mono_realProjectiveMomentSpectralSequence_page_two_d :
    Mono (((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
      (-4, 2) (-2, 1)) := by
  have := mono_singularHomologyδ_upperTriple
  rw [page_two_d_eq]
  infer_instance

/-- **The first differential from the maximum to the saddle has cokernel `ℤ/2`.** -/
theorem nonempty_cokernel_realProjectiveMomentSpectralSequence_page_two_d_iso :
    Nonempty (cokernel (((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
      (-4, 2) (-2, 1)) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  rw [page_two_d_eq]
  exact ⟨cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    cokernelSingularHomologyδUpperTripleIso⟩

/-- **The first differential from the maximum to the saddle is multiplication by `±2`.** Whatever
identifications of the objects `(-4, 2)` and `(-2, 1)` of the first page with `ℤ` are chosen, the
differential between them becomes multiplication by `2` or by `-2`. -/
theorem realProjectiveMomentSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul
    (e₁ : ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-4, 2) ≅
      ModuleCat.of ℤ ℤ)
    (e₂ : ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-2, 1) ≅
      ModuleCat.of ℤ ℤ) :
    e₁.inv ≫ ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
        (-4, 2) (-2, 1) ≫ e₂.hom = (2 : ℤ) • 𝟙 _ ∨
      e₁.inv ≫ ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
        (-4, 2) (-2, 1) ≫ e₂.hom = (-2 : ℤ) • 𝟙 _ := by
  set φ := e₁.inv ≫ ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d
    (-4, 2) (-2, 1) ≫ e₂.hom
  -- An endomorphism of `ℤ` is multiplication by its value `m` at `1`, with cokernel `ℤ/m`.
  set m := φ.hom 1
  have hφ : φ.hom = LinearMap.toSpanSingleton ℤ ℤ m := LinearMap.ext_ring (by simp [m])
  obtain ⟨e⟩ := nonempty_cokernel_realProjectiveMomentSpectralSequence_page_two_d_iso
  have hcard : Nat.card (ZMod 2) = m.natAbs :=
    calc Nat.card (ZMod 2) = Nat.card (cokernel φ : ModuleCat ℤ) :=
          Nat.card_congr
            (cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ e).toLinearEquiv.toEquiv.symm
      _ = Nat.card (ℤ ⧸ LinearMap.range φ.hom) :=
          Nat.card_congr (ModuleCat.cokernelIsoRangeQuotient φ).toLinearEquiv.toEquiv
      _ = Nat.card (ℤ ⧸ Ideal.span {m}) := by
          rw [hφ, ← LinearMap.span_singleton_eq_range]
      _ = m.natAbs := (Nat.card_congr (Int.quotientSpanEquivZMod m).toEquiv).trans
          (Nat.card_zmod _)
  rw [Nat.card_zmod] at hcard
  have hφm : φ = m • 𝟙 _ := by
    ext
    simp [hφ, mul_comm]
  rcases Int.natAbs_eq m with h | h <;> rw [← hcard] at h <;> rw [hφm, h] <;> simp

/-- The triple `({f ≤ 3/2}, {f ≤ 1/2}, {f ≤ -1/2})` of the first differential from the saddle to the
minimum; its last stage is empty. -/
private abbrev lowerTriple : TopTriple :=
  TopTriple.ofInclusions (monotone_filt (by norm_num : (0 : ℤ) ≤ 1))
    (monotone_filt (by norm_num : (1 : ℤ) ≤ 2))

/-- The connecting map `H₁({f ≤ 3/2}, {f ≤ 1/2}) ⟶ H₀({f ≤ 1/2}, {f ≤ -1/2})` vanishes: it factors
through the connecting map of the pair `({f ≤ 3/2}, {f ≤ 1/2})`, which vanishes because `H₀` of
the contractible `{f ≤ 1/2}` injects into `H₀({f ≤ 3/2})`. -/
private theorem singularHomologyδ_lowerTriple_eq_zero :
    lowerTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 = 0 := by
  have : ContractibleSpace (TopTriple.outerPair.obj lowerTriple).snd := contractibleSpace_filt_one
  have h := ((TopTriple.outerPair.obj lowerTriple).map.mono_singularHomologyMap_of_isZero
    (ModuleCat.of ℤ ℤ) (isZero_reducedSingularHomologyFunctor_of_contractibleSpace
      (ModuleCat.of ℤ ℤ) _ 0)).right_cancellation _ _
    (((TopTriple.outerPair.obj lowerTriple).singularHomologyδ_comp (ModuleCat.of ℤ ℤ) 1 0
      rfl).trans zero_comp.symm)
  rw [lowerTriple.singularHomologyδ_eq_comp_singularHomologyπ (ModuleCat.of ℤ ℤ) 1 0 rfl, h]
  exact zero_comp

/-- The object of the minimum on the first page is `H₀({f ≤ 1/2}, {f ≤ -1/2})`. -/
private def minFirstPageXIso :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (0, 0) ≅
      (TopTriple.innerPair.obj lowerTriple).singularHomology (ModuleCat.of ℤ ℤ) 0 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of ℤ ℤ) monotone_filt (0, 0) 0 1 rfl rfl
    0 rfl 0 rfl

/-- The object of the saddle on the first page, as the relative homology of the outer pair of the
triple `({f ≤ 3/2}, {f ≤ 1/2}, {f ≤ -1/2})`. -/
private def saddleLowerFirstPageXIso :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).X (-2, 1) ≅
      (TopTriple.outerPair.obj lowerTriple).singularHomology (ModuleCat.of ℤ ℤ) 1 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of ℤ ℤ) monotone_filt (-2, 1) 1 2 rfl rfl
    (-1) rfl 1 rfl

/-- The first differential from the saddle to the minimum vanishes. -/
private theorem page_two_d_saddle_eq_zero :
    ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d (-2, 1) (0, 0) = 0 := by
  have h : ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2).d (-2, 1) (0, 0) =
      saddleLowerFirstPageXIso.hom ≫ lowerTriple.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 ≫
        minFirstPageXIso.inv :=
    filteredSpaceSpectralSequence_first_page_d_eq (ModuleCat.of ℤ ℤ) monotone_filt 1 (-2) 0
      (by norm_num)
  rw [h, singularHomologyδ_lowerTriple_eq_zero, zero_comp, comp_zero]

/-- On the first page, the position before `pq + (2, -1)` is `pq`. -/
private theorem prev_page_two (pq pq' : ℤ × ℤ) (h₁ : pq.1 + 2 = pq'.1) (h₂ : pq.2 - 1 = pq'.2) :
    (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).prev pq' = pq :=
  (ComplexShape.up' _).prev_eq' (Prod.ext h₁ (by simp only [Prod.snd_add]; lia))

/-- On the first page, the position after `pq` is `pq + (2, -1)`. -/
private theorem next_page_two (pq pq' : ℤ × ℤ) (h₁ : pq.1 + 2 = pq'.1) (h₂ : pq.2 - 1 = pq'.2) :
    (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).next pq = pq' :=
  (ComplexShape.up' _).next_eq' (Prod.ext h₁ (by simp only [Prod.snd_add]; lia))

/-- **The second page at the maximum vanishes.** On the second page (numbered `3`) of the
spectral sequence of the critical-band filtration of `ℝℙ²` with integer coefficients, the object
at `(-4, 2)` of the maximum is zero: the first differential out of it is injective. -/
theorem isZero_realProjectiveMomentSpectralSequence_page_three_X_neg_four_two :
    IsZero (((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (-4, 2)) := by
  set K := (realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2
  have := mono_realProjectiveMomentSpectralSequence_page_two_d
  refine IsZero.of_iso ?_ ((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).iso 2 3
    (-4, 2)).symm
  refine IsZero.of_iso ?_ (K.homologyIsoSc' (-6, 3) (-4, 2) (-2, 1)
    (prev_page_two (-6, 3) (-4, 2) (by norm_num) (by norm_num))
    (next_page_two (-4, 2) (-2, 1) (by norm_num) (by norm_num)))
  refine (ShortComplex.exact_iff_isZero_homology _).1
    ((ShortComplex.exact_iff_mono (K.sc' (-6, 3) (-4, 2) (-2, 1))
      ((isZero_realProjectiveMomentSpectralSequence_page_two_X (ModuleCat.of ℤ ℤ) (-6, 3)
        fun k hk h ↦ ?_).eq_of_src _ _)).2 this)
  simp only [Prod.ext_iff] at h
  omega

/-- **The second page at the saddle is `ℤ/2`.** On the second page (numbered `3`) of the spectral
sequence of the critical-band filtration of `ℝℙ²` with integer coefficients, the object at
`(-2, 1)` of the saddle is the cokernel `ℤ/2` of the first differential from the maximum. -/
theorem nonempty_realProjectiveMomentSpectralSequence_page_three_X_neg_two_one_iso :
    Nonempty (((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (-2, 1) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  set K := (realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2
  obtain ⟨e⟩ := nonempty_cokernel_realProjectiveMomentSpectralSequence_page_two_d_iso
  exact ⟨((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).iso 2 3 (-2, 1)).symm ≪≫
    K.isoHomologyι (-2, 1) (0, 0) (next_page_two (-2, 1) (0, 0) (by norm_num) (by norm_num))
      page_two_d_saddle_eq_zero ≪≫
    (K.opcyclesIsCokernel (-4, 2) (-2, 1)
      (prev_page_two (-4, 2) (-2, 1) (by norm_num) (by norm_num))).coconePointUniqueUpToIso
      (cokernelIsCokernel _) ≪≫ e⟩

/-- **The second page at the minimum is `ℤ`.** On the second page (numbered `3`) of the spectral
sequence of the critical-band filtration of `ℝℙ²` with integer coefficients, the object at
`(0, 0)` of the minimum is still a copy of `ℤ`. -/
theorem nonempty_realProjectiveMomentSpectralSequence_page_three_X_zero_zero_iso :
    Nonempty (((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 3).X (0, 0) ≅
      ModuleCat.of ℤ ℤ) := by
  set K := (realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).page 2
  obtain ⟨e⟩ := nonempty_realProjectiveMomentSpectralSequence_page_two_X_iso (N := 2)
    (ModuleCat.of ℤ ℤ) 0 (by norm_num)
  have hd : K.d (0, 0) (2, -1) = 0 :=
    (isZero_filteredSpaceSpectralSequence_page_two_X (ModuleCat.of ℤ ℤ) monotone_filt (2, -1)
      (by norm_num)).eq_of_tgt _ _
  exact ⟨((realProjectiveMomentSpectralSequence 2 (ModuleCat.of ℤ ℤ)).iso 2 3 (0, 0)).symm ≪≫
    (K.isoHomologyπ (-2, 1) (0, 0) (prev_page_two (-2, 1) (0, 0) (by norm_num) (by norm_num))
      page_two_d_saddle_eq_zero).symm ≪≫
    K.iCyclesIso (0, 0) (2, -1) (next_page_two (0, 0) (2, -1) (by norm_num) (by norm_num)) hd ≪≫ e⟩

end Plane

end TauCeti
