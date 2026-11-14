/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.RankLocus
public import TauCeti.RingTheory.Grassmannian.Schubert

import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Grassmannian.Proper
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Schubert cells and Schubert rank subschemes of the Grassmannian

Let `M` be a free module over a commutative ring `R` with a basis `b` indexed by `Fin n`, and let
`F_j = b.flag j` be the complete flag spanned by its first `j` basis vectors. For strictly
increasing zero-based pivot positions `p : Fin r → Fin n`, `Module.Grassmannian.schemeSchubertLocus`
cuts out the determinantal Schubert rank subscheme `X_p` of `G(k, M) = Module.Grassmannian.scheme`
where each `F_{p i + 1}` maps to the universal quotient with rank at most `p i - i`.

This file establishes the scheme-theoretic properties of extreme Grassmannians, Schubert rank
subschemes, and Schubert cells:

* **Extreme dimensions:** `G(k, M)` is empty when `n < k` (`isEmpty_scheme_of_lt`), whereas the
  structure morphism `toSpec R M k : G(k, M) ⟶ Spec R` is an isomorphism for `k = 0` and arbitrary
  `M` (`isIso_toSpec_zero`) and for `k = n` when `M` has a basis of size `n`
  (`isIso_toSpec_of_basis`).
* **Full-flag presentation and Bruhat order:** `schemeSchubertLocus k b p` agrees with the
  rank-condition subscheme imposing the rank bounds at all `n + 1` steps of `b.flag`
  (`schemeSchubertLocus_eq_schemeRankLocus_flag`), is antitone in `p` as an ideal sheaf
  (`schemeSchubertLocus_antitone`) — and reverses the coordinatewise Bruhat order precisely when
  `R` is nontrivial and `r + k = n` (`schemeSchubertLocus_le_iff`) — and vanishes for the top pivot
  tuple `p i = k + i` (`schemeSchubertLocus_top_eq_bot`).
* **Schubert cell scheme and open immersion:** when `r + k = n`, the affine space
  `Spec (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)` embeds as a closed subscheme of
  the adapted standard chart (`schubertCellToChart`) and as an open subscheme of
  `(schemeSchubertLocus k b p).subscheme` (`schubertCellToLocus`), forming a Cartesian square over
  `G(k, M)` (`isPullback_schubertCellToChart_schubertCellToLocus`).
* **Zariski closure and reduced schematic image:** the Zariski closure of the Schubert cell
  `schubertCellι b hp hnk` in `G(k, M)` is the support of `schemeSchubertLocus k b p` over any
  commutative ring `R` (`closure_range_schubertCellι`). Consequently, the schematic image ideal
  sheaf `(schubertCellι b hp hnk).ker` and `schemeSchubertLocus k b p` have the same radical
  (`radical_ker_schubertCellι`), and when `R` is reduced the schematic image of the Schubert cell is
  the reduced induced subscheme `(schemeSchubertLocus k b p).radical`
  (`ker_schubertCellι_eq_radical`), which is integral when `R` is a domain
  (`isIntegral_subscheme_radical_schemeSchubertLocus`).

## Main definitions

* `Module.Grassmannian.schubertCellToChart b hp hnk`: the closed immersion from the Schubert cell
  affine space into the adapted standard chart.
* `Module.Grassmannian.schubertCellι b hp hnk`: the immersion of the Schubert cell into `G(k, M)`.
* `Module.Grassmannian.schubertCellToLocus b hp hnk`: the open immersion of the Schubert cell into
  `(schemeSchubertLocus k b p).subscheme`.

## Main results

* `Module.Grassmannian.isEmpty_scheme_of_lt`, `Module.Grassmannian.isIso_toSpec_zero`, and
  `Module.Grassmannian.isIso_toSpec_of_basis`: extreme Grassmannian schemes.
* `Module.Grassmannian.schemeSchubertLocus_eq_schemeRankLocus_flag` and
  `Module.Grassmannian.schemeSchubertLocus_le_iff`: full-flag presentation and Bruhat order.
* `Module.Grassmannian.isPullback_schubertCellToChart_schubertCellToLocus`: the Schubert cell is the
  intersection of `schemeSchubertLocus k b p` with the adapted chart, hence an open subscheme of
  `(schemeSchubertLocus k b p).subscheme`.
* `Module.Grassmannian.closure_range_schubertCellι`: the Zariski closure of the Schubert cell is
  `(schemeSchubertLocus k b p).support`.
* `Module.Grassmannian.radical_ker_schubertCellι` and
  `Module.Grassmannian.ker_schubertCellι_eq_radical`: comparison of the schematic image of the
  Schubert cell with the radical of `schemeSchubertLocus k b p`.

## References

* W. Fulton, *Young tableaux*, London Mathematical Society Student Texts 35, Cambridge University
  Press (1997), §9.4.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and
  Monographs 107, American Mathematical Society (2003), Part II, Chapter 13.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Module Finset Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

/-! ### Extreme Grassmannian schemes -/

section Extreme

/-- When `M` has a basis of size `n < k`, the Grassmannian scheme `G(k, M)` is empty. -/
theorem isEmpty_scheme_of_lt {n : ℕ} (b : Basis (Fin n) R M) (h : n < k) :
    IsEmpty (scheme R M k) := by
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨x, y, -⟩ := chartι_jointly_surjective z
  have : Nontrivial (ChartAlgebra R x ⧸ y.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr y.isPrime.ne_top
  exact (isEmpty_of_lt (A := ChartAlgebra R x ⧸ y.asIdeal) b h).false
    (chartHomEquiv R x _ (Ideal.Quotient.mkₐ R y.asIdeal)).1

/-- The inclusion `chartι R x` classifies the universal point of `ChartAlgebra R x`. -/
private theorem toSchemeHom_chartHomEquiv_id (x : Fin k → M) :
    toSchemeHom (chartHomEquiv R x (ChartAlgebra R x) (AlgHom.id R _)).1 = chartι R x := by
  have hid : CommRingCat.ofHom
      ((AlgHom.id R (ChartAlgebra R x) : ChartAlgebra R x →ₐ[R] ChartAlgebra R x) :
        ChartAlgebra R x →+* ChartAlgebra R x) = 𝟙 (CommRingCat.of (ChartAlgebra R x)) :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
  rw [toSchemeHom_chartHomEquiv, hid, Spec.map_id, Category.id_comp]

/-- If `G(k, A ⊗[R] M; A)` is a singleton for every `R`-algebra `A`, then the structure morphism
`toSpec R M k : G(k, M) ⟶ Spec R` is an isomorphism. -/
private theorem isIso_toSpec_of_unique
    (hU : ∀ (A : Type u) [CommRing A] [Algebra R A], Unique G(k, A ⊗[R] M; A)) :
    IsIso (toSpec R M k) := by
  let inv : Spec (.of R) ⟶ scheme R M k := toSchemeHom (hU R).default
  refine ⟨inv, ?_, ?_⟩
  · refine (Scheme.Cover.mkOfCovers (Fin k → M) _ (chartι R)
      chartι_jointly_surjective : (scheme R M k).OpenCover).hom_ext _ _ fun x₀ ↦ ?_
    let x : Fin k → M := x₀
    let A := ChartAlgebra R x
    change chartι R x ≫ toSpec R M k ≫ inv = chartι R x ≫ 𝟙 (scheme R M k)
    -- Unfold the cover index `x₀` and component map to `chartι R x`.
    have h₁ : chartι R x ≫ toSpec R M k ≫ inv =
        toSchemeHom (map (IsScalarTower.toAlgHom R R A) (hU R).default) := by
      rw [chartι_toSpec_assoc, ← IsScalarTower.coe_toAlgHom R R A, ← toSchemeHom_map]
    have h₂ : chartι R x ≫ 𝟙 (scheme R M k) =
        toSchemeHom (chartHomEquiv R x A (AlgHom.id R A)).1 := by
      rw [Category.comp_id, ← toSchemeHom_chartHomEquiv_id x]
    let _ := hU A
    exact h₁.trans ((congrArg toSchemeHom (Subsingleton.elim _ _)).trans h₂.symm)
  · have hid : CommRingCat.ofHom (algebraMap R R) = 𝟙 (CommRingCat.of R) :=
      CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
    rw [toSchemeHom_toSpec, hid, Spec.map_id]

/-- For every module `M`, the structure morphism `G(0, M) ⟶ Spec R` is an isomorphism. -/
instance isIso_toSpec_zero : IsIso (toSpec R M 0) :=
  isIso_toSpec_of_unique fun _ _ _ ↦ uniqueZero

/-- When `M` has a basis indexed by `Fin n`, the structure morphism `G(n, M) ⟶ Spec R` is an
isomorphism. -/
theorem isIso_toSpec_of_basis {n : ℕ} (b : Basis (Fin n) R M) : IsIso (toSpec R M n) :=
  isIso_toSpec_of_unique fun A _ _ ↦ uniqueOfBasis b A

end Extreme

/-! ### Full-flag presentation and Bruhat order of Schubert rank subschemes -/

section Bruhat

variable {n r : ℕ}

/-- Pulling back `schemeRankLocus k F s` along the standard chart `chartι R x` gives the ideal sheaf
generated by the universal rank-locus ideal on `ChartAlgebra R x`. -/
private theorem comap_chartι_schemeRankLocus {ι : Sort*} (F : ι → Submodule R M) (s : ι → ℕ)
    (x : Fin k → M) :
    (schemeRankLocus k F s).comap (chartι R x) =
      ofIdealTop ((⨆ i, (chartHomEquiv R x _ (AlgHom.id R _)).1.rankLocus (F i) (s i)).map
        (Scheme.ΓSpecIso (.of (ChartAlgebra R x))).inv.hom) := by
  rw [← toSchemeHom_chartHomEquiv_id x, comap_toSchemeHom_schemeRankLocus]

/-- Containment of the universal rank-locus ideals on every standard chart implies containment of
the rank-condition ideal sheaves on `G(k, M)`. -/
private theorem schemeRankLocus_le_of_iSup_le {ι₁ ι₂ : Sort*}
    (F₁ : ι₁ → Submodule R M) (s₁ : ι₁ → ℕ) (F₂ : ι₂ → Submodule R M) (s₂ : ι₂ → ℕ)
    (hle : ∀ x : Fin k → M,
      (⨆ i, (chartHomEquiv R x _ (AlgHom.id R _)).1.rankLocus (F₁ i) (s₁ i)) ≤
        ⨆ j, (chartHomEquiv R x _ (AlgHom.id R _)).1.rankLocus (F₂ j) (s₂ j)) :
    schemeRankLocus k F₁ s₁ ≤ schemeRankLocus k F₂ s₂ := by
  let 𝒰 : (scheme R M k).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin k → M) _ (chartι R) chartι_jointly_surjective
  rw [← (schemeRankLocus k F₁ s₁).iInf_map_comap_openCover 𝒰,
    ← (schemeRankLocus k F₂ s₂).iInf_map_comap_openCover 𝒰]
  refine iInf_mono fun x₀ ↦ map_mono (𝒰.f x₀) ?_
  let x : Fin k → M := x₀
  change (schemeRankLocus k F₁ s₁).comap (chartι R x) ≤
    (schemeRankLocus k F₂ s₂).comap (chartι R x)
  -- `𝒰.f x₀` is definitionally `chartι R x` for `x : Fin k → M`.
  rw [comap_chartι_schemeRankLocus, comap_chartι_schemeRankLocus, ← equivOfIsAffine_symm_apply,
    ← equivOfIsAffine_symm_apply, map_le_map_iff]
  exact Ideal.map_mono (hle x)

/-- **Full-flag presentation of the Schubert rank subscheme.** For strictly increasing pivot
positions `p : Fin r → Fin n`, the Schubert rank locus `schemeSchubertLocus k b p` cut out by the
`r` jump conditions agrees with the rank-condition subscheme imposing the rank bounds at all
`n + 1` subspaces of the complete flag `b.flag`. -/
theorem schemeSchubertLocus_eq_schemeRankLocus_flag (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) :
    schemeSchubertLocus k b p =
      schemeRankLocus k b.flag (fun j ↦ (j : ℕ) - #{i : Fin r | (p i).castSucc < j}) := by
  rw [schemeSchubertLocus_def]
  exact le_antisymm
    (schemeRankLocus_le_of_iSup_le _ _ _ _ fun _ ↦ (iSup_rankLocus_flag_succ_eq b hp _).le)
    (schemeRankLocus_le_of_iSup_le _ _ _ _ fun _ ↦ (iSup_rankLocus_flag_succ_eq b hp _).ge)

/-- **Bruhat monotonicity of Schubert rank subschemes.** If `p' i ≤ p i` for every `i`, then the
ideal sheaf `schemeSchubertLocus k b p` is contained in `schemeSchubertLocus k b p'`, so the closed
subscheme `X_{p'}` is a closed subscheme of `X_p`. -/
theorem schemeSchubertLocus_antitone (b : Basis (Fin n) R M) {p p' : Fin r → Fin n}
    (hp : StrictMono p) (hp' : StrictMono p') (hle : ∀ i, p' i ≤ p i) :
    schemeSchubertLocus k b p ≤ schemeSchubertLocus k b p' := by
  rw [schemeSchubertLocus_def, schemeSchubertLocus_def]
  exact schemeRankLocus_le_of_iSup_le _ _ _ _ fun _ ↦
    iSup_rankLocus_flag_succ_antitone b hp hp' hle _

/-- **Bruhat order characterization of Schubert rank subschemes.** Over a nontrivial ring `R`, when
`r + k = n`, `schemeSchubertLocus k b p ≤ schemeSchubertLocus k b p'` holds if and only if
`p' i ≤ p i` for every `i`. -/
theorem schemeSchubertLocus_le_iff [Nontrivial R] (b : Basis (Fin n) R M) {p p' : Fin r → Fin n}
    (hp : StrictMono p) (hp' : StrictMono p') (hnk : r + k = n) :
    schemeSchubertLocus k b p ≤ schemeSchubertLocus k b p' ↔ ∀ i, p' i ≤ p i := by
  refine ⟨fun h ↦ ?_, schemeSchubertLocus_antitone b hp hp'⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let _ := Ideal.Quotient.field m
  let c := (schubertCellEquiv b hp' hnk (R ⧸ m)).symm 0
  have hc' : schemeSchubertLocus k b p' ≤ (toSchemeHom c.1.1).ker := by
    rw [schemeSchubertLocus_def, schemeRankLocus_le_ker_toSchemeHom_iff]
    exact c.2
  have hc : ∀ i, c.1.1.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥ := by
    have hker := h.trans hc'
    rwa [schemeSchubertLocus_def, schemeRankLocus_le_ker_toSchemeHom_iff] at hker
  obtain ⟨p₁, hp₁, hpiv₁, hle₁⟩ :=
    (forall_rankLocus_eq_bot_iff_exists_flagPivots b hp hnk c.1.1).mp hc
  have hpiv' : (b.baseChange (R ⧸ m)).flagPivots c.1.1.toSubmodule = univ.image p' :=
    (mem_chart_and_rankLocus_eq_bot_iff_flagPivots b hp' hnk c.1.1).mp ⟨c.1.2, c.2⟩
  have heq : p' = p₁ := (hp'.range_inj_of_wellFoundedLT hp₁).mp <| by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      congrArg (↑· : Finset (Fin n) → Set (Fin n)) (hpiv'.symm.trans hpiv₁)
  exact heq ▸ hle₁

/-- For the top pivot tuple `p i = k + i` (when `r + k = n`), the Schubert rank ideal sheaf vanishes
identically, so the corresponding closed subscheme is the whole Grassmannian `G(k, M)`. -/
theorem schemeSchubertLocus_top_eq_bot (b : Basis (Fin n) R M) (hnk : r + k = n) :
    schemeSchubertLocus k b (fun i : Fin r ↦ ⟨k + i, by omega⟩) = ⊥ := by
  let 𝒰 : (scheme R M k).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin k → M) _ (chartι R) chartι_jointly_surjective
  refine ext_of_comap_openCover 𝒰 fun x₀ ↦ ?_
  let x : Fin k → M := x₀
  change (schemeSchubertLocus k b _).comap (chartι R x) =
    (⊥ : (scheme R M k).IdealSheafData).comap (chartι R x)
  -- Compare pullbacks on each standard chart `chartι R x`.
  rw [schemeSchubertLocus_def, comap_chartι_schemeRankLocus,
    iSup_rankLocus_flag_succ_top_eq_bot b hnk, Ideal.map_bot, comap_bot, ofIdealTop_eq_bot_iff]

end Bruhat

/-! ### Schubert cell scheme and open immersion into `schemeSchubertLocus` -/

section Cell

variable {n r : ℕ}

/-- The closed immersion from the Schubert cell affine space
`Spec (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)` into the adapted standard chart of
`G(k, M)`, induced by `Module.Grassmannian.schubertChartAlgHom`. -/
noncomputable def schubertCellToChart (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    Spec (.of (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)) ⟶
      Spec (.of (ChartAlgebra R (fun j ↦ schubertChartBasis b hp hnk (.inr j)))) :=
  Spec.map (CommRingCat.ofHom (schubertChartAlgHom b hp hnk : _ →+* _))

instance isClosedImmersion_schubertCellToChart (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    IsClosedImmersion (schubertCellToChart b hp hnk) :=
  IsClosedImmersion.spec_of_surjective _ (schubertChartAlgHom_surjective b hp hnk)

/-- The immersion of the Schubert cell `C_p ≅ 𝔸^{∑ i, (p i - i)}_R` into the Grassmannian scheme
`G(k, M)`, obtained by composing `schubertCellToChart` with the adapted chart open immersion. -/
noncomputable def schubertCellι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    Spec (.of (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)) ⟶ scheme R M k :=
  schubertCellToChart b hp hnk ≫ chartι R (fun j ↦ schubertChartBasis b hp hnk (.inr j))

instance isPreimmersion_schubertCellι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    IsPreimmersion (schubertCellι b hp hnk) := by
  rw [schubertCellι]
  infer_instance

/-- `schubertCellι` is a morphism over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schubertCellι_toSpec (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    schubertCellι b hp hnk ≫ toSpec R M k =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial (Finset.univ.image p).echelonFreeEntries R))) := by
  rw [schubertCellι, schubertCellToChart, Category.assoc, chartι_toSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r ↦ (schubertChartAlgHom b hp hnk).commutes r)

/-- The morphism `Spec A ⟶ G(k, M)` classifying the Schubert cell point associated to an
`R`-algebra map `g` is `Spec.map g ≫ schubertCellι b hp hnk`. -/
@[simp]
theorem toSchemeHom_schubertCellHomEquiv (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) {A : Type u} [CommRing A] [Algebra R A]
    (g : MvPolynomial (Finset.univ.image p).echelonFreeEntries R →ₐ[R] A) :
    toSchemeHom (schubertCellHomEquiv b hp hnk A g).1.1 =
      Spec.map (CommRingCat.ofHom (g : _ →+* A)) ≫ schubertCellι b hp hnk := by
  have hcomp : (schubertCellHomEquiv b hp hnk A g).1.1 =
      (chartHomEquiv R _ A (g.comp (schubertChartAlgHom b hp hnk))).1 := by
    rw [chartHomEquiv_comp, chartHomEquiv_schubertChartAlgHom, ← schubertCellHomEquiv_comp,
      AlgHom.comp_id]
  rw [hcomp, toSchemeHom_chartHomEquiv, schubertCellι, schubertCellToChart,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, AlgHom.comp_toRingHom]

/-- **Scheme-theoretic intersection of `schemeSchubertLocus` with the adapted chart.** Pulling back
`schemeSchubertLocus k b p` along the adapted chart open immersion gives the kernel ideal sheaf of
the closed immersion `schubertCellToChart b hp hnk`. -/
theorem comap_chartι_schemeSchubertLocus (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    (schemeSchubertLocus k b p).comap
      (chartι R (fun j ↦ schubertChartBasis b hp hnk (.inr j))) =
      (schubertCellToChart b hp hnk).ker := by
  rw [schemeSchubertLocus_def, comap_chartι_schemeRankLocus, ← ker_schubertChartAlgHom b hp hnk,
    schubertCellToChart, Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom]
  rfl

/-- The open immersion of the Schubert cell `Spec (MvPolynomial ... R)` into the Schubert rank
subscheme `(schemeSchubertLocus k b p).subscheme`. -/
noncomputable def schubertCellToLocus (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    Spec (.of (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)) ⟶
      (schemeSchubertLocus k b p).subscheme :=
  IsClosedImmersion.lift (schemeSchubertLocus k b p).subschemeι (schubertCellι b hp hnk) <| by
    rw [ker_subschemeι, schubertCellι, Scheme.Hom.ker_comp, le_map_iff_comap_le,
      comap_chartι_schemeSchubertLocus]

@[reassoc (attr := simp)]
theorem schubertCellToLocus_subschemeι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    schubertCellToLocus b hp hnk ≫ (schemeSchubertLocus k b p).subschemeι =
      schubertCellι b hp hnk :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The Schubert cell is the pullback of `schemeSchubertLocus` to the adapted chart.** -/
theorem isPullback_schubertCellToChart_schubertCellToLocus (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) :
    IsPullback (schubertCellToChart b hp hnk) (schubertCellToLocus b hp hnk)
      (chartι R (fun j ↦ schubertChartBasis b hp hnk (.inr j)))
      (schemeSchubertLocus k b p).subschemeι := by
  refine isPullback_of_isClosedImmersion _ _ _ _
    (schubertCellToLocus_subschemeι b hp hnk).symm ?_
  rw [ker_subschemeι, comap_chartι_schemeSchubertLocus]

/-- **The Schubert cell embeds as an open subscheme of `(schemeSchubertLocus k b p).subscheme`.** -/
instance isOpenImmersion_schubertCellToLocus (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    IsOpenImmersion (schubertCellToLocus b hp hnk) :=
  MorphismProperty.of_isPullback
    (isPullback_schubertCellToChart_schubertCellToLocus b hp hnk) inferInstance

/-- **Functor-of-points characterization of `schubertCellι`.** A morphism `Spec A ⟶ G(k, M)`
classifying `N ∈ G(k, A ⊗[R] M; A)` factors through `schubertCellι b hp hnk` if and only if `N`
lies in the adapted chart and all Schubert rank loci of `p` vanish on `N`. -/
theorem exists_comp_schubertCellι_eq_toSchemeHom_iff (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) {A : Type u} [CommRing A]
    [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    (∃ f : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)),
      f ≫ schubertCellι b hp hnk = toSchemeHom N) ↔
      N ∈ chart A (fun j ↦ (1 : A) ⊗ₜ[R] schubertChartBasis b hp hnk (.inr j)) ∧
        ∀ i : Fin r, N.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥ := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    have hR : CommRingCat.ofHom
        (algebraMap R (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)) ≫ φ =
        CommRingCat.ofHom (algebraMap R A) :=
      Spec.map_injective <| by
        rw [Spec.map_comp, ← schubertCellι_toSpec b hp hnk, ← Category.assoc, hf,
          toSchemeHom_toSpec]
    let g : MvPolynomial (Finset.univ.image p).echelonFreeEntries R →ₐ[R] A :=
      { φ.hom with commutes' := fun r ↦ congr(($hR).hom r) }
    have hN : N = (schubertCellHomEquiv b hp hnk A g).1.1 :=
      toSchemeHom_injective (hf.symm.trans (toSchemeHom_schubertCellHomEquiv b hp hnk g).symm)
    rw [hN]
    exact ⟨(schubertCellHomEquiv b hp hnk A g).1.2, (schubertCellHomEquiv b hp hnk A g).2⟩
  · rintro ⟨hchart, hrank⟩
    let g := (schubertCellHomEquiv b hp hnk A).symm ⟨⟨N, hchart⟩, hrank⟩
    refine ⟨Spec.map (CommRingCat.ofHom (g : _ →+* A)), ?_⟩
    rw [← toSchemeHom_schubertCellHomEquiv b hp hnk g]
    simp [g]

/-- **Field points of `schubertCellι` via `flagPivots`.** Over a field `K`, the morphism
classifying `N ∈ G(k, K ⊗[R] M; K)` factors through `schubertCellι b hp hnk` if and only if
`(b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p`. -/
theorem exists_comp_schubertCellι_eq_toSchemeHom_iff_flagPivots (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) {K : Type u} [Field K]
    [Algebra R K] (N : G(k, K ⊗[R] M; K)) :
    (∃ f : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Finset.univ.image p).echelonFreeEntries R)),
      f ≫ schubertCellι b hp hnk = toSchemeHom N) ↔
      (b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p :=
  (exists_comp_schubertCellι_eq_toSchemeHom_iff b hp hnk N).trans
    (mem_chart_and_rankLocus_eq_bot_iff_flagPivots b hp hnk N)

/-- **Field points of `schemeSchubertLocus` via `flagPivots`.** Over a field `K` (with `r + k = n`),
the morphism classifying `N ∈ G(k, K ⊗[R] M; K)` factors through `schemeSchubertLocus k b p` if and
only if the strictly increasing pivot tuple `p'` of `N.toSubmodule` satisfies `p' ≤ p`
coordinatewise. -/
theorem schemeSchubertLocus_le_ker_toSchemeHom_iff_exists_flagPivots (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) {K : Type u} [Field K]
    [Algebra R K] (N : G(k, K ⊗[R] M; K)) :
    schemeSchubertLocus k b p ≤ (toSchemeHom N).ker ↔
      ∃ p' : Fin r → Fin n, StrictMono p' ∧
        (b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p' ∧
        ∀ i : Fin r, p' i ≤ p i := by
  rw [schemeSchubertLocus_def]
  exact (schemeRankLocus_le_ker_toSchemeHom_iff _ _ N).trans
    (forall_rankLocus_eq_bot_iff_exists_flagPivots b hp hnk N)

end Cell

/-! ### Zariski closure, irreducibility, and reduced schematic image -/

section Closure

variable {n r : ℕ}

/-- Induction on the Bruhat gap `∑ i, (p i - p' i)` using one-step `𝔸¹`-deformations shows that
every field-valued point with pivot tuple `p' ≤ p` lands in the Zariski closure of
`schubertCellι b hp hnk`. -/
private theorem range_toSchemeHom_subset_closure_aux (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) :
    ∀ (d : ℕ) {K : Type u} [Field K] [Algebra R K] (N : G(k, K ⊗[R] M; K))
      {p' : Fin r → Fin n}, StrictMono p' → (∀ i, p' i ≤ p i) →
      (b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p' →
      ∑ i, ((p i : ℕ) - p' i) = d →
      Set.range (toSchemeHom N) ⊆ closure (Set.range (schubertCellι b hp hnk)) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro K _ _ N p' hp' hle hpiv hd
    by_cases hne : p' = p
    · subst hne
      obtain ⟨f, hf⟩ := (exists_comp_schubertCellι_eq_toSchemeHom_iff_flagPivots b hp hnk N).mpr
        hpiv
      rintro _ ⟨q, rfl⟩
      rw [← hf, Scheme.Hom.comp_apply]
      exact subset_closure ⟨f q, rfl⟩
    · obtain ⟨N_poly, p'', hp'', hp''_le, hsum, hN₀, hpiv_gen⟩ :=
        exists_polynomial_deformation_of_flagPivots_lt b hp hp' hle hne N hpiv
      let P := Polynomial K
      let L := FractionRing P
      let ev₀ : P →ₐ[R] K := (Polynomial.aeval (0 : K)).restrictScalars R
      let ι : P →ₐ[R] L := IsScalarTower.toAlgHom R P L
      have hgen := ih _ (hd ▸ hsum) (map ι N_poly) hp'' hp''_le hpiv_gen rfl
      rintro _ ⟨q, rfl⟩
      let q_L : Spec (.of L) := (⊥ : PrimeSpectrum L)
      let q_gen : Spec (.of P) := Spec.map (CommRingCat.ofHom (ι : P →+* L)) q_L
      let q₀ : Spec (.of P) := Spec.map (CommRingCat.ofHom (ev₀ : P →+* K)) q
      let q_gen' : PrimeSpectrum P := q_gen
      let q₀' : PrimeSpectrum P := q₀
      have hq_gen_bot : q_gen'.asIdeal = ⊥ := by
        change Ideal.comap (ι : P →+* L) ⊥ = ⊥
        -- `Spec.map` acts on points of `PrimeSpectrum` by `PrimeSpectrum.comap`.
        rw [← RingHom.ker_eq_comap_bot]
        exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective P L)
      have hle_spec : q_gen' ≤ q₀' := show q_gen'.asIdeal ≤ q₀'.asIdeal from hq_gen_bot ▸ bot_le
      have hspec : toSchemeHom N_poly q_gen ⤳ toSchemeHom N_poly q₀ :=
        ((PrimeSpectrum.le_iff_specializes q_gen' q₀').mp hle_spec).map
          (toSchemeHom N_poly).continuous
      have heq_gen : toSchemeHom N_poly q_gen = toSchemeHom (map ι N_poly) q_L := by
        rw [toSchemeHom_map, Scheme.Hom.comp_apply]
      have heq₀ : toSchemeHom N_poly q₀ = toSchemeHom N q := by
        rw [← hN₀, toSchemeHom_map, Scheme.Hom.comp_apply]
      exact heq₀ ▸ hspec.mem_closed isClosed_closure (heq_gen ▸ hgen ⟨q_L, rfl⟩)

/-- Every field-valued point of `schemeSchubertLocus k b p` lands in the Zariski closure of the
Schubert cell `schubertCellι b hp hnk`. -/
theorem range_toSchemeHom_subset_closure_range_schubertCellι (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) {K : Type u} [Field K]
    [Algebra R K] (N : G(k, K ⊗[R] M; K))
    (hN : schemeSchubertLocus k b p ≤ (toSchemeHom N).ker) :
    Set.range (toSchemeHom N) ⊆ closure (Set.range (schubertCellι b hp hnk)) := by
  obtain ⟨p', hp', hpiv, hle⟩ :=
    (schemeSchubertLocus_le_ker_toSchemeHom_iff_exists_flagPivots b hp hnk N).mp hN
  exact range_toSchemeHom_subset_closure_aux b hp hnk _ N hp' hle hpiv rfl

/-- **The Zariski closure of the Schubert cell is the Schubert rank locus.** Over any commutative
ring `R`, when `r + k = n`, the closure of `Set.range (schubertCellι b hp hnk)` in `G(k, M)` equals
the underlying closed subset `(schemeSchubertLocus k b p).support`. -/
theorem closure_range_schubertCellι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    closure (Set.range (schubertCellι b hp hnk)) = (schemeSchubertLocus k b p).support := by
  refine Set.Subset.antisymm ?_ fun z hz ↦ ?_
  · rw [(schemeSchubertLocus k b p).support.isClosed.closure_subset_iff,
      ← schubertCellToLocus_subschemeι b hp hnk, ← range_subschemeι]
    rintro _ ⟨x, rfl⟩
    exact ⟨schubertCellToLocus b hp hnk x, rfl⟩
  · obtain ⟨z₀, rfl⟩ := (range_subschemeι (schemeSchubertLocus k b p)).symm ▸ hz
    let Z := (schemeSchubertLocus k b p).subscheme
    let K : Type u := IsLocalRing.ResidueField (Z.presheaf.stalk z₀)
    let g : Spec (.of K) ⟶ scheme R M k :=
      Z.fromSpecResidueField z₀ ≫ (schemeSchubertLocus k b p).subschemeι
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ toSpec R M k)
    let : Algebra R K := φ.hom.toAlgebra
    obtain ⟨N, hN⟩ := exists_toSchemeHom_eq (A := K) g hφ.symm
    have hker : schemeSchubertLocus k b p ≤ (toSchemeHom N).ker := by
      rw [hN, ← (schemeSchubertLocus k b p).ker_subschemeι]
      exact Scheme.Hom.le_ker_comp _ _
    have hpt : (schemeSchubertLocus k b p).subschemeι z₀ ∈ Set.range (toSchemeHom N) := by
      refine ⟨(default : Spec (Z.residueField z₀)), ?_⟩
      rw [hN]
      exact congrArg (schemeSchubertLocus k b p).subschemeι
        (Z.fromSpecResidueField_apply z₀ default)
    exact range_toSchemeHom_subset_closure_range_schubertCellι b hp hnk N hker hpt

/-- The support of the schematic image of `schubertCellι b hp hnk` equals the support of
`schemeSchubertLocus k b p`. -/
theorem support_ker_schubertCellι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    (schubertCellι b hp hnk).ker.support = (schemeSchubertLocus k b p).support := by
  ext1
  exact (Scheme.Hom.support_ker (schubertCellι b hp hnk)).trans
    (closure_range_schubertCellι b hp hnk)

/-- **Over any commutative ring `R`, the schematic image of the Schubert cell and the determinantal
Schubert locus have the same radical.** -/
theorem radical_ker_schubertCellι (b : Basis (Fin n) R M) {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n) :
    (schubertCellι b hp hnk).ker.radical = (schemeSchubertLocus k b p).radical := by
  rw [← vanishingIdeal_support, ← vanishingIdeal_support, support_ker_schubertCellι]

/-- **When `R` is reduced, the schematic image ideal sheaf of the Schubert cell equals the radical
of `schemeSchubertLocus k b p`.** -/
theorem ker_schubertCellι_eq_radical [_root_.IsReduced R] (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) :
    (schubertCellι b hp hnk).ker = (schemeSchubertLocus k b p).radical := by
  refine le_antisymm ?_ ?_
  · rw [← radical_ker_schubertCellι b hp hnk]
    exact le_radical _
  · rw [← vanishingIdeal_support]
    exact vanishingIdeal_le_ker_of_range_subset (schubertCellι b hp hnk)
      (subset_closure.trans_eq (closure_range_schubertCellι b hp hnk))

/-- Over an integral domain `R`, the support of `schemeSchubertLocus k b p` is irreducible. -/
theorem isIrreducible_support_schemeSchubertLocus [IsDomain R] (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) :
    IsIrreducible ((schemeSchubertLocus k b p).support : Set (scheme R M k)) := by
  rw [← closure_range_schubertCellι b hp hnk, ← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ _).image _
    (schubertCellι b hp hnk).continuous.continuousOn).closure

/-- Over an integral domain `R`, the reduced Schubert variety
`(schemeSchubertLocus k b p).radical.subscheme` is an integral scheme. -/
theorem isIntegral_subscheme_radical_schemeSchubertLocus [IsDomain R] (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) :
    IsIntegral (schemeSchubertLocus k b p).radical.subscheme := by
  rw [← vanishingIdeal_support]
  exact isIntegral_subscheme_vanishingIdeal (isIrreducible_support_schemeSchubertLocus b hp hnk)

end Closure

end Module.Grassmannian
