/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.IntervalChart
public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.PreAdicSpace
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.Analysis.SpecialFunctions.Pow.NNRat

/-!
# The Frobenius orbit space as an adic space

Let `R` be a perfect ring of characteristic `p` and give the Witt vectors `𝕎 R` the `(p, [ϖ])`-adic
topology; for `R = 𝒪_F` this is `A_inf`. The pre-adic spaces `𝒴 = D(p) ∩ D([ϖ])` and
`𝒳 = 𝒴 / φ^ℤ` of `TauCeti.FarguesFontaine.spaYPreAdicSpace` and
`TauCeti.FarguesFontaine.spaXPreAdicSpace` are adic spaces as soon as the structure presheaf
`𝒪_𝒴` is a sheaf, and `𝒳` is then the quotient of `𝒴` by Frobenius in the category `(Adic)` of
adic spaces. When `R` is the ring of integers of a valuation on a field, `𝒪_𝒴` is a sheaf
(`isSheaf_spaYPresheaf`), so `𝒴` and `𝒳` are adic spaces with no further hypothesis.

* `𝒴` is an open subspace of the pre-adic space `Spa(𝕎 R, 𝕎 R)`, so it is locally affinoid with
  no further hypothesis, and it is an adic space exactly when `𝒪_𝒴` is a sheaf.
* `𝒳` is covered by the charts `V → 𝒳` on the wandering opens `V ⊆ 𝒴`, such as the Frobenius
  windows. These charts are open immersions, so each open affinoid subspace of `𝒴` inside a
  wandering open is carried onto an open affinoid subspace of `𝒳`, and `𝒳` is locally affinoid.
  Its structure presheaf is a sheaf because `𝒪_𝒴` is (`isSheafy_spaXPreAdicSpace`): the sheaf
  property of `𝒳` descends from `𝒴`, not from the affinoid charts.

For a general perfect ring `R`, the sheaf condition on `𝒪_𝒴` is a hypothesis of the results on
`𝒳`, as it is for the pre-adic space `𝒳` itself. This file reduces it to windows: `𝒴` is a
pre-adic space, exhausted by the increasing windows `W_n = {v ∈ 𝒴 : p ^ (-n) ≤ κ(v) ≤ p ^ n}`,
and every open affinoid subspace of `𝒴` is quasi-compact, so lies in one of them. Hence `𝒪_𝒴` is
a sheaf as soon as its restriction to each `W_n` is (`isSheaf_spaYPresheaf_of_isSheafy_restrict`).
When `R` is the ring of integers of a valuation `v` on a field and `0 < v(ϖ) < 1`,
`TauCeti.FarguesFontaine.windowPreAdicSpaceIso` identifies `W_n` with `Spa(B^I, B^{I,+})` for the
interval ring `B^I` of `I = [v(ϖ) ^ (p ^ n), v(ϖ) ^ (p ^ (-n))]`. The ring `B^I` is strongly
noetherian (Kedlaya's Theorem 4.10), so the pair `(B^I, B^{I,+})` is sheafy, and `𝒪_𝒴` is a
sheaf (`isSheaf_spaYPresheaf`).

## Main definitions

* `TauCeti.FarguesFontaine.spaYAdicSpace` and `TauCeti.FarguesFontaine.spaXAdicSpace`: `𝒴` and
  `𝒳` as objects of `(Adic)`, when `𝒪_𝒴` is a sheaf.
* `TauCeti.FarguesFontaine.spaYAdicFrobenius` and `TauCeti.FarguesFontaine.quotientAdicHom`:
  Frobenius on `𝒴` and the projection `𝒴 → 𝒳` as morphisms of adic spaces.

## Main results

* `TauCeti.FarguesFontaine.isLocallyAffinoid_spaYPreAdicSpace`: `𝒴` is locally affinoid.
* `TauCeti.FarguesFontaine.isPreAdic_spaYPreAdicSpace`: `𝒴` is a pre-adic space.
* `TauCeti.FarguesFontaine.isSheaf_spaYPresheaf_of_isSheafy_restrict`: `𝒪_𝒴` is a sheaf if its
  restriction to every window `W_n` is.
* `TauCeti.FarguesFontaine.isSheaf_spaYPresheaf`: `𝒪_𝒴` is a sheaf when `R` is the ring of
  integers of a valuation on a field.
* `TauCeti.FarguesFontaine.isAdic_spaYPreAdicSpace_iff`: `𝒴` is an adic space exactly when `𝒪_𝒴`
  is a sheaf.
* `TauCeti.FarguesFontaine.isLocallyAffinoid_spaXPreAdicSpace`: `𝒳` is locally affinoid.
* `TauCeti.FarguesFontaine.isAdic_spaXPreAdicSpace`: `𝒳` is an adic space.
* `TauCeti.FarguesFontaine.isColimitQuotientAdicCofork`: `𝒳` is the coequalizer of the identity
  and Frobenius on `𝒴` in `(Adic)`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.22, Remark 8.27 and
  Theorem 8.28.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes, §3.1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Theorem 4.10.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector
open scoped NNReal

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]
  [IsTopologicalRing (WittVector p R)] {ϖ : R}
  (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-! ### `𝒴` as an adic space -/

/-- **`𝒴` is locally affinoid**, as an open subspace of the pre-adic space `Spa(𝕎 R, 𝕎 R)`. No
sheaf condition is needed. -/
theorem isLocallyAffinoid_spaYPreAdicSpace :
    PreAdicSpace.isLocallyAffinoid (spaYPreAdicSpace P hI) :=
  PreAdicSpace.isLocallyAffinoid_restrict _
    (isPreAdic_presentationLimitPreAdicSpace P _ _ le_top).isLocallyAffinoid

/-- **`𝒴` is a pre-adic space**, as the restriction of the pre-adic space `Spa(𝕎 R, 𝕎 R)` to an
open. -/
theorem isPreAdic_spaYPreAdicSpace : PreAdicSpace.isPreAdic (spaYPreAdicSpace P hI) :=
  PreAdicSpace.isPreAdic_restrict _ (isPreAdic_presentationLimitPreAdicSpace P _ _ le_top)

/-- **`𝒪_𝒴` is a sheaf if it is one on every window**: if the restriction of `𝒴` to each window
`W_n = {v ∈ 𝒴 : p ^ (-n) ≤ κ(v) ≤ p ^ n}` is sheafy, then `𝒪_𝒴` is a sheaf. The windows are a
directed family of opens exhausting the pre-adic space `𝒴`, so every open affinoid subspace of `𝒴`,
being quasi-compact, lies in one of them. -/
theorem isSheaf_spaYPresheaf_of_isSheafy_restrict
    (h : ∀ n, PreAdicSpace.isSheafy ((spaYPreAdicSpace P hI).restrict
      (spaYWindow ϖ hI n : Opens (spaYPreAdicSpace P hI)).isOpenEmbedding)) :
    (spaYPresheaf P ϖ).IsSheaf :=
  (isPreAdic_spaYPreAdicSpace P hI).isSheafy_of_directed (monotone_spaYWindow hI).directed_le
    (iSup_spaYWindow hI) h

/-- **`𝒴` is an adic space exactly when `𝒪_𝒴` is a sheaf**, since it is locally affinoid. -/
theorem isAdic_spaYPreAdicSpace_iff :
    PreAdicSpace.isAdic (spaYPreAdicSpace P hI) ↔ (spaYPresheaf P ϖ).IsSheaf :=
  ⟨fun h ↦ h.isSheafy,
    fun h ↦ PreAdicSpace.isAdic_iff.mpr ⟨h, isLocallyAffinoid_spaYPreAdicSpace P hI⟩⟩

-- The object is exposed, as `spaYPreAdicSpace` is: its underlying pre-adic space must be `𝒴` by
-- definition for the morphisms out of it to typecheck.
@[expose] public section SpaYAdicDef

/-- **`𝒴` as an adic space**, an object of `(Adic)`, when `𝒪_𝒴` is a sheaf. -/
def spaYAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) : AdicSpace.{v} :=
  ⟨spaYPreAdicSpace P hI, (isAdic_spaYPreAdicSpace_iff P hI).mpr h⟩

end SpaYAdicDef

variable {P hI} in
/-- The pre-adic space underlying the adic space `𝒴` is `spaYPreAdicSpace`. -/
@[simp]
theorem spaYAdicSpace_obj (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpace P hI h).obj = spaYPreAdicSpace P hI :=
  (rfl)

/-! ### Sheafiness of `𝒪_𝒴` -/

section IntervalRing

variable [CharP R p] [PerfectRing R p] {K : Type*} [Field K] [Algebra R K] {v : Valuation K ℝ≥0}
  {P}

include hI in
/-- **`𝒪_𝒴` is a sheaf**: let `R` be the ring of integers of a valuation `v` on a field `K`,
perfect of characteristic `p`, and `ϖ ∈ R` with `0 < v(ϖ) < 1`; for `R = 𝒪_F` this is the
Fargues–Fontaine space `𝒴 ⊆ Spa(A_inf, A_inf)`. Then the structure presheaf `𝒪_𝒴` is a sheaf, so
`𝒴` and `𝒳 = 𝒴 / φ^ℤ` are adic spaces (`isAdic_spaYPreAdicSpace_iff`, `isAdic_spaXPreAdicSpace`).
The window `W_n = {p ^ (-n) ≤ κ ≤ p ^ n}` is `Spa(B^I, B^{I,+})` for
`I = [v(ϖ) ^ (p ^ n), v(ϖ) ^ (p ^ (-n))]` (`TauCeti.FarguesFontaine.windowPreAdicSpaceIso`), and
this pair is sheafy because `B^I` is strongly noetherian (Kedlaya's Theorem 4.10), so `𝒪_𝒴` is
sheafy on each window (`isSheafy_spaYPreAdicSpace_restrict`), and hence a sheaf
(`isSheaf_spaYPresheaf_of_isSheafy_restrict`). -/
theorem isSheaf_spaYPresheaf (hv : v.Integers R) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap R K ϖ) < 1) :
    (spaYPresheaf P ϖ).IsSheaf := by
  have hϖ₀ : 0 < v (algebraMap R K ϖ) :=
    pos_iff_ne_zero.mpr ((map_ne_zero v).mpr ((map_ne_zero_iff _ hv.hom_inj).mpr hϖ))
  -- the radius of `κ = q` is `v(ϖ) ^ (1 / q)`, which lies in `(0, 1)` for `q ≠ 0`
  have hρ {q : ℚ≥0} (hq : q ≠ 0) : v (algebraMap R K ϖ) ^ ((q : ℝ)⁻¹) ∈ Set.Ioo 0 1 :=
    ⟨NNReal.rpow_pos hϖ₀,
      NNReal.rpow_lt_one hϖ' (inv_pos.mpr (NNRat.cast_pos.mpr (pos_iff_ne_zero.mpr hq)))⟩
  have hp : (p : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine isSheaf_spaYPresheaf_of_isSheafy_restrict P hI fun n ↦ ?_
  have hq : (p : ℚ≥0) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ hp
  have hq' : (p : ℚ≥0) ^ (n : ℤ) ≠ 0 := zpow_ne_zero _ hp
  have h₁₂ : v (algebraMap R K ϖ) ^ (((p : ℚ≥0) ^ (-(n : ℤ)) : ℚ≥0) : ℝ)⁻¹ ≤
      v (algebraMap R K ϖ) ^ (((p : ℚ≥0) ^ (n : ℤ) : ℚ≥0) : ℝ)⁻¹ := by
    refine NNReal.rpow_le_rpow_of_exponent_ge hϖ₀ hϖ'.le (inv_anti₀ ?_ ?_)
    · exact NNRat.cast_pos.mpr (pos_iff_ne_zero.mpr hq)
    · have h1 : (1 : ℚ≥0) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
      exact_mod_cast (zpow_le_zpow_right₀ h1 (by omega : -(n : ℤ) ≤ n))
  exact isSheafy_spaYPreAdicSpace_restrict hv hϖ hϖ' (hρ hq) (hρ hq') _
    (NNReal.rpow_inv_nnratCast_pow_num _ hq) (NNReal.rpow_inv_nnratCast_pow_num _ hq') h₁₂
    fun x ↦ (mem_spaYWindow_iff hI).mp x.2

end IntervalRing

/-! ### `𝒳` as an adic space -/

variable [CharP R p] [PerfectRing R p] {P hI}

/-- **`𝒳` is locally affinoid** when `𝒪_𝒴` is a sheaf: every point of `𝒳` lies in the image of an
open affinoid subspace of `𝒴` contained in a wandering open, and that image is an open affinoid
subspace of `𝒳`, since the chart on a wandering open is an open immersion. -/
theorem isLocallyAffinoid_spaXPreAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    PreAdicSpace.isLocallyAffinoid (spaXPreAdicSpace P hI h) := by
  intro x
  obtain ⟨y, rfl⟩ := (isOpenQuotientMap_quotientMap hI).surjective x
  obtain ⟨V, hV, hy⟩ := exists_wandering_open_mem hI y
  let f := (spaYPreAdicSpace P hI).ofRestrict V.isOpenEmbedding ≫ quotientPreAdicHom P hI h
  -- on points the projection is `quotientMap`: the base of `quotientPresheafedHom` is the
  -- abbreviation `quotientTopHom`, the bundled `quotientMap`
  have hq : (quotientPreAdicHom P hI h).toHom.base y = quotientMap hI y := by
    rw [quotientPreAdicHom_toHom]
    rfl
  have : PreAdicSpace.IsOpenImmersion f := isOpenImmersion_ofRestrict_comp_quotientPreAdicHom h hV
  -- an open affinoid neighbourhood of `y` in `V`, read in the restriction of `𝒳` along the chart
  obtain ⟨W, hW, hyW⟩ := ObjectProperty.prop_of_iso PreAdicSpace.isLocallyAffinoid
    (PreAdicSpace.IsOpenImmersion.isoRestrict f)
    (PreAdicSpace.isLocallyAffinoid_restrict V.isOpenEmbedding
      (isLocallyAffinoid_spaYPreAdicSpace P hI)) ⟨y, hy⟩
  exact ⟨_, (PreAdicSpace.mem_affinoidOpens_restrict_iff _ f.isOpenEmbedding W).mp hW,
    ⟨y, hy⟩, hyW, hq⟩

/-- **`𝒳 = 𝒴 / φ^ℤ` is an adic space** when `𝒪_𝒴` is a sheaf: it is sheafy
(`isSheafy_spaXPreAdicSpace`) and locally affinoid (`isLocallyAffinoid_spaXPreAdicSpace`). -/
theorem isAdic_spaXPreAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    PreAdicSpace.isAdic (spaXPreAdicSpace P hI h) :=
  PreAdicSpace.isAdic_iff.mpr ⟨isSheafy_spaXPreAdicSpace h, isLocallyAffinoid_spaXPreAdicSpace h⟩

/-! ### The quotient in `(Adic)` -/

-- The object is exposed, as `spaXPreAdicSpace` is: its underlying pre-adic space must be `𝒳` by
-- definition for the morphisms into it to typecheck.
@[expose] public section SpaXAdicDef

variable (P hI) in
/-- **`𝒳 = 𝒴 / φ^ℤ` as an adic space**, an object of `(Adic)`, when `𝒪_𝒴` is a sheaf. -/
def spaXAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) : AdicSpace.{v} :=
  ⟨spaXPreAdicSpace P hI h, isAdic_spaXPreAdicSpace h⟩

end SpaXAdicDef

/-- The pre-adic space underlying the adic space `𝒳` is `spaXPreAdicSpace`. -/
@[simp]
theorem spaXAdicSpace_obj (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXAdicSpace P hI h).obj = spaXPreAdicSpace P hI h :=
  (rfl)

variable (P hI) in
/-- **Witt Frobenius as an endomorphism of the adic space `𝒴`**: the morphism of pre-adic spaces
`spaYFrobenius`, read in the full subcategory `(Adic)`. -/
def spaYAdicFrobenius (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYAdicSpace P hI h ⟶ spaYAdicSpace P hI h :=
  ObjectProperty.homMk (spaYFrobenius P hI)

variable (P hI) in
/-- **The projection `𝒴 → 𝒳` as a morphism of adic spaces**: the morphism of pre-adic spaces
`quotientPreAdicHom`, read in the full subcategory `(Adic)`. -/
def quotientAdicHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYAdicSpace P hI h ⟶ spaXAdicSpace P hI h :=
  ObjectProperty.homMk (quotientPreAdicHom P hI h)

/-- The morphism of pre-adic spaces underlying Frobenius on the adic space `𝒴` is
`spaYFrobenius`. -/
@[simp]
theorem spaYAdicFrobenius_hom (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicFrobenius P hI h).hom = spaYFrobenius P hI :=
  (rfl)

/-- The morphism of pre-adic spaces underlying the projection of adic spaces is
`quotientPreAdicHom`. -/
@[simp]
theorem quotientAdicHom_hom (h : (spaYPresheaf P ϖ).IsSheaf) :
    (quotientAdicHom P hI h).hom = quotientPreAdicHom P hI h :=
  (rfl)

/-- **The projection to `𝒳` is Frobenius-invariant** as a morphism of adic spaces. -/
@[reassoc (attr := simp)]
theorem spaYAdicFrobenius_comp_quotientAdicHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYAdicFrobenius P hI h ≫ quotientAdicHom P hI h = quotientAdicHom P hI h :=
  ObjectProperty.hom_ext _ (spaYFrobenius_comp_quotientPreAdicHom h)

variable (P hI) in
/-- **`𝒳 = 𝒴 / φ^ℤ` is the quotient of `𝒴` by Frobenius in `(Adic)`**: when `𝒪_𝒴` is a sheaf, the
adic space `𝒳` is the coequalizer of the identity and Frobenius on the adic space `𝒴`, with the
projection `q` as coprojection. The inclusion of `(Adic)` into `𝒱^pre` is fully faithful, so this
is the universal property of `𝒳` in `𝒱^pre` (`isColimitQuotientPreAdicCofork`) restricted to
adic spaces. -/
def isColimitQuotientAdicCofork (h : (spaYPresheaf P ϖ).IsSheaf) :
    IsColimit (Cofork.ofπ (f := 𝟙 _) (g := spaYAdicFrobenius P hI h) (quotientAdicHom P hI h)
      ((Category.id_comp _).trans (spaYAdicFrobenius_comp_quotientAdicHom h).symm)) :=
  Cofork.IsColimit.mk _
    (fun s ↦ ObjectProperty.homMk (quotientPreAdicDesc s.π.hom h (by
      have hs := congrArg InducedCategory.Hom.hom s.condition
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.id_hom, Category.id_comp, spaYAdicFrobenius_hom] at hs
      exact hs.symm)))
    (fun s ↦ ObjectProperty.hom_ext _ (quotientPreAdicHom_comp_quotientPreAdicDesc h _))
    (fun s m hm ↦ ObjectProperty.hom_ext _ (quotientPreAdicHom_hom_ext
      ((congrArg InducedCategory.Hom.hom hm).trans
        (quotientPreAdicHom_comp_quotientPreAdicDesc h _).symm)))

end TauCeti.FarguesFontaine
