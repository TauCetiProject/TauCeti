/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Rep.TensorShortExact
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The cup product and the connecting maps of a short exact sequence

The Tate cup product is defined in the second variable by the rule `x ∪ δ y = (-1)^p δ (x ∪ y)`
for the connecting maps `δ` of the upward dimension-shifting sequence when `y` has degree `q ≥ 0`,
and of the downward one when `q < 0` (`TauCeti.TateCohomology.cup_dimensionShiftUpIso_hom`,
`TauCeti.TateCohomology.cup_dimensionShiftDownIso_hom`). This file extends the rule, in every
degree `q`, to the connecting maps of every short exact sequence `0 → N₁ → N₂ → N₃ → 0` whose first
map has a `k`-linear retraction (`TauCeti.TateCohomology.cup_δ_of_leftInverse`). This applies in
particular to the tensor products of the dimension-shifting sequences with a representation, which
are split `k`-linearly but in general not as sequences of representations.

When the first factor `M` is flat over `k`, the rule holds for every short exact sequence in the
second variable (`TauCeti.TateCohomology.cup_δ_of_flat`). This covers sequences which do not split
over `k`, such as `0 → ℤ → ℚ → ℚ/ℤ → 0` against classes of the trivial representation `ℤ`, whose
connecting map produces the class `δχ ∈ H²(G, ℤ)` of a character `χ` in the Artin–Tate character
formula.

In the first variable, the rule `δ (x ∪ y) = δ x ∪ y` holds for every short exact sequence whose
first map has a `k`-linear retraction (`TauCeti.TateCohomology.δ_cup_of_leftInverse`), where the
connecting map on the left is that of the tensor product of the sequence on the right with the
second factor. It is proved by the same dimension shifting in the second variable, using that the
connecting maps of the `3 × 3` diagram of tensor products of two `k`-split short exact sequences
anticommute (`TauCeti.TateCohomology.δ_comp_δ_eq_neg`).

## Main statements

* `TauCeti.TateCohomology.cup_δ_of_leftInverse`: for a short exact sequence whose first map has a
  `k`-linear retraction, `x ∪ δ y = (-1)^p δ (x ∪ y)` for `x` of degree `p` and `y` of any degree
  `q`.
* `TauCeti.TateCohomology.cup_δ_of_flat`: if the underlying module of `M` is flat over `k`, then
  `x ∪ δ y = (-1)^p δ (x ∪ y)` for every short exact sequence, `x` of degree `p` and `y` of any
  degree `q`.
* `TauCeti.TateCohomology.δ_cup_of_leftInverse`: the rule in the first variable: for a short exact
  sequence whose first map has a `k`-linear retraction, `δ (x ∪ y) = δ x ∪ y` for `x` and `y` of
  any degrees.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

/- Proof of `cup_δ_of_leftInverse` for `0 → N₁ → N₂ → N₃ → 0` and `y` of degree `q`. For `q ≥ 0`,
a retraction `r` of the first map gives a morphism from the sequence to the upward
dimension-shifting sequence of `N₁` which is the identity on `N₁`: on `N₂` it is
`n ↦ (g ↦ r (g • n))`. For `q < 0`, the corresponding `k`-linear section `s` of the last map gives
a morphism to the sequence from the downward dimension-shifting sequence of `N₃` which is the
identity on `N₃`: on `Ind_⊥^G N₃` it is `⟦g ⊗ₜ n⟧ ↦ g⁻¹ • s n`. In either case the connecting maps
of the two sequences, and of their tensor products with the first factor, are related by
naturality of the connecting maps, and the cup product is natural in the second variable. -/

/-- The morphism from a short exact sequence whose first map has a `k`-linear retraction `r` to the
upward dimension-shifting sequence of its first term: the identity on the first term, and
`n ↦ (g ↦ r (g • n))` on the middle term. -/
private def toDimensionShiftUpSES {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) :
    S ⟶ ShortComplex.mk (coindBotUnit S.X₁) (dimensionShiftUpπ S.X₁)
      (coindBotUnit_comp_dimensionShiftUpπ S.X₁) :=
  have := hS.epi_g
  { τ₁ := 𝟙 S.X₁
    τ₂ := toCoindBot S.X₂ r
    τ₃ := hS.exact.desc (toCoindBot S.X₂ r ≫ dimensionShiftUpπ S.X₁)
      (by rw [comp_toCoindBot_of_leftInverse_assoc S.f hr,
        coindBotUnit_comp_dimensionShiftUpπ])
    comm₁₂ := by
      rw [Category.id_comp]
      exact (comp_toCoindBot_of_leftInverse S.f hr).symm
    comm₂₃ := (hS.exact.g_desc _ _).symm }

/-- The morphism to a short exact sequence whose last map has a `k`-linear section `s` from the
downward dimension-shifting sequence of its last term: the identity on the last term, and
`⟦g ⊗ₜ a⟧ ↦ g⁻¹ • s a` on the middle term. -/
private def fromDimensionShiftDownSES {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {s : S.X₃.V →ₗ[k] S.X₂.V} (hs : Function.RightInverse s S.g.hom) :
    ShortComplex.mk (dimensionShiftDownι S.X₃) (indBotCounit S.X₃)
      (dimensionShiftDownι_comp_indBotCounit S.X₃) ⟶ S :=
  have := hS.mono_f
  { τ₁ := hS.exact.lift (dimensionShiftDownι S.X₃ ≫ fromIndBot S.X₂ s)
      (by rw [Category.assoc, fromIndBot_comp_of_rightInverse S.g hs,
        dimensionShiftDownι_comp_indBotCounit])
    τ₂ := fromIndBot S.X₂ s
    τ₃ := 𝟙 S.X₃
    comm₁₂ := hS.exact.lift_f _ _
    comm₂₃ := by
      rw [Category.comp_id]
      exact fromIndBot_comp_of_rightInverse S.g hs }

variable [Fintype G]

/-- The rule `x ∪ δ y = (-1)^p δ (x ∪ y)` for a short exact sequence whose first map has a
`k`-linear retraction, when `y` has degree `q ≥ 0`. -/
private theorem cup_δ_of_leftInverse_of_nonneg (M : Rep k G) {S : ShortComplex (Rep k G)}
    (hS : S.ShortExact) {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom)
    (hMS : (S.map (tensorLeft M)).ShortExact) {p q n : ℤ} (hq : 0 ≤ q) (h : p + q = n)
    (x : tateCohomology M p) (y : tateCohomology S.X₃ q) :
    cup M S.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hS q y) =
      p.negOnePow • _root_.TateCohomology.δ hMS n (cup M S.X₃ p q n h x y) := by
  have hD : (ShortComplex.mk (coindBotUnit S.X₁) (dimensionShiftUpπ S.X₁)
      (coindBotUnit_comp_dimensionShiftUpπ S.X₁)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact S.X₁
  let Φ := toDimensionShiftUpSES hS hr
  -- The connecting maps of `S` and of the dimension-shifting sequence, and of their tensor
  -- products with `M`, are related through `Φ`, which is the identity on the first terms.
  let Ψ : S.map (tensorLeft M) ⟶ (ShortComplex.mk (coindBotUnit S.X₁) (dimensionShiftUpπ S.X₁)
      (coindBotUnit_comp_dimensionShiftUpπ S.X₁)).map (tensorLeft M) :=
    (tensorLeft M).mapShortComplex.map Φ
  -- `Φ.τ₁` is the identity by construction.
  have e₁ : (tateCohomologyFunctor (q + 1)).map Φ.τ₁ = 𝟙 _ :=
    (tateCohomologyFunctor (q + 1)).map_id _
  have e₂ : (tateCohomologyFunctor (n + 1)).map Ψ.τ₁ = 𝟙 _ :=
    (congrArg (tateCohomologyFunctor (n + 1)).map ((tensorLeft M).map_id S.X₁)).trans
      ((tateCohomologyFunctor (n + 1)).map_id _)
  have h₁ := _root_.TateCohomology.δ_naturality hS hD Φ q
  have h₂ := _root_.TateCohomology.δ_naturality hMS
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact S.X₁ M)
    Ψ n
  rw [e₁, Category.comp_id] at h₁
  rw [e₂, Category.comp_id] at h₂
  rw [h₁, h₂, ModuleCat.comp_apply, ModuleCat.comp_apply, ← dimensionShiftUpIso_hom,
    cup_dimensionShiftUpIso_hom M S.X₁ hq h rfl, cup_map_right, tensorDimensionShiftUpIso_hom]
  -- `Ψ.τ₃` is `M ◁ Φ.τ₃` by definition of `tensorLeft`.
  rfl

/-- The rule `x ∪ δ y = (-1)^p δ (x ∪ y)` for a short exact sequence whose last map has a
`k`-linear section, when `y` has degree `q < 0`. -/
private theorem cup_δ_of_rightInverse_of_neg (M : Rep k G) {S : ShortComplex (Rep k G)}
    (hS : S.ShortExact) {s : S.X₃.V →ₗ[k] S.X₂.V} (hs : Function.RightInverse s S.g.hom)
    (hMS : (S.map (tensorLeft M)).ShortExact) {p q n : ℤ} (hq : q < 0) (h : p + q = n)
    (x : tateCohomology M p) (y : tateCohomology S.X₃ q) :
    cup M S.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hS q y) =
      p.negOnePow • _root_.TateCohomology.δ hMS n (cup M S.X₃ p q n h x y) := by
  have hD : (ShortComplex.mk (dimensionShiftDownι S.X₃) (indBotCounit S.X₃)
      (dimensionShiftDownι_comp_indBotCounit S.X₃)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact S.X₃
  let Φ := fromDimensionShiftDownSES hS hs
  -- The connecting maps of the dimension-shifting sequence and of `S`, and of their tensor
  -- products with `M`, are related through `Φ`, which is the identity on the last terms.
  let Ψ : (ShortComplex.mk (dimensionShiftDownι S.X₃) (indBotCounit S.X₃)
      (dimensionShiftDownι_comp_indBotCounit S.X₃)).map (tensorLeft M) ⟶ S.map (tensorLeft M) :=
    (tensorLeft M).mapShortComplex.map Φ
  -- `Φ.τ₃` is the identity by construction.
  have e₁ : (tateCohomologyFunctor q).map Φ.τ₃ = 𝟙 _ :=
    (tateCohomologyFunctor q).map_id _
  have e₂ : (tateCohomologyFunctor n).map Ψ.τ₃ = 𝟙 _ :=
    (congrArg (tateCohomologyFunctor n).map ((tensorLeft M).map_id S.X₃)).trans
      ((tateCohomologyFunctor n).map_id _)
  have h₁ := _root_.TateCohomology.δ_naturality hD hS Φ q
  have h₂ := _root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_tensorLeft_shortExact S.X₃ M) hMS Ψ n
  rw [e₁, Category.id_comp] at h₁
  rw [e₂, Category.id_comp] at h₂
  rw [← h₁, ← h₂, ModuleCat.comp_apply, ModuleCat.comp_apply, ← dimensionShiftDownIso_hom,
    cup_map_right, cup_dimensionShiftDownIso_hom M S.X₃ hq h rfl, map_zsmul_unit,
    tensorDimensionShiftDownIso_hom]
  -- `Ψ.τ₁` is `M ◁ Φ.τ₁` by definition of `tensorLeft`.
  rfl

/-- **The cup product rule for a split short exact sequence in the second variable.** For a short
exact sequence `S` whose first map has a `k`-linear retraction, `x` of degree `p` and `y` of any
degree `q`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the second `δ` is the connecting map of the tensor
product of `S` with `M`, which is short exact by `Rep.shortExact_map_tensorLeft_of_leftInverse`. -/
theorem cup_δ_of_leftInverse (M : Rep k G) {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) {p q n : ℤ}
    (h : p + q = n) (x : tateCohomology M p) (y : tateCohomology S.X₃ q) :
    cup M S.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hS q y) =
      p.negOnePow • _root_.TateCohomology.δ
        (haveI := hS.epi_g; shortExact_map_tensorLeft_of_leftInverse hS.exact M hr) n
        (cup M S.X₃ p q n h x y) := by
  rcases le_or_gt 0 q with hq | hq
  · exact cup_δ_of_leftInverse_of_nonneg M hS hr _ hq h x y
  · have := hS.epi_g
    obtain ⟨s, hs⟩ := Rep.exists_rightInverse_of_leftInverse hS.exact hr
    exact cup_δ_of_rightInverse_of_neg M hS hs _ hq h x y

/- Proof of `cup_δ_of_flat` for `S : 0 → N₁ → N₂ → N₃ → 0`. The sequence
`T : 0 → K → Ind_⊥^G N₂ → N₃ → 0`, whose last map is the projection onto `N₂` followed by
`N₂ → N₃`, maps to `S` through the projection `Ind_⊥^G N₂ → N₂`, and to the downward
dimension-shifting sequence `D` of `N₃` through `Ind_⊥^G N₂ → Ind_⊥^G N₃`, in both cases by the
identity on `N₃`. The defect `x ∪ δ y - (-1)^p δ (x ∪ y)` is natural along such morphisms. It
vanishes for `D`, which splits `k`-linearly. The tensored sequences `M ⊗ T` and `M ⊗ D` are short
exact because `M` is flat, and their middle terms have no Tate cohomology, so their connecting maps
are isomorphisms; hence `M ⊗ K → M ⊗ dimensionShiftDown N₃` is an isomorphism on Tate cohomology,
and the defect vanishes for `T`, hence for `S`. -/

/-- The left side `x ∪ δ y` of the cup product rule is natural along a morphism of short exact
sequences. -/
private theorem cup_δ_naturality (M : Rep k G) {S S' : ShortComplex (Rep k G)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (Φ : S' ⟶ S) {p q r : ℤ} (h : p + (q + 1) = r)
    (x : tateCohomology M p) (y : tateCohomology S'.X₃ q) :
    cup M S.X₁ p (q + 1) r h x
        (_root_.TateCohomology.δ hS q ((tateCohomologyFunctor q).map Φ.τ₃ y)) =
      (tateCohomologyFunctor r).map (M ◁ Φ.τ₁)
        (cup M S'.X₁ p (q + 1) r h x (_root_.TateCohomology.δ hS' q y)) := by
  rw [← ModuleCat.comp_apply, ← _root_.TateCohomology.δ_naturality hS' hS Φ q,
    ModuleCat.comp_apply, cup_map_right]

/-- The right side `δ (x ∪ y)` of the cup product rule is natural along a morphism of short exact
sequences. -/
private theorem δ_cup_naturality (M : Rep k G) {S S' : ShortComplex (Rep k G)}
    (hMS : (S.map (tensorLeft M)).ShortExact) (hMS' : (S'.map (tensorLeft M)).ShortExact)
    (Φ : S' ⟶ S) {p q n : ℤ} (h : p + q = n) (x : tateCohomology M p)
    (y : tateCohomology S'.X₃ q) :
    _root_.TateCohomology.δ hMS n (cup M S.X₃ p q n h x ((tateCohomologyFunctor q).map Φ.τ₃ y)) =
      (tateCohomologyFunctor (n + 1)).map (M ◁ Φ.τ₁)
        (_root_.TateCohomology.δ hMS' n (cup M S'.X₃ p q n h x y)) := by
  rw [cup_map_right]
  exact congrArg (fun φ ↦ φ (cup M S'.X₃ p q n h x y)) (_root_.TateCohomology.δ_naturality hMS'
    hMS ((tensorLeft M).mapShortComplex.map Φ) n).symm

/-- **The cup product rule for a flat first factor.** If the underlying module of `M` is flat
over `k`, then for every short exact sequence `S`, `x` of degree `p` and `y` of any degree `q`,
`x ∪ δ y = (-1)^p δ (x ∪ y)`, where the second `δ` is the connecting map of the tensor product of
`S` with `M`, which is short exact by `Rep.shortExact_map_tensorLeft_of_flat`. Unlike
`TauCeti.TateCohomology.cup_δ_of_leftInverse`, the sequence need not split `k`-linearly: for
`k = ℤ` and `M` the trivial representation `ℤ`, this applies to `0 → ℤ → ℚ → ℚ/ℤ → 0`. -/
theorem cup_δ_of_flat (M : Rep k G) [Module.Flat k M.V] {S : ShortComplex (Rep k G)}
    (hS : S.ShortExact) {p q n : ℤ} (h : p + q = n) (x : tateCohomology M p)
    (y : tateCohomology S.X₃ q) :
    cup M S.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hS q y) =
      p.negOnePow • _root_.TateCohomology.δ (shortExact_map_tensorLeft_of_flat hS M) n
        (cup M S.X₃ p q n h x y) := by
  have := hS.epi_g
  have := hS.mono_f
  -- The sequence `T : 0 → K → Ind_⊥^G N₂ → N₃ → 0` and the dimension-shifting sequence `D` of `N₃`.
  let T := ShortComplex.kernelSequence (indBotCounit S.X₂ ≫ S.g)
  have hT : T.ShortExact := TauCeti.kernelSequence_shortExact _
  let D := ShortComplex.mk (dimensionShiftDownι S.X₃) (indBotCounit S.X₃)
    (dimensionShiftDownι_comp_indBotCounit S.X₃)
  have hD : D.ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact S.X₃
  have := hD.mono_f
  obtain ⟨r, hr⟩ := exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit S.X₃)
  -- The morphisms `φ : T ⟶ S` and `ψ : T ⟶ D`, both the identity on `N₃`.
  let φ : T ⟶ S := ShortComplex.homMk
    (hS.exact.lift (T.f ≫ indBotCounit S.X₂) ((Category.assoc _ _ _).trans T.zero))
    (indBotCounit S.X₂) (𝟙 S.X₃) (hS.exact.lift_f _ _) (Category.comp_id _).symm
  let ψ : T ⟶ D := ShortComplex.homMk
    (hD.exact.lift (T.f ≫ indBotMap S.g) ((Category.assoc _ _ _).trans
      ((congrArg (T.f ≫ ·) (indBotCounit_naturality S.g)).trans T.zero)))
    (indBotMap S.g) (𝟙 S.X₃) (hD.exact.lift_f _ _)
    ((indBotCounit_naturality S.g).trans (Category.comp_id _).symm)
  have hMT := shortExact_map_tensorLeft_of_flat hT M
  have hMD : (D.map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_tensorLeft_shortExact S.X₃ M
  -- The connecting maps of `M ⊗ T` and `M ⊗ D` are isomorphisms, so `M ◁ ψ.τ₁` induces an
  -- injection on Tate cohomology.
  have hinj : Function.Injective ((tateCohomologyFunctor (n + 1)).map (M ◁ ψ.τ₁)) := by
    have hδT : IsIso (_root_.TateCohomology.δ hMT n) :=
      ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hMT).δIso n (n + 1) rfl
        (isZero_tensor_indBot S.X₂.V M n) (isZero_tensor_indBot S.X₂.V M (n + 1))).isIso_hom
    have hδD : IsIso (_root_.TateCohomology.δ hMD n) :=
      ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hMD).δIso n (n + 1) rfl
        (isZero_tensor_indBot S.X₃.V M n) (isZero_tensor_indBot S.X₃.V M (n + 1))).isIso_hom
    -- `ψ.τ₃` is the identity, so naturality of the connecting maps along `M ◁ ψ` reads
    -- `δ_{M ⊗ T} ≫ (M ◁ ψ.τ₁)_* = δ_{M ⊗ D}`.
    have e₃ : (tateCohomologyFunctor n).map ((tensorLeft M).mapShortComplex.map ψ).τ₃ = 𝟙 _ :=
      (congrArg (tateCohomologyFunctor n).map ((tensorLeft M).map_id S.X₃)).trans
        ((tateCohomologyFunctor n).map_id _)
    have e := _root_.TateCohomology.δ_naturality hMT hMD ((tensorLeft M).mapShortComplex.map ψ) n
    rw [e₃] at e
    have e' : _root_.TateCohomology.δ hMT n ≫ (tateCohomologyFunctor (n + 1)).map (M ◁ ψ.τ₁) =
        _root_.TateCohomology.δ hMD n :=
      e.trans (Category.id_comp _)
    have : IsIso (_root_.TateCohomology.δ hMT n ≫
        (tateCohomologyFunctor (n + 1)).map (M ◁ ψ.τ₁)) := by
      rw [e']
      exact hδD
    have := IsIso.of_isIso_comp_left (_root_.TateCohomology.δ hMT n)
      ((tateCohomologyFunctor (n + 1)).map (M ◁ ψ.τ₁))
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  -- The rule for `T`, from the rule for `D` through `ψ`.
  have hT' : cup M T.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hT q y) =
      p.negOnePow • _root_.TateCohomology.δ hMT n (cup M T.X₃ p q n h x y) := by
    apply hinj
    have e₁ := cup_δ_naturality M hD hT ψ (r := n + 1) (by omega) x y
    have e₂ := δ_cup_naturality M hMD hMT ψ h x y
    rw [Units.smul_def, map_zsmul, ← e₁, ← e₂, ← Units.smul_def]
    exact cup_δ_of_leftInverse M hD hr h x ((tateCohomologyFunctor q).map ψ.τ₃ y)
  -- The rule for `S`, from the rule for `T` through `φ`.
  have e₁ := cup_δ_naturality M hS hT φ (r := n + 1) (by omega) x y
  have e₂ := δ_cup_naturality M (shortExact_map_tensorLeft_of_flat hS M) hMT φ h x y
  -- `φ.τ₃` is the identity of `N₃`.
  have e₃ : (tateCohomologyFunctor q).map φ.τ₃ = 𝟙 _ := (tateCohomologyFunctor q).map_id S.X₃
  rw [hT', Units.smul_def, map_zsmul, ← e₂, ← Units.smul_def, e₃] at e₁
  -- `e₁` now applies the identity of the degree-`q` Tate cohomology of `N₃` to `y` on both sides,
  -- which is `y` by definition; it is not rewritten away because the identity is stated on `T.X₃`,
  -- which is `N₃` only up to unfolding `T`.
  exact e₁

/-! ### The cup product rule in the first variable -/

/- Proof of `δ_cup_of_leftInverse` for `S : 0 → M₁ → M₂ → M₃ → 0` and `y` of degree `q`. For
`q = 0` it is `δ_cupH0`. The general case follows by induction on `q`, upwards through the dimension
shift `0 → N → Coind_⊥^G N → dimensionShiftUp N → 0` and downwards through
`0 → dimensionShiftDown N → Ind_⊥^G N → N → 0`, for which `x ∪ δ y = (-1)^p δ (x ∪ y)` holds by
definition of the cup product. Both steps compare the connecting maps of the `3 × 3` diagram of
tensor products of the terms of `S` and of the dimension-shifting sequence, whose rows and columns
are short exact because both sequences split `k`-linearly. Its two composites of connecting maps
differ by a sign (`TauCeti.TateCohomology.δ_comp_δ_eq_neg`), which accounts for the change of the
sign `(-1)^p` of the rule for `x` to the sign `(-1)^(p + 1)` of the rule for `δ x`. -/

/-- The `3 × 3` diagram of tensor products of the terms of `S` and of `T`: its rows are the tensor
products of `T` on the left with the terms of `S`, and its columns are the tensor products of `S`
on the right with the terms of `T`. -/
private def tensorDiagram (S T : ShortComplex (Rep k G)) :
    ShortComplex (ShortComplex (Rep k G)) :=
  ShortComplex.mk (T.mapNatTrans ((tensoringLeft (Rep k G)).map S.f))
    (T.mapNatTrans ((tensoringLeft (Rep k G)).map S.g)) (by
      ext <;> simp [← comp_whiskerRight])

/-- The connecting maps of the tensor products of two short exact sequences `S` and `T` that split
`k`-linearly anticommute: the two composites `Ĥⁿ(G, S₃ ⊗ T₃) ⟶ Ĥⁿ⁺²(G, S₁ ⊗ T₁)` differ by a
sign. -/
private theorem δ_comp_δ_tensor {S T : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) (hT : T.ShortExact)
    {r' : T.X₂.V →ₗ[k] T.X₁.V} (hr' : Function.LeftInverse r' T.f.hom) (n : ℤ)
    (c : tateCohomology (S.X₃ ⊗ T.X₃) n) :
    _root_.TateCohomology.δ (haveI := hS.epi_g;
      Rep.shortExact_map_tensorRight_of_leftInverse hS.exact T.X₁ hr) (n + 1)
        (_root_.TateCohomology.δ (haveI := hT.epi_g;
          Rep.shortExact_map_tensorLeft_of_leftInverse hT.exact S.X₃ hr') n c) =
      -_root_.TateCohomology.δ (haveI := hT.epi_g;
        Rep.shortExact_map_tensorLeft_of_leftInverse hT.exact S.X₁ hr') (n + 1)
          (_root_.TateCohomology.δ (haveI := hS.epi_g;
            Rep.shortExact_map_tensorRight_of_leftInverse hS.exact T.X₃ hr) n c) := by
  have := hS.epi_g
  have := hT.epi_g
  have key := δ_comp_δ_eq_neg (tensorDiagram S T)
    (Rep.shortExact_map_tensorLeft_of_leftInverse hT.exact S.X₁ hr')
    (Rep.shortExact_map_tensorLeft_of_leftInverse hT.exact S.X₂ hr')
    (Rep.shortExact_map_tensorLeft_of_leftInverse hT.exact S.X₃ hr')
    (Rep.shortExact_map_tensorRight_of_leftInverse hS.exact T.X₁ hr)
    (Rep.shortExact_map_tensorRight_of_leftInverse hS.exact T.X₂ hr)
    (Rep.shortExact_map_tensorRight_of_leftInverse hS.exact T.X₃ hr) n
  exact ConcreteCategory.congr_hom key c

variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact) {r : S.X₂.V →ₗ[k] S.X₁.V}
  (hr : Function.LeftInverse r S.f.hom)
include hS hr

/-- The rule `δ (x ∪ y) = δ x ∪ y` for a short exact sequence whose first map has a `k`-linear
retraction, when `y` has degree zero. -/
private theorem δ_cup_of_leftInverse_zero (N : Rep k G) {p n : ℤ} (h : p + 0 = n)
    (x : tateCohomology S.X₃ p) (y : tateCohomology N 0) :
    _root_.TateCohomology.δ (haveI := hS.epi_g;
      Rep.shortExact_map_tensorRight_of_leftInverse hS.exact N hr) n (cup S.X₃ N p 0 n h x y) =
      cup S.X₁ N (p + 1) 0 (n + 1) (by omega) (_root_.TateCohomology.δ hS p x) y := by
  obtain rfl : p = n := by omega
  rw [cup_zero_right, cup_zero_right]
  exact δ_cupH0 hS _ p x y

/-- The upward step in the proof of `δ_cup_of_leftInverse`: if the rule holds in degree `q ≥ 0` for
the upward shift of `N`, then it holds in degree `q + 1` for `N`. -/
private theorem δ_cup_of_leftInverse_add_one (N : Rep k G) {p q n : ℤ} (hq : 0 ≤ q)
    (h : p + q = n) (x : tateCohomology S.X₃ p)
    (ih : ∀ y : tateCohomology (dimensionShiftUp N) q,
      _root_.TateCohomology.δ (haveI := hS.epi_g;
        Rep.shortExact_map_tensorRight_of_leftInverse hS.exact (dimensionShiftUp N) hr) n
          (cup S.X₃ (dimensionShiftUp N) p q n h x y) =
        cup S.X₁ (dimensionShiftUp N) (p + 1) q (n + 1) (by omega)
          (_root_.TateCohomology.δ hS p x) y)
    (y : tateCohomology N (q + 1)) :
    _root_.TateCohomology.δ (haveI := hS.epi_g;
      Rep.shortExact_map_tensorRight_of_leftInverse hS.exact N hr) (n + 1)
        (cup S.X₃ N p (q + 1) (n + 1) (by omega) x y) =
      cup S.X₁ N (p + 1) (q + 1) (n + 1 + 1) (by omega) (_root_.TateCohomology.δ hS p x) y := by
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  have hD : (ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  rw [cup_dimensionShiftUpIso_hom S.X₃ N hq h rfl,
    cup_dimensionShiftUpIso_hom S.X₁ N hq (by omega : p + 1 + q = n + 1) rfl, ← ih,
    map_zsmul_unit, Int.negOnePow_succ, Units.neg_smul, ← smul_neg, tensorDimensionShiftUpIso_hom,
    tensorDimensionShiftUpIso_hom]
  exact congrArg (p.negOnePow • ·)
    (δ_comp_δ_tensor hS hr hD (leftInverse_coindBotUnit N) n (cup S.X₃ _ p q n h x y))

/-- The downward step in the proof of `δ_cup_of_leftInverse`: if the rule holds in degree `q + 1`
for the downward shift of `N`, where `q < 0`, then it holds in degree `q` for `N`. -/
private theorem δ_cup_of_leftInverse_of_add_one (N : Rep k G) {p q n : ℤ} (hq : q < 0)
    (h : p + q = n) (x : tateCohomology S.X₃ p)
    (ih : ∀ y : tateCohomology (dimensionShiftDown N) (q + 1),
      _root_.TateCohomology.δ (haveI := hS.epi_g;
        Rep.shortExact_map_tensorRight_of_leftInverse hS.exact (dimensionShiftDown N) hr) (n + 1)
          (cup S.X₃ (dimensionShiftDown N) p (q + 1) (n + 1) (by omega) x y) =
        cup S.X₁ (dimensionShiftDown N) (p + 1) (q + 1) (n + 1 + 1) (by omega)
          (_root_.TateCohomology.δ hS p x) y)
    (y : tateCohomology N q) :
    _root_.TateCohomology.δ (haveI := hS.epi_g;
      Rep.shortExact_map_tensorRight_of_leftInverse hS.exact N hr) n (cup S.X₃ N p q n h x y) =
      cup S.X₁ N (p + 1) q (n + 1) (by omega) (_root_.TateCohomology.δ hS p x) y := by
  have hD : (ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N
  obtain ⟨ρ, hρ⟩ := Rep.exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit N)
  refine (tensorDimensionShiftDownIso N S.X₁ (n + 1) (n + 1 + 1) rfl).toLinearEquiv.injective ?_
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  have key := δ_comp_δ_tensor hS hr hD hρ n (cup S.X₃ N p q n h x y)
  have e := cup_dimensionShiftDownIso_hom S.X₁ N hq (by omega : p + 1 + q = n + 1) rfl
    (_root_.TateCohomology.δ hS p x) y
  rw [← ih, cup_dimensionShiftDownIso_hom S.X₃ N hq h rfl x y, map_zsmul_unit, Int.negOnePow_succ,
    Units.neg_smul] at e
  replace e := congrArg (p.negOnePow • ·) e
  simp only [negOnePow_smul_negOnePow_smul, smul_neg] at e
  rw [tensorDimensionShiftDownIso_hom, tensorDimensionShiftDownIso_hom] at e
  rw [tensorDimensionShiftDownIso_hom]
  exact neg_inj.1 (key.symm.trans e)

/-- **The cup product rule in the first variable for a split short exact sequence.** For a short
exact sequence `S` whose first map has a `k`-linear retraction, `x` of degree `p` and `y` of any
degree `q`, `δ (x ∪ y) = δ x ∪ y`, where the first `δ` is the connecting map of the tensor product
of `S` on the right with `N`, which is short exact by
`Rep.shortExact_map_tensorRight_of_leftInverse`. Together with the rule
`x ∪ δ y = (-1)^p δ (x ∪ y)` in the second variable (`TauCeti.TateCohomology.cup_δ_of_leftInverse`),
this is the compatibility of the cup product with connecting maps in both variables. -/
theorem δ_cup_of_leftInverse (N : Rep k G) {p q n : ℤ} (h : p + q = n)
    (x : tateCohomology S.X₃ p) (y : tateCohomology N q) :
    _root_.TateCohomology.δ (haveI := hS.epi_g;
      Rep.shortExact_map_tensorRight_of_leftInverse hS.exact N hr) n (cup S.X₃ N p q n h x y) =
      cup S.X₁ N (p + 1) q (n + 1) (by omega) (_root_.TateCohomology.δ hS p x) y := by
  rcases le_or_gt 0 q with hq | hq
  · induction q, hq using Int.leInduction generalizing N n with
    | base => exact δ_cup_of_leftInverse_zero hS hr N h x y
    | succ q hq ih =>
      obtain rfl : n = p + q + 1 := by omega
      exact δ_cup_of_leftInverse_add_one hS hr N hq rfl x (ih (dimensionShiftUp N) rfl) y
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    clear hq
    induction m generalizing N n with
    | zero =>
      -- `Int.negSucc 0 + 1` is `0` by definition, so the hypothesis of the step is the degree-zero
      -- case.
      exact δ_cup_of_leftInverse_of_add_one hS hr N (Int.negSucc_lt_zero 0) h x
        (δ_cup_of_leftInverse_zero hS hr (dimensionShiftDown N) (by omega) x) y
    | succ m ih =>
      exact δ_cup_of_leftInverse_of_add_one hS hr N (Int.negSucc_lt_zero _) h x
        (ih (dimensionShiftDown N) (by omega)) y

end TauCeti.TateCohomology
