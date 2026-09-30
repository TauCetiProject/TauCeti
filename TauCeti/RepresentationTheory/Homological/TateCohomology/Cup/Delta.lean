/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# The cup product and the connecting maps of a split sequence

The Tate cup product is defined in the second variable by the rule `x ∪ δ y = (-1)^p δ (x ∪ y)`
for the connecting maps `δ` of the upward dimension-shifting sequence when `y` has degree `q ≥ 0`,
and of the downward one when `q < 0` (`TauCeti.TateCohomology.cup_dimensionShiftUpIso_hom`,
`TauCeti.TateCohomology.cup_dimensionShiftDownIso_hom`). This file extends the rule, in every
degree `q`, to the connecting maps of every short exact sequence `0 → N₁ → N₂ → N₃ → 0` whose first
map has a `k`-linear retraction (`TauCeti.TateCohomology.cup_δ_of_leftInverse`).

For `q ≥ 0`, a retraction `r` gives a morphism from the sequence to the upward dimension-shifting
sequence of `N₁` which is the identity on `N₁`: on `N₂` it is `n ↦ (g ↦ r (g • n))`. For `q < 0`,
the corresponding `k`-linear section `s` of the last map gives a morphism to the sequence from the
downward dimension-shifting sequence of `N₃` which is the identity on `N₃`: on `Ind_⊥^G N₃` it is
`⟦g ⊗ₜ n⟧ ↦ g⁻¹ • s n`. In either case the connecting maps of the two sequences, and of their tensor
products with the first factor, are related by naturality of the connecting maps, and the cup
product is natural in the second variable.

## Main statements

* `TauCeti.TateCohomology.cup_δ_of_leftInverse`: for a short exact sequence whose first map has a
  `k`-linear retraction, `x ∪ δ y = (-1)^p δ (x ∪ y)` for `x` of degree `p` and `y` of any degree
  `q`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

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
      (by rw [reassoc_of% (comp_toCoindBot_of_leftInverse S.f hr),
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
`k`-linear retraction, when `y` has degree `q ≥ 0`: compare with the upward dimension-shifting
sequence of the first term. -/
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
`k`-linear section, when `y` has degree `q < 0`: compare with the downward dimension-shifting
sequence of the last term. -/
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
        (haveI := hS.epi_g; shortExact_map_tensorLeft_of_leftInverse hS.exact M r hr) n
        (cup M S.X₃ p q n h x y) := by
  rcases le_or_gt 0 q with hq | hq
  · exact cup_δ_of_leftInverse_of_nonneg M hS hr _ hq h x y
  · have := hS.epi_g
    obtain ⟨s, hs⟩ := Rep.exists_rightInverse_of_leftInverse hS.exact hr
    exact cup_δ_of_rightInverse_of_neg M hS hs _ hq h x y

end TauCeti.TateCohomology
