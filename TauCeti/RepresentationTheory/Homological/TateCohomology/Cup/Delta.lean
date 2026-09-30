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
for the connecting maps `δ` of the upward and downward dimension-shifting sequences
(`TauCeti.TateCohomology.cup_dimensionShiftUpIso_hom`). This file extends the rule, for second
degree `q ≥ 0`, to the connecting maps of every short exact sequence `0 → N₁ → N₂ → N₃ → 0`
whose first map has a `k`-linear retraction (`TauCeti.TateCohomology.cup_δ_of_leftInverse`).

Such a retraction `r` gives a morphism from the sequence to the upward dimension-shifting sequence
of `N₁` which is the identity on `N₁`: on `N₂` it is `n ↦ (g ↦ r (g • n))`. The connecting maps
of the two sequences, and of their tensor products with the first factor, are then related by
naturality of the connecting maps, and the cup product is natural in the second variable.

## Main statements

* `TauCeti.TateCohomology.cup_δ_of_leftInverse`: for a short exact sequence whose first map has a
  `k`-linear retraction, `x ∪ δ y = (-1)^p δ (x ∪ y)` for `x` of degree `p` and `y` of degree
  `q ≥ 0`.

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

/-- The morphism `n ↦ (g ↦ r (g • n))` from a representation to the representation coinduced from
the trivial subgroup, attached to a `k`-linear map `r`. -/
private def toCoindBot (A : Rep k G) {X : Type u} [AddCommGroup X] [Module k X]
    (r : A.V →ₗ[k] X) : A ⟶ coindBot k G X :=
  coindBotUnit A ≫ (coindBotFunctor k G).map (ModuleCat.ofHom r)

private theorem toCoindBot_hom_apply_coe (A : Rep k G) {X : Type u} [AddCommGroup X] [Module k X]
    (r : A.V →ₗ[k] X) (a : A) (g : G) :
    (dsimp% only (((toCoindBot A r).hom a).1 g)) = r (A.ρ g a) := by
  -- The underlying map of a composite of representations is the composite of the underlying maps;
  -- `Rep.hom_comp` does not fire here because the middle object is `coindBot k G A.V` on one side
  -- and `(coindBotFunctor k G).obj _` on the other.
  change (((coindBotFunctor k G).map (ModuleCat.ofHom r)).hom ((coindBotUnit A).hom a)).1 g = _
  rw [coindBotFunctor_map_hom_apply_coe, ModuleCat.hom_ofHom, coindBotUnit_hom_apply_coe]

/-- If `r` is a retraction of `f : A ⟶ B`, then `f` followed by `n ↦ (g ↦ r (g • n))` is the
embedding of `A` into its coinduced representation. -/
private theorem comp_toCoindBot_of_leftInverse {A B : Rep k G} (f : A ⟶ B) {r : B.V →ₗ[k] A.V}
    (hr : Function.LeftInverse r f.hom) : f ≫ toCoindBot B r = coindBotUnit A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext a : 1
  refine Subtype.ext (funext fun g ↦ ?_)
  -- Evaluate both sides as functions `G → A`.
  change ((toCoindBot B r).hom (f.hom a)).1 g = ((coindBotUnit A).hom a).1 g
  rw [toCoindBot_hom_apply_coe, coindBotUnit_hom_apply_coe, ← Rep.hom_comm_apply, hr]

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

variable [Fintype G]

/-- **The cup product rule for a split short exact sequence in the second variable.** For a short
exact sequence `S` whose first map has a `k`-linear retraction, `x` of degree `p` and `y` of degree
`q ≥ 0`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the second `δ` is the connecting map of the tensor
product of `S` with `M`, which is short exact by `Rep.shortExact_map_tensorLeft_of_leftInverse`. -/
theorem cup_δ_of_leftInverse (M : Rep k G) {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) {p q n : ℤ} (hq : 0 ≤ q)
    (h : p + q = n) (x : tateCohomology M p) (y : tateCohomology S.X₃ q) :
    cup M S.X₁ p (q + 1) (n + 1) (by omega) x (_root_.TateCohomology.δ hS q y) =
      p.negOnePow • _root_.TateCohomology.δ
        (haveI := hS.epi_g; shortExact_map_tensorLeft_of_leftInverse hS.exact M r hr) n
        (cup M S.X₃ p q n h x y) := by
  have := hS.epi_g
  have hMS := shortExact_map_tensorLeft_of_leftInverse hS.exact M r hr
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

end TauCeti.TateCohomology
