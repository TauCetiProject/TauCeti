/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.ChangeOfGroup
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# The Tate cup product under change of group in positive degrees

Let `φ : G →* Q` be a homomorphism of finite groups. For classes `x` and `y` of positive degrees in
the Tate cohomology of `Q`-representations `M` and `N`, and morphisms `f : Res_φ M ⟶ M'` and
`g : Res_φ N ⟶ N'`, change of group (`TauCeti.TateCohomology.posMap`) carries the cup product
`x ∪ y` along `f ⊗ g` to the cup product of the changed classes
(`TauCeti.TateCohomology.cup_posMap`). Restriction to a subgroup and inflation from a quotient are
both instances. For inflation this is the compatibility that, together with the scaling of the
fundamental class, gives the inflation formula for the Tate isomorphism of a class formation.
Both degrees must be positive, since change of group does not exist in Tate degree zero.

## Main statements

* `TauCeti.TateCohomology.cup_posMap`: change of group preserves the cup product of two classes
  of positive degree.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter V, §3 and Chapter VI, §5.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G Q : Type u} [CommRing k] [Group G] [Group Q] [Fintype G] [Fintype Q]
  (φ : G →* Q)

-- Proof strategy. The cup product is defined by dimension shifting in the second factor, so the
-- proof shifts the second degree down to zero along the coinduced sequences
-- `0 → N → Coind_⊥^Q N → N' → 0`. Their restrictions along `φ` are no longer coinduced, but they
-- are still split by evaluation at `1`, so the cup product over `G` still turns their connecting
-- maps into connecting maps of the tensored sequences (`cup_δ_of_leftInverse`), and change of
-- group commutes with all of these connecting maps. Since change of group does not exist in Tate
-- degree zero, the second factor is carried along as an ordinary cohomology class: in degree zero
-- it is an invariant of `N`, which is also an invariant of `Res_φ N`, and cup product with it is a
-- map of coefficients.

-- The base case: a degree-zero right factor is represented by an invariant, and cup product with it
-- is the coefficient map `m ↦ m ⊗ v`, which commutes with change of group.
private theorem posMap_cupH0_H0π (M N : Rep k Q) (p : ℕ) (x : tateCohomology M (p + 1 : ℕ))
    (v : N.ρ.invariants) :
    posMap φ (𝟙 (Rep.res φ (M ⊗ N))) (p + 1) (cupH0 M N (p + 1 : ℕ) x (H0π N v)) =
      cupH0 (Rep.res φ M) (Rep.res φ N) (p + 1 : ℕ) (posMap φ (𝟙 (Rep.res φ M)) (p + 1) x)
        (H0π (Rep.res φ N) ⟨v, fun g ↦ v.2 (φ g)⟩) := by
  rw [cupH0_H0π, cupH0_H0π, ← ModuleCat.comp_apply, map_comp_posMap, ← ModuleCat.comp_apply,
    posMap_comp_map]
  have hcoef : (resFunctor φ).map (M.tensorInvariant v) =
      (Rep.res φ M).tensorInvariant (N := Rep.res φ N) ⟨v, fun g ↦ v.2 (φ g)⟩ := by
    ext m
    -- Restriction keeps the underlying linear map, so both sides are `m ↦ m ⊗ v`.
    exact (Rep.tensorInvariant_hom_apply M v m).trans
      (Rep.tensorInvariant_hom_apply (Rep.res φ M) (N := Rep.res φ N)
        ⟨v, fun g ↦ v.2 (φ g)⟩ m).symm
  rw [Category.comp_id, Category.id_comp, hcoef]
  rfl

omit [Fintype Q] in
-- In degree zero, change of group sends the class of an invariant to the class of the same
-- element, now an invariant of the restricted representation.
private theorem fromGroupCohomology_zero_map (N : Rep k Q) (z : groupCohomology N 0) :
    fromGroupCohomology (Rep.res φ N) 0 (groupCohomology.map φ (𝟙 (Rep.res φ N)) 0 z) =
      H0π (Rep.res φ N) ⟨(groupCohomology.H0Iso N).hom z,
        fun g ↦ ((groupCohomology.H0Iso N).hom z).2 (φ g)⟩ := by
  rw [fromGroupCohomology_zero, ModuleCat.comp_apply]
  exact congrArg (H0π (Rep.res φ N)) (Subtype.ext
    (groupCohomology.map_H0Iso_hom_f_apply φ (𝟙 (Rep.res φ N)) z))

/-- The inductive step: the compatibility of the cup product with change of group for an ordinary
class of degree `q + 1` in the second factor follows from the compatibility in degree `q` for the
upward dimension shift of the second factor. -/
private theorem posMap_cup_fromGroupCohomology_succ (M : Rep k Q) (p : ℕ)
    (x : tateCohomology M (p + 1 : ℕ)) (q : ℕ) (N : Rep k Q)
    (ih : ∀ z : groupCohomology (dimensionShiftUp N) q,
      posMap φ (𝟙 (Rep.res φ (M ⊗ dimensionShiftUp N))) (p + q + 1)
          (cup M (dimensionShiftUp N) (p + 1 : ℕ) q (p + q + 1 : ℕ) (by push_cast; ring) x
            (fromGroupCohomology (dimensionShiftUp N) q z)) =
        cup (Rep.res φ M) (Rep.res φ (dimensionShiftUp N)) (p + 1 : ℕ) q (p + q + 1 : ℕ)
          (by push_cast; ring) (posMap φ (𝟙 (Rep.res φ M)) (p + 1) x)
          (fromGroupCohomology (Rep.res φ (dimensionShiftUp N)) q
            (groupCohomology.map φ (𝟙 (Rep.res φ (dimensionShiftUp N))) q z)))
    (z : groupCohomology N (q + 1)) :
    posMap φ (𝟙 (Rep.res φ (M ⊗ N))) (p + (q + 1) + 1)
        (cup M N (p + 1 : ℕ) (q + 1 : ℕ) (p + (q + 1) + 1 : ℕ) (by push_cast; ring) x
          (fromGroupCohomology N (q + 1) z)) =
      cup (Rep.res φ M) (Rep.res φ N) (p + 1 : ℕ) (q + 1 : ℕ) (p + (q + 1) + 1 : ℕ)
        (by push_cast; ring) (posMap φ (𝟙 (Rep.res φ M)) (p + 1) x)
        (fromGroupCohomology (Rep.res φ N) (q + 1)
          (groupCohomology.map φ (𝟙 (Rep.res φ N)) (q + 1) z)) := by
  -- Write `z = δ z'` for the dimension-shifting sequence `0 → N → Coind_⊥^Q N → N' → 0`.
  let D := ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
    (coindBotUnit_comp_dimensionShiftUpπ N)
  have hD : D.ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  have hresD : (D.map (Rep.resFunctor φ)).ShortExact := (shortExact_res φ).2 hD
  obtain ⟨z', rfl⟩ : ∃ z', groupCohomology.δ hD q (q + 1) rfl z' = z :=
    (ModuleCat.epi_iff_surjective _).1
      (groupCohomology.epi_δ_of_isZero hD q (groupCohomology.isZero_coindBot_succ N.V q)) z
  -- On both sides, the ordinary connecting map becomes the Tate connecting map.
  have hL : fromGroupCohomology N (q + 1) (groupCohomology.δ hD q (q + 1) rfl z') =
      _root_.TateCohomology.δ hD q (fromGroupCohomology (dimensionShiftUp N) q z') := by
    simpa only [ModuleCat.comp_apply] using congr($(δ_comp_fromGroupCohomology hD q) z')
  have hR : fromGroupCohomology (Rep.res φ N) (q + 1)
        (groupCohomology.map φ (𝟙 (Rep.res φ N)) (q + 1)
          (groupCohomology.δ hD q (q + 1) rfl z')) =
      _root_.TateCohomology.δ hresD q (fromGroupCohomology (Rep.res φ (dimensionShiftUp N)) q
        (groupCohomology.map φ (𝟙 (Rep.res φ (dimensionShiftUp N))) q z')) := by
    have h₁ := congr($(TauCeti.groupCohomology.δ_naturality φ hD hresD (𝟙 _) q (q + 1) rfl) z')
    have h₂ := congr($(δ_comp_fromGroupCohomology hresD q) (groupCohomology.map φ (𝟙 _) q z'))
    simp only [ModuleCat.comp_apply] at h₁ h₂
    exact (congrArg (fromGroupCohomology (Rep.res φ N) (q + 1)) h₁).trans h₂
  rw [hL, hR]
  -- Both sequences are split by evaluation at `1`, so on either side the cup product turns the
  -- connecting map in the second factor into the connecting map of the tensored sequence, and
  -- change of group commutes with the connecting maps of the tensored sequences.
  have hr := leftInverse_coindBotUnit N
  have hMD : (D.map (tensorLeft M)).ShortExact :=
    haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact M hr
  have hresMD : ((D.map (Rep.resFunctor φ)).map (tensorLeft (Rep.res φ M))).ShortExact :=
    haveI := hresD.epi_g; shortExact_map_tensorLeft_of_leftInverse hresD.exact (Rep.res φ M) hr
  have hdeg : ((p + 1 : ℕ) : ℤ) + (q : ℤ) = ((p + q + 1 : ℕ) : ℤ) := by push_cast; ring
  let w := cup M (dimensionShiftUp N) (p + 1 : ℕ) q (p + q + 1 : ℕ) hdeg x
    (fromGroupCohomology (dimensionShiftUp N) q z')
  refine (congrArg (posMap φ (𝟙 (Rep.res φ (M ⊗ N))) (p + (q + 1) + 1))
    (cup_δ_of_leftInverse M hD hr hdeg x _)).trans ?_
  rw [map_zsmul_unit]
  refine (congrArg (((p + 1 : ℕ) : ℤ).negOnePow • ·)
    congr($(δ_comp_posMap φ hMD hresMD (𝟙 _) (p + q + 1)) w)).trans ?_
  rw [ModuleCat.comp_apply]
  refine (congrArg (fun t ↦ ((p + 1 : ℕ) : ℤ).negOnePow •
    _root_.TateCohomology.δ hresMD ((p + q + 1 : ℕ) : ℤ) t) (ih z')).trans ?_
  exact (cup_δ_of_leftInverse (Rep.res φ M) hresD hr hdeg _ _).symm

/-- The compatibility of the cup product with change of group, for a left factor of positive
degree and a right factor given by an ordinary class of any nonnegative degree. -/
private theorem posMap_cup_fromGroupCohomology (M : Rep k Q) (p : ℕ)
    (x : tateCohomology M (p + 1 : ℕ)) (q : ℕ) (N : Rep k Q) (z : groupCohomology N q) :
    posMap φ (𝟙 (Rep.res φ (M ⊗ N))) (p + q + 1)
        (cup M N (p + 1 : ℕ) q (p + q + 1 : ℕ) (by push_cast; ring) x
          (fromGroupCohomology N q z)) =
      cup (Rep.res φ M) (Rep.res φ N) (p + 1 : ℕ) q (p + q + 1 : ℕ) (by push_cast; ring)
        (posMap φ (𝟙 (Rep.res φ M)) (p + 1) x)
        (fromGroupCohomology (Rep.res φ N) q (groupCohomology.map φ (𝟙 (Rep.res φ N)) q z)) := by
  induction q generalizing N with
  | zero =>
    have hz : fromGroupCohomology N 0 z = H0π N ((groupCohomology.H0Iso N).hom z) := by
      rw [fromGroupCohomology_zero, ModuleCat.comp_apply]
    rw [hz, fromGroupCohomology_zero_map]
    exact (congrArg (posMap φ (𝟙 (Rep.res φ (M ⊗ N))) (p + 1))
      (LinearMap.congr_fun₂ (cup_zero_right M N ((p + 1 : ℕ) : ℤ) (by simp)) x _)).trans
      ((posMap_cupH0_H0π φ M N p x _).trans (LinearMap.congr_fun₂
        (cup_zero_right (Rep.res φ M) (Rep.res φ N) ((p + 1 : ℕ) : ℤ) (by simp)) _ _).symm)
  | succ q ih =>
    exact posMap_cup_fromGroupCohomology_succ φ M p x q N (ih (dimensionShiftUp N)) z

/-- Change of group preserves the cup product of two positive-degree classes, with the identity
coefficient maps. -/
private theorem posMap_id_cup (M N : Rep k Q) (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r]
    (h : (p : ℤ) + q = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    posMap φ (𝟙 (Rep.res φ (M ⊗ N))) r (cup M N p q r h x y) =
      cup (Rep.res φ M) (Rep.res φ N) p q r h (posMap φ (𝟙 (Rep.res φ M)) p x)
        (posMap φ (𝟙 (Rep.res φ N)) q y) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  obtain rfl : r = p + (q + 1) + 1 := by omega
  -- In positive degree every Tate class of the second factor is the image of an ordinary class.
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (fromGroupCohomology N (q + 1))) y
  rw [← ModuleCat.comp_apply (fromGroupCohomology N (q + 1)), fromGroupCohomology_comp_posMap,
    ModuleCat.comp_apply]
  exact posMap_cup_fromGroupCohomology φ M p x (q + 1) N z

/-- **Change of group preserves the Tate cup product in positive degrees.** For `φ : G →* Q` and
morphisms `f : Res_φ M ⟶ M'`, `g : Res_φ N ⟶ N'`, changing the group of `x ∪ y` along
`f ⊗ g` gives the cup product of the changed classes, for `x` and `y` of positive degrees. -/
theorem cup_posMap (M N : Rep k Q) {M' N' : Rep k G} (f : Rep.res φ M ⟶ M')
    (g : Rep.res φ N ⟶ N') (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (h : (p : ℤ) + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q) :
    posMap φ (M := M ⊗ N) (f ⊗ₘ g : Rep.res φ M ⊗ Rep.res φ N ⟶ M' ⊗ N') r
        (cup M N p q r h x y) =
      cup M' N' p q r h (posMap φ f p x) (posMap φ g q y) := by
  have hf : ∀ {A : Rep k Q} {B : Rep k G} (f : Rep.res φ A ⟶ B) (n : ℕ) [NeZero n],
      posMap φ f n = posMap φ (𝟙 (Rep.res φ A)) n ≫ (tateCohomologyFunctor n).map f := by
    intro A B f n _
    rw [posMap_comp_map, Category.id_comp]
  have hfg : posMap φ (M := M ⊗ N) (f ⊗ₘ g : Rep.res φ M ⊗ Rep.res φ N ⟶ M' ⊗ N') r =
      posMap φ (M := M ⊗ N) (𝟙 (Rep.res φ M ⊗ Rep.res φ N) :
          Rep.res φ M ⊗ Rep.res φ N ⟶ Rep.res φ M ⊗ Rep.res φ N) r ≫
        (tateCohomologyFunctor (r : ℤ)).map (Rep.res φ M ◁ g) ≫
          (tateCohomologyFunctor (r : ℤ)).map (f ▷ N') := by
    rw [← Functor.map_comp, ← tensorHom_def']
    exact hf _ r
  rw [hf f, hf g, ModuleCat.comp_apply, ModuleCat.comp_apply, cup_map_left, cup_map_right,
    ← posMap_id_cup, hfg]
  rfl

end TauCeti.TateCohomology
