/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.PositiveZero
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Delta

/-!
# Restriction of the Tate cup product in nonnegative bidegrees

For a subgroup `H` of a finite group `G`, restriction to `H` preserves the Tate cup product of a
class of degree `p ≥ 0` and a class of degree `q ≥ 0`
(`TauCeti.TateCohomology.cup_res_of_nonneg`).

The proof is by induction on `q`, starting from the bidegrees `(p, 0)`, where the cup product is
induced by a morphism of coefficients (`TauCeti.TateCohomology.cup_res_zero_zero`,
`TauCeti.TateCohomology.cup_posRes_zero_right`). A class `y` of degree `q + 1` is the image of a
class `y'` of degree `q` of the upward dimension shift of `N` under the connecting map of the
dimension-shifting sequence, and `x ∪ δ y' = (-1)^p δ (x ∪ y')`. Restriction commutes with the
connecting maps in nonnegative degrees (`TauCeti.TateCohomology.δ_comp_res`), and after restriction
the dimension-shifting sequence is still split over `k`, so the same rule holds for the cup product
over `H` (`TauCeti.TateCohomology.cup_δ_of_leftInverse`).

See Artin and Tate, *Class Field Theory*, Preliminaries, §2, and Brown, *Cohomology of Groups*,
Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- The inductive step: restriction preserves the cup product in bidegree `(p, q + 1)` if it does
in bidegree `(p, q)` for the upward dimension shift of the second factor. -/
private theorem cup_res_add_one (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (h : p + q = r) (x : tateCohomology M p)
    (ih : ∀ y : tateCohomology (dimensionShiftUp N) q,
      res (M ⊗ dimensionShiftUp N) H r (cup M (dimensionShiftUp N) p q r h x y) =
        cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftUp N)) p q r h
          (res M H p x) (res (dimensionShiftUp N) H q y))
    (y : tateCohomology N (q + 1)) :
    res (M ⊗ N) H (r + 1) (cup M N p (q + 1) (r + 1) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p (q + 1) (r + 1) (by omega)
        (res M H p x) (res N H (q + 1) y) := by
  have hD : (ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  have hMD : ((ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact N M
  -- Write `y = δ y'` for the dimension-shifting sequence `0 → N → Coind_⊥^G N → N' → 0`.
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  -- On the left, `x ∪ δ y' = (-1)^p δ (x ∪ y')`, and restriction commutes with `δ` and, by
  -- hypothesis, with `x ∪ y'`.
  rw [cup_dimensionShiftUpIso_hom M N hq h rfl, map_zsmul_unit, tensorDimensionShiftUpIso_hom]
  have hL := congr($(δ_comp_res hMD H (by omega : 0 ≤ r)) (cup M (dimensionShiftUp N) p q r h x y))
  have hR := congr($(δ_comp_res hD H hq) y)
  simp only [ModuleCat.comp_apply] at hL hR
  refine (congrArg (p.negOnePow • ·) (hL.trans (congrArg _ (ih y)))).trans ?_
  -- On the right, restriction commutes with `δ`.
  rw [dimensionShiftUpIso_hom]
  refine Eq.trans ?_ (congrArg (cup _ _ p (q + 1) (r + 1) _ (res M H p x)) hR).symm
  -- The restricted dimension-shifting sequence is still split by evaluation at `1`, so the cup
  -- product over `H` satisfies the same rule for its connecting map.
  have hresD := (shortExact_res H.subtype).2 hD
  exact (cup_δ_of_leftInverse (Rep.res H.subtype M) hresD (leftInverse_coindBotUnit N) h _
    _).symm

/-- **Restriction preserves the Tate cup product in nonnegative bidegrees.** For a subgroup `H` of
a finite group `G`, a class `x` of degree `p ≥ 0` and a class `y` of degree `q ≥ 0`, the
restriction of `x ∪ y` to `H` is the cup product of the restrictions of `x` and `y`. -/
@[simp]
theorem cup_res_of_nonneg (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p + q = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    res (M ⊗ N) H r (cup M N p q r h x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h (res M H p x) (res N H q y) := by
  induction q, hq using Int.leInduction generalizing N r with
  | base =>
    obtain rfl : p = r := by omega
    rcases hp.eq_or_lt with rfl | hp
    · exact cup_res_zero_zero M N H x y
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) + 1 := ⟨p.toNat - 1, by omega⟩
      simp only [res_ofNat_succ, res_zero]
      exact cup_posRes_zero_right M N H n x y
  | succ q hq ih =>
    obtain rfl : r = p + q + 1 := by omega
    exact cup_res_add_one M N H hp hq rfl x (ih (dimensionShiftUp N) rfl) y

end TauCeti.TateCohomology
