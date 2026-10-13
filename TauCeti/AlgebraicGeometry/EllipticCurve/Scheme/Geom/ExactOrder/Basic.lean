/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Points of exact order `N` on an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `P` an `S`-point of `E`. Following Katz and
Mazur, `P` has **exact order `N`** when the relative effective Cartier divisor

  `D = [P] + [2P] + ⋯ + [NP]`

on `E` is a subgroup scheme of `E`. This is Drinfeld's notion of a point of exact order `N`, and it
is the definition of a `[Γ₁(N)]`-structure over an arbitrary base. It is not a condition on the
order of `P` in a group of points: over a base of characteristic `p`, the divisor `p[0]` is the
kernel of the relative Frobenius of `E`, so the zero section has exact order `p`.

Each `[aP]` is the divisor of the section `aP` of the smooth separated curve `E ⟶ S`, cut out by
its ideal sheaf, and the sum of divisors is the product of ideal sheaves
(`EllipticCurveGeom.multiplesDivisor`). The subgroup condition asks that the closed subscheme `D`
carry a group-scheme structure for which its inclusion into `E` is a homomorphism
(`EllipticCurveGeom.IsOfExactOrder`); by the closed-subgroup criterion this says that the ideal
sheaf of `D` vanishes on the identity, on the sum of two points of `D` and on the negative of a
point of `D`, scheme-theoretically.

The main theorem is that a point of exact order `N` is killed by `N`
(`EllipticCurveGeom.IsOfExactOrder.pow_eq_one`), so it is an `S`-point of the `N`-torsion `E[N]`
(`EllipticCurveGeom.IsOfExactOrder.comp_mulBy_eq_one`). This holds over every base, including
nonreduced ones, with no finiteness or rank hypothesis on `D`.

Points of exact order `N` are stable under base change
(`EllipticCurveGeom.IsOfExactOrder.pointsPullback`): along a pullback square of elliptic curves,
the divisor `[P'] + ⋯ + [NP']` of the base change `P'` of `P` is the inverse image of
`[P] + ⋯ + [NP]`, and the inverse image of a closed subgroup scheme is again a closed subgroup
scheme (`EllipticCurveGeom.exists_grpObj_isMonHom_comap`). This is the base-change functoriality
of `[Γ₁(N)]`-structures.

Following `EllipticCurveGeom.mulBy`, the group law on points of `E` is written multiplicatively:
`P ^ a` is the point `aP`, and `1` is the zero section.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.multiplesDivisor E P N`: the divisor
  `[P] + [2P] + ⋯ + [NP]`, as an ideal sheaf on `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder E P N`: the point `P` has exact
  order `N` in the sense of Katz and Mazur.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_iff`: the closed-subgroup criterion
  for `IsOfExactOrder`, in terms of the ideal sheaf of `[P] + ⋯ + [NP]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_multiplesDivisor`:
  `[P] + ⋯ + [NP]` is a relative effective Cartier divisor on `E` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.ker_comap_leftTranslation_hom`: translation by
  `Q` pulls the divisor `[x]` of a point back to `[x - Q]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.pow_eq_one`: a point of exact order
  `N` is killed by `N`; `IsOfExactOrder.comp_mulBy_eq_one` is the same statement for
  multiplication by `N`, which places the point in `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_one_iff`: the only point of exact
  order one is the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.multiplesDivisor_pointsPullback`: the divisor
  `[P] + ⋯ + [NP]` commutes with base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.pointsPullback`: points of exact
  order `N` are stable under base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact order
  `N`) and §3.2 (`[Γ₁(N)]`-structures).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The divisor `[P] + [2P] + ⋯ + [NP]` of the first `N` positive multiples of an `S`-point `P` of
an elliptic curve `E` over `S`, as an ideal sheaf on `E`: the product of the ideal sheaves of the
sections `P ^ a` for `1 ≤ a ≤ N`. For `N = 0` it is the empty divisor `⊤`. -/
noncomputable def multiplesDivisor (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    E.carrier.IdealSheafData :=
  ∏ a ∈ Finset.range N, (P ^ (a + 1)).left.ker

/-- **Points of exact order `N`** (Katz–Mazur). An `S`-point `P` of an elliptic curve `E` over `S`
has exact order `N` when the closed subscheme of the divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup
scheme of `E`: it carries a group-object structure in `Over S` for which its inclusion into `E` is
a homomorphism. By the closed-subgroup criterion
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_iff_ker_le`), such a structure is unique when it
exists. The divisor is indexed by `1 ≤ a ≤ N`, not by residues modulo `N`, since `NP = 0` is a
consequence (`IsOfExactOrder.pow_eq_one`) rather than an assumption. No rank condition is imposed:
being a sum of `N` divisors of degree one, the divisor already has degree `N`. -/
def IsOfExactOrder (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) : Prop :=
  ∃ _ : GrpObj (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)),
    IsMonHom (Over.homMk (E.multiplesDivisor P N).subschemeι :
      Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap)

variable {E}

/-- A point `P` has exact order `N` exactly when the closed subscheme of `[P] + ⋯ + [NP]` is a
subgroup scheme of `E`. -/
theorem isOfExactOrder_def {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} :
    E.IsOfExactOrder P N ↔
      ∃ _ : GrpObj (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)),
        IsMonHom (Over.homMk (E.multiplesDivisor P N).subschemeι :
          Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
            Over.mk E.structureMap) :=
  Iff.rfl

/-- **The closed-subgroup criterion for points of exact order `N`.** A point `P` has exact order
`N` exactly when the ideal sheaf of `D = [P] + ⋯ + [NP]` vanishes on the identity, on the product
of two points of `D` and on the inverse of a point of `D`. -/
theorem isOfExactOrder_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} :
    E.IsOfExactOrder P N ↔
      E.multiplesDivisor P N ≤ E.zero.ker ∧
      E.multiplesDivisor P N ≤ (((Over.homMk (E.multiplesDivisor P N).subschemeι :
          Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
            Over.mk E.structureMap) ⊗ₘ (Over.homMk (E.multiplesDivisor P N).subschemeι :
          Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
            Over.mk E.structureMap)) ≫ μ[Over.mk E.structureMap]).left.ker ∧
      E.multiplesDivisor P N ≤ ((Over.homMk (E.multiplesDivisor P N).subschemeι :
          Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
            Over.mk E.structureMap) ≫ ι[Over.mk E.structureMap]).left.ker := by
  let i : Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
      Over.mk E.structureMap := Over.homMk (E.multiplesDivisor P N).subschemeι
  have : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (E.multiplesDivisor P N).subschemeι)
  have hi : i.left.ker = E.multiplesDivisor P N := Scheme.IdealSheafData.ker_subschemeι _
  rw [IsOfExactOrder, GroupScheme.exists_grpObj_isMonHom_iff_ker_le i, hi, one_left]

/-- The divisor of the first zero multiples of a point is empty. -/
@[simp]
theorem multiplesDivisor_zero (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    E.multiplesDivisor P 0 = ⊤ := by
  simp [multiplesDivisor]

/-- `[P] + ⋯ + [(N + 1)P]` is `[P] + ⋯ + [NP]` plus `[(N + 1)P]`. -/
theorem multiplesDivisor_succ (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    E.multiplesDivisor P (N + 1) =
      E.multiplesDivisor P N * Scheme.Hom.ker (Y := E.carrier) (P ^ (N + 1)).left :=
  Finset.prod_range_succ _ _

/-- The divisor `[P] + [2P] + ⋯ + [NP]` is a relative effective Cartier divisor on `E` over `S`. -/
theorem isRelativeEffectiveCartier_multiplesDivisor (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    (N : ℕ) : (E.multiplesDivisor P N).IsRelativeEffectiveCartier E.structureMap :=
  isRelativeEffectiveCartier_prod fun a _ ↦
    Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension (f := E.structureMap)
      _ (Over.w (P ^ (a + 1)))

/-- Each of the points `P, 2P, …, NP` lies on the divisor `[P] + [2P] + ⋯ + [NP]`. -/
theorem multiplesDivisor_le_ker {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N a : ℕ}
    (ha : a < N) : E.multiplesDivisor P N ≤ (P ^ (a + 1)).left.ker := by
  rw [multiplesDivisor, ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr ha)]
  exact mul_le_of_le_one_right bot_le le_top

/-! ### Translating divisors of points -/

/-- **Translating the divisor of a point.** Left translation `y ↦ Q * y` on `E` pulls the divisor
`[x]` of an `S`-point `x` back to the divisor `[Q⁻¹ * x]`. -/
theorem ker_comap_leftTranslation_hom (Q x : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    x.left.ker.comap (leftTranslation Q).hom.left = (Q⁻¹ * x).left.ker := by
  have := x.left.isClosedImmersion_of_comp_eq_id (f := E.structureMap) (Over.w _)
  refine (Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ (g := 𝟙 _) ?_).symm
  refine IsPullback.of_vert_isIso ⟨?_⟩
  rw [Category.id_comp, ← Over.comp_left, comp_leftTranslation_hom,
    toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, mul_inv_cancel_left]

/-- If `P` has exact order `N`, translation by `-P` carries the divisor `[P] + ⋯ + [NP]` onto
itself. -/
private theorem IsOfExactOrder.comap_leftTranslation_inv
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} (h : E.IsOfExactOrder P N) (hN : N ≠ 0) :
    (E.multiplesDivisor P N).comap (leftTranslation P).inv.left = E.multiplesDivisor P N := by
  obtain ⟨_, _⟩ := h
  let i : Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
      Over.mk E.structureMap := Over.homMk (E.multiplesDivisor P N).subschemeι
  have : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (E.multiplesDivisor P N).subschemeι)
  have hi : i.left.ker = E.multiplesDivisor P N := Scheme.IdealSheafData.ker_subschemeι _
  -- `P` is a point of the subgroup scheme `D`, through the lift `closedImmersionOverLift i P hP`.
  have hP : i.left.ker ≤ P.left.ker := by
    simpa only [hi, zero_add, pow_one] using multiplesDivisor_le_ker (P := P) (a := 0) (by omega)
  have hp : closedImmersionOverLift i P hP ≫ i = P := closedImmersionOverLift_comp i P hP
  -- Translations by the points `P` and `-P` of `D` carry `D` into itself.
  have h₁ := GroupScheme.ker_comap_leftTranslation_le i (closedImmersionOverLift i P hP)
  have h₂ := GroupScheme.ker_comap_leftTranslation_le i (closedImmersionOverLift i P hP)⁻¹
  rw [hp] at h₁
  rw [GrpObj.inv_comp, hp, ← leftTranslation_inv] at h₂
  rw [← hi]
  refine le_antisymm h₂ ?_
  calc i.left.ker
      = i.left.ker.comap ((leftTranslation P).inv ≫ (leftTranslation P).hom).left := by
        rw [Iso.inv_hom_id, Over.id_left, Scheme.IdealSheafData.comap_id]
    _ = (i.left.ker.comap (leftTranslation P).hom.left).comap (leftTranslation P).inv.left := by
        rw [Over.comp_left, Scheme.IdealSheafData.comap_comp]
    _ ≤ i.left.ker.comap (leftTranslation P).inv.left := Scheme.IdealSheafData.comap_mono _ h₁

/-! ### Points of exact order `N` are killed by `N` -/

/-- **A point of exact order `N` is killed by `N`** (Katz–Mazur, §1.4): if the divisor
`[P] + [2P] + ⋯ + [NP]` is a subgroup scheme of `E`, then `NP = 0`. -/
theorem IsOfExactOrder.pow_eq_one {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfExactOrder P N) : P ^ N = 1 := by
  obtain _ | n := N
  · exact pow_zero P
  -- Both `D + [(n + 1 + 1)P]` and `D + [P]` are `[P] + ⋯ + [(n + 1 + 1)P]`: the second because
  -- translation by `-P` carries `D` to `[2P] + ⋯ + [(n + 1 + 1)P]`.
  have hcancel : E.multiplesDivisor P (n + 1) * Scheme.Hom.ker (Y := E.carrier)
      (P ^ (n + 1 + 1)).left =
      E.multiplesDivisor P (n + 1) * Scheme.Hom.ker (Y := E.carrier) (P ^ (0 + 1)).left := by
    conv_rhs => rw [← h.comap_leftTranslation_inv (Nat.succ_ne_zero n), multiplesDivisor,
      Scheme.IdealSheafData.comap_prod]
    simp only [leftTranslation_inv, ker_comap_leftTranslation_hom, inv_inv, ← pow_succ']
    rw [multiplesDivisor, ← Finset.prod_range_succ, Finset.prod_range_succ']
  -- Cancel the effective Cartier divisor `D`; a section of the separated morphism `E ⟶ S` is
  -- determined by its ideal sheaf, so `[(n + 1 + 1)P] = [P]` gives `(n + 1 + 1)P = P`.
  have hker := ((isRelativeEffectiveCartier_multiplesDivisor P (n + 1)).isEffectiveCartier
    ).mul_left_cancel hcancel
  rw [Scheme.Hom.ker_eq_ker_iff_of_comp_eq_id (f := E.structureMap) _ _ (Over.w _) (Over.w _)]
    at hker
  have hpow : P ^ (n + 1 + 1) = P ^ (0 + 1) := Over.OverMorphism.ext hker
  rwa [pow_succ, zero_add, pow_one, mul_eq_right] at hpow

/-- **A point of exact order `N` is killed by multiplication by `N`**: `[N] P = 0`. Equivalently
(`EllipticCurveGeom.exists_comp_torsionι_iff`), `P` is an `S`-point of the `N`-torsion `E[N]`. -/
theorem IsOfExactOrder.comp_mulBy_eq_one {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfExactOrder P N) : P ≫ E.mulBy N = 1 := by
  rw [EllipticCurveGeom.comp_mulBy, zpow_natCast, h.pow_eq_one]

/-! ### Exact order one -/

/-- **The points of exact order one**: an `S`-point of `E` has exact order one exactly when it is
the zero section. The divisor `[0]` is the trivial subgroup scheme of `E`. -/
@[simp]
theorem isOfExactOrder_one_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} :
    E.IsOfExactOrder P 1 ↔ P = 1 := by
  refine ⟨fun h ↦ by simpa using h.pow_eq_one, ?_⟩
  rintro rfl
  have hD : E.multiplesDivisor 1 1 = E.zero.ker := by
    simp [multiplesDivisor, hom_one_left]
  let i : Over.mk ((E.multiplesDivisor 1 1).subschemeι ≫ E.structureMap) ⟶
      Over.mk E.structureMap := Over.homMk (E.multiplesDivisor 1 1).subschemeι
  have : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (E.multiplesDivisor 1 1).subschemeι)
  have hi : i.left.ker = E.zero.ker := (Scheme.IdealSheafData.ker_subschemeι _).trans hD
  -- The inclusion of `[0]` factors through the zero section, so it is the zero homomorphism.
  have hi₁ : i = 1 := by
    have hle : E.zero.ker ≤ i.left.ker := hi.ge
    have := E.zero.isClosedImmersion_of_comp_eq_id E.zero_comp
    have key : (IsClosedImmersion.lift E.zero i.left hle ≫ E.zero) ≫ E.structureMap ≫ E.zero =
        IsClosedImmersion.lift E.zero i.left hle ≫ E.zero := by
      rw [Category.assoc, zero_comp_structureMap_assoc]
    rw [IsClosedImmersion.lift_fac] at key
    ext1
    rw [hom_one_left]
    -- The structure morphism of the closed subscheme `[0]` is `i.left ≫ E.structureMap`.
    exact key.symm.trans (Category.assoc _ _ _).symm
  -- Every morphism to `E` which is the zero homomorphism vanishes on `[0]`.
  have hone {Z : Over S} (f : Z ⟶ Over.mk E.structureMap) (hf : f = 1) :
      i.left.ker ≤ f.left.ker := by
    rw [hi, hf, hom_one_left]
    exact Scheme.Hom.le_ker_comp _ _
  refine (GroupScheme.exists_grpObj_isMonHom_iff_ker_le i).mpr ⟨hone _ ?_, hone _ ?_, hone _ ?_⟩
  · rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · rw [← lift_fst_comp_snd_comp, ← Hom.mul_def, hi₁, MonObj.comp_one, MonObj.comp_one,
      _root_.one_mul]
  · rw [← Hom.inv_def, hi₁, inv_one]

/-! ### Base change -/

section BaseChange

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- **The divisor `[P] + ⋯ + [NP]` commutes with base change**: for the base change `P'` of an
`S`-point `P` of `E`, the divisor `[P'] + ⋯ + [NP']` on `E'` is the inverse image along `g` of the
divisor `[P] + ⋯ + [NP]` on `E`. -/
theorem multiplesDivisor_pointsPullback (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    E'.multiplesDivisor (pointsPullback hg h0 P) N = (E.multiplesDivisor P N).comap g := by
  simp only [multiplesDivisor, Scheme.IdealSheafData.comap_prod, ← map_pow,
    ker_pointsPullback_left]

/-- **Points of exact order `N` are stable under base change** (Katz–Mazur, §1.4): if an `S`-point
`P` of `E` has exact order `N`, then so does its base change, the `S'`-point `P'` of `E'`. -/
theorem IsOfExactOrder.pointsPullback {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfExactOrder P N) : E'.IsOfExactOrder (pointsPullback hg h0 P) N := by
  -- The divisor cannot be rewritten in place, since the types in `IsOfExactOrder` depend on it.
  have key (D : E'.carrier.IdealSheafData) (hD : D = (E.multiplesDivisor P N).comap g) :
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E'.structureMap)),
        IsMonHom (Over.homMk D.subschemeι :
          Over.mk (D.subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap) :=
    hD ▸ exists_grpObj_isMonHom_comap hg h0 _ h
  exact key _ (multiplesDivisor_pointsPullback hg h0 P N)

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
