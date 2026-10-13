/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.TateNormalForm

/-!
# The modular curve `Y₁(N)` from the universal Tate normal form

Let `T = Spec ℤ[A, B][Δ⁻¹]` be the base of the universal Tate normal form
`Y² + AXY + BY = X³ + BX²`, with its point `(0, 0)`. An elliptic curve `E` over a scheme `S` with
an `S`-point `P` such that none of `P`, `2P`, `3P` meets the zero section is the pullback of the
universal Tate normal form with its point `(0, 0)` along a unique morphism `S ⟶ T`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_tateNormalForm`). This file cuts the
modular curve `Y₁(N)` out of `T`:

* the **`N`-torsion locus** `TauCeti.AlgebraicGeometry.UniversalTate.torsionLocus N` is the
  closed subscheme of `T` on which `N • (0, 0) = 0`, the equalizer of `N • (0, 0)` and the zero
  section. A morphism `t : S ⟶ T` factors through it exactly when the pullback of `N • (0, 0)`
  along `t` is the pullback of the zero section, an equality of morphisms rather than a condition
  at points (`TauCeti.AlgebraicGeometry.UniversalTate.exists_comp_torsionLocusι_eq_iff`);
* `TauCeti.AlgebraicGeometry.UniversalTate.yOne N` is the open subscheme of the `N`-torsion locus
  at whose points none of `(0, 0), 2 • (0, 0), …, (N - 1) • (0, 0)` meets the zero section
  (`TauCeti.AlgebraicGeometry.UniversalTate.exists_comp_yOneι_eq_iff`).

The main result is that, for `N ≥ 4`, `Y₁(N)` is the fine moduli scheme of elliptic curves with an
`S`-point `P` of exact order `N` in every fibre: `N • P = 0` and none of `P, 2P, …, (N - 1)P`
meets the zero section. Such a pair `(E, P)` is the pullback of the universal Tate normal form with
its point `(0, 0)` along a unique morphism `S ⟶ Y₁(N)`, by a unique cartesian morphism carrying
the zero section to the zero section and `P` to `(0, 0)`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`); conversely, every such pullback
along a morphism `S ⟶ Y₁(N)` has a point of exact order `N` in every fibre
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_yOne_iff`). The bound `N ≥ 4` makes `P`,
`2P` and `3P` miss the zero section, so that the Tate normal form applies. A point of exact order
`N` in every fibre is the same as a homomorphism `ℤ/Nℤ →* E(S)` injective on every fibre, a naive
`[Γ₁(N)]`-structure in the sense of Katz and Mazur
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne_of_isFiberwiseInjective`).

No hypothesis on `S` or on `N` beyond `N ≥ 4` is needed: `S` may be nonreduced, and `N` need not
be invertible on `S`. The condition `N • P = 0` is scheme-theoretic, while the exact-order
condition is a condition at the points of `S`.

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalTate.torsionLocus n`,
  `TauCeti.AlgebraicGeometry.UniversalTate.torsionLocusι n`: the closed subscheme of
  `Spec ℤ[A, B][Δ⁻¹]` on which `n • (0, 0) = 0`, with its inclusion.
* `TauCeti.AlgebraicGeometry.UniversalTate.exactOrderOpens N`: the open subset of
  `Spec ℤ[A, B][Δ⁻¹]` at whose points none of the multiples `k • (0, 0)`, `0 < k < N`, meets the
  zero section.
* `TauCeti.AlgebraicGeometry.UniversalTate.yOne N`,
  `TauCeti.AlgebraicGeometry.UniversalTate.yOneι N`: the modular curve `Y₁(N)`, the open subscheme
  `yOneOpens N` of the `N`-torsion locus lying over `exactOrderOpens N`, with its immersion into
  `Spec ℤ[A, B][Δ⁻¹]`.

## Main results

* `TauCeti.AlgebraicGeometry.UniversalTate.exists_comp_torsionLocusι_eq_iff`: the morphisms to
  the base factoring through the `n`-torsion locus are those along which `n • (0, 0)` vanishes.
* `TauCeti.AlgebraicGeometry.UniversalTate.exists_comp_yOneι_eq_iff`: the morphisms to the base
  factoring through `Y₁(N)` are those along which `N • (0, 0)` vanishes and no `k • (0, 0)`,
  `0 < k < N`, meets the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`: for `N ≥ 4`, `Y₁(N)` is a fine
  moduli scheme for points of exact order `N` in every fibre.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_yOne_iff`: the pullback of `(0, 0)` along a
  morphism to `Y₁(N)` has exact order `N` in every fibre, and these are all such points.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne_of_isFiberwiseInjective`: the
  same for naive `[Γ₁(N)]`-structures.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §2.2 and Chapter 4.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
* D. Loeffler, *Modular curves*, lecture notes, §3.3.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
  TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.UniversalTate

open WeierstrassCurve

/-! ### The torsion locus -/

/-- The **`n`-torsion locus** of the universal Tate normal form: the closed subscheme of
`Spec ℤ[A, B][Δ⁻¹]` on which `n • (0, 0)` is the zero section, the equalizer of `n • (0, 0)` and
the zero section. -/
noncomputable def torsionLocus (n : ℕ) : Scheme.{u} :=
  (equalizer (pointHom.{u} ^ n) 1).left

/-- The inclusion of the `n`-torsion locus into `Spec ℤ[A, B][Δ⁻¹]`. -/
noncomputable def torsionLocusι (n : ℕ) :
    torsionLocus.{u} n ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  (equalizer.ι (pointHom.{u} ^ n) 1).left

/-- The `n`-torsion locus is a closed subscheme, since the universal Tate normal form is separated
over its base. -/
instance isClosedImmersion_torsionLocusι (n : ℕ) : IsClosedImmersion (torsionLocusι.{u} n) := by
  -- instance search does not unfold `(Over.mk E.structureMap).hom` to `E.structureMap`
  have : IsSeparated (Over.mk curveGeom.{u}.structureMap).hom :=
    inferInstanceAs (IsSeparated curveGeom.{u}.structureMap)
  exact isClosedImmersion_equalizer_ι_left _ _

/-- On the `n`-torsion locus, `n • (0, 0)` is the zero section. -/
@[reassoc]
theorem torsionLocusι_comp_pointHom_pow_left (n : ℕ) :
    torsionLocusι.{u} n ≫ (pointHom ^ n).left = torsionLocusι n ≫ curveGeom.zero := by
  have := congrArg Over.Hom.left (equalizer.condition (pointHom.{u} ^ n) 1)
  simp only [Over.comp_left, EllipticCurveGeom.hom_one_left, Over.tensorUnit_hom] at this
  exact this

/-- **The universal property of the `n`-torsion locus.** A morphism `t : S ⟶ Spec ℤ[A, B][Δ⁻¹]`
factors through the `n`-torsion locus exactly when the pullback of `n • (0, 0)` along `t` is the
pullback of the zero section. The factorization is unique, as `torsionLocusι n` is a closed
immersion. -/
theorem exists_comp_torsionLocusι_eq_iff {S : Scheme.{u}}
    (t : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) (n : ℕ) :
    (∃ h : S ⟶ torsionLocus.{u} n, h ≫ torsionLocusι n = t) ↔
      t ≫ (pointHom ^ n).left = t ≫ curveGeom.zero := by
  refine ⟨fun ⟨h, ht⟩ ↦ ht ▸ by simp [torsionLocusι_comp_pointHom_pow_left], fun ht ↦ ?_⟩
  let t' : Over.mk t ⟶ 𝟙_ (Over (Spec (.of (ULift.{u} UniversalTate.Ring)))) :=
    Over.homMk t (by simp)
  refine ⟨(equalizer.lift t' ?_).left, congrArg Over.Hom.left (equalizer.lift_ι t' _)⟩
  ext1
  simpa [t', EllipticCurveGeom.hom_one_left] using ht

/-! ### `Y₁(N)` -/

/-- The open subset of `Spec ℤ[A, B][Δ⁻¹]` at whose points none of the multiples
`(0, 0), 2 • (0, 0), …, (N - 1) • (0, 0)` of the universal point meets the zero section. -/
noncomputable def exactOrderOpens (N : ℕ) :
    (Spec (.of (ULift.{u} UniversalTate.Ring))).Opens where
  carrier := {t | ∀ k : ℕ, 0 < k → k < N → (pointHom ^ k).left t ≠ curveGeom.zero t}
  is_open' := by
    have : {t : Spec (.of (ULift.{u} UniversalTate.Ring)) | ∀ k : ℕ, 0 < k → k < N →
        (pointHom ^ k).left t ≠ curveGeom.zero t} =
        ⋂ k ∈ Finset.Ioo 0 N, {t | (pointHom ^ k).left t = curveGeom.zero t}ᶜ := by
      ext t
      simp [and_imp]
    rw [this]
    exact isOpen_biInter_finset fun k _ ↦
      (curveGeom.isClosed_setOf_left_apply_eq_zero (pointHom ^ k)).isOpen_compl

/-- The defining property of `exactOrderOpens N`. -/
@[simp]
theorem mem_exactOrderOpens_iff {N : ℕ} {t : Spec (.of (ULift.{u} UniversalTate.Ring))} :
    t ∈ exactOrderOpens N ↔ ∀ k : ℕ, 0 < k → k < N → (pointHom ^ k).left t ≠ curveGeom.zero t :=
  Iff.rfl

/-- The open subset of the `N`-torsion locus lying over `exactOrderOpens N`. -/
noncomputable def yOneOpens (N : ℕ) : (torsionLocus.{u} N).Opens :=
  torsionLocusι N ⁻¹ᵁ exactOrderOpens N

/-- The defining property of `yOneOpens N`. -/
@[simp]
theorem mem_yOneOpens_iff {N : ℕ} {z : torsionLocus.{u} N} :
    z ∈ yOneOpens N ↔ torsionLocusι N z ∈ exactOrderOpens N :=
  Iff.rfl

/-- **The modular curve `Y₁(N)`**: the open subscheme of the `N`-torsion locus of the universal
Tate normal form lying over `exactOrderOpens N`, on which `N • (0, 0) = 0` and none of
`(0, 0), 2 • (0, 0), …, (N - 1) • (0, 0)` meets the zero section. For `N ≥ 4` it is the fine moduli
scheme of elliptic curves with a point of exact order `N` in every fibre
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`). -/
noncomputable abbrev yOne (N : ℕ) : Scheme.{u} :=
  (yOneOpens.{u} N).toScheme

/-- The morphism `Y₁(N) ⟶ Spec ℤ[A, B][Δ⁻¹]`: the inclusion of an open subscheme of the
`N`-torsion locus followed by the inclusion of that closed subscheme. -/
noncomputable def yOneι (N : ℕ) : yOne.{u} N ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  (yOneOpens.{u} N).ι ≫ torsionLocusι N

/-- `yOneι N` is the inclusion of `yOneOpens N` followed by that of the `N`-torsion locus. -/
theorem yOneι_def (N : ℕ) : yOneι.{u} N = (yOneOpens.{u} N).ι ≫ torsionLocusι N :=
  (rfl)

/-- `Y₁(N)` is a locally closed subscheme of `Spec ℤ[A, B][Δ⁻¹]`. -/
instance isImmersion_yOneι (N : ℕ) : IsImmersion (yOneι.{u} N) := by
  rw [yOneι_def]
  infer_instance

/-- **The universal property of `Y₁(N)`.** A morphism `t : S ⟶ Spec ℤ[A, B][Δ⁻¹]` factors
through `Y₁(N)` exactly when the pullback of `N • (0, 0)` along `t` is the pullback of the zero
section and `t` lands in `exactOrderOpens N`, that is, none of the multiples `k • (0, 0)`,
`0 < k < N`, meets the zero section at a point of the image of `t`. The factorization is unique,
as `yOneι N` is an immersion. -/
theorem exists_comp_yOneι_eq_iff {S : Scheme.{u}}
    (t : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) (N : ℕ) :
    (∃ h : S ⟶ yOne.{u} N, h ≫ yOneι N = t) ↔
      t ≫ (pointHom ^ N).left = t ≫ curveGeom.zero ∧ ∀ s, t s ∈ exactOrderOpens N := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨(exists_comp_torsionLocusι_eq_iff _ _).mp ⟨h ≫ (yOneOpens N).ι, by
      rw [yOneι_def, Category.assoc]⟩, fun s ↦ ?_⟩
    have : (yOneOpens N).ι (h s) ∈ yOneOpens N := (h s).2
    simpa [yOneι_def] using this
  · rintro ⟨hN, ht⟩
    obtain ⟨h, rfl⟩ := (exists_comp_torsionLocusι_eq_iff _ _).mpr hN
    refine ⟨IsOpenImmersion.lift (yOneOpens N).ι h ?_, by
      rw [yOneι_def, ← Category.assoc, IsOpenImmersion.lift_fac]⟩
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht s

end TauCeti.AlgebraicGeometry.UniversalTate

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

open WeierstrassCurve UniversalTate

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}

/-! ### Classifying pairs -/

variable {t : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
  {g : E.carrier ⟶ curveGeom.{u}.carrier}
  (hg : IsPullback g E.structureMap curveGeom.structureMap t) (h₀ : E.zero ≫ g = t ≫ curveGeom.zero)
  (hP : P.left ≫ g = t ≫ pointHom.left)

include hg h₀ hP in
-- Along a classifying pair, `P` is the pullback of the universal point.
private theorem eq_pointsPullback_pointHom : P = pointsPullback hg h₀ pointHom :=
  (eq_pointsPullback_iff hg h₀).mpr hP

include hg h₀ hP in
-- Along a classifying pair over `t`, `n • P = 0` exactly when `n • (0, 0)` vanishes along `t`.
private theorem pow_eq_one_iff_of_isTate (n : ℕ) :
    P ^ n = 1 ↔ t ≫ (pointHom ^ n).left = t ≫ curveGeom.zero := by
  rw [eq_pointsPullback_pointHom hg h₀ hP, ← map_pow]
  simpa [Over.OverMorphism.ext_iff, hom_one_left] using
    comp_pointsPullback_left_eq_comp_zero_iff hg h₀ (pointHom ^ n) (𝟙 S)

include hg h₀ hP in
-- Along a classifying pair over `t`, `n • P` meets the zero section at a point `s` of `S` exactly
-- when `n • (0, 0)` meets it at `t s`.
private theorem pow_left_apply_eq_zero_iff_of_isTate (n : ℕ) (s : S) :
    (P ^ n).left s = E.zero s ↔ (pointHom ^ n).left (t s) = curveGeom.zero (t s) := by
  rw [eq_pointsPullback_pointHom hg h₀ hP, ← map_pow]
  exact pointsPullback_left_apply_eq_zero_iff hg h₀ (pointHom ^ n) s

/-! ### The moduli property of `Y₁(N)` -/

/-- **`Y₁(N)` is a fine moduli scheme for points of exact order `N`.** Let `N ≥ 4` and let `P` be
an `S`-point of an elliptic curve `E` over `S` with `N • P = 0` such that none of
`P, 2P, …, (N - 1)P` meets the zero section at any point of `S`. Then there are a unique morphism
`f : S ⟶ Y₁(N)` and a unique morphism `g` from `E` to the universal Tate normal form exhibiting
`E` as its pullback along `f`, carrying the zero section to the zero section and `P` to the point
`(0, 0)`. -/
theorem existsUnique_yOne {N : ℕ} (hN : 4 ≤ N) (hPN : P ^ N = 1)
    (hPk : ∀ k : ℕ, 0 < k → k < N → ∀ s, (P ^ k).left s ≠ E.zero s) :
    ∃! fg : (S ⟶ yOne.{u} N) × (E.carrier ⟶ curveGeom.{u}.carrier),
      IsPullback fg.2 E.structureMap curveGeom.structureMap (fg.1 ≫ yOneι N) ∧
        E.zero ≫ fg.2 = (fg.1 ≫ yOneι N) ≫ curveGeom.zero ∧
        P.left ≫ fg.2 = (fg.1 ≫ yOneι N) ≫ pointHom.left := by
  -- `P`, `2P` and `3P` miss the zero section, so `(E, P)` has a Tate normal form
  have hmul (k : ℕ) : P.left ≫ (E.mulBy k).left = (P ^ k).left := by
    rw [← Over.comp_left, comp_mulBy, zpow_natCast]
  have h₁ : ∀ s, P.left s ≠ E.zero s := by simpa using hPk 1 (by omega) (by omega)
  have h₂ : ∀ s, (P.left ≫ (E.mulBy 2).left) s ≠ E.zero s := by
    simpa only [← hmul, Nat.cast_ofNat] using hPk 2 (by omega) (by omega)
  have h₃ : ∀ s, (P.left ≫ (E.mulBy 3).left) s ≠ E.zero s := by
    simpa only [← hmul, Nat.cast_ofNat] using hPk 3 (by omega) (by omega)
  obtain ⟨⟨f, g⟩, ⟨hg, h₀, hgP⟩, huniq⟩ :=
    E.existsUnique_tateNormalForm_curveGeom (left_comp_structureMap P) h₁ h₂ h₃
  -- the classifying morphism factors through `Y₁(N)`
  obtain ⟨h, rfl⟩ := (exists_comp_yOneι_eq_iff f N).mpr
    ⟨(pow_eq_one_iff_of_isTate hg h₀ hgP N).mp hPN, fun s k hk hkN hs ↦
      hPk k hk hkN s ((pow_left_apply_eq_zero_iff_of_isTate hg h₀ hgP k s).mpr hs)⟩
  refine ⟨(h, g), ⟨hg, h₀, hgP⟩, ?_⟩
  -- a second classifying pair through `Y₁(N)` is a second Tate normal form
  rintro ⟨h', g'⟩ hfg'
  have := huniq (h' ≫ yOneι N, g') hfg'
  simp only [Prod.mk.injEq] at this
  exact Prod.ext ((cancel_mono (yOneι N)).mp this.1) this.2

/-- **The points classified by `Y₁(N)`.** For `N ≥ 4`, an `S`-point `P` of an elliptic curve `E`
over `S` is the pullback of the point `(0, 0)` of the universal Tate normal form along some
morphism `S ⟶ Y₁(N)`, by a cartesian morphism carrying the zero section to the zero section,
exactly when `N • P = 0` and none of `P, 2P, …, (N - 1)P` meets the zero section at any point
of `S`. -/
theorem exists_yOne_iff {N : ℕ} (hN : 4 ≤ N) :
    (∃ (f : S ⟶ yOne.{u} N) (g : E.carrier ⟶ curveGeom.{u}.carrier),
      IsPullback g E.structureMap curveGeom.structureMap (f ≫ yOneι N) ∧
        E.zero ≫ g = (f ≫ yOneι N) ≫ curveGeom.zero ∧
        P.left ≫ g = (f ≫ yOneι N) ≫ pointHom.left) ↔
      P ^ N = 1 ∧ ∀ k : ℕ, 0 < k → k < N → ∀ s, (P ^ k).left s ≠ E.zero s := by
  refine ⟨fun ⟨f, g, hg, h₀, hgP⟩ ↦ ?_, fun ⟨hPN, hPk⟩ ↦
    let ⟨⟨f, g⟩, h, _⟩ := existsUnique_yOne hN hPN hPk; ⟨f, g, h⟩⟩
  -- the classifying morphism `f ≫ yOneι N` satisfies the conditions defining `Y₁(N)`
  obtain ⟨hN', hk⟩ := (exists_comp_yOneι_eq_iff (f ≫ yOneι N) N).mp ⟨f, rfl⟩
  exact ⟨(pow_eq_one_iff_of_isTate hg h₀ hgP N).mpr hN', fun k hk' hkN s hs ↦
    hk s k hk' hkN ((pow_left_apply_eq_zero_iff_of_isTate hg h₀ hgP k s).mp hs)⟩

/-- **`Y₁(N)` classifies naive `[Γ₁(N)]`-structures.** For `N ≥ 4`, let `φ : ℤ/Nℤ →* E(S)` be a
homomorphism injective on every fibre of `E` over `S`. Then there are a unique morphism
`f : S ⟶ Y₁(N)` and a unique morphism `g` from `E` to the universal Tate normal form exhibiting
`E` as its pullback along `f`, carrying the zero section to the zero section and `φ 1` to the point
`(0, 0)`. -/
theorem existsUnique_yOne_of_isFiberwiseInjective {N : ℕ} (hN : 4 ≤ N)
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (hφ : E.IsFiberwiseInjective φ) :
    ∃! fg : (S ⟶ yOne.{u} N) × (E.carrier ⟶ curveGeom.{u}.carrier),
      IsPullback fg.2 E.structureMap curveGeom.structureMap (fg.1 ≫ yOneι N) ∧
        E.zero ≫ fg.2 = (fg.1 ≫ yOneι N) ≫ curveGeom.zero ∧
        (φ (.ofAdd 1)).left ≫ fg.2 = (fg.1 ≫ yOneι N) ≫ pointHom.left := by
  have : NeZero N := ⟨by omega⟩
  refine existsUnique_yOne hN ?_ (isFiberwiseInjective_zmod_iff.mp hφ)
  rw [← map_pow, ← ofAdd_nsmul]
  simp

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
