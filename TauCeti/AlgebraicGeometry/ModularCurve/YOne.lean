/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder.FiniteEtale
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.TateNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
public import TauCeti.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Retract

/-!
# The fine moduli scheme `Y₁(N)` for `N ≥ 4`

Let `B` be a scheme. The **universal Tate normal form over `B`** (`EllObj.universalTate B`) is the
object of `Ell/B` given by the projective model of `Y² + AXY + BY = X³ + BX²` over
`B × Spec ℤ[A, B][Δ⁻¹]`, with its point `(0, 0)` (`EllObj.universalTatePoint B`). It classifies
elliptic curves with a section `P` such that none of `P`, `2P` and `3P` meets the zero section:
for such a pair `(E/S, P)` there is exactly one arrow `(E/S) ⟶ EllObj.universalTate B` of `Ell/B`
pulling the point `(0, 0)` back to `P` (`EllObj.existsUnique_hom_universalTate`). This is the
universal property `EllipticCurveGeom.existsUnique_tateNormalForm`, read in `Ell/B`.

Now let `N ≥ 4` be invertible on `B`. A naive `[Γ₁(N)]`-structure on `E/S` is a point `P` of
exact order `N` in every fibre, so `P`, `2P` and `3P` miss the zero section, and `(E, P)` is
classified by an arrow to the universal Tate normal form. That arrow is a naive
`[Γ₁(N)]`-structure exactly when its morphism of bases factors through the locus where `(0, 0)`
has naive exact order `N`, the closed subscheme `Y₁(N)` of `B × Spec ℤ[A, B][Δ⁻¹]` on which
`N(0, 0) = 0` and `d(0, 0)` misses the zero section for every proper divisor `d` of `N`
(`EllipticCurveGeom.naiveExactOrderPreimage`). Hence the naive moduli problem `[Γ₁(N)]` is
represented by the restriction `EllObj.yOne B N hN` of the universal Tate normal form to `Y₁(N)`
(`ModuliProblem.gammaOneNaiveRepresentableBy`): `Y₁(N)` is a fine moduli scheme. It is a closed
subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`, so it is affine over `B`
(`EllObj.isAffineHom_yOne_structureMap`), and affine when `B` is, for example for
`B = Spec ℤ[1/N]`. It is also smooth over `B` (`EllObj.smooth_yOne_structureMap`): the point
`(0, 0)` embeds `Y₁(N)` as a retract, over `B`, of the scheme of points of naive exact order `N`
on the universal Tate normal form, which is finite étale over the smooth `B`-scheme
`B × Spec ℤ[A, B][Δ⁻¹]`; the retraction classifies the tautological point.

The hypothesis `N ≥ 4` is what makes the Tate normal form apply: for `N ≤ 3`, a point `P` with
`NP = 0` has one of `P`, `2P` and `3P` equal to the zero section. For `N ≤ 2` the automorphism
`[-1]` fixes every naive `[Γ₁(N)]`-structure, so `[Γ₁(N)]` is not rigid.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllObj.universalTate B`: the universal Tate normal form over `B`, as
  an object of `Ell/B`.
* `TauCeti.AlgebraicGeometry.EllObj.universalTatePoint B`: its point `(0, 0)`.
* `TauCeti.AlgebraicGeometry.EllObj.yOne B N hN`: the restriction of the universal Tate normal
  form to the locus `Y₁(N)` where `(0, 0)` has naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllObj.yOnePoint`: the point `(0, 0)` of the universal elliptic curve
  over `Y₁(N)`, which has naive exact order `N` (`EllObj.isOfNaiveExactOrder_yOnePoint`).
* `TauCeti.AlgebraicGeometry.EllObj.naiveExactOrderOver X hN`,
  `TauCeti.AlgebraicGeometry.EllObj.naiveExactOrderPoint X hN`: the scheme `Z` of points of naive
  exact order `N` of an object `X = (E/S)` of `Ell/B`, as a scheme over `S`, and the tautological
  point of `E_Z`, which has naive exact order `N`
  (`EllObj.isOfNaiveExactOrder_naiveExactOrderPoint`).

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.existsUnique_hom_universalTate`: the universal property of the
  universal Tate normal form in `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveRepresentableBy`: for `N ≥ 4` invertible
  on `B`, the naive moduli problem `[Γ₁(N)]` over `Ell/B` is represented by `EllObj.yOne B N hN`.
* `TauCeti.AlgebraicGeometry.EllObj.isAffineHom_yOne_structureMap`: `Y₁(N)` is affine over `B`.
* `TauCeti.AlgebraicGeometry.EllObj.existsUnique_hom_yOne`: for `N ≥ 4` invertible on `B`, a point
  of naive exact order `N` on an object of `Ell/B` is the pullback of `(0, 0)` along exactly one
  arrow to `EllObj.yOne B N hN`.
* `TauCeti.AlgebraicGeometry.EllObj.smooth_yOne_structureMap`: for `N ≥ 4` invertible on `B`,
  `Y₁(N)` is smooth over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.3 (Tate normal form) and Chapter 4.
* D. Loeffler, *Modular Curves*, lecture notes, 3.3.4 and §3.8.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

/-!
## The modular curve `Y₁(N)` from the universal Tate normal form

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

universe u

section SchemeTheoretic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
  TauCeti.AlgebraicGeometry


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

end SchemeTheoretic

section RelativeModuli

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj WeierstrassCurve UniversalTate


namespace TauCeti.AlgebraicGeometry

namespace EllObj

/-! ### The universal Tate normal form in `Ell/B` -/

variable (B : Scheme.{u})

/-- **The universal Tate normal form over `B`**: the projective model of the universal Tate normal
form `Y² + AXY + BY = X³ + BX²`, pulled back to `B × Spec ℤ[A, B][Δ⁻¹]` along the second
projection, as an object of `Ell/B` through the first projection. -/
noncomputable abbrev universalTate : EllObj B :=
  prodCurve B UniversalTate.curveGeom.{u}

/-- **The point `(0, 0)` of the universal Tate normal form over `B`**: the base change of the point
`(0, 0)` of the universal Tate normal form over `Spec ℤ[A, B][Δ⁻¹]`. -/
noncomputable def universalTatePoint :
    𝟙_ (Over (universalTate B).base) ⟶ Over.mk (universalTate B).curve.structureMap :=
  prodCurvePoint B UniversalTate.pointHom

section Classifying

variable {B} {X : EllObj B}

/-- **The universal property of the universal Tate normal form in `Ell/B`.** Let `X = (E/S)` be an
object of `Ell/B` and `P` an `S`-point of `E` such that none of `P`, `2P` and `3P` meets the zero
section over any point of `S`. Then there is exactly one arrow `k : X ⟶ universalTate B` of `Ell/B`
along which the point `(0, 0)` pulls back to `P`. -/
theorem existsUnique_hom_universalTate (P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)
    (h₁ : ∀ s, P.left s ≠ X.curve.zero s)
    (h₂ : ∀ s, (P.left ≫ (X.curve.mulBy 2).left) s ≠ X.curve.zero s)
    (h₃ : ∀ s, (P.left ≫ (X.curve.mulBy 3).left) s ≠ X.curve.zero s) :
    ∃! k : X ⟶ universalTate B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total (universalTatePoint B) = P := by
  -- arrows into `universalTate B` are the classifying pairs of the Tate normal form
  refine (homProdCurveEquiv X).existsUnique_congr_left.mpr ?_
  obtain ⟨⟨f, g⟩, ⟨hg, h₀, hgP⟩, huniq⟩ :=
    X.curve.existsUnique_tateNormalForm_curveGeom (EllipticCurveGeom.left_comp_structureMap P) h₁
      h₂ h₃
  refine ⟨⟨(f, g), hg, h₀⟩, (pointsPullback_prodCurvePoint_eq_iff _ _ _).mpr ?_,
    fun fg hfg ↦ Subtype.ext (huniq _ ⟨fg.2.1, fg.2.2, ?_⟩)⟩
  · rw [Equiv.apply_symm_apply]
    exact hgP
  · simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg

end Classifying

/-! ### The locus `Y₁(N)` -/

variable (N : ℕ) (hN : ∀ b : B, (N : B.residueField b) ≠ 0)

include hN in
/-- If `N` is invertible on `B`, then it is invertible on the base of the universal Tate normal
form over `B`. -/
theorem natCast_residueField_universalTate_ne_zero (s : (universalTate B).base) :
    (N : (universalTate B).base.residueField s) ≠ 0 :=
  Scheme.Hom.natCast_residueField_ne_zero prod.fst (hN _)

/-- **The fine moduli scheme `Y₁(N)`**, with its universal elliptic curve: when `N` is invertible
on `B`, the restriction of the universal Tate normal form over `B` to the closed subscheme of
`B × Spec ℤ[A, B][Δ⁻¹]` on which the point `(0, 0)` has naive exact order `N`. For `N ≥ 4` it
represents the naive moduli problem `[Γ₁(N)]` (`ModuliProblem.gammaOneNaiveRepresentableBy`). -/
-- Exposed, so that the base of `yOne B N hN` is publicly the locus `naiveExactOrderPreimage`: the
-- statements of `yOneι_base` and `yOne_curve` compare morphisms and curves over the two schemes.
@[expose]
noncomputable def yOne : EllObj B :=
  (universalTate B).baseChangeFunctor.obj (Over.mk (EllipticCurveGeom.naiveExactOrderPreimageι
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B)))

/-- The base of `yOne B N hN` is the locus where `(0, 0)` has naive exact order `N`. -/
@[simp]
theorem yOne_base : (yOne B N hN).base = EllipticCurveGeom.naiveExactOrderPreimage
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B) :=
  (rfl)

/-- The arrow of `Ell/B` exhibiting the universal elliptic curve over `Y₁(N)` as the restriction
of the universal Tate normal form. -/
noncomputable def yOneι : yOne B N hN ⟶ universalTate B :=
  (universalTate B).baseChangeFunctorHom _

/-- The morphism of bases of `yOneι` is the inclusion of the locus where `(0, 0)` has naive exact
order `N`. -/
@[simp]
theorem yOneι_base : (yOneι B N hN).base = EllipticCurveGeom.naiveExactOrderPreimageι
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B) :=
  (baseChangeFunctorHom_base _).trans (Over.mk_hom _)

/-- The structure morphism of `Y₁(N)` is its inclusion in `B × Spec ℤ[A, B][Δ⁻¹]` followed by the
first projection. -/
@[simp]
theorem yOne_structureMap : (yOne B N hN).structureMap = (yOneι B N hN).base ≫ prod.fst := by
  rw [yOneι_base]
  exact (baseChangeFunctor_obj_structureMap (universalTate B) _).trans
    (congrArg (· ≫ prod.fst) (Over.mk_hom _))

/-- The universal elliptic curve over `Y₁(N)` is the base change of the universal Tate normal form
along the inclusion of `Y₁(N)`. -/
theorem yOne_curve : (yOne B N hN).curve = (universalTate B).curve.baseChange
    (EllipticCurveGeom.naiveExactOrderPreimageι (natCast_residueField_universalTate_ne_zero B N hN)
      (universalTatePoint B)) :=
  (rfl)

/-- `Y₁(N)` is a closed subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`. -/
instance isClosedImmersion_yOneι_base : IsClosedImmersion (yOneι B N hN).base := by
  rw [yOneι_base]
  exact EllipticCurveGeom.isClosedImmersion_naiveExactOrderPreimageι _ _ _

/-- **`Y₁(N)` is affine over `B`**: it is a closed subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`. -/
instance isAffineHom_yOne_structureMap : IsAffineHom (yOne B N hN).structureMap := by
  have : IsAffineHom (prod.fst : B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring)) ⟶ B) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance
  rw [yOne_structureMap]
  infer_instance

/-- `Y₁(N)` is affine when `B` is, for example for `B = Spec ℤ[1/N]`. -/
instance isAffine_yOne_base [IsAffine B] : IsAffine (yOne B N hN).base :=
  isAffine_of_isAffineHom (yOne B N hN).structureMap

variable {B N hN}

/-- **The point `(0, 0)` of the universal elliptic curve over `Y₁(N)`**: the base change of the
point `(0, 0)` of the universal Tate normal form along `yOneι`. -/
noncomputable def yOnePoint :
    𝟙_ (Over (yOne B N hN).base) ⟶ Over.mk (yOne B N hN).curve.structureMap :=
  EllipticCurveGeom.pointsPullback (yOneι B N hN).isPullback (yOneι B N hN).zero_total
    (universalTatePoint B)

/-- The point `(0, 0)` of the universal elliptic curve over `Y₁(N)` has naive exact order `N`. -/
theorem isOfNaiveExactOrder_yOnePoint :
    (yOne B N hN).curve.IsOfNaiveExactOrder yOnePoint N := by
  rw [← EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff (yOneι B N hN).isPullback
    (yOneι B N hN).zero_total]
  refine (EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff _ _ ?_).mp
    ⟨𝟙 _, (Category.id_comp _).trans (yOneι_base B N hN).symm⟩
  rw [EllipticCurveGeom.pointsBaseChangeEquiv_left, yOnePoint,
    EllipticCurveGeom.pointsPullback_left_comp]
  simp only [Over.mk_hom]

variable [NeZero N]

-- The naive `[Γ₁(N)]`-structure on an object `X = (E/S)` of `Ell/B` sending `1` to an `S`-point
-- `P` of `E` of naive exact order `N`.
private noncomputable def structureOfPoint {X : EllObj B}
    {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap} (hP : X.curve.IsOfNaiveExactOrder P N) :
    (ModuliProblem.gammaOneNaive B N).obj (op X) :=
  (ModuliProblem.naiveLevelEquiv X).symm
    ⟨(zmodMonoidHomEquiv N _).symm ⟨P, hP.pow_eq_one⟩,
      EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mpr (by
        rw [zmodMonoidHomEquiv_symm_apply_ofAdd_one]
        exact hP)⟩

private theorem naiveLevelEquiv_structureOfPoint {X : EllObj B}
    {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap} (hP : X.curve.IsOfNaiveExactOrder P N) :
    (ModuliProblem.naiveLevelEquiv X (structureOfPoint hP)).1 (.ofAdd 1) = P := by
  rw [structureOfPoint, Equiv.apply_symm_apply, zmodMonoidHomEquiv_symm_apply_ofAdd_one]

-- The universal naive `[Γ₁(N)]`-structure on the universal elliptic curve over `Y₁(N)`: the point
-- `(0, 0)`.
private noncomputable def yOneStructure :
    (ModuliProblem.gammaOneNaive B N).obj (op (yOne B N hN)) :=
  structureOfPoint isOfNaiveExactOrder_yOnePoint

private theorem naiveLevelEquiv_map_yOneStructure {X : EllObj B} (k : X ⟶ yOne B N hN) :
    (ModuliProblem.naiveLevelEquiv X ((ModuliProblem.gammaOneNaive B N).map k.op
        yOneStructure)).1 (.ofAdd 1) =
      EllipticCurveGeom.pointsPullback (k ≫ yOneι B N hN).isPullback
        (k ≫ yOneι B N hN).zero_total (universalTatePoint B) := by
  rw [ModuliProblem.naiveLevelEquiv_map, MonoidHom.comp_apply, yOneStructure,
    naiveLevelEquiv_structureOfPoint]
  exact (EllipticCurveGeom.pointsPullback_comp _ _ _ _ _).symm

-- For `N ≥ 4`, the point `P` of a naive `[Γ₁(N)]`-structure satisfies the three conditions of the
-- Tate normal form: `P`, `2P` and `3P` miss the zero section everywhere.
private theorem tate_conditions (h4 : 4 ≤ N) {X : EllObj B}
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)}
    (hφ : X.curve.IsFiberwiseInjective φ) :
    (∀ s, (φ (.ofAdd 1)).left s ≠ X.curve.zero s) ∧
      (∀ s, ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy 2).left) s ≠ X.curve.zero s) ∧
        ∀ s, ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy 3).left) s ≠ X.curve.zero s := by
  have h := EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mp hφ
  have hn (n : ℕ) (hn : 0 < n) (hnN : n < N) (s : X.base) :
      ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy n).left) s ≠ X.curve.zero s := by
    rw [← Over.comp_left, EllipticCurveGeom.comp_mulBy, zpow_natCast]
    exact h n hn hnN s
  exact ⟨fun s ↦ by simpa using h 1 one_pos (by omega) s, hn 2 two_pos (by omega),
    hn 3 three_pos (by omega)⟩

-- Pulling back the universal naive `[Γ₁(N)]`-structure is a bijection from arrows into `Y₁(N)`.
private theorem bijective_map_yOneStructure (h4 : 4 ≤ N) (X : EllObj B) :
    Function.Bijective fun k : X ⟶ yOne B N hN ↦
      (ModuliProblem.gammaOneNaive B N).map k.op yOneStructure := by
  constructor
  · -- two arrows pulling back the same structure agree after composing with `yOneι`, by the
    -- universal property of the universal Tate normal form, and `yOneι` is a monomorphism on bases
    intro k k' h
    have hp := congrArg (fun α ↦ (ModuliProblem.naiveLevelEquiv X α).1 (.ofAdd 1)) h
    simp only [naiveLevelEquiv_map_yOneStructure] at hp
    obtain ⟨h₁, h₂, h₃⟩ := tate_conditions h4
      (ModuliProblem.naiveLevelEquiv X ((ModuliProblem.gammaOneNaive B N).map k.op
        yOneStructure)).2
    rw [naiveLevelEquiv_map_yOneStructure] at h₁ h₂ h₃
    have hk : k ≫ yOneι B N hN = k' ≫ yOneι B N hN :=
      (existsUnique_hom_universalTate _ h₁ h₂ h₃).unique rfl hp.symm
    refine EllObj.hom_ext_of_comp (yOneι B N hN) hk ?_
    rw [← cancel_mono (yOneι B N hN).base, ← comp_base, hk, comp_base]
  · -- the arrow classifying `(X, P)` lands in `Y₁(N)` because `P` has naive exact order `N`
    intro α
    have hα := (ModuliProblem.naiveLevelEquiv X α).2
    obtain ⟨h₁, h₂, h₃⟩ := tate_conditions h4 hα
    obtain ⟨k₀, hk₀, -⟩ := existsUnique_hom_universalTate _ h₁ h₂ h₃
    obtain ⟨l, hl⟩ := (EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff
      (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B)
      (Z := Over.mk k₀.base)
      (x := EllipticCurveGeom.pointsBaseChangeEquiv k₀.isPullback k₀.zero_total _) (by
        rw [EllipticCurveGeom.pointsBaseChangeEquiv_left, ← hk₀,
          EllipticCurveGeom.pointsPullback_left_comp]
        simp only [Over.mk_hom])).mpr
          ((EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff _ _).mpr
            (EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hα))
    obtain ⟨l', hl'⟩ : ∃ l' : X.base ⟶ (yOne B N hN).base, l' ≫ (yOneι B N hN).base = k₀.base :=
      ⟨l, by rw [yOneι_base]; exact hl.trans (Over.mk_hom _)⟩
    refine ⟨Hom.lift (yOneι B N hN) k₀ l' hl', ?_⟩
    apply (ModuliProblem.naiveLevelEquiv X).injective
    apply Subtype.ext
    apply (zmodMonoidHomEquiv N _).injective
    apply Subtype.ext
    simp only [coe_zmodMonoidHomEquiv_apply]
    rw [naiveLevelEquiv_map_yOneStructure, Hom.lift_comp]
    exact hk₀

end EllObj

namespace ModuliProblem

variable {B : Scheme.{u}} {N : ℕ} (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N)

/-- **`Y₁(N)` is a fine moduli scheme for `N ≥ 4`.** If `N ≥ 4` is invertible on `B`, the naive
moduli problem `[Γ₁(N)]` over `Ell/B` is represented by the universal elliptic curve over `Y₁(N)`
(`EllObj.yOne B N hN`): the naive `[Γ₁(N)]`-structures on an object `X` of `Ell/B` correspond to
the arrows `X ⟶ EllObj.yOne B N hN`, by pulling back the point `(0, 0)`
(`naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv`). -/
noncomputable def gammaOneNaiveRepresentableBy :
    (gammaOneNaive B N).RepresentableBy (EllObj.yOne B N hN) :=
  haveI : NeZero N := ⟨by omega⟩
  { homEquiv := Equiv.ofBijective (fun k ↦ (gammaOneNaive B N).map k.op EllObj.yOneStructure)
      (EllObj.bijective_map_yOneStructure (hN := hN) h4 _)
    homEquiv_comp f k := by
      rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, op_comp, Functor.map_comp_apply] }

/-- The naive `[Γ₁(N)]`-structure corresponding to an arrow `k : X ⟶ EllObj.yOne B N hN` sends `1`
to the base change of the point `(0, 0)` of the universal Tate normal form along `k`. -/
theorem naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv {X : EllObj B}
    (k : X ⟶ EllObj.yOne B N hN) :
    (naiveLevelEquiv X ((gammaOneNaiveRepresentableBy hN h4).homEquiv k)).1 (.ofAdd 1) =
      EllipticCurveGeom.pointsPullback (k ≫ EllObj.yOneι B N hN).isPullback
        (k ≫ EllObj.yOneι B N hN).zero_total (EllObj.universalTatePoint B) :=
  haveI : NeZero N := ⟨by omega⟩
  EllObj.naiveLevelEquiv_map_yOneStructure k

/-- The universal naive `[Γ₁(N)]`-structure on `EllObj.yOne B N hN`, attached to its identity
arrow, sends `1` to the point `(0, 0)` of the universal elliptic curve over `Y₁(N)`. -/
theorem naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv_id :
    (naiveLevelEquiv _ ((gammaOneNaiveRepresentableBy hN h4).homEquiv (𝟙 _))).1 (.ofAdd 1) =
      EllObj.yOnePoint := by
  have : NeZero N := ⟨by omega⟩
  rw [gammaOneNaiveRepresentableBy, Equiv.ofBijective_apply, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, EllObj.yOneStructure, EllObj.naiveLevelEquiv_structureOfPoint]

end ModuliProblem

namespace EllObj

/-! ### Smoothness of `Y₁(N)` -/

variable {B : Scheme.{u}} {N : ℕ} {hN : ∀ b : B, (N : B.residueField b) ≠ 0}

/-- **The universal property of `Y₁(N)` in terms of points.** Let `N ≥ 4` be invertible on `B`,
let `X = (E/S)` be an object of `Ell/B`, and let `P` be an `S`-point of `E` of naive exact order
`N`. Then there is exactly one arrow `k : X ⟶ EllObj.yOne B N hN` of `Ell/B` along which the point
`(0, 0)` of the universal Tate normal form pulls back to `P`. -/
theorem existsUnique_hom_yOne (h4 : 4 ≤ N) {X : EllObj B}
    {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap} (hP : X.curve.IsOfNaiveExactOrder P N) :
    ∃! k : X ⟶ yOne B N hN, EllipticCurveGeom.pointsPullback (k ≫ yOneι B N hN).isPullback
      (k ≫ yOneι B N hN).zero_total (universalTatePoint B) = P := by
  have : NeZero N := ⟨by omega⟩
  let R := ModuliProblem.gammaOneNaiveRepresentableBy hN h4
  have hα := naiveLevelEquiv_structureOfPoint hP
  refine ⟨R.homEquiv.symm (structureOfPoint hP), ?_, fun k hk ↦ R.homEquiv.injective ?_⟩
  · beta_reduce
    rw [← ModuliProblem.naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv hN h4,
      Equiv.apply_symm_apply, hα]
  · -- a naive `[Γ₁(N)]`-structure is determined by the image of `1`
    rw [Equiv.apply_symm_apply]
    refine (ModuliProblem.naiveLevelEquiv X).injective (Subtype.ext ?_)
    refine (zmodMonoidHomEquiv N _).injective (Subtype.ext ?_)
    rw [coe_zmodMonoidHomEquiv_apply, coe_zmodMonoidHomEquiv_apply,
      ModuliProblem.naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv, hk, hα]

/-- The scheme `Z` of points of naive exact order `N` of an object `X = (E/S)` of `Ell/B`, as a
scheme over `S`: the open subscheme `naiveExactOrderOpens` of the `N`-torsion `E[N]`. It is finite
étale over `S`. -/
noncomputable abbrev naiveExactOrderOver (X : EllObj B)
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) : Over X.base :=
  Over.mk ((X.curve.naiveExactOrderOpens hN).ι ≫ (X.curve.torsion N).X.hom)

/-- The tautological point of the scheme `Z` of points of naive exact order `N` of an object
`X = (E/S)` of `Ell/B`: the `Z`-point of the base change `E_Z` given by the inclusion
`Z ⟶ E[N] ⟶ E`. -/
noncomputable def naiveExactOrderPoint (X : EllObj B)
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) :
    𝟙_ (Over (X.baseChangeFunctor.obj (X.naiveExactOrderOver hN)).base) ⟶
      Over.mk (X.baseChangeFunctor.obj (X.naiveExactOrderOver hN)).curve.structureMap :=
  (X.baseChangePointsEquiv _).symm
    ((X.curve.naiveExactOrderRepresentableBy hN).homEquiv (𝟙 _)).1

/-- The tautological point of the scheme `Z` of points of naive exact order `N`, followed by the
projection `E_Z ⟶ E`, is the inclusion `Z ⟶ E[N] ⟶ E`. -/
theorem naiveExactOrderPoint_left_comp_total (X : EllObj B)
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) :
    (X.naiveExactOrderPoint hN).left ≫ (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).total =
      (X.curve.naiveExactOrderOpens hN).ι ≫ (X.curve.torsionι N).left := by
  have h := congrArg Over.Hom.left ((X.baseChangePointsEquiv _).apply_symm_apply
    ((X.curve.naiveExactOrderRepresentableBy hN).homEquiv (𝟙 (X.naiveExactOrderOver hN))).1)
  rw [baseChangePointsEquiv_apply_left] at h
  refine h.trans ?_
  rw [EllipticCurveGeom.coe_naiveExactOrderRepresentableBy_homEquiv]
  simp

/-- The tautological point of the scheme of points of naive exact order `N` has naive exact
order `N`. -/
theorem isOfNaiveExactOrder_naiveExactOrderPoint (X : EllObj B)
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) :
    (X.baseChangeFunctor.obj (X.naiveExactOrderOver hN)).curve.IsOfNaiveExactOrder
      (X.naiveExactOrderPoint hN) N := by
  let x := (X.curve.naiveExactOrderRepresentableBy hN).homEquiv (𝟙 (X.naiveExactOrderOver hN))
  refine (EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff
    (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).isPullback
    (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).zero_total).mp ?_
  -- the base of `X.baseChangeFunctorHom _` is only propositionally the structure morphism of `Z`;
  -- its source is only definitionally `Z`, so `simp` cannot use `Category.id_comp` on `𝟙 _ ≫ _`
  let e : Over.mk (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).base ⟶
      X.naiveExactOrderOver hN :=
    Over.homMk (𝟙 _) (by
      simp only [Over.mk_hom, baseChangeFunctorHom_base]
      exact Category.id_comp _)
  have key : EllipticCurveGeom.pointsBaseChangeEquiv
      (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).isPullback
      (X.baseChangeFunctorHom (X.naiveExactOrderOver hN)).zero_total (X.naiveExactOrderPoint hN) =
        e ≫ x.1 := by
    ext1
    rw [EllipticCurveGeom.pointsBaseChangeEquiv_left, naiveExactOrderPoint_left_comp_total,
      EllipticCurveGeom.coe_naiveExactOrderRepresentableBy_homEquiv]
    simp only [e, Over.comp_left, EllipticCurveGeom.naiveExactOrderι_left]
    exact (Category.id_comp _).symm
  rw [key]
  exact (EllipticCurveGeom.mem_naiveExactOrderSubfunctor_obj.mp x.2).comp _

variable (B) in
/-- The base `B × Spec ℤ[A, B][Δ⁻¹]` of the universal Tate normal form over `B` is smooth over
`B`. -/
instance smooth_universalTate_structureMap : Smooth (universalTate B).structureMap :=
  MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance

variable (B N hN) in
/-- **`Y₁(N)` is smooth over `B`.** For `N ≥ 4` invertible on `B`, the structure morphism of the
fine moduli scheme `Y₁(N)` to `B` is smooth; for example `Y₁(N)` is smooth over `ℤ[1/N]`. -/
theorem smooth_yOne_structureMap (h4 : 4 ≤ N) : Smooth (yOne B N hN).structureMap := by
  -- `Y₁(N)` is a retract over `B` of the scheme `Z` of points of naive exact order `N` on the
  -- universal Tate normal form, which is finite étale over the smooth `B`-scheme
  -- `B × Spec ℤ[A, B][Δ⁻¹]`: the point `(0, 0)` gives a section `Y₁(N) ⟶ Z`, and the morphism
  -- `Z ⟶ Y₁(N)` classifying the tautological point `P` of `Z` retracts it
  have hN' := natCast_residueField_universalTate_ne_zero B N hN
  have hP := (universalTate B).isOfNaiveExactOrder_naiveExactOrderPoint hN'
  have hPx := (universalTate B).naiveExactOrderPoint_left_comp_total hN'
  set T := (universalTate B).naiveExactOrderOver hN'
  set P := (universalTate B).naiveExactOrderPoint hN'
  have hT : Smooth T.hom := inferInstanceAs (Smooth (_ ≫ _))
  -- the retraction `r : Z ⟶ Y₁(N)` is the base of the arrow `k` classifying `P`
  obtain ⟨k, hk, -⟩ := existsUnique_hom_yOne (hN := hN) h4 hP
  -- the section `i : Y₁(N) ⟶ Z` given by the point `(0, 0)`, and the arrow `j` of `Ell/B` over it
  let i := EllipticCurveGeom.naiveExactOrderPreimagePoint hN' (universalTatePoint B)
  have hsq := EllipticCurveGeom.isPullback_naiveExactOrderPreimage hN' (universalTatePoint B)
  have hi : i ≫ T.hom = EllipticCurveGeom.naiveExactOrderPreimageι hN' (universalTatePoint B) := by
    have h := hsq.w =≫ (universalTate B).curve.structureMap
    rw [Category.assoc, Category.assoc, EllipticCurveGeom.left_comp_structureMap,
      Category.comp_id] at h
    simpa [T, ← EllipticCurveGeom.torsionι_left_structureMap] using h.symm
  let j : yOne B N hN ⟶ (universalTate B).baseChangeFunctor.obj T :=
    (universalTate B).baseChangeFunctor.map (Over.homMk i hi)
  have hjι : j ≫ (universalTate B).baseChangeFunctorHom T = yOneι B N hN :=
    baseChangeFunctor_map_baseChangeFunctorHom _
  have hjb : j.base = i := baseChangeFunctor_map_base _ _
  -- `P` pulls back along `j` to the point `(0, 0)` of the universal curve over `Y₁(N)`
  have hj : yOnePoint.left ≫ j.total = j.base ≫ P.left := by
    refine ((universalTate B).baseChangeFunctorHom T).isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, ← comp_total, hjι, yOnePoint, EllipticCurveGeom.pointsPullback_left_comp,
        Category.assoc, hPx, hjb, yOneι_base]
      exact hsq.w
    · simp [T]
  -- so `j ≫ k` and the identity both classify `(0, 0)`, and agree
  have hjk : j ≫ k = 𝟙 _ := by
    refine (existsUnique_hom_yOne (hN := hN) h4 isOfNaiveExactOrder_yOnePoint).unique ?_ ?_
    · have hk' := (EllipticCurveGeom.eq_pointsPullback_iff _ _).mp hk.symm
      rw [comp_total, comp_base] at hk'
      symm
      rw [EllipticCurveGeom.eq_pointsPullback_iff, comp_total, comp_total, comp_base, comp_base,
        Category.assoc, reassoc_of% hj, hk']
      simp only [Category.assoc]
    · symm
      rw [EllipticCurveGeom.eq_pointsPullback_iff, Category.id_comp]
      exact EllipticCurveGeom.pointsPullback_left_comp _ _ _
  refine Smooth.of_retract_of_comp_eq _ (T.hom ≫ (universalTate B).structureMap) i k.base ?_ ?_
  · rw [← hjb]
    exact (comp_base j k).symm.trans ((congrArg Hom.base hjk).trans (id_base _))
  · exact k.base_structureMap.trans (baseChangeFunctor_obj_structureMap _ _)

end EllObj

end TauCeti.AlgebraicGeometry

end RelativeModuli
