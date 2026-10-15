/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.ModularCurve.HomLevel
public import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Rigidity
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus

/-!
# The naive moduli problems `[Γ₁(N)]` and `[Γ(N)]`

Let `A` be a group. A *naive `A`-structure* on an elliptic curve `E` over a scheme `S` is a
homomorphism `φ : A →* E(S)` to the group of `S`-points of `E` which is injective on every fibre
of `E` over `S` (`EllipticCurveGeom.IsFiberwiseInjective`): for `a ≠ 1` the section `φ a` misses
the zero section everywhere. The condition is pointwise, so it is stable under base change
(`EllipticCurveGeom.IsFiberwiseInjective.pointsPullback`), and the naive `A`-structures form a
moduli problem over `Ell/B` (`ModuliProblem.naiveLevel`), an instance of `ModuliProblem.homLevel`.

For `A = ℤ/Nℤ` this is the naive moduli problem `[Γ₁(N)]` (`ModuliProblem.gammaOneNaive`): for
`N ≠ 0`, a naive `[Γ₁(N)]`-structure is an `S`-point `P` of `E[N]` none of whose multiples
`P, …, (N - 1)P` meets the zero section (`ModuliProblem.gammaOneNaiveEquiv`).
For `A = (ℤ/Nℤ)²` it is the naive moduli problem `[Γ(N)]` (`ModuliProblem.gammaNaive`): a pair
`(P, Q)` of `S`-points of `E[N]` none of whose combinations `aP + bQ` with `(a, b) ≠ 0` meets the
zero section (`ModuliProblem.gammaNaiveEquiv`), which, when `N` is invertible on `S`, is a basis of
the `N`-torsion in every geometric fibre
(`EllipticCurveGeom.isFiberwiseInjective_iff_range_eq_ker`). Restriction along an injective
homomorphism `A' →* A` is a morphism of moduli problems (`ModuliProblem.naiveLevelMap`); keeping
the first component `P` of a pair `(P, Q)`, the first basis vector when `N` is invertible, gives
`[Γ(N)] ⟶ [Γ₁(N)]` (`ModuliProblem.gammaNaiveToGammaOneNaive`).

The automorphisms of `A` act on the right on naive `A`-structures, `φ ↦ φ ∘ σ`
(`ModuliProblem.naiveLevelAction`), and the action is free over a nonempty base because naive
structures are injective. Through `GL₂(ℤ/Nℤ) ≃* Aut((ℤ/Nℤ)²)` (`TauCeti.zmodProdMulAutEquiv`)
this is the right action of `GL₂(ℤ/Nℤ)` on `[Γ(N)]` (`ModuliProblem.gammaNaiveAction`) in the
row-vector convention of Katz and Mazur: `g = !![a, b; c, d]` sends `(P, Q)` to
`(aP + cQ, bP + dQ)`. The morphism `[Γ(N)] ⟶ [Γ₁(N)]` is invariant under the matrices with first
column `(1, 0)`.

Naive `[Γ(N)]`-structures rigidify for `N ≥ 3` (Katz–Mazur 2.7.2): an automorphism of an elliptic
curve `E/S` fixing a naive `[Γ(N)]`-structure is the identity (`ModuliProblem.isRigid_gammaNaive`),
with no hypothesis on `S`; such a structure can only exist where `N` is invertible. More generally
the naive `A`-structures are rigid as soon as `A` contains elements `a` and `b` with `a² ≠ 1`,
`b ≠ 1` and `b ≠ a^{±1}` (`ModuliProblem.isRigid_naiveLevel`), since an automorphism fixing `φ a`
and `φ b` is trivial (`EllipticCurveGeom.IsFiberwiseInjective.eq_id_of_isPullback`). The bound
`N ≥ 3` is sharp: for `N ≤ 2`, the automorphism `[-1]` fixes every point killed by `N`. Taking
`a = 1` and `b = 2` in `ℤ/Nℤ` shows that `[Γ₁(N)]` is rigid for `N ≥ 4`
(`ModuliProblem.isRigid_gammaOneNaive`).

The definitions make sense over every base `B`, but they are the naive level structures of Katz and
Mazur only over a base on which `N` is invertible, where `E[N]` is finite étale. Over a general base
the level structures are Drinfeld's (`ModuliProblem.gammaOne` for `[Γ₁(N)]`, `ModuliProblem.gamma`
for `[Γ(N)]`).

**Relative representability.** For a finite group `A`, suppose that the homomorphisms
`A →* E(T)`, for schemes `T` over `S`, are represented by a scheme `H` over `S` with a universal
homomorphism `u : A →* E(H)`. Then the naive `A`-structures on the base changes `E_T` are
represented by the open subscheme of `H` on which `u` is injective on fibres, the naive locus of
`u` (`ModuliProblem.naiveLevelRepresentableBy`): a `T`-point of `E_T` is the same as a point of `E`
with values in `T` (`EllObj.baseChangePointsEquiv`), and such a point meets the zero section of
`E_T` exactly where its image meets the zero section of `E`. For `A = ℤ/Nℤ`, `N ≠ 0`, the
`N`-torsion `E[N]` with its universal point is such an `H`
(`EllipticCurveGeom.existsUnique_comp_torsionPointHom`), so the naive problem `[Γ₁(N)]` is
relatively representable by the open subscheme of `E[N]` of points of exact order `N` in every
fibre (`ModuliProblem.gammaOneNaiveRelRepData`); when `N` is invertible on `B`, `E[N]` is étale,
so `[Γ₁(N)]` is étale over `Ell/B` (`ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData`).
For `A = (ℤ/Nℤ)²`, `N ≠ 0`, the fibre product `E[N] ×_S E[N]` with the universal pair of points
of `E[N]` is such an `H` (`EllipticCurveGeom.existsUnique_comp_torsionPairHom`), so the naive
problem `[Γ(N)]` is relatively representable over every base (`ModuliProblem.gammaNaiveRelRepData`).
Its representing schemes are open subschemes of `E[N] ×_S E[N]`, so they inherit from `E[N]` every
property stable under base change and composition which open immersions have
(`ModuliProblem.hasProperty_gammaNaiveRelRepData`), for instance local finite presentation.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevel B A`: the moduli problem of naive
  `A`-structures over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv`: the naive `A`-structures on an object
  `(E/S)` of `Ell/B` are the homomorphisms `A →* E(S)` injective on every fibre.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelMap`: restriction of naive structures along
  an injective homomorphism of groups.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelAction`: the right action of `Aut A` on naive
  `A`-structures.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveAction`: the right action of `GL₂(ℤ/Nℤ)` on
  the naive moduli problem `[Γ(N)]`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaive B N` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaive B N`: the naive moduli problems `[Γ₁(N)]`
  and `[Γ(N)]`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv`: for `N ≠ 0`, the naive
  `[Γ₁(N)]`-structures are the `S`-points of `E[N]` of exact order `N` in every fibre, and the
  naive `[Γ(N)]`-structures are the pairs of `S`-points of `E[N]` independent in every fibre.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLocusEquiv`: for a universal homomorphism `u`, the
  points of the naive locus of `u` with values in `T` are the naive structures on `E_T`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelRepresentableBy`: the naive locus represents
  the fibre of the problem of naive `A`-structures.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveRelRepData` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveRelRepData`: relative-representability data
  for the naive problems `[Γ₁(N)]` and `[Γ(N)]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.Hom.isFiberwiseInjective_pointsPullback`: naive structures
  pull back along arrows of `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_map`: the pull-back of a naive
  structure along an arrow of `Ell/B` is its composite with base change of points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaNaiveToGammaOneNaive_app_apply`:
  the morphism `[Γ(N)] ⟶ [Γ₁(N)]` restricts a naive `[Γ(N)]`-structure along `z ↦ (z, 0)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.eq_one_of_naiveLevelAction_hom_app_eq_self` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.eq_one_of_gammaNaiveAction_hom_app_eq_self`: the actions
  are free over a nonempty base.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv_gammaNaiveAction_hom_app_fst_torsionι`
  and its `snd` analogue: `(P, Q) g = (aP + cQ, bP + dQ)` for `g = !![a, b; c, d]`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_naiveLevel`,
  `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaNaive` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaOneNaive`: naive `A`-structures are rigid
  when `A` contains a suitable pair of elements, the naive moduli problem `[Γ(N)]` is rigid for
  `N ≥ 3`, and `[Γ₁(N)]` is rigid for `N ≥ 4`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive`:
  keeping the first point is invariant under the matrices with first column `(1, 0)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv_map_torsionι` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv_map_fst_torsionι`: the points of `E[N]`
  of a pulled-back naive structure are the base changes of the original points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isFiberwiseInjective_baseChange_iff`: injectivity on
  the fibres of a base change `E_T`, read on the points of `E` with values in `T`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_gammaOneNaiveRelRepData` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_gammaNaiveRelRepData`: the representing
  morphisms of `[Γ₁(N)]` and `[Γ(N)]` inherit the properties of `E[N]` stable under base change
  and composition and holding for open immersions.
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData`: if `N` is
  invertible on `B`, the naive problem `[Γ₁(N)]` is étale over `Ell/B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 (naive level structures
  where `N` is invertible), 3.7.1 (relative representability of naive full level `N`),
  Chapter 4, and §7.1 (the action of `GL₂(ℤ/Nℤ)` on `[Γ(N)]`).
* D. Loeffler, *Modular curves*, lecture notes, Proposition 3.8.2 (naive level structures are
  relatively representable and étale over `Ell/ℤ[1/N]`).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

/-- **Naive `A`-structures pull back along arrows of `Ell/B`**: an arrow `f : X ⟶ Y` exhibits `X`
as a base change of `Y`, and a homomorphism `A →* E(S)` injective on every fibre stays so after
composing with base change of points along `f`. -/
theorem EllObj.Hom.isFiberwiseInjective_pointsPullback {X Y : EllObj B} {A : Type} [Group A]
    {φ : A →* (𝟙_ (Over Y.base) ⟶ Over.mk Y.curve.structureMap)} (f : X ⟶ Y)
    (h : Y.curve.IsFiberwiseInjective φ) :
    X.curve.IsFiberwiseInjective
      ((EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp φ) :=
  h.pointsPullback f.isPullback f.zero_total

namespace ModuliProblem

variable (B) (A : Type) [Group A]

/-- **The moduli problem of naive `A`-structures** over `Ell/B`. A naive `A`-structure on an
object `(E/S)` of `Ell/B` is a homomorphism `A →* E(S)` injective on every fibre of `E` over `S`
(`naiveLevelEquiv`), and it pulls back along an arrow of `Ell/B` by base change of points
(`naiveLevelEquiv_map`). The group `A` lies in `Type`, as the groups `(ℤ/Nℤ)ʳ` of level structures
do, so that the naive structures lie in the universe `Type (u + 1)` of moduli problems. -/
noncomputable def naiveLevel : ModuliProblem B :=
  homLevel B A (fun X φ ↦ X.curve.IsFiberwiseInjective φ)
    EllObj.Hom.isFiberwiseInjective_pointsPullback

variable {B A}

/-- The naive `A`-structures on an object `(E/S)` of `Ell/B` are the homomorphisms `A →* E(S)`
injective on every fibre of `E` over `S`. -/
noncomputable def naiveLevelEquiv (X : EllObj B) :
    (naiveLevel B A).obj (op X) ≃
      {φ : A →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) //
        X.curve.IsFiberwiseInjective φ} :=
  homLevelEquiv (hp := EllObj.Hom.isFiberwiseInjective_pointsPullback) X

/-- The pull-back of a naive `A`-structure along an arrow `φ` of `Ell/B` is its composite with
base change of points along `φ`. -/
@[simp]
theorem naiveLevelEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (naiveLevel B A).obj (op Y)) :
    (naiveLevelEquiv X ((naiveLevel B A).map φ.op α)).1 =
      (EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total).comp (naiveLevelEquiv Y α).1 :=
  homLevelEquiv_map φ α

variable (B) in
/-- **Restriction of naive structures.** An injective homomorphism `ψ : A' →* A` restricts naive
`A`-structures to naive `A'`-structures, `φ ↦ φ ∘ ψ`. -/
noncomputable def naiveLevelMap {A' : Type} [Group A'] (ψ : A' →* A)
    (hψ : Function.Injective ψ) : naiveLevel B A ⟶ naiveLevel B A' :=
  homLevelMap (hp := EllObj.Hom.isFiberwiseInjective_pointsPullback)
    (hp' := EllObj.Hom.isFiberwiseInjective_pointsPullback) B ψ fun _ _ h ↦ h.comp hψ

/-- Restriction along `ψ` composes a naive structure with `ψ`. -/
@[simp]
theorem naiveLevelEquiv_naiveLevelMap_app {A' : Type} [Group A'] (ψ : A' →* A)
    (hψ : Function.Injective ψ) (X : EllObj B) (α : (naiveLevel B A).obj (op X)) :
    (naiveLevelEquiv X ((naiveLevelMap B ψ hψ).app (op X) α)).1 = (naiveLevelEquiv X α).1.comp ψ :=
  homLevelEquiv_homLevelMap_app (hp := EllObj.Hom.isFiberwiseInjective_pointsPullback)
    (hp' := EllObj.Hom.isFiberwiseInjective_pointsPullback) ψ (fun _ _ h ↦ h.comp hψ) X α

/-- Two morphisms of moduli problems into the naive `A`-structures agree once they assign the same
homomorphism `A →* E(S)` to every structure. -/
@[ext]
theorem naiveLevel_hom_ext {P : ModuliProblem B} {f g : P ⟶ naiveLevel B A}
    (h : ∀ (X : EllObj B) (α : P.obj (op X)),
      (naiveLevelEquiv X (f.app (op X) α)).1 = (naiveLevelEquiv X (g.app (op X) α)).1) :
    f = g := by
  ext X α
  exact (naiveLevelEquiv X.unop).injective (Subtype.ext (h X.unop α))

/-! ### The action of the automorphisms of `A` -/

variable (B A) in
/-- **The right action of the automorphisms of `A` on naive `A`-structures.** An automorphism `σ`
of `A` sends a naive `A`-structure `φ : A →* E(S)` to `φ ∘ σ`
(`naiveLevelEquiv_naiveLevelAction_hom_app`). Since `φ ∘ (σ ∘ τ) = (φ ∘ σ) ∘ τ`, this is a right
action, that is, a homomorphism from the opposite group `(Aut A)ᵐᵒᵖ` to the automorphisms of the
moduli problem. -/
noncomputable def naiveLevelAction : (MulAut A)ᵐᵒᵖ →* Aut (naiveLevel B A) where
  toFun σ :=
    { hom := naiveLevelMap B σ.unop.toMonoidHom σ.unop.injective
      inv := naiveLevelMap B σ.unop.symm.toMonoidHom σ.unop.symm.injective
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  map_one' := by
    apply Iso.ext
    refine naiveLevel_hom_ext fun X α ↦ MonoidHom.ext fun a ↦ ?_
    -- Mathlib has no lemma for the unit of `Aut`; it is `Iso.refl` by definition
    change _ = (naiveLevelEquiv X α).1 a
    simp
  map_mul' σ τ := by
    refine Eq.trans ?_ (Aut.Aut_mul_def _ _ _).symm
    apply Iso.ext
    refine naiveLevel_hom_ext fun X α ↦ MonoidHom.ext fun a ↦ ?_
    simp

/-- An automorphism `σ` of `A` sends a naive `A`-structure `φ` to `φ ∘ σ`. -/
@[simp]
theorem naiveLevelEquiv_naiveLevelAction_hom_app (σ : (MulAut A)ᵐᵒᵖ) (X : EllObj B)
    (α : (naiveLevel B A).obj (op X)) :
    (naiveLevelEquiv X ((naiveLevelAction B A σ).hom.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp σ.unop.toMonoidHom :=
  naiveLevelEquiv_naiveLevelMap_app _ σ.unop.injective X α

/-- The inverse of the automorphism of the moduli problem given by `σ` sends a naive
`A`-structure `φ` to `φ ∘ σ⁻¹`. -/
@[simp]
theorem naiveLevelEquiv_naiveLevelAction_inv_app (σ : (MulAut A)ᵐᵒᵖ) (X : EllObj B)
    (α : (naiveLevel B A).obj (op X)) :
    (naiveLevelEquiv X ((naiveLevelAction B A σ).inv.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp σ.unop.symm.toMonoidHom :=
  naiveLevelEquiv_naiveLevelMap_app _ σ.unop.symm.injective X α

/-- **The action of the automorphisms of `A` on naive `A`-structures is free.** Over a nonempty
base, an automorphism of `A` fixing a naive `A`-structure is the identity, because a naive
structure is injective. Over the empty base every automorphism fixes the unique structure. -/
theorem eq_one_of_naiveLevelAction_hom_app_eq_self {X : EllObj B} [Nonempty X.base]
    {σ : (MulAut A)ᵐᵒᵖ} {α : (naiveLevel B A).obj (op X)}
    (h : (naiveLevelAction B A σ).hom.app (op X) α = α) : σ = 1 := by
  have h' := congrArg (fun α ↦ (naiveLevelEquiv X α).1) h
  simp only [naiveLevelEquiv_naiveLevelAction_hom_app] at h'
  refine MulOpposite.unop_injective (MulEquiv.ext fun a ↦ (naiveLevelEquiv X α).2.injective ?_)
  simpa using DFunLike.congr_fun h' a

/-! ### Rigidity -/

variable (B) in
/-- **Naive `A`-structures are rigid when `A` contains a full level pair.** If `A` contains `a` and
`b` with `a² ≠ 1`, `b ≠ 1`, `b ≠ a` and `b ≠ a⁻¹`, then an automorphism of an elliptic curve
`E/S` over the identity of `S` fixing a naive `A`-structure is the identity. No hypothesis is made
on the base. -/
theorem isRigid_naiveLevel {a b : A} (ha : a * a ≠ 1) (hb : b ≠ 1) (hba : b ≠ a)
    (hba' : b ≠ a⁻¹) : (naiveLevel B A).IsRigid := by
  refine (isRigid_iff _).mpr fun X σ hσ α hα ↦ ?_
  have hfix (c : A) :
      ((naiveLevelEquiv X α).1 c).left ≫ σ.total = ((naiveLevelEquiv X α).1 c).left := by
    have h := DFunLike.congr_fun (naiveLevelEquiv_map σ α) c
    rw [hα, MonoidHom.comp_apply, EllipticCurveGeom.eq_pointsPullback_iff] at h
    rw [h, hσ, Category.id_comp]
  refine EllObj.hom_ext ?_
  rw [EllObj.id_total]
  exact (naiveLevelEquiv X α).2.eq_id_of_isPullback ha hb hba hba' (hσ ▸ σ.isPullback)
    (by rw [σ.zero_total, hσ, Category.id_comp]) (hfix a) (hfix b)

variable (B) (N : ℕ)

/-- **The naive moduli problem `[Γ₁(N)]`** over `Ell/B`: a naive `[Γ₁(N)]`-structure on `(E/S)` is
a homomorphism `ℤ/Nℤ →* E(S)` injective on every fibre, that is, for `N ≠ 0`, an `S`-point `P` of
`E[N]` none of whose multiples `P, …, (N - 1)P` meets the zero section
(`EllipticCurveGeom.isFiberwiseInjective_zmod_iff`). It is the naive level structure of Katz and
Mazur over a base on which `N` is invertible. -/
noncomputable abbrev gammaOneNaive : ModuliProblem B :=
  naiveLevel B (Multiplicative (ZMod N))

/-- **The naive moduli problem `[Γ(N)]`** over `Ell/B`: a naive `[Γ(N)]`-structure on `(E/S)` is a
homomorphism `(ℤ/Nℤ)² →* E(S)` injective on every fibre. Over a base on which `N` is invertible,
it is a pair of `S`-points of `E[N]` forming a basis of the `N`-torsion in every geometric fibre
(`EllipticCurveGeom.isFiberwiseInjective_iff_range_eq_ker`). -/
noncomputable abbrev gammaNaive : ModuliProblem B :=
  naiveLevel B (Multiplicative (ZMod N × ZMod N))

/-- **Full level structures rigidify for `N ≥ 3`** (Katz–Mazur 2.7.2). An automorphism of an
elliptic curve `E/S` over the identity of `S` fixing a naive `[Γ(N)]`-structure `(P, Q)` is the
identity, because it fixes `P`, `Q` and `-P`, which are distinct in every fibre. No hypothesis is
made on the base, which may be nonreduced or non-affine. -/
theorem isRigid_gammaNaive (hN : 3 ≤ N) : (gammaNaive B N).IsRigid := by
  have : Fact (1 < N) := ⟨by omega⟩
  have h2 : (2 : ZMod N) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 N).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos this
    omega
  refine isRigid_naiveLevel B (a := .ofAdd (1, 0)) (b := .ofAdd (0, 1)) ?_ ?_ ?_ ?_
  · rw [← ofAdd_add, Ne, ofAdd_eq_one, Prod.ext_iff]
    simp [one_add_one_eq_two, h2]
  · simp [Prod.ext_iff]
  · simp [Prod.ext_iff]
  · rw [← ofAdd_neg, Ne, Multiplicative.ofAdd.injective.eq_iff]
    simp [Prod.ext_iff]

/-- **Naive `[Γ₁(N)]`-structures rigidify for `N ≥ 4`.** An automorphism of an elliptic curve
`E/S` over the identity of `S` fixing a naive `[Γ₁(N)]`-structure `P` is the identity, because it
fixes `P`, `2P` and `-P`, which are distinct in every fibre. No hypothesis is made on the base. The
bound is sharp: on `Y² + Y = X³` over a field containing a primitive cube root of unity `ζ`, the
automorphism `(X, Y) ↦ (ζX, Y)` fixes the point `(0, 0)` of order `3`. -/
theorem isRigid_gammaOneNaive (hN : 4 ≤ N) : (gammaOneNaive B N).IsRigid := by
  have hne (k : ℕ) (hk₀ : 0 < k) (hk : k < 4) : (k : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd (Nat.le_of_dvd hk₀ h) (by omega)
  refine isRigid_naiveLevel B (a := .ofAdd 1) (b := .ofAdd 2) ?_ ?_ ?_ ?_
  · rw [← ofAdd_add, Ne, ofAdd_eq_one, one_add_one_eq_two]
    exact_mod_cast hne 2 (by norm_num) (by norm_num)
  · rw [Ne, ofAdd_eq_one]
    exact_mod_cast hne 2 (by norm_num) (by norm_num)
  · rw [Ne, Multiplicative.ofAdd.injective.eq_iff, ← sub_eq_zero]
    norm_num [show (1 : ZMod N) ≠ 0 by exact_mod_cast hne 1 (by norm_num) (by norm_num)]
  · rw [← ofAdd_neg, Ne, Multiplicative.ofAdd.injective.eq_iff, ← sub_eq_zero, sub_neg_eq_add]
    norm_num [show (3 : ZMod N) ≠ 0 by exact_mod_cast hne 3 (by norm_num) (by norm_num)]

/-- The morphism `[Γ(N)] ⟶ [Γ₁(N)]` of naive moduli problems which keeps the first component `P`
of a naive `[Γ(N)]`-structure `(P, Q)`, that is, restricts it along `z ↦ (z, 0)`. When `N` is
invertible, `P` is the first vector of the basis `(P, Q)` of the `N`-torsion. -/
noncomputable def gammaNaiveToGammaOneNaive : gammaNaive B N ⟶ gammaOneNaive B N :=
  naiveLevelMap B (AddMonoidHom.toMultiplicative (AddMonoidHom.inl (ZMod N) (ZMod N)))
    (Multiplicative.ofAdd.injective.comp (Prod.mk_left_injective 0))

/-- The morphism `[Γ(N)] ⟶ [Γ₁(N)]` restricts a naive `[Γ(N)]`-structure along `z ↦ (z, 0)`. -/
@[simp]
theorem naiveLevelEquiv_gammaNaiveToGammaOneNaive_app_apply (X : EllObj B)
    (α : (gammaNaive B N).obj (op X)) (z : Multiplicative (ZMod N)) :
    (naiveLevelEquiv X ((gammaNaiveToGammaOneNaive B N).app (op X) α)).1 z =
      (naiveLevelEquiv X α).1 (.ofAdd (z.toAdd, 0)) :=
  DFunLike.congr_fun (naiveLevelEquiv_naiveLevelMap_app _ _ X α) z

/-! ### Naive level structures as points of `E[N]` -/

section Points

variable {B N} [NeZero N]

/-- **Naive `[Γ₁(N)]`-structures are points of `E[N]`.** For `N ≠ 0`, a naive
`[Γ₁(N)]`-structure `φ` on `(E/S)` is determined by the `S`-point `P = φ 1` of `E[N]`, and the
`S`-points of `E[N]` arising this way are those of exact order `N` in every fibre: none of
`P, 2P, …, (N - 1)P` meets the zero section (`EllipticCurveGeom.isFiberwiseInjective_zmod_iff`). -/
noncomputable def gammaOneNaiveEquiv (X : EllObj B) :
    (gammaOneNaive B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X //
        ∀ k : ℕ, 0 < k → k < N → ∀ s, ((P ≫ X.curve.torsionι N) ^ k).left s ≠ X.curve.zero s} :=
  (naiveLevelEquiv X).trans <|
    ((zmodMonoidHomEquiv N _).trans <| (Equiv.subtypeEquivRight fun _ ↦ by
      rw [zpow_natCast]).trans (X.curve.torsionPointsEquiv N _)).subtypeEquiv fun φ ↦ by
      rw [EllipticCurveGeom.isFiberwiseInjective_zmod_iff]
      simp

/-- The `S`-point of `E[N]` of a naive `[Γ₁(N)]`-structure `φ` is `φ 1`. -/
@[simp]
theorem gammaOneNaiveEquiv_apply_torsionι (X : EllObj B) (α : (gammaOneNaive B N).obj (op X)) :
    (gammaOneNaiveEquiv X α).1 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd 1) :=
  (X.curve.torsionPointsEquiv_apply_torsionι _ _ _).trans (coe_zmodMonoidHomEquiv_apply _)

/-- The naive `[Γ₁(N)]`-structure of an `S`-point `P` of `E[N]` sends `a` to `aP`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneNaiveEquiv_symm_apply (X : EllObj B)
    (P : {P : 𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ s, ((P ≫ X.curve.torsionι N) ^ k).left s ≠ X.curve.zero s})
    (a : ZMod N) :
    (naiveLevelEquiv X ((gammaOneNaiveEquiv X).symm P)).1 (.ofAdd a) =
      (P.1 ≫ X.curve.torsionι N) ^ a.val := by
  simp [gammaOneNaiveEquiv]

/-- The `S`-point of `E[N]` of the pull-back of a naive `[Γ₁(N)]`-structure along an arrow `φ` of
`Ell/B` is the base change along `φ` of its `S`-point of `E[N]`. -/
theorem gammaOneNaiveEquiv_map_torsionι {X Y : EllObj B} (φ : X ⟶ Y)
    (α : (gammaOneNaive B N).obj (op Y)) :
    (gammaOneNaiveEquiv X ((gammaOneNaive B N).map φ.op α)).1 ≫ X.curve.torsionι N =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total
        ((gammaOneNaiveEquiv Y α).1 ≫ Y.curve.torsionι N) := by
  simp

/-- **Naive `[Γ(N)]`-structures are pairs of points of `E[N]`.** For `N ≠ 0`, a naive
`[Γ(N)]`-structure `φ` on `(E/S)` is determined by the pair `(P, Q) = (φ (1, 0), φ (0, 1))` of
`S`-points of `E[N]`, and the pairs arising this way are those none of whose combinations `aP + bQ`
with `(a, b) ≠ 0` meets the zero section (`EllipticCurveGeom.isFiberwiseInjective_zmod_prod_iff`).
When `N` is invertible on `S`, these are the pairs forming a basis of the `N`-torsion in every
geometric fibre. -/
noncomputable def gammaNaiveEquiv (X : EllObj B) :
    (gammaNaive B N).obj (op X) ≃
      {PQ : (𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X) ×
          (𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X) //
        ∀ a b : ZMod N, (a, b) ≠ 0 → ∀ s, ((PQ.1 ≫ X.curve.torsionι N) ^ a.val *
          (PQ.2 ≫ X.curve.torsionι N) ^ b.val).left s ≠ X.curve.zero s} :=
  (naiveLevelEquiv X).trans <| ((zmodProdMonoidHomEquiv N _).trans <|
    ((Equiv.subtypeEquivRight fun _ ↦ by rw [zpow_natCast]).trans
      (X.curve.torsionPointsEquiv N _)).prodCongr
    ((Equiv.subtypeEquivRight fun _ ↦ by rw [zpow_natCast]).trans
      (X.curve.torsionPointsEquiv N _))).subtypeEquiv fun φ ↦ by
      rw [EllipticCurveGeom.isFiberwiseInjective_zmod_prod_iff]
      simp

/-- The first `S`-point `P` of `E[N]` of a naive `[Γ(N)]`-structure `φ` is `φ (1, 0)`. -/
@[simp]
theorem gammaNaiveEquiv_apply_fst_torsionι (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X α).1.1 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd (1, 0)) :=
  (X.curve.torsionPointsEquiv_apply_torsionι _ _ _).trans (coe_zmodProdMonoidHomEquiv_apply_fst _)

/-- The second `S`-point `Q` of `E[N]` of a naive `[Γ(N)]`-structure `φ` is `φ (0, 1)`. -/
@[simp]
theorem gammaNaiveEquiv_apply_snd_torsionι (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X α).1.2 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd (0, 1)) :=
  (X.curve.torsionPointsEquiv_apply_torsionι _ _ _).trans (coe_zmodProdMonoidHomEquiv_apply_snd _)

/-- The naive `[Γ(N)]`-structure of a pair `(P, Q)` of `S`-points of `E[N]` sends `(a, b)` to
`aP + bQ`. -/
@[simp]
theorem naiveLevelEquiv_gammaNaiveEquiv_symm_apply (X : EllObj B)
    (PQ : {PQ : (𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X) ×
        (𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X) //
      ∀ a b : ZMod N, (a, b) ≠ 0 → ∀ s, ((PQ.1 ≫ X.curve.torsionι N) ^ a.val *
        (PQ.2 ≫ X.curve.torsionι N) ^ b.val).left s ≠ X.curve.zero s})
    (a b : ZMod N) :
    (naiveLevelEquiv X ((gammaNaiveEquiv X).symm PQ)).1 (.ofAdd (a, b)) =
      (PQ.1.1 ≫ X.curve.torsionι N) ^ a.val * (PQ.1.2 ≫ X.curve.torsionι N) ^ b.val := by
  simp [gammaNaiveEquiv]

/-- The first `S`-point of `E[N]` of the pull-back of a naive `[Γ(N)]`-structure along an arrow `φ`
of `Ell/B` is the base change along `φ` of its first `S`-point of `E[N]`. -/
theorem gammaNaiveEquiv_map_fst_torsionι {X Y : EllObj B} (φ : X ⟶ Y)
    (α : (gammaNaive B N).obj (op Y)) :
    (gammaNaiveEquiv X ((gammaNaive B N).map φ.op α)).1.1 ≫ X.curve.torsionι N =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total
        ((gammaNaiveEquiv Y α).1.1 ≫ Y.curve.torsionι N) := by
  simp

/-- The second `S`-point of `E[N]` of the pull-back of a naive `[Γ(N)]`-structure along an arrow
`φ` of `Ell/B` is the base change along `φ` of its second `S`-point of `E[N]`. -/
theorem gammaNaiveEquiv_map_snd_torsionι {X Y : EllObj B} (φ : X ⟶ Y)
    (α : (gammaNaive B N).obj (op Y)) :
    (gammaNaiveEquiv X ((gammaNaive B N).map φ.op α)).1.2 ≫ X.curve.torsionι N =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total
        ((gammaNaiveEquiv Y α).1.2 ≫ Y.curve.torsionι N) := by
  simp

end Points

/-! ### The action of `GL₂(ℤ/Nℤ)` on naive `[Γ(N)]`-structures -/

section GeneralLinear

variable {B N}

variable (B N) in
/-- **The right action of `GL₂(ℤ/Nℤ)` on the naive moduli problem `[Γ(N)]`.** A matrix
`g = !![a, b; c, d]` acts on `(ℤ/Nℤ)²` by multiplication of column vectors
(`TauCeti.zmodProdMulAutEquiv`), and so sends the naive `[Γ(N)]`-structure with points `(P, Q)` to
the one with points `(P, Q) g = (aP + cQ, bP + dQ)`
(`gammaNaiveEquiv_gammaNaiveAction_hom_app_fst_torsionι`,
`gammaNaiveEquiv_gammaNaiveAction_hom_app_snd_torsionι`). -/
noncomputable def gammaNaiveAction : (GL (Fin 2) (ZMod N))ᵐᵒᵖ →* Aut (gammaNaive B N) :=
  (naiveLevelAction B _).comp (MonoidHom.op (zmodProdMulAutEquiv N).toMonoidHom)

/-- A matrix `g` sends a naive `[Γ(N)]`-structure `φ : (ℤ/Nℤ)² →* E(S)` to `φ ∘ g`. -/
@[simp]
theorem naiveLevelEquiv_gammaNaiveAction_hom_app (g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ) (X : EllObj B)
    (α : (gammaNaive B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaNaiveAction B N g).hom.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp (zmodProdMulAutEquiv N g.unop).toMonoidHom :=
  naiveLevelEquiv_naiveLevelAction_hom_app _ X α

/-- The inverse of the automorphism of `[Γ(N)]` given by a matrix `g` sends a naive
`[Γ(N)]`-structure `φ : (ℤ/Nℤ)² →* E(S)` to `φ ∘ g⁻¹`. -/
@[simp]
theorem naiveLevelEquiv_gammaNaiveAction_inv_app (g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ) (X : EllObj B)
    (α : (gammaNaive B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaNaiveAction B N g).inv.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp (zmodProdMulAutEquiv N g.unop).symm.toMonoidHom :=
  naiveLevelEquiv_naiveLevelAction_inv_app _ X α

/-- The naive `[Γ(N)]`-structures are acted on freely by `GL₂(ℤ/Nℤ)` over a nonempty base. -/
theorem eq_one_of_gammaNaiveAction_hom_app_eq_self {X : EllObj B} [Nonempty X.base]
    {g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ} {α : (gammaNaive B N).obj (op X)}
    (h : (gammaNaiveAction B N g).hom.app (op X) α = α) : g = 1 := by
  simpa using eq_one_of_naiveLevelAction_hom_app_eq_self h

variable (B) in
/-- **Keeping the first point is invariant under the matrices fixing `(1, 0)`.** A matrix whose
first column is `(1, 0)` does not change the first point `P` of a naive `[Γ(N)]`-structure, so the
morphism `[Γ(N)] ⟶ [Γ₁(N)]` is invariant under the subgroup of such matrices. -/
theorem gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive {g : GL (Fin 2) (ZMod N)}
    (h₀₀ : g 0 0 = 1) (h₁₀ : g 1 0 = 0) :
    (gammaNaiveAction B N (.op g)).hom ≫ gammaNaiveToGammaOneNaive B N =
      gammaNaiveToGammaOneNaive B N := by
  ext X α z
  simp [h₀₀, h₁₀]

variable [NeZero N]

/-- **The row-vector convention, first point.** The first point of `E[N]` of the naive
`[Γ(N)]`-structure `(P, Q) g` is `aP + cQ`, where `(a, c)` is the first column of `g`. -/
theorem gammaNaiveEquiv_gammaNaiveAction_hom_app_fst_torsionι (g : GL (Fin 2) (ZMod N))
    (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X ((gammaNaiveAction B N (.op g)).hom.app (op X) α)).1.1 ≫
        X.curve.torsionι N =
      ((gammaNaiveEquiv X α).1.1 ≫ X.curve.torsionι N) ^ (g 0 0).val *
        ((gammaNaiveEquiv X α).1.2 ≫ X.curve.torsionι N) ^ (g 1 0).val := by
  rw [← naiveLevelEquiv_gammaNaiveEquiv_symm_apply, Equiv.symm_apply_apply]
  simp

/-- **The row-vector convention, second point.** The second point of `E[N]` of the naive
`[Γ(N)]`-structure `(P, Q) g` is `bP + dQ`, where `(b, d)` is the second column of `g`. -/
theorem gammaNaiveEquiv_gammaNaiveAction_hom_app_snd_torsionι (g : GL (Fin 2) (ZMod N))
    (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X ((gammaNaiveAction B N (.op g)).hom.app (op X) α)).1.2 ≫
        X.curve.torsionι N =
      ((gammaNaiveEquiv X α).1.1 ≫ X.curve.torsionι N) ^ (g 0 1).val *
        ((gammaNaiveEquiv X α).1.2 ≫ X.curve.torsionι N) ^ (g 1 1).val := by
  rw [← naiveLevelEquiv_gammaNaiveEquiv_symm_apply, Equiv.symm_apply_apply]
  simp

end GeneralLinear

/-! ### Relative representability -/

section Representable

open EllipticCurveGeom

variable {B} {X : EllObj B} {A : Type} [Group A] {H : Over X.base}
  (u : A →* (H ⟶ Over.mk X.curve.structureMap))

/-- **Injectivity on fibres of a base change, read on the original curve.** For an object
`X = (E/S)` of `Ell/B` and a scheme `T` over `S`, a homomorphism `φ : A →* E_T(T)` is injective on
every fibre of the base change `E_T` exactly when, for every `a ≠ 1`, the point of `E` with values
in `T` given by `φ a` (`EllObj.baseChangePointsEquiv`) misses the zero section of `E` at every
point of `T`. -/
theorem isFiberwiseInjective_baseChange_iff {T : Over X.base}
    {φ : A →* (𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
      Over.mk (X.baseChangeFunctor.obj T).curve.structureMap)} :
    (X.baseChangeFunctor.obj T).curve.IsFiberwiseInjective φ ↔
      ∀ a, a ≠ 1 → ∀ t, (X.baseChangePointsEquiv T (φ a)).left t ≠ X.curve.zero (T.hom t) := by
  rw [EllipticCurveGeom.isFiberwiseInjective_iff]
  refine forall₂_congr fun a _ ↦ forall_congr' fun t ↦ Iff.not ?_
  refine (EllipticCurveGeom.left_apply_eq_zero_iff_of_isPullback
    (X.baseChangeFunctorHom T).isPullback (X.baseChangeFunctorHom T).zero_total (φ a) t).trans ?_
  rw [← Scheme.Hom.comp_apply, ← EllObj.baseChangePointsEquiv_apply_left,
    EllObj.baseChangeFunctorHom_base]
  -- the two sides differ only in the type of `t`: the base `(X.baseChangeFunctor.obj T).base` of
  -- the base change is `T.left` by definition
  exact Iff.rfl

variable [Finite A]

/-- **The naive structure of a point of the naive locus.** For a point `y` of the naive locus of
`u` with values in a scheme `T` over `S`, the homomorphism `A →* E_T(T)` sending `a` to the
`T`-point of the base change `E_T` given by the point `y ≫ u a` of `E` with values in `T`. It is
injective on every fibre (`isFiberwiseInjective_naiveLocusHom`). -/
noncomputable def naiveLocusHom {T : Over X.base} (y : T ⟶ naiveLocusOver u) :
    A →* (𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
      Over.mk (X.baseChangeFunctor.obj T).curve.structureMap) :=
  { toFun a := (X.baseChangePointsEquiv T).symm (y ≫ naiveLocusι u ≫ u a)
    map_one' := by simp
    map_mul' a b := by simp [MonObj.comp_mul] }

@[simp]
theorem baseChangePointsEquiv_naiveLocusHom {T : Over X.base} (y : T ⟶ naiveLocusOver u) (a : A) :
    X.baseChangePointsEquiv T (naiveLocusHom u y a) = y ≫ naiveLocusι u ≫ u a :=
  MulEquiv.apply_symm_apply _ _

/-- The naive structure of a point of the naive locus is injective on every fibre. -/
theorem isFiberwiseInjective_naiveLocusHom {T : Over X.base} (y : T ⟶ naiveLocusOver u) :
    (X.baseChangeFunctor.obj T).curve.IsFiberwiseInjective (naiveLocusHom u y) := by
  rw [isFiberwiseInjective_baseChange_iff]
  simp_rw [baseChangePointsEquiv_naiveLocusHom, ← Category.assoc]
  refine (range_left_subset_naiveLocus_iff u _).mp ?_
  rintro _ ⟨t, rfl⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply, naiveLocusι_left, ← coe_naiveLocusOpens u,
    ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

variable (hu : ∀ (T : Over X.base) (φ : A →* (T ⟶ Over.mk X.curve.structureMap)),
  ∃! x : T ⟶ H, ∀ a, x ≫ u a = φ a)

include hu in
private theorem bijective_naiveLocusHom (T : Over X.base) :
    Function.Bijective fun y : T ⟶ naiveLocusOver u ↦ (naiveLevelEquiv _).symm
      ⟨naiveLocusHom u y, isFiberwiseInjective_naiveLocusHom u y⟩ := by
  refine ⟨fun y y' h ↦ ?_, fun α ↦ ?_⟩
  · have h' := congrArg (fun α ↦ (naiveLevelEquiv _ α).1) h
    simp only [Equiv.apply_symm_apply] at h'
    have hyy' : ∀ a, (y' ≫ naiveLocusι u) ≫ u a = (y ≫ naiveLocusι u) ≫ u a := fun a ↦ by
      simpa using (congrArg (X.baseChangePointsEquiv T) (DFunLike.congr_fun h' a)).symm
    rw [← cancel_mono (naiveLocusι u)]
    exact (hu T ((X.baseChangePointsEquiv T).toMonoidHom.comp (naiveLocusHom u y))).unique
      (fun a ↦ by simp) (fun a ↦ by simpa using hyy' a)
  · obtain ⟨⟨ψ, hψ⟩, rfl⟩ := (naiveLevelEquiv _).symm.surjective α
    obtain ⟨x, hx, -⟩ := hu T ((X.baseChangePointsEquiv T).toMonoidHom.comp ψ)
    have hrange : Set.range x.left ⊆ naiveLocus u := by
      rw [range_left_subset_naiveLocus_iff]
      simpa [hx] using isFiberwiseInjective_baseChange_iff.mp hψ
    let y : T ⟶ naiveLocusOver u := Over.homMk (IsOpenImmersion.lift (naiveLocusOpens u).ι
      x.left (by rwa [Scheme.Opens.range_ι, coe_naiveLocusOpens])) (by simp)
    have hy : y ≫ naiveLocusι u = x := by
      ext1
      simp [y]
    refine ⟨y, congrArg _ (Subtype.ext (MonoidHom.ext fun a ↦ ?_))⟩
    apply (X.baseChangePointsEquiv T).injective
    simpa [reassoc_of% hy] using hx a

/-- **The naive structures given by the naive locus.** For a universal homomorphism `u`, the points
of the naive locus of `u` with values in a scheme `T` over `S` correspond to the naive
`A`-structures on the base change `E_T`, a point `y` corresponding to `naiveLocusHom u y`. -/
noncomputable def naiveLocusEquiv (T : Over X.base) :
    (T ⟶ naiveLocusOver u) ≃ (naiveLevel B A).obj (op (X.baseChangeFunctor.obj T)) :=
  Equiv.ofBijective _ (bijective_naiveLocusHom u hu T)

@[simp]
theorem naiveLevelEquiv_naiveLocusEquiv {T : Over X.base} (y : T ⟶ naiveLocusOver u) :
    (naiveLevelEquiv _ (naiveLocusEquiv u hu T y)).1 = naiveLocusHom u y := by
  simp [naiveLocusEquiv]

/-- The correspondence `naiveLocusEquiv` is natural in the scheme `T` over `S`. -/
theorem naiveLocusEquiv_comp {T' T : Over X.base} (f : T' ⟶ T) (y : T ⟶ naiveLocusOver u) :
    naiveLocusEquiv u hu T' (f ≫ y) =
      (naiveLevel B A).map (X.baseChangeFunctor.map f).op (naiveLocusEquiv u hu T y) := by
  refine (naiveLevelEquiv _).injective (Subtype.ext (MonoidHom.ext fun a ↦ ?_))
  apply (X.baseChangePointsEquiv T').injective
  simp only [naiveLevelEquiv_map, naiveLevelEquiv_naiveLocusEquiv, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [EllObj.baseChangePointsEquiv_pointsPullback]
  simp

/-- **Naive structures are represented by the naive locus.** Let `X = (E/S)` be an object of
`Ell/B`, `A` a finite group, and `u : A →* E(H)` a universal homomorphism to the points of `E` with
values in a scheme `H` over `S`: every homomorphism `φ : A →* E(T)`, for `T` over `S`, is
`a ↦ x ≫ u a` for a unique point `x` of `H` with values in `T`. Then the naive `A`-structures on the
base changes `E_T` are represented by the open subscheme of `H` on which `u` is injective on
fibres (`naiveLocusEquiv`). -/
noncomputable def naiveLevelRepresentableBy :
    ((naiveLevel B A).fibre X).RepresentableBy (naiveLocusOver u) where
  homEquiv {T} := naiveLocusEquiv u hu T
  homEquiv_comp f y := naiveLocusEquiv_comp u hu f y

end Representable

/-! ### Relative representability of the naive problem `[Γ₁(N)]` -/

section GammaOneNaive

variable {B N} [NeZero N]

/-- **The naive moduli problem `[Γ₁(N)]` is relatively representable.** For an object
`X = (E/S)` of `Ell/B`, the naive `[Γ₁(N)]`-structures on the base changes `E_T` of `E` are
represented by the open subscheme of `E[N]` of points `P` none of whose multiples `aP` with
`a ≠ 0` meets the zero section, the points of exact order `N` in every fibre: the naive locus of
the universal point of `E[N]` (`EllipticCurveGeom.torsionPointHom`). -/
noncomputable def gammaOneNaiveRelRepData : (gammaOneNaive B N).RelRepData where
  rep X := EllipticCurveGeom.naiveLocusOver (X.curve.torsionPointHom N)
  representableBy X :=
    naiveLevelRepresentableBy _ fun _ ↦ X.curve.existsUnique_comp_torsionPointHom N

@[simp]
theorem gammaOneNaiveRelRepData_rep (X : EllObj B) :
    (gammaOneNaiveRelRepData (B := B) (N := N)).rep X =
      EllipticCurveGeom.naiveLocusOver (X.curve.torsionPointHom N) :=
  (rfl)

/-- The representing morphisms of the naive problem `[Γ₁(N)]` have every property of morphisms of
schemes which is stable under composition, holds for open immersions, and holds for the
`N`-torsion of every elliptic curve: each representing scheme is an open subscheme of `E[N]`. -/
theorem hasProperty_gammaOneNaiveRelRepData {W : MorphismProperty Scheme.{u}}
    [W.IsStableUnderComposition] (hW : @IsOpenImmersion ≤ W)
    (h : ∀ X : EllObj B, W (X.curve.torsion N).X.hom) :
    (gammaOneNaiveRelRepData (B := B) (N := N)).HasProperty W :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦ EllipticCurveGeom.naiveLocusOver_hom_mem _ hW (h X)

/-- **The naive moduli problem `[Γ₁(N)]` is étale over `Ell/B` when `N` is invertible on `B`**:
if `N` is invertible in every residue field of `B`, every representing scheme is étale over its
base, as an open subscheme of the étale `N`-torsion. -/
theorem hasProperty_etale_gammaOneNaiveRelRepData (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    (gammaOneNaiveRelRepData (B := B) (N := N)).HasProperty @Etale :=
  -- instance search does not reach composition stability of étale morphisms by itself
  have : MorphismProperty.IsStableUnderComposition @Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  hasProperty_gammaOneNaiveRelRepData (fun _ _ _ _ ↦ inferInstance) fun X ↦
    X.curve.etale_torsion_hom_of_forall_intCast_ne_zero (n := N) fun s hs ↦
      hN (X.structureMap s) <| (X.structureMap.residueFieldMap s).hom.injective <| by
        rw [map_natCast, map_zero]
        simpa using hs

end GammaOneNaive

/-! ### Relative representability of the naive problem `[Γ(N)]` -/

section GammaNaive

variable {B N} [NeZero N]

/-- **The naive moduli problem `[Γ(N)]` is relatively representable.** For an object `X = (E/S)`
of `Ell/B`, the naive `[Γ(N)]`-structures on the base changes `E_T` of `E` are represented by the
open subscheme of `E[N] ×_S E[N]` of pairs `(P, Q)` none of whose combinations `aP + bQ` with
`(a, b) ≠ 0` meets the zero section: the naive locus of the universal pair of points of `E[N]`
(`EllipticCurveGeom.torsionPairHom`). This holds over every base `B`; over a base on which `N` is
invertible these are the naive full level `N` structures of Katz and Mazur. -/
noncomputable def gammaNaiveRelRepData : (gammaNaive B N).RelRepData where
  rep X := EllipticCurveGeom.naiveLocusOver (X.curve.torsionPairHom N)
  representableBy X :=
    naiveLevelRepresentableBy _ fun _ ↦ X.curve.existsUnique_comp_torsionPairHom N

@[simp]
theorem gammaNaiveRelRepData_rep (X : EllObj B) :
    (gammaNaiveRelRepData (B := B) (N := N)).rep X =
      EllipticCurveGeom.naiveLocusOver (X.curve.torsionPairHom N) :=
  (rfl)

/-- The representing morphisms of the naive problem `[Γ(N)]` have every property of morphisms of
schemes which is stable under base change and composition, holds for open immersions, and holds
for the `N`-torsion of every elliptic curve: each representing scheme is an open subscheme of
`E[N] ×_S E[N]`, whose structure morphism is the composite of that open immersion with the
morphism from `E[N] ×_S E[N]` to the base. -/
theorem hasProperty_gammaNaiveRelRepData {W : MorphismProperty Scheme.{u}}
    [W.IsStableUnderBaseChange] [W.IsStableUnderComposition] (hW : @IsOpenImmersion ≤ W)
    (h : ∀ X : EllObj B, W (X.curve.torsion N).X.hom) :
    (gammaNaiveRelRepData (B := B) (N := N)).HasProperty W :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦
    EllipticCurveGeom.naiveLocusOver_hom_mem _ hW
      (W.comp_mem _ _ (W.pullback_fst _ _ (h X)) (h X))

/-- The naive problem `[Γ(N)]` is locally of finite presentation over `Ell/B`. -/
theorem hasProperty_gammaNaiveRelRepData_locallyOfFinitePresentation :
    (gammaNaiveRelRepData (B := B) (N := N)).HasProperty @LocallyOfFinitePresentation :=
  hasProperty_gammaNaiveRelRepData (fun _ _ _ _ ↦ inferInstance) fun _ ↦ inferInstance

end GammaNaive

end ModuliProblem

end TauCeti.AlgebraicGeometry
