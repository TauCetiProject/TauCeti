/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Primitive
public import TauCeti.AlgebraicGeometry.ModularCurve.HomLevel
public import TauCeti.Data.ZMod.MonoidHomEquiv

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

The definitions make sense over every base `B`, but they are the naive level structures of Katz and
Mazur only over a base on which `N` is invertible, where `E[N]` is finite étale. Over a general base
the level structures are Drinfeld's (`ModuliProblem.gammaOne` for `[Γ₁(N)]`, `ModuliProblem.gamma`
for `[Γ(N)]`).

For `N ≠ 0` the naive problem `[Γ₁(N)]` is relatively representable over `Ell/B`
(`ModuliProblem.gammaOneNaiveRelRepData`): for an object `(E/S)`, the naive
`[Γ₁(N)]`-structures on the base change `E_T` along a scheme `T` over `S` are the morphisms
`T ⟶ E[N]^×` over `S` (`ModuliProblem.gammaOneNaiveBaseChangeEquiv`), where `E[N]^×` is the open
subscheme of `E[N]` of points of exact order `N` in every fibre
(`EllipticCurveGeom.primitiveTorsion`). When `N` is invertible on `B`, `E[N]` is étale over `S`, so
`[Γ₁(N)]` is étale over `Ell/B` (`ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData`).

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
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveBaseChangeEquiv`: the naive
  `[Γ₁(N)]`-structures on the base change `E_T` are the morphisms `T ⟶ E[N]^×`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveRelRepData`: the naive problem `[Γ₁(N)]`
  is relatively representable, by `E[N]^×`.

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
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive`:
  keeping the first point is invariant under the matrices with first column `(1, 0)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv_map_torsionι` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv_map_fst_torsionι`: the points of `E[N]`
  of a pulled-back naive structure are the base changes of the original points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveBaseChangeEquiv_map`: the correspondence
  with morphisms to `E[N]^×` is natural in `T`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData`: if `N` is
  invertible on `B`, the naive problem `[Γ₁(N)]` is étale over `Ell/B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 (naive level structures
  where `N` is invertible), Chapter 4, and §7.1 (the action of `GL₂(ℤ/Nℤ)` on `[Γ(N)]`).
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

/-! ### Relative representability of `[Γ₁(N)]` -/

section RelRep

variable {B N} [NeZero N]

/-- The `T`-points of `E_T[N]` of exact order `N` in every fibre are the points of `E[N]` with
values in `T` of exact order `N` in every fibre. The domain is written with
`X.baseChangeFunctor.obj T`, as in `gammaOneNaiveEquiv`, and the codomain as in
`EllipticCurveGeom.primitiveTorsionHomEquiv`. -/
private noncomputable def gammaOneNaiveBaseChangeEquivAux (X : EllObj B) (T : Over X.base) :
    {P : 𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
        ((X.baseChangeFunctor.obj T).curve.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ s,
        ((P ≫ (X.baseChangeFunctor.obj T).curve.torsionι N) ^ k).left s ≠
          (X.baseChangeFunctor.obj T).curve.zero s} ≃
      {y : T ⟶ (X.curve.torsion N).X //
        ∀ k : ℕ, 0 < k → k < N → ∀ z, ((y ≫ X.curve.torsionι N) ^ k).left z ≠
          X.curve.zero (T.hom z)} :=
  (EllipticCurveGeom.torsionPointsEquivOfIsPullback N (X.curve.isPullback_baseChange T.hom)
    (by simp)).subtypeEquiv fun P ↦
      forall_congr' fun k ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun t ↦
        not_congr <| by
          rw [EllipticCurveGeom.torsionPointsEquivOfIsPullback_apply_torsionι, ← map_pow,
            EllipticCurveGeom.pointsMulEquivOfIsPullback_apply_left]
          exact EllipticCurveGeom.left_apply_eq_zero_iff_of_isPullback
            (X.curve.isPullback_baseChange T.hom) (by simp) _ t

omit [NeZero N] in
private theorem gammaOneNaiveBaseChangeEquivAux_apply_comp_left (X : EllObj B) (T : Over X.base)
    (P : {P : 𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
        ((X.baseChangeFunctor.obj T).curve.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ s,
        ((P ≫ (X.baseChangeFunctor.obj T).curve.torsionι N) ^ k).left s ≠
          (X.baseChangeFunctor.obj T).curve.zero s}) :
    ((gammaOneNaiveBaseChangeEquivAux X T P : T ⟶ (X.curve.torsion N).X) ≫
        X.curve.torsionι N).left =
      (P.1 ≫ (X.baseChangeFunctor.obj T).curve.torsionι N).left ≫
        (X.curve.baseChangeIso T.hom).hom ≫ pullback.fst _ _ :=
  -- `gammaOneNaiveBaseChangeEquivAux` is `torsionPointsEquivOfIsPullback` on underlying points
  (congrArg Over.Hom.left (EllipticCurveGeom.torsionPointsEquivOfIsPullback_apply_torsionι
    N (X.curve.isPullback_baseChange T.hom) (by simp) P.1)).trans
      (EllipticCurveGeom.pointsMulEquivOfIsPullback_apply_left _ _ _)

/-- **Naive `[Γ₁(N)]`-structures on base changes are points of `E[N]^×`.** For an object
`X = (E/S)` of `Ell/B` and a scheme `T` over `S`, the naive `[Γ₁(N)]`-structures on the base change
`E_T` of `E` correspond to the morphisms `T ⟶ E[N]^×` over `S`: a structure `α` corresponds to the
morphism whose composite with `E[N]^× ⟶ E[N] ⟶ E` is the point `α 1` of `E_T` followed by the
projection `E_T ⟶ E` (`gammaOneNaiveBaseChangeEquiv_apply_comp_left`). -/
noncomputable def gammaOneNaiveBaseChangeEquiv (X : EllObj B) (T : Over X.base) :
    (gammaOneNaive B N).obj (op (X.baseChangeFunctor.obj T)) ≃
      (T ⟶ X.curve.primitiveTorsion N) :=
  (gammaOneNaiveEquiv _).trans <|
    (gammaOneNaiveBaseChangeEquivAux X T).trans (X.curve.primitiveTorsionHomEquiv N T).symm

/-- The morphism `T ⟶ E[N]^×` of a naive `[Γ₁(N)]`-structure `α` on `E_T`, followed by
`E[N]^× ⟶ E[N] ⟶ E`, is the point `α 1` of `E_T` followed by the projection `E_T ⟶ E`. -/
theorem gammaOneNaiveBaseChangeEquiv_apply_comp_left (X : EllObj B) (T : Over X.base)
    (α : (gammaOneNaive B N).obj (op (X.baseChangeFunctor.obj T))) :
    (gammaOneNaiveBaseChangeEquiv X T α ≫ X.curve.primitiveTorsionι N ≫ X.curve.torsionι N).left =
      ((naiveLevelEquiv _ α).1 (.ofAdd 1)).left ≫ (X.curve.baseChangeIso T.hom).hom ≫
        pullback.fst _ _ := by
  rw [gammaOneNaiveBaseChangeEquiv, Equiv.trans_apply, Equiv.trans_apply,
    EllipticCurveGeom.primitiveTorsionHomEquiv_symm_apply_comp_assoc,
    gammaOneNaiveBaseChangeEquivAux_apply_comp_left, gammaOneNaiveEquiv_apply_torsionι]

/-- **Naturality of `gammaOneNaiveBaseChangeEquiv`.** Along a morphism `k : T' ⟶ T` of schemes
over the base of `X`, the morphism `T' ⟶ E[N]^×` of the pull-back to `E_{T'}` of a naive
`[Γ₁(N)]`-structure on `E_T` is the composite of `k` with the morphism `T ⟶ E[N]^×` of the
structure. -/
theorem gammaOneNaiveBaseChangeEquiv_map (X : EllObj B) {T' T : Over X.base} (k : T' ⟶ T)
    (α : (gammaOneNaive B N).obj (op (X.baseChangeFunctor.obj T))) :
    gammaOneNaiveBaseChangeEquiv X T' ((gammaOneNaive B N).map (X.baseChangeFunctor.map k).op α) =
      k ≫ gammaOneNaiveBaseChangeEquiv X T α := by
  -- both sides are compared as points of `E` with values in `T'`
  refine (cancel_mono (X.curve.primitiveTorsionι N ≫ X.curve.torsionι N)).mp ?_
  rw [Category.assoc]
  ext1
  rw [Over.comp_left _ _ _ k, gammaOneNaiveBaseChangeEquiv_apply_comp_left,
    gammaOneNaiveBaseChangeEquiv_apply_comp_left, naiveLevelEquiv_map, MonoidHom.comp_apply]
  -- the morphism `E_{T'} ⟶ E_T` lies over `k` and composes with `E_T ⟶ E` to `E_{T'} ⟶ E`
  have hk := congrArg EllObj.Hom.total (X.baseChangeFunctor_map_baseChangeFunctorHom k)
  simp only [EllObj.comp_total, EllObj.baseChangeFunctorHom_total] at hk
  -- the composites are formed by terms, since the base change `E_{T'}` appears both as
  -- `(X.baseChangeFunctor.obj T').curve` and as `X.curve.baseChange T'.hom`
  exact (congrArg (fun m ↦ (EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map k).isPullback
    (X.baseChangeFunctor.map k).zero_total ((naiveLevelEquiv _ α).1 (.ofAdd 1))).left ≫ m)
      hk.symm).trans (EllipticCurveGeom.pointsPullback_left_comp_assoc _ _ _ _)

/-- Naturality of `gammaOneNaiveBaseChangeEquiv`, read backwards: the naive `[Γ₁(N)]`-structure on
`E_{T'}` of the composite of `k : T' ⟶ T` with a morphism `T ⟶ E[N]^×` is the pull-back of the
structure on `E_T` of that morphism. -/
theorem gammaOneNaiveBaseChangeEquiv_symm_comp (X : EllObj B) {T' T : Over X.base}
    (k : T' ⟶ T) (a : T ⟶ X.curve.primitiveTorsion N) :
    (gammaOneNaiveBaseChangeEquiv X T').symm (k ≫ a) =
      (gammaOneNaive B N).map (X.baseChangeFunctor.map k).op
        ((gammaOneNaiveBaseChangeEquiv X T).symm a) := by
  rw [Equiv.symm_apply_eq, gammaOneNaiveBaseChangeEquiv_map, Equiv.apply_symm_apply]

variable (B N) in
/-- **The naive moduli problem `[Γ₁(N)]` is relatively representable.** For an object
`X = (E/S)` of `Ell/B`, the functor `T ↦ [Γ₁(N)](E_T/T)` on schemes over `S` is represented by the
open subscheme `E[N]^×` of `E[N]` of points of exact order `N` in every fibre
(`EllipticCurveGeom.primitiveTorsion`), through `gammaOneNaiveBaseChangeEquiv`
(`gammaOneNaiveRelRepData_rep`, `gammaOneNaiveRelRepData_homEquiv`). -/
noncomputable def gammaOneNaiveRelRepData : (gammaOneNaive B N).RelRepData where
  rep X := X.curve.primitiveTorsion N
  representableBy X :=
    { homEquiv := (gammaOneNaiveBaseChangeEquiv X _).symm
      homEquiv_comp k a := (gammaOneNaiveBaseChangeEquiv_symm_comp X k a).trans
        -- the fibre of `[Γ₁(N)]` over `X` at `T` is `[Γ₁(N)](E_T/T)` after unfolding `fibre`
        rfl }

/-- The scheme representing naive `[Γ₁(N)]`-structures on base changes of `X = (E/S)` is
`E[N]^×`. -/
@[simp]
theorem gammaOneNaiveRelRepData_rep (X : EllObj B) :
    (gammaOneNaiveRelRepData B N).rep X = X.curve.primitiveTorsion N :=
  (rfl)

/-- The naive `[Γ₁(N)]`-structure on `E_T` of a morphism `T ⟶ E[N]^×` is the one given by
`gammaOneNaiveBaseChangeEquiv`, after identifying the representing scheme with `E[N]^×` through
`gammaOneNaiveRelRepData_rep`. -/
@[simp]
theorem gammaOneNaiveRelRepData_homEquiv (X : EllObj B) {T : Over X.base}
    (a : T ⟶ (gammaOneNaiveRelRepData B N).rep X) :
    ((gammaOneNaiveRelRepData B N).representableBy X).homEquiv a =
      (gammaOneNaiveBaseChangeEquiv X T).symm (a ≫ eqToHom (gammaOneNaiveRelRepData_rep X)) :=
  congrArg (gammaOneNaiveBaseChangeEquiv X T).symm (Category.comp_id a).symm

/-- **The naive moduli problem `[Γ₁(N)]` is étale over `Ell/B` when `N` is invertible on `B`**:
if `N` is invertible in every residue field of `B`, every representing scheme `E[N]^×` is étale over
its base. -/
theorem hasProperty_etale_gammaOneNaiveRelRepData (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    (gammaOneNaiveRelRepData B N).HasProperty @Etale :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦ X.curve.etale_primitiveTorsion_hom N fun s hs ↦
    hN (X.structureMap s) <| (X.structureMap.residueFieldMap s).hom.injective <| by
      rw [map_natCast, map_zero]
      exact hs

end RelRep

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

end ModuliProblem

end TauCeti.AlgebraicGeometry
