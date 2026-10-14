/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.ModularCurve.HomLevel
public import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Rigidity

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
`N ≥ 3` is sharp: for `N ≤ 2`, the automorphism `[-1]` fixes every point killed by `N`.

The definitions make sense over every base `B`, but they are the naive level structures of Katz and
Mazur only over a base on which `N` is invertible, where `E[N]` is finite étale. Over a general base
the level structures are Drinfeld's (`ModuliProblem.gammaOne` for `[Γ₁(N)]`, `ModuliProblem.gamma`
for `[Γ(N)]`).

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
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_naiveLevel` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaNaive`: naive `A`-structures are rigid when
  `A` contains a suitable pair of elements, and the naive moduli problem `[Γ(N)]` is rigid for
  `N ≥ 3`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive`:
  keeping the first point is invariant under the matrices with first column `(1, 0)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv_map_torsionι` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv_map_fst_torsionι`: the points of `E[N]`
  of a pulled-back naive structure are the base changes of the original points.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 (naive level structures
  where `N` is invertible), Chapter 4, and §7.1 (the action of `GL₂(ℤ/Nℤ)` on `[Γ(N)]`).
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

end ModuliProblem

end TauCeti.AlgebraicGeometry
