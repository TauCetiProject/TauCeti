/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# The naive moduli problems `[Γ₁(N)]` and `[Γ(N)]`

Let `A` be a group. A *naive `A`-structure* on an elliptic curve `E` over a scheme `S` is a
homomorphism `φ : A →* E(S)` to the group of `S`-points of `E` which is injective on every fibre
of `E` over `S` (`EllipticCurveGeom.IsFiberwiseInjective`): for `a ≠ 1` the section `φ a` misses
the zero section everywhere. The condition is pointwise, so it is stable under base change
(`EllipticCurveGeom.IsFiberwiseInjective.pointsPullback`), and the naive `A`-structures form a
moduli problem over `Ell/B` (`ModuliProblem.naiveLevel`).

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

The definitions make sense over every base `B`, but they are the naive level structures of Katz and
Mazur only over a base on which `N` is invertible, where `E[N]` is finite étale. Over a general base
the level structures are Drinfeld's (`ModuliProblem.gammaOne` for `[Γ₁(N)]`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevel B A`: the moduli problem of naive
  `A`-structures over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv`: the naive `A`-structures on an object
  `(E/S)` of `Ell/B` are the homomorphisms `A →* E(S)` injective on every fibre.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelMap`: restriction of naive structures along
  an injective homomorphism of groups.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaive B N` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaive B N`: the naive moduli problems `[Γ₁(N)]`
  and `[Γ(N)]`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv`: for `N ≠ 0`, the naive
  `[Γ₁(N)]`-structures are the `S`-points of `E[N]` of exact order `N` in every fibre, and the
  naive `[Γ(N)]`-structures are the pairs of `S`-points of `E[N]` independent in every fibre.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_map`: the pull-back of a naive
  structure along an arrow of `Ell/B` is its composite with base change of points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaNaiveToGammaOneNaive_app_apply`:
  the morphism `[Γ(N)] ⟶ [Γ₁(N)]` restricts a naive `[Γ(N)]`-structure along `z ↦ (z, 0)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveEquiv_map_torsionι` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveEquiv_map_fst_torsionι`: the points of `E[N]`
  of a pulled-back naive structure are the base changes of the original points.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 (naive level structures
  where `N` is invertible) and Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (A : Type) [Group A]

/-- **The moduli problem of naive `A`-structures** over `Ell/B`. A naive `A`-structure on an
object `(E/S)` of `Ell/B` is a homomorphism `A →* E(S)` injective on every fibre of `E` over `S`
(`naiveLevelEquiv`), and it pulls back along an arrow of `Ell/B` by base change of points
(`naiveLevelEquiv_map`). The group `A` lies in `Type`, as the groups `(ℤ/Nℤ)ʳ` of level structures
do, so that the naive structures lie in the universe `Type (u + 1)` of moduli problems. -/
noncomputable def naiveLevel : ModuliProblem B where
  obj X := ULift.{u + 1}
    {φ : A →* (𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap) //
      X.unop.curve.IsFiberwiseInjective φ}
  map φ := TypeCat.ofHom fun α ↦
    ⟨⟨(EllipticCurveGeom.pointsPullback φ.unop.isPullback φ.unop.zero_total).comp α.down.1,
      α.down.2.pointsPullback φ.unop.isPullback φ.unop.zero_total⟩⟩
  map_id X := by
    ext α a
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm
  map_comp φ ψ := by
    ext α a
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm

variable {B A}

/-- The naive `A`-structures on an object `(E/S)` of `Ell/B` are the homomorphisms `A →* E(S)`
injective on every fibre of `E` over `S`. -/
noncomputable def naiveLevelEquiv (X : EllObj B) :
    (naiveLevel B A).obj (op X) ≃
      {φ : A →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) //
        X.curve.IsFiberwiseInjective φ} :=
  Equiv.ulift

/-- The pull-back of a naive `A`-structure along an arrow `φ` of `Ell/B` is its composite with
base change of points along `φ`. -/
@[simp]
theorem naiveLevelEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (naiveLevel B A).obj (op Y)) :
    (naiveLevelEquiv X ((naiveLevel B A).map φ.op α)).1 =
      (EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total).comp (naiveLevelEquiv Y α).1 :=
  (rfl)

variable (B) in
/-- **Restriction of naive structures.** An injective homomorphism `ψ : A' →* A` restricts naive
`A`-structures to naive `A'`-structures, `φ ↦ φ ∘ ψ`. -/
noncomputable def naiveLevelMap {A' : Type} [Group A'] (ψ : A' →* A)
    (hψ : Function.Injective ψ) : naiveLevel B A ⟶ naiveLevel B A' where
  app X := TypeCat.ofHom fun α ↦ ⟨⟨α.down.1.comp ψ, α.down.2.comp hψ⟩⟩

/-- Restriction along `ψ` composes a naive structure with `ψ`. -/
@[simp]
theorem naiveLevelEquiv_naiveLevelMap_app {A' : Type} [Group A'] (ψ : A' →* A)
    (hψ : Function.Injective ψ) (X : EllObj B) (α : (naiveLevel B A).obj (op X)) :
    (naiveLevelEquiv X ((naiveLevelMap B ψ hψ).app (op X) α)).1 = (naiveLevelEquiv X α).1.comp ψ :=
  (rfl)

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
  (rfl)

/-! ### Naive level structures as points of `E[N]` -/

section Points

variable {B N}

/-- The homomorphism `ℤ/Nℤ →+ G` sending `1` to an element `g` of `G` killed by `N`. -/
private noncomputable def zmodLift {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    ZMod N →+ Additive G :=
  ZMod.lift N ⟨zmultiplesHom _ (.ofMul g), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩

private theorem zmodLift_natCast {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) (k : ℕ) :
    (zmodLift g hg k).toMul = g ^ k := by
  rw [← Int.cast_natCast, zmodLift, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul, toMul_nsmul,
    toMul_ofMul]

private theorem zmodLift_one {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    (zmodLift g hg 1).toMul = g := by
  rw [← Nat.cast_one, zmodLift_natCast, pow_one]

private theorem zmodLift_apply {G : Type*} [Group G] [NeZero N] (g : G) (hg : g ^ N = 1)
    (a : ZMod N) : (zmodLift g hg a).toMul = g ^ a.val := by
  rw [← zmodLift_natCast, ZMod.natCast_zmod_val]

/-- The `S`-points of `E` killed by `N` are the `S`-points of `E[N]`. -/
private noncomputable def torsionPointsEquiv {S : Scheme.{u}} (E : EllipticCurveGeom S) :
    {x : 𝟙_ (Over S) ⟶ Over.mk E.structureMap // x ^ N = 1} ≃
      (𝟙_ (Over S) ⟶ (E.torsion N).X) :=
  (Equiv.subtypeEquivRight fun x ↦ by
    rw [MonoidHom.mem_ker, IsMonHom.monoidHom_apply, EllipticCurveGeom.comp_mulBy,
      zpow_natCast]).trans (E.torsionPointsMulEquiv N _).symm.toEquiv

@[simp]
private theorem torsionPointsEquiv_torsionι {S : Scheme.{u}} (E : EllipticCurveGeom S)
    (x : {x : 𝟙_ (Over S) ⟶ Over.mk E.structureMap // x ^ N = 1}) :
    torsionPointsEquiv E x ≫ E.torsionι N = x :=
  E.torsionPointsMulEquiv_symm_apply_torsionι N _ _

@[simp]
private theorem coe_torsionPointsEquiv_symm {S : Scheme.{u}} (E : EllipticCurveGeom S)
    (P : 𝟙_ (Over S) ⟶ (E.torsion N).X) :
    ((torsionPointsEquiv E).symm P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) = P ≫ E.torsionι N :=
  E.coe_torsionPointsMulEquiv_apply N _ P

variable [NeZero N]

/-- Homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by `N`, through the image of `1`. -/
private noncomputable def zmodHomEquiv (G : Type*) [Group G] :
    (Multiplicative (ZMod N) →* G) ≃ {g : G // g ^ N = 1} where
  toFun φ := ⟨φ (.ofAdd 1), by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]⟩
  invFun g := (zmodLift g.1 g.2).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = .ofAdd (k : ZMod N) := ⟨z.toAdd.val, by simp⟩
    rw [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
      toAdd_ofAdd, zmodLift_natCast, ← map_pow, ← ofAdd_nsmul, nsmul_one]
  right_inv g := by
    refine Subtype.ext ?_
    dsimp only
    rw [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
      toAdd_ofAdd, zmodLift_one]

/-- Homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of `G` killed by `N`, through the
images of `(1, 0)` and `(0, 1)`. -/
private noncomputable def zmodProdHomEquiv (G : Type*) [CommGroup G] :
    (Multiplicative (ZMod N × ZMod N) →* G) ≃ {g : G // g ^ N = 1} × {g : G // g ^ N = 1} where
  toFun φ := (zmodHomEquiv G (φ.comp (AddMonoidHom.inl _ _).toMultiplicative),
    zmodHomEquiv G (φ.comp (AddMonoidHom.inr _ _).toMultiplicative))
  invFun g := ((zmodLift g.1.1 g.1.2).coprod (zmodLift g.2.1 g.2.2)).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, z = .ofAdd ((a : ZMod N), (b : ZMod N)) :=
      ⟨z.toAdd.1.val, z.toAdd.2.val, by simp⟩
    have hab : ((a : ZMod N), (b : ZMod N)) = a • (1, 0) + b • (0, 1) := by ext <;> simp
    rw [hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
    simp [zmodHomEquiv, zmodLift_one]
  right_inv g := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [zmodHomEquiv, zmodLift_one]

/-- **Naive `[Γ₁(N)]`-structures are points of `E[N]`.** For `N ≠ 0`, a naive
`[Γ₁(N)]`-structure `φ` on `(E/S)` is determined by the `S`-point `P = φ 1` of `E[N]`, and the
`S`-points of `E[N]` arising this way are those of exact order `N` in every fibre: none of
`P, 2P, …, (N - 1)P` meets the zero section (`EllipticCurveGeom.isFiberwiseInjective_zmod_iff`). -/
noncomputable def gammaOneNaiveEquiv (X : EllObj B) :
    (gammaOneNaive B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X //
        ∀ k : ℕ, 0 < k → k < N → ∀ s, ((P ≫ X.curve.torsionι N) ^ k).left s ≠ X.curve.zero s} :=
  (naiveLevelEquiv X).trans <|
    ((zmodHomEquiv _).trans (torsionPointsEquiv X.curve)).subtypeEquiv fun φ ↦ by
      rw [EllipticCurveGeom.isFiberwiseInjective_zmod_iff]
      simp [zmodHomEquiv]

/-- The `S`-point of `E[N]` of a naive `[Γ₁(N)]`-structure `φ` is `φ 1`. -/
@[simp]
theorem gammaOneNaiveEquiv_apply_torsionι (X : EllObj B) (α : (gammaOneNaive B N).obj (op X)) :
    (gammaOneNaiveEquiv X α).1 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd 1) :=
  torsionPointsEquiv_torsionι _ _

/-- The naive `[Γ₁(N)]`-structure of an `S`-point `P` of `E[N]` sends `a` to `aP`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneNaiveEquiv_symm_apply (X : EllObj B)
    (P : {P : 𝟙_ (Over X.base) ⟶ (X.curve.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ s, ((P ≫ X.curve.torsionι N) ^ k).left s ≠ X.curve.zero s})
    (a : ZMod N) :
    (naiveLevelEquiv X ((gammaOneNaiveEquiv X).symm P)).1 (.ofAdd a) =
      (P.1 ≫ X.curve.torsionι N) ^ a.val := by
  simp [gammaOneNaiveEquiv, zmodHomEquiv, zmodLift_apply]

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
  (naiveLevelEquiv X).trans <| ((zmodProdHomEquiv _).trans
    ((torsionPointsEquiv X.curve).prodCongr (torsionPointsEquiv X.curve))).subtypeEquiv fun φ ↦ by
      rw [EllipticCurveGeom.isFiberwiseInjective_zmod_prod_iff]
      simp [zmodProdHomEquiv, zmodHomEquiv]

/-- The first `S`-point `P` of `E[N]` of a naive `[Γ(N)]`-structure `φ` is `φ (1, 0)`. -/
@[simp]
theorem gammaNaiveEquiv_apply_fst_torsionι (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X α).1.1 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd (1, 0)) :=
  torsionPointsEquiv_torsionι _ _

/-- The second `S`-point `Q` of `E[N]` of a naive `[Γ(N)]`-structure `φ` is `φ (0, 1)`. -/
@[simp]
theorem gammaNaiveEquiv_apply_snd_torsionι (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaNaiveEquiv X α).1.2 ≫ X.curve.torsionι N = (naiveLevelEquiv X α).1 (.ofAdd (0, 1)) :=
  torsionPointsEquiv_torsionι _ _

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
  simp [gammaNaiveEquiv, zmodProdHomEquiv, zmodLift_apply]

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

end ModuliProblem

end TauCeti.AlgebraicGeometry
