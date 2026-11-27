/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.FiniteEtale
public import TauCeti.FieldTheory.Finite.Frobenius
import TauCeti.CategoryTheory.Aut.Basic

/-!
# Stalk Frobenius at geometric points over a finite field

Let `k` be a finite field of cardinality `q = Nat.card k`, let `a : Spec (.of k) ⟶ S` be a
`k`-valued point of a scheme `S`, and let `kbar` be a separably closed perfect extension of `k`
(`[IsSepClosed kbar] [PerfectField kbar]`, covering both algebraic closures of `k` and geometric
points such as `AlgebraicClosure (RatFunc k)`). The geometric point `ofOver a kbar` carries two
canonical Galois automorphisms of its stalk functor
`(Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber`:

* **`stalkGeometricFrobenius a kbar`** (Stacks Project, Tag 03SW): the action of `Spec Φ`, where
  `Φ = (TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar).symm` is the geometric Frobenius,
  the inverse of the arithmetic Frobenius `x ↦ x ^ q`.
* **`stalkArithmeticFrobenius a kbar`**: the action of `Spec` of the arithmetic Frobenius
  `x ↦ x ^ q` (`TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar`), which is the inverse of
  `stalkGeometricFrobenius a kbar`.

Over `Spec (.of k)`, we compute the action of both automorphisms on stalks of finite étale sheaves:

* On `FiniteEtaleScheme.toSheaf` of `Spec B` (`B : CommAlgCat.FiniteEtale k`) or of any finite
  étale `k`-scheme `X`, `stalkArithmeticFrobenius` raises coordinate values to the `q`-th power
  and `stalkGeometricFrobenius` extracts their `q`-th roots
  (`toSheafSpecStalkEquiv_stalkArithmeticFrobenius`,
  `toSheafSpecStalkEquiv_stalkGeometricFrobenius_apply_pow_card`,
  `toSheafStalkEquiv_stalkArithmeticFrobenius`,
  `toSheafStalkEquiv_stalkGeometricFrobenius_apply_pow_card`).
* On the stalk `rootsOfUnity n kbar` of a Kummer cover `Spec k[x]/(x ^ n - t)` over `1`,
  `stalkArithmeticFrobenius` acts by `ζ ↦ ζ ^ q`, while whenever `m * q ≡ 1 [MOD n]`,
  `stalkGeometricFrobenius` acts by `ζ ↦ ζ ^ m`
  (`kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_of_mul_modEq`).
* On the stalk of a finite field extension `Spec L ⟶ Spec k`, every germ has exact period
  `Module.finrank k L` under `stalkGeometricFrobenius`
  (`stalkGeometricFrobenius_pow_app_eq_iff`); in particular, for a quadratic extension
  (`Module.finrank k L = 2`), `stalkGeometricFrobenius` is a fixed-point-free involution and
  coincides with `stalkArithmeticFrobenius` on that stalk.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkGeometricFrobenius`: the geometric
  Frobenius automorphism of the stalk functor at `ofOver a kbar` (Stacks, Tag 03SW).
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkArithmeticFrobenius`: the arithmetic
  Frobenius automorphism of the stalk functor at `ofOver a kbar`.

## Main results

* `stalkArithmeticFrobenius_eq_inv`, `stalkGeometricFrobenius_eq_inv`: the arithmetic and geometric
  stalk Frobenius automorphisms are inverses of each other.
* `toSheafSpecStalkEquiv_stalkArithmeticFrobenius`,
  `toSheafSpecStalkEquiv_stalkGeometricFrobenius_apply_pow_card`,
  `toSheafStalkEquiv_stalkArithmeticFrobenius`,
  `toSheafStalkEquiv_stalkGeometricFrobenius_apply_pow_card`:
  formulae for the Frobenius action on stalks of finite étale covers.
* `kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_of_mul_modEq`: on
  `rootsOfUnity n kbar`, `stalkGeometricFrobenius` acts by `ζ ↦ ζ ^ m` whenever
  `m * Nat.card k ≡ 1 [MOD n]`.
* `stalkGeometricFrobenius_pow_app_eq_iff`, `stalkGeometricFrobenius_involutive_of_finrank_eq_two`,
  `stalkGeometricFrobenius_ne_self_of_one_lt_finrank`: exact period of `stalkGeometricFrobenius`
  on the stalk of a finite field extension `Spec L ⟶ Spec k`.

## References

* The Stacks Project, [Tag 03SW](https://stacks.math.columbia.edu/tag/03SW).
* P. Deligne, *Cohomologie étale (SGA 4½)*, Rapport sur la formule des traces.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section Definition

variable {S : Scheme.{u}} {k : Type u} [Field k] [Finite k] (a : Spec (.of k) ⟶ S)
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [PerfectField kbar] [IsSepClosed kbar]
variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The geometric stalk Frobenius** at a `k`-valued point `a : Spec (.of k) ⟶ S` (with `k`
finite) and the geometric point `ofOver a kbar` (Stacks Project, Tag 03SW): the automorphism of the
stalk functor induced by `Spec Φ`, where `Φ` is the geometric Frobenius, the inverse of the
arithmetic Frobenius `x ↦ x ^ Nat.card k`. -/
noncomputable def stalkGeometricFrobenius :
    Aut ((Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber (A := A)) :=
  ofOverGaloisStalkAction a kbar (TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar).symm

/-- The automorphism of the stalk functor at `ofOver a kbar` induced by `Spec` of the arithmetic
Frobenius `x ↦ x ^ Nat.card k` (`TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar`), which is
the inverse of `stalkGeometricFrobenius a kbar`. -/
noncomputable def stalkArithmeticFrobenius :
    Aut ((Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber (A := A)) :=
  ofOverGaloisStalkAction a kbar (TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar)

/-- The arithmetic Frobenius acts on stalks by the inverse of `stalkGeometricFrobenius`. -/
theorem stalkArithmeticFrobenius_eq_inv :
    stalkArithmeticFrobenius a kbar (A := A) = (stalkGeometricFrobenius a kbar (A := A))⁻¹ := by
  rw [stalkArithmeticFrobenius, stalkGeometricFrobenius, ← map_inv, AlgEquiv.aut_inv,
    AlgEquiv.symm_symm]

/-- `stalkGeometricFrobenius` is the inverse of `stalkArithmeticFrobenius`. -/
theorem stalkGeometricFrobenius_eq_inv :
    stalkGeometricFrobenius a kbar (A := A) = (stalkArithmeticFrobenius a kbar (A := A))⁻¹ := by
  rw [stalkArithmeticFrobenius_eq_inv, inv_inv]

/-- `stalkArithmeticFrobenius` is the right inverse of `stalkGeometricFrobenius`. -/
@[simp]
theorem stalkGeometricFrobenius_mul_stalkArithmeticFrobenius :
    stalkGeometricFrobenius a kbar (A := A) * stalkArithmeticFrobenius a kbar (A := A) = 1 := by
  rw [stalkArithmeticFrobenius_eq_inv, mul_inv_cancel]

/-- `stalkArithmeticFrobenius` is the left inverse of `stalkGeometricFrobenius`. -/
@[simp]
theorem stalkArithmeticFrobenius_mul_stalkGeometricFrobenius :
    stalkArithmeticFrobenius a kbar (A := A) * stalkGeometricFrobenius a kbar (A := A) = 1 := by
  rw [stalkArithmeticFrobenius_eq_inv, inv_mul_cancel]

/-- The forward natural transformation of `stalkGeometricFrobenius` is the stalk map of geometric
Frobenius. -/
theorem stalkGeometricFrobenius_asIso_hom :
    (stalkGeometricFrobenius a kbar (A := A)).asIso.hom =
      ((toPointFunctor S).map
        (homOfAlgHom a
          (TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar).symm.toAlgHom)).sheafFiber := by
  rw [stalkGeometricFrobenius, ofOverGaloisStalkAction_asIso_hom]

/-- The forward natural transformation of `stalkArithmeticFrobenius` is the stalk map of
arithmetic Frobenius. -/
theorem stalkArithmeticFrobenius_asIso_hom :
    (stalkArithmeticFrobenius a kbar (A := A)).asIso.hom =
      ((toPointFunctor S).map
        (homOfAlgHom a
          (TauCeti.FiniteField.frobeniusAlgEquivOfFinite k kbar).toAlgHom)).sheafFiber := by
  rw [stalkArithmeticFrobenius, ofOverGaloisStalkAction_asIso_hom]

/-- On any sheaf of sets, `stalkGeometricFrobenius` followed by `stalkArithmeticFrobenius` is the
identity. -/
@[simp]
theorem stalkArithmeticFrobenius_app_stalkGeometricFrobenius_app
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber.obj F) :
    (stalkArithmeticFrobenius a kbar).asIso.hom.app F
        ((stalkGeometricFrobenius a kbar).asIso.hom.app F z) = z := by
  rw [← Aut.functor_mul_asIso_hom_app_apply, stalkArithmeticFrobenius_mul_stalkGeometricFrobenius,
    Aut.functor_one_asIso_hom_app_apply]

/-- On any sheaf of sets, `stalkArithmeticFrobenius` followed by `stalkGeometricFrobenius` is the
identity. -/
@[simp]
theorem stalkGeometricFrobenius_app_stalkArithmeticFrobenius_app
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber.obj F) :
    (stalkGeometricFrobenius a kbar).asIso.hom.app F
        ((stalkArithmeticFrobenius a kbar).asIso.hom.app F z) = z := by
  rw [← Aut.functor_mul_asIso_hom_app_apply, stalkGeometricFrobenius_mul_stalkArithmeticFrobenius,
    Aut.functor_one_asIso_hom_app_apply]

end Definition

section FiniteEtaleAction

variable (k : Type u) [Field k] [Finite k]
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [PerfectField kbar] [IsSepClosed kbar]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of `Spec B`, `stalkArithmeticFrobenius` raises
every coordinate value to the power `Nat.card k`. -/
@[simp]
theorem toSheafSpecStalkEquiv_stalkArithmeticFrobenius (B : CommAlgCat.FiniteEtale.{u} k)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op B))))
    (b : B.obj) :
    toSheafSpecStalkEquiv k kbar B
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            ((FiniteEtaleScheme.spec (.of k)).obj (op B))) z) b =
      (toSheafSpecStalkEquiv k kbar B z b) ^ Nat.card k := by
  rw [stalkArithmeticFrobenius, toSheafSpecStalkEquiv_ofOverGaloisStalkAction, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, TauCeti.FiniteField.frobeniusAlgEquivOfFinite_apply]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of `Spec B`, raising the coordinate values after
applying `stalkGeometricFrobenius` to the power `Nat.card k` recovers the original coordinate
values. -/
theorem toSheafSpecStalkEquiv_stalkGeometricFrobenius_apply_pow_card
    (B : CommAlgCat.FiniteEtale.{u} k)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op B))))
    (b : B.obj) :
    (toSheafSpecStalkEquiv k kbar B
        ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            ((FiniteEtaleScheme.spec (.of k)).obj (op B))) z) b) ^ Nat.card k =
      toSheafSpecStalkEquiv k kbar B z b := by
  rw [stalkGeometricFrobenius, toSheafSpecStalkEquiv_ofOverGaloisStalkAction, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, TauCeti.FiniteField.frobeniusAlgEquivOfFinite_symm_apply_pow]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of any finite étale `k`-scheme `X`,
`stalkArithmeticFrobenius` raises every coordinate value to the power `Nat.card k`. -/
@[simp]
theorem toSheafStalkEquiv_stalkArithmeticFrobenius
    (X : FiniteEtaleScheme (Spec (.of k)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X))
    (b : ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
      (.of k)).inverse.obj X).unop.obj) :
    toSheafStalkEquiv k kbar X
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X) z) b =
      (toSheafStalkEquiv k kbar X z b) ^ Nat.card k := by
  rw [stalkArithmeticFrobenius, toSheafStalkEquiv_ofOverGaloisStalkAction, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, TauCeti.FiniteField.frobeniusAlgEquivOfFinite_apply]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of any finite étale `k`-scheme `X`, raising the
coordinate values after applying `stalkGeometricFrobenius` to the power `Nat.card k` recovers the
original coordinate values. -/
theorem toSheafStalkEquiv_stalkGeometricFrobenius_apply_pow_card
    (X : FiniteEtaleScheme (Spec (.of k)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X))
    (b : ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
      (.of k)).inverse.obj X).unop.obj) :
    (toSheafStalkEquiv k kbar X
        ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X) z) b) ^ Nat.card k =
      toSheafStalkEquiv k kbar X z b := by
  rw [stalkGeometricFrobenius, toSheafStalkEquiv_ofOverGaloisStalkAction, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, TauCeti.FiniteField.frobeniusAlgEquivOfFinite_symm_apply_pow]

end FiniteEtaleAction

section Kummer

variable (k : Type u) [Field k] [Finite k]
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [PerfectField kbar] [IsSepClosed kbar]
variable (t : (CommRingCat.of k)ˣ) (n : ℕ) (hn : IsUnit (n : CommRingCat.of k))
  (h : algebraMap k kbar t = 1)

/-- On the stalk `rootsOfUnity n kbar` of a Kummer cover over `1`, `stalkArithmeticFrobenius`
raises every `n`-th root of unity to the power `Nat.card k`. -/
@[simp]
theorem kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z) ^ Nat.card k := by
  apply Subtype.ext
  apply Units.ext
  rw [stalkArithmeticFrobenius, coe_kummerCoverStalkEquivRootsOfUnity_ofOverGaloisStalkAction,
    TauCeti.FiniteField.frobeniusAlgEquivOfFinite_apply, Subgroup.coe_pow,
    Units.val_pow_eq_pow_val]

/-- On the stalk `rootsOfUnity n kbar` of a Kummer cover over `1`, raising the image of `ζ` under
`stalkGeometricFrobenius` to the power `Nat.card k` recovers `ζ`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_apply_pow_card
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z)) ^ Nat.card k =
      kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, stalkGeometricFrobenius,
    coe_kummerCoverStalkEquivRootsOfUnity_ofOverGaloisStalkAction,
    TauCeti.FiniteField.frobeniusAlgEquivOfFinite_symm_apply_pow]

/-- **Action of `stalkGeometricFrobenius` on `μ_n`.** Whenever `m * Nat.card k ≡ 1 [MOD n]`,
`stalkGeometricFrobenius` acts on the stalk `rootsOfUnity n kbar` of a Kummer cover over `1` by
`ζ ↦ ζ ^ m`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_of_mul_modEq
    {m : ℕ} (hm : m * Nat.card k ≡ 1 [MOD n])
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z) ^ m := by
  set ζ' := kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
    ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn)) z)
  have hpow : ζ' ^ Nat.card k = kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z :=
    kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_apply_pow_card k kbar t n hn h z
  have hord : orderOf ζ' ∣ n := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (mem_rootsOfUnity' n _).mp ζ'.prop)
  have hmod : Nat.card k * m ≡ 1 [MOD orderOf ζ'] := by
    rw [mul_comm]
    exact hm.of_dvd hord
  calc ζ' = ζ' ^ 1 := (pow_one ζ').symm
    _ = ζ' ^ (Nat.card k * m) := (pow_eq_pow_iff_modEq.mpr hmod).symm
    _ = (ζ' ^ Nat.card k) ^ m := pow_mul ζ' (Nat.card k) m
    _ = (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z) ^ m := by rw [hpow]

end Kummer

section FiniteFieldExtension

variable (k L : Type u) [Field k] [Finite k] [Field L] [Algebra k L] [Module.Finite k L]
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [PerfectField kbar] [IsSepClosed kbar]

/-- **Period of arithmetic Frobenius on the stalk of a finite field extension.** For a finite
extension `L / k` of finite fields, the `m`-th power of `stalkArithmeticFrobenius` fixes a germ in
the stalk of `Spec L ⟶ Spec k` if and only if `[L : k] ∣ m`. -/
theorem stalkArithmeticFrobenius_pow_app_eq_iff (m : ℕ)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L))))) :
    ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))) z = z ↔
      Module.finrank k L ∣ m := by
  let B := CommAlgCat.FiniteEtale.ofSeparableFieldExt k L
  rw [stalkArithmeticFrobenius, ← map_pow, ← (toSheafSpecStalkEquiv k kbar B).injective.eq_iff,
    toSheafSpecStalkEquiv_ofOverGaloisStalkAction]
  let φ : L →ₐ[k] kbar := toSheafSpecStalkEquiv k kbar B z
  exact TauCeti.FiniteField.frobeniusAlgEquivOfFinite_pow_comp_eq_iff k kbar φ m

/-- **Period of `stalkGeometricFrobenius` on the stalk of a finite field extension.** For a finite
extension `L / k` of finite fields, the `m`-th power of `stalkGeometricFrobenius` fixes a germ in
the stalk of `Spec L ⟶ Spec k` if and only if `[L : k] ∣ m`. -/
theorem stalkGeometricFrobenius_pow_app_eq_iff (m : ℕ)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L))))) :
    ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))) z = z ↔
      Module.finrank k L ∣ m := by
  let B := CommAlgCat.FiniteEtale.ofSeparableFieldExt k L
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
    ((FiniteEtaleScheme.spec (.of k)).obj (op B))
  let e := (((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.app F).toEquiv
  have hgeom :
      ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F z = e.symm z := by
    rw [stalkGeometricFrobenius_eq_inv, inv_pow, Aut.inv_asIso, Iso.symm_hom, ← Iso.app_inv,
      Iso.toEquiv_symm_apply]
  rw [hgeom, e.symm_apply_eq, eq_comm]
  exact stalkArithmeticFrobenius_pow_app_eq_iff k L kbar m z

/-- For any nontrivial finite extension `L / k` of finite fields (`1 < [L : k]`),
`stalkGeometricFrobenius` has no fixed points on the stalk of `Spec L ⟶ Spec k`. -/
theorem stalkGeometricFrobenius_ne_self_of_one_lt_finrank (hdeg : 1 < Module.finrank k L)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L))))) :
    (stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))) z ≠
      z := by
  intro h
  have hdvd := (stalkGeometricFrobenius_pow_app_eq_iff k L kbar 1 z).mp (by simpa using h)
  exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)

/-- For a quadratic extension `L / k` of finite fields (`[L : k] = 2`), `stalkGeometricFrobenius`
acts as an involution on the stalk of `Spec L ⟶ Spec k`. -/
theorem stalkGeometricFrobenius_involutive_of_finrank_eq_two (hdeg : Module.finrank k L = 2) :
    Function.Involutive ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L))))) := by
  intro z
  have h2 := (stalkGeometricFrobenius_pow_app_eq_iff k L kbar 2 z).mpr (by rw [hdeg])
  rw [pow_two, Aut.functor_mul_asIso_hom_app_apply] at h2
  exact h2

/-- For a quadratic extension `L / k` of finite fields (`[L : k] = 2`),
`stalkGeometricFrobenius` and `stalkArithmeticFrobenius` agree on the stalk of `Spec L ⟶ Spec k`
(an involution equals its own inverse). -/
theorem stalkGeometricFrobenius_eq_stalkArithmeticFrobenius_of_finrank_eq_two
    (hdeg : Module.finrank k L = 2)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L))))) :
    (stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))) z =
      (stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))) z := by
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
    ((FiniteEtaleScheme.spec (.of k)).obj (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt k L)))
  calc
    (stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z
      = (stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F
          ((stalkGeometricFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F
            ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z)) := by
        rw [stalkGeometricFrobenius_app_stalkArithmeticFrobenius_app]
    _ = (stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z :=
        stalkGeometricFrobenius_involutive_of_finrank_eq_two k L kbar hdeg _

end FiniteFieldExtension

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
