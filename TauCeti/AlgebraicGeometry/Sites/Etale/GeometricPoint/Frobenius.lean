/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.FiniteEtale
public import TauCeti.FieldTheory.Finite.Frobenius

/-!
# Stalk Frobenius at geometric points over a finite field

Let `k` be a finite field of cardinality `q = Nat.card k`, let `a : Spec (.of k) ⟶ S` be a
`k`-rational point of a scheme `S`, and let `kbar` be an algebraically closed algebraic extension
of `k`. The geometric point `ofOver a kbar` carries two canonical Galois automorphisms of its
stalk functor `(Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber`:

* **`stalkFrobenius a kbar`** (Stacks Project, Tag 03SW): the action of `Spec Φ`, where
  `Φ = (FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).symm` is the geometric Frobenius, the
  inverse of the arithmetic Frobenius `x ↦ x ^ q`.
* **`stalkArithmeticFrobenius a kbar`**: the action of `Spec` of the arithmetic Frobenius
  `x ↦ x ^ q` (`FiniteField.frobeniusAlgEquivOfAlgebraic k kbar`), which is the inverse of
  `stalkFrobenius a kbar`.

Over `Spec (.of k)`, we compute the action of both automorphisms on stalks of finite étale sheaves:

* On `FiniteEtaleScheme.toSheaf` of `Spec B` (`B : CommAlgCat.FiniteEtale k`) or of any finite
  étale `k`-scheme `X`, `stalkArithmeticFrobenius` raises coordinate values to the `q`-th power
  and `stalkFrobenius` extracts their `q`-th roots
  (`toSheafSpecStalkEquiv_stalkArithmeticFrobenius`, `toSheafSpecStalkEquiv_stalkFrobenius_pow`).
* On the stalk `rootsOfUnity n kbar` of a Kummer cover `Spec k[x]/(x ^ n - t)` over `1`,
  `stalkArithmeticFrobenius` acts by `ζ ↦ ζ ^ q`, while whenever `m * q ≡ 1 [MOD n]`,
  `stalkFrobenius` acts by `ζ ↦ ζ ^ m`
  (`kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_of_mul_modEq`).
* On the stalk of a finite field extension `Spec L ⟶ Spec k`, every germ has exact period
  `Module.finrank k L` under `stalkFrobenius` (`stalkFrobenius_pow_app_eq_iff`); in particular, for
  a quadratic extension (`Module.finrank k L = 2`), `stalkFrobenius` is a fixed-point-free
  involution and coincides with `stalkArithmeticFrobenius` on that stalk.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkFrobenius`: the geometric Frobenius
  automorphism of the stalk functor at `ofOver a kbar` (Stacks, Tag 03SW).
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkArithmeticFrobenius`: the arithmetic
  Frobenius automorphism of the stalk functor at `ofOver a kbar`.

## Main results

* `stalkArithmeticFrobenius_eq_inv`, `stalkFrobenius_eq_inv`: the arithmetic and geometric stalk
  Frobenius automorphisms are inverses of each other.
* `toSheafSpecStalkEquiv_stalkArithmeticFrobenius`, `toSheafSpecStalkEquiv_stalkFrobenius_pow`:
  formulae for the Frobenius action on stalks of affine finite étale covers.
* `kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_of_mul_modEq`: on `rootsOfUnity n kbar`,
  `stalkFrobenius` acts by `ζ ↦ ζ ^ m` whenever `m * Nat.card k ≡ 1 [MOD n]`.
* `stalkFrobenius_pow_app_eq_iff`, `stalkFrobenius_involutive_of_finrank_eq_two`,
  `stalkFrobenius_ne_self_of_one_lt_finrank`: exact period of `stalkFrobenius` on the stalk of a
  finite field extension `Spec L ⟶ Spec k`.

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
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  [IsSepClosed kbar]
variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The stalk Frobenius** at a `k`-rational point `a : Spec (.of k) ⟶ S` (with `k` finite) and
the geometric point `ofOver a kbar` (Stacks Project, Tag 03SW): the automorphism of the stalk
functor induced by `Spec Φ`, where `Φ` is the geometric Frobenius, the inverse of the arithmetic
Frobenius `x ↦ x ^ Nat.card k`. -/
noncomputable def stalkFrobenius :
    Aut ((Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber (A := A)) :=
  let _ := Fintype.ofFinite k
  galStalkAut a kbar (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).symm

/-- The automorphism of the stalk functor at `ofOver a kbar` induced by `Spec` of the arithmetic
Frobenius `x ↦ x ^ Nat.card k` (`FiniteField.frobeniusAlgEquivOfAlgebraic k kbar`), which is the
inverse of `stalkFrobenius a kbar`. -/
noncomputable def stalkArithmeticFrobenius :
    Aut ((Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber (A := A)) :=
  let _ := Fintype.ofFinite k
  galStalkAut a kbar (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar)

/-- The arithmetic Frobenius acts on stalks by the inverse of `stalkFrobenius`. -/
theorem stalkArithmeticFrobenius_eq_inv :
    stalkArithmeticFrobenius a kbar (A := A) = (stalkFrobenius a kbar (A := A))⁻¹ := by
  rw [stalkArithmeticFrobenius, stalkFrobenius, ← map_inv]
  rfl

/-- `stalkFrobenius` is the inverse of `stalkArithmeticFrobenius`. -/
theorem stalkFrobenius_eq_inv :
    stalkFrobenius a kbar (A := A) = (stalkArithmeticFrobenius a kbar (A := A))⁻¹ := by
  rw [stalkArithmeticFrobenius_eq_inv, inv_inv]

/-- `stalkFrobenius` and `stalkArithmeticFrobenius` multiply to `1` on the right. -/
@[simp]
theorem stalkFrobenius_mul_stalkArithmeticFrobenius :
    stalkFrobenius a kbar (A := A) * stalkArithmeticFrobenius a kbar (A := A) = 1 := by
  rw [stalkArithmeticFrobenius_eq_inv, mul_inv_cancel]

/-- `stalkArithmeticFrobenius` and `stalkFrobenius` multiply to `1` on the right. -/
@[simp]
theorem stalkArithmeticFrobenius_mul_stalkFrobenius :
    stalkArithmeticFrobenius a kbar (A := A) * stalkFrobenius a kbar (A := A) = 1 := by
  rw [stalkArithmeticFrobenius_eq_inv, inv_mul_cancel]

/-- The forward natural transformation of `stalkFrobenius` is the stalk map of geometric
Frobenius. -/
theorem stalkFrobenius_asIso_hom [Fintype k] :
    (stalkFrobenius a kbar (A := A)).asIso.hom =
      ((toPointFunctor S).map
        (homOfAlgHom a kbar
          (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).symm.toAlgHom)).sheafFiber := by
  rw [stalkFrobenius, galStalkAut_asIso_hom, Subsingleton.elim (Fintype.ofFinite k) inferInstance]

/-- The forward natural transformation of `stalkArithmeticFrobenius` is the stalk map of
arithmetic Frobenius. -/
theorem stalkArithmeticFrobenius_asIso_hom [Fintype k] :
    (stalkArithmeticFrobenius a kbar (A := A)).asIso.hom =
      ((toPointFunctor S).map
        (homOfAlgHom a kbar
          (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).toAlgHom)).sheafFiber := by
  rw [stalkArithmeticFrobenius, galStalkAut_asIso_hom,
    Subsingleton.elim (Fintype.ofFinite k) inferInstance]

/-- On any sheaf of sets, `stalkFrobenius` followed by `stalkArithmeticFrobenius` is the
identity. -/
@[simp]
theorem stalkArithmeticFrobenius_app_stalkFrobenius_app
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber.obj F) :
    (stalkArithmeticFrobenius a kbar).asIso.hom.app F
        ((stalkFrobenius a kbar).asIso.hom.app F z) = z := by
  change ((stalkArithmeticFrobenius a kbar * stalkFrobenius a kbar).asIso.hom.app F z) = z
  rw [stalkArithmeticFrobenius_mul_stalkFrobenius]
  rfl

/-- On any sheaf of sets, `stalkArithmeticFrobenius` followed by `stalkFrobenius` is the
identity. -/
@[simp]
theorem stalkFrobenius_app_stalkArithmeticFrobenius_app
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a kbar).hom).sheafFiber.obj F) :
    (stalkFrobenius a kbar).asIso.hom.app F
        ((stalkArithmeticFrobenius a kbar).asIso.hom.app F z) = z := by
  change ((stalkFrobenius a kbar * stalkArithmeticFrobenius a kbar).asIso.hom.app F z) = z
  rw [stalkFrobenius_mul_stalkArithmeticFrobenius]
  rfl

end Definition

section FiniteEtaleAction

variable (k : Type u) [Field k] [Finite k]
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  [IsSepClosed kbar]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of `Spec B`, `stalkArithmeticFrobenius` raises
every coordinate value to the power `Nat.card k`. -/
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
  let _ := Fintype.ofFinite k
  rw [stalkArithmeticFrobenius, toSheafSpecStalkEquiv_galStalkAut, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Nat.card_eq_fintype_card]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of `Spec B`, raising the coordinate values after
applying `stalkFrobenius` to the power `Nat.card k` recovers the original coordinate values. -/
theorem toSheafSpecStalkEquiv_stalkFrobenius_pow (B : CommAlgCat.FiniteEtale.{u} k)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op B))))
    (b : B.obj) :
    (toSheafSpecStalkEquiv k kbar B
        ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            ((FiniteEtaleScheme.spec (.of k)).obj (op B))) z) b) ^ Nat.card k =
      toSheafSpecStalkEquiv k kbar B z b := by
  let _ := Fintype.ofFinite k
  rw [stalkFrobenius, toSheafSpecStalkEquiv_galStalkAut, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, Nat.card_eq_fintype_card]
  exact (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).apply_symm_apply _

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of any finite étale `k`-scheme `X`,
`stalkArithmeticFrobenius` raises every coordinate value to the power `Nat.card k`. -/
theorem toSheafFieldStalkEquiv_stalkArithmeticFrobenius
    (X : FiniteEtaleScheme (Spec (.of k)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X))
    (b : ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
      (.of k)).inverse.obj X).unop.obj) :
    toSheafFieldStalkEquiv k kbar X
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X) z) b =
      (toSheafFieldStalkEquiv k kbar X z b) ^ Nat.card k := by
  let _ := Fintype.ofFinite k
  rw [stalkArithmeticFrobenius, toSheafFieldStalkEquiv_galStalkAut, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Nat.card_eq_fintype_card]

/-- On the stalk of `FiniteEtaleScheme.toSheaf` of any finite étale `k`-scheme `X`, raising the
coordinate values after applying `stalkFrobenius` to the power `Nat.card k` recovers the original
coordinate values. -/
theorem toSheafFieldStalkEquiv_stalkFrobenius_pow
    (X : FiniteEtaleScheme (Spec (.of k)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X))
    (b : ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
      (.of k)).inverse.obj X).unop.obj) :
    (toSheafFieldStalkEquiv k kbar X
        ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj X) z) b) ^ Nat.card k =
      toSheafFieldStalkEquiv k kbar X z b := by
  let _ := Fintype.ofFinite k
  rw [stalkFrobenius, toSheafFieldStalkEquiv_galStalkAut, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, Nat.card_eq_fintype_card]
  exact (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).apply_symm_apply _

end FiniteEtaleAction

section Kummer

variable (k : Type u) [Field k] [Finite k]
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  [IsSepClosed kbar]
variable (t : (CommRingCat.of k)ˣ) (n : ℕ) (hn : IsUnit (n : CommRingCat.of k))
  (h : algebraMap k kbar t = 1)

/-- On the stalk `rootsOfUnity n kbar` of a Kummer cover over `1`, `stalkArithmeticFrobenius`
raises every `n`-th root of unity to the power `Nat.card k`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z) ^ Nat.card k := by
  let _ := Fintype.ofFinite k
  apply Subtype.ext
  apply Units.ext
  rw [stalkArithmeticFrobenius, coe_kummerCoverStalkEquivRootsOfUnity_galStalkAut,
    _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card,
    Subgroup.coe_pow, Units.val_pow_eq_pow_val]

/-- On the stalk `rootsOfUnity n kbar` of a Kummer cover over `1`, raising the image of `ζ` under
`stalkFrobenius` to the power `Nat.card k` recovers `ζ`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_pow
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z)) ^ Nat.card k =
      kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z := by
  let _ := Fintype.ofFinite k
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, stalkFrobenius,
    coe_kummerCoverStalkEquivRootsOfUnity_galStalkAut, Nat.card_eq_fintype_card]
  exact (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k kbar).apply_symm_apply _

/-- **Action of `stalkFrobenius` on `μ_n`.** Whenever `m * Nat.card k ≡ 1 [MOD n]`,
`stalkFrobenius` acts on the stalk `rootsOfUnity n kbar` of a Kummer cover over `1` by
`ζ ↦ ζ ^ m`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_of_mul_modEq
    {m : ℕ} (hm : m * Nat.card k ≡ 1 [MOD n])
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
        ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z) ^ m := by
  set ζ' := kummerCoverStalkEquivRootsOfUnity k kbar t n hn h
    ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        (FiniteEtaleScheme.kummerCover t n hn)) z)
  have hpow : ζ' ^ Nat.card k = kummerCoverStalkEquivRootsOfUnity k kbar t n hn h z :=
    kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_pow k kbar t n hn h z
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
variable (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  [IsSepClosed kbar]

/-- **Exact period of arithmetic Frobenius on the stalk of a finite field extension.** For a finite
extension `L / k` of finite fields, the `m`-th power of `stalkArithmeticFrobenius` fixes a germ in
the stalk of `Spec L ⟶ Spec k` if and only if `[L : k] ∣ m`. -/
theorem stalkArithmeticFrobenius_pow_app_eq_iff (m : ℕ)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))) :
    ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z = z ↔
      Module.finrank k L ∣ m := by
  let _ := Fintype.ofFinite k
  let B := finiteEtaleOfSeparableFieldExt k L
  rw [stalkArithmeticFrobenius, ← map_pow, ← (toSheafSpecStalkEquiv k kbar B).injective.eq_iff,
    toSheafSpecStalkEquiv_galStalkAut]
  let φ : L →ₐ[k] kbar := toSheafSpecStalkEquiv k kbar B z
  exact TauCeti.FiniteField.frobeniusAlgEquivOfAlgebraic_pow_comp_eq_iff k kbar φ m

/-- **Exact period of `stalkFrobenius` on the stalk of a finite field extension.** For a finite
extension `L / k` of finite fields, the `m`-th power of `stalkFrobenius` fixes a germ in the stalk
of `Spec L ⟶ Spec k` if and only if `[L : k] ∣ m`. -/
theorem stalkFrobenius_pow_app_eq_iff (m : ℕ)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))) :
    ((stalkFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z = z ↔
      Module.finrank k L ∣ m := by
  let B := finiteEtaleOfSeparableFieldExt k L
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
    ((FiniteEtaleScheme.spec (.of k)).obj (op B))
  rw [← stalkArithmeticFrobenius_pow_app_eq_iff k L kbar m z]
  have hcancel
      (u : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj F) :
      ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F
          (((stalkFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F u) = u := by
    change (((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m *
      (stalkFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F u) = u
    rw [stalkArithmeticFrobenius_eq_inv, inv_pow, inv_mul_cancel]
    rfl
  have hcancel'
      (u : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj F) :
      ((stalkFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F
          (((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F u) = u := by
    change (((stalkFrobenius (𝟙 (Spec (.of k))) kbar) ^ m *
      (stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar) ^ m).asIso.hom.app F u) = u
    rw [stalkArithmeticFrobenius_eq_inv, inv_pow, mul_inv_cancel]
    rfl
  exact ⟨fun h ↦ (congrArg _ h).symm.trans (hcancel z),
    fun h ↦ (congrArg _ h).symm.trans (hcancel' z)⟩

/-- For any nontrivial finite extension `L / k` of finite fields (`1 < [L : k]`), `stalkFrobenius`
has no fixed points on the stalk of `Spec L ⟶ Spec k`. -/
theorem stalkFrobenius_ne_self_of_one_lt_finrank (hdeg : 1 < Module.finrank k L)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))) :
    (stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z ≠
      z := by
  intro h
  have hdvd := (stalkFrobenius_pow_app_eq_iff k L kbar 1 z).mp (by simpa using h)
  exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)

/-- For a quadratic extension `L / k` of finite fields (`[L : k] = 2`), `stalkFrobenius` acts as an
involution on the stalk of `Spec L ⟶ Spec k`. -/
theorem stalkFrobenius_involutive_of_finrank_eq_two (hdeg : Module.finrank k L = 2)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))) :
    (stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))
        ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
            ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z) =
      z := by
  have h2 := (stalkFrobenius_pow_app_eq_iff k L kbar 2 z).mpr (by rw [hdeg])
  rw [pow_two] at h2
  exact h2

/-- For a quadratic extension `L / k` of finite fields (`[L : k] = 2`), `stalkFrobenius` and
`stalkArithmeticFrobenius` agree on the stalk of `Spec L ⟶ Spec k` (an involution equals its own
inverse). -/
theorem stalkFrobenius_eq_stalkArithmeticFrobenius_of_finrank_eq_two
    (hdeg : Module.finrank k L = 2)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of k))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
        ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L))))) :
    (stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z =
      (stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
          ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))) z := by
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of k))).obj
    ((FiniteEtaleScheme.spec (.of k)).obj (op (finiteEtaleOfSeparableFieldExt k L)))
  calc
    (stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z
      = (stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F
          ((stalkFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F
            ((stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z)) := by
        rw [stalkFrobenius_app_stalkArithmeticFrobenius_app]
    _ = (stalkArithmeticFrobenius (𝟙 (Spec (.of k))) kbar).asIso.hom.app F z :=
        stalkFrobenius_involutive_of_finrank_eq_two k L kbar hdeg _

end FiniteFieldExtension

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
