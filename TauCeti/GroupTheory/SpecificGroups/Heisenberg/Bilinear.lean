/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# The Heisenberg extension of a bilinear map

A bilinear map `B : W × W → C` between additive groups is biadditive, so read multiplicatively it
is a factor set of `W` with values in `C` for the trivial action. The central extension it builds,
`E_B`, has underlying set `C × W`, written in coefficient-first coordinates `(t, w)`, and group law

  `(t, w) * (s, v) = (t + s + B(w, v), w + v)`.

For a symplectic form `ω` and `2` invertible, `E_{½ω}` is the Heisenberg group `H(W)` of the
symplectic space `W`: the group on which the Schrödinger and Weil representations live. Its
commutator is `ω` itself, and when `ω` is nondegenerate its center is exactly the coefficient
group. Choosing instead a non-alternating `B` with `B - Bᵀ = ω` (for instance `B(x + y, x' + y') =
ω(x, y')` on a polarization `W = X ⊕ Y`) gives an isomorphic group in different coordinates, the
isomorphism correcting the coefficient by the quadratic form `½B(w, w)`.

The constructions are those of the Tau Ceti factor-set API: the extension, its coefficient
inclusion, projection and canonical section are `TauCeti.FactorSet.Extension`,
`TauCeti.FactorSet.inl`, `TauCeti.FactorSet.rightHom` and `TauCeti.FactorSet.canonicalSection` of
`LinearMap.BilinMap.factorSet B`. Homomorphisms out of `E_B` that read off the coefficient, such as
the central characters `(t, w) ↦ ψ(t)` of a character `ψ` killing every value of `B`, are
`TauCeti.FactorSet.extendHom`. The canonical Heisenberg group of triples, `TauCeti.HeisenbergGroup`,
corresponds in the coordinates `(z, (x, y))` to the extension of the form
`((x, y), (x', y')) ↦ x * y'` on `R × R`.

The trivial action of `Multiplicative W` on `Multiplicative C` is the local instance
`TauCeti.trivialMulDistribMulAction`; statements about these extensions need it in scope.

## Main definitions

* `LinearMap.BilinMap.factorSet`: the factor set `(w, v) ↦ B(w, v)` of a bilinear map.
* `LinearMap.BilinMap.polarizationEquiv`: the equivalence of extensions
  `E_{½(B - Bᵀ)} ≃ E_B`, `(t, w) ↦ (t + ½B(w, w), w)`.
* `LinearMap.BilinForm.IsometryEquiv.extensionCongr`: the isomorphism `E_B ≃* E_D`,
  `(t, w) ↦ (t, e w)`, induced by an isometry `e : B ≃ D` of scalar bilinear forms.
* `LinearMap.BilinForm.isometryGroupToMulAut`: the action of the isometry group of `B` on `E_B`.

## Main results

* `LinearMap.BilinMap.toAdd_mul_left` and `LinearMap.BilinMap.toAdd_inv_left`: the coefficient
  coordinates of products and inverses.
* `LinearMap.BilinMap.commutatorElement_eq_inl`: the commutator of `(t, w)` and `(s, v)` is
  `(B(w, v) - B(v, w), 0)`.
* `LinearMap.BilinMap.mem_center_iff` and `LinearMap.BilinMap.center_eq_range_inl_iff`: `(t, w)` is
  central exactly when `B(w, ·) = B(·, w)`, so the center is the coefficient group exactly when
  `B - Bᵀ` is left-separating.
* `LinearMap.BilinMap.commutatorElement_invOf_two_smul_eq_inl` and
  `LinearMap.BilinMap.center_invOf_two_smul_eq_range_inl`: for alternating `ω` the commutator in
  `E_{½ω}` is `ω`, and for left-separating `ω` the center of `E_{½ω}` is the coefficient group.
* `LinearMap.BilinMap.factorSet_invOf_two_smul_sub_flip_mul`: the factor sets of `½(B - Bᵀ)` and
  of `B` differ by the coboundary of `w ↦ ½B(w, w)`.
* `LinearMap.BilinForm.isometryGroupToMulAut_injective`: the isometry action is faithful.

## References

* S. S. Kudla, *Notes on the local theta correspondence*, lecture notes (1996), §I.1, p. 3, for
  the bilinear extensions, their commutators and centers, and §I.2, p. 6, for the polarized
  coordinates and central characters.
* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), §3, equation (3),
  for the quadratic correction between the two cocycles.
-/

public section

open Multiplicative TauCeti
open scoped commutatorElement

attribute [local instance] trivialMulDistribMulAction

namespace LinearMap.BilinMap

variable {R W C : Type*} [CommSemiring R] [AddCommGroup W] [Module R W] [AddCommGroup C]
  [Module R C]

/-- **The factor set of a bilinear map**: `(w, v) ↦ B(w, v)`, read multiplicatively, as a factor set
of `W` with values in `C` for the trivial action. The cocycle identity is biadditivity of `B`. Its
extension `E_B` has law `(t, w) * (s, v) = (t + s + B(w, v), w + v)`
(`LinearMap.BilinMap.toAdd_mul_left`). -/
def factorSet (B : LinearMap.BilinMap R W C) : FactorSet (Multiplicative W) (Multiplicative C) :=
  FactorSet.ofBimultiplicative
    { toFun w := AddMonoidHom.toMultiplicative (B w.toAdd).toAddMonoidHom
      map_one' := by ext; simp
      map_mul' w v := by ext; simp }
    trivialMulDistribMulAction_smul

variable (B : LinearMap.BilinMap R W C)

@[simp]
theorem factorSet_apply (p : Multiplicative W × Multiplicative W) :
    B.factorSet p = ofAdd (B p.1.toAdd p.2.toAdd) :=
  FactorSet.ofBimultiplicative_apply _ _ p

/-! ### The group law -/

/-- The coefficient coordinate of a product in `E_B` is `t + s + B(w, v)`. -/
theorem toAdd_mul_left (p q : B.factorSet.Extension) :
    (p * q).left.toAdd = p.left.toAdd + q.left.toAdd + B p.right.toAdd q.right.toAdd := by
  simp

/-- The coefficient coordinate of an inverse in `E_B` is `B(w, w) - t`; the quotient coordinate is
`-w` by `TauCeti.FactorSet.Extension.inv_right`. -/
theorem toAdd_inv_left (p : B.factorSet.Extension) :
    p⁻¹.left.toAdd = B p.right.toAdd p.right.toAdd - p.left.toAdd := by
  simp [sub_eq_add_neg]

/-- **The commutator in `E_B`**: `⁅(t, w), (s, v)⁆ = (B(w, v) - B(v, w), 0)`, with the convention
`⁅p, q⁆ = p * q * p⁻¹ * q⁻¹`. -/
theorem commutatorElement_eq_inl (p q : B.factorSet.Extension) :
    ⁅p, q⁆ = FactorSet.inl _
      (ofAdd (B p.right.toAdd q.right.toAdd - B q.right.toAdd p.right.toAdd)) := by
  rw [FactorSet.commutatorElement_eq_inl _ trivialMulDistribMulAction_smul, factorSet_apply,
    factorSet_apply, ofAdd_sub]

/-- **The center criterion**: `(t, w)` is central in `E_B` exactly when `B(w, v) = B(v, w)` for
every `v`. -/
theorem mem_center_iff {p : B.factorSet.Extension} :
    p ∈ Subgroup.center B.factorSet.Extension ↔ ∀ v, B p.right.toAdd v = B v p.right.toAdd := by
  have key (q : B.factorSet.Extension) :
      q * p = p * q ↔ B p.right.toAdd q.right.toAdd = B q.right.toAdd p.right.toAdd := by
    rw [eq_comm, ← commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_inl,
      map_eq_one_iff _ (FactorSet.inl_injective _), ofAdd_eq_one, sub_eq_zero]
  simp only [Subgroup.mem_center_iff, key]
  exact ⟨fun h v => h ⟨1, ofAdd v⟩, fun h q => h _⟩

/-- **The center of `E_B` is the coefficient group exactly when `B - Bᵀ` is left-separating**, that
is, when no nonzero `w` has `B(w, ·) = B(·, w)`. -/
theorem center_eq_range_inl_iff :
    Subgroup.center B.factorSet.Extension = (FactorSet.inl B.factorSet).range ↔
      (B - B.flip).SeparatingLeft := by
  have hinl (p : B.factorSet.Extension) : p ∈ (FactorSet.inl B.factorSet).range ↔ p.right = 1 := by
    rw [FactorSet.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, FactorSet.rightHom_apply]
  constructor
  · intro h w hw
    have hc : (⟨1, ofAdd w⟩ : B.factorSet.Extension) ∈ Subgroup.center _ :=
      mem_center_iff B |>.2 fun v => sub_eq_zero.1 (hw v)
    rw [h, hinl] at hc
    exact ofAdd_eq_one.1 hc
  · intro h
    ext p
    rw [mem_center_iff, hinl, ← toAdd_eq_zero]
    exact ⟨fun hp => h _ fun v => sub_eq_zero.2 (hp v), fun hp v => by simp [hp]⟩

/-! ### The Heisenberg group of an alternating form -/

section Half

variable [Invertible (2 : R)] {ω : LinearMap.BilinMap R W C}

/-- **The commutator in the Heisenberg group**: for alternating `ω` and `2` invertible, the
commutator of `(t, w)` and `(s, v)` in `E_{½ω}` is `(ω(w, v), 0)`. -/
theorem commutatorElement_invOf_two_smul_eq_inl (hω : ω.IsAlt)
    (p q : ((⅟2 : R) • ω).factorSet.Extension) :
    ⁅p, q⁆ = FactorSet.inl _ (ofAdd (ω p.right.toAdd q.right.toAdd)) := by
  rw [commutatorElement_eq_inl, hω.invOf_two_smul_apply_sub_apply]

/-- **The center of the Heisenberg group**: for alternating left-separating `ω` and `2` invertible,
the center of `E_{½ω}` is exactly the coefficient group. -/
theorem center_invOf_two_smul_eq_range_inl (hω : ω.IsAlt) (hs : ω.SeparatingLeft) :
    Subgroup.center ((⅟2 : R) • ω).factorSet.Extension =
      (FactorSet.inl ((⅟2 : R) • ω).factorSet).range := by
  refine (center_eq_range_inl_iff _).2 fun w hw => hs w fun v => ?_
  rw [← hω.invOf_two_smul_sub_flip]
  exact hw v

/-- **The quadratic correction between Heisenberg cocycles**: the factor sets of `½(B - Bᵀ)` and of
`B` differ by the coboundary of `q(w) = ½B(w, w)`. Additively,
`½(B(w, v) - B(v, w)) + q(w + v) = B(w, v) + q(v) + q(w)`. -/
theorem factorSet_invOf_two_smul_sub_flip_mul (w v : Multiplicative W) :
    ((⅟2 : R) • (B - B.flip)).factorSet (w, v) *
        ofAdd ((⅟2 : R) • B (w * v).toAdd (w * v).toAdd) =
      B.factorSet (w, v) *
        (ofAdd ((⅟2 : R) • B v.toAdd v.toAdd) * ofAdd ((⅟2 : R) • B w.toAdd w.toAdd)) := by
  apply toAdd.injective
  simp only [factorSet_apply, toAdd_mul, toAdd_ofAdd, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.flip_apply, map_add, LinearMap.add_apply, smul_add, smul_sub]
  conv_rhs => rw [← invOf_two_smul_add_invOf_two_smul R (B w.toAdd v.toAdd)]
  abel

/-- **Polarized Heisenberg coordinates**: the equivalence of extensions `E_{½(B - Bᵀ)} ≃ E_B`,
`(t, w) ↦ (t + ½B(w, w), w)`, rescaling the canonical section by the quadratic form `½B(w, w)`. It
fixes the coefficient group and the projection to `W` by construction. -/
def polarizationEquiv :
    ((⅟2 : R) • (B - B.flip)).factorSet.groupExtension.Equiv B.factorSet.groupExtension :=
  FactorSet.rescaleEquiv _ _ (fun w => ofAdd ((⅟2 : R) • B w.toAdd w.toAdd))
    (factorSet_invOf_two_smul_sub_flip_mul B)

@[simp]
theorem polarizationEquiv_apply (p : ((⅟2 : R) • (B - B.flip)).factorSet.Extension) :
    polarizationEquiv B p = ⟨p.left * ofAdd ((⅟2 : R) • B p.right.toAdd p.right.toAdd), p.right⟩ :=
  FactorSet.rescaleEquiv_apply _ _ _ _ p

@[simp]
theorem polarizationEquiv_symm_apply (p : B.factorSet.Extension) :
    (polarizationEquiv B).symm p = ⟨p.left * (ofAdd ((⅟2 : R) • B p.right.toAdd p.right.toAdd))⁻¹,
      p.right⟩ :=
  FactorSet.rescaleEquiv_symm_apply _ _ _ _ p

end Half

end LinearMap.BilinMap

/-! ### Isometries -/

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R W W' W'' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
  [Module R W'] [AddCommGroup W''] [Module R W'']
  {B : BilinForm R W} {D : BilinForm R W'} {D' : BilinForm R W''}

namespace IsometryEquiv

/-- **The isomorphism of extensions induced by an isometry**: an isometry `e : B ≃ D` of scalar
bilinear forms gives `E_B ≃* E_D`, `(t, w) ↦ (t, e w)`, fixing the coefficient group
(`LinearMap.BilinForm.IsometryEquiv.extensionCongr_inl`). -/
def extensionCongr (e : B.IsometryEquiv D) :
    B.factorSet.Extension ≃* D.factorSet.Extension where
  toFun p := ⟨p.left, ofAdd (e p.right.toAdd)⟩
  invFun p := ⟨p.left, ofAdd (e.symm p.right.toAdd)⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_mul' p q := by ext <;> simp [e.map_app]

@[simp]
theorem extensionCongr_apply (e : B.IsometryEquiv D) (p : B.factorSet.Extension) :
    e.extensionCongr p = ⟨p.left, ofAdd (e p.right.toAdd)⟩ :=
  (rfl)

@[simp]
theorem extensionCongr_symm (e : B.IsometryEquiv D) :
    e.extensionCongr.symm = e.symm.extensionCongr :=
  (rfl)

@[simp]
theorem extensionCongr_refl : (IsometryEquiv.refl B).extensionCongr = MulEquiv.refl _ := by
  ext p <;> simp [← coe_toLinearEquiv, toLinearEquiv_refl]

/-- The isomorphism induced by a composite isometry `e.trans f`, which applies `e` first, is the
composite of the induced isomorphisms in the same order. -/
@[simp]
theorem extensionCongr_trans (e : B.IsometryEquiv D) (f : D.IsometryEquiv D') :
    (e.trans f).extensionCongr = e.extensionCongr.trans f.extensionCongr := by
  ext p <;> simp

/-- The isomorphism induced by an isometry fixes the coefficient group. -/
theorem extensionCongr_inl (e : B.IsometryEquiv D) (t : Multiplicative R) :
    e.extensionCongr (FactorSet.inl _ t) = FactorSet.inl _ t := by
  ext <;> simp

end IsometryEquiv

variable (B)

/-- **The isometry action on the Heisenberg extension**: the isometry group of a scalar bilinear
form `B` acts on `E_B` by `(t, w) ↦ (t, g w)`. -/
def isometryGroupToMulAut : isometryGroup B →* MulAut B.factorSet.Extension where
  toFun g := (isometryGroupEquivIsometryEquiv B g).extensionCongr
  map_one' := by ext p <;> simp
  map_mul' g h := by ext p <;> simp

@[simp]
theorem isometryGroupToMulAut_apply (g : isometryGroup B) (p : B.factorSet.Extension) :
    isometryGroupToMulAut B g p = ⟨p.left, ofAdd ((g : W ≃ₗ[R] W) p.right.toAdd)⟩ := by
  simp [isometryGroupToMulAut]

/-- Every isometry fixes the coefficient group of `E_B`. -/
theorem isometryGroupToMulAut_inl (g : isometryGroup B) (t : Multiplicative R) :
    isometryGroupToMulAut B g (FactorSet.inl _ t) = FactorSet.inl _ t := by
  ext <;> simp

/-- **The isometry action on `E_B` is faithful**: an isometry is determined by its action on the
elements `(0, w)`. -/
theorem isometryGroupToMulAut_injective : Function.Injective (isometryGroupToMulAut B) := by
  intro g h hgh
  ext w
  have := congrArg FactorSet.Extension.right (DFunLike.congr_fun hgh ⟨1, ofAdd w⟩)
  simpa using this

end LinearMap.BilinForm
