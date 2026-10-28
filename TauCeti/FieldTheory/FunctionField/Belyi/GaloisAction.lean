/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.FieldTheory.FunctionField.Belyi.Bundled
public import TauCeti.FieldTheory.FunctionField.Belyi.Conjugation

/-!
# The Galois action on isomorphism classes of algebraic Belyi pairs

Let `σ : k ≃+* k'` be an isomorphism of fields of characteristic zero. The **conjugate** of an
algebraic Belyi pair `X = (F, k(t) ↪ F)` along `σ` is the same field `F`, with its embedding of
`k'(t)` precomposed with the coefficient map of `σ⁻¹` (`TauCeti.RatFunc.mapRingEquiv`), and with
the same distinguished function `t`. This is base change of the Belyi map along `σ`; that the
result is again an algebraic Belyi pair is `TauCeti.IsAlgebraicBelyiPair.of_mapRingEquiv`. The
identity of `F` is a ring isomorphism from `X` to its conjugate,
`TauCeti.AlgebraicBelyiPair.conjRingEquiv`, carrying `k(t)` onto `k'(t)` by the coefficient map
of `σ`, so the place-by-place results of `TauCeti.FieldTheory.FunctionField.Belyi.Conjugation`
(marked places, ramification indices and residue degrees) apply to it.

Conjugation is functorial in morphisms of pairs, and on isomorphism classes it is a group action:
any group `G` acting on `k` by ring automorphisms, for instance the absolute Galois group
`Gal(ℚ̄/ℚ)` acting on `ℚ̄`, acts on the isomorphism classes of algebraic Belyi pairs over `k`, by
`g • [X] = [X conjugated along g]`, so that `(g * h) • c = g • (h • c)`. The action preserves the
degree. It does **not** fix classes in general: that it moves them is what fields of moduli and
Galois orbits of Belyi maps measure. The **true orbit size**
`TauCeti.AlgebraicBelyiPair.IsoClass.trueOrbitSize` of a class is the cardinality of its orbit
under `Gal(k/ℚ)`, which is the index of its stabilizer.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.conj`: the conjugate of an algebraic Belyi pair along `σ : k ≃+* k'`.
* `TauCeti.AlgebraicBelyiPair.conjAlgHom` and `TauCeti.AlgebraicBelyiPair.conjAlgEquiv`:
  conjugation of morphisms and isomorphisms of pairs.
* `TauCeti.AlgebraicBelyiPair.IsoClass.conj`: conjugation of isomorphism classes, and the
  `MulAction` of a group `G` acting on `k` by ring automorphisms.
* `TauCeti.AlgebraicBelyiPair.IsoClass.trueOrbitSize`: the size of the `Gal(k/ℚ)`-orbit of a
  class.

## Main results

* `TauCeti.AlgebraicBelyiPair.finrank_conj`: conjugation preserves the degree.
* `TauCeti.AlgebraicBelyiPair.IsoClass.conj_refl` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.conj_conj`: conjugation of classes is functorial in `σ`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.degree_smul`: the action preserves the degree.
* `TauCeti.AlgebraicBelyiPair.IsoClass.trueOrbitSize_eq_index`: the true orbit size is the index
  of the stabilizer.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k k' k'' : Type u} [Field k] [CharZero k] [Field k'] [CharZero k'] [Field k'']
  [CharZero k'']

/-- The **conjugate** of an algebraic Belyi pair `X` along an isomorphism `σ : k ≃+* k'`: the same
function field, with its embedding of `k'(t)` precomposed with the coefficient map of `σ⁻¹`, and
its `k'`-algebra structure the one induced through `k'(t)`, so that the constants are embedded by
precomposition with `σ⁻¹`. This is the base change of the Belyi map along `σ`. -/
noncomputable def conj (σ : k ≃+* k') (X : AlgebraicBelyiPair k) : AlgebraicBelyiPair k' :=
  letI : Algebra (RatFunc k') X :=
    ((algebraMap (RatFunc k) X).comp (RatFunc.mapRingEquiv σ.symm).toRingHom).toAlgebra
  letI : Algebra k' X := ((algebraMap (RatFunc k') X).comp (algebraMap k' (RatFunc k'))).toAlgebra
  haveI : IsScalarTower k' (RatFunc k') X := .of_algebraMap_eq' rfl
  have hτ (x : RatFunc k) : RingEquiv.refl X (algebraMap (RatFunc k) X x) =
      algebraMap (RatFunc k') X (RatFunc.mapRingEquiv σ x) := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, ← RatFunc.mapRingEquiv_symm, RingEquiv.symm_apply_apply,
      RingEquiv.refl_apply]
  haveI : FiniteDimensional (RatFunc k') X :=
    .of_equiv_equiv (RatFunc.mapRingEquiv σ) (RingEquiv.refl X) (RingHom.ext fun x ↦ (hτ x).symm)
  { carrier := X
    isAlgebraicBelyiPair := X.isAlgebraicBelyiPair.of_mapRingEquiv σ (RingEquiv.refl X) hτ }

variable (σ : k ≃+* k') (X : AlgebraicBelyiPair k)

/-- The identity of the function field, as a ring isomorphism from an algebraic Belyi pair to its
conjugate along `σ`. It carries `k(t)` onto `k'(t)` by the coefficient map of `σ`
(`TauCeti.AlgebraicBelyiPair.conjRingEquiv_algebraMap_ratFunc`). -/
noncomputable def conjRingEquiv : X ≃+* X.conj σ :=
  RingEquiv.refl X

/-- The embedding of `k'(t)` into the conjugate of `X` along `σ` is that of `X`, precomposed with
the coefficient map of `σ⁻¹`. -/
theorem algebraMap_conj (x : RatFunc k') :
    algebraMap (RatFunc k') (X.conj σ) x =
      conjRingEquiv σ X (algebraMap (RatFunc k) X (RatFunc.mapRingEquiv σ.symm x)) :=
  (rfl)

/-- The identification of `X` with its conjugate along `σ` carries `k(t)` onto `k'(t)` by the
coefficient map of `σ`. -/
@[simp]
theorem conjRingEquiv_algebraMap_ratFunc (x : RatFunc k) :
    conjRingEquiv σ X (algebraMap (RatFunc k) X x) =
      algebraMap (RatFunc k') (X.conj σ) (RatFunc.mapRingEquiv σ x) := by
  rw [algebraMap_conj, ← RatFunc.mapRingEquiv_symm, RingEquiv.symm_apply_apply]

/-- The identification of `X` with its conjugate along `σ` carries the constants `k` onto `k'`
along `σ`. -/
@[simp]
theorem conjRingEquiv_algebraMap (c : k) :
    conjRingEquiv σ X (algebraMap k X c) = algebraMap k' (X.conj σ) (σ c) :=
  apply_algebraMap_eq_of_mapRingEquiv σ _ (conjRingEquiv_algebraMap_ratFunc σ X) c

/-- **Conjugation preserves the degree** of an algebraic Belyi pair. -/
@[simp]
theorem finrank_conj :
    Module.finrank (RatFunc k') (X.conj σ) = Module.finrank (RatFunc k) X :=
  finrank_eq_of_mapRingEquiv σ _ (conjRingEquiv_algebraMap_ratFunc σ X)

variable {X} {Y : AlgebraicBelyiPair k}

/-- **Conjugation of morphisms**: a morphism of algebraic Belyi pairs over `k(t)` is also a
morphism of their conjugates along `σ` over `k'(t)`. -/
noncomputable def conjAlgHom (f : X →ₐ[RatFunc k] Y) : X.conj σ →ₐ[RatFunc k'] Y.conj σ :=
  { ((conjRingEquiv σ Y : Y →+* Y.conj σ).comp (f : X →+* Y)).comp
      ((conjRingEquiv σ X).symm : X.conj σ →+* X) with
    commutes' x := by
      simp [algebraMap_conj, -conjRingEquiv_algebraMap_ratFunc] }

@[simp]
theorem conjAlgHom_conjRingEquiv (f : X →ₐ[RatFunc k] Y) (x : X) :
    conjAlgHom σ f (conjRingEquiv σ X x) = conjRingEquiv σ Y (f x) := by
  simp [conjAlgHom]

/-- **Conjugation of isomorphisms**: an isomorphism of algebraic Belyi pairs over `k(t)` is also
an isomorphism of their conjugates along `σ` over `k'(t)`. -/
noncomputable def conjAlgEquiv (e : X ≃ₐ[RatFunc k] Y) : X.conj σ ≃ₐ[RatFunc k'] Y.conj σ :=
  AlgEquiv.ofAlgHom (conjAlgHom σ e) (conjAlgHom σ e.symm)
    (AlgHom.ext fun y ↦ by
      obtain ⟨y, rfl⟩ := (conjRingEquiv σ Y).surjective y
      simp)
    (AlgHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := (conjRingEquiv σ X).surjective x
      simp)

@[simp]
theorem conjAlgEquiv_conjRingEquiv (e : X ≃ₐ[RatFunc k] Y) (x : X) :
    conjAlgEquiv σ e (conjRingEquiv σ X x) = conjRingEquiv σ Y (e x) :=
  conjAlgHom_conjRingEquiv σ (e : X →ₐ[RatFunc k] Y) x

variable (X)

/-- Conjugating along the identity of `k` gives back an isomorphic pair. -/
noncomputable def conjRefl : X.conj (RingEquiv.refl k) ≃ₐ[RatFunc k] X :=
  AlgEquiv.ofRingEquiv (f := (conjRingEquiv (RingEquiv.refl k) X).symm) fun x ↦ by
    rw [algebraMap_conj, RingEquiv.symm_apply_apply, RingEquiv.symm_refl,
      RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]

/-- Conjugating along `σ` and then along `τ` is isomorphic to conjugating along `σ.trans τ`. -/
noncomputable def conjTrans (τ : k' ≃+* k'') :
    (X.conj σ).conj τ ≃ₐ[RatFunc k''] X.conj (σ.trans τ) :=
  AlgEquiv.ofRingEquiv
    (f := (conjRingEquiv τ (X.conj σ)).symm.trans
      ((conjRingEquiv σ X).symm.trans (conjRingEquiv (σ.trans τ) X))) fun x ↦ by
    simp only [RingEquiv.trans_apply, algebraMap_conj, RingEquiv.symm_apply_apply,
      RingEquiv.symm_trans, RatFunc.mapRingEquiv_trans]

@[simp]
theorem conjRefl_conjRingEquiv (x : X) : conjRefl X (conjRingEquiv (RingEquiv.refl k) X x) = x :=
  (conjRingEquiv (RingEquiv.refl k) X).symm_apply_apply x

@[simp]
theorem conjTrans_conjRingEquiv (τ : k' ≃+* k'') (x : X) :
    conjTrans σ X τ (conjRingEquiv τ (X.conj σ) (conjRingEquiv σ X x)) =
      conjRingEquiv (σ.trans τ) X x := by
  simp [conjTrans]

/-! ### The action on isomorphism classes -/

namespace IsoClass

/-- **Conjugation of isomorphism classes** of algebraic Belyi pairs along `σ : k ≃+* k'`: the
class of the conjugate of any representative. -/
noncomputable def conj (σ : k ≃+* k') : IsoClass k → IsoClass k' :=
  Quotient.map (AlgebraicBelyiPair.conj σ) fun _ _ ⟨e⟩ ↦ ⟨conjAlgEquiv σ e⟩

@[simp]
theorem conj_mk : (mk X).conj σ = mk (X.conj σ) :=
  (rfl)

@[simp]
theorem conj_refl (c : IsoClass k) : c.conj (RingEquiv.refl k) = c := by
  induction c using ind with
  | h X => exact mk_eq_mk (conjRefl X)

theorem conj_conj (c : IsoClass k) (τ : k' ≃+* k'') :
    (c.conj σ).conj τ = c.conj (σ.trans τ) := by
  induction c using ind with
  | h X => exact mk_eq_mk (conjTrans σ X τ)

/-- **Conjugation preserves the degree** of an isomorphism class. -/
@[simp]
theorem degree_conj (c : IsoClass k) : (c.conj σ).degree = c.degree := by
  induction c using ind with
  | h X => simp

variable {G : Type*} [Group G] [MulSemiringAction G k]

/-- **The Galois action on isomorphism classes**: a group `G` acting on `k` by ring automorphisms
acts on the isomorphism classes of algebraic Belyi pairs over `k` by conjugation,
`g • c = c.conj (MulSemiringAction.toRingEquiv G k g)`. For `G = Gal(ℚ̄/ℚ)` acting on `ℚ̄` this is
the action of the absolute Galois group on Belyi maps. -/
noncomputable instance instMulAction : MulAction G (IsoClass k) where
  smul g c := c.conj (MulSemiringAction.toRingEquiv G k g)
  one_smul c := (congrArg c.conj (RingEquiv.ext fun x ↦ one_smul G x)).trans (conj_refl c)
  mul_smul g h c := (congrArg c.conj (RingEquiv.ext fun x ↦ mul_smul g h x)).trans
    (conj_conj _ c _).symm

theorem smul_def (g : G) (c : IsoClass k) :
    g • c = c.conj (MulSemiringAction.toRingEquiv G k g) :=
  (rfl)

theorem smul_mk (g : G) : g • mk X = mk (X.conj (MulSemiringAction.toRingEquiv G k g)) :=
  (rfl)

/-- **The Galois action preserves the degree** of an isomorphism class. -/
@[simp]
theorem degree_smul (g : G) (c : IsoClass k) : (g • c).degree = c.degree := by
  rw [smul_def, degree_conj]

/-- The **true orbit size** of an isomorphism class `c` of algebraic Belyi pairs over a field `k`
of characteristic zero: the number of isomorphism classes in its orbit under `Gal(k/ℚ)`, the group
of all field automorphisms of `k`. For `k = ℚ̄` this is the size of the Galois orbit of the Belyi
map; it is attached to the class, not to any field of definition. As a `Nat.card` it is `0` on an
infinite orbit; that orbits are finite for `k = ℚ̄` is not proved here. -/
noncomputable def trueOrbitSize (c : IsoClass k) : ℕ :=
  Nat.card (MulAction.orbit (k ≃ₐ[ℚ] k) c)

/-- The true orbit size of a class is the index of its stabilizer in `Gal(k/ℚ)`. -/
theorem trueOrbitSize_eq_index (c : IsoClass k) :
    c.trueOrbitSize = (MulAction.stabilizer (k ≃ₐ[ℚ] k) c).index := by
  rw [MulAction.index_stabilizer, trueOrbitSize, Nat.card_coe_set_eq]

/-- Galois-conjugate classes have the same true orbit size. -/
@[simp]
theorem trueOrbitSize_smul (g : k ≃ₐ[ℚ] k) (c : IsoClass k) :
    (g • c).trueOrbitSize = c.trueOrbitSize := by
  rw [trueOrbitSize, trueOrbitSize, MulAction.orbit_smul]

end IsoClass

end AlgebraicBelyiPair

end TauCeti
