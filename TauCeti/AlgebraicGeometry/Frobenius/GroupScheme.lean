/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import TauCeti.AlgebraicGeometry.Frobenius.Iterate

/-!
# The `q`-power Frobenius of a group scheme over a finite field

Let `k` be a finite field with `q = p ^ a` elements. The `q`-power Frobenius
`AlgebraicGeometry.Scheme.qPowerFrobenius` of a scheme `X` over `k` is a morphism over `k`, and
every morphism of `k`-schemes commutes with it. So it is an endomorphism of the identity functor
of `Over (Spec k)`. Since the identity functor preserves finite products, this endomorphism lifts
to group objects: the `q`-power Frobenius `F : G ⟶ G` of every group scheme `G` over `k` is a
homomorphism of group schemes, and the same holds for commutative group schemes.

On points, `F` acts through the Frobenius of the test scheme: a point `x : T ⟶ G` over `k` goes
to `F_T ≫ x`, where `F_T` is the `q`-power Frobenius of `T`. In particular `F` fixes the points of
`G` with values in `Spec k` itself, the `k`-rational points.

## Main definitions

* `AlgebraicGeometry.Scheme.qPowerFrobeniusOver k a ha X`: the `q`-power Frobenius of a scheme `X`
  over `k`, as an endomorphism of `X` in `Over (Spec k)`.
* `AlgebraicGeometry.Scheme.qPowerFrobeniusNatTrans k a ha`: the `q`-power Frobenius as an
  endomorphism of the identity functor of `Over (Spec k)`.
* `AlgebraicGeometry.Scheme.qPowerFrobeniusGrpHom k a ha G` and
  `AlgebraicGeometry.Scheme.qPowerFrobeniusCommGrpHom k a ha G`: the `q`-power Frobenius of a
  (commutative) group scheme `G` over `k`, as an endomorphism of `G`.

## Main results

* `AlgebraicGeometry.Scheme.qPowerFrobeniusOver_unit`: the `q`-power Frobenius of the base
  `Spec k`, the unit object of `Over (Spec k)`, is the identity.
* `AlgebraicGeometry.Scheme.comp_qPowerFrobeniusOver`: the `q`-power Frobenius of `G` acts
  on points through the `q`-power Frobenius of the test scheme.

## References

* The Stacks Project, chapter Varieties, section Frobenii, Remark 33.36.11.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Section 1.f.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (a : ℕ)
  (ha : Nat.card k = p ^ a)

/-- The `q`-power Frobenius of a scheme `X` over a finite field `k` with `q = p ^ a` elements, as
an endomorphism of `X` in `Over (Spec k)`. -/
noncomputable def qPowerFrobeniusOver (X : Over (Spec (CommRingCat.of k))) : X ⟶ X :=
  Over.homMk (qPowerFrobenius k X.hom a ha) (qPowerFrobenius_over k X.hom a ha)

@[simp]
theorem qPowerFrobeniusOver_left (X : Over (Spec (CommRingCat.of k))) :
    (qPowerFrobeniusOver k a ha X).left = qPowerFrobenius k X.hom a ha :=
  (rfl)

/-- **Frobenius on points.** A point `x : T ⟶ X` over `k` followed by the `q`-power Frobenius of
`X` is the `q`-power Frobenius of `T` followed by `x`. -/
@[reassoc]
theorem comp_qPowerFrobeniusOver {T X : Over (Spec (CommRingCat.of k))} (x : T ⟶ X) :
    x ≫ qPowerFrobeniusOver k a ha X = qPowerFrobeniusOver k a ha T ≫ x := by
  ext
  exact (qPowerFrobenius_naturality k T.hom X.hom x.left a ha).symm

/-- The `q`-power Frobenius of the base `Spec k`, the unit object of `Over (Spec k)`, is the
identity: the `q`-th power map of `k` is the identity. -/
@[simp]
theorem qPowerFrobeniusOver_unit :
    qPowerFrobeniusOver k a ha (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ := by
  ext
  simpa using qPowerFrobenius_over k (𝟙 (Spec (CommRingCat.of k))) a ha

/-- The `n`-th power of the `q`-power Frobenius of `X` is the `q ^ n`-power Frobenius: the absolute
Frobenius of `X` iterated `a * n` times. -/
theorem qPowerFrobeniusOver_pow_asHom_left (X : Over (Spec (CommRingCat.of k))) (n : ℕ) :
    (End.of (qPowerFrobeniusOver k a ha X) ^ n).asHom.left =
      X.left.iterateFrobenius p (natCast_eq_zero_of_hom X.hom
        (natCast_spec_eq_zero (CommRingCat.of k))) (a * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_asHom, Over.comp_left, ih, qPowerFrobeniusOver_left,
      qPowerFrobenius_eq_iterated, ← iterateFrobenius_add, Nat.mul_succ]

/-- **Powers of Frobenius on points.** A point `x : T ⟶ X` over `k` followed by the `n`-th power of
the `q`-power Frobenius of `X` is the `n`-th power of the `q`-power Frobenius of `T` followed by
`x`. -/
@[reassoc]
theorem comp_qPowerFrobeniusOver_pow {T X : Over (Spec (CommRingCat.of k))} (x : T ⟶ X) (n : ℕ) :
    x ≫ (End.of (qPowerFrobeniusOver k a ha X) ^ n).asHom =
      (End.of (qPowerFrobeniusOver k a ha T) ^ n).asHom ≫ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', End.mul_asHom]
    rw [reassoc_of% ih, comp_qPowerFrobeniusOver, Category.assoc]

/-- The `q`-power Frobenius over a finite field `k` with `q = p ^ a` elements, as an endomorphism
of the identity functor of `Over (Spec k)`. -/
noncomputable def qPowerFrobeniusNatTrans :
    𝟭 (Over (Spec (CommRingCat.of k))) ⟶ 𝟭 (Over (Spec (CommRingCat.of k))) where
  app X := qPowerFrobeniusOver k a ha X
  naturality _ _ g := comp_qPowerFrobeniusOver k a ha g

@[simp]
theorem qPowerFrobeniusNatTrans_app (X : Over (Spec (CommRingCat.of k))) :
    (qPowerFrobeniusNatTrans k a ha).app X = qPowerFrobeniusOver k a ha X :=
  (rfl)

/-- **The `q`-power Frobenius of a group scheme is a homomorphism.** For a group scheme `G` over a
finite field `k` with `q` elements, the `q`-power Frobenius `G ⟶ G` is an endomorphism of `G` as a
group scheme. -/
noncomputable def qPowerFrobeniusGrpHom (G : Grp (Over (Spec (CommRingCat.of k)))) : G ⟶ G :=
  Functor.mapGrpIdIso.inv.app G ≫
    (Functor.mapGrpNatTrans (qPowerFrobeniusNatTrans k a ha)).app G ≫ Functor.mapGrpIdIso.hom.app G

@[simp]
theorem qPowerFrobeniusGrpHom_hom_hom (G : Grp (Over (Spec (CommRingCat.of k)))) :
    (qPowerFrobeniusGrpHom k a ha G).hom.hom = qPowerFrobeniusOver k a ha G.X :=
  (rfl)

/-- Every homomorphism of group schemes over `k` commutes with the `q`-power Frobenius. -/
@[reassoc]
theorem qPowerFrobeniusGrpHom_naturality {G H : Grp (Over (Spec (CommRingCat.of k)))}
    (φ : G ⟶ H) : qPowerFrobeniusGrpHom k a ha G ≫ φ = φ ≫ qPowerFrobeniusGrpHom k a ha H :=
  Grp.hom_ext _ _ <| by simpa using (comp_qPowerFrobeniusOver k a ha φ.hom.hom).symm

/-- The `q`-power Frobenius of a commutative group scheme `G` over a finite field `k` with `q`
elements, as an endomorphism of `G` as a commutative group scheme. -/
noncomputable def qPowerFrobeniusCommGrpHom (G : CommGrp (Over (Spec (CommRingCat.of k)))) :
    G ⟶ G :=
  InducedCategory.homMk (qPowerFrobeniusGrpHom k a ha G.toGrp)

@[simp]
theorem qPowerFrobeniusCommGrpHom_hom_hom_hom (G : CommGrp (Over (Spec (CommRingCat.of k)))) :
    (qPowerFrobeniusCommGrpHom k a ha G).hom.hom.hom = qPowerFrobeniusOver k a ha G.X :=
  qPowerFrobeniusGrpHom_hom_hom k a ha G.toGrp

/-- The `n`-th power of the `q`-power Frobenius of a commutative group scheme `G`, as an
endomorphism of `G`, has as underlying morphism the `n`-th power of the `q`-power Frobenius of the
scheme `G`. -/
@[simp]
theorem qPowerFrobeniusCommGrpHom_pow_hom_hom_hom (G : CommGrp (Over (Spec (CommRingCat.of k))))
    (n : ℕ) : (End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ n).asHom.hom.hom.hom =
      (End.of (qPowerFrobeniusOver k a ha G.X) ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih]

/-- Every homomorphism of commutative group schemes over `k` commutes with the `q`-power
Frobenius. -/
@[reassoc]
theorem qPowerFrobeniusCommGrpHom_naturality {G H : CommGrp (Over (Spec (CommRingCat.of k)))}
    (φ : G ⟶ H) :
    qPowerFrobeniusCommGrpHom k a ha G ≫ φ = φ ≫ qPowerFrobeniusCommGrpHom k a ha H :=
  CommGrp.hom_ext _ _ <| by simpa using (comp_qPowerFrobeniusOver k a ha φ.hom.hom.hom).symm

end AlgebraicGeometry.Scheme
