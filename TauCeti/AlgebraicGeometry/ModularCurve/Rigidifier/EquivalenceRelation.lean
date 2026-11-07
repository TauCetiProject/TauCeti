/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.Double

/-!
# The scheme of two rigidifications is an equivalence relation

Suppose `(𝒫, δ)` is represented by an elliptic family `V` and `δ` is relatively representable, so
that the base change `V_{δ_V}` of `V` to the relative representing scheme `δ_V` represents
`(𝒫, δ, δ)` (`RelRepData.doubleRepresentableBy`). An arrow `X ⟶ V_{δ_V}` of `Ell/B` is a triple
`(p, d₁, d₂)` on `X`, and the two forgetful projections `p₁, p₂ : V_{δ_V} ⟶ V` retain `(p, d₁)` and
`(p, d₂)` respectively. Reading triples this way, this file constructs three arrows of `Ell/B`:

* the **diagonal** `V ⟶ V_{δ_V}`, `(p, d) ↦ (p, d, d)` (`RelRepData.doubleDiag`);
* the **swap** `V_{δ_V} ⟶ V_{δ_V}`, `(p, d₁, d₂) ↦ (p, d₂, d₁)` (`RelRepData.doubleSwap`);
* the **composition** of two triples `(p, d₁, d₂)` and `(p, d₂, d₃)` on the same object, which is
  the triple `(p, d₁, d₃)` (`RelRepData.doubleComp`).

When `𝒫` is rigid, the morphisms of bases of `p₁` and `p₂` are jointly monic
(`RelRepData.mono_pullback_lift_baseChangeFunctorHom_doubleSnd`), and the morphisms of bases of
these three arrows make the pair `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` an internal equivalence relation in the
category of schemes (`RelRepData.doubleEquivalenceRelation`). Transitivity is checked on the
fibre product of schemes `𝕄(𝒫, δ, δ) ×_{p₂, 𝕄(𝒫, δ), p₁} 𝕄(𝒫, δ, δ)`: over it, the two
projections are morphisms of bases of arrows of `Ell/B` from one common elliptic curve, which
carries composable triples.

For a finite étale rigidifier `δ`, both projections are moreover finite étale
(`RelRepData.mem_doubleSnd_base`), so this is the finite étale equivalence relation whose quotient
Katz and Mazur take to construct the moduli scheme of `𝒫`. No group acting on `δ` is used.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleDiag`,
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleSwap` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleComp`: reflexivity, symmetry and
  transitivity of the relation, as arrows of `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleEquivalenceRelation`: for rigid `𝒫`,
  the two projections `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` form an equivalence relation in schemes.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 4, proof of Theorem 4.7.0.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

variable {B : Scheme.{u}} {P Q : ModuliProblem B} (D : Q.RelRepData)
  {V : EllObj B} (R : (P ⊗ Q).RepresentableBy V)

/-! ### Reflexivity -/

/-- The **diagonal** of the scheme of two rigidifications: the arrow `V ⟶ V_{δ_V}` classifying the
triple `(p, d, d)`, where `(p, d)` is the universal pair on `V`. It is a section of both forgetful
projections (`doubleDiag_comp_baseChangeFunctorHom`, `doubleDiag_comp_doubleSnd`). -/
noncomputable def doubleDiag : V ⟶ V.baseChangeFunctor.obj (D.rep V) :=
  (D.doubleRepresentableBy R).homEquiv.symm ((P ◁ lift (𝟙 Q) (𝟙 Q)).app _ (R.homEquiv (𝟙 V)))

/-- The diagonal classifies the universal pair with its `δ`-structure repeated. -/
theorem doubleRepresentableBy_homEquiv_doubleDiag :
    (D.doubleRepresentableBy R).homEquiv (D.doubleDiag R) =
      (P ◁ lift (𝟙 Q) (𝟙 Q)).app _ (R.homEquiv (𝟙 V)) :=
  (D.doubleRepresentableBy R).homEquiv.apply_symm_apply _

/-- The diagonal is a section of the first projection. -/
@[reassoc (attr := simp)]
theorem doubleDiag_comp_baseChangeFunctorHom :
    D.doubleDiag R ≫ V.baseChangeFunctorHom (D.rep V) = 𝟙 V :=
  R.homEquiv.injective (by
    rw [homEquiv_comp_baseChangeFunctorHom, doubleRepresentableBy_homEquiv_doubleDiag,
      ← NatTrans.comp_app_apply, ← whiskerLeft_comp, lift_fst, whiskerLeft_id, NatTrans.id_app,
      types_id_apply])

/-- The diagonal is a section of the second projection. -/
@[reassoc (attr := simp)]
theorem doubleDiag_comp_doubleSnd : D.doubleDiag R ≫ D.doubleSnd R = 𝟙 V :=
  R.homEquiv.injective (by
    rw [homEquiv_comp_doubleSnd, doubleRepresentableBy_homEquiv_doubleDiag,
      ← NatTrans.comp_app_apply, ← whiskerLeft_comp, lift_snd, whiskerLeft_id, NatTrans.id_app,
      types_id_apply])

/-! ### Symmetry -/

/-- The **swap** of the scheme of two rigidifications: the arrow `V_{δ_V} ⟶ V_{δ_V}` classifying
the universal triple `(p, d₁, d₂)` with its two `δ`-structures exchanged, `(p, d₂, d₁)`. It
exchanges the two forgetful projections (`doubleSwap_comp_baseChangeFunctorHom`,
`doubleSwap_comp_doubleSnd`). -/
noncomputable def doubleSwap :
    V.baseChangeFunctor.obj (D.rep V) ⟶ V.baseChangeFunctor.obj (D.rep V) :=
  (D.doubleRepresentableBy R).homEquiv.symm
    ((P ◁ (β_ Q Q).hom).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)))

/-- The swap classifies the universal triple with its two `δ`-structures exchanged. -/
theorem doubleRepresentableBy_homEquiv_doubleSwap :
    (D.doubleRepresentableBy R).homEquiv (D.doubleSwap R) =
      (P ◁ (β_ Q Q).hom).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)) :=
  (D.doubleRepresentableBy R).homEquiv.apply_symm_apply _

/-- The swap followed by the first projection is the second projection. -/
@[reassoc (attr := simp)]
theorem doubleSwap_comp_baseChangeFunctorHom :
    D.doubleSwap R ≫ V.baseChangeFunctorHom (D.rep V) = D.doubleSnd R := by
  refine R.homEquiv.injective ?_
  rw [homEquiv_comp_baseChangeFunctorHom, doubleRepresentableBy_homEquiv_doubleSwap,
    ← NatTrans.comp_app_apply, ← whiskerLeft_comp, braiding_hom_fst, homEquiv_doubleSnd]

/-- The swap followed by the second projection is the first projection. -/
@[reassoc (attr := simp)]
theorem doubleSwap_comp_doubleSnd :
    D.doubleSwap R ≫ D.doubleSnd R = V.baseChangeFunctorHom (D.rep V) := by
  refine R.homEquiv.injective ?_
  rw [homEquiv_comp_doubleSnd, doubleRepresentableBy_homEquiv_doubleSwap,
    ← NatTrans.comp_app_apply, ← whiskerLeft_comp, braiding_hom_snd, ← Category.id_comp
      (V.baseChangeFunctorHom (D.rep V)), homEquiv_comp_baseChangeFunctorHom]

/-! ### Transitivity -/

/-- The **composition** of two triples on the same object: for arrows `f g : X ⟶ V_{δ_V}`
classifying triples `(p, d₁, d₂)` and `(p', d₂', d₃)`, the arrow classifying `(p, d₁, d₃)`. When
`f ≫ p₂ = g ≫ p₁`, that is `(p, d₂) = (p', d₂')`, its composites with the two forgetful projections
are those of `f` with the first and of `g` with the second (`doubleComp_comp_baseChangeFunctorHom`,
`doubleComp_comp_doubleSnd`). -/
noncomputable def doubleComp {X : EllObj B} (f g : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    X ⟶ V.baseChangeFunctor.obj (D.rep V) :=
  (D.doubleRepresentableBy R).homEquiv.symm
    (((D.doubleRepresentableBy R).homEquiv f).1,
      (((D.doubleRepresentableBy R).homEquiv f).2.1, ((D.doubleRepresentableBy R).homEquiv g).2.2))

/-- The composition of two triples classifies the `𝒫`-structure and first `δ`-structure of the
first triple, followed by the last `δ`-structure of the second. -/
theorem doubleRepresentableBy_homEquiv_doubleComp {X : EllObj B}
    (f g : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    (D.doubleRepresentableBy R).homEquiv (D.doubleComp R f g) =
      (((D.doubleRepresentableBy R).homEquiv f).1,
        (((D.doubleRepresentableBy R).homEquiv f).2.1,
          ((D.doubleRepresentableBy R).homEquiv g).2.2)) :=
  (D.doubleRepresentableBy R).homEquiv.apply_symm_apply _

/-- The composition of two triples has the first pair of the first triple. -/
@[reassoc (attr := simp)]
theorem doubleComp_comp_baseChangeFunctorHom {X : EllObj B}
    (f g : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    D.doubleComp R f g ≫ V.baseChangeFunctorHom (D.rep V) =
      f ≫ V.baseChangeFunctorHom (D.rep V) :=
  R.homEquiv.injective (by
    rw [homEquiv_comp_baseChangeFunctorHom, homEquiv_comp_baseChangeFunctorHom,
      doubleRepresentableBy_homEquiv_doubleComp, whiskerLeft_app_apply]
    -- whiskering keeps the `𝒫`-structure and projects the pair of `δ`-structures; the left side
    -- applies it to a literal tuple, which `rw` cannot match, so it is computed componentwise
    exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _)
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans
        ((Functor.Monoidal.fst_app_apply _).trans (Functor.Monoidal.fst_app_apply _).symm)))

/-- The composition of two composable triples has the last pair of the second triple. -/
@[reassoc]
theorem doubleComp_comp_doubleSnd {X : EllObj B} {f g : X ⟶ V.baseChangeFunctor.obj (D.rep V)}
    (h : f ≫ D.doubleSnd R = g ≫ V.baseChangeFunctorHom (D.rep V)) :
    D.doubleComp R f g ≫ D.doubleSnd R = g ≫ D.doubleSnd R := by
  refine R.homEquiv.injective ?_
  -- `h` says that the `𝒫`-structures of the two triples agree
  have hp := congrArg Prod.fst (congrArg R.homEquiv h)
  rw [homEquiv_comp_doubleSnd, homEquiv_comp_baseChangeFunctorHom,
    Functor.Monoidal.whiskerLeft_app_apply_fst, Functor.Monoidal.whiskerLeft_app_apply_fst] at hp
  rw [homEquiv_comp_doubleSnd, homEquiv_comp_doubleSnd, doubleRepresentableBy_homEquiv_doubleComp,
    whiskerLeft_app_apply]
  -- whiskering keeps the `𝒫`-structure, where `hp` applies, and projects the pair of
  -- `δ`-structures, where both sides are the last `δ`-structure of `g`; as above, the left side
  -- is computed componentwise
  exact Prod.ext ((Functor.Monoidal.whiskerLeft_app_apply_fst _ _).trans hp)
    ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans
      ((Functor.Monoidal.snd_app_apply _).trans (Functor.Monoidal.snd_app_apply _).symm))

/-! ### The equivalence relation on the scheme of one rigidification -/

/-- **The scheme of two rigidifications is an equivalence relation** on the scheme of one
rigidification (Katz and Mazur, proof of Theorem 4.7.0). If `𝒫` is rigid, the morphisms of bases
`𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` of the two forgetful projections form an equivalence relation in the
category of schemes. Its reflexivity, symmetry and transitivity morphisms are the morphisms of
bases of `doubleDiag`, `doubleSwap` and `doubleComp`; the last is evaluated on the two projections
from the fibre product `𝕄(𝒫, δ, δ) ×_{𝕄(𝒫, δ)} 𝕄(𝒫, δ, δ)`, lifted to arrows of `Ell/B`. -/
noncomputable def doubleEquivalenceRelation (hP : P.IsRigid) :
    EquivalenceRelation (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base :=
  let W := V.baseChangeFunctor.obj (D.rep V)
  let p₁ := V.baseChangeFunctorHom (D.rep V)
  let p₂ := D.doubleSnd R
  -- the two projections from the fibre product, as arrows of `Ell/B` from one common object
  let a := W.baseChangeFunctorHom (Over.mk (pullback.fst p₂.base p₁.base))
  let b := EllObj.Hom.lift p₁ (a ≫ p₂) (pullback.snd p₂.base p₁.base)
    (by
      rw [EllObj.comp_base, EllObj.baseChangeFunctorHom_base (X := W)]
      -- `Over.mk f` has structure morphism `f` and the base of `a`'s source is `pullback _ _`, by
      -- definition; the rewrite `Over.mk_hom` fails because the goal mixes the two spellings
      exact pullback.condition.symm)
  have hab : a ≫ p₂ = b ≫ p₁ := (EllObj.Hom.lift_comp _ _ _ _).symm
  { right_cancellation := fun _ f g h₁ h₂ ↦
      (D.mono_pullback_lift_baseChangeFunctorHom_doubleSnd R hP).right_cancellation f g
        (pullback.hom_ext (by rw [Category.assoc, Category.assoc, pullback.lift_fst, h₁])
          (by rw [Category.assoc, Category.assoc, pullback.lift_snd, h₂]))
    r := (D.doubleDiag R).base
    reflexivity₁ := by
      rw [← EllObj.comp_base, doubleDiag_comp_baseChangeFunctorHom, EllObj.id_base]
    reflexivity₂ := by rw [← EllObj.comp_base, doubleDiag_comp_doubleSnd, EllObj.id_base]
    s := (D.doubleSwap R).base
    symmetry₁ := by rw [← EllObj.comp_base, doubleSwap_comp_baseChangeFunctorHom]
    symmetry₂ := by rw [← EllObj.comp_base, doubleSwap_comp_doubleSnd]
    c := PullbackCone.mk _ _ pullback.condition
    isLimit := pullbackIsPullback p₂.base p₁.base
    t := (D.doubleComp R a b).base
    transitivity₁ := by
      have h := congrArg EllObj.Hom.base (D.doubleComp_comp_baseChangeFunctorHom R a b)
      rw [EllObj.comp_base, EllObj.comp_base, EllObj.baseChangeFunctorHom_base (X := W)] at h
      -- `(Over.mk f).hom` is `f`, and `c.fst` is `pullback.fst _ _`, by definition
      exact h
    transitivity₂ := by
      have h := congrArg EllObj.Hom.base (D.doubleComp_comp_doubleSnd R hab)
      have hb : b.base = pullback.snd p₂.base p₁.base := EllObj.Hom.lift_base _ _ _ _
      rw [EllObj.comp_base, EllObj.comp_base, hb] at h
      -- `c.snd` is `pullback.snd _ _` by definition
      exact h }

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
