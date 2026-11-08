/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.EquivalenceRelation
public import TauCeti.AlgebraicGeometry.Quotient.EquivalenceRelation

/-!
# The quotient of a rigidified moduli scheme by the scheme of two rigidifications

Let `𝒫` and `δ` be moduli problems over `Ell/B`, with `δ` relatively representable, and suppose
that the simultaneous problem `(𝒫, δ)` is represented by an object `V` of `Ell/B`, whose base
`𝕄(𝒫, δ) = V.base` is the moduli scheme of `𝒫` rigidified by `δ`. The relative representing scheme
`δ_V` is the scheme `𝕄(𝒫, δ, δ)` of two rigidifications, with its two forgetful projections
`p₁, p₂ : 𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)`; the first is the representing morphism `δ_V ⟶ V.base` itself.
Katz and Mazur construct the moduli scheme `𝕄(𝒫)` of `𝒫` as the quotient of `𝕄(𝒫, δ)` by this
relation. This file carries out that step.

**The quotient.** The quotient `𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` is the affine coequalizer of
`p₁` and `p₂` (`ModuliProblem.RelRepData.doubleQuotient`): the spectrum of the ring of functions on
`𝕄(𝒫, δ)` whose pullbacks along `p₁` and `p₂` agree. When `𝒫` is rigid, `p₁` and `p₂` form an
equivalence relation (`ModuliProblem.RelRepData.doubleEquivalenceRelation`), so if moreover
`𝕄(𝒫, δ)` is affine and `p₁` is finite locally free, SGA 3, Exposé V, Théorème 4.1 applies: the
projection `π : 𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` is finite locally free and surjective, the relation
is its kernel pair, and `π` is the coequalizer of `p₁` and `p₂` both in schemes and in fppf
sheaves. These are the results on `AlgebraicGeometry.Scheme.Hom.affineCoequalizerπ`, which apply to
`π` once `ModuliProblem.RelRepData.isEquivalenceRelation` is installed as a local instance. The
quotient is a `B`-scheme (`ModuliProblem.RelRepData.doubleQuotientStructureMap`).

**The classifying morphism.** Suppose that `δ` is flat, surjective and locally of finite
presentation over `Ell/B`; a finite étale surjective rigidifier is an example. A `𝒫`-structure
`α` on an object `X = (E/S)` of `Ell/B` then has a classifying morphism
`S ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` (`ModuliProblem.RelRepData.toDoubleQuotient`). Over the scheme `δ_X` of
`δ`-structures on `E`, the pair formed by the pullback of `α` and the universal `δ`-structure is
classified by an arrow to `V`, whose morphism of bases `δ_X ⟶ 𝕄(𝒫, δ)` is composed with `π`. Two
arrows to `V` with the same `𝒫`-structure, but possibly different `δ`-structures, have the same
image in the quotient (`ModuliProblem.RelRepData.base_comp_doubleQuotientπ_eq`), since together
they are classified by an arrow to `𝕄(𝒫, δ, δ)`. Hence the composite does not depend on the
choice of a point of `δ_X` over a point of `S`, and descends along the fppf covering `δ_X ⟶ S`.

The classifying morphism can be computed from any local rigidification: for an arrow
`g : W ⟶ X` of `Ell/B` and any `δ`-structure `d` on `W`, the composite `g.base ≫ toDoubleQuotient α`
is the image in the quotient of the morphism of bases of the arrow `W ⟶ V` classifying
`(g^* α, d)` (`ModuliProblem.RelRepData.comp_toDoubleQuotient`). Consequently the classifying
morphism is natural along arrows of `Ell/B` (`ModuliProblem.RelRepData.toDoubleQuotient_map`),
isomorphic structures have the same classifying morphism, and the `𝒫`-structure classified by an
arrow `h : W ⟶ V` has classifying morphism `h.base ≫ π`
(`ModuliProblem.RelRepData.toDoubleQuotient_fst_homEquiv`); in particular `π` classifies the
universal `𝒫`-structure on `V`. Neither rigidity nor affineness is needed for the classifying
morphism.

This file does not show that the quotient represents `𝒫`: that requires descending the universal
elliptic curve over `𝕄(𝒫, δ)` along `π`, and showing that the classifying morphism is a bijection
onto morphisms of `B`-schemes.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleQuotient`: the quotient
  `𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)`, with projection `doubleQuotientπ`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleQuotientStructureMap`: its morphism to
  `B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.toDoubleQuotient`: the classifying morphism
  of a `𝒫`-structure.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isEquivalenceRelation`: for rigid `𝒫`,
  the two projections `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` form an equivalence relation, so the affine
  coequalizer results of SGA 3, Exposé V, Théorème 4.1 apply to the projection to the quotient.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isColimitDoubleQuotientCofork`: the
  projection is the coequalizer of the two projections in schemes.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.comp_toDoubleQuotient`: the classifying
  morphism is computed by any local rigidification.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.toDoubleQuotient_map`: naturality of the
  classifying morphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 4, proof of Theorem 4.7.0.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, Théorème 4.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

variable {B : Scheme.{u}} {P Q : ModuliProblem B} (D : Q.RelRepData)
  {V : EllObj B} (R : (P ⊗ Q).RepresentableBy V)

/-! ### The quotient scheme -/

/-- The **quotient** `𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` of the scheme `𝕄(𝒫, δ) = V.base` of one rigidification
by the scheme `𝕄(𝒫, δ, δ)` of two rigidifications: the affine coequalizer of the two forgetful
projections, the spectrum of the ring of functions on `𝕄(𝒫, δ)` whose pullbacks along them agree.
The first projection is the representing morphism `δ_V ⟶ V.base`. For rigid `𝒫`, affine
`𝕄(𝒫, δ)` and finite locally free `δ_V ⟶ V.base` it is the quotient of `𝕄(𝒫, δ)` by an
equivalence relation (`isEquivalenceRelation`, `isColimitDoubleQuotientCofork`). -/
noncomputable abbrev doubleQuotient : Scheme.{u} :=
  (D.rep V).hom.affineCoequalizer (D.doubleSnd R).base

/-- The projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` to the quotient. -/
noncomputable abbrev doubleQuotientπ : V.base ⟶ D.doubleQuotient R :=
  (D.rep V).hom.affineCoequalizerπ (D.doubleSnd R).base

/-- The projection to the quotient coequalizes the two forgetful projections
`𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)`. -/
@[reassoc]
theorem doubleQuotient_condition :
    (D.rep V).hom ≫ D.doubleQuotientπ R = (D.doubleSnd R).base ≫ D.doubleQuotientπ R :=
  Scheme.Hom.affineCoequalizer_condition _ _

/-- For rigid `𝒫`, the two forgetful projections `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` form an equivalence
relation: this is `doubleEquivalenceRelation`, whose first projection
`(V.baseChangeFunctorHom (D.rep V)).base` is the representing morphism `(D.rep V).hom`. Installed as
a local instance, it makes the results of SGA 3, Exposé V, Théorème 4.1 on
`Scheme.Hom.affineCoequalizerπ` apply to `doubleQuotientπ`. -/
theorem isEquivalenceRelation (hP : P.IsRigid) :
    IsEquivalenceRelation (D.rep V).hom (D.doubleSnd R).base := by
  have := (D.doubleEquivalenceRelation R hP).isEquivalenceRelation
  rwa [EllObj.baseChangeFunctorHom_base] at this

/-- The structure morphism of `𝕄(𝒫, δ)` coequalizes the two forgetful projections, since both lie
over `B`. -/
private lemma rep_hom_structureMap :
    (D.rep V).hom ≫ V.structureMap = (D.doubleSnd R).base ≫ V.structureMap := by
  simp

section Quotient

variable [IsAffine V.base] [IsFinite (D.rep V).hom] [Flat (D.rep V).hom]
  [LocallyOfFinitePresentation (D.rep V).hom]

/-- **The quotient is a coequalizer of schemes** (SGA 3, Exposé V, Théorème 4.1). For rigid `𝒫`,
affine `𝕄(𝒫, δ)` and finite locally free `δ_V ⟶ 𝕄(𝒫, δ)`, the projection to the quotient is the
coequalizer of the two forgetful projections `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` in the category of schemes. -/
noncomputable def isColimitDoubleQuotientCofork (hP : P.IsRigid) :
    IsColimit (Cofork.ofπ _ (D.doubleQuotient_condition R)) :=
  have := D.isEquivalenceRelation R hP
  Scheme.Hom.isColimitAffineCoequalizerCofork _ _

/-- The **structure morphism** `𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ) ⟶ B` of the quotient, for rigid `𝒫`, affine
`𝕄(𝒫, δ)` and finite locally free `δ_V ⟶ 𝕄(𝒫, δ)`: the morphism through which the structure
morphism of `𝕄(𝒫, δ)` factors (`doubleQuotientπ_doubleQuotientStructureMap`). -/
noncomputable def doubleQuotientStructureMap (hP : P.IsRigid) : D.doubleQuotient R ⟶ B :=
  (D.isColimitDoubleQuotientCofork R hP).desc (Cofork.ofπ _ (D.rep_hom_structureMap R))

/-- The structure morphism of `𝕄(𝒫, δ)` factors through the quotient. -/
@[reassoc (attr := simp)]
theorem doubleQuotientπ_doubleQuotientStructureMap (hP : P.IsRigid) :
    D.doubleQuotientπ R ≫ D.doubleQuotientStructureMap R hP = V.structureMap :=
  (D.isColimitDoubleQuotientCofork R hP).fac _ WalkingParallelPair.one

end Quotient

/-! ### The classifying morphism -/

/-- **Arrows with the same `𝒫`-structure have the same image in the quotient.** If two arrows
`a₁ a₂ : W ⟶ V` of `Ell/B` classify pairs with the same `𝒫`-structure, then their morphisms of bases
have the same composite with the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)`: the triple formed by
the common `𝒫`-structure and the two `δ`-structures is classified by an arrow to `𝕄(𝒫, δ, δ)`, whose
forgetful projections are `a₁` and `a₂`. -/
theorem base_comp_doubleQuotientπ_eq {W : EllObj B} {a₁ a₂ : W ⟶ V}
    (h : (R.homEquiv a₁).1 = (R.homEquiv a₂).1) :
    a₁.base ≫ D.doubleQuotientπ R = a₂.base ≫ D.doubleQuotientπ R := by
  let b := (D.doubleRepresentableBy R).homEquiv.symm
    ((R.homEquiv a₁).1, ((R.homEquiv a₁).2, (R.homEquiv a₂).2))
  have hb : (D.doubleRepresentableBy R).homEquiv b =
      ((R.homEquiv a₁).1, ((R.homEquiv a₁).2, (R.homEquiv a₂).2)) :=
    Equiv.apply_symm_apply _ _
  have h₁ : b ≫ V.baseChangeFunctorHom (D.rep V) = a₁ := R.homEquiv.injective <| by
    rw [homEquiv_comp_baseChangeFunctorHom, hb]
    -- whiskering by the first projection keeps the first two entries of the literal triple
    rfl
  have h₂ : b ≫ D.doubleSnd R = a₂ := R.homEquiv.injective <| by
    rw [homEquiv_comp_doubleSnd, hb]
    exact Prod.ext h rfl
  rw [← h₁, ← h₂, EllObj.comp_base, EllObj.comp_base, Category.assoc, Category.assoc,
    EllObj.baseChangeFunctorHom_base]
  exact b.base ≫= D.doubleQuotient_condition R

-- the arrow `X_{δ_X} ⟶ V` classifying the pullback of `α` to the scheme `δ_X` of `δ`-structures
-- on `X`, together with the universal `δ`-structure
private noncomputable def rigidification {X : EllObj B} (α : P.obj (op X)) :
    X.baseChangeFunctor.obj (D.rep X) ⟶ V :=
  R.homEquiv.symm (P.map (X.baseChangeFunctorHom (D.rep X)).op α, D.universal X)

private lemma fst_homEquiv_rigidification_self {X : EllObj B} (α : P.obj (op X)) :
    (R.homEquiv (D.rigidification R α)).1 = P.map (X.baseChangeFunctorHom (D.rep X)).op α :=
  congrArg Prod.fst (R.homEquiv.apply_symm_apply _)

-- pulling back `rigidification` along a morphism `T ⟶ δ_X` of schemes over `X.base` gives an arrow
-- classifying the pullback of `α` to `T`
private lemma fst_homEquiv_rigidification {X : EllObj B} (α : P.obj (op X)) {T : Over X.base}
    (k : T ⟶ D.rep X) :
    (R.homEquiv (X.baseChangeFunctor.map k ≫ D.rigidification R α)).1 =
      P.map (X.baseChangeFunctorHom T).op α := by
  rw [R.homEquiv_comp, Functor.Monoidal.tensorObj_map_apply_fst, fst_homEquiv_rigidification_self,
    ← Functor.map_comp_apply, ← op_comp, EllObj.baseChangeFunctor_map_baseChangeFunctorHom]

-- two points `g₁ g₂` of `δ_X` over the same point of `X.base` are two `δ`-structures on one base
-- change of `X`, with the same pullback of `α`, so they have the same image in the quotient
private lemma rigidification_base_comp_eq {X : EllObj B} (α : P.obj (op X)) {Z : Scheme.{u}}
    (g₁ g₂ : Z ⟶ (D.rep X).left) (h : g₁ ≫ (D.rep X).hom = g₂ ≫ (D.rep X).hom) :
    g₁ ≫ (D.rigidification R α).base ≫ D.doubleQuotientπ R =
      g₂ ≫ (D.rigidification R α).base ≫ D.doubleQuotientπ R := by
  let T : Over X.base := Over.mk (g₁ ≫ (D.rep X).hom)
  have e := D.base_comp_doubleQuotientπ_eq R
    (a₁ := X.baseChangeFunctor.map (Over.homMk g₁ : T ⟶ D.rep X) ≫ D.rigidification R α)
    (a₂ := X.baseChangeFunctor.map (Over.homMk g₂ h.symm : T ⟶ D.rep X) ≫ D.rigidification R α)
    (by rw [fst_homEquiv_rigidification, fst_homEquiv_rigidification])
  rw [EllObj.comp_base, EllObj.comp_base, EllObj.baseChangeFunctor_map_base,
    EllObj.baseChangeFunctor_map_base] at e
  -- `(Over.homMk gᵢ _).left` is `gᵢ`, and the base of the base change of `X` to `T` is `Z`, by
  -- definition; `rw` cannot reassociate across these two spellings of the same object
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

variable (hf : D.HasProperty @Flat) (hl : D.HasProperty @LocallyOfFinitePresentation)
  (hs : D.HasProperty @Surjective)

/-- The **classifying morphism** `S ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` of a `𝒫`-structure `α` on an object
`X = (E/S)` of `Ell/B`, for a rigidifier `δ` which is flat, surjective and locally of finite
presentation over `Ell/B`. Over the scheme `δ_X` of `δ`-structures on `E`, the pullback of `α`
and the universal `δ`-structure are classified by an arrow to `V`; the composite of its morphism of
bases with the projection to the quotient descends along the fppf covering `δ_X ⟶ S`. It is
characterised by `comp_toDoubleQuotient`. -/
noncomputable def toDoubleQuotient {X : EllObj B} (α : P.obj (op X)) :
    X.base ⟶ D.doubleQuotient R :=
  have := D.hasProperty_iff.mp hf X
  have := D.hasProperty_iff.mp hl X
  have := D.hasProperty_iff.mp hs X
  EffectiveEpi.desc (D.rep X).hom ((D.rigidification R α).base ≫ D.doubleQuotientπ R)
    (D.rigidification_base_comp_eq R α)

private lemma rep_hom_comp_toDoubleQuotient {X : EllObj B} (α : P.obj (op X)) :
    (D.rep X).hom ≫ D.toDoubleQuotient R hf hl hs α =
      (D.rigidification R α).base ≫ D.doubleQuotientπ R :=
  have := D.hasProperty_iff.mp hf X
  have := D.hasProperty_iff.mp hl X
  have := D.hasProperty_iff.mp hs X
  EffectiveEpi.fac _ _ (D.rigidification_base_comp_eq R α)

/-- **The classifying morphism is computed by any local rigidification.** Let `α` be a
`𝒫`-structure on `X`, let `g : W ⟶ X` be an arrow of `Ell/B`, and let `d` be any `δ`-structure on
`W`. Then `g.base` followed by the classifying morphism of `α` is the image in the quotient
`𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)` of the morphism of bases of the arrow `W ⟶ V` classifying `(g^* α, d)`. -/
theorem comp_toDoubleQuotient {X W : EllObj B} (α : P.obj (op X)) (g : W ⟶ X)
    (d : Q.obj (op W)) :
    g.base ≫ D.toDoubleQuotient R hf hl hs α =
      (R.homEquiv.symm (P.map g.op α, d)).base ≫ D.doubleQuotientπ R := by
  -- `W` is the base change of `X` along `g.base`, and `d` is classified by a morphism `k` from
  -- `g.base` to the scheme `δ_X` of `δ`-structures on `X`
  let e := EllObj.isoBaseChange g
  let k : Over.mk g.base ⟶ D.rep X := (D.representableBy X).homEquiv.symm (Q.map e.inv.op d)
  have hk : k.left ≫ (D.rep X).hom = g.base := Over.w k
  have h := D.base_comp_doubleQuotientπ_eq R
    (a₁ := R.homEquiv.symm (P.map g.op α, d))
    (a₂ := e.hom ≫ X.baseChangeFunctor.map k ≫ D.rigidification R α)
    ((congrArg Prod.fst (R.homEquiv.apply_symm_apply _)).trans (by
      rw [R.homEquiv_comp, Functor.Monoidal.tensorObj_map_apply_fst,
        fst_homEquiv_rigidification, ← Functor.map_comp_apply, ← op_comp,
        EllObj.isoBaseChange_hom_comp]))
  refine (congrArg (· ≫ D.toDoubleQuotient R hf hl hs α) hk.symm).trans ?_
  rw [Category.assoc, rep_hom_comp_toDoubleQuotient, h, EllObj.comp_base, EllObj.comp_base,
    EllObj.isoBaseChange_hom_base, EllObj.baseChangeFunctor_map_base]
  -- `𝟙 W.base ≫ k.left` is `k.left`, whose source is `W.base` only up to the definition of the base
  -- change of `X` along `g.base`, so the identity is removed by a term
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ D.doubleQuotientπ R) (Category.id_comp _).symm)

/-- **Naturality of the classifying morphism.** For an arrow `f : Y ⟶ X` of `Ell/B` and a
`𝒫`-structure `α` on `X`, the classifying morphism of the pullback `f^* α` is `f.base` followed by
the classifying morphism of `α`. In particular isomorphic `𝒫`-structures on the same elliptic curve
have the same classifying morphism. -/
@[simp]
theorem toDoubleQuotient_map {X Y : EllObj B} (f : Y ⟶ X) (α : P.obj (op X)) :
    D.toDoubleQuotient R hf hl hs (P.map f.op α) = f.base ≫ D.toDoubleQuotient R hf hl hs α := by
  have := D.hasProperty_iff.mp hf Y
  have := D.hasProperty_iff.mp hl Y
  have := D.hasProperty_iff.mp hs Y
  refine (cancel_epi (D.rep Y).hom).mp ?_
  have h₁ := D.comp_toDoubleQuotient R hf hl hs (P.map f.op α)
    (Y.baseChangeFunctorHom (D.rep Y)) (D.universal Y)
  have h₂ := D.comp_toDoubleQuotient R hf hl hs α
    (Y.baseChangeFunctorHom (D.rep Y) ≫ f) (D.universal Y)
  rw [EllObj.baseChangeFunctorHom_base] at h₁
  rw [EllObj.comp_base, EllObj.baseChangeFunctorHom_base, op_comp, Functor.map_comp_apply] at h₂
  exact h₁.trans (h₂.symm.trans (Category.assoc _ _ _))

/-- **The classifying morphism of a classified structure.** The `𝒫`-structure classified by an
arrow `h : W ⟶ V` of `Ell/B` has classifying morphism `h.base` followed by the projection
`𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)`. For `h = 𝟙 V`, the projection classifies the universal
`𝒫`-structure on `V`. -/
theorem toDoubleQuotient_fst_homEquiv {W : EllObj B} (h : W ⟶ V) :
    D.toDoubleQuotient R hf hl hs (R.homEquiv h).1 = h.base ≫ D.doubleQuotientπ R := by
  have h' := D.comp_toDoubleQuotient R hf hl hs (R.homEquiv h).1 (𝟙 W) (R.homEquiv h).2
  rw [EllObj.id_base, Category.id_comp, op_id, Functor.map_id_apply] at h'
  exact h'.trans
    (congrArg (fun a : W ⟶ V ↦ a.base ≫ D.doubleQuotientπ R) (R.homEquiv.symm_apply_apply h))

/-- The classifying morphism of a `𝒫`-structure on `X = (E/S)` is a morphism of `B`-schemes from
`S` to the quotient. -/
@[reassoc (attr := simp)]
theorem toDoubleQuotient_doubleQuotientStructureMap [IsAffine V.base] [IsFinite (D.rep V).hom]
    [Flat (D.rep V).hom] [LocallyOfFinitePresentation (D.rep V).hom] (hP : P.IsRigid)
    {X : EllObj B} (α : P.obj (op X)) :
    D.toDoubleQuotient R hf hl hs α ≫ D.doubleQuotientStructureMap R hP = X.structureMap := by
  have := D.hasProperty_iff.mp hf X
  have := D.hasProperty_iff.mp hl X
  have := D.hasProperty_iff.mp hs X
  refine (cancel_epi (D.rep X).hom).mp ?_
  rw [← Category.assoc, rep_hom_comp_toDoubleQuotient]
  exact (Category.assoc _ _ _).trans <|
    (congrArg ((D.rigidification R α).base ≫ ·)
      (D.doubleQuotientπ_doubleQuotientStructureMap R hP)).trans <|
    (D.rigidification R α).base_structureMap.trans (EllObj.baseChangeFunctor_obj_structureMap _ _)

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
