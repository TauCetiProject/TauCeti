/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.EquivalenceRelation
public import TauCeti.AlgebraicGeometry.Quotient.EquivalenceRelation

/-!
# The quotient of the scheme of one rigidification and its classifying map

Suppose `(𝒫, δ)` is represented by an elliptic family `V` and `δ` is relatively representable, so
that `V_{δ_V}` represents `(𝒫, δ, δ)` and its two forgetful projections `p₁, p₂ : V_{δ_V} ⟶ V`
induce morphisms of bases `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)`. Katz and Mazur construct the moduli scheme of a
rigid problem `𝒫` as the quotient of `𝕄(𝒫, δ)` by this relation. This file constructs that
quotient and the map which sends a `𝒫`-structure to a point of it.

**The classifying map.** Let `π : 𝕄(𝒫, δ) ⟶ M` be any morphism of schemes which coequalizes the
two projections, and suppose every representing morphism `δ_{E/S} ⟶ S` is an effective
epimorphism (for instance finite étale and surjective). A `𝒫`-structure `α` on `X = (E/S)` acquires
a `δ`-structure after base change to `δ_{E/S}`, and the pair is classified by a morphism
`δ_{E/S} ⟶ 𝕄(𝒫, δ)`. Two `δ`-structures on the same `𝒫`-structure form a triple, classified by
`𝕄(𝒫, δ, δ)`, so the composite with `π` does not depend on the `δ`-structure. It therefore
descends along `δ_{E/S} ⟶ S` to the **classifying map** `S ⟶ M` of `α`
(`RelRepData.classifyingMap`). It is characterised by its values on pairs: whenever `α` pulled back
along `k : Z ⟶ X` is the `𝒫`-part of a pair classified by `g : Z ⟶ V`, then
`k.base ≫ classifyingMap α = g.base ≫ π` (`RelRepData.classifyingMap_spec`). It is natural in `X`
(`RelRepData.classifyingMap_map`), and it is the only natural family with these values
(`RelRepData.eq_classifyingMap`). No rigidity is needed for this construction.

**The quotient.** The quotient `𝕄(𝒫, δ)/𝕄(𝒫, δ, δ)` is the affine coequalizer of the two
projections (`RelRepData.quotient`). If `𝒫` is rigid, `𝕄(𝒫, δ)` is affine and the representing
morphism of `δ` over `V` is finite locally free, the two projections form a finite locally free
equivalence relation (`RelRepData.doubleEquivalenceRelation`), so SGA 3, Exposé V, Théorème 4.1
applies: the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ)/𝕄(𝒫, δ, δ)` is finite locally free and surjective, it
coequalizes the relation in schemes, and the relation is its kernel pair. The quotient lies over
`B`, and the classifying map of a `𝒫`-structure on `(E/S)` is a morphism over `B`
(`RelRepData.classifyingMap_comp_quotientStructureMap`).

In Katz and Mazur's proof of Theorem 4.7.0, the universal curve over `𝕄(𝒫, δ)` then descends
along this finite locally free projection, and the classifying map identifies `𝒫` with the problem
represented by the quotient; neither of these two statements is proved here.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.classifyingMap`: the morphism `S ⟶ M` of a
  `𝒫`-structure on `(E/S)`, for a morphism `π : 𝕄(𝒫, δ) ⟶ M` coequalizing the two projections.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.quotient` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.quotientπ`: the quotient of `𝕄(𝒫, δ)` by
  `𝕄(𝒫, δ, δ)` and its projection.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.classifyingMap_spec`,
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.classifyingMap_map` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.eq_classifyingMap`: the characterisation,
  naturality and uniqueness of the classifying map.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isKernelPair_quotientπ` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isColimitQuotientCofork`: for rigid `𝒫`,
  `𝕄(𝒫, δ, δ)` is the kernel pair of the projection to the quotient, and the projection is the
  coequalizer of `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)`.

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

/-! ### Morphisms coequalizing the two projections -/

section Coequalizing

variable {M : Scheme.{u}} {π : V.base ⟶ M}

/-- **A coequalizing morphism forgets the `δ`-structure.** If `π : 𝕄(𝒫, δ) ⟶ M` coequalizes the two
projections from `𝕄(𝒫, δ, δ)`, then two arrows `f₁ f₂ : X ⟶ V` of `Ell/B` which classify pairs with
the same `𝒫`-structure have the same composite `f₁.base ≫ π = f₂.base ≫ π`: the two pairs `(p, d₁)`
and `(p, d₂)` are the two projections of the triple `(p, d₁, d₂)`. -/
theorem base_comp_eq_of_homEquiv_fst_eq
    (hπ : (V.baseChangeFunctorHom (D.rep V)).base ≫ π = (D.doubleSnd R).base ≫ π)
    {X : EllObj B} {f₁ f₂ : X ⟶ V} (h : (R.homEquiv f₁).1 = (R.homEquiv f₂).1) :
    f₁.base ≫ π = f₂.base ≫ π := by
  -- the arrow classifying the triple `(p, d₁, d₂)`
  let t := (D.doubleRepresentableBy R).homEquiv.symm
    ((R.homEquiv f₁).1, ((R.homEquiv f₁).2, (R.homEquiv f₂).2))
  have ht : (D.doubleRepresentableBy R).homEquiv t =
      ((R.homEquiv f₁).1, ((R.homEquiv f₁).2, (R.homEquiv f₂).2)) :=
    (D.doubleRepresentableBy R).homEquiv.apply_symm_apply _
  -- whiskering keeps the `𝒫`-structure and projects the pair of `δ`-structures; the triple is a
  -- literal tuple, which `rw` cannot match, so both sides are compared componentwise
  have h₁ : t ≫ V.baseChangeFunctorHom (D.rep V) = f₁ := R.homEquiv.injective (by
    rw [homEquiv_comp_baseChangeFunctorHom, ht]
    exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _)
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans (Functor.Monoidal.fst_app_apply _)))
  have h₂ : t ≫ D.doubleSnd R = f₂ := R.homEquiv.injective (by
    rw [homEquiv_comp_doubleSnd, ht]
    exact Prod.ext ((Functor.Monoidal.whiskerLeft_app_apply_fst _ _).trans h)
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans (Functor.Monoidal.snd_app_apply _)))
  rw [← h₁, ← h₂, EllObj.comp_base, EllObj.comp_base, Category.assoc, Category.assoc, hπ]

/-- The arrow to `V` classifying a `𝒫`-structure `α` on `X`, pulled back to the base change of `X`
to `δ_X`, together with the universal `δ`-structure there. -/
private noncomputable def rigidifyHom {X : EllObj B} (α : P.obj (op X)) :
    X.baseChangeFunctor.obj (D.rep X) ⟶ V :=
  R.homEquiv.symm (P.map (X.baseChangeFunctorHom (D.rep X)).op α, D.universal X)

private theorem homEquiv_rigidifyHom {X : EllObj B} (α : P.obj (op X)) :
    R.homEquiv (D.rigidifyHom R α) =
      (P.map (X.baseChangeFunctorHom (D.rep X)).op α, D.universal X) :=
  R.homEquiv.apply_symm_apply _

private theorem homEquiv_comp_rigidifyHom_fst {X Y : EllObj B} (α : P.obj (op X))
    (k : Y ⟶ X.baseChangeFunctor.obj (D.rep X)) :
    (R.homEquiv (k ≫ D.rigidifyHom R α)).1 = P.map (k ≫ X.baseChangeFunctorHom (D.rep X)).op α := by
  rw [R.homEquiv_comp, homEquiv_rigidifyHom]
  exact (Functor.Monoidal.tensorObj_map_apply_fst _ _).trans
    (by rw [op_comp, Functor.map_comp_apply])

/-- The composite of `rigidifyHom` with a coequalizing morphism `π` is constant on the fibres of
the representing morphism `δ_X ⟶ X.base`. -/
private theorem comp_rigidifyHom_base_comp_eq
    (hπ : (V.baseChangeFunctorHom (D.rep V)).base ≫ π = (D.doubleSnd R).base ≫ π)
    {X : EllObj B} (α : P.obj (op X)) {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (D.rep X).left)
    (hg : g₁ ≫ (D.rep X).hom = g₂ ≫ (D.rep X).hom) :
    g₁ ≫ (D.rigidifyHom R α).base ≫ π = g₂ ≫ (D.rigidifyHom R α).base ≫ π := by
  -- the base change `Y` of `X` to `Z`, with its two arrows to the base change of `X` to `δ_X`
  let u := X.baseChangeFunctorHom (Over.mk (g₁ ≫ (D.rep X).hom))
  have hu₁ : g₁ ≫ (X.baseChangeFunctorHom (D.rep X)).base = u.base := by
    simp only [u, EllObj.baseChangeFunctorHom_base, Over.mk_hom]
  have hu₂ : g₂ ≫ (X.baseChangeFunctorHom (D.rep X)).base = u.base := by
    simp only [u, EllObj.baseChangeFunctorHom_base, Over.mk_hom, hg]
  let k₁ := EllObj.Hom.lift (X.baseChangeFunctorHom (D.rep X)) u g₁ hu₁
  let k₂ := EllObj.Hom.lift (X.baseChangeFunctorHom (D.rep X)) u g₂ hu₂
  have hk₁ : k₁ ≫ X.baseChangeFunctorHom (D.rep X) = u := EllObj.Hom.lift_comp _ _ _ _
  have hk₂ : k₂ ≫ X.baseChangeFunctorHom (D.rep X) = u := EllObj.Hom.lift_comp _ _ _ _
  have hk₁b : k₁.base = g₁ := EllObj.Hom.lift_base _ _ _ _
  have hk₂b : k₂.base = g₂ := EllObj.Hom.lift_base _ _ _ _
  have h := D.base_comp_eq_of_homEquiv_fst_eq R hπ (f₁ := k₁ ≫ D.rigidifyHom R α)
    (f₂ := k₂ ≫ D.rigidifyHom R α) (by
      rw [homEquiv_comp_rigidifyHom_fst, homEquiv_comp_rigidifyHom_fst, hk₁, hk₂])
  rw [EllObj.comp_base, EllObj.comp_base, hk₁b, hk₂b] at h
  -- the base of the base change of `X` to `Z` is `Z` only by definition, so `rw` cannot
  -- reassociate `h`
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

variable [∀ X : EllObj B, EffectiveEpi (D.rep X).hom]

/-- **The classifying map** of a `𝒫`-structure `α` on `X = (E/S)`, with values in a scheme `M`
receiving a morphism `π : 𝕄(𝒫, δ) ⟶ M` which coequalizes the two projections from `𝕄(𝒫, δ, δ)`.
Over `δ_{E/S}`, the structure `α` and the universal `δ`-structure form a pair, classified by a
morphism `δ_{E/S} ⟶ 𝕄(𝒫, δ)`; its composite with `π` descends along the effective epimorphism
`δ_{E/S} ⟶ S` to the morphism `S ⟶ M`. It is characterised by `classifyingMap_spec`. -/
noncomputable def classifyingMap
    (hπ : (V.baseChangeFunctorHom (D.rep V)).base ≫ π = (D.doubleSnd R).base ≫ π)
    {X : EllObj B} (α : P.obj (op X)) : X.base ⟶ M :=
  EffectiveEpi.desc (D.rep X).hom ((D.rigidifyHom R α).base ≫ π)
    (D.comp_rigidifyHom_base_comp_eq R hπ α)

variable (hπ : (V.baseChangeFunctorHom (D.rep V)).base ≫ π = (D.doubleSnd R).base ≫ π)

@[reassoc]
private theorem rep_hom_comp_classifyingMap {X : EllObj B} (α : P.obj (op X)) :
    (D.rep X).hom ≫ D.classifyingMap R hπ α = (D.rigidifyHom R α).base ≫ π :=
  EffectiveEpi.fac _ _ _

/-- **The classifying map is determined by pairs.** If the pull-back of a `𝒫`-structure `α` on `X`
along an arrow `k : Z ⟶ X` of `Ell/B` is the `𝒫`-part of the pair classified by an arrow
`g : Z ⟶ V`, then the classifying map of `α` restricts along `k.base` to `g.base ≫ π`. -/
theorem classifyingMap_spec {X Z : EllObj B} (α : P.obj (op X)) (k : Z ⟶ X) (g : Z ⟶ V)
    (h : (R.homEquiv g).1 = P.map k.op α) :
    k.base ≫ D.classifyingMap R hπ α = g.base ≫ π := by
  -- test on the effective epimorphism `δ_Z ⟶ Z.base`, which maps to `δ_X` over `k.base`
  let m := (D.repIsoPullback k).hom.left ≫ pullback.fst (D.rep X).hom k.base
  have hm : m ≫ (D.rep X).hom = (D.rep Z).hom ≫ k.base := (D.isPullback k).w
  let hZ := Z.baseChangeFunctorHom (D.rep Z)
  let l := EllObj.Hom.lift (X.baseChangeFunctorHom (D.rep X)) (hZ ≫ k) m (by
    rw [EllObj.baseChangeFunctorHom_base, EllObj.comp_base, EllObj.baseChangeFunctorHom_base]
    exact hm)
  have hl : l ≫ X.baseChangeFunctorHom (D.rep X) = hZ ≫ k := EllObj.Hom.lift_comp _ _ _ _
  have hlb : l.base = m := EllObj.Hom.lift_base _ _ _ _
  have hZb : hZ.base = (D.rep Z).hom := EllObj.baseChangeFunctorHom_base _
  -- the arrows `l ≫ rigidifyHom α` and `hZ ≫ g` classify pairs with the same `𝒫`-structure
  have hp := D.base_comp_eq_of_homEquiv_fst_eq R hπ (f₁ := l ≫ D.rigidifyHom R α)
    (f₂ := hZ ≫ g) (by
      rw [homEquiv_comp_rigidifyHom_fst, hl, R.homEquiv_comp, op_comp, Functor.map_comp_apply,
        ← h]
      exact (Functor.Monoidal.tensorObj_map_apply_fst _ _).symm)
  rw [EllObj.comp_base, EllObj.comp_base, hlb, hZb] at hp
  refine (cancel_epi (D.rep Z).hom).1 ?_
  calc (D.rep Z).hom ≫ k.base ≫ D.classifyingMap R hπ α
      = m ≫ (D.rep X).hom ≫ D.classifyingMap R hπ α := by
        rw [← Category.assoc, ← hm, Category.assoc]
    _ = m ≫ (D.rigidifyHom R α).base ≫ π :=
        congrArg (m ≫ ·) (D.rep_hom_comp_classifyingMap R hπ α)
    -- the bases of the base changes of `X` and `Z` are `δ_X` and `δ_Z` only by definition, so
    -- `rw` cannot reassociate `hp`
    _ = (D.rep Z).hom ≫ g.base ≫ π :=
        (Category.assoc _ _ _).symm.trans (hp.trans (Category.assoc _ _ _))

/-- The classifying map of a `𝒫`-structure which is the `𝒫`-part of the pair classified by an arrow
`g : X ⟶ V` is `g.base ≫ π`. -/
theorem classifyingMap_eq {X : EllObj B} (α : P.obj (op X)) (g : X ⟶ V)
    (h : (R.homEquiv g).1 = α) : D.classifyingMap R hπ α = g.base ≫ π := by
  have := D.classifyingMap_spec R hπ α (𝟙 X) g (by rw [op_id, Functor.map_id_apply, h])
  rwa [EllObj.id_base, Category.id_comp] at this

/-- The classifying map of the `𝒫`-part of the pair classified by an arrow `g : X ⟶ V` is
`g.base ≫ π`. In particular, the classifying map of the `𝒫`-part of the universal pair on `V` is
`π`. -/
theorem classifyingMap_homEquiv_fst {X : EllObj B} (g : X ⟶ V) :
    D.classifyingMap R hπ (R.homEquiv g).1 = g.base ≫ π :=
  D.classifyingMap_eq R hπ _ g rfl

/-- **The classifying map is natural**: the classifying map of the pull-back of a `𝒫`-structure
along an arrow `f : X' ⟶ X` of `Ell/B` is the classifying map of the structure, restricted along
`f.base`. -/
theorem classifyingMap_map {X X' : EllObj B} (f : X' ⟶ X) (α : P.obj (op X)) :
    D.classifyingMap R hπ (P.map f.op α) = f.base ≫ D.classifyingMap R hπ α := by
  refine (cancel_epi (D.rep X').hom).1 ?_
  have hs := D.classifyingMap_spec R hπ α (X'.baseChangeFunctorHom (D.rep X') ≫ f)
    (D.rigidifyHom R (P.map f.op α)) (by
      rw [homEquiv_rigidifyHom, op_comp, Functor.map_comp_apply])
  rw [EllObj.comp_base, EllObj.baseChangeFunctorHom_base] at hs
  rw [D.rep_hom_comp_classifyingMap]
  exact hs.symm.trans (Category.assoc _ _ _)

/-- **Uniqueness of the classifying map.** A family of morphisms `c α : X.base ⟶ M`, one for each
`𝒫`-structure `α` on each object `X` of `Ell/B`, which is natural in `X` and sends the `𝒫`-part of
the pair classified by any arrow `g : X ⟶ V` to `g.base ≫ π`, is the classifying map. -/
theorem eq_classifyingMap (c : ∀ ⦃X : EllObj B⦄, P.obj (op X) → (X.base ⟶ M))
    (hc_map : ∀ ⦃X X' : EllObj B⦄ (f : X' ⟶ X) (α : P.obj (op X)),
      c (P.map f.op α) = f.base ≫ c α)
    (hc : ∀ ⦃X : EllObj B⦄ (g : X ⟶ V), c (R.homEquiv g).1 = g.base ≫ π)
    {X : EllObj B} (α : P.obj (op X)) : c α = D.classifyingMap R hπ α := by
  refine (cancel_epi (D.rep X).hom).1 ?_
  have hr : (R.homEquiv (D.rigidifyHom R α)).1 =
      P.map (X.baseChangeFunctorHom (D.rep X)).op α := by
    rw [homEquiv_rigidifyHom]
  rw [D.rep_hom_comp_classifyingMap, ← hc, hr, hc_map]
  exact congrArg (· ≫ c α) (EllObj.baseChangeFunctorHom_base (X := X) (D.rep X)).symm

/-- **The classifying map lies over `B`.** If `s : M ⟶ B` restricts along `π` to the structure
morphism of `𝕄(𝒫, δ)`, then the classifying map of every `𝒫`-structure on `(E/S)` is a morphism over
`B`. -/
@[reassoc]
theorem classifyingMap_comp {s : M ⟶ B} (hs : π ≫ s = V.structureMap) {X : EllObj B}
    (α : P.obj (op X)) : D.classifyingMap R hπ α ≫ s = X.structureMap := by
  refine (cancel_epi (D.rep X).hom).1 ?_
  rw [D.rep_hom_comp_classifyingMap_assoc]
  -- the base of the base change of `X` to `δ_X` is `δ_X` only by definition, so `rw` cannot
  -- reassociate the goal
  exact (Category.assoc _ _ _).trans (by
    rw [hs]
    exact (EllObj.Hom.base_structureMap _).trans (EllObj.baseChangeFunctor_obj_structureMap _ _))

end Coequalizing

/-! ### The quotient of the scheme of one rigidification -/

/-- **The quotient** `𝕄(𝒫, δ)/𝕄(𝒫, δ, δ)` of the scheme of one rigidification by the scheme of two
rigidifications: the affine coequalizer of the morphisms of bases of the two forgetful projections,
the spectrum of the ring of functions on `𝕄(𝒫, δ)` whose two pull-backs to `𝕄(𝒫, δ, δ)` agree. -/
noncomputable abbrev quotient : Scheme.{u} :=
  (V.baseChangeFunctorHom (D.rep V)).base.affineCoequalizer (D.doubleSnd R).base

/-- The projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫, δ)/𝕄(𝒫, δ, δ)` to the quotient. -/
noncomputable abbrev quotientπ : V.base ⟶ D.quotient R :=
  (V.baseChangeFunctorHom (D.rep V)).base.affineCoequalizerπ (D.doubleSnd R).base

/-- The projection to the quotient coequalizes the two forgetful projections. -/
@[reassoc]
theorem quotient_condition :
    (V.baseChangeFunctorHom (D.rep V)).base ≫ D.quotientπ R =
      (D.doubleSnd R).base ≫ D.quotientπ R :=
  Scheme.Hom.affineCoequalizer_condition _ _

section Quotient

variable [IsAffine V.base] [hfin : IsFinite (D.rep V).hom] [hflat : Flat (D.rep V).hom]
  [hlfp : LocallyOfFinitePresentation (D.rep V).hom] (hP : P.IsRigid)
include hfin hflat hlfp hP

-- the two projections form an equivalence relation whose first projection is finite locally free,
-- which are the hypotheses of the affine quotient; the first projection has morphism of bases
-- `(D.rep V).hom` (`EllObj.baseChangeFunctorHom_base`)
omit [IsAffine V.base] in
private theorem quotient_hypotheses :
    IsEquivalenceRelation (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base ∧
      IsFinite (V.baseChangeFunctorHom (D.rep V)).base ∧
      Flat (V.baseChangeFunctorHom (D.rep V)).base ∧
      LocallyOfFinitePresentation (V.baseChangeFunctorHom (D.rep V)).base :=
  ⟨(D.doubleEquivalenceRelation R hP).isEquivalenceRelation,
    by rw [EllObj.baseChangeFunctorHom_base]; exact hfin,
    by rw [EllObj.baseChangeFunctorHom_base]; exact hflat,
    by rw [EllObj.baseChangeFunctorHom_base]; exact hlfp⟩

/-- **The relation is the kernel pair of the projection to the quotient.** If `𝒫` is rigid,
`𝕄(𝒫, δ)` is affine and `δ_V ⟶ 𝕄(𝒫, δ)` is finite locally free, then `𝕄(𝒫, δ, δ)` is the fibre
product of `𝕄(𝒫, δ)` with itself over the quotient, with the two forgetful projections. -/
theorem isKernelPair_quotientπ :
    IsKernelPair (D.quotientπ R) (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base := by
  obtain ⟨_, _, _, _⟩ := D.quotient_hypotheses R hP
  exact Scheme.Hom.isKernelPair_affineCoequalizerπ _ _

/-- For rigid `𝒫`, the projection to the quotient is finite. -/
theorem isFinite_quotientπ : IsFinite (D.quotientπ R) := by
  obtain ⟨_, _, _, _⟩ := D.quotient_hypotheses R hP
  infer_instance

/-- For rigid `𝒫`, the projection to the quotient is flat. -/
theorem flat_quotientπ : Flat (D.quotientπ R) := by
  obtain ⟨_, _, _, _⟩ := D.quotient_hypotheses R hP
  infer_instance

/-- For rigid `𝒫`, the projection to the quotient is surjective. -/
theorem surjective_quotientπ : Surjective (D.quotientπ R) := by
  obtain ⟨_, _, _, _⟩ := D.quotient_hypotheses R hP
  infer_instance

/-- For rigid `𝒫`, the projection to the quotient is locally of finite presentation. -/
theorem locallyOfFinitePresentation_quotientπ : LocallyOfFinitePresentation (D.quotientπ R) := by
  obtain ⟨_, _, _, _⟩ := D.quotient_hypotheses R hP
  infer_instance

/-- **The quotient is the coequalizer** of `𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` in schemes, for rigid `𝒫` with
`𝕄(𝒫, δ)` affine and `δ_V ⟶ 𝕄(𝒫, δ)` finite locally free (Katz and Mazur, proof of Theorem 4.7.0,
by SGA 3, Exposé V, Théorème 4.1). -/
noncomputable def isColimitQuotientCofork :
    IsColimit (Cofork.ofπ (D.quotientπ R) (D.quotient_condition R)) :=
  have := (D.quotient_hypotheses R hP).1
  have := (D.quotient_hypotheses R hP).2.1
  have := (D.quotient_hypotheses R hP).2.2.1
  have := (D.quotient_hypotheses R hP).2.2.2
  Scheme.Hom.isColimitAffineCoequalizerCofork _ _

/-- The structure morphism `𝕄(𝒫, δ)/𝕄(𝒫, δ, δ) ⟶ B` of the quotient, induced by the structure
morphism of `𝕄(𝒫, δ)`, which coequalizes the two projections since both lie over `B`. -/
noncomputable def quotientStructureMap : D.quotient R ⟶ B :=
  (D.isColimitQuotientCofork R hP).desc (Cofork.ofπ V.structureMap (by
    rw [EllObj.Hom.base_structureMap, EllObj.Hom.base_structureMap]))

/-- The structure morphism of the quotient restricts to that of `𝕄(𝒫, δ)`. -/
@[reassoc (attr := simp)]
theorem quotientπ_comp_quotientStructureMap :
    D.quotientπ R ≫ D.quotientStructureMap R hP = V.structureMap :=
  (D.isColimitQuotientCofork R hP).fac _ WalkingParallelPair.one

/-- **The classifying map to the quotient lies over `B`.** For rigid `𝒫`, the classifying map of a
`𝒫`-structure on `(E/S)` with values in `𝕄(𝒫, δ)/𝕄(𝒫, δ, δ)` is a morphism of schemes over `B`. -/
@[reassoc (attr := simp)]
theorem classifyingMap_comp_quotientStructureMap [∀ X : EllObj B, EffectiveEpi (D.rep X).hom]
    {X : EllObj B} (α : P.obj (op X)) :
    D.classifyingMap R (D.quotient_condition R) α ≫ D.quotientStructureMap R hP =
      X.structureMap :=
  D.classifyingMap_comp R _ (D.quotientπ_comp_quotientStructureMap R hP) α

end Quotient

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
