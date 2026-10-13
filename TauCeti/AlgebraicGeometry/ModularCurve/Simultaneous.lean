/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# Simultaneous moduli problems with a representable factor

Let `𝒫` be a relatively representable moduli problem over `Ell/B`, with representing schemes
`𝒫_{E/S}`, and let `𝒬` be a moduli problem represented by an object `U = (E_U/M)` of `Ell/B`.
Then the simultaneous problem `(𝒫, 𝒬)`, the product presheaf `𝒫 ⊗ 𝒬`, is representable: it is
represented by the base change of `E_U` to the representing scheme `𝒫_U = 𝒫_{E_U/M}`
(`ModuliProblem.RelRepData.tensorRepresentableBy`). The universal object carries the universal
`𝒫`-structure of `𝒫_U` (`ModuliProblem.RelRepData.universal`) and the pull-back of the universal
`𝒬`-structure of `U`.

These are the formal steps in Katz and Mazur's passage from relative representability to
representability. For a rigidifying problem `δ` represented by an object over an affine base, the
simultaneous problem `(𝒫, δ)` is represented over `𝒫_U`, which is affine when `𝒫` is affine over
`Ell/B`. If moreover `𝒫` is rigid, then the scheme `𝕄(𝒫, δ, δ)` representing `(𝒫, δ, δ)` maps by a
monomorphism to `𝕄(𝒫, δ) ×_B 𝕄(𝒫, δ)` through its two projections
(`ModuliProblem.IsRigid.mono_pullback_lift`). Thus `𝕄(𝒫, δ, δ)` is a relation on `𝕄(𝒫, δ)`, and
Katz and Mazur represent `𝒫` by the quotient of `𝕄(𝒫, δ)` by this relation.

The proof uses that every arrow `g : X ⟶ U` of `Ell/B` exhibits `X` as the base change of `U` along
`g.base` (`EllObj.isoBaseChange`). Under this identification a `𝒫`-structure on `X` is a morphism
`X.base ⟶ 𝒫_U` over `g.base`, and an arrow `X ⟶ U_{𝒫_U}` lifting `g` is the same datum, since the
projection `U_{𝒫_U} ⟶ U` is cartesian.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.universal`: the universal level structure
  over the representing scheme `𝒫_{E/S}`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.tensorRepresentableBy`: the simultaneous
  problem `𝒫 ⊗ 𝒬` is represented by the base change of `U` to `𝒫_U`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.homEquiv_eq_map_universal`: every level
  structure on a base change `E_T` is the pull-back of the universal one along `T ⟶ 𝒫_{E/S}`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.tensorRepresentableBy_homEquiv`: the
  bijection of `tensorRepresentableBy` pulls back the two universal level structures.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid.mono_pullback_lift`: for a rigid `𝒫`, the
  projections forgetting `𝒬₂` and `𝒬₁` induce a monomorphism from the base of the object
  representing `(𝒫, 𝒬₁, 𝒬₂)` to the fibre product over `B` of the bases of the objects
  representing `(𝒫, 𝒬₁)` and `(𝒫, 𝒬₂)`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 4, proof of Theorem 4.7.0.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} {P Q : ModuliProblem B}

namespace RelRepData

variable (D : P.RelRepData)

/-- The **universal level structure** of a relatively representable moduli problem `𝒫` over an
object `X = (E/S)` of `Ell/B`: the `𝒫`-structure on the base change of `E` to the representing
scheme `𝒫_{E/S}` which corresponds to the identity of `𝒫_{E/S}`. -/
noncomputable def universal (X : EllObj B) : P.obj (op (X.baseChangeFunctor.obj (D.rep X))) :=
  (D.representableBy X).homEquiv (𝟙 (D.rep X))

/-- Every level structure on a base change `E_T` of `X = (E/S)` is the pull-back of the universal
level structure along the corresponding morphism `T ⟶ 𝒫_{E/S}` of schemes over `S`. -/
theorem homEquiv_eq_map_universal {X : EllObj B} {T : Over X.base} (k : T ⟶ D.rep X) :
    (D.representableBy X).homEquiv k = P.map (X.baseChangeFunctor.map k).op (D.universal X) :=
  (D.representableBy X).homEquiv_eq k

variable {U : EllObj B} (R : Q.RepresentableBy U)

/-- The pair of level structures attached to an arrow `f : X ⟶ U_{𝒫_U}`: the pull-back of the
universal `𝒫`-structure, and the `𝒬`-structure classifying the composite of `f` with the
projection to `U`. -/
private noncomputable def tensorMap {X : EllObj B} (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) :
    (P ⊗ Q).obj (op X) :=
  (P.map f.op (D.universal U), R.homEquiv (f ≫ U.baseChangeFunctorHom (D.rep U)))

private theorem tensorMap_comp {X X' : EllObj B} (f : X ⟶ X')
    (g : X' ⟶ U.baseChangeFunctor.obj (D.rep U)) :
    D.tensorMap R (f ≫ g) = (P ⊗ Q).map f.op (D.tensorMap R g) := by
  -- `(P ⊗ Q).map f.op` acts componentwise on pairs, by definition of the product of presheaves
  change (P.map (f ≫ g).op _, R.homEquiv ((f ≫ g) ≫ _)) =
    (P.map f.op (P.map g.op _), Q.map f.op (R.homEquiv (g ≫ _)))
  rw [Category.assoc, R.homEquiv_comp, op_comp, Functor.map_comp_apply]

/-- The morphism of bases of an arrow `f : X ⟶ U_{𝒫_U}`, as a morphism to `𝒫_U` of schemes over
`U.base`, where `X.base` lies over `U.base` through the composite `g` of `f` with the projection
to `U`. -/
private noncomputable def overHom {X : EllObj B} {g : X ⟶ U}
    (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) (hf : f ≫ U.baseChangeFunctorHom (D.rep U) = g) :
    Over.mk g.base ⟶ D.rep U :=
  Over.homMk f.base (by
    subst hf
    simp only [EllObj.comp_base, EllObj.baseChangeFunctorHom_base, Over.mk_hom]
    -- the two sides differ only in the source of `f.base`, which is `X.base` by definition
    rfl)

private theorem overHom_left {X : EllObj B} {g : X ⟶ U}
    (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) (hf : f ≫ U.baseChangeFunctorHom (D.rep U) = g) :
    (D.overHom f hf).left = f.base :=
  (rfl)

/-- An arrow `f : X ⟶ U_{𝒫_U}` lifting `g : X ⟶ U` is the identification `EllObj.isoBaseChange g`
of `X` with the base change of `U` along `g.base`, followed by the base change of its morphism of
bases. -/
private theorem eq_isoBaseChange_hom_comp {X : EllObj B} {g : X ⟶ U}
    (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) (hf : f ≫ U.baseChangeFunctorHom (D.rep U) = g) :
    f = (EllObj.isoBaseChange g).hom ≫ U.baseChangeFunctor.map (D.overHom f hf) :=
  EllObj.hom_ext_of_comp (U.baseChangeFunctorHom (D.rep U)) (by simp [hf])
    (by
      rw [EllObj.comp_base, EllObj.isoBaseChange_hom_base, EllObj.baseChangeFunctor_map_base,
        overHom_left]
      exact (Category.id_comp _).symm)

/-- Along the identification `EllObj.isoBaseChange g`, the pull-back of the universal
`𝒫`-structure along a lift `f` of `g` is the `𝒫`-structure classified by the morphism of bases
of `f`. -/
private theorem map_universal_eq {X : EllObj B} {g : X ⟶ U}
    (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) (hf : f ≫ U.baseChangeFunctorHom (D.rep U) = g) :
    P.map f.op (D.universal U) =
      P.map (EllObj.isoBaseChange g).hom.op ((D.representableBy U).homEquiv (D.overHom f hf)) := by
  conv_lhs => rw [D.eq_isoBaseChange_hom_comp f hf]
  rw [op_comp, Functor.map_comp_apply, ← homEquiv_eq_map_universal]

private theorem tensorMap_injective {X : EllObj B} :
    Function.Injective (D.tensorMap R (X := X)) := by
  intro f f' h
  have h₁ : P.map f.op (D.universal U) = P.map f'.op (D.universal U) := congrArg Prod.fst h
  have h₂ : f ≫ U.baseChangeFunctorHom (D.rep U) = f' ≫ U.baseChangeFunctorHom (D.rep U) :=
    R.homEquiv.injective (congrArg Prod.snd h)
  refine EllObj.hom_ext_of_comp (U.baseChangeFunctorHom (D.rep U)) h₂ ?_
  rw [D.map_universal_eq f rfl, D.map_universal_eq f' h₂.symm] at h₁
  exact congrArg CommaMorphism.left ((D.representableBy U).homEquiv.injective
    ((P.mapIso (EllObj.isoBaseChange _).op).toEquiv.injective h₁))

private theorem tensorMap_surjective {X : EllObj B} :
    Function.Surjective (D.tensorMap R (X := X)) := by
  rintro ⟨α, β⟩
  obtain ⟨g, rfl⟩ := R.homEquiv.surjective β
  obtain ⟨k, hk⟩ := (D.representableBy U).homEquiv.surjective
    (P.map (EllObj.isoBaseChange g).inv.op α)
  have hg : ((EllObj.isoBaseChange g).hom ≫ U.baseChangeFunctor.map k) ≫
      U.baseChangeFunctorHom (D.rep U) = g := by
    simp
  have hk' : D.overHom _ hg = k := by
    ext
    rw [overHom_left, EllObj.comp_base, EllObj.isoBaseChange_hom_base,
      EllObj.baseChangeFunctor_map_base]
    exact Category.id_comp _
  refine ⟨(EllObj.isoBaseChange g).hom ≫ U.baseChangeFunctor.map k, Prod.ext ?_ ?_⟩
  · change P.map _ (D.universal U) = α
    rw [D.map_universal_eq _ hg, hk', hk, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id,
      op_id, Functor.map_id_apply]
  · change R.homEquiv _ = R.homEquiv g
    rw [hg]

/-- **The simultaneous problem with a representable problem is representable.** If `𝒫` is
relatively representable and `𝒬` is represented by an object `U = (E_U/M)` of `Ell/B`, then the
simultaneous problem `(𝒫, 𝒬)`, the product presheaf `𝒫 ⊗ 𝒬`, is represented by the base change of
`E_U` to the representing scheme `𝒫_U` over `M`. An arrow `f : X ⟶ U_{𝒫_U}` corresponds to the pair
formed by the pull-back of the universal `𝒫`-structure along `f` and the `𝒬`-structure classifying
the composite of `f` with the projection to `U` (`tensorRepresentableBy_homEquiv`). -/
noncomputable def tensorRepresentableBy :
    (P ⊗ Q).RepresentableBy (U.baseChangeFunctor.obj (D.rep U)) where
  homEquiv := Equiv.ofBijective (D.tensorMap R) ⟨D.tensorMap_injective R, D.tensorMap_surjective R⟩
  homEquiv_comp f g := D.tensorMap_comp R f g

theorem tensorRepresentableBy_homEquiv {X : EllObj B}
    (f : X ⟶ U.baseChangeFunctor.obj (D.rep U)) :
    (D.tensorRepresentableBy R).homEquiv f =
      (P.map f.op (D.universal U), R.homEquiv (f ≫ U.baseChangeFunctorHom (D.rep U))) :=
  (rfl)

end RelRepData

/-! ### Rigidity and the two projections -/

section Rigid

variable {Q₁ Q₂ : ModuliProblem B} {V V₁ V₂ : EllObj B}
  {R : (P ⊗ (Q₁ ⊗ Q₂)).RepresentableBy V} {R₁ : (P ⊗ Q₁).RepresentableBy V₁}
  {R₂ : (P ⊗ Q₂).RepresentableBy V₂} {a₁ : V ⟶ V₁} {a₂ : V ⟶ V₂}

/-- The elementwise form of `IsRigid.mono_pullback_lift`: two morphisms `x y : T ⟶ V.base` with the
same composites with the morphisms of bases of `a₁` and of `a₂` are equal. -/
private theorem IsRigid.eq_of_comp_base_eq (hP : P.IsRigid)
    (ha₁ : R₁.homEquiv a₁ = (P ◁ fst Q₁ Q₂).app (op V) (R.homEquiv (𝟙 V)))
    (ha₂ : R₂.homEquiv a₂ = (P ◁ snd Q₁ Q₂).app (op V) (R.homEquiv (𝟙 V)))
    {T : Scheme.{u}} {x y : T ⟶ V.base} (h₁ : x ≫ a₁.base = y ≫ a₁.base)
    (h₂ : x ≫ a₂.base = y ≫ a₂.base) : x = y := by
  -- Through `V₁` and `V₂`, the base changes `ex`, `ey` of `V` along `x` and `y` are identified
  -- over `T` by isomorphisms `σ₁`, `σ₂`, which both respect the `𝒫`-structures. Rigidity of `𝒫`
  -- forces `σ₁ = σ₂`; this common isomorphism respects all three level structures, so it carries
  -- `ey` to `ex`, and comparing morphisms of bases gives `x = y`.
  let ex := V.baseChangeFunctorHom (Over.mk x)
  let ey := V.baseChangeFunctorHom (Over.mk y)
  have hh {W : EllObj B} (a : V ⟶ W) (h : x ≫ a.base = y ≫ a.base) :
      𝟙 T ≫ (ey ≫ a).base = (ex ≫ a).base := by
    simp only [ex, ey, EllObj.comp_base, EllObj.baseChangeFunctorHom_base, Over.mk_hom]
    exact (Category.id_comp _).trans h.symm
  let σ₁ := EllObj.Hom.lift (ey ≫ a₁) (ex ≫ a₁) (𝟙 T) (hh a₁ h₁)
  let σ₂ := EllObj.Hom.lift (ey ≫ a₂) (ex ≫ a₂) (𝟙 T) (hh a₂ h₂)
  have hσ₁b : σ₁.base = 𝟙 T := EllObj.Hom.lift_base _ _ _ _
  have hσ₂b : σ₂.base = 𝟙 T := EllObj.Hom.lift_base _ _ _ _
  have hσ₁ := congrArg R₁.homEquiv (EllObj.Hom.lift_comp (ey ≫ a₁) (ex ≫ a₁) (𝟙 T) (hh a₁ h₁))
  have hσ₂ := congrArg R₂.homEquiv (EllObj.Hom.lift_comp (ey ≫ a₂) (ex ≫ a₂) (𝟙 T) (hh a₂ h₂))
  have hex : R.homEquiv ex = (P ⊗ (Q₁ ⊗ Q₂)).map ex.op (R.homEquiv (𝟙 V)) := by
    rw [← R.homEquiv_comp, Category.comp_id]
  have hey : R.homEquiv ey = (P ⊗ (Q₁ ⊗ Q₂)).map ey.op (R.homEquiv (𝟙 V)) := by
    rw [← R.homEquiv_comp, Category.comp_id]
  rw [R₁.homEquiv_comp, R₁.homEquiv_comp, R₁.homEquiv_comp, ha₁] at hσ₁
  rw [R₂.homEquiv_comp, R₂.homEquiv_comp, R₂.homEquiv_comp, ha₂] at hσ₂
  generalize R.homEquiv (𝟙 V) = ξ at hσ₁ hσ₂ hex hey
  obtain ⟨p, q₁, q₂⟩ := ξ
  -- the components of these identities, read off from the definition of the product presheaves
  have hp₁ : P.map σ₁.op (P.map ey.op p) = P.map ex.op p := congrArg Prod.fst hσ₁
  have hq₁ : Q₁.map σ₁.op (Q₁.map ey.op q₁) = Q₁.map ex.op q₁ := congrArg Prod.snd hσ₁
  have hp₂ : P.map σ₂.op (P.map ey.op p) = P.map ex.op p := congrArg Prod.fst hσ₂
  have hq₂ : Q₂.map σ₂.op (Q₂.map ey.op q₂) = Q₂.map ex.op q₂ := congrArg Prod.snd hσ₂
  -- `σ₁` and `σ₂` are isomorphisms over `T`, and `σ₁ ≫ σ₂⁻¹` fixes the `𝒫`-structure
  have : IsIso σ₂ := (EllObj.isIso_iff_isIso_base _ _).2 (by rw [hσ₂b]; exact IsIso.id T)
  have hinv : (inv σ₂).base = 𝟙 T := by
    have h := congrArg EllObj.Hom.base (IsIso.inv_hom_id σ₂)
    rw [EllObj.comp_base, hσ₂b, EllObj.id_base] at h
    exact (Category.comp_id _).symm.trans h
  have hinvp : P.map (inv σ₂).op (P.map ex.op p) = P.map ey.op p := by
    rw [← hp₂, ← Functor.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id, Functor.map_id_apply]
  have hσ : σ₁ = σ₂ := by
    rw [← comp_inv_eq_id σ₂]
    refine P.isRigid_iff.1 hP _ ?_ (P.map ex.op p) ?_
    · rw [EllObj.comp_base, hσ₁b, hinv]
      exact Category.comp_id _
    · rw [op_comp, Functor.map_comp_apply, hinvp, hp₁]
  rw [hσ] at hq₁
  -- the common isomorphism carries the arrow `ey` to `ex`
  have hcomp : σ₂ ≫ ey = ex := by
    refine R.homEquiv.injective ?_
    rw [R.homEquiv_comp, hey, hex]
    -- `(P ⊗ (Q₁ ⊗ Q₂)).map` acts componentwise on triples, by definition of the product presheaf
    change (P.map σ₂.op (P.map ey.op p), Q₁.map σ₂.op (Q₁.map ey.op q₁),
      Q₂.map σ₂.op (Q₂.map ey.op q₂)) = (P.map ex.op p, Q₁.map ex.op q₁, Q₂.map ex.op q₂)
    rw [hp₂, hq₁, hq₂]
  have h := congrArg EllObj.Hom.base hcomp
  rw [EllObj.comp_base, hσ₂b] at h
  simp only [ex, ey, EllObj.baseChangeFunctorHom_base, Over.mk_hom] at h
  exact ((Category.id_comp y).symm.trans h).symm

/-- **Rigidity separates the two projections** (the monomorphism step in Katz and Mazur's proof
of Theorem 4.7.0). Let `𝒫` be rigid, and let `V`, `V₁` and `V₂` represent the simultaneous
problems `(𝒫, 𝒬₁, 𝒬₂)`, `(𝒫, 𝒬₁)` and `(𝒫, 𝒬₂)`. Let `a₁ : V ⟶ V₁` and `a₂ : V ⟶ V₂` be the arrows
which forget `𝒬₂`, respectively `𝒬₁`, that is, which classify the corresponding parts of the
universal level structure on `V`. Then the morphism of bases `V.base ⟶ V₁.base ×_B V₂.base` which
they induce is a monomorphism. For a rigidifying problem `δ = 𝒬₁ = 𝒬₂`, this is the statement that
`𝕄(𝒫, δ, δ) ⟶ 𝕄(𝒫, δ) ×_B 𝕄(𝒫, δ)` is a monomorphism. -/
theorem IsRigid.mono_pullback_lift (hP : P.IsRigid)
    (ha₁ : R₁.homEquiv a₁ = (P ◁ fst Q₁ Q₂).app (op V) (R.homEquiv (𝟙 V)))
    (ha₂ : R₂.homEquiv a₂ = (P ◁ snd Q₁ Q₂).app (op V) (R.homEquiv (𝟙 V))) :
    Mono (pullback.lift a₁.base a₂.base (by simp) :
      V.base ⟶ pullback V₁.structureMap V₂.structureMap) :=
  ⟨fun x y h ↦ hP.eq_of_comp_base_eq ha₁ ha₂ (by simpa using h =≫ pullback.fst _ _)
    (by simpa using h =≫ pullback.snd _ _)⟩

end Rigid

end ModuliProblem

end TauCeti.AlgebraicGeometry
