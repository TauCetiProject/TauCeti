/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.EquivalenceRelation
public import TauCeti.AlgebraicGeometry.Quotient.EquivalenceRelation

/-!
# The quotient of a rigidified moduli scheme

Suppose `(𝒫, δ)` is represented by an elliptic family `V` over an affine scheme `𝕄(𝒫, δ)`, the
rigidifying problem `δ` is relatively representable, and its representing morphism over `V` is
finite locally free (for instance finite étale). If `𝒫` is rigid, the two forgetful projections
`𝕄(𝒫, δ, δ) ⇉ 𝕄(𝒫, δ)` form a finite locally free equivalence relation
(`RelRepData.doubleEquivalenceRelation`). Katz and Mazur construct the moduli scheme of `𝒫` as its
quotient. This file forms that quotient with the affine case of SGA 3, Exposé V, Théorème 4.1:

* `RelRepData.doubleQuotient` is the affine scheme `𝕄(𝒫) = 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)`, whose ring of
  functions consists of the functions on `𝕄(𝒫, δ)` with equal pullbacks along both projections, and
  `RelRepData.doubleQuotientπ : 𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is the projection;
* the projection is finite locally free and surjective, `𝕄(𝒫, δ, δ)` is its kernel pair
  (`RelRepData.isKernelPair_doubleQuotientπ`), and it is the coequalizer of the two projections
  both in schemes and in fppf sheaves;
* every property of morphisms that descends along fpqc coverings, such as being étale or smooth,
  passes from the rigidifying cover to the projection (`RelRepData.doubleQuotientπ_mem`).

The quotient has the expected points (`RelRepData.base_comp_doubleQuotientπ_eq_iff`): two
rigidified `𝒫`-structures have the same image in `𝕄(𝒫)` exactly when there is an arrow of `Ell/B`
between their curves, over the given morphism of bases, carrying one `𝒫`-structure to the other.
The rigidifications play no role, so `𝕄(𝒫)` sees only the `𝒫`-structures up to isomorphism.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleQuotient`: the quotient `𝕄(𝒫)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.doubleQuotientπ`: the projection
  `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isKernelPair_doubleQuotientπ`: the scheme of
  two rigidifications is `𝕄(𝒫, δ) ×_{𝕄(𝒫)} 𝕄(𝒫, δ)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isColimitDoubleQuotientCofork` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isColimitFppfYonedaDoubleQuotientCofork`:
  `𝕄(𝒫)` is the coequalizer of the two projections in schemes and in fppf sheaves.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.base_comp_doubleQuotientπ_eq_iff`: two
  rigidified `𝒫`-structures have the same image in `𝕄(𝒫)` if and only if their `𝒫`-structures are
  isomorphic.

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

/-- The **quotient of a rigidified moduli scheme** `𝕄(𝒫) = 𝕄(𝒫, δ) / 𝕄(𝒫, δ, δ)`: the affine
coequalizer of the two forgetful projections from the scheme of two rigidifications to the base
`𝕄(𝒫, δ)` of `V`. It is the spectrum of the ring of functions on `𝕄(𝒫, δ)` whose pullbacks along
both projections agree. When `𝕄(𝒫, δ)` is affine, `𝒫` is rigid and the rigidifying cover is finite
locally free, it is the quotient of `𝕄(𝒫, δ)` by the equivalence relation
`RelRepData.doubleEquivalenceRelation` (`RelRepData.isColimitDoubleQuotientCofork`). -/
noncomputable def doubleQuotient : Scheme.{u} :=
  (V.baseChangeFunctorHom (D.rep V)).base.affineCoequalizer (D.doubleSnd R).base

/-- The projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` from the base of `V` to the quotient
`RelRepData.doubleQuotient`. -/
noncomputable def doubleQuotientπ : V.base ⟶ D.doubleQuotient R :=
  (V.baseChangeFunctorHom (D.rep V)).base.affineCoequalizerπ (D.doubleSnd R).base

/-- The quotient of a rigidified moduli scheme is affine. -/
instance isAffine_doubleQuotient : IsAffine (D.doubleQuotient R) := by
  -- `doubleQuotient` is by definition the spectrum of a ring
  unfold doubleQuotient
  infer_instance

/-- The projection to the quotient coequalizes the two forgetful projections from the scheme of
two rigidifications. -/
@[reassoc]
theorem doubleQuotientπ_condition :
    (V.baseChangeFunctorHom (D.rep V)).base ≫ D.doubleQuotientπ R =
      (D.doubleSnd R).base ≫ D.doubleQuotientπ R :=
  Scheme.Hom.affineCoequalizer_condition _ _

/-- The projection to the quotient takes equal values on the bases of two arrows into `V` which
classify the same `𝒫`-structure: both are projections of an arrow into the scheme of two
rigidifications. -/
theorem base_comp_doubleQuotientπ_eq_of_fst_eq {X : EllObj B} {f g : X ⟶ V}
    (h : (R.homEquiv f).1 = (R.homEquiv g).1) :
    f.base ≫ D.doubleQuotientπ R = g.base ≫ D.doubleQuotientπ R := by
  have h₁ := congrArg EllObj.Hom.base (D.doubleLift_comp_baseChangeFunctorHom R f g)
  have h₂ := congrArg EllObj.Hom.base (D.doubleLift_comp_doubleSnd R h)
  rw [EllObj.comp_base] at h₁ h₂
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, doubleQuotientπ_condition]

variable [IsAffine V.base] [IsFinite (D.rep V).hom] [Flat (D.rep V).hom]
  [LocallyOfFinitePresentation (D.rep V).hom]

-- the two forgetful projections form an equivalence relation whose first projection has morphism
-- of bases `(D.rep V).hom`, so the affine case of SGA 3 V 4.1 applies to them
omit [IsAffine V.base] in
private theorem isEquivalenceRelation_and (hP : P.IsRigid) :
    IsEquivalenceRelation (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base ∧
      IsFinite (V.baseChangeFunctorHom (D.rep V)).base ∧
      Flat (V.baseChangeFunctorHom (D.rep V)).base ∧
      LocallyOfFinitePresentation (V.baseChangeFunctorHom (D.rep V)).base := by
  refine ⟨(D.doubleEquivalenceRelation R hP).isEquivalenceRelation, ?_, ?_, ?_⟩ <;>
    rwa [EllObj.baseChangeFunctorHom_base]

-- SGA 3 V 4.1 for affine schemes, applied to the equivalence relation of two rigidifications
private theorem isKernelPair_and (hP : P.IsRigid) :
    IsKernelPair (D.doubleQuotientπ R) (V.baseChangeFunctorHom (D.rep V)).base
        (D.doubleSnd R).base ∧
      IsFinite (D.doubleQuotientπ R) ∧ Flat (D.doubleQuotientπ R) ∧
      Surjective (D.doubleQuotientπ R) ∧ LocallyOfFinitePresentation (D.doubleQuotientπ R) := by
  have h := D.isEquivalenceRelation_and R hP
  have := h.1
  have := h.2.1
  have := h.2.2.1
  have := h.2.2.2
  -- `doubleQuotientπ` is by definition the projection to the affine coequalizer
  unfold doubleQuotientπ
  exact ⟨Scheme.Hom.isKernelPair_affineCoequalizerπ _ _, Scheme.Hom.isFinite_affineCoequalizerπ _ _,
    Scheme.Hom.flat_affineCoequalizerπ _ _, Scheme.Hom.surjective_affineCoequalizerπ _ _,
    Scheme.Hom.locallyOfFinitePresentation_affineCoequalizerπ _ _⟩

/-- **The scheme of two rigidifications is the kernel pair of the quotient map.** If `𝒫` is rigid,
`𝕄(𝒫, δ, δ)` is the fibre product `𝕄(𝒫, δ) ×_{𝕄(𝒫)} 𝕄(𝒫, δ)`, with the two forgetful projections
as its projections. -/
theorem isKernelPair_doubleQuotientπ (hP : P.IsRigid) :
    IsKernelPair (D.doubleQuotientπ R) (V.baseChangeFunctorHom (D.rep V)).base
      (D.doubleSnd R).base :=
  (D.isKernelPair_and R hP).1

/-- If `𝒫` is rigid, the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is finite. -/
theorem isFinite_doubleQuotientπ (hP : P.IsRigid) : IsFinite (D.doubleQuotientπ R) :=
  (D.isKernelPair_and R hP).2.1

/-- If `𝒫` is rigid, the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is flat. -/
theorem flat_doubleQuotientπ (hP : P.IsRigid) : Flat (D.doubleQuotientπ R) :=
  (D.isKernelPair_and R hP).2.2.1

/-- If `𝒫` is rigid, the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is surjective. -/
theorem surjective_doubleQuotientπ (hP : P.IsRigid) : Surjective (D.doubleQuotientπ R) :=
  (D.isKernelPair_and R hP).2.2.2.1

/-- If `𝒫` is rigid, the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_doubleQuotientπ (hP : P.IsRigid) :
    LocallyOfFinitePresentation (D.doubleQuotientπ R) :=
  (D.isKernelPair_and R hP).2.2.2.2

/-- **Properties of the rigidifying cover descend to the quotient map.** If `𝒫` is rigid, every
property of morphisms of schemes that descends along surjective, flat, quasi-compact morphisms
passes from the representing morphism of the rigidifying problem over `V` to the projection
`𝕄(𝒫, δ) ⟶ 𝕄(𝒫)`. In particular, for a finite étale rigidifier the projection is finite étale. -/
theorem doubleQuotientπ_mem (hP : P.IsRigid) {W : MorphismProperty Scheme.{u}}
    [W.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (h : W (D.rep V).hom) :
    W (D.doubleQuotientπ R) := by
  have := D.isFinite_doubleQuotientπ R hP
  rw [← EllObj.baseChangeFunctorHom_base] at h
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (D.isKernelPair_doubleQuotientπ R hP)
    ⟨⟨D.surjective_doubleQuotientπ R hP, D.flat_doubleQuotientπ R hP⟩, inferInstance⟩ h

/-- **The quotient is the coequalizer in schemes.** If `𝒫` is rigid, the projection
`𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is the coequalizer of the two forgetful projections from the scheme of two
rigidifications. -/
noncomputable def isColimitDoubleQuotientCofork (hP : P.IsRigid) :
    IsColimit (Cofork.ofπ _ (D.doubleQuotientπ_condition R) :
      Cofork (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base) :=
  have h := D.isEquivalenceRelation_and R hP
  have := h.1
  have := h.2.1
  have := h.2.2.1
  have := h.2.2.2
  Scheme.Hom.isColimitAffineCoequalizerCofork _ _

/-- **The quotient is the fppf quotient sheaf.** If `𝒫` is rigid, then under the Yoneda embedding
into fppf sheaves, the projection `𝕄(𝒫, δ) ⟶ 𝕄(𝒫)` is the coequalizer of the two forgetful
projections from the scheme of two rigidifications. -/
noncomputable def isColimitFppfYonedaDoubleQuotientCofork (hP : P.IsRigid) :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map (D.doubleQuotientπ R))
        (by rw [← Functor.map_comp, doubleQuotientπ_condition, Functor.map_comp]) :
      Cofork (Scheme.fppfTopology.yoneda.map (V.baseChangeFunctorHom (D.rep V)).base)
        (Scheme.fppfTopology.yoneda.map (D.doubleSnd R).base)) :=
  have h := D.isEquivalenceRelation_and R hP
  have := h.1
  have := h.2.1
  have := h.2.2.1
  have := h.2.2.2
  Scheme.Hom.isColimitFppfYonedaAffineCoequalizerCofork _ _

/-- **Points of the quotient are isomorphism classes of `𝒫`-structures.** Let `𝒫` be rigid, with
`𝕄(𝒫, δ)` affine and the rigidifying cover finite locally free. Let arrows `f : X ⟶ V` and
`g : Y ⟶ V` of `Ell/B` classify rigidified `𝒫`-structures `(p, d)` on `X` and `(q, d')` on `Y`, and
let `e` be a morphism from the base of `X` to the base of `Y`. Then the two points `f.base` and
`e ≫ g.base` of `𝕄(𝒫, δ)` have the same image in `𝕄(𝒫)` if and only if some arrow `X ⟶ Y` of
`Ell/B` over `e` pulls `q` back to `p`. The rigidifications `d` and `d'` are arbitrary. -/
theorem base_comp_doubleQuotientπ_eq_iff (hP : P.IsRigid) {X Y : EllObj B} (f : X ⟶ V)
    (g : Y ⟶ V) (e : X.base ⟶ Y.base) :
    f.base ≫ D.doubleQuotientπ R = e ≫ g.base ≫ D.doubleQuotientπ R ↔
      ∃ σ : X ⟶ Y, σ.base = e ∧ P.map σ.op (R.homEquiv g).1 = (R.homEquiv f).1 := by
  constructor
  · intro h
    -- the two points of `𝕄(𝒫, δ)` come from a point `k` of the kernel pair `𝕄(𝒫, δ, δ)`
    have hk := D.isKernelPair_doubleQuotientπ R hP
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, k ≫ (V.baseChangeFunctorHom (D.rep V)).base = f.base ∧
        k ≫ (D.doubleSnd R).base = e ≫ g.base :=
      ⟨hk.lift f.base (e ≫ g.base) (by rw [Category.assoc, h]), hk.lift_fst _ _ _,
        hk.lift_snd _ _ _⟩
    -- `k` lifts to an arrow `l : X ⟶ V_{δ_V}` whose first projection is `f`; its second projection
    -- lies over `e ≫ g.base`, so it factors through `g` over `e`
    obtain ⟨l, hl₁, hl⟩ : ∃ l : X ⟶ V.baseChangeFunctor.obj (D.rep V),
        l ≫ V.baseChangeFunctorHom (D.rep V) = f ∧ l.base = k :=
      ⟨EllObj.Hom.lift _ f k hk₁, EllObj.Hom.lift_comp _ _ _ _, EllObj.Hom.lift_base _ _ _ _⟩
    have hl₂ : e ≫ g.base = (l ≫ D.doubleSnd R).base := by rw [EllObj.comp_base, hl, hk₂]
    refine ⟨EllObj.Hom.lift g (l ≫ D.doubleSnd R) e hl₂, EllObj.Hom.lift_base _ _ _ _, ?_⟩
    calc P.map (EllObj.Hom.lift g (l ≫ D.doubleSnd R) e hl₂).op (R.homEquiv g).1
        = (R.homEquiv (EllObj.Hom.lift g (l ≫ D.doubleSnd R) e hl₂ ≫ g)).1 := by
          rw [R.homEquiv_comp]
          exact (Functor.Monoidal.tensorObj_map_apply_fst _ _).symm
      _ = (R.homEquiv f).1 := by
          rw [EllObj.Hom.lift_comp, fst_homEquiv_comp_doubleSnd, hl₁]
  · rintro ⟨σ, rfl, hσ⟩
    rw [← Category.assoc, ← EllObj.comp_base]
    refine D.base_comp_doubleQuotientπ_eq_of_fst_eq R ?_
    rw [R.homEquiv_comp]
    exact hσ.symm.trans (Functor.Monoidal.tensorObj_map_apply_fst _ _).symm

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
