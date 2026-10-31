/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.FiniteEtale.Colimits
public import TauCeti.AlgebraicGeometry.FiniteEtale.Conservative
public import TauCeti.CategoryTheory.Limits.Shapes.SingleObj
public import TauCeti.RingTheory.Invariant.Basic

/-!
# The Galois category of finite étale covers of a connected affine scheme

Let `R` be a commutative ring and `x : Spec Ω ⟶ Spec R` a geometric point, with `Ω` separably
closed. The geometric fibre functor `FiniteEtaleScheme.fiber x` preserves quotients by finite
groups: if a finite group `G` acts on a finite étale `Spec R`-scheme `Y`, the geometric fibre of
the quotient `Y / G` is the set of `G`-orbits on the geometric fibre of `Y`. This is the quotient
part of Lenstra's axiom (G5) for a fibre functor.

Together with the axioms already established for finite étale schemes, it follows that
`FiniteEtaleScheme (Spec R)` is a `CategoryTheory.PreGaloisCategory`, that every geometric fibre
functor is a `CategoryTheory.PreGaloisCategory.FiberFunctor` when `Spec R` is connected, and
hence that finite étale schemes over a connected affine scheme form a
`CategoryTheory.GaloisCategory`. Mathlib's theory of Galois categories then applies to them: for
instance, `CategoryTheory.PreGaloisCategory.functorToContAction` is an equivalence from finite étale
schemes over `Spec R` to finite continuous sets under the automorphism group of a geometric fibre
functor.

The proof of preservation works with lifts of `x`, which are the points of the fibre
(`FiniteEtaleScheme.fiberCompInclIso`). Surjectivity on fibres holds because the quotient map is
an epimorphism and the fibre functor preserves epimorphisms. For injectivity modulo `G`, the
global sections of the quotient are the invariant global sections of `Y`, since global sections
compute quotients as invariants. Two lifts of `x` with the same image in the quotient therefore
correspond to two ring maps from the coordinate ring of `Y` to a field that agree on the
invariants, and these are conjugate under `G`
(`TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq`).

## Main results

* `PreservesColimitsOfShape (SingleObj G) (FiniteEtaleScheme.fiber x)` for a finite group `G`:
  geometric fibre functors over an affine base preserve quotients by finite groups.
* `PreGaloisCategory (FiniteEtaleScheme (Spec R))`.
* `PreGaloisCategory.FiberFunctor (FiniteEtaleScheme.fiber x)` when `Spec R` is connected.
* `GaloisCategory (FiniteEtaleScheme (Spec R))` when `Spec R` is connected.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

universe u v

namespace TauCeti.FiniteEtaleScheme

variable {R : CommRingCat.{u}} {G : Type v} [Group G]
  {F : SingleObj G ⥤ FiniteEtaleScheme (Spec R)} {c : Cocone F}

/-- An invariant global section of a finite étale `Spec R`-scheme comes from its quotient. -/
private theorem exists_appTop_eq [Finite G] (hc : IsColimit c)
    (a : Γ((F.obj (SingleObj.star G)).obj.left, ⊤))
    (ha : ∀ g : G, (F.map g).hom.left.appTop a = a) :
    ∃ b, (c.ι.app (SingleObj.star G)).hom.left.appTop b = a := by
  -- Global sections send `c` to a limit of algebras; test it against `R[X] → A`, `X ↦ a`.
  let Φ := (finiteEtaleSchemeProperty (Spec R)).ι ⋙ algΓ R
  have hc' := isColimitOfPreserves Φ hc
  let A := (Φ.obj (F.obj (SingleObj.star G))).unop
  -- The carrier of `A` is `Γ(Y, ⊤)`, and `Φ` acts on morphisms by `appTop`.
  have hX : Polynomial.aeval (R := R) (A := A) a Polynomial.X = a := Polynomial.aeval_X _
  let s : Cocone (F ⋙ Φ) :=
    { pt := .op (CommAlgCat.of R (Polynomial R))
      ι :=
        { app _ := (CommAlgCat.ofHom (Polynomial.aeval (R := R) (A := A) a)).op
          naturality _ _ g := Quiver.Hom.unop_inj <| CommAlgCat.hom_ext <|
            Polynomial.algHom_ext <| (congrArg _ hX).trans ((ha g).trans hX.symm) } }
  exact ⟨(hc'.desc s).unop Polynomial.X,
    congr(($(hc'.fac s (SingleObj.star G))).unop.hom Polynomial.X).trans hX⟩

/-- Two lifts of a point `x` to a finite étale `Spec R`-scheme with the same image in its quotient
by a finite group are conjugate under the group. -/
private theorem exists_comp_map_eq [Finite G] (hc : IsColimit c) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ Spec R) (u₁ u₂ : Over.mk x ⟶ (F.obj (SingleObj.star G)).obj)
    (h : u₁ ≫ (c.ι.app (SingleObj.star G)).hom = u₂ ≫ (c.ι.app (SingleObj.star G)).hom) :
    ∃ g : G, u₁ ≫ (F.map g).hom = u₂ := by
  let Y := (F.obj (SingleObj.star G)).obj.left
  have : IsAffine Y := isAffine_of_isAffineHom (F.obj (SingleObj.star G)).obj.hom
  -- `g` acts on `Γ(Y, ⊤)` by pullback along `F.map g⁻¹`.
  let σ : G →* Aut Y :=
    ((F ⋙ (finiteEtaleSchemeProperty (Spec R)).ι ⋙ Over.forget _).mapAut (SingleObj.star G)).comp
      ((Units.toAut G).toMonoidHom.comp toUnits.toMonoidHom)
  let _ : MulSemiringAction G Γ(Y, ⊤) := Scheme.globalSectionsMulSemiringAction σ
  have hsmul (g : G) (a : Γ(Y, ⊤)) : g • a = (F.map g⁻¹).hom.left.appTop a := by
    rw [Scheme.globalSectionsMulSemiringAction_smul_def]
    -- `(σ g⁻¹).asIso.hom` is `F.map g⁻¹` on underlying schemes, by `Functor.mapAut` and
    -- `Units.toAut`.
    rfl
  -- The ring maps given by `u₁` and `u₂` agree on the invariants, which come from the quotient.
  have hfix : u₁.left.appTop.hom.comp (algebraMap (FixedPoints.subring Γ(Y, ⊤) G) Γ(Y, ⊤)) =
      u₂.left.appTop.hom.comp (algebraMap (FixedPoints.subring Γ(Y, ⊤) G) Γ(Y, ⊤)) := by
    refine RingHom.ext fun ⟨a, ha⟩ ↦ ?_
    obtain ⟨b, rfl⟩ := exists_appTop_eq hc a fun g ↦ by
      simpa [hsmul] using ha g⁻¹
    -- Both sides are `u₁` and `u₂` composed with the leg of the quotient, on global sections.
    exact congr(($h).left.appTop b)
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq
    (FixedPoints.subring Γ(Y, ⊤) G) G (K := Γ(Spec (.of Ω), ⊤)) _ _ hfix
  refine ⟨g⁻¹, Over.OverMorphism.ext (ext_of_isAffine (CommRingCat.hom_ext
    (RingHom.ext fun a ↦ ?_)))⟩
  have := congr($hg a)
  rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, hsmul] at this
  -- `this` reads `u₁.appTop ((F.map g⁻¹).appTop a) = u₂.appTop a`, which is the goal since
  -- `appTop` of a composite is the composite of the `appTop`s.
  exact this

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre of a quotient of a finite étale `Spec R`-scheme by a finite group, as a
type, is the quotient of the geometric fibre by the group. -/
private noncomputable def isColimitInclMapCoconeFiber [Finite G] (x : Spec (.of Ω) ⟶ Spec R)
    (hc : IsColimit c) : IsColimit (FintypeCat.incl.mapCocone ((fiber x).mapCocone c)) := by
  -- The leg of a colimit over `SingleObj G` is an epimorphism.
  have : Epi (c.ι.app (SingleObj.star G)) := ⟨fun _ _ h ↦ hc.hom_ext fun ⟨⟩ ↦ h⟩
  refine SingleObj.Types.isColimitOf _
    (surjective_of_epi (FintypeCat.incl.map ((fiber x).map (c.ι.app _)))) fun y₂ y₁ h ↦ ?_
  -- Pass to lifts of `x`, the points of the fibre.
  let e := (fiberCompInclIso x).hom
  have h₁ := NatTrans.naturality_apply e (c.ι.app (SingleObj.star G)) y₁
  have h₂ := NatTrans.naturality_apply e (c.ι.app (SingleObj.star G)) y₂
  have hu : e.app _ y₁ ≫ (c.ι.app _).hom = e.app _ y₂ ≫ (c.ι.app _).hom := by
    simpa using h₁.symm.trans ((congrArg (e.app c.pt) h.symm).trans h₂)
  obtain ⟨g, hg⟩ := exists_comp_map_eq hc x _ _ hu
  refine ⟨g, (mono_iff_injective (e.app _)).mp inferInstance ?_⟩
  have h₃ : e.app _ ((fiber x).map (F.map g) y₁) = e.app _ y₂ := by
    simpa [hg] using
      NatTrans.naturality_apply e (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g) y₁
  -- The action of `g` on the fibre is, by definition, the fibre of `F.map g`.
  exact h₃

/-- **Geometric fibre functors over an affine base preserve quotients by finite groups.** The
geometric fibre of the quotient of a finite étale `Spec R`-scheme by a finite group is the set of
orbits of the group on the geometric fibre. -/
instance [Finite G] (x : Spec (.of Ω) ⟶ Spec R) :
    PreservesColimitsOfShape (SingleObj G) (fiber x) where
  preservesColimit := ⟨fun hc ↦ ⟨isColimitOfReflects FintypeCat.incl
    (isColimitInclMapCoconeFiber x hc)⟩⟩

/-- **Finite étale schemes over an affine scheme form a pre-Galois category.** -/
instance : PreGaloisCategory (FiniteEtaleScheme (Spec R)) where
  hasQuotientsByFiniteGroups _ := inferInstance
  monoInducesIsoOnDirectSummand i _ := exists_isColimit_binaryCofanMk_of_mono i

/-- **Over a connected affine scheme, every geometric fibre functor is a fibre functor** of the
Galois category of finite étale schemes. -/
instance [PreconnectedSpace (Spec R)] (x : Spec (.of Ω) ⟶ Spec R) : FiberFunctor (fiber x) where
  preservesQuotientsByFiniteGroups _ := inferInstance

/-- **Finite étale schemes over a connected affine scheme form a Galois category.** A fibre
functor is the geometric fibre at an algebraic closure of a residue field. -/
instance [ConnectedSpace (Spec R)] : GaloisCategory (FiniteEtaleScheme (Spec R)) where
  hasFiberFunctor := by
    obtain ⟨p⟩ : Nonempty (Spec R) := inferInstance
    let K := (Spec R).residueField p
    let x := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      (Spec R).fromSpecResidueField p
    exact ⟨fiber x, inferInstance⟩

end TauCeti.FiniteEtaleScheme
