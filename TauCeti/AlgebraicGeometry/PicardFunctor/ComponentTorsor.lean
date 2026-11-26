/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Torsor
public import TauCeti.AlgebraicGeometry.PicardFunctor.DegreeComponent
public import TauCeti.AlgebraicGeometry.PicardFunctor.Scheme

/-!
# The components of the Picard scheme and their torsor structure

Let `f : X ⟶ S` be a morphism of schemes. The relative Picard fppf sheaf of `f` has the
degree-`d` components `Picᵈ_{X/S}` (`relativePicardDegreeFppfSubfunctor f d`), the sections of
degree `d` on every geometric fibre. As for the whole Picard sheaf (`HasPicardScheme`), the
representability of `Picᵈ_{X/S}` is a property with a canonical representing object:
`HasPicardComponent f d` says that `Picᵈ_{X/S}` is representable, and the **degree-`d` component
of the Picard scheme** `picardComponent f d : Over S` is the representing object chosen by
Mathlib's `Functor.reprX`. When the Picard scheme exists too, `picardComponent f d` is a
subobject of it (`picardComponentι`). For a smooth proper geometrically connected curve `X` over
a field `k`, possibly without a rational point, this is `Picᵈ_{X/k}`.

For a smooth proper geometrically connected family of curves `f`:

* `Pic⁰_{X/S}` is a commutative group scheme over `S`. Its group law is the tensor product of
  line-bundle classes, transported by Yoneda from the degree-zero Picard sheaf
  `relativePicardDegreeZeroFppfSheaf f`, whose sections are those of `Pic⁰_{X/S}`
  (`relativePicardDegreeZeroFppfSheafIso`).
* `Pic⁰_{X/S}` acts on `Picᵈ_{X/S}` by tensor product (`picardComponentSMul`).
* **`Picᵈ_{X/S}` is a `Pic⁰_{X/S}`-torsor for the fppf topology** (`isTorsor_picardComponent`).
  The action is simply transitive on points, since two classes of degree `d` differ by a class of
  degree zero; and `Picᵈ_{X/S}` has a section over the fppf covering `X ⟶ S`, namely `d` times
  the class of the graph of the diagonal, a relative effective Cartier divisor of degree one
  (`relativePicardDegreeFppfSubfunctor_obj_op_mk_nonempty`). Consequently `Picᵈ_{X/S} ⟶ S` is
  surjective, and the class of the torsor in `Sheaf.NonabelianH1` is trivial exactly when
  `Picᵈ_{X/S}` has a section over `S` (`TauCeti.GroupScheme.mk_toTorsor_eq_one_iff`).

## Main declarations

* `TauCeti.AlgebraicGeometry.HasPicardComponent`: `Picᵈ_{X/S}` is representable;
* `TauCeti.AlgebraicGeometry.picardComponent`: its representing object;
* `TauCeti.AlgebraicGeometry.picardComponentι`: the monomorphism into the Picard scheme, with
  `TauCeti.AlgebraicGeometry.picardComponentLift` lifting the points of degree `d` and
  `TauCeti.AlgebraicGeometry.exists_comp_picardComponentι_eq_iff`: a point of the Picard scheme
  factors through `picardComponentι f d` exactly when its class has degree `d`;
* the instance `CommGrpObj (picardComponent f 0)`: the group law of `Pic⁰_{X/S}`;
* the instance `ModObj (picardComponent f 0) (picardComponent f d)`: the action on `Picᵈ_{X/S}`;
* `TauCeti.AlgebraicGeometry.isTorsor_picardComponent`: `Picᵈ_{X/S}` is a `Pic⁰_{X/S}`-torsor;
* the instance `TauCeti.AlgebraicGeometry.isIso_leftSMul_picardComponent`: the action is simply
  transitive, so the difference morphism of pseudo-torsors
  `TauCeti.ModObj.diff : Picᵈ_{X/S} ×_S Picᵈ_{X/S} ⟶ Pic⁰_{X/S}` applies; it sends `(L, M)` to
  `M ⊗ L⁻¹` (`TauCeti.AlgebraicGeometry.picardComponentRepresentableBy_homEquiv_diff_val`), and
  in degree zero to `M * L⁻¹` (`TauCeti.AlgebraicGeometry.lift_diff_picardComponent_zero`);
* the instance `IsMonHom (picardComponentι f 0)` and
  `TauCeti.AlgebraicGeometry.smul_comp_picardComponentι`: `Pic⁰_{X/S}` is a subgroup scheme of the
  Picard scheme, acting on `Picᵈ_{X/S}` by the restricted group law.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.4.
* B. Poonen, M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math.
  150 (1999), Section 2.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` **has a degree-`d` Picard component** when the degree-`d` component
`Picᵈ_{X/S}` of its relative Picard fppf sheaf is representable on schemes over `S`. -/
abbrev HasPicardComponent (d : ℤ) : Prop :=
  (relativePicardDegreeFppfSubfunctor f d).toFunctor.IsRepresentable

/-- The **degree-`d` component of the Picard scheme** of `f : X ⟶ S`: the representing object of
the degree-`d` component `Picᵈ_{X/S}` of the relative Picard fppf sheaf, as a scheme over `S`. -/
def picardComponent (d : ℤ) [HasPicardComponent f d] : Over S :=
  (relativePicardDegreeFppfSubfunctor f d).toFunctor.reprX

/-- The representation of `Picᵈ_{X/S}` by `picardComponent f d`: morphisms
`T ⟶ picardComponent f d` of schemes over `S` are the sections of `Picᵈ_{X/S}` over `T`. -/
def picardComponentRepresentableBy (d : ℤ) [HasPicardComponent f d] :
    (relativePicardDegreeFppfSubfunctor f d).toFunctor.RepresentableBy (picardComponent f d) :=
  Functor.representableBy _

section PicardScheme

variable (d : ℤ) [HasPicardScheme f] [HasPicardComponent f d]

/-- The inclusion of the degree-`d` component `picardComponent f d` into the Picard scheme,
representing the inclusion of `Picᵈ_{X/S}` into the relative Picard fppf sheaf. -/
def picardComponentι : picardComponent f d ⟶ picardScheme f :=
  (picardSchemeRepresentableBy f).homEquiv.symm
    ((picardComponentRepresentableBy f d).homEquiv (𝟙 _)).val

/-- A point of `picardComponent f d`, composed with the inclusion into the Picard scheme, is the
section of the relative Picard fppf sheaf it represents. -/
theorem picardSchemeRepresentableBy_homEquiv_comp_picardComponentι {T : Over S}
    (φ : T ⟶ picardComponent f d) :
    (picardSchemeRepresentableBy f).homEquiv (φ ≫ picardComponentι f d) =
      ((picardComponentRepresentableBy f d).homEquiv φ).val := by
  rw [picardComponentι, (picardSchemeRepresentableBy f).homEquiv_comp, Equiv.apply_symm_apply,
    ← Category.comp_id φ, (picardComponentRepresentableBy f d).homEquiv_comp, Category.comp_id]
  -- The restriction of a section of the subfunctor `Picᵈ_{X/S}` is computed in the sheaf.
  rfl

/-- The degree-`d` component is a subobject of the Picard scheme. -/
instance : Mono (picardComponentι f d) where
  right_cancellation g h hgh := by
    refine (picardComponentRepresentableBy f d).homEquiv.injective (Subtype.ext ?_)
    rw [← picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
      ← picardSchemeRepresentableBy_homEquiv_comp_picardComponentι, hgh]

/-- A point of the Picard scheme whose class has degree `d` lifts to the degree-`d` component
`picardComponent f d`. -/
def picardComponentLift {T : Over S} (ψ : T ⟶ picardScheme f)
    (h : (picardSchemeRepresentableBy f).homEquiv ψ ∈
      (relativePicardDegreeFppfSubfunctor f d).obj (op T)) :
    T ⟶ picardComponent f d :=
  (picardComponentRepresentableBy f d).homEquiv.symm ⟨_, h⟩

/-- The lift of a point of the Picard scheme to `picardComponent f d` factors it through
`picardComponentι f d`. -/
@[reassoc (attr := simp)]
theorem picardComponentLift_comp_picardComponentι {T : Over S} (ψ : T ⟶ picardScheme f)
    (h : (picardSchemeRepresentableBy f).homEquiv ψ ∈
      (relativePicardDegreeFppfSubfunctor f d).obj (op T)) :
    picardComponentLift f d ψ h ≫ picardComponentι f d = ψ := by
  refine (picardSchemeRepresentableBy f).homEquiv.injective ?_
  rw [picardSchemeRepresentableBy_homEquiv_comp_picardComponentι, picardComponentLift,
    Equiv.apply_symm_apply]

/-- A point of the Picard scheme factors through the degree-`d` component exactly when its class
has degree `d`. -/
theorem exists_comp_picardComponentι_eq_iff {T : Over S} (ψ : T ⟶ picardScheme f) :
    (∃ φ : T ⟶ picardComponent f d, φ ≫ picardComponentι f d = ψ) ↔
      (picardSchemeRepresentableBy f).homEquiv ψ ∈
        (relativePicardDegreeFppfSubfunctor f d).obj (op T) := by
  refine ⟨?_, fun h ↦ ⟨_, picardComponentLift_comp_picardComponentι f d ψ h⟩⟩
  rintro ⟨φ, rfl⟩
  rw [picardSchemeRepresentableBy_homEquiv_comp_picardComponentι]
  exact ((picardComponentRepresentableBy f d).homEquiv φ).property

end PicardScheme

section Torsor

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
  [HasPicardComponent f 0]

/-! ### The group law of `Pic⁰` -/

/-- The representation of the degree-zero Picard sheaf, written multiplicatively, by
`picardComponent f 0`, through the identification `relativePicardDegreeZeroFppfSheafIso` of its
sections with those of `Pic⁰_{X/S}`. -/
def picardComponentZeroMulRepresentableBy :
    (((relativePicardDegreeZeroFppfSheaf f).obj ⋙ AddCommGrpCat.toCommGrp) ⋙
      forget CommGrpCat).RepresentableBy (picardComponent f 0) :=
  ((picardComponentRepresentableBy f 0).ofIso (relativePicardDegreeZeroFppfSheafIso f).symm).ofIso
    (NatIso.ofComponents (fun _ ↦ Equiv.toIso Multiplicative.ofAdd) fun _ ↦ rfl)

/-- The **group law of `Pic⁰_{X/S}`**: tensor product of line-bundle classes of degree zero,
transported by Yoneda from the degree-zero Picard sheaf written multiplicatively. -/
instance : CommGrpObj (picardComponent f 0) :=
  CommGrpObj.ofRepresentableBy (picardComponent f 0) _ (picardComponentZeroMulRepresentableBy f)

/-- The representation `picardComponentZeroMulRepresentableBy f` is
`picardComponentRepresentableBy f 0`, followed by `relativePicardDegreeZeroFppfSheafIso` and
`Multiplicative.ofAdd`. -/
lemma picardComponentZeroMulRepresentableBy_homEquiv' {T : Over S}
    (φ : T ⟶ picardComponent f 0) :
    (picardComponentZeroMulRepresentableBy f).homEquiv' φ =
      Multiplicative.ofAdd ((relativePicardDegreeZeroFppfSheafIso f).inv.app (op T)
        ((picardComponentRepresentableBy f 0).homEquiv φ)) :=
  (rfl)

-- The lemmas below about `(picardComponentRepresentableBy f d).homEquiv` are not `@[simp]`: `simp`
-- rewrites the type of the sections of `Picᵈ_{X/S}` by `Subfunctor.toFunctor_obj` and
-- `Functor.comp_obj`, after which their left-hand sides no longer match.
/-- The class represented by a section of `Pic⁰_{X/S}` is the image, under the inclusion
`relativePicardDegreeZeroFppfSheafι`, of the section of the degree-zero Picard sheaf that it
represents through `picardComponentZeroMulRepresentableBy f`. -/
theorem picardComponentRepresentableBy_homEquiv_val {T : Over S}
    (φ : T ⟶ picardComponent f 0) :
    ((picardComponentRepresentableBy f 0).homEquiv φ).val =
      (relativePicardDegreeZeroFppfSheafι f).hom.app (op T)
        ((picardComponentZeroMulRepresentableBy f).homEquiv' φ).toAdd :=
  (relativePicardDegreeZeroFppfSheafι_hom_app_relativePicardDegreeZeroFppfSheafIso_inv_app
    f _).symm

/-- The unit section of `Pic⁰_{X/S}` represents the trivial class. -/
theorem picardComponentRepresentableBy_homEquiv_one_val (T : Over S) :
    ((picardComponentRepresentableBy f 0).homEquiv (1 : T ⟶ picardComponent f 0)).val = 0 := by
  have h : (picardComponentZeroMulRepresentableBy f).homEquiv' (1 : T ⟶ picardComponent f 0) =
      1 := by
    -- `MonObj.ofRepresentableBy_one` states the unit through the representation of the sheaf
    -- composed with `forget₂`, so `Equiv.apply_symm_apply` only applies up to defeq.
    rw [Hom.one_def, MonObj.ofRepresentableBy_one, Functor.RepresentableBy.homEquiv'_comp]
    exact (congrArg _ (Equiv.apply_symm_apply _ _)).trans (map_one _)
  rw [picardComponentRepresentableBy_homEquiv_val, h]
  exact map_zero _

/-- The product of two sections of `Pic⁰_{X/S}` represents the sum of their classes, that is, the
tensor product of line-bundle classes. -/
theorem picardComponentRepresentableBy_homEquiv_mul_val {T : Over S}
    (φ ψ : T ⟶ picardComponent f 0) :
    ((picardComponentRepresentableBy f 0).homEquiv (φ * ψ)).val =
      ((picardComponentRepresentableBy f 0).homEquiv φ).val +
        ((picardComponentRepresentableBy f 0).homEquiv ψ).val := by
  let e := picardComponentZeroMulRepresentableBy f
  have h : e.homEquiv' (φ * ψ) = e.homEquiv' φ * e.homEquiv' ψ := by
    -- As for the unit, `MonObj.ofRepresentableBy_mul` states the product through the
    -- representation composed with `forget₂`, so the rewrites only apply up to defeq.
    rw [Hom.mul_def, MonObj.ofRepresentableBy_mul, Functor.RepresentableBy.homEquiv'_comp]
    refine (congrArg _ (Equiv.apply_symm_apply _ _)).trans ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) ((e.homEquiv'_comp _ _).symm.trans (congrArg _ (lift_fst φ ψ)))
      ((e.homEquiv'_comp _ _).symm.trans (congrArg _ (lift_snd φ ψ)))
  rw [picardComponentRepresentableBy_homEquiv_val, picardComponentRepresentableBy_homEquiv_val,
    picardComponentRepresentableBy_homEquiv_val, h]
  exact map_add _ _ _

/-- The inverse of a section of `Pic⁰_{X/S}` represents the negative of its class. -/
theorem picardComponentRepresentableBy_homEquiv_inv_val {T : Over S}
    (φ : T ⟶ picardComponent f 0) :
    ((picardComponentRepresentableBy f 0).homEquiv φ⁻¹).val =
      -((picardComponentRepresentableBy f 0).homEquiv φ).val :=
  eq_neg_of_add_eq_zero_left (by
    rw [← picardComponentRepresentableBy_homEquiv_mul_val, inv_mul_cancel,
      picardComponentRepresentableBy_homEquiv_one_val])

/-! ### The action of `Pic⁰` on `Picᵈ` -/

variable (d : ℤ) [HasPicardComponent f d]

/-- The **action of `Pic⁰_{X/S}` on `Picᵈ_{X/S}`** by tensor product of line-bundle classes: the
morphism representing the sum of the two projections, which has degree `0 + d = d`. -/
def picardComponentSMul : picardComponent f 0 ⊗ picardComponent f d ⟶ picardComponent f d :=
  (picardComponentRepresentableBy f d).homEquiv.symm
    ⟨((picardComponentRepresentableBy f 0).homEquiv (fst _ _)).val +
        ((picardComponentRepresentableBy f d).homEquiv (snd _ _)).val, by
      have := add_mem_relativePicardDegreeFppfSubfunctor_obj f
        ((picardComponentRepresentableBy f 0).homEquiv (fst _ _)).property
        ((picardComponentRepresentableBy f d).homEquiv (snd _ _)).property
      rwa [zero_add] at this⟩

/-- Composing with the action morphism adds the represented classes of the two components. -/
private lemma picardComponentRepresentableBy_homEquiv_comp_smul_val {T : Over S}
    (g : T ⟶ picardComponent f 0 ⊗ picardComponent f d) :
    ((picardComponentRepresentableBy f d).homEquiv (g ≫ picardComponentSMul f d)).val =
      ((picardComponentRepresentableBy f 0).homEquiv (g ≫ fst _ _)).val +
        ((picardComponentRepresentableBy f d).homEquiv (g ≫ snd _ _)).val := by
  rw [(picardComponentRepresentableBy f d).homEquiv_comp, picardComponentSMul,
    Equiv.apply_symm_apply, (picardComponentRepresentableBy f 0).homEquiv_comp,
    (picardComponentRepresentableBy f d).homEquiv_comp]
  exact ((relativePicardFppfSheaf f).obj.map g.op).hom.map_add _ _

/-- `Pic⁰_{X/S}` acts on `Picᵈ_{X/S}` through `picardComponentSMul`. -/
instance : ModObj (picardComponent f 0) (picardComponent f d) where
  smul := picardComponentSMul f d
  one_smul := by
    refine (picardComponentRepresentableBy f d).homEquiv.injective (Subtype.ext ?_)
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso, leftUnitor_hom,
      picardComponentRepresentableBy_homEquiv_comp_smul_val, whiskerRight_fst, whiskerRight_snd]
    rw [toUnit_unique (fst _ _) (toUnit _), ← Hom.one_def,
      picardComponentRepresentableBy_homEquiv_one_val, zero_add]
  mul_smul := by
    refine (picardComponentRepresentableBy f d).homEquiv.injective (Subtype.ext ?_)
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso, selfLeftAction_actionObj, ← Category.assoc,
      picardComponentRepresentableBy_homEquiv_comp_smul_val]
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst,
      whiskerLeft_snd]
    rw [← Category.assoc, picardComponentRepresentableBy_homEquiv_comp_smul_val]
    simp only [Category.assoc, associator_hom_fst, associator_hom_snd_fst,
      associator_hom_snd_snd]
    rw [show fst (picardComponent f 0 ⊗ picardComponent f 0) (picardComponent f d) ≫ μ =
        (fst _ _ ≫ fst _ _) * (fst _ _ ≫ snd _ _) by
          rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id],
      picardComponentRepresentableBy_homEquiv_mul_val, add_assoc]

/-- The action of a section `m` of `Pic⁰_{X/S}` on a section `x` of `Picᵈ_{X/S}` represents the
sum of their classes, that is, the tensor product of line-bundle classes. -/
theorem picardComponentRepresentableBy_homEquiv_smul_val {T : Over S}
    (m : T ⟶ picardComponent f 0) (x : T ⟶ picardComponent f d) :
    ((picardComponentRepresentableBy f d).homEquiv (m • x)).val =
      ((picardComponentRepresentableBy f 0).homEquiv m).val +
        ((picardComponentRepresentableBy f d).homEquiv x).val := by
  rw [Hom.smul_def]
  exact (picardComponentRepresentableBy_homEquiv_comp_smul_val f d (lift m x)).trans
    (by rw [lift_fst, lift_snd])

/-- **`Pic⁰_{X/S}` acts simply transitively on `Picᵈ_{X/S}`**: the morphism
`(m, x) ↦ (m • x, x)` from `Pic⁰ ×_S Picᵈ` to `Picᵈ ×_S Picᵈ` is an isomorphism, since two
classes of degree `d` differ by a unique class of degree zero. -/
instance isIso_leftSMul_picardComponent :
    IsIso (ModObj.leftSMul (picardComponent f 0) (picardComponent f d)) := by
  rw [ModObj.isIso_leftSMul_iff]
  intro T x y
  let e₀ := picardComponentRepresentableBy f 0
  let e := picardComponentRepresentableBy f d
  have hm : (e.homEquiv y).val - (e.homEquiv x).val ∈
      (relativePicardDegreeFppfSubfunctor f 0).obj (op T) := by
    have := sub_mem_relativePicardDegreeFppfSubfunctor_obj f (e.homEquiv y).property
      (e.homEquiv x).property
    rwa [sub_self] at this
  refine ⟨e₀.homEquiv.symm ⟨_, hm⟩, ?_, fun m hm' ↦ ?_⟩
  · refine e.homEquiv.injective (Subtype.ext ?_)
    rw [picardComponentRepresentableBy_homEquiv_smul_val, Equiv.apply_symm_apply, sub_add_cancel]
  · refine e₀.homEquiv.injective (Subtype.ext ?_)
    rw [Equiv.apply_symm_apply]
    exact eq_sub_of_add_eq (by rw [← picardComponentRepresentableBy_homEquiv_smul_val, hm'])

/-- **`Picᵈ_{X/S}` is a `Pic⁰_{X/S}`-torsor** for the fppf topology, for a smooth proper
geometrically connected family of curves `f` (Poonen–Stoll, Section 2). The action is simply
transitive (`isIso_leftSMul_picardComponent`), and `Picᵈ_{X/S}` has a section over the fppf
covering `f` itself: `d` times the class of the graph of the diagonal. -/
theorem isTorsor_picardComponent :
    (Scheme.fppfTopology.over S).IsTorsor (Grp.mk (picardComponent f 0)) (picardComponent f d) where
  isIso_leftSMul := isIso_leftSMul_picardComponent f d
  coversTop := by
    have := SmoothOfRelativeDimension.smooth 1 f
    rw [Scheme.fppfTopology.coversTop_over_iff]
    obtain ⟨σ, hσ⟩ := relativePicardDegreeFppfSubfunctor_obj_op_mk_nonempty f d
    let p := (picardComponentRepresentableBy f d).homEquiv.symm ⟨σ, hσ⟩
    -- The fppf covering `f` factors through the structure morphism of `picardComponent f d`.
    refine Scheme.fppfTopology.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck f.singleton_mem_fppfPrecoverage)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact ⟨_, p.left, (picardComponent f d).hom, Presieve.singleton.mk, Over.w p⟩

/-- The structure morphism of `Picᵈ_{X/S}` is surjective, as for every torsor. -/
instance : Surjective (picardComponent f d).hom :=
  GroupScheme.surjective_of_isTorsor (isTorsor_picardComponent f d)

/-! ### The difference morphism -/

/-- The difference `ModObj.diff` of two sections `x`, `y` of `Picᵈ_{X/S}`, a section of
`Pic⁰_{X/S}`, represents the difference of their classes: `δ(x, y)` is the class of `M ⊗ L⁻¹`
when `x`, `y` are the classes of `L`, `M`. -/
theorem picardComponentRepresentableBy_homEquiv_diff_val {T : Over S}
    (x y : T ⟶ picardComponent f d) :
    ((picardComponentRepresentableBy f 0).homEquiv
        (lift x y ≫ ModObj.diff (picardComponent f 0) (picardComponent f d))).val =
      ((picardComponentRepresentableBy f d).homEquiv y).val -
        ((picardComponentRepresentableBy f d).homEquiv x).val :=
  eq_sub_of_add_eq (by
    rw [← picardComponentRepresentableBy_homEquiv_smul_val, ModObj.lift_diff_smul])

/-- `Pic⁰_{X/S}` acts on itself by its group law. -/
theorem picardComponentSMul_zero : picardComponentSMul f 0 = μ[picardComponent f 0] := by
  refine (picardComponentRepresentableBy f 0).homEquiv.injective (Subtype.ext ?_)
  -- Both sides represent the sum of the classes of the two projections.
  have hsmul := picardComponentRepresentableBy_homEquiv_comp_smul_val f 0 (𝟙 _)
  have hmul := picardComponentRepresentableBy_homEquiv_mul_val f
    (fst (picardComponent f 0) (picardComponent f 0)) (snd _ _)
  simp only [Category.id_comp] at hsmul
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  exact hsmul.trans hmul.symm

/-- In degree zero the difference is computed by the group law: `δ(L, M) = M * L⁻¹`, so
`Pic⁰_{X/S}` is the trivial torsor under itself, with the unit section as origin. -/
theorem lift_diff_picardComponent_zero {T : Over S} (x y : T ⟶ picardComponent f 0) :
    lift x y ≫ ModObj.diff (picardComponent f 0) (picardComponent f 0) = y * x⁻¹ :=
  ModObj.lift_diff_eq_mul_inv (picardComponentSMul_zero f) x y

/-! ### Compatibility with the Picard scheme -/

section PicardScheme

variable [HasPicardScheme f]

/-- The inclusion of `Pic⁰_{X/S}` into the Picard scheme is a homomorphism of group objects:
`Pic⁰_{X/S}` is a subgroup scheme of the Picard scheme. -/
instance : IsMonHom (picardComponentι f 0) where
  one_hom := by
    refine (picardSchemeRepresentableBy f).homEquiv.injective ?_
    rw [picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
      ← Category.id_comp η[picardScheme f], ← toUnit_unique (toUnit _) (𝟙 _), ← Hom.one_def,
      picardSchemeRepresentableBy_homEquiv_one, ← Category.id_comp η[picardComponent f 0],
      ← toUnit_unique (toUnit _) (𝟙 _), ← Hom.one_def,
      picardComponentRepresentableBy_homEquiv_one_val]
  mul_hom := by
    refine (picardSchemeRepresentableBy f).homEquiv.injective ?_
    rw [picardSchemeRepresentableBy_homEquiv_comp_picardComponentι, ← lift_fst_comp_snd_comp,
      ← Hom.mul_def, picardSchemeRepresentableBy_homEquiv_mul,
      picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
      picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
      ← Category.id_comp μ[picardComponent f 0], ← lift_fst_snd, ← Hom.mul_def,
      picardComponentRepresentableBy_homEquiv_mul_val]

/-- In the Picard scheme, the action of `Pic⁰_{X/S}` on `Picᵈ_{X/S}` is the restriction of the
group law. -/
theorem smul_comp_picardComponentι {T : Over S} (m : T ⟶ picardComponent f 0)
    (x : T ⟶ picardComponent f d) :
    (m • x) ≫ picardComponentι f d = (m ≫ picardComponentι f 0) * (x ≫ picardComponentι f d) := by
  refine (picardSchemeRepresentableBy f).homEquiv.injective ?_
  rw [picardSchemeRepresentableBy_homEquiv_mul,
    picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
    picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
    picardSchemeRepresentableBy_homEquiv_comp_picardComponentι,
    picardComponentRepresentableBy_homEquiv_smul_val]

end PicardScheme

end Torsor

end

end TauCeti.AlgebraicGeometry
