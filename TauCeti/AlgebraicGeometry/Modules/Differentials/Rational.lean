/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Stalk
public import TauCeti.AlgebraicGeometry.LineBundle.Germ
import all TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Regular differentials inside rational differentials

On an integral scheme over `Spec R`, a differential section has a rational value in
`Ω[k(X)⁄R]`: take its generic germ and use the stalk comparison for relative differentials.
The value of `d a` is `d` of the rational function represented by `a`, and rational values
commute with restriction to nonempty open subsets.

If the differential sheaf is invertible, these maps are injective. Moreover, a rational
differential is regular on an open subset precisely when it comes from the differential stalk
at every point of that subset. In particular these results apply to schemes smooth of relative
dimension one, over an arbitrary commutative base ring. This realizes the differential line
bundle as local lattices in its rational differential space, the input to comparing it with a
divisor sheaf and with the canonical bundle defined using Weil differentials.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Sections 6 and 8.
* The Stacks Project, Tag 08TE (stalks of differentials).

The generic-stalk identification uses `Scheme.relativeDifferentialsStalkEquiv`; the regularity
criterion uses `InvertibleSheaf.mem_range_genericPoint_germ_iff`.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [IsIntegral X]

/-- The generic stalk of the differential sheaf, identified with the differentials of the
function field. Both base-algebra structures are given by the generic germ of the base-ring map.
-/
def relativeDifferentialsGenericStalkEquiv :
    (X.relativeDifferentials R).presheaf.stalk (genericPoint X) ≃ₗ[X.functionField]
      Ω[X.functionField⁄R] :=
  -- `functionField` is the generic stalk; exposing the base-algebra implementation here
  -- identifies the two base-ring maps, both global pullback followed by the generic germ.
  X.relativeDifferentialsStalkEquiv R (genericPoint X)

/-- The rational value of a differential section over a nonempty open subset. -/
def rationalDifferential (U : X.Opens) [Nonempty U] :
    Γ(X.relativeDifferentials R, U) →ₗ[Γ(X, U)] Ω[X.functionField⁄R] where
  toFun s := relativeDifferentialsGenericStalkEquiv R
    ((X.relativeDifferentials R).presheaf.germ U (genericPoint X)
      (Scheme.genericPoint_mem U) s)
  map_add' s t := by simp
  map_smul' a s := by
    -- The section-ring action on function-field differentials is restriction of scalars
    -- along the generic germ, so `germ_smul` identifies the two actions.
    simp only [Scheme.Modules.germ_smul, map_smul]
    rfl

/-- The rational value is the differential's generic germ under the stalk comparison.
This is not a simp lemma: computation rules preserve `rationalDifferential` as the normal form.
-/
lemma rationalDifferential_apply (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials R, U)) :
    rationalDifferential R U s = relativeDifferentialsGenericStalkEquiv R
      ((X.relativeDifferentials R).presheaf.germ U (genericPoint X)
        (Scheme.genericPoint_mem U) s) :=
  (rfl)

/-- The rational value of `d a` is the differential of the rational function represented by `a`.
-/
@[simp]
lemma rationalDifferential_d (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    rationalDifferential R U ((X.universalDerivation R).d a) =
      KaehlerDifferential.D R X.functionField (X.germToFunctionField U a) := by
  exact X.relativeDifferentialsStalkEquiv_germ_d R (genericPoint X) U
    (Scheme.genericPoint_mem U) a

/-- Restriction to a nonempty open subset preserves the rational value of a differential. -/
@[simp]
lemma rationalDifferential_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(X.relativeDifferentials R, V)) :
    rationalDifferential R U ((X.relativeDifferentials R).presheaf.map i.op s) =
      rationalDifferential R V s := by
  simp only [rationalDifferential_apply, TopCat.Presheaf.germ_res_apply]

/-- The map from a differential stalk to rational differentials, induced by specialization to
the generic stalk, linear for the local-ring action through its map to the function field. -/
def rationalDifferentialStalk (x : X) :
    (X.relativeDifferentials R).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      Ω[X.functionField⁄R] where
  toFun s := relativeDifferentialsGenericStalkEquiv R
    ((X.relativeDifferentials R).presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x)) s)
  map_add' s t := by simp
  map_smul' a s := by
    -- Represent both germs on a common neighborhood to use the section-level scalar rule.
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨V, hVU, hxV, s, rfl⟩ :=
      (X.relativeDifferentials R).presheaf.exists_le_germ_eq s hxU
    let _ : Nonempty V := ⟨⟨x, hxV⟩⟩
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a,
      ← Scheme.Modules.germ_smul]
    have hg (m : Γ(X.relativeDifferentials R, V)) :
        (X.relativeDifferentials R).presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ x))
            ((X.relativeDifferentials R).presheaf.germ V x hxV m) =
          (X.relativeDifferentials R).presheaf.germ V (genericPoint X)
            (Scheme.genericPoint_mem V) m :=
      ConcreteCategory.congr_hom
        ((X.relativeDifferentials R).presheaf.germ_stalkSpecializes hxV _) m
    rw [hg, Scheme.Modules.germ_smul, map_smul, hg]
    rw [RingHom.id_apply,
      ← IsScalarTower.algebraMap_smul X.functionField
        (X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op a)),
      X.algebraMap_germ_eq_germToFunctionField]

/-- The local rational value is specialization to the generic stalk under the stalk comparison.
This is not a simp lemma: computation rules preserve `rationalDifferentialStalk` as the normal form.
-/
lemma rationalDifferentialStalk_apply (x : X)
    (s : (X.relativeDifferentials R).presheaf.stalk x) :
    rationalDifferentialStalk R x s = relativeDifferentialsGenericStalkEquiv R
      ((X.relativeDifferentials R).presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ x)) s) :=
  (rfl)

/-- Passing from a differential section through any stalk gives its rational value. -/
@[simp]
lemma rationalDifferentialStalk_germ {U : X.Opens} [Nonempty U] (x : X) (hx : x ∈ U)
    (s : Γ(X.relativeDifferentials R, U)) :
    rationalDifferentialStalk R x ((X.relativeDifferentials R).presheaf.germ U x hx s) =
      rationalDifferential R U s := by
  exact congrArg (relativeDifferentialsGenericStalkEquiv R)
    (ConcreteCategory.congr_hom ((X.relativeDifferentials R).presheaf.germ_stalkSpecializes
      hx ((genericPoint_spec X).specializes (Set.mem_univ x))) s)

/-- The local rational-differential map sends the local differential of `a` to the
differential of its image in the function field. -/
@[simp]
lemma rationalDifferentialStalk_symm_D (x : X) (a : X.presheaf.stalk x) :
    rationalDifferentialStalk R x
        ((X.relativeDifferentialsStalkEquiv R x).symm
          (KaehlerDifferential.D R (X.presheaf.stalk x) a)) =
      KaehlerDifferential.D R X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField a) := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq a
  let _ : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [X.relativeDifferentialsStalkEquiv_symm_D_germ R x U hx a,
    rationalDifferentialStalk_germ R x hx ((X.universalDerivation R).d a),
    rationalDifferential_d, X.algebraMap_germ_eq_germToFunctionField]

section Invertible

variable [SheafOfModules.isInvertible X (X.relativeDifferentials R)]

/-- A differential section is determined by its rational value when the differential sheaf is
invertible, in particular on a scheme smooth of relative dimension one. -/
theorem rationalDifferential_injective (U : X.Opens) [Nonempty U] :
    Function.Injective (rationalDifferential R U) :=
  (relativeDifferentialsGenericStalkEquiv R).injective.comp
    (InvertibleSheaf.germ_injective_of_isIntegral ⟨X.relativeDifferentials R, inferInstance⟩
      (genericPoint X) (Scheme.genericPoint_mem U))

/-- A differential section with zero rational value is zero when the differential sheaf is
invertible. -/
@[simp]
lemma rationalDifferential_eq_zero_iff (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials R, U)) :
    rationalDifferential R U s = 0 ↔ s = 0 :=
  (injective_iff_map_eq_zero' (rationalDifferential R U)).mp
    (rationalDifferential_injective R U) s

/-- A rational differential is regular on a nonempty open subset exactly when it comes from
all the differential stalks there, provided the differential sheaf is invertible. -/
theorem mem_range_rationalDifferential_iff (U : X.Opens) [Nonempty U]
    (ω : Ω[X.functionField⁄R]) :
    ω ∈ Set.range (rationalDifferential R U) ↔
      ∀ x ∈ U, ω ∈ Set.range (rationalDifferentialStalk R x) := by
  let e := relativeDifferentialsGenericStalkEquiv R (X := X)
  have hrange {A : Type u} (f : A → (X.relativeDifferentials R).presheaf.stalk (genericPoint X)) :
      ω ∈ Set.range (fun a ↦ e (f a)) ↔ e.symm ω ∈ Set.range f := by
    simpa only [← Set.range_comp, LinearEquiv.coe_toEquiv,
      LinearEquiv.coe_symm_toEquiv, Function.comp_def] using
      (Set.mem_image_equiv (S := Set.range f) (f := e.toEquiv) (x := ω))
  -- Express the bundled maps as composites under `Set.range`; this only exposes their
  -- coercions, so the range-transport lemma applies without unfolding sheaf constructions.
  rw [show (rationalDifferential R U : _ → _) =
    (fun s ↦ e ((X.relativeDifferentials R).presheaf.germ U (genericPoint X)
      (Scheme.genericPoint_mem U) s)) from rfl, hrange]
  simp_rw [show ∀ x, (rationalDifferentialStalk R x : _ → _) =
    (fun s ↦ e ((X.relativeDifferentials R).presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x)) s)) from fun _ ↦ rfl, hrange]
  exact InvertibleSheaf.mem_range_genericPoint_germ_iff
    ⟨X.relativeDifferentials R, inferInstance⟩ (U := U) (e.symm ω)

end Invertible

end

end TauCeti.AlgebraicGeometry
