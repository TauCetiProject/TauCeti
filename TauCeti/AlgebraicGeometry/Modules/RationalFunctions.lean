/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Topology.Sheaves.Flasque

/-!
# The sheaf of rational functions on an integral scheme

Mathlib defines the function field `X.functionField` of an irreducible scheme as the stalk of
its structure sheaf at the generic point, but it does not organize the rational functions into a
sheaf on `X`. On an integral scheme the sheaf of total quotient rings is the constant sheaf with
value `K(X)`, and the constant sheaf with value the stalk at the generic point is the pushforward
of the structure sheaf along the canonical morphism `Spec K(X) ⟶ X`: that morphism hits exactly
the generic point, and on an irreducible space an open subset contains the generic point as soon
as it is nonempty. This file takes that pushforward as the definition, which makes the sheaf
condition and the `𝒪_X`-module structure automatic.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem`, the elementary fact that every nonempty open
  subset of an irreducible scheme contains the generic point, and
  `TauCeti.AlgebraicGeometry.Scheme.germ_smul_functionField`, which says that a function on such
  a subset acts on the function field through its germ at any of its points;
* `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`, the canonical morphism
  `Spec K(X) ⟶ X` from the spectrum of the function field, and
  `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField_preimage`: it pulls a nonempty open
  subset back to everything;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRing`, the sheaf `𝒦_X` as a sheaf of
  commutative rings, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctions`, its underlying
  `𝒪_X`-module sheaf, and `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsSectionsEquiv`,
  the canonical identification of their sections;
* `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctionsRing` and
  `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions`, the canonical morphisms from `𝒪_X`
  as ring and module sheaves, respectively;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRingEquiv`, the identification of the
  ring of sections over a nonempty open subset with `K(X)`, compatible with restriction maps,
  together with the constant-sheaf statements it gives for the ring sheaf,
  `TauCeti.AlgebraicGeometry.Scheme.isIso_rationalFunctionsRing_map` and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctionsRing`;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv`, the identification
  `Γ(𝒦_X, U) ≃ₗ[Γ(X, U)] K(X)` of its sections over a nonempty open subset with the function
  field, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map`, the compatibility of
  these identifications with the restriction maps, and the two statements which say that `𝒦_X`
  really is the constant sheaf: `TauCeti.AlgebraicGeometry.Scheme.isIso_rationalFunctions_map`,
  the restriction maps between nonempty open subsets are isomorphisms, and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions`, the sections over an empty
  open subset vanish; together these give
  `TauCeti.AlgebraicGeometry.Scheme.isFlasque_rationalFunctions`;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul`, multiplication by a rational function
  as an endomorphism of `𝒦_X`, obtained by pushing forward multiplication by the corresponding
  global function on `Spec K(X)`; `rationalFunctionsEquiv_rationalFunctionsMul_app` identifies it
  with multiplication on sections, and `rationalFunctionsMul_mul` and `rationalFunctionsMul_one`
  make it multiplicative, so that multiplying by a unit is an automorphism of `𝒦_X`
  (`rationalFunctionsMul_comp_inv` and `rationalFunctionsMul_inv_comp`);
* the module morphism `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions` is
  `X.germToFunctionField` on sections
  (`TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app`), is
  injective on sections over every open subset of an integral scheme
  (`TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions_app_injective`), and is therefore a
  monomorphism;
* `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range`: a
  rational function lying in the local ring at every point of a nonempty open subset `U` is
  regular on `U`.

The sheaf `𝒪_X(D)` attached to a Weil divisor is the submodule of `𝒦_X` cut out by an order
bound; it is built in `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, and the
multiplication endomorphisms above are what make it depend only on the divisor class of `D`.

The Cartier divisors of `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A ("Divisors on a
curve: Weil divisors `⊕_x ℤ` and Cartier divisors; the dictionaries `Cartier ≃ line bundles`
and (smooth curve) `Weil ≃ Cartier`"), are the global sections of `𝒦_X^*/𝒪_X^*`, and the line
bundle `𝒪_X(D)` attached to a divisor is a subsheaf of `𝒦_X`; both need the sheaf `𝒦_X` and the
inclusion `𝒪_X ⟶ 𝒦_X` built here. On an integral scheme the sheaf of total quotient rings agrees
with this constant sheaf, so no generality is lost at that stage.

No formalization is vendored. The construction reuses Mathlib's `Scheme.functionField`,
`Scheme.germToFunctionField`, `Scheme.fromSpecStalk` with its computation of the closed point, of
the range and of the maps on sections, `Scheme.ΓSpecIso`, `Scheme.Modules.pushforward` and
`SheafOfModules.unitToPushforwardObjUnit`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The canonical morphism `Spec K(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme, that is, the morphism from the spectrum of the stalk at the generic point. -/
def fromSpecFunctionField : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable {X}

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
theorem genericPoint_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- A function on a nonempty open subset `U` acts on the function field through its germ at any
point of `U`. -/
theorem germ_smul_functionField {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (r : Γ(X, U))
    (f : X.functionField) : X.presheaf.germ U x hx r • f = r • f := by
  rw [Algebra.smul_def, Algebra.smul_def, Scheme.algebraMap_germ_eq_germToFunctionField,
    RingHom.algebraMap_toAlgebra]

instance instUniqueSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Unique (Spec X.functionField) where
  default := IsLocalRing.closedPoint X.functionField
  uniq p := by
    -- The morphism `Spec 𝒪_{X, x} ⟶ X` is a preimmersion, hence injective on points, and its
    -- range consists of the points specializing to `x`. Only the generic point of an irreducible
    -- space specializes to the generic point, so the source has a single point.
    refine (X.fromSpecStalk (genericPoint X)).isEmbedding.injective ?_
    refine Eq.trans ?_ Scheme.fromSpecStalk_closedPoint.symm
    have hmem : X.fromSpecStalk (genericPoint X) p ∈
        Set.range (X.fromSpecStalk (genericPoint X)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    have hclosure : closure ({genericPoint X} : Set X) ⊆
        closure ({X.fromSpecStalk (genericPoint X) p} : Set X) :=
      specializes_iff_closure_subset.mp hmem
    rw [genericPoint_closure] at hclosure
    exact ((genericPoint_spec X).eq (Set.univ_subset_iff.mp hclosure)).symm

/-- The sheaf of commutative rings underlying the rational-function sheaf: the pushforward of
the structure sheaf of `Spec K(X)` along `fromSpecFunctionField`. -/
def rationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pushforward CommRingCat (fromSpecFunctionField X).base).obj
    (Spec X.functionField).sheaf

/-- The canonical morphism of sheaves of rings `𝒪_X ⟶ 𝒦_X`. -/
def toRationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    X.sheaf ⟶ rationalFunctionsRing X where
  hom := (fromSpecFunctionField X).c

/-- The sheaf `𝒦_X` of rational functions on an integral scheme `X`: the constant sheaf with
value the function field, realized as the pushforward of the structure sheaf of `Spec K(X)`
along `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`. -/
def rationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (SheafOfModules.unit _)

/-- The module sheaf and ring sheaf constructions of `𝒦_X` have canonically identified
sections. Their underlying additive presheaves are definitionally equal because both constructions
use Mathlib's pushforward of the structure sheaf. -/
def rationalFunctionsSectionsEquiv (X : Scheme.{u}) [IrreducibleSpace X] (U : X.Opens) :
    (Γ(rationalFunctions X, U) : Type u) ≃+
      ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) :=
  AddEquiv.refl _

/-- The identification between module-sheaf and ring-sheaf sections commutes with restriction
maps. -/
@[simp]
theorem rationalFunctionsSectionsEquiv_map {U V : X.Opens} (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsSectionsEquiv X U ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctionsRing X).presheaf.map i.op (rationalFunctionsSectionsEquiv X V s) :=
  by
    unfold rationalFunctionsSectionsEquiv rationalFunctions rationalFunctionsRing
    rfl

/-- On a nonempty open subset, the morphism `Spec K(X) ⟶ X` acts on sections by the germ map to
the function field. -/
theorem fromSpecFunctionField_app (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec X.functionField).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_app (genericPoint_mem U)

/-- The morphism `Spec K(X) ⟶ X` pulls every nonempty open subset back to the whole of
`Spec K(X)`, its source having a single point, which maps to the generic point. -/
@[simp]
theorem fromSpecFunctionField_preimage (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro p _
  apply TopologicalSpace.Opens.mem_map.mpr
  rw [Subsingleton.elim p (IsLocalRing.closedPoint X.functionField),
    fromSpecFunctionField, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem U

private def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecFunctionField_preimage U)).op).symm ≪≫ Scheme.ΓSpecIso X.functionField

/-- The sections of the ring sheaf `𝒦_X` over a nonempty open subset are the function field,
as commutative rings. -/
def rationalFunctionsRingEquiv (U : X.Opens) [Nonempty U] :
    ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) ≃+* X.functionField :=
  (functionFieldSectionsIso U).commRingCatIsoToRingEquiv

private theorem app_comp_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U ≫ (functionFieldSectionsIso U).hom =
      X.germToFunctionField U := by
  rw [fromSpecFunctionField_app, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim ((homOfLE le_top).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv) (𝟙 _)]
  simp

private theorem map_comp_functionFieldSectionsIso {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    (Spec X.functionField).presheaf.map
        ((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (functionFieldSectionsIso U).hom = (functionFieldSectionsIso V).hom := by
  rw [functionFieldSectionsIso, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim (((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv)
      (eqToIso (fromSpecFunctionField_preimage V)).op.inv]

/-- The ring equivalences identifying sections of `𝒦_X` with the function field commute with
restriction maps. -/
@[simp]
theorem rationalFunctionsRingEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : (rationalFunctionsRing X).presheaf.obj (.op V)) :
    rationalFunctionsRingEquiv U ((rationalFunctionsRing X).presheaf.map i.op s) =
      rationalFunctionsRingEquiv V s := by
  unfold rationalFunctionsRing at s ⊢
  -- The presheaf of a pushforward evaluates on `U` as the source presheaf evaluates on its
  -- preimage. This normalization exposes that documented pushforward computation so that
  -- `map_comp_functionFieldSectionsIso` applies.
  change (functionFieldSectionsIso U).hom
    ((Spec X.functionField).presheaf.map
      ((Opens.map (fromSpecFunctionField X).base).map i).op
        (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V))) =
          (functionFieldSectionsIso V).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply, map_comp_functionFieldSectionsIso]
  rfl

/-- The sections of `𝒦_X` over a nonempty open subset `U` are the function field, as a module
over the functions on `U`. -/
def rationalFunctionsEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃ₗ[Γ(X, U)] X.functionField :=
  { rationalFunctionsRingEquiv U with
    map_smul' r s := by
      -- The action of `Γ(X, U)` on the pushforward is multiplication after applying the map on
      -- sections, so multiplicativity of the identification reduces this to
      -- `app_comp_functionFieldSectionsIso`.
      -- The module-sheaf section type is definitionally the carrier of the corresponding
      -- pushforward ring section, which is the form used by that comparison lemma.
      change (functionFieldSectionsIso U).hom (r • s) =
        r • (functionFieldSectionsIso U).hom s
      have h : (functionFieldSectionsIso U).hom (r • s) =
          (functionFieldSectionsIso U).hom ((fromSpecFunctionField X).app U r *
            (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U))) := rfl
      rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
        app_comp_functionFieldSectionsIso, Algebra.smul_def]
      rfl
  }

/-- The module-sheaf identification with the function field is the ring-sheaf identification
transported across `rationalFunctionsSectionsEquiv`. -/
theorem rationalFunctionsEquiv_apply (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U s =
      rationalFunctionsRingEquiv U (rationalFunctionsSectionsEquiv X U s) :=
  by
    unfold rationalFunctionsEquiv rationalFunctionsSectionsEquiv
    rfl

/-- The identifications of the sections of `𝒦_X` with the function field are compatible with the
restriction maps: `𝒦_X` is the constant sheaf. -/
@[simp]
theorem rationalFunctionsEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsEquiv U ((rationalFunctions X).presheaf.map i.op s) =
      rationalFunctionsEquiv V s := by
  rw [rationalFunctionsEquiv_apply, rationalFunctionsSectionsEquiv_map,
    rationalFunctionsRingEquiv_map, rationalFunctionsEquiv_apply]

/-- The restriction maps of `𝒦_X` between nonempty open subsets are bijective. -/
theorem rationalFunctions_map_bijective {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    Function.Bijective ((rationalFunctions X).presheaf.map i.op) := by
  constructor
  · intro a b hab
    refine (rationalFunctionsEquiv V).injective ?_
    rw [← rationalFunctionsEquiv_map i a, ← rationalFunctionsEquiv_map i b, hab]
  · intro t
    refine ⟨(rationalFunctionsEquiv V).symm (rationalFunctionsEquiv U t), ?_⟩
    refine (rationalFunctionsEquiv U).injective ?_
    rw [rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply]

/-- The restriction maps of `𝒦_X` between nonempty open subsets are isomorphisms. -/
instance isIso_rationalFunctions_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    IsIso ((rationalFunctions X).presheaf.map i.op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rationalFunctions_map_bijective i)

/-- The restriction maps of the ring sheaf `𝒦_X` between nonempty open subsets are bijective. -/
theorem rationalFunctionsRing_map_bijective {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    Function.Bijective ((rationalFunctionsRing X).presheaf.map i.op) := by
  have h : ⇑((rationalFunctionsRing X).presheaf.map i.op) =
      rationalFunctionsSectionsEquiv X U ∘ (rationalFunctions X).presheaf.map i.op ∘
        (rationalFunctionsSectionsEquiv X V).symm := by
    funext s
    rw [Function.comp_apply, Function.comp_apply, rationalFunctionsSectionsEquiv_map,
      AddEquiv.apply_symm_apply]
  rw [h]
  exact (rationalFunctionsSectionsEquiv X U).bijective.comp
    ((rationalFunctions_map_bijective i).comp (rationalFunctionsSectionsEquiv X V).symm.bijective)

/-- The restriction maps of the ring sheaf `𝒦_X` between nonempty open subsets are
isomorphisms. -/
instance isIso_rationalFunctionsRing_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    IsIso ((rationalFunctionsRing X).presheaf.map i.op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rationalFunctionsRing_map_bijective i)

/-- The sheaf `𝒦_X` has no nonzero sections over an empty open subset. -/
theorem subsingleton_rationalFunctions (U : X.Opens) (hU : U = ⊥) :
    Subsingleton Γ(rationalFunctions X, U) := by
  subst hU
  have h : (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by simp
  have : Subsingleton Γ(Spec X.functionField,
      (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens)) := by rw [h]; infer_instance
  exact this

/-- The ring sheaf `𝒦_X` has no nonzero sections over an empty open subset. -/
theorem subsingleton_rationalFunctionsRing (U : X.Opens) (hU : U = ⊥) :
    Subsingleton ((rationalFunctionsRing X).presheaf.obj (.op U)) :=
  haveI := subsingleton_rationalFunctions U hU
  (rationalFunctionsSectionsEquiv X U).symm.injective.subsingleton

/-- The sheaf `𝒦_X` of rational functions on an irreducible scheme is flasque: its restriction
maps between nonempty open subsets are bijective, and its sections over the empty open subset
vanish. -/
instance isFlasque_rationalFunctions : (rationalFunctions X).presheaf.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    by_cases hV : V.unop = ⊥
    · have := subsingleton_rationalFunctions (X := X) V.unop hV
      exact fun t ↦ ⟨0, Subsingleton.elim _ _⟩
    · have hV := (Opens.ne_bot_iff_nonempty _).mp hV
      have : Nonempty V.unop := hV.to_subtype
      have : Nonempty U.unop := (hV.mono (leOfHom i.unop)).to_subtype
      exact (rationalFunctions_map_bijective (X := X) i.unop).surjective

/-- The canonical morphism `𝒪_X ⟶ 𝒦_X`; it is an inclusion when `X` is integral, by
`toRationalFunctions_app_injective`. -/
def toRationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (rationalFunctions X) :=
  SheafOfModules.unitToPushforwardObjUnit (fromSpecFunctionField X).toRingCatSheafHom

/-- The morphisms of ring sheaves and module sheaves `𝒪_X ⟶ 𝒦_X` agree on sections. -/
@[simp]
theorem toRationalFunctionsRing_app (U : X.Opens) (r : Γ(X, U)) :
    rationalFunctionsSectionsEquiv X U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      (toRationalFunctionsRing X).hom.app (.op U) r := by
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    (fromSpecFunctionField X).toRingCatSheafHom (X := .op U) r

/-- On a nonempty open subset, the inclusion `𝒪_X ⟶ 𝒦_X` is the germ map to the function
field. -/
@[simp]
theorem rationalFunctionsEquiv_toRationalFunctions_app (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      X.germToFunctionField U r := by
  exact ConcreteCategory.congr_hom (app_comp_functionFieldSectionsIso U) r

section SectionsMul

/-- The action of a regular function on a section of `𝒦_X` is multiplication in the ring of
sections of `𝒦_X` by the image of that function. -/
theorem rationalFunctionsSectionsEquiv_smul (U : X.Opens) (r : Γ(X, U))
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsSectionsEquiv X U (r • s) =
      (toRationalFunctionsRing X).hom.app (.op U) r * rationalFunctionsSectionsEquiv X U s :=
  (rfl)

variable (X) in
/-- Multiplication of two sections of `𝒦_X` over an open subset, as a bilinear map over the
regular functions there.

The product is computed in the ring of sections of the sheaf of rings underlying `𝒦_X`; over a
nonempty open subset it is multiplication in the function field, by
`rationalFunctionsEquiv_mulBilin`. -/
def rationalFunctionsMulBilin (U : X.Opens) :
    Γ(rationalFunctions X, U) →ₗ[Γ(X, U)] Γ(rationalFunctions X, U) →ₗ[Γ(X, U)]
      Γ(rationalFunctions X, U) :=
  LinearMap.mk₂ Γ(X, U)
    (fun s t ↦ (rationalFunctionsSectionsEquiv X U).symm
      (rationalFunctionsSectionsEquiv X U s * rationalFunctionsSectionsEquiv X U t))
    (fun s s' t ↦ (rationalFunctionsSectionsEquiv X U).injective (by simp [add_mul]))
    (fun r s t ↦ (rationalFunctionsSectionsEquiv X U).injective (by
      simp [rationalFunctionsSectionsEquiv_smul, mul_assoc]))
    (fun s t t' ↦ (rationalFunctionsSectionsEquiv X U).injective (by simp [mul_add]))
    (fun r s t ↦ (rationalFunctionsSectionsEquiv X U).injective (by
      simp [rationalFunctionsSectionsEquiv_smul, mul_left_comm]))

/-- The product of two sections of `𝒦_X` is their product in the ring of sections. -/
@[simp]
theorem rationalFunctionsSectionsEquiv_mulBilin (U : X.Opens)
    (s t : Γ(rationalFunctions X, U)) :
    rationalFunctionsSectionsEquiv X U (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsSectionsEquiv X U s * rationalFunctionsSectionsEquiv X U t := by
  simp [rationalFunctionsMulBilin]

/-- Over a nonempty open subset, the product of two sections of `𝒦_X` is their product in the
function field. -/
@[simp]
theorem rationalFunctionsEquiv_mulBilin (U : X.Opens) [Nonempty U]
    (s t : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsEquiv U s * rationalFunctionsEquiv U t := by
  rw [rationalFunctionsEquiv_apply, rationalFunctionsSectionsEquiv_mulBilin, map_mul,
    rationalFunctionsEquiv_apply, rationalFunctionsEquiv_apply]

/-- Multiplying a section of `𝒦_X` by the image of a regular function is the action of that
function on the section. -/
@[simp]
theorem rationalFunctionsMulBilin_toRationalFunctions_app (U : X.Opens) (r : Γ(X, U))
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsMulBilin X U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U r) s = r • s := by
  apply (rationalFunctionsSectionsEquiv X U).injective
  rw [rationalFunctionsSectionsEquiv_mulBilin, toRationalFunctionsRing_app,
    rationalFunctionsSectionsEquiv_smul]

/-- Multiplication of sections of `𝒦_X` commutes with the restriction maps. -/
@[simp]
theorem rationalFunctionsMulBilin_map {U V : X.Opens} (i : V ⟶ U)
    (s t : Γ(rationalFunctions X, U)) :
    (rationalFunctions X).presheaf.map i.op (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsMulBilin X V ((rationalFunctions X).presheaf.map i.op s)
        ((rationalFunctions X).presheaf.map i.op t) := by
  apply (rationalFunctionsSectionsEquiv X V).injective
  rw [rationalFunctionsSectionsEquiv_map, rationalFunctionsSectionsEquiv_mulBilin,
    rationalFunctionsSectionsEquiv_mulBilin, rationalFunctionsSectionsEquiv_map,
    rationalFunctionsSectionsEquiv_map, map_mul]

end SectionsMul

section Mul

variable (X)

/-- Multiplication by a rational function, as an endomorphism of `𝒦_X`.

It is the pushforward along `Spec K(X) ⟶ X` of multiplication by the corresponding global
function on `Spec K(X)`, so no sheaf-theoretic gluing is needed to build it. -/
def rationalFunctionsMul (f : X.functionField) :
    rationalFunctions X ⟶ rationalFunctions X := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  exact (Scheme.Modules.pushforward (fromSpecFunctionField X)).map
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit _)
      ((rationalFunctionsRingEquiv (X := X) ⊤).symm f))

variable {X}

/-- Multiplication by `f` really is multiplication by `f` on sections. -/
@[simp]
theorem rationalFunctionsEquiv_rationalFunctionsMul_app (f : X.functionField) (U : X.Opens)
    [Nonempty U] (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app (rationalFunctionsMul X f) U s) =
      f * rationalFunctionsEquiv U s := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  -- The pushforward of a scalar multiplication acts on sections over `U` as the scalar
  -- multiplication over the preimage of `U`, which is multiplication in the ring of sections.
  have hval : rationalFunctionsSectionsEquiv X U
      (Scheme.Modules.Hom.app (rationalFunctionsMul X f) U s) =
      (rationalFunctionsRing X).presheaf.map (homOfLE le_top).op
          (rationalFunctionsSectionsEquiv X ⊤ ((rationalFunctionsRingEquiv (X := X) ⊤).symm f)) *
        rationalFunctionsSectionsEquiv X U s :=
    congrArg (rationalFunctionsSectionsEquiv X U)
      (ConcreteCategory.congr_hom (Scheme.Modules.globalSectionsSmul_app
        (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
        ((rationalFunctionsRingEquiv (X := X) ⊤).symm f) (fromSpecFunctionField X ⁻¹ᵁ U)) s)
  rw [rationalFunctionsEquiv_apply, hval, map_mul, rationalFunctionsRingEquiv_map,
    ← rationalFunctionsEquiv_apply]
  congr 1
  exact (rationalFunctionsRingEquiv (X := X) ⊤).apply_symm_apply f

/-- Multiplication by a product is the composite of the two multiplications. -/
@[simp]
theorem rationalFunctionsMul_mul (f g : X.functionField) :
    rationalFunctionsMul X (f * g) = rationalFunctionsMul X g ≫ rationalFunctionsMul X f := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  simp only [rationalFunctionsMul, map_mul]
  let M : (Spec X.functionField).Modules :=
    SheafOfModules.unit (Spec X.functionField).ringCatSheaf
  let F := Scheme.Modules.pushforward (fromSpecFunctionField X)
  let f' : Γ(Spec X.functionField, ⊤) := (rationalFunctionsRingEquiv (X := X) ⊤).symm f
  let g' : Γ(Spec X.functionField, ⊤) := (rationalFunctionsRingEquiv (X := X) ⊤).symm g
  -- Unfolding the local names here exposes the pushforward and scalar-multiplication wrappers;
  -- their laws can then be applied without reasoning sectionwise.
  change F.map (Scheme.Modules.globalSectionsSmul M (f' * g')) =
    F.map (Scheme.Modules.globalSectionsSmul M g') ≫
      F.map (Scheme.Modules.globalSectionsSmul M f')
  rw [Scheme.Modules.globalSectionsSmul_mul, Functor.map_comp]

/-- Multiplication by `1` is the identity. -/
@[simp]
theorem rationalFunctionsMul_one : rationalFunctionsMul X 1 = 𝟙 _ := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  simp only [rationalFunctionsMul, map_one]
  let M : (Spec X.functionField).Modules :=
    SheafOfModules.unit (Spec X.functionField).ringCatSheaf
  let F := Scheme.Modules.pushforward (fromSpecFunctionField X)
  -- As above, this definitional change only exposes the pushforward and scalar-multiplication
  -- wrappers so their identity laws apply directly.
  change F.map (Scheme.Modules.globalSectionsSmul M 1) = 𝟙 _
  rw [Scheme.Modules.globalSectionsSmul_one]
  exact F.map_id M

/-- Multiplying by a unit `g` and then by `g⁻¹` is the identity on `𝒦_X`. -/
@[simp]
theorem rationalFunctionsMul_comp_inv (g : X.functionFieldˣ) :
    rationalFunctionsMul X (g : X.functionField) ≫
        rationalFunctionsMul X ((g⁻¹ : X.functionFieldˣ) : X.functionField) = 𝟙 _ := by
  rw [← rationalFunctionsMul_mul, g.inv_mul, rationalFunctionsMul_one]

/-- Multiplying by the inverse of a unit `g` and then by `g` is the identity on `𝒦_X`. -/
@[simp]
theorem rationalFunctionsMul_inv_comp (g : X.functionFieldˣ) :
    rationalFunctionsMul X ((g⁻¹ : X.functionFieldˣ) : X.functionField) ≫
        rationalFunctionsMul X (g : X.functionField) = 𝟙 _ := by
  rw [← rationalFunctionsMul_mul, g.mul_inv, rationalFunctionsMul_one]

end Mul

variable [IsIntegral X]

/-- The inclusion `𝒪_X ⟶ 𝒦_X` is injective on sections over every open subset: over a nonempty
one because the germ map to the function field of an integral scheme is injective, and over an
empty one because there are no nonzero functions there. -/
theorem toRationalFunctions_app_injective (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (toRationalFunctions X) U) := by
  rcases U.1.eq_empty_or_nonempty with h | h
  · have hU : U = ⊥ := SetLike.ext' h
    have hsub : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    exact fun a b _ => Subsingleton.elim (id a : Γ(X, U)) (id b : Γ(X, U))
  · have : Nonempty U := by simpa using h
    intro a b hab
    have key : X.germToFunctionField U (id a : Γ(X, U)) =
        X.germToFunctionField U (id b : Γ(X, U)) := by
      rw [← rationalFunctionsEquiv_toRationalFunctions_app,
        ← rationalFunctionsEquiv_toRationalFunctions_app]
      exact congrArg _ hab
    exact X.germToFunctionField_injective U key

/-- **A locally regular rational function is regular.** On an integral scheme, a rational function
lying in the local ring `𝒪_{X,y}` at every point `y` of a nonempty open subset `U` is the germ of a
section of `𝒪_X` over `U`: inside the function field, `Γ(X, U)` is the intersection of the local
rings at the points of `U`. -/
theorem exists_germToFunctionField_eq_of_forall_mem_range {U : X.Opens} [Nonempty U]
    {f : X.functionField}
    (hf : ∀ y ∈ U, f ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f := by
  -- The generic point lies in every nonempty open subset, so germs there see every overlap.
  have hgen : ∀ V : X.Opens, Nonempty V → genericPoint X ∈ V := fun V _ ↦ genericPoint_mem V
  -- Every point of `U` has a neighbourhood inside `U` on which `f` is regular.
  have key : ∀ y : U, ∃ V : X.Opens, ∃ _ : (y : X) ∈ V, ∃ hV : V ≤ U,
      ∃ s : Γ(X, V), X.presheaf.germ V (genericPoint X) (hgen V ⟨⟨(y : X), ‹_›⟩⟩) s = f := by
    intro y
    obtain ⟨g, hgf⟩ := hf y y.2
    obtain ⟨W, hyW, s, hs⟩ := X.presheaf.exists_germ_eq g
    have hmem : (y : X) ∈ (W ⊓ U : X.Opens) := ⟨hyW, y.2⟩
    have hWU : Nonempty (W ⊓ U : X.Opens) := ⟨⟨(y : X), hmem⟩⟩
    -- Only needed as an instance, so that `algebraMap_germ_eq_germToFunctionField` applies at `W`.
    have : Nonempty W := ⟨⟨(y : X), hyW⟩⟩
    refine ⟨W ⊓ U, hmem, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [X.presheaf.germ_res_apply (homOfLE (inf_le_left : W ⊓ U ≤ W)) (genericPoint X)
      (hgen _ hWU) s, ← hgf, ← hs]
    exact (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hyW s).symm
  choose V hyV hVU s hs using key
  -- The chosen local regular functions agree on overlaps, since they all have germ `f`.
  have hne : ∀ y : U, Nonempty (V y) := fun y ↦ ⟨⟨(y : X), hyV y⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro y z
    have hyz : Nonempty (V y ⊓ V z : X.Opens) :=
      ⟨⟨genericPoint X, hgen _ (hne y), hgen _ (hne z)⟩⟩
    refine X.germToFunctionField_injective (V y ⊓ V z) ?_
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s y),
      X.presheaf.germ_res_apply (Opens.infLERight (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s z)]
    exact (hs y).trans (hs z).symm
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩) s hcompat
  obtain ⟨y⟩ := ‹Nonempty U›
  refine ⟨a, ?_⟩
  -- `ha` is phrased through `X.sheaf`, whose underlying presheaf is `X.presheaf`; naming the
  -- restriction identity with its `X.presheaf` type keeps the rewrites below type-correct.
  have hres : X.presheaf.map (homOfLE (hVU y)).op a = s y := ha y
  rw [← hs y, ← hres,
    X.presheaf.germ_res_apply (homOfLE (hVU y)) (genericPoint X) (hgen _ (hne y)) a]

/-- The morphism `𝒪_X ⟶ 𝒦_X` of ring sheaves is injective on sections over every open
subset of an integral scheme. -/
theorem toRationalFunctionsRing_app_injective (U : X.Opens) :
    Function.Injective ((toRationalFunctionsRing X).hom.app (.op U)) := by
  intro r s hrs
  apply toRationalFunctions_app_injective U
  apply (rationalFunctionsSectionsEquiv X U).injective
  exact (toRationalFunctionsRing_app U r).trans
    (hrs.trans (toRationalFunctionsRing_app U s).symm)

instance : Mono (toRationalFunctionsRing X).hom := by
  have hU : ∀ U : (Opens X)ᵒᵖ, Mono ((toRationalFunctionsRing X).hom.app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (toRationalFunctionsRing_app_injective U.unop)
  exact NatTrans.mono_of_mono_app _

instance : Mono (toRationalFunctions X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ,
      Mono (((Scheme.Modules.toPresheaf X).map (toRationalFunctions X)).app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (toRationalFunctions_app_injective U.unop)
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map (NatTrans.mono_of_mono_app _)

end Scheme

end

end AlgebraicGeometry

end TauCeti
