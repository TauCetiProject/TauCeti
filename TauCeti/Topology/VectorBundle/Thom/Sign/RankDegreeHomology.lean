/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The twisted Thom isomorphism normalized by a generator

For a real vector bundle of rank `r` and a commutative coefficient ring `R`,
`TauCeti.thomPairTwistedHomologyFinrankIsoOfGenerator` identifies the rank-degree homology of its
Thom pair with coefficients in the orientation system with `H₀(B; R)`. It sends the twisted fibre
class normalized by a generator of `Hᵣ(F, F ∖ {0}; R)` to the class of its base point.

The isomorphism uses `TauCeti.thomPairTwistedHomologyFinrankIso` over an arbitrary base. In
coordinates given by the point class, changing the generator multiplies the fibre classes by a
unit of `R`, so the corresponding identification of homology is rescaled by the inverse unit.
-/

public noncomputable section

open Bundle CategoryTheory Module AlgebraicTopology Set

universe w

namespace TauCeti

variable {B F : Type w} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {R : Type w}

section Ring

variable [Ring R]
  (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
    (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R))

/-- Coordinates of a model-fibre class in the basis given by the point class. -/
private abbrev fiberClassCoordinate : R :=
  (asIso (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl)).inv γ

variable (E) in
/-- The orientation-twisted fibre class over `b`, normalized by a model orientation `ω` and a
model-fibre class `γ`. -/
def thomPairTwistedFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  fiberClassCoordinate γ • thomPairSignFiberClass F E R hι ω b

/-- Reversing the orientation of the model fibre negates the twisted fibre class. -/
@[simp]
theorem thomPairTwistedFiberClass_neg (b : B) :
    thomPairTwistedFiberClass E hι (-ω) γ b = -thomPairTwistedFiberClass E hι ω γ b := by
  simp only [thomPairTwistedFiberClass, thomPairSignFiberClass_neg, smul_neg]

/-- A linear trivialization takes the defining class on the fibre to `γ`. The fibre inclusion
uses the orientation which the trivialization reads as `ω` to identify its coefficients with `R`. -/
theorem thomPairTwistedFiberClass_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) :
    thomPairTwistedFiberClass E hι ω γ b =
      thomPairSignFiberMap F E R hι b ((e.mapOrientation ι hb).symm ω) (finrank ℝ F)
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F) γ) := by
  rw [thomPairTwistedFiberClass, thomPairSignFiberClass_eq_thomPairSignFiberMap hι ω b
    ((e.mapOrientation ι hb).symm ω), orientedFiberGenerator_of_mapOrientation_eq ω hι e hb
    (Equiv.apply_symm_apply _ ω), ← map_smul, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
  rw [fiberClassCoordinate, asIso_inv, IsIso.inv_hom_id_apply]

end Ring

variable [CommRing R]
  (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
    (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R))

private theorem isUnit_fiberClassCoordinate (hγ : Submodule.span R {γ} = ⊤) :
    IsUnit (fiberClassCoordinate γ) := by
  let e := (asIso (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl)).symm.toLinearEquiv
  exact e.span_singleton_eq_top_iff_isUnit.1 hγ

/-- The rank-degree twisted Thom isomorphism for an arbitrary base, normalized by a generator
`γ` of the model fibre's relative homology. -/
def thomPairTwistedHomologyFinrankIsoOfGenerator (hγ : Submodule.span R {γ} = ⊤) :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj (TopCat.of B) :=
  thomPairTwistedHomologyFinrankIso F E R hι ω ≪≫
    (LinearEquiv.smulOfUnit (isUnit_fiberClassCoordinate γ hγ).unit).toModuleIso.symm

/-- The inverse normalized Thom isomorphism takes a point class to its twisted fibre class. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIsoOfGenerator_inv_singularHomology₀Section
    (hγ : Submodule.span R {γ} = ⊤) (b : B) :
    (thomPairTwistedHomologyFinrankIsoOfGenerator hι ω γ hγ).inv
        (singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1) =
      thomPairTwistedFiberClass E hι ω γ b := by
  rw [← thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass (E := E) hι ω b]
  change (thomPairTwistedHomologyFinrankIso F E R hι ω).inv
    (((isUnit_fiberClassCoordinate γ hγ).unit : R) • _) = _
  rw [IsUnit.unit_spec, map_smul, ← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply, thomPairTwistedFiberClass]

/-- The normalized Thom isomorphism takes the twisted fibre class to the class of the base point. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIsoOfGenerator_hom_thomPairTwistedFiberClass
    (hγ : Submodule.span R {γ} = ⊤) (b : B) :
    (thomPairTwistedHomologyFinrankIsoOfGenerator hι ω γ hγ).hom
        (thomPairTwistedFiberClass E hι ω γ b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  rw [← thomPairTwistedHomologyFinrankIsoOfGenerator_inv_singularHomology₀Section hι ω γ hγ,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

end TauCeti
