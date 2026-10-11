/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Local coefficients from covering spaces

A covering transports its fibre along paths by monodromy. Applying the free-module construction
to this set-valued local system gives a module-valued local coefficient system whose fibres are
the finitely supported formal sums of sheets. This is the permutation local system used to
describe singular transfer for finite covers, including covers that are not regular.

The construction does not require finite fibres: finiteness is needed only by later transfer
formulas, not to define the local system. The basis-vector formula records the sheet-level
transport explicitly, so a later chain-level transfer can use the same path-lifting data.

The local-system viewpoint follows Hatcher, *Algebraic Topology*, Section 3.H; the covering
monodromy is Mathlib's `IsCoveringMap.monodromyFunctor`.
-/

public section

open CategoryTheory

universe u v w

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- The permutation local coefficient system of a covering map, with fibre the free `R`-module
on the sheet over each point. Its transport maps are the linear extensions of path lifting. -/
@[expose] noncomputable def permutationLocalSystem (hp : IsCoveringMap p) (R : Type v)
    [Ring R] : TauCeti.LocalCoefficientSystem R B where
  obj x := ModuleCat.of R ((p ⁻¹' {x.as}) →₀ R)
  map {x y} γ := ModuleCat.ofHom <|
    Finsupp.lmapDomain R R (hp.monodromy γ)
  map_id x := by
    have hmon : hp.monodromy (𝟙 x) = id := by
      -- The groupoid identity is represented by the reflexive path class.
      rw [show (𝟙 x : x ⟶ x) = Path.Homotopic.Quotient.refl x.as from rfl,
        hp.monodromy_refl]
    ext f e
    simp [hmon]
  map_comp γ δ := by
    have hmon : hp.monodromy (γ ≫ δ) = hp.monodromy δ ∘ hp.monodromy γ :=
      funext fun e => hp.monodromy_trans_apply γ δ e
    ext f e
    simp [hmon]

/-- The fibre of the permutation local coefficient system over `x` is the free module on the
sheet over `x`. -/
theorem permutationLocalSystem_obj (hp : IsCoveringMap p) (R : Type v) [Ring R]
    (x : FundamentalGroupoid B) :
    (hp.permutationLocalSystem R).obj x =
      ModuleCat.of R ((p ⁻¹' {x.as}) →₀ R) :=
  rfl

/-- Evaluating transport in the permutation local system is the linear extension of monodromy. -/
@[simp]
theorem permutationLocalSystem_map_apply (hp : IsCoveringMap p) (R : Type v) [Ring R]
    {x y : FundamentalGroupoid B} (γ : x ⟶ y) (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystem R).map γ).hom f =
      Finsupp.lmapDomain R R (hp.monodromy γ) f :=
  rfl

/-- Transport sends each basis vector to the basis vector of the lifted endpoint. -/
theorem permutationLocalSystem_map_single (hp : IsCoveringMap p) (R : Type v) [Ring R]
    {x y : FundamentalGroupoid B} (γ : x ⟶ y) (e : p ⁻¹' {x.as}) (r : R) :
    ((hp.permutationLocalSystem R).map γ).hom (Finsupp.single e r) =
      Finsupp.single (hp.monodromy γ e) r := by
  rw [permutationLocalSystem_map_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

end IsCoveringMap
