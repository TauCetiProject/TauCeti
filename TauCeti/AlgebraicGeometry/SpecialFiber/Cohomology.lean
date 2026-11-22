/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.SpecialFiber.Components
public import TauCeti.AlgebraicGeometry.SpecialFiber.Subscheme
import TauCeti.AlgebraicGeometry.Curves.Cohomology.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.SpecialFiber.Dimension

/-!
# Cohomology finiteness for components of the special fibre

Let `R` be a local ring with residue field `k` and let `toBase : X ⟶ Spec R` be a proper scheme
over `R` whose points all have codimension at most two. The closure of any codimension-one point
`η` of `X` in the special fibre, with its reduced structure, is a proper scheme over `k` of Krull
dimension at most one
(`AlgebraicGeometry.Scheme.Hom.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton`). Its
structure-sheaf cohomology is therefore finite-dimensional over `k` in every degree
(`AlgebraicGeometry.Scheme.Hom.finiteDimensional_cohomology_trivial_subscheme_closure_singleton`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.finiteDimensional_cohomology_trivial_subscheme_closure_singleton`:
  `Hⁿ(C, 𝒪_C)` is finite-dimensional over `ResidueField R` in every degree `n` for each reduced
  closure `C` of a codimension-one point in the special fibre.
-/

public section

noncomputable section

open AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a scheme `X` proper over a local ring `R` with all points of codimension at most two, the
structure-sheaf cohomology of the reduced closure of any codimension-one point in the special fibre
is finite-dimensional over `ResidueField R` in every degree. -/
theorem finiteDimensional_cohomology_trivial_subscheme_closure_singleton
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsProper toBase]
    (hX : ∀ x : X, coheight x ≤ 2) {η : CodimensionOnePoint X} (hη' : toBase η = closedPoint R)
    (n : ℕ) :
    letI := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hη')
    FiniteDimensional (ResidueField R) (Cohomology (InvertibleSheaf.trivial
      (vanishingIdeal ⟨closure {(η : X)}, isClosed_closure⟩).subscheme).obj n) := by
  let hI := toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hη'
  let := subschemeOverResidueField hI
  have := isProper_subschemeOverResidueField hI
  have hdim := (relativeDimensionLE_iff_of_field _).mp
    (toBase.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton hX
      (fun h ↦ one_ne_zero (η.property.symm.trans (coheight_eq_zero.mpr h))) hη')
  let Y := (vanishingIdeal ⟨closure {(η : X)}, isClosed_closure⟩).subscheme
  let L := InvertibleSheaf.trivial Y
  have : TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) L.obj := L.property
  let F : _root_.SheafOfModules Y.ringCatSheaf := L.obj
  have : L.obj.IsFiniteType := inferInstanceAs F.IsFiniteType
  exact Scheme.Modules.finiteDimensional_cohomology_of_topologicalKrullDim_le_one
    (ResidueField R) hdim L.obj n

end AlgebraicGeometry.Scheme.Hom

end
