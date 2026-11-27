/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Restriction
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The map of fundamental groups along `Spec 𝔽_(p²) → Spec 𝔽_p`

For `f : Spec 𝔽_(p²) → Spec 𝔽_p` and the geometric point given by an algebraic closure `Ω` of
`𝔽_(p²)`, the induced map `π₁(Spec 𝔽_(p²), x) → π₁(Spec 𝔽_p, x ≫ f)` is injective, its image
has index two, and so it is not surjective. Here `𝔽_(p²)` is `GaloisField p 2` and `Ω` is
`AlgebraicClosure (GaloisField p 2)`.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.FiniteEtaleScheme

namespace TauCeti.Examples.FiniteEtaleGaloisRestriction

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => AlgebraicClosure (GaloisField p 2)

instance instIsGaloisZModAlgebraicClosure : IsGalois (ZMod p) Ω := {}

/-- The map `π₁(Spec 𝔽_(p²)) → π₁(Spec 𝔽_p)` is injective. -/
theorem injective :
    Function.Injective (mapAutFiber
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (GaloisField p 2))))
      (Spec.algebraMap_comp_algebraMap (ZMod p) (GaloisField p 2) Ω)) :=
  mapAutFiber_spec_injective _ _ _

/-- The image of `π₁(Spec 𝔽_(p²)) → π₁(Spec 𝔽_p)` has index two. -/
theorem index_range :
    (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (GaloisField p 2))))
      (Spec.algebraMap_comp_algebraMap (ZMod p) (GaloisField p 2) Ω)).toMonoidHom.range.index
        = 2 := by
  rw [index_range_mapAutFiber_spec, GaloisField.finrank p two_ne_zero]

/-- The map `π₁(Spec 𝔽_(p²)) → π₁(Spec 𝔽_p)` is not surjective. -/
theorem not_surjective :
    ¬ Function.Surjective (mapAutFiber
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (GaloisField p 2))))
      (Spec.algebraMap_comp_algebraMap (ZMod p) (GaloisField p 2) Ω)) := by
  rw [mapAutFiber_spec_surjective_iff_finrank_eq_one, GaloisField.finrank p two_ne_zero]
  decide

end TauCeti.Examples.FiniteEtaleGaloisRestriction
