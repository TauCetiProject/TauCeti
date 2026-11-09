/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ResidueCocycle
public import TauCeti.Algebra.Lie.Extension.Basic

/-!
# Maps between residue central extensions

For an invariant symmetric bilinear form `Φ` on a Lie algebra `L` over a commutative ring `R`, the
residue central extension of the formal current algebra `L((t)) = R⸨X⸩ ⊗[R] L` is Mathlib's
`LieAlgebra.ofTwoCocycle` of the residue cocycle `TauCeti.CurrentAlgebra.twoCocycleOfBilinear`. As
an `R`-module it is `L((t)) × R`; write `K` for the central element `(0, 1)`
(`LieAlgebra.ofTwoCocycle.centralElement`, defined for the extension of any Lie algebra by a
2-cocycle with trivial coefficients in `R`), which is central and nonzero over a nontrivial ring,
and every element is a current plus a multiple of `K`
(`LieAlgebra.ofTwoCocycle.ofProd_eq_add_smul_centralElement`). This file constructs the two
basic maps between such extensions, both instances of the morphisms of central extensions
`LieAlgebra.ofTwoCocycle.map`.

* **Level rescaling.** If `Ψ = r • Φ`, then the map which is the identity on currents and sends
  `K` to `r • K` is a Lie algebra morphism from the extension of `Φ` to that of `Ψ`
  (`TauCeti.CurrentAlgebra.levelHom`). When `r` is a unit it is an isomorphism
  (`TauCeti.CurrentAlgebra.levelEquiv`). At `r = 0` it is a morphism to the split extension of
  the zero form which kills `K`, so it is not injective unless `R` is trivial.
* **Polynomial currents.** The extension of the polynomial loop algebra by Mathlib's residue
  cocycle `LieAlgebra.LoopAlgebra.twoCocycleOfBilinear` embeds in the extension of formal currents
  by the inclusion `TauCeti.CurrentAlgebra.ofLoop` on currents and the identity on the centre
  (`TauCeti.CurrentAlgebra.ofLoopExtension`), which sends the central element of the polynomial
  extension to `K` (`TauCeti.CurrentAlgebra.ofLoopExtension_centralElement`).

It also identifies the negative currents `t⁻¹ L[t⁻¹]`, the elements `(u, 0)` with `u` a
polynomial current of negative order, as a Lie subalgebra of the extension
(`TauCeti.CurrentAlgebra.negativeLieSubalgebra`): the residue cocycle vanishes on them. Over a
field the vacuum module is free of rank one over its enveloping algebra
(`TauCeti.CurrentAlgebra.vacuumPBWEquiv`).

The isomorphism `levelEquiv` for a unit `u` does not identify the representations on which the
central elements act by `1`: pulling back along it a module on which `K` acts by `1` gives one on
which `K` acts by `u`.

The forms use Mathlib's residue convention `Res(f dg) Φ(x, y)`; the affine convention with level
form `κ` is the case `Φ = -κ`, and `-(r • κ) = r • (-κ)`, so rescaling the level form is rescaling
`Φ`. No degree derivation is adjoined.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the affine central
  extension of a loop algebra and its normalisation by the level.
-/

public section

noncomputable section

open scoped LaurentSeries
open LieAlgebra LieModule.Cohomology
open LieAlgebra.ofTwoCocycle (centralElement)

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "C" => currentAlgebra R L
local notation "Z" => TrivialLieModule R C R

section Level

variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)

local notation "cΦ" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R L Ψ hΨ hΨs

/-- Rescaling the level of a residue central extension: if `Ψ = r • Φ`, the Lie algebra morphism
from the extension of `Φ` to that of `Ψ` which is the identity on currents and multiplies the
central coordinate by `r`, so that `K ↦ r • K`. -/
def levelHom {r : R} (h : Ψ = r • Φ) : ofTwoCocycle cΦ →ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.map cΦ LieHom.id (r • LinearMap.id) cΨ fun u v ↦ by
    subst h
    simp [twoCocycleOfBilinear_smul R L r Φ hΦ hΦs, smul_apply_apply]

/-- Level rescaling fixes the current coordinate and multiplies the central coordinate by `r`. -/
@[simp]
theorem levelHom_ofProd {r : R} (h : Ψ = r • Φ) (u : C) (z : Z) :
    levelHom hΦ hΦs hΨ hΨs h (ofProd cΦ (u, z)) = ofProd cΨ (u, r • z) := by
  simp [levelHom]

/-- The coordinates of the image under level rescaling. -/
@[simp]
theorem ofProd_symm_levelHom {r : R} (h : Ψ = r • Φ) (v : ofTwoCocycle cΦ) :
    (ofProd cΨ).symm (levelHom hΦ hΦs hΨ hΨs h v) =
      (((ofProd cΦ).symm v).1, r • ((ofProd cΦ).symm v).2) := by
  simp [levelHom]

/-- Level rescaling is the identity on the current coordinate. -/
theorem proj_levelHom {r : R} (h : Ψ = r • Φ) (v : ofTwoCocycle cΦ) :
    ofTwoCocycle.proj cΨ (levelHom hΦ hΦs hΨ hΨs h v) = ofTwoCocycle.proj cΦ v := by
  simp [levelHom]

/-- If `Ψ = u • Φ` for a unit `u`, the residue central extensions of `Φ` and `Ψ` are isomorphic
by the identity on currents and `K ↦ u • K`. -/
def levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) : ofTwoCocycle cΦ ≃ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.mapEquiv cΦ (LieEquiv.refl : C ≃ₗ⁅R⁆ C) (LinearEquiv.smulOfUnit u) cΨ fun v w ↦ by
    subst h
    simp [twoCocycleOfBilinear_smul R L (u : R) Φ hΦ hΦs, smul_apply_apply,
      LinearEquiv.smulOfUnit, Units.smul_def]

/-- The level isomorphism fixes the current coordinate and multiplies the central coordinate by
`u`. -/
@[simp]
theorem levelEquiv_ofProd {u : Rˣ} (h : Ψ = (u : R) • Φ) (v : C) (z : Z) :
    levelEquiv hΦ hΦs hΨ hΨs h (ofProd cΦ (v, z)) = ofProd cΨ (v, u • z) := by
  simp [levelEquiv, LinearEquiv.smulOfUnit]

/-- The coordinates of the image under the level isomorphism. -/
@[simp]
theorem ofProd_symm_levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) (v : ofTwoCocycle cΦ) :
    (ofProd cΨ).symm (levelEquiv hΦ hΦs hΨ hΨs h v) =
      (((ofProd cΦ).symm v).1, u • ((ofProd cΦ).symm v).2) := by
  simp [levelEquiv, LinearEquiv.smulOfUnit]

/-- The inverse level isomorphism multiplies the central coordinate by `u⁻¹`. -/
@[simp]
theorem levelEquiv_symm_ofProd {u : Rˣ} (h : Ψ = (u : R) • Φ) (v : C) (z : Z) :
    (levelEquiv hΦ hΦs hΨ hΨs h).symm (ofProd cΨ (v, z)) = ofProd cΦ (v, u⁻¹ • z) := by
  simp [levelEquiv, LinearEquiv.smulOfUnit]

/-- The level isomorphism is the level rescaling morphism of the unit. -/
@[simp]
theorem toLieHom_levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (levelEquiv hΦ hΦs hΨ hΨs h).toLieHom = levelHom hΦ hΦs hΨ hΨs h :=
  LieHom.ext fun v ↦ by
    obtain ⟨⟨w, z⟩, rfl⟩ := (ofProd cΦ).surjective v
    simp [Units.smul_def]

end Level

section Loop

variable [HasUniqueDiv R] (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
  (hΦs : Φ.IsSymm)

local notation "P" => LieAlgebra.loopAlgebra R ℤ L
local notation "cP" => LieAlgebra.LoopAlgebra.twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs

/-- The embedding of the residue central extension of the polynomial loop algebra, built from
Mathlib's residue cocycle, into that of formal currents: `ofLoop` on currents and the identity on
the centre `R`. -/
def ofLoopExtension : ofTwoCocycle cP →ₗ⁅R⁆ ofTwoCocycle c :=
  ofTwoCocycle.map cP (ofLoop R L)
    ((TrivialLieModule.equiv R C R).symm.toLinearMap ∘ₗ
      (TrivialLieModule.equiv R P R).toLinearMap) c fun u v ↦ by
    simp

/-- The polynomial embedding is `ofLoop` on currents and the identity on the centre. -/
@[simp]
theorem ofLoopExtension_ofProd (u : P) (z : TrivialLieModule R P R) :
    ofLoopExtension Φ hΦ hΦs (ofProd cP (u, z)) =
      ofProd c (ofLoop R L u,
        (TrivialLieModule.equiv R C R).symm (TrivialLieModule.equiv R P R z)) := by
  simp [ofLoopExtension]

/-- The coordinates of the image under the polynomial embedding. -/
@[simp]
theorem ofProd_symm_ofLoopExtension (v : ofTwoCocycle cP) :
    (ofProd c).symm (ofLoopExtension Φ hΦ hΦs v) =
      (ofLoop R L ((ofProd cP).symm v).1, (TrivialLieModule.equiv R C R).symm
        (TrivialLieModule.equiv R P R ((ofProd cP).symm v).2)) := by
  simp [ofLoopExtension]

/-- The polynomial embedding lies over `ofLoop`. -/
theorem proj_ofLoopExtension (v : ofTwoCocycle cP) :
    ofTwoCocycle.proj c (ofLoopExtension Φ hΦ hΦs v) = ofLoop R L (ofTwoCocycle.proj cP v) := by
  simp [ofLoopExtension]

/-- The polynomial embedding sends the central element `K` of the polynomial extension to the
central element `K` of the formal one. -/
@[simp]
theorem ofLoopExtension_centralElement :
    ofLoopExtension Φ hΦ hΦs (centralElement cP) = centralElement c := by
  apply (ofProd c).symm.injective
  simp

/-- The residue central extension of polynomial currents embeds in that of formal currents. -/
theorem ofLoopExtension_injective : Function.Injective (ofLoopExtension Φ hΦ hΦs) :=
  ofTwoCocycle.map_injective _ _ _ _ _ (ofLoop_injective R L)
    ((TrivialLieModule.equiv R C R).symm.injective.comp (TrivialLieModule.equiv R P R).injective)

end Loop

section Negative

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs

/-- **The negative currents** `t⁻¹ L[t⁻¹]` as a Lie subalgebra of the residue central extension:
the elements `(u, 0)` with `u` a polynomial current of negative order. They form a Lie subalgebra
since the bracket of negative currents is negative and the residue cocycle vanishes on them. -/
def negativeLieSubalgebra : LieSubalgebra R (ofTwoCocycle c) where
  toSubmodule :=
    (truncSubmodule R L 0).map ((ofProdLinearEquiv c).toLinearMap ∘ₗ LinearMap.inl R C Z)
  lie_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    refine ⟨⁅u, v⁆, truncSubmodule_mono R L (by omega) (lie_mem_truncSubmodule R L hu hv), ?_⟩
    simp [bracket_ofTwoCocycle, coe_ofProdLinearEquiv, twoCochainOfBilinear_apply_apply,
      residuePairing_eq_zero_of_mem_truncSubmodule R L Φ hu hv (by omega)]

variable {Φ hΦ hΦs}

/-- An element of the residue extension is a negative current exactly when its current
coordinate is a polynomial current of negative order and its central coordinate vanishes. -/
theorem mem_negativeLieSubalgebra {x : ofTwoCocycle c} :
    x ∈ negativeLieSubalgebra Φ hΦ hΦs ↔
      ((ofProd c).symm x).1 ∈ truncSubmodule R L 0 ∧ ((ofProd c).symm x).2 = 0 := by
  rw [← LieSubalgebra.mem_toSubmodule]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [coe_ofProdLinearEquiv] using hu
  · rintro ⟨hu, hz⟩
    refine ⟨_, hu, ?_⟩
    rw [← (ofProd c).apply_symm_apply x]
    simp [coe_ofProdLinearEquiv, ← hz]

/-- The element `(u, z)` is a negative current exactly when `u` is a polynomial current of
negative order and `z = 0`. -/
@[simp]
theorem ofProd_mem_negativeLieSubalgebra {u : C} {z : Z} :
    ofProd c (u, z) ∈ negativeLieSubalgebra Φ hΦ hΦs ↔ u ∈ truncSubmodule R L 0 ∧ z = 0 := by
  rw [mem_negativeLieSubalgebra, Equiv.symm_apply_apply]

end Negative

end TauCeti.CurrentAlgebra
