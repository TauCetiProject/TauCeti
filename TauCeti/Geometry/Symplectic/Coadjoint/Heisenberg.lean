/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Nil.Adjoint
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

/-!
# The coadjoint orbits of the real Heisenberg group

`Nil` is the real Heisenberg group, an analytic Lie group whose Lie algebra `𝔫` has coordinates
`(a, b, c)` and the single bracket relation `⁅X, Y⁆ = Z` for the coordinate vectors
(`TauCeti.Geometry.Manifold.Riemannian.Nil.Adjoint`); in the statements below, `Z` is the vector
`groupLieAlgebraEquiv.symm (heisenbergZ ℝ) = (0, 0, 1)` of `𝔫`. Write the coordinates of a
functional `ν ∈ 𝔫*` as `(p, q, r) = (ν X, ν Y, ν Z)`. The coadjoint action of `g = (x, y, z)` is

`Ad*_g (p, q, r) = (p + r y, q - r x, r)`,

the action of the matrix Heisenberg group `TauCeti.HeisenbergGroup.coadjointRepresentation`
transported along the Lie algebra isomorphism `TauCeti.Nil.groupLieAlgebraEquiv`. This file
computes the coadjoint orbits of the Lie group `Nil`, their stabilizers and their
Kirillov–Kostant–Souriau forms `Module.Dual.coadjointOrbitForm`.

* The coordinate `r = ν Z` is invariant
  (`TauCeti.Nil.coadjointRepresentation_apply_groupLieAlgebraEquiv_symm_heisenbergZ`).
* If `r ≠ 0`, the orbit of `ν` is the whole plane `{μ | μ Z = r}`
  (`TauCeti.Nil.range_coadjointRepresentation_apply_of_ne_zero`), and the stabilizer of `ν` is the
  centre of `Nil`, its `z`-axis (`TauCeti.Nil.stabilizer_coadjointRepresentation_of_ne_zero`). So
  the orbit manifold `Nil ⧸ Nil_ν` is two-dimensional
  (`TauCeti.Nil.finrank_quotientModelSpace_of_ne_zero`).
* If `r = 0`, the orbit of `ν` is the point `{ν}`
  (`TauCeti.Nil.range_coadjointRepresentation_apply_of_eq_zero`), fixed by all of `Nil`
  (`TauCeti.Nil.stabilizer_coadjointRepresentation_of_eq_zero`).

So the coadjoint orbits are even-dimensional, whereas the adjoint orbits of noncentral elements
are the affine lines `a X + b Y + ℝ Z` (`TauCeti.Nil.range_adjointRepresentation_apply_of_ne_zero`).

The KKS form pairs the generators of `ξ = (a, b, c)` and `η = (a', b', c')` to

`ω_ν(ξ_O, η_O) = r (a b' - b a')`

at every point of the orbit (`TauCeti.Nil.eval₂_coadjointOrbitForm_fundamentalVectorField`). On
the algebraic tangent model of the orbit this is the form `dp ∧ dq / r` of the plane `r = const`
(`Module.Dual.apply_heisenbergZ_mul_kksForm`).

## Main results

* `TauCeti.Nil.mem_range_coadjointRepresentation_apply_iff`: the coadjoint orbits of `Nil` are
  those of the matrix Heisenberg group.
* `TauCeti.Nil.range_coadjointRepresentation_apply_of_ne_zero`,
  `TauCeti.Nil.range_coadjointRepresentation_apply_of_eq_zero`: the coadjoint orbits.
* `TauCeti.Nil.stabilizer_coadjointRepresentation_of_ne_zero`,
  `TauCeti.Nil.stabilizer_coadjointRepresentation_of_eq_zero`: the coadjoint stabilizers.
* `TauCeti.Nil.finrank_quotientModelSpace_of_ne_zero`: the nontrivial orbits are
  two-dimensional.
* `TauCeti.Nil.eval₂_coadjointOrbitForm_fundamentalVectorField`: the KKS form on generators.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Chapter 2 (the coadjoint orbits of the Heisenberg group).
-/

public section

open Manifold Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Nil

local notation "R3" => ℝ × ℝ × ℝ

/-- **The coordinate `r = ν Z` is invariant under the coadjoint action**, since `Z` is central. -/
theorem coadjointRepresentation_apply_groupLieAlgebraEquiv_symm_heisenbergZ (g : Nil)
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) =
      ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) := by
  simpa using LinearMap.congr_fun (dualMap_groupLieAlgebraEquiv_coadjointRepresentation g ν)
    (heisenbergZ ℝ)

/-- **The coadjoint orbits of `Nil` are those of the matrix Heisenberg group**: `μ` lies in the
coadjoint orbit of `ν` exactly when their restrictions along `groupLieAlgebraEquiv.symm` lie in
one orbit of the matrix coadjoint action. -/
theorem mem_range_coadjointRepresentation_apply_iff {ν μ : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)} :
    μ ∈ Set.range (fun g : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν) ↔
      groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap μ ∈ Set.range
        (fun a ↦ HeisenbergGroup.coadjointRepresentation ℝ a
          (groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap ν)) := by
  simp only [Set.mem_range, toHeisenberg.surjective.exists,
    ← dualMap_groupLieAlgebraEquiv_coadjointRepresentation, EmbeddingLike.apply_eq_iff_eq]

/-- **The coadjoint orbit through a functional `ν` with `r = ν Z ≠ 0` is the plane
`{μ | μ Z = r}`.** -/
theorem range_coadjointRepresentation_apply_of_ne_zero {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    Set.range (fun g : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν) =
      {μ | μ (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) =
        ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ))} := by
  ext μ
  rw [mem_range_coadjointRepresentation_apply_iff,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_isUnit (by simpa using hν.isUnit)]
  simp

/-- **The coadjoint orbit through a functional vanishing on the centre is a point.** -/
theorem range_coadjointRepresentation_apply_of_eq_zero {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) = 0) :
    Set.range (fun g : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν) = {ν} := by
  ext μ
  rw [mem_range_coadjointRepresentation_apply_iff,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_eq_zero (by simpa using hν)]
  simp

/-- **The coadjoint stabilizer of a functional `ν` with `ν Z ≠ 0` is the centre of `Nil`**, its
`z`-axis `{(0, 0, z)}`. -/
theorem stabilizer_coadjointRepresentation_of_ne_zero {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν = Subgroup.center Nil := by
  have hstab := HeisenbergGroup.stabilizer_coadjointRepresentation_of_mem_nonZeroDivisors
    (ν := groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap ν)
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hν))
  ext g
  rw [Representation.mem_stabilizer, mem_center_iff,
    ← groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap.injective.eq_iff,
    dualMap_groupLieAlgebraEquiv_coadjointRepresentation, ← Representation.mem_stabilizer, hstab,
    HeisenbergGroup.mem_zAxis_iff, x_toHeisenberg, y_toHeisenberg]

/-- **The coadjoint orbits of `Nil` through functionals with `ν Z ≠ 0` are two-dimensional**: the
orbit manifold `Nil ⧸ Nil_ν` is modelled on a two-dimensional space. -/
theorem finrank_quotientModelSpace_of_ne_zero {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    finrank ℝ (Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
      ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) = 2 := by
  -- The orbit model is the algebraic tangent model `𝔫 ⧸ 𝔫_ν`, and `groupLieAlgebraEquiv`
  -- identifies it with that of the matrix Heisenberg Lie algebra.
  rw [Module.Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator,
    (Module.Dual.quotientLieAnnihilatorEquiv (groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap ν)
      (f := groupLieAlgebraEquiv.toLieHom) groupLieAlgebraEquiv.surjective
      (by ext ξ; simp)).finrank_eq]
  exact finrank_quotient_lieAnnihilator_heisenberg (by simpa using hν)

/-- **A functional vanishing on the centre is fixed by all of `Nil`.** -/
theorem stabilizer_coadjointRepresentation_of_eq_zero {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) = 0) :
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ Representation.mem_stabilizer.mpr ?_
  have h := range_coadjointRepresentation_apply_of_eq_zero hν
  exact Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self g)

/-- **The Kirillov–Kostant–Souriau form of a coadjoint orbit of `Nil`.** At every point of the
orbit of `ν`, the KKS form pairs the generators of `ξ = (a, b, c)` and `η = (a', b', c')` to
`r (a b' - b a')`, where `r = ν Z`. -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (x : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)
    (ξ η : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x
        (fundamentalVectorField 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) ξ x)
        (fundamentalVectorField 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) η x) =
      ν (groupLieAlgebraEquiv.symm (heisenbergZ ℝ)) *
        ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).2.1 -
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).1) := by
  -- The bracket `⁅ξ, η⁆` is `(a b' - b a') Z`, and every point of the orbit takes the value `r`
  -- on the central vector `Z`.
  have hlie : ⁅ξ, η⁆ = ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).2.1 -
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).1) •
      groupLieAlgebraEquiv.symm (heisenbergZ ℝ) := by
    apply (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).injective
    rw [map_smul, tangentSpaceCastModel_lie, tangentSpaceCastModel_groupLieAlgebraEquiv_symm]
    simp
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField, Representation.orbitMap_mk,
    hlie, map_smul, coadjointRepresentation_apply_groupLieAlgebraEquiv_symm_heisenbergZ,
    smul_eq_mul, mul_comm]

end TauCeti.Nil
