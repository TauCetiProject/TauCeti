/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic

/-!
# Functoriality of the PBW Rees algebra

Every homomorphism `f : L →ₗ⁅R⁆ M` of Lie algebras over a commutative ring `R` induces an
enveloping-algebra homomorphism `TauCeti.UniversalEnvelopingAlgebra.map R f` that preserves PBW
filtration degree (`map_mem_pbwFiltration`). Coefficientwise application on `U(L)[X]` therefore
restricts to an `R[X]`-algebra homomorphism

`reesMap R f : reesAlgebra R L →ₐ[R[X]] reesAlgebra R M`

fixing the central parameter `reesParameter` and sending `reesGenerator R L x` to
`reesGenerator R M (f x)`. Because `reesParameter` and `Set.range (reesGenerator R L)` generate
`reesAlgebra R L` over `R` (`adjoin_reesParameter_union_range_reesGenerator`), and
`Set.range (reesGenerator R L)` alone generates it over `R[X]` (`adjoin_range_reesGenerator`),
homomorphisms out of `reesAlgebra R L` are determined by their values on these generators.

From these extensionality principles follow functoriality (`reesMap_id`, `reesMap_comp`), the
induced equivalence `reesMapEquiv` for a Lie isomorphism, and compatibility with scalar evaluation
`coeffSubalgebra.eval`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reesMap`: the `R[X]`-algebra homomorphism of PBW Rees
  algebras induced by a Lie algebra homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.reesMapEquiv`: the `R[X]`-algebra isomorphism induced by a
  Lie algebra equivalence.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reesMap_reesParameter`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_reesGenerator`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_id`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_comp`.
* `TauCeti.UniversalEnvelopingAlgebra.eval_comp_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.eval_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.evalOne_reesMap`: naturality of scalar evaluations.

## References

* J. Dixmier, *Enveloping Algebras*, §2.3, for filtered homomorphisms of enveloping algebras and
  their Rees algebras.
-/

public section

open Polynomial

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

section Functoriality

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

/-- The `R[X]`-algebra homomorphism of PBW Rees algebras induced by a Lie algebra homomorphism
`f : L →ₗ⁅R⁆ M`, acting coefficientwise via `TauCeti.UniversalEnvelopingAlgebra.map R f`. -/
noncomputable def reesMap (f : L →ₗ⁅R⁆ M) : reesAlgebra R L →ₐ[R[X]] reesAlgebra R M :=
  coeffSubalgebra.mapPolynomialAlgHom (pbwFiltration R L) (pbwFiltration R M) (map R f)
    (fun _ _ hb ↦ map_mem_pbwFiltration R f hb)
    (one_mem_pbwFiltration R L 1) (one_mem_pbwFiltration R M 1)

@[simp]
theorem coe_reesMap (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    (reesMap R f p : Polynomial (_root_.UniversalEnvelopingAlgebra R M)) =
      (p : Polynomial (_root_.UniversalEnvelopingAlgebra R L)).map (map R f) := by
  simp [reesMap]

/-- `reesMap R f` fixes the central parameter `reesParameter`. -/
@[simp]
theorem reesMap_reesParameter (f : L →ₗ⁅R⁆ M) :
    reesMap R f (reesParameter R L) = reesParameter R M := by
  simp [reesMap]

/-- `reesMap R f` maps `reesGenerator R L x` to `reesGenerator R M (f x)`. -/
@[simp]
theorem reesMap_reesGenerator (f : L →ₗ⁅R⁆ M) (x : L) :
    reesMap R f (reesGenerator R L x) = reesGenerator R M (f x) := by
  apply Subtype.ext
  simp

/-- `reesMap R` sends the identity Lie homomorphism to the identity `R[X]`-algebra homomorphism. -/
@[simp]
theorem reesMap_id :
    reesMap R (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R[X] (reesAlgebra R L) := by
  rw [reesMap, ← coeffSubalgebra.mapPolynomialAlgHom_id (pbwFiltration R L)
    (fun _ _ hb ↦ hb) (one_mem_pbwFiltration R L 1)]
  exact coeffSubalgebra.mapPolynomialAlgHom_congr (map_id R) _ _ _ _

/-- `reesMap R` preserves composition of Lie homomorphisms. -/
@[simp]
theorem reesMap_comp (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ N) :
    reesMap R (g.comp f) = (reesMap R g).comp (reesMap R f) := by
  rw [reesMap, reesMap, reesMap, coeffSubalgebra.mapPolynomialAlgHom_comp]
  exact coeffSubalgebra.mapPolynomialAlgHom_congr (map_comp R f g) _ _ _ _

/-- The `R[X]`-algebra equivalence of PBW Rees algebras induced by a Lie algebra equivalence. -/
noncomputable def reesMapEquiv (e : L ≃ₗ⁅R⁆ M) : reesAlgebra R L ≃ₐ[R[X]] reesAlgebra R M :=
  AlgEquiv.ofAlgHom (reesMap R e.toLieHom) (reesMap R e.symm.toLieHom)
    (by
      rw [← reesMap_comp]
      convert reesMap_id R (L := M)
      ext y
      exact e.apply_symm_apply y)
    (by
      rw [← reesMap_comp]
      convert reesMap_id R (L := L)
      ext x
      exact e.symm_apply_apply x)

@[simp]
theorem reesMapEquiv_apply (e : L ≃ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    reesMapEquiv R e p = reesMap R e.toLieHom p :=
  (rfl)

@[simp]
theorem reesMapEquiv_toAlgHom (e : L ≃ₗ⁅R⁆ M) :
    (reesMapEquiv R e : reesAlgebra R L →ₐ[R[X]] reesAlgebra R M) = reesMap R e.toLieHom :=
  (rfl)

@[simp]
theorem reesMapEquiv_symm (e : L ≃ₗ⁅R⁆ M) :
    (reesMapEquiv R e).symm = reesMapEquiv R e.symm :=
  (rfl)

@[simp]
theorem reesMapEquiv_refl :
    reesMapEquiv R (LieEquiv.refl : L ≃ₗ⁅R⁆ L) = AlgEquiv.refl :=
  AlgEquiv.ext fun p ↦ AlgHom.congr_fun (reesMap_id R) p

@[simp]
theorem reesMapEquiv_trans (e : L ≃ₗ⁅R⁆ M) (d : M ≃ₗ⁅R⁆ N) :
    (reesMapEquiv R e).trans (reesMapEquiv R d) = reesMapEquiv R (e.trans d) :=
  AlgEquiv.ext fun p ↦ (AlgHom.congr_fun (reesMap_comp R e.toLieHom d.toLieHom) p).symm

/-- Scalar evaluation at `r : R` commutes with `reesMap` and the induced enveloping-algebra map. -/
theorem eval_comp_reesMap (f : L →ₗ⁅R⁆ M) (r : R) :
    (coeffSubalgebra.eval (pbwFiltration R M) r).comp ((reesMap R f).restrictScalars R) =
      (map R f).comp (coeffSubalgebra.eval (pbwFiltration R L) r) :=
  AlgHom.ext fun p ↦ by simp [reesMap]

@[simp]
theorem eval_reesMap (f : L →ₗ⁅R⁆ M) (r : R) (p : reesAlgebra R L) :
    coeffSubalgebra.eval (pbwFiltration R M) r (reesMap R f p) =
      map R f (coeffSubalgebra.eval (pbwFiltration R L) r p) :=
  AlgHom.congr_fun (eval_comp_reesMap R f r) p

@[simp]
theorem evalOne_reesMap (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    coeffSubalgebra.evalOne (pbwFiltration R M) (reesMap R f p) =
      map R f (coeffSubalgebra.evalOne (pbwFiltration R L) p) := by
  simp [reesMap]

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
