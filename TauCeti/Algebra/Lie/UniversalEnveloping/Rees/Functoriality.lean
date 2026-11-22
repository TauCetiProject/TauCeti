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
  `TauCeti.UniversalEnvelopingAlgebra.eval_reesMap`: naturality of scalar evaluations.

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
  let φ : reesAlgebra R L →ₐ[R] reesAlgebra R M :=
    AlgHom.codRestrict ((Polynomial.mapAlgHom (map R f)).comp (reesAlgebra R L).val)
      (reesAlgebra R M) fun p ↦
        mem_coeffSubalgebra_iff.mpr fun n ↦ by
          rw [AlgHom.comp_apply, Subalgebra.coe_val, Polynomial.coe_mapAlgHom, Polynomial.coeff_map]
          exact map_mem_pbwFiltration R f (mem_coeffSubalgebra_iff.mp p.property n)
  AlgHom.ofLinearMap
    { toAddHom := φ.toAddHom
      map_smul' := fun q p ↦ Subtype.ext <| by
        simp [φ, Algebra.smul_def, coeffSubalgebra.coe_algebraMap, Polynomial.map_map] }
    (map_one φ) (map_mul φ)

@[simp]
theorem coe_reesMap (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    (reesMap R f p : Polynomial (_root_.UniversalEnvelopingAlgebra R M)) =
      (p : Polynomial (_root_.UniversalEnvelopingAlgebra R L)).map (map R f) :=
  (rfl)

@[simp]
theorem reesMap_reesParameter (f : L →ₗ⁅R⁆ M) :
    reesMap R f (reesParameter R L) = reesParameter R M := by
  apply Subtype.ext
  simp

@[simp]
theorem reesMap_reesGenerator (f : L →ₗ⁅R⁆ M) (x : L) :
    reesMap R f (reesGenerator R L x) = reesGenerator R M (f x) := by
  apply Subtype.ext
  simp

@[simp]
theorem reesMap_id :
    reesMap R (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R[X] (reesAlgebra R L) := by
  ext x
  simp

@[simp]
theorem reesMap_comp (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ N) :
    reesMap R (g.comp f) = (reesMap R g).comp (reesMap R f) := by
  ext x
  simp

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
  reesAlgebra_algHom_ext (by simp) (fun x ↦ by simp)

@[simp]
theorem eval_reesMap (f : L →ₗ⁅R⁆ M) (r : R) (p : reesAlgebra R L) :
    coeffSubalgebra.eval (pbwFiltration R M) r (reesMap R f p) =
      map R f (coeffSubalgebra.eval (pbwFiltration R L) r p) :=
  AlgHom.congr_fun (eval_comp_reesMap R f r) p

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
