/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.OneFiber
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.ZeroFiber

/-!
# Functoriality of the PBW Rees algebra and its fibres

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
induced equivalence `reesMapEquiv` for a Lie isomorphism, compatibility with scalar evaluation
`coeffSubalgebra.eval` and `coeffSubalgebra.evalOne`, compatibility with the `t = 1` quotient and
tensor-product fibres (`quotientReesParameterSubOneEquiv`, `reesOneFiberEquiv`), and—when `L` and
`M` are free `R`-modules—compatibility with `reesSpecializationZero` and `reesZeroFiberEquiv`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reesMap`: the `R[X]`-algebra homomorphism of PBW Rees
  algebras induced by a Lie algebra homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.reesMapEquiv`: the `R[X]`-algebra isomorphism induced by a
  Lie algebra equivalence.
* `TauCeti.UniversalEnvelopingAlgebra.quotientReesParameterSubOneMap` and
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberMap`: the induced `R`-algebra maps on the
  quotients modulo `t - 1` and modulo `t`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reesMap_reesParameter`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_reesGenerator`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_id`,
  `TauCeti.UniversalEnvelopingAlgebra.reesMap_comp`.
* `TauCeti.UniversalEnvelopingAlgebra.eval_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.evalOne_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.quotientReesParameterSubOneEquiv_map`,
  `TauCeti.UniversalEnvelopingAlgebra.reesOneFiberEquiv_map`: naturality of scalar evaluations and
  of the `t = 1` fibre comparisons.
* `TauCeti.UniversalEnvelopingAlgebra.reesSpecializationZero_comp_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.reesSpecializationZero_reesMap`,
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberEquiv_map`: naturality of the zero-parameter
  specialization and zero-fibre equivalence.

## References

* J. Dixmier, *Enveloping Algebras*, §2.3, for filtered homomorphisms of enveloping algebras and
  their Rees algebras.
-/

public section

open Polynomial
open scoped TensorProduct

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
          exact map_mem_pbwFiltration R f (mem_coeffSubalgebra_iff.mp p.2 n)
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

/-! ### Naturality of scalar evaluations and the `t = 1` fibre -/

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

theorem evalOne_comp_reesMap (f : L →ₗ⁅R⁆ M) :
    (coeffSubalgebra.evalOne (pbwFiltration R M)).comp ((reesMap R f).restrictScalars R) =
      (map R f).comp (coeffSubalgebra.evalOne (pbwFiltration R L)) := by
  rw [coeffSubalgebra.evalOne_eq_eval, coeffSubalgebra.evalOne_eq_eval]
  exact eval_comp_reesMap R f 1

@[simp]
theorem evalOne_reesMap (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    coeffSubalgebra.evalOne (pbwFiltration R M) (reesMap R f p) =
      map R f (coeffSubalgebra.evalOne (pbwFiltration R L) p) := by
  rw [coeffSubalgebra.evalOne_eq_eval, coeffSubalgebra.evalOne_eq_eval]
  exact eval_reesMap R f 1 p

/-- The `R`-algebra map on `t = 1` Rees quotients induced by a Lie algebra homomorphism. -/
noncomputable def quotientReesParameterSubOneMap (f : L →ₗ⁅R⁆ M) :
    (reesAlgebra R L ⧸ Ideal.span {reesParameter R L - 1}) →ₐ[R]
      (reesAlgebra R M ⧸ Ideal.span {reesParameter R M - 1}) :=
  Ideal.quotientMapₐ (Ideal.span {reesParameter R M - 1}) ((reesMap R f).restrictScalars R) <|
    Ideal.span_le.mpr <| by
      rintro p (rfl : p = reesParameter R L - 1)
      simp

@[simp]
theorem quotientReesParameterSubOneMap_mk (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    quotientReesParameterSubOneMap R f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (reesMap R f p) :=
  (rfl)

@[simp]
theorem quotientReesParameterSubOneEquiv_map (f : L →ₗ⁅R⁆ M)
    (q : reesAlgebra R L ⧸ Ideal.span {reesParameter R L - 1}) :
    quotientReesParameterSubOneEquiv R M (quotientReesParameterSubOneMap R f q) =
      map R f (quotientReesParameterSubOneEquiv R L q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- Naturality of the tensor-product `t = 1` fibre `reesOneFiberEquiv`. -/
@[simp]
theorem reesOneFiberEquiv_map (f : L →ₗ⁅R⁆ M) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    ∀ z : R ⊗[R[X]] reesAlgebra R L,
      reesOneFiberEquiv R M (Algebra.TensorProduct.map (AlgHom.id R R) (reesMap R f) z) =
        map R f (reesOneFiberEquiv R L z) := by
  let := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
  intro z
  exact TensorProduct.inductionOn z
    (fun r p ↦ by simp [reesOneFiberEquiv_tmul])
    (fun x y hx hy ↦ by simp [hx, hy])

/-! ### Naturality of the zero fibre -/

/-- The `R`-algebra map on `t = 0` Rees quotients induced by a Lie algebra homomorphism, requiring
no freeness hypothesis on `L` or `M`. -/
noncomputable def reesZeroFiberMap (f : L →ₗ⁅R⁆ M) :
    (reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) →ₐ[R]
      (reesAlgebra R M ⧸ Ideal.span {reesParameter R M}) :=
  Ideal.quotientMapₐ (Ideal.span {reesParameter R M}) ((reesMap R f).restrictScalars R) <|
    Ideal.span_le.mpr <| by
      rintro p (rfl : p = reesParameter R L)
      simp

@[simp]
theorem reesZeroFiberMap_mk (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    reesZeroFiberMap R f (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (reesMap R f p) :=
  (rfl)

/-- **Naturality of `reesSpecializationZero`.** For Lie algebras free as `R`-modules, zero
specialization intertwines `reesMap R f` with `SymmetricAlgebra.map R f.toLinearMap`. -/
theorem reesSpecializationZero_comp_reesMap [Module.Free R L] [Module.Free R M] (f : L →ₗ⁅R⁆ M) :
    (reesSpecializationZero R M).comp ((reesMap R f).restrictScalars R) =
      (SymmetricAlgebra.map R f.toLinearMap).comp (reesSpecializationZero R L) :=
  reesAlgebra_algHom_ext (by simp) (fun x ↦ by simp)

@[simp]
theorem reesSpecializationZero_reesMap [Module.Free R L] [Module.Free R M] (f : L →ₗ⁅R⁆ M)
    (p : reesAlgebra R L) :
    reesSpecializationZero R M (reesMap R f p) =
      SymmetricAlgebra.map R f.toLinearMap (reesSpecializationZero R L p) :=
  AlgHom.congr_fun (reesSpecializationZero_comp_reesMap R f) p

/-- **Naturality of `reesZeroFiberEquiv`.** -/
@[simp]
theorem reesZeroFiberEquiv_map [Module.Free R L] [Module.Free R M] (f : L →ₗ⁅R⁆ M)
    (q : reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) :
    reesZeroFiberEquiv R M (reesZeroFiberMap R f q) =
      SymmetricAlgebra.map R f.toLinearMap (reesZeroFiberEquiv R L q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
