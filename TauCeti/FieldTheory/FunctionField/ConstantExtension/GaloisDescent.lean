/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.Galois.SemilinearDescent
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree

/-!
# Galois descent of function fields

Let `L / k` be a finite Galois extension and let `F / L` be an algebraic function field with exact
constant field `L`. A semilinear action `ρ : Gal(L/k) →* (F ≃ₐ[k] F)`, one whose automorphisms
restrict to the elements of `Gal(L/k)` on the constants, is the descent datum of Weil's criterion
for the field of definition of a curve, applied to its function field. Its fixed field `F₀` is the
function field of the descended curve:

* `F` is the constant field extension `F₀ · L` of `F₀`
  (`TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top`);
* `F₀ / k` has exact constant field `k` (`TauCeti.GaloisDescent.isIntegrallyClosedIn_fixedField`).
  It is an algebraic function field over `k` because `F` is one and the image of `ρ` is finite
  (`TauCeti.IsFunctionField.of_finiteDimensional` and `TauCeti.IsFunctionField.fixedField`);
* degrees over rational subfields descend: for every `x ∈ F₀`, `[F₀ : k(x)] = [F : L(x)]`
  (`TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple`). For a Belyi function `t`
  fixed by the action, this says that `t` has the same degree as a function on `F₀` as on `F`.

Effectiveness is Galois descent for `F` as an `L`-vector space with a semilinear action, which
needs no finiteness of `F` over `L`: `F` is spanned over `L` by `F₀`
(`TauCeti.GaloisDescent.span_fixedField_eq_top`), and is the base change `L ⊗[k] F₀`
(`TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv`).

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.9) Theorem.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), Théorème 3 (critère de Weil).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 3.6.
-/

public section

open IntermediateField

namespace TauCeti

variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra k F] [Algebra L F]

namespace GaloisDescent

/-- **The descended field generates.** For a semilinear action `ρ` of the automorphism group of
`L / k` on `F`, the field `F` is the compositum of the fixed field of `ρ` with `L`. -/
theorem constantCompositum_fixedField_eq_top [Finite (L ≃ₐ[k] L)]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    constantCompositum (fixedField ρ.range) L F = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span L (fixedField ρ.range : Set F) := by
    rw [span_fixedField_eq_top hρ]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact (constantCompositum (fixedField ρ.range) L F).algebraMap_mem ⟨x, hx⟩
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a _ _ hx =>
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_constantCompositum _ _ _ a) hx

variable [IsScalarTower k L F]

/-- **Degrees descend.** If `L` is the exact constant field of `F`, then for a semilinear action
`ρ` of `Gal(L/k)` on `F` and an element `x` of its fixed field `F₀`, the degree of `F₀` over
`k(x)` is the degree of `F` over `L(x)`. -/
theorem finrank_fixedField_over_adjoin_simple [FiniteDimensional k L] [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hL : IsIntegrallyClosedIn L F) (x : fixedField ρ.range) :
    Module.finrank k⟮x⟯ (fixedField ρ.range) = Module.finrank L⟮(x : F)⟯ F :=
  (finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top
    (isIntegrallyClosedIn_fixedField hρ hL) (constantCompositum_fixedField_eq_top hρ) x).symm

end GaloisDescent

end TauCeti
