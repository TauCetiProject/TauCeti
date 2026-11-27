/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.Galois.SemilinearDescent
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Galois descent of function fields

Let `L / k` be a Galois extension, possibly of infinite degree, and let `F / L` be an algebraic
function field. A discrete semilinear action `ρ : Gal(L/k) →* (F ≃ₐ[k] F)` — one whose
automorphisms restrict to the elements of `Gal(L/k)` on the constants and under which every element
of `F` has an open stabilizer in `Gal(L/k)` for the Krull topology (automatic when `L / k` is
finite) — is the descent datum of Weil's criterion for the field of definition of a curve, applied
to its function field. Its fixed field `F₀` is the function field of the descended curve:

* `F` is the constant field extension `F₀ · L` of `F₀`
  (`TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top_of_isOpen`, and
  `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top` when `Aut_k(L)` is finite);
* `F₀ / k` is an algebraic function field (`TauCeti.GaloisDescent.isFunctionField_fixedField`), with
  exact constant field `k` whenever `L` is exact in `F`
  (`TauCeti.GaloisDescent.isIntegrallyClosedIn_fixedField`);
* degrees over rational subfields descend without assuming exactness of constants: for every
  `x ∈ F₀`, `[F₀ : k(x)] = [F : L(x)]`
  (`TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple`). For a Belyi function `t` fixed by
  the action, this says that `t` has the same degree as a function on `F₀` as on `F`. When `F` is
  an algebra over `L(t)` and `F₀` over `k(t)` compatibly, this is `[F₀ : k(t)] = [F : L(t)]`
  (`TauCeti.GaloisDescent.finrank_ratFunc_fixedField`).

Effectiveness is discrete Galois descent for `F` as an `L`-vector space with a semilinear action,
which needs no finiteness of `F` over `L`: `F` is spanned over `L` by `F₀`
(`TauCeti.GaloisDescent.span_fixedField_eq_top_of_isOpen`), and is the base change `L ⊗[k] F₀`
(`TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv`).

## Main results

* `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top_of_isOpen` and
  `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top`: `F` is the constant-field
  compositum of `fixedField ρ.range` with `L`.
* `TauCeti.GaloisDescent.isFunctionField_fixedField`: `fixedField ρ.range` is an algebraic function
  field over `k`.
* `TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple`: degrees over rational subfields
  `k(x)` descend.
* `TauCeti.GaloisDescent.finrank_ratFunc_fixedField` and
  `TauCeti.GaloisDescent.finiteDimensional_ratFunc_fixedField`: degree and finiteness over `k(t)`
  descend.

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
open scoped TensorProduct

namespace TauCeti

variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra k F] [Algebra L F]

namespace GaloisDescent

private theorem setRange_algebraMap (E : IntermediateField k F) :
    Set.range (algebraMap E F) = (E : Set F) :=
  E.toSubalgebra.setRange_algebraMap

/-- **The descended field generates.** For a semilinear action `ρ` of a finite automorphism group
of `L / k` on `F`, the field `F` is the compositum of the fixed field of `ρ` with `L`. -/
theorem constantCompositum_fixedField_eq_top [Finite (L ≃ₐ[k] L)]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    constantCompositum (fixedField ρ.range) L F = ⊤ := by
  apply constantCompositum_eq_top_of_span_eq_top
  rw [setRange_algebraMap]
  exact span_fixedField_eq_top hρ

variable [IsScalarTower k L F]

/-- **The descended field of a discrete semilinear action generates.** For an arbitrary Galois
extension `L / k` and a semilinear action `ρ` of `Gal(L/k)` on `F` with open stabilizers, `F` is
the compositum of `fixedField ρ.range` with `L`. -/
theorem constantCompositum_fixedField_eq_top_of_isOpen [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x}) :
    constantCompositum (fixedField ρ.range) L F = ⊤ := by
  apply constantCompositum_eq_top_of_span_eq_top
  rw [setRange_algebraMap]
  exact span_fixedField_eq_top_of_isOpen hρ hopen

private theorem linearDisjoint_fixedField [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x}) :
    (IsScalarTower.toAlgHom k L F).fieldRange.LinearDisjoint (fixedField ρ.range) := by
  let eL : L ≃ₐ[k] (IsScalarTower.toAlgHom k L F).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L F)
  have hfield : IsField (fixedField ρ.range ⊗[k] (IsScalarTower.toAlgHom k L F).fieldRange) :=
    ((Algebra.TensorProduct.comm k (fixedField ρ.range) _).trans <|
      (Algebra.TensorProduct.congr eL.symm AlgEquiv.refl).trans <|
        (fixedFieldBaseChangeEquiv hρ hopen).restrictScalars k).toMulEquiv.isField
      (Field.toIsField F)
  exact (IntermediateField.LinearDisjoint.of_isField hfield).symm

private theorem finiteDimensional_fixedField_adjoin_simple [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (x : fixedField ρ.range) [FiniteDimensional L⟮(x : F)⟯ F] :
    FiniteDimensional k⟮x⟯ (fixedField ρ.range) := by
  let F₀ := fixedField ρ.range
  have : IsScalarTower k⟮x⟯ F₀ F := .of_algebraMap_eq fun _ ↦ rfl
  have hsub : (constantCompositum k⟮x⟯ L F).toSubfield = L⟮(x : F)⟯.toSubfield :=
    constantCompositum_adjoin_simple_toSubfield (k := k) (K := L) (F := F₀) (F' := F) x
  have : FiniteDimensional (constantCompositum k⟮x⟯ L F) F :=
    Module.Finite.of_equiv_equiv (RingEquiv.subfieldCongr hsub.symm) (RingEquiv.refl F) rfl
  have : Algebra.IsAlgebraic k⟮x⟯ (constantCompositum k⟮x⟯ L F) :=
    isAlgebraic_constantCompositum (k := k) (k' := L) (F := k⟮x⟯) (F' := F)
  have : Algebra.IsAlgebraic k⟮x⟯ F :=
    Algebra.IsAlgebraic.trans k⟮x⟯ (constantCompositum k⟮x⟯ L F) F
  have : Algebra.IsAlgebraic k⟮x⟯ F₀ := Algebra.IsAlgebraic.tower_bot k⟮x⟯ F₀ F
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F₀
  let b' := constantExtensionBasisOfLinearDisjoint (linearDisjoint_fixedField hρ hopen)
    (constantCompositum_fixedField_eq_top_of_isOpen hρ hopen) k⟮x⟯ b
  have hadj : IntermediateField.adjoin L (Set.range (algebraMap k⟮x⟯ F)) = L⟮(x : F)⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right,
      IntermediateField.algebraMap_apply]
  have : FiniteDimensional (IntermediateField.adjoin L (Set.range (algebraMap k⟮x⟯ F))) F := by
    rwa [hadj]
  have : Finite (Module.Basis.ofVectorSpaceIndex k⟮x⟯ F₀) := Module.Finite.finite_basis b'
  exact Module.Finite.of_basis b

/-- **The function-field property descends along a discrete semilinear action.** Let `L / k` be an
arbitrary Galois extension and let `F / L` be an algebraic function field. For a semilinear action
`ρ` of `Gal(L/k)` on `F` whose stabilizers are open, the fixed field `fixedField ρ.range` is an
algebraic function field over `k`. -/
theorem isFunctionField_fixedField [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hF : IsFunctionField L F) :
    IsFunctionField k (fixedField ρ.range) := by
  set F₀ := fixedField ρ.range
  have : Algebra.IsAlgebraic F₀ F := isAlgebraic_of_constantCompositum_eq_top (k := k)
    (constantCompositum_fixedField_eq_top_of_isOpen hρ hopen)
  have htrF : Algebra.trdeg k F = 1 := by
    rw [← trdeg_eq_of_isAlgebraic_base (S := L)]
    exact hF.trdeg_eq_one
  have htr : Algebra.trdeg k F₀ = 1 := by
    have h := lift_trdeg_add_eq k F₀ F
    rw [trdeg_eq_zero_iff.mpr (inferInstance : Algebra.IsAlgebraic F₀ F), Cardinal.lift_zero,
      add_zero, htrF, Cardinal.lift_one] at h
    simpa using h
  have : Algebra.Transcendental k F₀ := trdeg_ne_zero_iff.mp (htr ▸ one_ne_zero)
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := F₀)
  have : FiniteDimensional L⟮(x : F)⟯ F :=
    hF.finiteDimensional_adjoin ((linearDisjoint_fixedField hρ hopen).transcendental_algebraMap hx)
  have : FiniteDimensional k⟮x⟯ F₀ := finiteDimensional_fixedField_adjoin_simple hρ hopen x
  exact .of_finiteDimensional_adjoin hx

/-- **Degrees descend along discrete semilinear actions.** For an arbitrary Galois extension
`L / k`, a semilinear action `ρ` of `Gal(L/k)` on `F` with open stabilizers, and an element `x` of
its fixed field `F₀`, the degree of `F₀` over `k(x)` is the degree of `F` over `L(x)`. -/
theorem finrank_fixedField_over_adjoin_simple [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x}) (x : fixedField ρ.range) :
    Module.finrank k⟮x⟯ (fixedField ρ.range) = Module.finrank L⟮(x : F)⟯ F := by
  have hcomp := constantCompositum_fixedField_eq_top_of_isOpen hρ hopen
  by_cases hfin : FiniteDimensional L⟮(x : F)⟯ F
  · have := finiteDimensional_fixedField_adjoin_simple hρ hopen x
    exact (finrank_over_adjoin_simple_eq_of_linearDisjoint
      (linearDisjoint_fixedField hρ hopen) hcomp x).symm
  · have hfin₀ : ¬ FiniteDimensional k⟮x⟯ (fixedField ρ.range) := fun h ↦
      hfin (finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) hcomp x)
    rw [Module.finrank_of_not_finite hfin₀, Module.finrank_of_not_finite hfin]

section RatFunc

variable [Algebra (RatFunc L) F] [IsScalarTower L (RatFunc L) F] [IsGalois k L]
  {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)} [Algebra (RatFunc k) (fixedField ρ.range)]
  [IsScalarTower k (RatFunc k) (fixedField ρ.range)]

/-- **The degree of a Belyi map descends along discrete semilinear actions.** Let `ρ` be a
semilinear action of `Gal(L/k)` with open stabilizers on a field `F` over `L(t)`. If the variable
of `k(t)` acts on the fixed field `F₀` of `ρ` as the variable of `L(t)` acts on `F`, then
`[F₀ : k(t)] = [F : L(t)]`. -/
theorem finrank_ratFunc_fixedField
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    Module.finrank (RatFunc k) (fixedField ρ.range) = Module.finrank (RatFunc L) F := by
  rw [← finrank_adjoin_algebraMap_X (k := k), ← finrank_adjoin_algebraMap_X (k := L), ← hX]
  exact finrank_fixedField_over_adjoin_simple hρ hopen
    (algebraMap (RatFunc k) (fixedField ρ.range) RatFunc.X)

/-- The fixed field of a discrete semilinear action of `Gal(L/k)` on a field `F` finite over
`L(t)` is finite over `k(t)`, when the variable of `k(t)` acts on it as the variable of `L(t)` acts
on `F`. -/
theorem finiteDimensional_ratFunc_fixedField [FiniteDimensional (RatFunc L) F]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    FiniteDimensional (RatFunc k) (fixedField ρ.range) :=
  Module.finite_of_finrank_pos
    (finrank_ratFunc_fixedField hρ hopen hX ▸ Module.finrank_pos)

end RatFunc

end GaloisDescent

end TauCeti
