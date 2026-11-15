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

/-!
# Galois descent of function fields

Let `L / k` be a Galois extension, possibly of infinite degree, and let `F / L` be an algebraic
function field with exact constant field `L`. A discrete semilinear action
`ρ : Gal(L/k) →* (F ≃ₐ[k] F)` — one whose automorphisms restrict to the elements of `Gal(L/k)` on
the constants and under which every element of `F` has an open stabilizer in `Gal(L/k)` for the
Krull topology (automatic when `L / k` is finite) — is the descent datum of Weil's criterion for
the field of definition of a curve, applied to its function field. Its fixed field `F₀` is the
function field of the descended curve:

* `F` is the constant field extension `F₀ · L` of `F₀`
  (`TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top_of_isOpen`, and
  `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top` when `Aut_k(L)` is finite);
* `F₀ / k` is an algebraic function field
  (`TauCeti.GaloisDescent.isFunctionField_fixedField_of_isOpen` and
  `TauCeti.GaloisDescent.isFunctionField_fixedField`), with exact constant field `k` whenever `L`
  is exact in `F` (`TauCeti.GaloisDescent.isIntegrallyClosedIn_fixedField`);
* degrees over rational subfields descend: for every `x ∈ F₀`, `[F₀ : k(x)] = [F : L(x)]`
  (`TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple_of_isOpen` and
  `TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple`). For a Belyi function `t` fixed by
  the action, this says that `t` has the same degree as a function on `F₀` as on `F`. When `F` is
  an algebra over `L(t)` and `F₀` over `k(t)` compatibly, this is `[F₀ : k(t)] = [F : L(t)]`
  (`TauCeti.GaloisDescent.finrank_ratFunc_fixedField_of_isOpen` and
  `TauCeti.GaloisDescent.finrank_ratFunc_fixedField`).

Effectiveness is discrete Galois descent for `F` as an `L`-vector space with a semilinear action,
which needs no finiteness of `F` over `L`: `F` is spanned over `L` by `F₀`
(`TauCeti.GaloisDescent.span_fixedField_eq_top_of_isOpen`), and is the base change `L ⊗[k] F₀`
(`TauCeti.GaloisDescent.fixedFieldBaseChangeEquivOfIsOpen`).

## Main results

* `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top_of_isOpen` and
  `TauCeti.GaloisDescent.constantCompositum_fixedField_eq_top`: `F` is the constant-field
  compositum of `fixedField ρ.range` with `L`.
* `TauCeti.GaloisDescent.isFunctionField_fixedField_of_isOpen` and
  `TauCeti.GaloisDescent.isFunctionField_fixedField`: `fixedField ρ.range` is an algebraic
  function field over `k`.
* `TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple_of_isOpen` and
  `TauCeti.GaloisDescent.finrank_fixedField_over_adjoin_simple`: degrees over rational subfields
  `k(x)` descend.
* `TauCeti.GaloisDescent.finrank_ratFunc_fixedField_of_isOpen`,
  `TauCeti.GaloisDescent.finiteDimensional_ratFunc_fixedField_of_isOpen`,
  `TauCeti.GaloisDescent.finrank_ratFunc_fixedField`, and
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

omit [Algebra k L] in
private theorem constantCompositum_eq_top_of_span_eq_top {E : IntermediateField k F}
    (hspan : Submodule.span L (E : Set F) = ⊤) :
    constantCompositum E L F = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span L (E : Set F) := hspan ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact (constantCompositum E L F).algebraMap_mem ⟨x, hx⟩
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a _ _ hx =>
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_constantCompositum _ _ _ a) hx

/-- **The descended field generates.** For a semilinear action `ρ` of a finite automorphism group
of `L / k` on `F`, the field `F` is the compositum of the fixed field of `ρ` with `L`. -/
theorem constantCompositum_fixedField_eq_top [Finite (L ≃ₐ[k] L)]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    constantCompositum (fixedField ρ.range) L F = ⊤ :=
  constantCompositum_eq_top_of_span_eq_top (span_fixedField_eq_top hρ)

variable [IsScalarTower k L F]

/-- **The descended field of a discrete semilinear action generates.** For an arbitrary Galois
extension `L / k` and a semilinear action `ρ` of `Gal(L/k)` on `F` with open stabilizers, `F` is
the compositum of `fixedField ρ.range` with `L`. -/
theorem constantCompositum_fixedField_eq_top_of_isOpen [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x}) :
    constantCompositum (fixedField ρ.range) L F = ⊤ :=
  constantCompositum_eq_top_of_span_eq_top (span_fixedField_eq_top_of_isOpen hρ hopen)

/-- **The function-field property descends along a discrete semilinear action.** Let `L / k` be an
arbitrary Galois extension and let `F / L` be an algebraic function field. For a semilinear action
`ρ` of `Gal(L/k)` on `F` whose stabilizers are open, the fixed field `fixedField ρ.range` is an
algebraic function field over `k`. -/
theorem isFunctionField_fixedField_of_isOpen [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hF : IsFunctionField L F) :
    IsFunctionField k (fixedField ρ.range) := by
  set F₀ := fixedField ρ.range
  have hcomp : constantCompositum F₀ L F = ⊤ :=
    constantCompositum_fixedField_eq_top_of_isOpen hρ hopen
  have : Algebra.IsAlgebraic F₀ F := isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp
  let eL : L ≃ₐ[k] (IsScalarTower.toAlgHom k L F).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L F)
  have hfield : IsField (F₀ ⊗[k] (IsScalarTower.toAlgHom k L F).fieldRange) :=
    ((Algebra.TensorProduct.comm k F₀ _).trans <|
      (Algebra.TensorProduct.congr eL.symm AlgEquiv.refl).trans <|
        (fixedFieldBaseChangeEquivOfIsOpen hρ hopen).restrictScalars k).toMulEquiv.isField
      (Field.toIsField F)
  have hld : (IsScalarTower.toAlgHom k L F).fieldRange.LinearDisjoint F₀ :=
    (IntermediateField.LinearDisjoint.of_isField hfield).symm
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
  have hxL : Transcendental L (algebraMap F₀ F x) := hld.transcendental_algebraMap hx
  have : FiniteDimensional L⟮algebraMap F₀ F x⟯ F := hF.finiteDimensional_adjoin hxL
  have htower := trdeg_add_eq k k⟮x⟯ (A := F₀)
  rw [hx.isFunctionField_adjoin.trdeg_eq_one, htr] at htower
  have hzero : Algebra.trdeg k⟮x⟯ F₀ = 0 := by
    rcases Cardinal.add_eq_left_iff.mp htower with h | h
    · exact absurd ((le_max_left _ _).trans h) Cardinal.one_lt_aleph0.not_ge
    · exact h
  have : Algebra.IsAlgebraic k⟮x⟯ F₀ := trdeg_eq_zero_iff.mp hzero
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F₀
  let b' := constantExtensionBasisOfLinearDisjoint hld hcomp k⟮x⟯ b
  have hadj : IntermediateField.adjoin L (Set.range (algebraMap k⟮x⟯ F)) =
      L⟮algebraMap F₀ F x⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right]
  have : FiniteDimensional (IntermediateField.adjoin L (Set.range (algebraMap k⟮x⟯ F))) F := by
    rwa [hadj]
  have : Finite (Module.Basis.ofVectorSpaceIndex k⟮x⟯ F₀) := Module.Finite.finite_basis b'
  have : FiniteDimensional k⟮x⟯ F₀ := Module.Finite.of_basis b
  exact .of_finiteDimensional_adjoin hx

/-- **The function-field property descends along a finite Galois extension.** -/
theorem isFunctionField_fixedField [FiniteDimensional k L] [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) (hF : IsFunctionField L F) :
    IsFunctionField k (fixedField ρ.range) :=
  isFunctionField_fixedField_of_isOpen hρ (fun _ ↦ isOpen_discrete _) hF

/-- **Degrees descend along discrete semilinear actions.** If `L` is the exact constant field of
`F`, then for an arbitrary Galois extension `L / k`, a semilinear action `ρ` of `Gal(L/k)` on `F`
with open stabilizers, and an element `x` of its fixed field `F₀`, the degree of `F₀` over `k(x)`
is the degree of `F` over `L(x)`. -/
theorem finrank_fixedField_over_adjoin_simple_of_isOpen [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hL : IsIntegrallyClosedIn L F) (x : fixedField ρ.range) :
    Module.finrank k⟮x⟯ (fixedField ρ.range) = Module.finrank L⟮(x : F)⟯ F :=
  (finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top
    (isIntegrallyClosedIn_fixedField hρ hL)
    (constantCompositum_fixedField_eq_top_of_isOpen hρ hopen) x).symm

/-- **Degrees descend.** If `L` is the exact constant field of `F`, then for a semilinear action
`ρ` of `Gal(L/k)` on `F` over a finite Galois extension `L / k` and an element `x` of its fixed
field `F₀`, the degree of `F₀` over `k(x)` is the degree of `F` over `L(x)`. -/
theorem finrank_fixedField_over_adjoin_simple [FiniteDimensional k L] [IsGalois k L]
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hL : IsIntegrallyClosedIn L F) (x : fixedField ρ.range) :
    Module.finrank k⟮x⟯ (fixedField ρ.range) = Module.finrank L⟮(x : F)⟯ F :=
  finrank_fixedField_over_adjoin_simple_of_isOpen hρ (fun _ ↦ isOpen_discrete _) hL x

section RatFunc

variable [Algebra (RatFunc L) F] [IsScalarTower L (RatFunc L) F] [IsGalois k L]
  {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)} [Algebra (RatFunc k) (fixedField ρ.range)]
  [IsScalarTower k (RatFunc k) (fixedField ρ.range)]

/-- **The degree of a Belyi map descends along discrete semilinear actions.** Let `ρ` be a
semilinear action of `Gal(L/k)` with open stabilizers on a field `F` over `L(t)` with exact
constant field `L`. If the variable of `k(t)` acts on the fixed field `F₀` of `ρ` as the variable
of `L(t)` acts on `F`, then `[F₀ : k(t)] = [F : L(t)]`. -/
theorem finrank_ratFunc_fixedField_of_isOpen
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hL : IsIntegrallyClosedIn L F)
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    Module.finrank (RatFunc k) (fixedField ρ.range) = Module.finrank (RatFunc L) F :=
  (finrank_ratFunc_eq_of_constantCompositum_eq_top (isIntegrallyClosedIn_fixedField hρ hL)
    (constantCompositum_fixedField_eq_top_of_isOpen hρ hopen) hX).symm

/-- The fixed field of a discrete semilinear action of `Gal(L/k)` on a function field finite over
`L(t)`, with exact constant field `L`, is finite over `k(t)`, when the variable of `k(t)` acts on
it as the variable of `L(t)` acts on `F`. -/
theorem finiteDimensional_ratFunc_fixedField_of_isOpen [FiniteDimensional (RatFunc L) F]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[k] L | ρ σ x = x})
    (hL : IsIntegrallyClosedIn L F)
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    FiniteDimensional (RatFunc k) (fixedField ρ.range) :=
  Module.finite_of_finrank_pos
    (finrank_ratFunc_fixedField_of_isOpen hρ hopen hL hX ▸ Module.finrank_pos)

variable [FiniteDimensional k L]

/-- **The degree of a Belyi map descends.** Let `ρ` be a semilinear action of `Gal(L/k)` on a
field `F` over `L(t)` with exact constant field `L`, for a finite Galois extension `L / k`. If the
variable of `k(t)` acts on the fixed field `F₀` of `ρ` as the variable of `L(t)` acts on `F`, then
`[F₀ : k(t)] = [F : L(t)]`. -/
theorem finrank_ratFunc_fixedField (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hL : IsIntegrallyClosedIn L F)
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    Module.finrank (RatFunc k) (fixedField ρ.range) = Module.finrank (RatFunc L) F :=
  finrank_ratFunc_fixedField_of_isOpen hρ (fun _ ↦ isOpen_discrete _) hL hX

/-- The fixed field of a semilinear action of `Gal(L/k)` on a function field finite over `L(t)`,
with exact constant field `L` and `L / k` finite Galois, is finite over `k(t)`, when the variable
of `k(t)` acts on it as the variable of `L(t)` acts on `F`. -/
theorem finiteDimensional_ratFunc_fixedField [FiniteDimensional (RatFunc L) F]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hL : IsIntegrallyClosedIn L F)
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc k) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    FiniteDimensional (RatFunc k) (fixedField ρ.range) :=
  finiteDimensional_ratFunc_fixedField_of_isOpen hρ (fun _ ↦ isOpen_discrete _) hL hX

end RatFunc

end GaloisDescent

end TauCeti
