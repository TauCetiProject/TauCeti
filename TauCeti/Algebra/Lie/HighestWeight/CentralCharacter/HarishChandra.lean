/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Triangular
-- Non-public: an element of `U(𝔟)` is congruent to its character value modulo the induced
-- relations, used only inside the proof of the evaluation formula.
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Character
-- Non-public: a field of characteristic zero is infinite, which the separation below needs.
import Mathlib.Algebra.CharZero.Infinite
-- Non-public: elements of `S(H)` are separated by their values at weights, used only to prove
-- that the projection is multiplicative on the centre.
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# The Harish-Chandra projection

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its root system, with
nilradicals `n⁻` and `n⁺`. The triangular decomposition
`TauCeti.UniversalEnvelopingAlgebra.triangularMulEquiv : U(n⁻) ⊗ U(H) ⊗ U(n⁺) ≃ U(L)` writes every
element of `U(L)` uniquely as a sum of ordered products `f h e`. Applying the augmentation `ε` to
the two outer factors gives the **Cartan projection**

`TauCeti.cartanProjection b : U(L) →ₗ[K] U(H)`,   `f h e ↦ ε(f) ε(e) h`.

It is linear, and not multiplicative on all of `U(L)`. Its value on a central element `z` computes
the central character of every weight: since `H` is abelian, `U(H)` is the symmetric algebra
`S(H)`, the algebra of polynomial functions on the weights `H*`, and

`χ_λ(z) = (cartanProjection b z)(λ)`

(`TauCeti.vermaCentralCharacter_eq_lift_cartanProjection`). The reason is the Verma module:
`M(λ)` is a free `U(n⁻)`-module on its generator `v_λ`, and `f h e · v_λ = ε(e) λ(h) f · v_λ`, so
reading off the coefficient of `v_λ` in `z · v_λ = χ_λ(z) v_λ` returns `ε(f) ε(e) λ(h)` summed over
the decomposition of `z`, which is the value of `cartanProjection b z` at `λ`.

Central characters are algebra homomorphisms, and a polynomial function over an infinite field is
determined by its values, so the evaluation formula shows that the Cartan projection is
multiplicative on the centre. This gives the **Harish-Chandra projection**

`TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)`,

the restriction of the Cartan projection to the centre, read in `S(H)`, with no `ρ`-shift. It is
the homomorphism whose image is identified, in the Harish-Chandra isomorphism, with the
polynomials invariant under the dot action of the Weyl group.

## Main definitions

* `TauCeti.cartanProjection`: the projection `U(L) →ₗ[K] U(H)` along the triangular decomposition.
* `TauCeti.hcProjection`: the Harish-Chandra projection `Z(U(L)) →ₐ[K] S(H)`.

## Main results

* `TauCeti.cartanProjection_mul_mul`: the projection of an ordered product `f h e` is
  `ε(f) ε(e) h`.
* `TauCeti.vermaCentralCharacter_eq_lift_cartanProjection`: the central character of a weight `λ`
  is evaluation at `λ` of the Cartan projection.
* `TauCeti.lift_hcProjection`: the same formula for `hcProjection`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. E. Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category `O`*, §1.7.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module
open scoped TensorProduct

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

local notation "U" => _root_.UniversalEnvelopingAlgebra K

variable (b : (IsKilling.rootSystem H).Base)

/-! ### The Cartan projection -/

/-- **The Cartan projection** `U(L) → U(H)`: write an element of `U(L)` through the triangular
decomposition `U(n⁻) ⊗ U(H) ⊗ U(n⁺) ≃ U(L)` and apply the augmentation to the two outer factors, so
that an ordered product `f h e` goes to `ε(f) ε(e) h` (`TauCeti.cartanProjection_mul_mul`). It is
linear but not multiplicative; on the centre of `U(L)` it is the Harish-Chandra projection
`TauCeti.hcProjection`. -/
noncomputable def cartanProjection : U L →ₗ[K] U H :=
  (TensorProduct.lid K (U H)).toLinearMap ∘ₗ
    TensorProduct.map (Coalgebra.counit (R := K))
      ((TensorProduct.rid K (U H)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := K)).lTensor (U H)) ∘ₗ
    (UniversalEnvelopingAlgebra.triangularMulEquiv H b).symm.toLinearMap

/-- **The Cartan projection of an ordered product** `f h e`, with `f` in `U(n⁻)`, `h` in `U(H)` and
`e` in `U(n⁺)`, is `ε(f) ε(e) h`. -/
@[simp]
theorem cartanProjection_mul_mul (f : U (negativeNilradical H b)) (h : U H)
    (e : U (positiveNilradical H b)) :
    cartanProjection b
        (UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f *
          UniversalEnvelopingAlgebra.map K H.incl h *
            UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl e) =
      (Coalgebra.counit (R := K) f * Coalgebra.counit (R := K) e) • h := by
  simp [cartanProjection, mul_smul, smul_comm (Coalgebra.counit (R := K) f)]

/-- **The Cartan projection restricts to the identity on `U(H)`.** -/
@[simp]
theorem cartanProjection_map_incl (h : U H) :
    cartanProjection b (UniversalEnvelopingAlgebra.map K H.incl h) = h := by
  simpa using cartanProjection_mul_mul b 1 h 1

/-! ### Evaluation at a weight -/

variable (lam : Dual K H)

/-- Evaluation of `U(H) = S(H)` at the weight `lam`: the algebra homomorphism `U(H) → K` sending
`ι x` to `lam x`. -/
private noncomputable def cartanEval : U H →ₐ[K] K :=
  (SymmetricAlgebra.lift lam).comp
    (UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm.toAlgHom

omit [CharZero K] [IsTriangularizable K H L] in
private theorem cartanEval_apply (h : U H) :
    cartanEval lam h =
      SymmetricAlgebra.lift lam ((UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm h) :=
  (rfl)

omit [CharZero K] [IsTriangularizable K H L] in
private theorem cartanEval_ι (x : H) :
    cartanEval lam (_root_.UniversalEnvelopingAlgebra.ι K x) = lam x := by
  rw [cartanEval_apply, UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_ι,
    SymmetricAlgebra.lift_ι_apply]

/-- The Borel character of weight `lam`, extended to `U(𝔟)`, restricts on `U(H)` to evaluation at
`lam`. -/
private theorem lift_borelCharacter_map_cartan (h : U H) :
    _root_.UniversalEnvelopingAlgebra.lift K (borelCharacter H b lam)
        (UniversalEnvelopingAlgebra.map K (LieSubalgebra.inclusion (le_borelSubalgebra H b)) h) =
      cartanEval lam h := by
  induction h using UniversalEnvelopingAlgebra.induction_ι with
  | ι x =>
    rw [UniversalEnvelopingAlgebra.map_ι, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
      cartanEval_ι, borelCharacter_apply_of_mem_cartan H b lam x.2]
    -- the element `⟨inclusion _ x, _⟩` of `H` is `x` itself, by eta for subtypes
    rfl
  | algebraMap r => simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  | add h h' hh hh' => rw [map_add, map_add, hh, hh', map_add]
  | mul h h' hh hh' => rw [map_mul, map_mul, hh, hh', map_mul]

/-- The Borel character of weight `lam`, extended to `U(𝔟)`, restricts on `U(n⁺)` to the
augmentation. -/
private theorem lift_borelCharacter_map_positiveNilradical (e : U (positiveNilradical H b)) :
    _root_.UniversalEnvelopingAlgebra.lift K (borelCharacter H b lam)
        (UniversalEnvelopingAlgebra.map K
          (LieSubalgebra.inclusion (positiveNilradical_le_borelSubalgebra H b)) e) =
      Coalgebra.counit (R := K) e := by
  induction e using UniversalEnvelopingAlgebra.induction_ι with
  | ι x =>
    rw [UniversalEnvelopingAlgebra.map_ι, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
      UniversalEnvelopingAlgebra.counit_ι]
    exact borelCharacter_apply_of_mem_positiveNilradical H b lam x.2
  | algebraMap r => simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      ← Bialgebra.counitAlgHom_apply, AlgHom.commutes]
  | add e e' he he' => rw [map_add, map_add, he, he', map_add]
  | mul e e' he he' =>
    rw [map_mul, map_mul, he, he', ← Bialgebra.counitAlgHom_apply, ← Bialgebra.counitAlgHom_apply,
      ← Bialgebra.counitAlgHom_apply, map_mul]

/-! ### The central character through the Cartan projection -/

/-- The coefficient of the generator `v_lam` in an element of the Verma module, read through the
freeness `U(n⁻) ≃ M(lam)` followed by the augmentation of `U(n⁻)`. -/
private noncomputable def vermaCoeff : VermaModule b lam →ₗ[K] K :=
  Coalgebra.counit (R := K) ∘ₗ (universalEnvelopingEquivVermaModule b lam).symm.toLinearMap

/-- An ordered product `f h e` acts on `v_lam` as `ε(e) lam(h) f`, so the coefficient of `v_lam`
in `f h e · v_lam` is `ε(f) ε(e) lam(h)`, the value of the Cartan projection at `lam`. -/
private theorem vermaCoeff_vermaMk_mul_mul (f : U (negativeNilradical H b)) (h : U H)
    (e : U (positiveNilradical H b)) :
    vermaCoeff b lam (vermaMk b lam
        (UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f *
          UniversalEnvelopingAlgebra.map K H.incl h *
            UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl e)) =
      cartanEval lam (cartanProjection b
        (UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f *
          UniversalEnvelopingAlgebra.map K H.incl h *
            UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl e)) := by
  -- the Borel factor `h e` lies in `U(𝔟)`, where it is congruent to its character value
  let r : U (borelSubalgebra H b) :=
    UniversalEnvelopingAlgebra.map K (LieSubalgebra.inclusion (le_borelSubalgebra H b)) h *
      UniversalEnvelopingAlgebra.map K
        (LieSubalgebra.inclusion (positiveNilradical_le_borelSubalgebra H b)) e
  have hr : UniversalEnvelopingAlgebra.map K (borelSubalgebra H b).incl r =
      UniversalEnvelopingAlgebra.map K H.incl h *
        UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl e := by
    rw [map_mul, ← AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_incl_comp_map_inclusion,
      ← AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_incl_comp_map_inclusion]
  have hχ : _root_.UniversalEnvelopingAlgebra.lift K (borelCharacter H b lam) r =
      cartanEval lam h * Coalgebra.counit (R := K) e := by
    rw [map_mul, lift_borelCharacter_map_cartan, lift_borelCharacter_map_positiveNilradical]
  have hmem :=
    _root_.UniversalEnvelopingAlgebra.map_sub_algebraMap_lift_mem_span_range_ι_sub_algebraMap
      (borelSubalgebra H b) (borelCharacter H b lam) r
  rw [← vermaIdeal_eq_span_range_ι_sub_algebraMap, ← vermaMk_eq_iff, hr, hχ] at hmem
  -- so `f h e · v_lam = (lam(h) ε(e)) f · v_lam`, which is the image of `f` under `U(n⁻) ≃ M(lam)`
  have hL : vermaMk b lam
      (UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f *
        UniversalEnvelopingAlgebra.map K H.incl h *
          UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl e) =
      (cartanEval lam h * Coalgebra.counit (R := K) e) •
        universalEnvelopingEquivVermaModule b lam f := by
    rw [mul_assoc, ← smul_vermaMk, hmem, smul_vermaMk, ← Algebra.commutes, ← smul_vermaMk,
      algebraMap_smul, universalEnvelopingEquivVermaModule_apply, smul_vermaGenerator]
  rw [hL, cartanProjection_mul_mul, map_smul, map_smul]
  simp only [vermaCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, smul_eq_mul]
  ring

/-- The coefficient of `v_lam` in `u · v_lam` is the value at `lam` of the Cartan projection of
`u`, for every `u` in `U(L)`: both sides are linear in `u`, and they agree on ordered products. -/
private theorem vermaCoeff_vermaMk (u : U L) :
    vermaCoeff b lam (vermaMk b lam u) = cartanEval lam (cartanProjection b u) := by
  obtain ⟨t, rfl⟩ := (UniversalEnvelopingAlgebra.triangularMulEquiv H b).surjective u
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, map_add, map_add, ht, ht', map_add]
  | tmul f t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, ht, ht', map_add]
    | tmul h e =>
      rw [UniversalEnvelopingAlgebra.triangularMulEquiv_tmul]
      exact vermaCoeff_vermaMk_mul_mul b lam f h e

/-- **The central character of a weight is evaluation of the Cartan projection at that weight**:
for a central `z` in `U(L)`, `χ_lam(z)` is the value at `lam` of `cartanProjection b z`, read as a
polynomial function on the weights through `U(H) ≃ S(H)`. -/
theorem vermaCentralCharacter_eq_lift_cartanProjection (z : Subalgebra.center K (U L)) :
    vermaCentralCharacter b lam z =
      SymmetricAlgebra.lift lam
        ((UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm
          (cartanProjection b (z : U L))) := by
  have hz :=
    (isHighestWeightVector_vermaGenerator b lam).representation_eq_vermaCentralCharacter_smul z
  rw [representation_vermaModule_apply, smul_vermaGenerator] at hz
  have hv : vermaCoeff b lam (vermaGenerator b lam) = 1 := by
    rw [vermaCoeff, LinearMap.comp_apply, ← universalEnvelopingEquivVermaModule_one,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Bialgebra.counit_one]
  have hcoeff := congrArg (vermaCoeff b lam) hz
  rw [vermaCoeff_vermaMk, map_smul, hv, smul_eq_mul, mul_one, cartanEval_apply] at hcoeff
  exact hcoeff.symm

/-! ### The Harish-Chandra projection -/

/-- The value at every weight of the Cartan projection of a product of central elements is the
product of the values. -/
private theorem lift_cartanProjection_mul (z w : Subalgebra.center K (U L)) (lam : Dual K H) :
    SymmetricAlgebra.lift lam ((UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm
        (cartanProjection b ((z * w : Subalgebra.center K (U L)) : U L))) =
      SymmetricAlgebra.lift lam ((UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm
        (cartanProjection b (z : U L) * cartanProjection b (w : U L))) := by
  rw [← vermaCentralCharacter_eq_lift_cartanProjection]
  simp only [map_mul]
  rw [vermaCentralCharacter_eq_lift_cartanProjection,
    vermaCentralCharacter_eq_lift_cartanProjection]

/-- **The Harish-Chandra projection** `Z(U(L)) →ₐ[K] S(H)`: the restriction to the centre of the
Cartan projection `TauCeti.cartanProjection`, read in the symmetric algebra through
`U(H) ≃ S(H)`, with no `ρ`-shift. It is multiplicative because its value at each weight `lam` is
the central character `χ_lam` (`TauCeti.lift_hcProjection`), and an element of `S(H)` is determined
by its values at all weights. -/
noncomputable def hcProjection : Subalgebra.center K (U L) →ₐ[K] SymmetricAlgebra K H where
  toFun z := (UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm (cartanProjection b z)
  map_one' := by
    rw [OneMemClass.coe_one, ← map_one (UniversalEnvelopingAlgebra.map K H.incl),
      cartanProjection_map_incl, map_one]
  map_mul' z w := by
    rw [← map_mul]
    exact SymmetricAlgebra.eq_of_forall_lift_apply_eq (lift_cartanProjection_mul b z w)
  map_zero' := by simp
  map_add' z w := by simp
  commutes' r := by
    rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul,
      ← map_one (UniversalEnvelopingAlgebra.map K H.incl), cartanProjection_map_incl, map_smul,
      map_one, Algebra.algebraMap_eq_smul_one]

/-- The Harish-Chandra projection of a central element is its Cartan projection, read in `S(H)`. -/
theorem hcProjection_apply (z : Subalgebra.center K (U L)) :
    hcProjection b z =
      (UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).symm (cartanProjection b (z : U L)) :=
  (rfl)

/-- **The central character of a weight is evaluation of the Harish-Chandra projection at that
weight**: `χ_lam(z) = (hcProjection b z)(lam)`. -/
@[simp]
theorem lift_hcProjection (z : Subalgebra.center K (U L)) :
    SymmetricAlgebra.lift lam (hcProjection b z) = vermaCentralCharacter b lam z :=
  (vermaCentralCharacter_eq_lift_cartanProjection b lam z).symm

end TauCeti
