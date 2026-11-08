/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SemiDirect.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.CentralQuotient
public import TauCeti.Algebra.OreExtension.Derivation

/-!
# Enveloping algebras of Lie algebras with an adjoined derivation

Let `D` be a derivation of a Lie algebra `L` over a commutative ring `R`, and let
`L ⋊⁅D.lineHom⁆ R` be the semidirect sum adjoining `D` to `L` as a new element
`d = inr 1`, with `⁅d, x⁆ = D x`. Fix `z : L` and `c : R`, and write
`U = U(L) / (ι z - c)` (`TauCeti.UniversalEnvelopingAlgebra.CentralQuotient`). Suppose that `δ` is a
derivation of `U` extending `D`, that is `δ (ι x) = ι (D x)` for all `x : L`.

Then the enveloping algebra `U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)` of the larger Lie algebra is the
differential operator ring `U[X; δ]`, the Ore extension of `U` by `δ` with identity twist
(`TauCeti.UniversalEnvelopingAlgebra.CentralQuotient.semiDirectSumOreEquiv`). The isomorphism sends
the image of `x : L` to the constant `C (ι x)` and the adjoined element `d` to the variable `X`.

Consequently the algebra map `U → U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)` induced by the inclusion of
`L` is injective (`TauCeti.UniversalEnvelopingAlgebra.CentralQuotient.map_inl_injective`), with no
field or flatness assumption on `R`, and the larger algebra is a free left `U`-module on the powers
`dⁿ`: the isomorphism carries the left monomial basis `a Xⁿ` of the Ore extension to `a dⁿ`
(`TauCeti.UniversalEnvelopingAlgebra.CentralQuotient.semiDirectSumOreEquiv_symm_monomial`).

The main example is the extended affine algebra, which adjoins the degree derivation `t d/dt` to an
affine Kac--Moody algebra.

## References

* J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, Chapter 1, §1.2 and §1.7,
  for differential operator rings and for enveloping algebras of Lie algebras extended by a
  derivation.
* J. Dixmier, *Enveloping Algebras*, §2.2, for the universal property of enveloping algebras.
-/

public section

noncomputable section

namespace TauCeti.UniversalEnvelopingAlgebra.CentralQuotient

open LieAlgebra LieAlgebra.SemiDirectSum OreExtension

-- The ring of scalars is used as a one-dimensional abelian Lie algebra, and associative algebras
-- are Lie algebras under the commutator.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {z : L} {c : R}
  {D : LieDerivation R L L} {δ : derivationLieAlgebra R (CentralQuotient R z c)}

local notation "U" => CentralQuotient R z c
local notation "O" =>
  OreExtension (AlgHom.id R (CentralQuotient R z c)) (derivationLieAlgebra.toSigmaDerivation δ)
local notation "U'" => CentralQuotient R (inl D.lineHom z) c

/-- The Lie algebra morphism `(x, t) ↦ C (ι x) + t • X` from the semidirect sum to the
differential operator ring. -/
private def toOreLieHom (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) :
    (L ⋊⁅D.lineHom⁆ R) →ₗ⁅R⁆ O where
  toFun x := C (ι z c x.left) + x.right • X
  map_add' x y := by
    simp only [add_eq_mk, map_add, add_smul]
    abel
  map_smul' r x := by simp [smul_add, smul_smul]
  map_lie' {x y} := by
    -- Expand both commutators: the variable contributes `δ` through `X * C a - C a * X`.
    have hX (a : U) : (X : O) * C a = C a * X + C ((δ : Module.End R U) a) := by
      rw [← X_mul_C_sub_C_mul_X δ a, add_sub_cancel]
    simp only [lie_eq_mk, LieDerivation.lineHom_apply, LieDerivation.smul_apply, map_add,
      map_sub, map_smul, LieHom.map_lie, Ring.lie_def, mul_comm x.right y.right, sub_self,
      zero_smul, add_zero, hδ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hX, C_mul]
    module

/-- The algebra morphism `U(L ⋊⁅D.lineHom⁆ R) / (ι z - c) → U[X; δ]`. -/
private def toOre (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) : U' →ₐ[R] O :=
  lift (toOreLieHom hδ) (by simp [toOreLieHom])

private theorem toOre_ι (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x))
    (x : L ⋊⁅D.lineHom⁆ R) :
    toOre hδ (ι (inl D.lineHom z) c x) = C (ι z c x.left) + x.right • X :=
  lift_ι _ _ x

private theorem toOre_ι_inr_one (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) :
    toOre hδ (ι (inl D.lineHom z) c (inr D.lineHom 1)) = X := by
  rw [toOre_ι]
  simp

private theorem toOre_map_inl (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (a : U) :
    toOre hδ (map (inl D.lineHom) rfl a) = C a := by
  have h : (toOre hδ).comp (map (inl D.lineHom) rfl) = OreExtension.CAlgHom :=
    algHom_ext fun x ↦ by
      rw [AlgHom.comp_apply, map_ι, toOre_ι, CAlgHom_eq_C]
      simp
  rw [← CAlgHom_eq_C, ← h, AlgHom.comp_apply]

/-- **The adjoined derivation acts on `U` by `δ`**: in `U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)`, the
commutator of the adjoined element `d` with the image of `a ∈ U` is the image of `δ a`. -/
theorem ι_inr_mul_map_inl (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (a : U) :
    ι (inl D.lineHom z) c (inr D.lineHom 1) * map (inl D.lineHom) rfl a =
      map (inl D.lineHom) rfl a * ι (inl D.lineHom z) c (inr D.lineHom 1) +
        map (inl D.lineHom) rfl ((δ : Module.End R U) a) := by
  obtain ⟨u, rfl⟩ := mk_surjective z c a
  induction u using UniversalEnvelopingAlgebra.induction_ι with
  | ι x =>
    rw [← ι_apply, hδ, map_ι, map_ι, ← sub_eq_iff_eq_add', ← Ring.lie_def, ← LieHom.map_lie,
      LieDerivation.lie_inr_lineHom_one_inl]
  | algebraMap r =>
    have h0 : (δ : Module.End R U) (algebraMap R U r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, derivationLieAlgebra.apply_one_eq_zero,
        smul_zero]
    rw [AlgHom.commutes, h0, map_zero, add_zero, AlgHom.commutes, Algebra.commutes]
  | add u v hu hv =>
    simp only [map_add, mul_add, add_mul, hu, hv]
    abel
  | mul u v hu hv =>
    simp only [map_mul, derivationLieAlgebra.leibniz, map_add, add_mul, ← mul_assoc, hu]
    simp only [mul_assoc, hv, mul_add]
    abel

/-- The algebra morphism `U[X; δ] → U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)` sending `C a` to the image of
`a` and `X` to the adjoined element. -/
private def ofOre (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) : O →ₐ[R] U' :=
  liftAlgHom (map (inl D.lineHom) rfl) (ι (inl D.lineHom z) c (inr D.lineHom 1)) fun a ↦ by
    rw [ι_inr_mul_map_inl hδ, AlgHom.id_apply, derivationLieAlgebra.coe_toSigmaDerivation]

private theorem ofOre_C (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (a : U) :
    ofOre hδ (C a) = map (inl D.lineHom) rfl a :=
  liftAlgHom_C _ _ _ a

private theorem ofOre_X (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) :
    ofOre hδ X = ι (inl D.lineHom z) c (inr D.lineHom 1) :=
  liftAlgHom_X _ _ _

/-- **The enveloping algebra of `L` with an adjoined derivation is a differential operator ring.**
If the derivation `δ` of `U = U(L) / (ι z - c)` extends the derivation `D` of `L`, then
`U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)` is the Ore extension `U[X; δ]`: the image of `x : L` corresponds
to `C (ι x)` and the adjoined element `d = inr 1` to `X`. -/
def semiDirectSumOreEquiv (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) : U' ≃ₐ[R] O :=
  AlgEquiv.ofAlgHom (toOre hδ) (ofOre hδ)
    (OreExtension.algHom_ext
      (fun a ↦ by rw [AlgHom.comp_apply, ofOre_C, toOre_map_inl, AlgHom.id_apply])
      (by rw [AlgHom.comp_apply, ofOre_X, toOre_ι_inr_one, AlgHom.id_apply]))
    (algHom_ext fun x ↦ by
      -- Every element of the semidirect sum is `inl x.left + x.right • inr 1`.
      have hx : x = inl D.lineHom x.left + x.right • inr D.lineHom 1 := by ext <;> simp
      rw [AlgHom.comp_apply, toOre_ι, map_add, map_smul, ofOre_C, ofOre_X, map_ι,
        AlgHom.id_apply]
      conv_rhs => rw [hx, map_add, map_smul])

private theorem semiDirectSumOreEquiv_apply
    (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (y : U') :
    semiDirectSumOreEquiv hδ y = toOre hδ y :=
  (rfl)

private theorem semiDirectSumOreEquiv_symm_apply
    (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (p : O) :
    (semiDirectSumOreEquiv hδ).symm p = ofOre hδ p :=
  (rfl)

-- The lemmas below are not `simp` lemmas: Mathlib's `SemiDirectSum.inl_eq_mk` and
-- `SemiDirectSum.inr_eq_mk` rewrite `inl` and `inr` in their left-hand sides. Consumers with a
-- named semidirect sum restate them as `simp` lemmas, as for the extended affine algebra.

/-- The equivalence sends the image of `x : L` to the constant `C (ι x)`. -/
theorem semiDirectSumOreEquiv_ι_inl (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x))
    (x : L) : semiDirectSumOreEquiv hδ (ι (inl D.lineHom z) c (inl D.lineHom x)) = C (ι z c x) := by
  rw [semiDirectSumOreEquiv_apply, toOre_ι]
  simp

/-- The equivalence sends the adjoined element `d = inr 1` to the variable `X`. -/
theorem semiDirectSumOreEquiv_ι_inr_one
    (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) :
    semiDirectSumOreEquiv hδ (ι (inl D.lineHom z) c (inr D.lineHom 1)) = X := by
  rw [semiDirectSumOreEquiv_apply, toOre_ι_inr_one]

/-- On the image of `U`, the equivalence is the inclusion of the constants. -/
theorem semiDirectSumOreEquiv_map_inl (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x))
    (a : U) : semiDirectSumOreEquiv hδ (map (inl D.lineHom) rfl a) = C a := by
  rw [semiDirectSumOreEquiv_apply, toOre_map_inl]

/-- **The left monomial basis**: the inverse equivalence sends the monomial `a Xⁿ` to `a dⁿ`, the
product of the image of `a ∈ U` with the `n`-th power of the adjoined element. -/
theorem semiDirectSumOreEquiv_symm_monomial
    (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) (n : ℕ) (a : U) :
    (semiDirectSumOreEquiv hδ).symm (monomial n a) =
      map (inl D.lineHom) rfl a * ι (inl D.lineHom z) c (inr D.lineHom 1) ^ n := by
  rw [semiDirectSumOreEquiv_symm_apply, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, ofOre_C,
    ofOre_X]

/-- **The enveloping algebra of `L` embeds.** If `D` extends to a derivation of
`U(L) / (ι z - c)`, the algebra map to `U(L ⋊⁅D.lineHom⁆ R) / (ι z - c)` induced by the inclusion
of `L` is injective. -/
theorem map_inl_injective (hδ : ∀ x, (δ : Module.End R U) (ι z c x) = ι z c (D x)) :
    Function.Injective (map (c := c) (inl D.lineHom) (rfl : inl D.lineHom z = _)) := by
  intro a b h
  have h' := congrArg (semiDirectSumOreEquiv hδ) h
  rw [semiDirectSumOreEquiv_map_inl, semiDirectSumOreEquiv_map_inl] at h'
  exact CRingHom_injective (σ := AlgHom.id R U) (δ := derivationLieAlgebra.toSigmaDerivation δ)
    (by rwa [CRingHom_eq_C, CRingHom_eq_C])

end TauCeti.UniversalEnvelopingAlgebra.CentralQuotient
