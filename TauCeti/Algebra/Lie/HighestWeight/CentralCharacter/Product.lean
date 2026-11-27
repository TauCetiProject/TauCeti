/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isomorphism
public import TauCeti.Algebra.Lie.UniversalEnveloping.Product.Center

/-!
# The Harish-Chandra isomorphism for a product with an abelian factor

Let `S` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, with a Cartan subalgebra `H` and a base `b` of its root
system, and let `Z` be an abelian Lie algebra. The centre of `U(Z × S)` is
`Sym(Z) ⊗ Z(U(S))` (`TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv`). Tensoring the
Harish-Chandra isomorphisms of `S` with the identity of `Sym(Z)` gives the Harish-Chandra
isomorphisms of `Z × S`,

`Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^{W·}` and `Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^W`

(`TauCeti.productHarishChandraIso`, `TauCeti.productHarishChandraLinearIso`). The Weyl group acts
trivially on `Z`, and `ρ` is extended by zero on `Z`, so the translation by `-ρ` relating the two
does not move the `Sym(Z)` factor
(`TauCeti.productHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants`).

For `ζ ∈ Z^*` and `λ ∈ H^*`, the character `TauCeti.productCentralCharacter b ζ λ` of
`Z(U(Z × S))` is evaluation at `ζ` on `Sym(Z)` and the central character `χ_λ` of the Verma module
`M(λ)` on `Z(U(S))`. It is evaluation at `(ζ, λ)` after the Harish-Chandra isomorphism
(`TauCeti.productCentralCharacter_eq_lift_productHarishChandraIso`), or at `(ζ, λ + ρ)` after the
linear one (`TauCeti.productCentralCharacter_sub_eq_lift_productHarishChandraLinearIso`). Two of
these characters agree exactly when the `Z`-weights agree and the `H`-weights lie in one dot orbit
(`TauCeti.productCentralCharacter_eq_iff`).

## Main definitions

* `TauCeti.productHarishChandraIso`: `Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^{W·}`.
* `TauCeti.productHarishChandraLinearIso`: `Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^W`.
* `TauCeti.productCentralCharacter`: the central character of weight `(ζ, λ)`.

## Main results

* `TauCeti.productHarishChandraIso_symm_tmul`: the inverse on a pure tensor `a ⊗ p` is the product
  of `a ∈ Sym(Z) = U(Z)` and the central element of `U(S)` with Harish-Chandra image `p`.
* `TauCeti.map_val_productHarishChandraIso_apply`: followed by the inclusion of the invariants,
  the Harish-Chandra isomorphism is `id ⊗ hcProjection` of the centre comparison.
* `TauCeti.productCentralCharacter_eq_iff`: Harish-Chandra's theorem on central characters for
  `Z × S`.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  (Z : Type v) [LieRing Z] [LieAlgebra K Z] [IsLieAbelian Z]
  {S : Type w} [LieRing S] [LieAlgebra K S] [IsKilling K S] [FiniteDimensional K S]
  {H : LieSubalgebra K S} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H S]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-! ### Central characters -/

variable {Z} in
/-- The **central character of weight `(ζ, λ)`** of `Z(U(Z × S))`, for `ζ ∈ Z^*` and `λ ∈ H^*`:
through the centre comparison `Z(U(Z × S)) ≃ Sym(Z) ⊗ Z(U(S))`, evaluation at `ζ` on `Sym(Z)`
times the central character `χ_λ` of the Verma module `M(λ)` on `Z(U(S))`. -/
noncomputable def productCentralCharacter (ζ : Module.Dual K Z) (lam : Module.Dual K H) :
    Subalgebra.center K (U (Z × S)) →ₐ[K] K :=
  (Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ) (vermaCentralCharacter b lam)
    fun _ _ ↦ .all _ _).comp (productCenterEquiv K Z S).toAlgHom

variable {Z b} in
/-- The central character of weight `(ζ, λ)` on the product of an element of `Sym(Z)` and a
central element of `U(S)`. -/
@[simp]
theorem productCentralCharacter_productCenterEquiv_symm_tmul (ζ : Module.Dual K Z)
    (lam : Module.Dual K H) (a : _root_.SymmetricAlgebra K Z) (c : Subalgebra.center K (U S)) :
    productCentralCharacter b ζ lam ((productCenterEquiv K Z S).symm (a ⊗ₜ[K] c)) =
      _root_.SymmetricAlgebra.lift ζ a * vermaCentralCharacter b lam c := by
  simp [productCentralCharacter]

variable [IsAlgClosed K]

/-! ### The isomorphisms -/

/-- **The Harish-Chandra isomorphism of `Z × S`**, `Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^{W·}`: the
centre comparison `Z(U(Z × S)) ≃ Sym(Z) ⊗ Z(U(S))` followed by the identity on `Sym(Z)` tensored
with the Harish-Chandra isomorphism of `S`. -/
noncomputable def productHarishChandraIso :
    Subalgebra.center K (U (Z × S)) ≃ₐ[K] _root_.SymmetricAlgebra K Z ⊗[K] dotInvariants b :=
  (productCenterEquiv K Z S).trans (Algebra.TensorProduct.congr AlgEquiv.refl (harishChandraIso b))

/-- **The linear Harish-Chandra isomorphism of `Z × S`**,
`Z(U(Z × S)) ≃ₐ[K] Sym(Z) ⊗ S(H)^W`. -/
noncomputable def productHarishChandraLinearIso :
    Subalgebra.center K (U (Z × S)) ≃ₐ[K] _root_.SymmetricAlgebra K Z ⊗[K] linearInvariants H :=
  (productCenterEquiv K Z S).trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (harishChandraLinearIso b))

/-- The Harish-Chandra isomorphism of `Z × S` is the Harish-Chandra isomorphism of `S` on the
second factor of the centre comparison. -/
theorem productHarishChandraIso_apply (z : Subalgebra.center K (U (Z × S))) :
    productHarishChandraIso Z b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : _root_.SymmetricAlgebra K Z ≃ₐ[K] _)
        (harishChandraIso b) (productCenterEquiv K Z S z) :=
  (rfl)

/-- The linear Harish-Chandra isomorphism of `Z × S` is the linear Harish-Chandra isomorphism of
`S` on the second factor of the centre comparison. -/
theorem productHarishChandraLinearIso_apply (z : Subalgebra.center K (U (Z × S))) :
    productHarishChandraLinearIso Z b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : _root_.SymmetricAlgebra K Z ≃ₐ[K] _)
        (harishChandraLinearIso b) (productCenterEquiv K Z S z) :=
  (rfl)

/-- The Harish-Chandra isomorphism of `Z × S` on the product of an element of `Sym(Z)` and a
central element of `U(S)`. -/
@[simp]
theorem productHarishChandraIso_productCenterEquiv_symm_tmul (a : _root_.SymmetricAlgebra K Z)
    (c : Subalgebra.center K (U S)) :
    productHarishChandraIso Z b ((productCenterEquiv K Z S).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraIso b c := by
  simp [productHarishChandraIso_apply]

/-- The linear Harish-Chandra isomorphism of `Z × S` on the product of an element of `Sym(Z)` and
a central element of `U(S)`. -/
@[simp]
theorem productHarishChandraLinearIso_productCenterEquiv_symm_tmul
    (a : _root_.SymmetricAlgebra K Z) (c : Subalgebra.center K (U S)) :
    productHarishChandraLinearIso Z b ((productCenterEquiv K Z S).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraLinearIso b c := by
  simp [productHarishChandraLinearIso_apply]

/-- The inverse Harish-Chandra isomorphism of `Z × S` on a pure tensor `a ⊗ p` is the product of
the image of `a ∈ Sym(Z) = U(Z)` and the image of the central element of `U(S)` with
Harish-Chandra image `p`. -/
@[simp]
theorem productHarishChandraIso_symm_tmul (a : _root_.SymmetricAlgebra K Z) (p : dotInvariants b) :
    ((productHarishChandraIso Z b).symm (a ⊗ₜ[K] p) : U (Z × S)) =
      map K (LieHom.inl K Z S) (symmetricAlgebraEquiv K Z a) *
        map K (LieHom.inr K Z S) ((harishChandraIso b).symm p : U S) := by
  rw [productHarishChandraIso, AlgEquiv.symm_trans_apply, Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  exact productCenterEquiv_symm_tmul K Z S a _

/-- The inverse linear Harish-Chandra isomorphism of `Z × S` on a pure tensor `a ⊗ q`. -/
@[simp]
theorem productHarishChandraLinearIso_symm_tmul (a : _root_.SymmetricAlgebra K Z)
    (q : linearInvariants H) :
    ((productHarishChandraLinearIso Z b).symm (a ⊗ₜ[K] q) : U (Z × S)) =
      map K (LieHom.inl K Z S) (symmetricAlgebraEquiv K Z a) *
        map K (LieHom.inr K Z S) ((harishChandraLinearIso b).symm q : U S) := by
  rw [productHarishChandraLinearIso, AlgEquiv.symm_trans_apply,
    Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul]
  exact productCenterEquiv_symm_tmul K Z S a _

/-- **The inclusion square of the Harish-Chandra isomorphism of `Z × S`.** Followed by the
inclusion of the dot-invariants into `S(H)`, the Harish-Chandra isomorphism of `Z × S` is the centre
comparison followed by `id ⊗ hcProjection` of `S`. -/
theorem map_val_productHarishChandraIso_apply (z : Subalgebra.center K (U (Z × S))) :
    Algebra.TensorProduct.map (AlgHom.id K (_root_.SymmetricAlgebra K Z)) (dotInvariants b).val
        (productHarishChandraIso Z b z) =
      Algebra.TensorProduct.map (AlgHom.id K _) (hcProjection b) (productCenterEquiv K Z S z) := by
  obtain ⟨t, rfl⟩ := (productCenterEquiv K Z S).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **The inclusion square of the linear Harish-Chandra isomorphism of `Z × S`.** -/
theorem map_val_productHarishChandraLinearIso_apply (z : Subalgebra.center K (U (Z × S))) :
    Algebra.TensorProduct.map (AlgHom.id K (_root_.SymmetricAlgebra K Z)) (linearInvariants H).val
        (productHarishChandraLinearIso Z b z) =
      Algebra.TensorProduct.map (AlgHom.id K _) (hcProjectionLinear b)
        (productCenterEquiv K Z S z) := by
  obtain ⟨t, rfl⟩ := (productCenterEquiv K Z S).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The two Harish-Chandra isomorphisms of `Z × S` differ by the translation by `-ρ` on the
second factor only: `ρ` is extended by zero on `Z`. -/
theorem productHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants :
    (productHarishChandraIso Z b).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl (dotInvariantsEquivLinearInvariants b)) =
      productHarishChandraLinearIso Z b := by
  rw [productHarishChandraLinearIso, ← harishChandraIso_trans_dotInvariantsEquivLinearInvariants]
  -- Mathlib has no `AlgEquiv.trans_assoc` or `AlgEquiv.refl_trans`: associativity of
  -- `AlgEquiv.trans` and `AlgEquiv.refl.trans AlgEquiv.refl = AlgEquiv.refl` close by defeq here.
  exact congrArg (productCenterEquiv K Z S).trans
    (Algebra.TensorProduct.congr_trans .refl .refl (harishChandraIso b) _).symm

variable {Z b}

/-- **Central characters through the Harish-Chandra isomorphism.** The central character of weight
`(ζ, λ)` is evaluation of the Harish-Chandra image at `(ζ, λ)`. -/
theorem productCentralCharacter_eq_lift_productHarishChandraIso (ζ : Module.Dual K Z)
    (lam : Module.Dual K H) (z : Subalgebra.center K (U (Z × S))) :
    productCentralCharacter b ζ lam z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (dotInvariants b).val) (fun _ _ ↦ .all _ _)
        (productHarishChandraIso Z b z) := by
  obtain ⟨t, rfl⟩ := (productCenterEquiv K Z S).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [lift_hcProjection]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Central characters through the linear Harish-Chandra isomorphism.** The central character of
weight `(ζ, λ - ρ)` is evaluation of the linear Harish-Chandra image at `(ζ, λ)`. -/
theorem productCentralCharacter_sub_eq_lift_productHarishChandraLinearIso (ζ : Module.Dual K Z)
    (lam : Module.Dual K H) (z : Subalgebra.center K (U (Z × S))) :
    productCentralCharacter b ζ (lam - weylVector (IsKilling.rootSystem H) b) z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (linearInvariants H).val) (fun _ _ ↦ .all _ _)
        (productHarishChandraLinearIso Z b z) := by
  obtain ⟨t, rfl⟩ := (productCenterEquiv K Z S).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [lift_hcProjectionLinear]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Harish-Chandra's theorem on central characters for `Z × S`.** The central characters of
weights `(ζ, λ)` and `(ζ', μ)` agree exactly when `ζ = ζ'` and `μ` lies in the dot orbit of `λ`. -/
theorem productCentralCharacter_eq_iff {ζ ζ' : Module.Dual K Z} {lam mu : Module.Dual K H} :
    productCentralCharacter b ζ lam = productCentralCharacter b ζ' mu ↔
      ζ = ζ' ∧ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  refine ⟨fun h ↦ ⟨LinearMap.ext fun x ↦ ?_, (vermaCentralCharacter_eq_iff b).mp ?_⟩, ?_⟩
  · have := congr($h ((productCenterEquiv K Z S).symm (_root_.SymmetricAlgebra.ι K Z x ⊗ₜ 1)))
    simpa using this
  · refine AlgHom.ext fun c ↦ ?_
    have := congr($h ((productCenterEquiv K Z S).symm (1 ⊗ₜ c)))
    simpa using this
  · rintro ⟨rfl, w, rfl⟩
    simp only [productCentralCharacter, vermaCentralCharacter_dotAction]

end TauCeti
