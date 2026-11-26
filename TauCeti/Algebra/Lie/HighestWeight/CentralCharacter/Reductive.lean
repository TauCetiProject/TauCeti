/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Product
public import TauCeti.Algebra.Lie.Reductive.EnvelopingCenter

/-!
# The Harish-Chandra isomorphism of a reductive Lie algebra

Let `L` be a finite-dimensional reductive Lie algebra over a field `K` of characteristic zero. Its
derived ideal `[L, L]` has non-degenerate Killing form (`TauCeti.isKilling_derivedSeries`); fix a
Cartan subalgebra `H` of `[L, L]` and a base `b` of its root system. The centre of `U(L)` is
`Sym(z(L)) ⊗ Z(U([L, L]))` (`TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv`), and
tensoring the Harish-Chandra isomorphisms of the derived ideal with the identity of `Sym(z(L))`
gives, for `K` algebraically closed, the Harish-Chandra isomorphisms of `L`,

`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}` and `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`

(`TauCeti.reductiveHarishChandraIso`, `TauCeti.reductiveHarishChandraLinearIso`). The Weyl group
fixes `z(L)` and `ρ` is extended by zero on `z(L)`, so the translation by `-ρ` relating the two
does not move the `Sym(z(L))` factor
(`TauCeti.reductiveHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants`).

For an arbitrary central weight `ζ ∈ z(L)^*` and `λ ∈ H^*`, the character
`TauCeti.reductiveCentralCharacter b ζ λ` of `Z(U(L))` is evaluation at `ζ` on `Sym(z(L))` and the
central character `χ_λ` of the Verma module `M(λ)` of `[L, L]` on `Z(U([L, L]))`. It is evaluation
at `(ζ, λ)` after the Harish-Chandra isomorphism
(`TauCeti.reductiveCentralCharacter_eq_lift_reductiveHarishChandraIso`), or at `(ζ, λ + ρ)` after
the linear one (`TauCeti.reductiveCentralCharacter_sub_eq_lift_reductiveHarishChandraLinearIso`).
Two of these characters agree exactly when the central weights agree and the `H`-weights lie in one
dot orbit (`TauCeti.reductiveCentralCharacter_eq_iff`). The input is the Harish-Chandra theorem of
the derived ideal; no Killing hypothesis on `L` is used.

This follows `CentralCharacter/Product.lean`: each construction here is its counterpart there
(`TauCeti.productCentralCharacter`, `TauCeti.productHarishChandraIso`,
`TauCeti.productHarishChandraLinearIso`) for `Z = z(L)` and `S = [L, L]`, composed with the
isomorphism `Z(U(L)) ≃ Z(U(z(L) × [L, L]))` induced by the splitting `L ≃ z(L) × [L, L]`, through
which `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv` factors; the results are derived
from those of the product.

## Main definitions

* `TauCeti.reductiveCentralCharacter`: the central character of weight `(ζ, λ)`.
* `TauCeti.reductiveHarishChandraIso`: `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}`.
* `TauCeti.reductiveHarishChandraLinearIso`: `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`.

## Main results

* `TauCeti.reductiveHarishChandraIso_symm_tmul`: the inverse on a pure tensor `a ⊗ p` is the
  product of the image of `a ∈ Sym(z(L)) = U(z(L))` and of the central element of `U([L, L])` with
  Harish-Chandra image `p`.
* `TauCeti.map_val_reductiveHarishChandraIso_apply`: followed by the inclusion of the invariants,
  the Harish-Chandra isomorphism is `id ⊗ hcProjection` of the centre comparison.
* `TauCeti.reductiveCentralCharacter_eq_iff`: Harish-Chandra's theorem on central characters for a
  reductive Lie algebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3, for the
  Harish-Chandra isomorphism of the semisimple derived ideal.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter V, §5, for the
  Harish-Chandra isomorphism of a reductive Lie algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L]
  {H : LieSubalgebra K (derivedSeries K L 1)} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H (derivedSeries K L 1)]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K
local notation "SZ" => _root_.SymmetricAlgebra K (center K L)

/- The centre of `U(L)` and the centre of `U(z(L) × [L, L])`, through the splitting
`L ≃ z(L) × [L, L]`. -/
local notation "ZE" => Subalgebra.centerCongr (mapEquiv K (LieEquiv.symm
  (LieIdeal.prodEquivOfIsCompl (center K L) (derivedSeries K L 1)
    (isCompl_center_derivedSeries K L))))

/-- The centre comparison of `L` is that of `z(L) × [L, L]` through the splitting. -/
private theorem reductiveCenterEquiv_eq_trans :
    reductiveCenterEquiv K L =
      (ZE).trans (productCenterEquiv K (center K L) (derivedSeries K L 1)) :=
  (reductiveCenterEquiv_def K L).trans (centerEquivOfIsCompl_def _ _ _ _)

/-! ### Central characters -/

/-- The **central character of weight `(ζ, λ)`** of `Z(U(L))` for a reductive `L`, with an
arbitrary central weight `ζ ∈ z(L)^*` and `λ ∈ H^*`: through the centre comparison
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`, evaluation at `ζ` on `Sym(z(L))` times the central
character `χ_λ` of the Verma module `M(λ)` of `[L, L]` on `Z(U([L, L]))`. It is
`TauCeti.productCentralCharacter` through the splitting `L ≃ z(L) × [L, L]`. -/
noncomputable def reductiveCentralCharacter (ζ : Module.Dual K (center K L))
    (lam : Module.Dual K H) : Subalgebra.center K (U L) →ₐ[K] K :=
  (productCentralCharacter b ζ lam).comp (ZE).toAlgHom

variable {b} in
/-- The central character of weight `(ζ, λ)` on the product of an element of `Sym(z(L))` and a
central element of `U([L, L])`. -/
@[simp]
theorem reductiveCentralCharacter_reductiveCenterEquiv_symm_tmul (ζ : Module.Dual K (center K L))
    (lam : Module.Dual K H) (a : SZ) (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveCentralCharacter b ζ lam ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      _root_.SymmetricAlgebra.lift ζ a * vermaCentralCharacter b lam c := by
  rw [reductiveCentralCharacter, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    reductiveCenterEquiv_eq_trans, AlgEquiv.symm_trans_apply, AlgEquiv.apply_symm_apply]
  exact productCentralCharacter_productCenterEquiv_symm_tmul ζ lam a c

variable [IsAlgClosed K]

/-! ### The isomorphisms -/

/-- **The Harish-Chandra isomorphism of a reductive Lie algebra**,
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}`: the centre comparison
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))` followed by the identity on `Sym(z(L))` tensored with the
Harish-Chandra isomorphism of the derived ideal. It is `TauCeti.productHarishChandraIso` through
the splitting `L ≃ z(L) × [L, L]`. -/
noncomputable def reductiveHarishChandraIso :
    Subalgebra.center K (U L) ≃ₐ[K] SZ ⊗[K] dotInvariants b :=
  (ZE).trans (productHarishChandraIso (center K L) b)

/-- **The linear Harish-Chandra isomorphism of a reductive Lie algebra**,
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`. -/
noncomputable def reductiveHarishChandraLinearIso :
    Subalgebra.center K (U L) ≃ₐ[K] SZ ⊗[K] linearInvariants H :=
  (ZE).trans (productHarishChandraLinearIso (center K L) b)

/-- The Harish-Chandra isomorphism of `L` is the Harish-Chandra isomorphism of `[L, L]` on the
second factor of the centre comparison. -/
theorem reductiveHarishChandraIso_apply (z : Subalgebra.center K (U L)) :
    reductiveHarishChandraIso b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : SZ ≃ₐ[K] SZ) (harishChandraIso b)
        (reductiveCenterEquiv K L z) := by
  rw [reductiveHarishChandraIso, AlgEquiv.trans_apply, productHarishChandraIso_apply,
    reductiveCenterEquiv_eq_trans, AlgEquiv.trans_apply]

/-- The linear Harish-Chandra isomorphism of `L` is the linear Harish-Chandra isomorphism of
`[L, L]` on the second factor of the centre comparison. -/
theorem reductiveHarishChandraLinearIso_apply (z : Subalgebra.center K (U L)) :
    reductiveHarishChandraLinearIso b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : SZ ≃ₐ[K] SZ) (harishChandraLinearIso b)
        (reductiveCenterEquiv K L z) := by
  rw [reductiveHarishChandraLinearIso, AlgEquiv.trans_apply, productHarishChandraLinearIso_apply,
    reductiveCenterEquiv_eq_trans, AlgEquiv.trans_apply]

/-- The Harish-Chandra isomorphism of `L` on the product of an element of `Sym(z(L))` and a
central element of `U([L, L])`. -/
@[simp]
theorem reductiveHarishChandraIso_reductiveCenterEquiv_symm_tmul (a : SZ)
    (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveHarishChandraIso b ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraIso b c := by
  rw [reductiveHarishChandraIso, AlgEquiv.trans_apply, reductiveCenterEquiv_eq_trans,
    AlgEquiv.symm_trans_apply, AlgEquiv.apply_symm_apply]
  exact productHarishChandraIso_productCenterEquiv_symm_tmul _ b a c

/-- The linear Harish-Chandra isomorphism of `L` on the product of an element of `Sym(z(L))` and
a central element of `U([L, L])`. -/
@[simp]
theorem reductiveHarishChandraLinearIso_reductiveCenterEquiv_symm_tmul (a : SZ)
    (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveHarishChandraLinearIso b ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraLinearIso b c := by
  rw [reductiveHarishChandraLinearIso, AlgEquiv.trans_apply, reductiveCenterEquiv_eq_trans,
    AlgEquiv.symm_trans_apply, AlgEquiv.apply_symm_apply]
  exact productHarishChandraLinearIso_productCenterEquiv_symm_tmul _ b a c

/-- The inverse Harish-Chandra isomorphism of `L` on a pure tensor `a ⊗ p` is the product of the
image of `a ∈ Sym(z(L)) = U(z(L))` and the image of the central element of `U([L, L])` with
Harish-Chandra image `p`. -/
@[simp]
theorem reductiveHarishChandraIso_symm_tmul (a : SZ) (p : dotInvariants b) :
    ((reductiveHarishChandraIso b).symm (a ⊗ₜ[K] p) : U L) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl
          ((harishChandraIso b).symm p : U (derivedSeries K L 1)) := by
  obtain ⟨c, rfl⟩ := (harishChandraIso b).surjective p
  rw [← reductiveHarishChandraIso_reductiveCenterEquiv_symm_tmul, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]
  exact reductiveCenterEquiv_symm_tmul K L a c

/-- The inverse linear Harish-Chandra isomorphism of `L` on a pure tensor `a ⊗ q`. -/
@[simp]
theorem reductiveHarishChandraLinearIso_symm_tmul (a : SZ) (q : linearInvariants H) :
    ((reductiveHarishChandraLinearIso b).symm (a ⊗ₜ[K] q) : U L) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl
          ((harishChandraLinearIso b).symm q : U (derivedSeries K L 1)) := by
  obtain ⟨c, rfl⟩ := (harishChandraLinearIso b).surjective q
  rw [← reductiveHarishChandraLinearIso_reductiveCenterEquiv_symm_tmul, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]
  exact reductiveCenterEquiv_symm_tmul K L a c

/-- **The inclusion square of the Harish-Chandra isomorphism.** Followed by the inclusion of the
dot-invariants into `S(H)`, the Harish-Chandra isomorphism of `L` is the centre comparison followed
by `id ⊗ hcProjection` of the derived ideal. -/
theorem map_val_reductiveHarishChandraIso_apply (z : Subalgebra.center K (U L)) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (dotInvariants b).val
        (reductiveHarishChandraIso b z) =
      Algebra.TensorProduct.map (AlgHom.id K SZ) (hcProjection b) (reductiveCenterEquiv K L z) := by
  rw [reductiveHarishChandraIso, AlgEquiv.trans_apply, map_val_productHarishChandraIso_apply,
    reductiveCenterEquiv_eq_trans, AlgEquiv.trans_apply]

/-- **The inclusion square of the linear Harish-Chandra isomorphism.** -/
theorem map_val_reductiveHarishChandraLinearIso_apply (z : Subalgebra.center K (U L)) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (linearInvariants H).val
        (reductiveHarishChandraLinearIso b z) =
      Algebra.TensorProduct.map (AlgHom.id K SZ) (hcProjectionLinear b)
        (reductiveCenterEquiv K L z) := by
  rw [reductiveHarishChandraLinearIso, AlgEquiv.trans_apply,
    map_val_productHarishChandraLinearIso_apply, reductiveCenterEquiv_eq_trans,
    AlgEquiv.trans_apply]

/-- The two Harish-Chandra isomorphisms of `L` differ by the translation by `-ρ` on the second
factor only: `ρ` is extended by zero on `z(L)`. -/
theorem reductiveHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants :
    (reductiveHarishChandraIso b).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl (dotInvariantsEquivLinearInvariants b)) =
      reductiveHarishChandraLinearIso b := by
  rw [reductiveHarishChandraLinearIso,
    ← productHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants]
  -- Mathlib has no `AlgEquiv.trans_assoc`: associativity of `AlgEquiv.trans` closes by defeq.
  rfl

variable {b}

/-- **Central characters through the Harish-Chandra isomorphism.** The central character of weight
`(ζ, λ)` is evaluation of the Harish-Chandra image at `(ζ, λ)`. -/
theorem reductiveCentralCharacter_eq_lift_reductiveHarishChandraIso
    (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H) (z : Subalgebra.center K (U L)) :
    reductiveCentralCharacter b ζ lam z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (dotInvariants b).val) (fun _ _ ↦ .all _ _)
        (reductiveHarishChandraIso b z) :=
  productCentralCharacter_eq_lift_productHarishChandraIso ζ lam _

/-- **Central characters through the linear Harish-Chandra isomorphism.** The central character of
weight `(ζ, λ - ρ)` is evaluation of the linear Harish-Chandra image at `(ζ, λ)`. -/
theorem reductiveCentralCharacter_sub_eq_lift_reductiveHarishChandraLinearIso
    (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H) (z : Subalgebra.center K (U L)) :
    reductiveCentralCharacter b ζ (lam - weylVector (IsKilling.rootSystem H) b) z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (linearInvariants H).val) (fun _ _ ↦ .all _ _)
        (reductiveHarishChandraLinearIso b z) :=
  productCentralCharacter_sub_eq_lift_productHarishChandraLinearIso ζ lam _

/-- **Harish-Chandra's theorem on central characters for a reductive Lie algebra.** The central
characters of weights `(ζ, λ)` and `(ζ', μ)` agree exactly when `ζ = ζ'` and `μ` lies in the dot
orbit of `λ`. -/
theorem reductiveCentralCharacter_eq_iff {ζ ζ' : Module.Dual K (center K L)}
    {lam mu : Module.Dual K H} :
    reductiveCentralCharacter b ζ lam = reductiveCentralCharacter b ζ' mu ↔
      ζ = ζ' ∧ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu :=
  (AlgHom.cancel_right (ZE).surjective).trans productCentralCharacter_eq_iff

end TauCeti
