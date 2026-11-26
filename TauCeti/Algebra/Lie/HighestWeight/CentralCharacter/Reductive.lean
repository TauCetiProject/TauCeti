/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isomorphism
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

## Main definitions

* `TauCeti.reductiveCentralCharacter`: the central character of weight `(ζ, λ)`.
* `TauCeti.reductiveHarishChandraIso`: `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}`.
* `TauCeti.reductiveHarishChandraLinearIso`: `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`.

## Main results

* `TauCeti.reductiveHarishChandraIso_symm_tmul`: the inverse on a pure tensor `a ⊗ p` is the
  product of the image of `a ∈ Sym(z(L)) = U(z(L))` and of the central element of `U([L, L])` with
  Harish-Chandra image `p`.
* `TauCeti.reductiveHarishChandraIso_inclusion`: followed by the inclusion of the invariants, the
  Harish-Chandra isomorphism is `id ⊗ hcProjection` of the centre comparison.
* `TauCeti.reductiveCentralCharacter_eq_iff`: Harish-Chandra's theorem on central characters for a
  reductive Lie algebra.
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

/-! ### Central characters -/

/-- The **central character of weight `(ζ, λ)`** of `Z(U(L))` for a reductive `L`, with an
arbitrary central weight `ζ ∈ z(L)^*` and `λ ∈ H^*`: through the centre comparison
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`, evaluation at `ζ` on `Sym(z(L))` times the central
character `χ_λ` of the Verma module `M(λ)` of `[L, L]` on `Z(U([L, L]))`. -/
noncomputable def reductiveCentralCharacter (ζ : Module.Dual K (center K L))
    (lam : Module.Dual K H) : Subalgebra.center K (U L) →ₐ[K] K :=
  (Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ) (vermaCentralCharacter b lam)
    fun _ _ ↦ .all _ _).comp (reductiveCenterEquiv K L).toAlgHom

variable {b} in
/-- The central character of weight `(ζ, λ)` on the product of an element of `Sym(z(L))` and a
central element of `U([L, L])`. -/
@[simp]
theorem reductiveCentralCharacter_reductiveCenterEquiv_symm_tmul (ζ : Module.Dual K (center K L))
    (lam : Module.Dual K H) (a : SZ) (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveCentralCharacter b ζ lam ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      _root_.SymmetricAlgebra.lift ζ a * vermaCentralCharacter b lam c := by
  simp [reductiveCentralCharacter]

variable [IsAlgClosed K]

/-! ### The isomorphisms -/

/-- **The Harish-Chandra isomorphism of a reductive Lie algebra**,
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}`: the centre comparison
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))` followed by the identity on `Sym(z(L))` tensored with the
Harish-Chandra isomorphism of the derived ideal. -/
noncomputable def reductiveHarishChandraIso :
    Subalgebra.center K (U L) ≃ₐ[K] SZ ⊗[K] dotInvariants b :=
  (reductiveCenterEquiv K L).trans (Algebra.TensorProduct.congr AlgEquiv.refl (harishChandraIso b))

/-- **The linear Harish-Chandra isomorphism of a reductive Lie algebra**,
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`. -/
noncomputable def reductiveHarishChandraLinearIso :
    Subalgebra.center K (U L) ≃ₐ[K] SZ ⊗[K] linearInvariants H :=
  (reductiveCenterEquiv K L).trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (harishChandraLinearIso b))

/-- The Harish-Chandra isomorphism of `L` is the Harish-Chandra isomorphism of `[L, L]` on the
second factor of the centre comparison. -/
theorem reductiveHarishChandraIso_apply (z : Subalgebra.center K (U L)) :
    reductiveHarishChandraIso b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : SZ ≃ₐ[K] SZ) (harishChandraIso b)
        (reductiveCenterEquiv K L z) :=
  (rfl)

/-- The linear Harish-Chandra isomorphism of `L` is the linear Harish-Chandra isomorphism of
`[L, L]` on the second factor of the centre comparison. -/
theorem reductiveHarishChandraLinearIso_apply (z : Subalgebra.center K (U L)) :
    reductiveHarishChandraLinearIso b z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : SZ ≃ₐ[K] SZ) (harishChandraLinearIso b)
        (reductiveCenterEquiv K L z) :=
  (rfl)

/-- The Harish-Chandra isomorphism of `L` on the product of an element of `Sym(z(L))` and a
central element of `U([L, L])`. -/
@[simp]
theorem reductiveHarishChandraIso_reductiveCenterEquiv_symm_tmul (a : SZ)
    (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveHarishChandraIso b ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraIso b c := by
  simp [reductiveHarishChandraIso_apply]

/-- The linear Harish-Chandra isomorphism of `L` on the product of an element of `Sym(z(L))` and
a central element of `U([L, L])`. -/
@[simp]
theorem reductiveHarishChandraLinearIso_reductiveCenterEquiv_symm_tmul (a : SZ)
    (c : Subalgebra.center K (U (derivedSeries K L 1))) :
    reductiveHarishChandraLinearIso b ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c)) =
      a ⊗ₜ[K] harishChandraLinearIso b c := by
  simp [reductiveHarishChandraLinearIso_apply]

/-- The inverse Harish-Chandra isomorphism of `L` on a pure tensor `a ⊗ p` is the product of the
image of `a ∈ Sym(z(L)) = U(z(L))` and the image of the central element of `U([L, L])` with
Harish-Chandra image `p`. -/
@[simp]
theorem reductiveHarishChandraIso_symm_tmul (a : SZ) (p : dotInvariants b) :
    ((reductiveHarishChandraIso b).symm (a ⊗ₜ[K] p) : U L) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl
          ((harishChandraIso b).symm p : U (derivedSeries K L 1)) := by
  rw [reductiveHarishChandraIso, AlgEquiv.symm_trans_apply, Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  exact reductiveCenterEquiv_symm_tmul K L a _

/-- The inverse linear Harish-Chandra isomorphism of `L` on a pure tensor `a ⊗ q`. -/
@[simp]
theorem reductiveHarishChandraLinearIso_symm_tmul (a : SZ) (q : linearInvariants H) :
    ((reductiveHarishChandraLinearIso b).symm (a ⊗ₜ[K] q) : U L) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl
          ((harishChandraLinearIso b).symm q : U (derivedSeries K L 1)) := by
  rw [reductiveHarishChandraLinearIso, AlgEquiv.symm_trans_apply,
    Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul]
  exact reductiveCenterEquiv_symm_tmul K L a _

/-- **The inclusion square of the Harish-Chandra isomorphism.** Followed by the inclusion of the
dot-invariants into `S(H)`, the Harish-Chandra isomorphism of `L` is the centre comparison followed
by `id ⊗ hcProjection` of the derived ideal. -/
theorem reductiveHarishChandraIso_inclusion (z : Subalgebra.center K (U L)) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (dotInvariants b).val
        (reductiveHarishChandraIso b z) =
      Algebra.TensorProduct.map (AlgHom.id K SZ) (hcProjection b) (reductiveCenterEquiv K L z) := by
  obtain ⟨t, rfl⟩ := (reductiveCenterEquiv K L).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **The inclusion square of the linear Harish-Chandra isomorphism.** -/
theorem reductiveHarishChandraLinearIso_inclusion (z : Subalgebra.center K (U L)) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (linearInvariants H).val
        (reductiveHarishChandraLinearIso b z) =
      Algebra.TensorProduct.map (AlgHom.id K SZ) (hcProjectionLinear b)
        (reductiveCenterEquiv K L z) := by
  obtain ⟨t, rfl⟩ := (reductiveCenterEquiv K L).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The two Harish-Chandra isomorphisms of `L` differ by the translation by `-ρ` on the second
factor only: `ρ` is extended by zero on `z(L)`. -/
theorem reductiveHarishChandraIso_trans_congr_dotInvariantsEquivLinearInvariants :
    (reductiveHarishChandraIso b).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl (dotInvariantsEquivLinearInvariants b)) =
      reductiveHarishChandraLinearIso b := by
  rw [reductiveHarishChandraLinearIso, ← harishChandraIso_trans_dotInvariantsEquivLinearInvariants]
  -- Mathlib has no `AlgEquiv.trans_assoc` or `AlgEquiv.refl_trans`: associativity of
  -- `AlgEquiv.trans` and `AlgEquiv.refl.trans AlgEquiv.refl = AlgEquiv.refl` close by defeq here.
  exact congrArg (reductiveCenterEquiv K L).trans
    (Algebra.TensorProduct.congr_trans .refl .refl (harishChandraIso b) _).symm

variable {b}

/-- **Central characters through the Harish-Chandra isomorphism.** The central character of weight
`(ζ, λ)` is evaluation of the Harish-Chandra image at `(ζ, λ)`. -/
theorem reductiveCentralCharacter_eq_lift_reductiveHarishChandraIso
    (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H) (z : Subalgebra.center K (U L)) :
    reductiveCentralCharacter b ζ lam z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (dotInvariants b).val) (fun _ _ ↦ .all _ _)
        (reductiveHarishChandraIso b z) := by
  obtain ⟨t, rfl⟩ := (reductiveCenterEquiv K L).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [lift_hcProjection]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Central characters through the linear Harish-Chandra isomorphism.** The central character of
weight `(ζ, λ - ρ)` is evaluation of the linear Harish-Chandra image at `(ζ, λ)`. -/
theorem reductiveCentralCharacter_sub_eq_lift_reductiveHarishChandraLinearIso
    (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H) (z : Subalgebra.center K (U L)) :
    reductiveCentralCharacter b ζ (lam - weylVector (IsKilling.rootSystem H) b) z =
      Algebra.TensorProduct.lift (_root_.SymmetricAlgebra.lift ζ)
        ((_root_.SymmetricAlgebra.lift lam).comp (linearInvariants H).val) (fun _ _ ↦ .all _ _)
        (reductiveHarishChandraLinearIso b z) := by
  obtain ⟨t, rfl⟩ := (reductiveCenterEquiv K L).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [lift_hcProjectionLinear]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Harish-Chandra's theorem on central characters for a reductive Lie algebra.** The central
characters of weights `(ζ, λ)` and `(ζ', μ)` agree exactly when `ζ = ζ'` and `μ` lies in the dot
orbit of `λ`. -/
theorem reductiveCentralCharacter_eq_iff {ζ ζ' : Module.Dual K (center K L)}
    {lam mu : Module.Dual K H} :
    reductiveCentralCharacter b ζ lam = reductiveCentralCharacter b ζ' mu ↔
      ζ = ζ' ∧ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  refine ⟨fun h ↦ ⟨LinearMap.ext fun x ↦ ?_, (vermaCentralCharacter_eq_iff b).mp ?_⟩, ?_⟩
  · have := congr($h ((reductiveCenterEquiv K L).symm
      (_root_.SymmetricAlgebra.ι K (center K L) x ⊗ₜ 1)))
    simpa using this
  · refine AlgHom.ext fun c ↦ ?_
    have := congr($h ((reductiveCenterEquiv K L).symm (1 ⊗ₜ c)))
    simpa using this
  · rintro ⟨rfl, w, rfl⟩
    simp only [reductiveCentralCharacter, vermaCentralCharacter_dotAction]

end TauCeti
