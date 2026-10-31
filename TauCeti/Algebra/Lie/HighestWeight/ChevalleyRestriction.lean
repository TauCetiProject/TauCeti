/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.Algebra.Lie.HighestWeight.TracePower
public import TauCeti.Algebra.Lie.Killing.ChevalleyRestriction

/-!
# Chevalley's restriction theorem

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and `H` a splitting Cartan subalgebra. Restricting polynomial functions from
`L` to `H` is, through the Killing identifications, the algebra map
`TauCeti.lieCartanRestriction H : S(L) →ₐ[K] S(H)`. **Chevalley's restriction theorem** says that
it restricts to an isomorphism from the invariants `S(L)^L` onto the Weyl invariants `S(H)^W`
(`TauCeti.linearInvariants H`). It has three parts.

* **Weyl invariance.** The restriction of an invariant is fixed by the coreflection of every root
  (`TauCeti.map_coreflection_lieCartanRestriction`), and the coreflections generate the Weyl
  group.
* **Injectivity** on `S(L)^L` is `LieSubalgebra.lieCartanRestriction_injOn_lieInvariants`: it rests
  on the density of the conjugates of `H` under the inner automorphisms.
* **Surjectivity.** The Weyl invariants form a graded subalgebra, and in each degree `m` they are
  spanned by the power sums `∑_μ dim L(λ)_μ · t_μ ^ m` of the weights of the irreducible modules
  `L(λ)`, `λ` dominant integral
  (`TauCeti.span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule`).
  Each such power sum is the restriction of the invariant polynomial function
  `x ↦ tr (ρ_λ(x) ^ m)` on `L`. This part uses that `K` is algebraically closed.

## Main definitions

* `LieSubalgebra.lieChevalleyRestrictionIso H`: the isomorphism `S(L)^L ≃ₐ[K] S(H)^W` given by
  restriction to `H`.

## Main results

* `TauCeti.lieCartanRestriction_mem_linearInvariants`: the restriction of an invariant is a Weyl
  invariant.
* `LieSubalgebra.linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants`: a homogeneous
  Weyl invariant of degree `m` is the restriction of an invariant of degree `m`.
* `LieSubalgebra.map_lieInvariants_lieCartanRestriction`: the image of `S(L)^L` is `S(H)^W`.
* `LieSubalgebra.lieChevalleyRestrictionIso_mem_homogeneousSubmodule_iff`: the isomorphism
  preserves degrees in both directions.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-! ### Weyl invariance of the restriction -/

section Weyl

variable [IsTriangularizable K H L]

variable {H} in
/-- **The restriction of an invariant is a Weyl invariant**: for `p ∈ S(L)^L`, the restriction
`TauCeti.lieCartanRestriction H p` lies in `S(H)^W`. -/
theorem lieCartanRestriction_mem_linearInvariants {p : _root_.SymmetricAlgebra K L}
    (hp : p ∈ lieInvariants K L L) : lieCartanRestriction H p ∈ linearInvariants H := by
  rw [mem_linearInvariants_iff]
  rintro ⟨w, hw⟩ lam
  induction hw using RootPairing.weylGroup.induction generalizing lam with
  | mem i =>
    -- the reflection of weights is the transpose of the coreflection
    have hs : (⟨_, (rootSystem H).reflection_mem_weylGroup i⟩ : (rootSystem H).weylGroup) • lam =
        lam ∘ₗ ((rootSystem H).coreflection i).toLinearMap :=
      LinearMap.ext fun y ↦ by
        simp [RootPairing.reflection_apply, RootPairing.coreflection_apply, mul_comm]
    have hlift :
        _root_.SymmetricAlgebra.lift (lam ∘ₗ ((rootSystem H).coreflection i).toLinearMap) =
          (_root_.SymmetricAlgebra.lift lam).comp
            (_root_.SymmetricAlgebra.map K ((rootSystem H).coreflection i).toLinearMap) :=
      _root_.SymmetricAlgebra.algHom_ext (LinearMap.ext fun y ↦ by simp)
    rw [hs, hlift, AlgHom.comp_apply, map_coreflection_lieCartanRestriction i hp]
  | one => simp
  | mul x y hx hy ihx ihy => rw [← MulMemClass.mk_mul_mk (hx := hx) (hy := hy), mul_smul, ihx, ihy]

end Weyl

end TauCeti

namespace LieSubalgebra

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module TauCeti TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-! ### Surjectivity onto the Weyl invariants -/

section Surjective

variable [IsAlgClosed K]

/-- **A homogeneous Weyl invariant is the restriction of a homogeneous invariant.** Every Weyl
invariant `q ∈ S(H)^W` homogeneous of degree `m` is `TauCeti.lieCartanRestriction H p` for some
invariant `p ∈ S(L)^L` homogeneous of degree `m`. -/
theorem linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants (m : ℕ) :
    Subalgebra.toSubmodule (linearInvariants H) ⊓ homogeneousSubmodule K H m ≤
      (Subalgebra.toSubmodule (lieInvariants K L L) ⊓ homogeneousSubmodule K L m).map
        (lieCartanRestriction H).toLinearMap := by
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  rw [← span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule b m,
    Submodule.span_le]
  rintro _ ⟨lam, hlam, rfl⟩
  have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  -- the power sum of the weights of `L(λ)` is the restriction of `x ↦ tr (ρ_λ(x) ^ m)`
  refine ⟨(killingSymmetricEquiv K L).symm
    (tracePowerPolynomial K L (irreducibleQuotient b lam) m), ⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, ← killingSymmetricEquiv_mem_lieInvariants_iff,
      AlgEquiv.apply_symm_apply]
    exact tracePowerPolynomial_mem_lieInvariants m
  · rw [killingSymmetricEquiv_symm, _root_.SymmetricAlgebra.mapEquiv_apply]
    exact map_mem_homogeneousSubmodule _ (tracePowerPolynomial_mem_homogeneousSubmodule m)
  · rw [AlgHom.toLinearMap_apply,
      lieCartanRestriction_killingSymmetricEquiv_symm_tracePowerPolynomial,
      highestWeightTracePowerRestriction_def]

/-- **Chevalley's restriction theorem, image form.** Restriction to `H` maps the invariants
`S(L)^L` onto the Weyl invariants `S(H)^W`. -/
theorem map_lieInvariants_lieCartanRestriction :
    (lieInvariants K L L).map (lieCartanRestriction H) = linearInvariants H := by
  classical
  refine le_antisymm (Subalgebra.map_le.mpr fun p hp ↦ lieCartanRestriction_mem_linearInvariants hp)
    fun q hq ↦ ?_
  -- the Weyl invariants are graded, so `q` is the sum of its homogeneous Weyl-invariant components
  have hhom : DirectSum.SetLike.IsHomogeneous (homogeneousSubmodule K H) (linearInvariants H) :=
    linearInvariants_eq_symmetricAlgebraInvariants (H := H) ▸
      Representation.isHomogeneous_symmetricAlgebraInvariants _
  rw [← DirectSum.sum_support_decompose (homogeneousSubmodule K H) q]
  refine Subalgebra.sum_mem _ fun m _ ↦ ?_
  obtain ⟨p, ⟨hp, -⟩, hpq⟩ := linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants H m
    ⟨hhom m hq, SetLike.coe_mem _⟩
  exact ⟨p, hp, hpq⟩

/-- **Chevalley's restriction theorem.** Restriction of polynomial functions from `L` to `H`,
`TauCeti.lieCartanRestriction H`, is an isomorphism from the invariants `S(L)^L` onto the Weyl
invariants `S(H)^W`. -/
noncomputable def lieChevalleyRestrictionIso : lieInvariants K L L ≃ₐ[K] linearInvariants H :=
  AlgEquiv.ofBijective
    (((lieCartanRestriction H).comp (lieInvariants K L L).val).codRestrict (linearInvariants H)
      fun p ↦ lieCartanRestriction_mem_linearInvariants p.2)
    ⟨fun p q hpq ↦ Subtype.ext <| lieCartanRestriction_injOn_lieInvariants H p.2 q.2
        (congrArg Subtype.val hpq),
      fun q ↦ by
        obtain ⟨p, hp, hpq⟩ := (map_lieInvariants_lieCartanRestriction H).ge q.2
        exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩⟩

/-- The Chevalley isomorphism is restriction to `H`. -/
@[simp]
theorem coe_lieChevalleyRestrictionIso_apply (p : lieInvariants K L L) :
    (lieChevalleyRestrictionIso H p : _root_.SymmetricAlgebra K H) = lieCartanRestriction H p :=
  (rfl)

/-- The inverse of the Chevalley isomorphism sends a Weyl invariant to the invariant restricting
to it. -/
@[simp]
theorem lieCartanRestriction_lieChevalleyRestrictionIso_symm_apply (q : linearInvariants H) :
    lieCartanRestriction H ((lieChevalleyRestrictionIso H).symm q : _root_.SymmetricAlgebra K L) =
      q := by
  rw [← coe_lieChevalleyRestrictionIso_apply, AlgEquiv.apply_symm_apply]

/-- **The Chevalley isomorphism preserves degrees**: an invariant is homogeneous of degree `m`
exactly when its restriction to `H` is. -/
theorem lieChevalleyRestrictionIso_mem_homogeneousSubmodule_iff {p : lieInvariants K L L}
    {m : ℕ} :
    (lieChevalleyRestrictionIso H p : _root_.SymmetricAlgebra K H) ∈ homogeneousSubmodule K H m ↔
      (p : _root_.SymmetricAlgebra K L) ∈ homogeneousSubmodule K L m := by
  rw [coe_lieChevalleyRestrictionIso_apply]
  refine ⟨fun hq ↦ ?_, lieCartanRestriction_mem_homogeneousSubmodule H⟩
  obtain ⟨p', ⟨hp', hp'm⟩, hpq⟩ := linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants
    H m ⟨lieCartanRestriction_mem_linearInvariants p.2, hq⟩
  rwa [← lieCartanRestriction_injOn_lieInvariants H hp' p.2 hpq]

end Surjective

end LieSubalgebra
