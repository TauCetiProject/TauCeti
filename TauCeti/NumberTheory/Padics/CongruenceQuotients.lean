/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import Mathlib.Topology.Separation.DisjointCover
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# The congruence quotients of `ℤ_pˣ` and functions factoring through them

Truncation modulo `p ^ n` on units, `PadicInt.unitsToZModPow n : ℤ_pˣ → (ℤ/p^nℤ)ˣ`, is a
surjective continuous homomorphism with kernel the principal unit group `U^(n) = 1 + p^n ℤ_p`,
and these kernels form a neighbourhood basis of `1`. This file records the consequences that make
the finite groups `(ℤ/p^nℤ)ˣ` a complete system of finite coordinates for `ℤ_pˣ`:

* the quotient `ℤ_pˣ ⧸ U^(n)` is identified with `(ℤ/p^nℤ)ˣ`
  (`TauCeti.unitToZModPowQuotient`), so two units have the same truncation modulo `p ^ n`
  exactly when they lie in the same coset of `U^(n)` (`TauCeti.unitsToZModPow_eq_iff`);
* a function on `ℤ_pˣ` factors through truncation modulo `p ^ n` exactly when it is invariant
  under translation by `U^(n)` (`TauCeti.exists_comp_unitsToZModPow_eq_iff`), and a factorisation
  at level `n` refines to every deeper level;
* every locally constant function on `ℤ_pˣ`, with values in any type, factors through
  truncation modulo `p ^ n` for some `n` (`IsLocallyConstant.exists_comp_unitsToZModPow_eq`),
  and a locally constant homomorphism does so through a homomorphism
  (`IsLocallyConstant.exists_monoidHom_comp_unitsToZModPow_eq`);
* the *cylinder functions* `g ∘ unitsToZModPow n` are dense in `C(ℤ_pˣ, R)` for every uniform
  space `R` (`TauCeti.dense_setOf_comp_unitsToZModPow`).

The factor of a function through the surjection `unitsToZModPow n` is unique
(`Function.Surjective.injective_comp_right` applied to `PadicInt.unitsToZModPow_surjective`,
or `MonoidHom.cancel_right` for homomorphisms).

These are the statements that let one integrate against a measure on `ℤ_pˣ` through its images
on the finite groups `(ℤ/p^nℤ)ˣ`: a test function that is locally constant is a finite sum over
some `(ℤ/p^nℤ)ˣ`, and such test functions are dense among all continuous ones.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Ann. Math. Qué.
  (2024), Definitions 3.7–3.8, Remarks 3.11–3.12 and Proposition 3.16.
-/

public section

open Filter Topology

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The quotient `ℤ_pˣ ⧸ U^(n)` -/

variable (p) in
/-- The **congruence quotient** `ℤ_pˣ ⧸ U^(n) ≃* (ℤ/p^nℤ)ˣ`, induced by the surjective
truncation `PadicInt.unitsToZModPow n`, whose kernel is the principal unit group `U^(n)`. -/
noncomputable def unitToZModPowQuotient (n : ℕ) :
    ℤ_[p]ˣ ⧸ unitsPrincipal p n ≃* (ZMod (p ^ n))ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitsToZModPow p n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (PadicInt.unitsToZModPow_surjective n))

/-- The congruence quotient sends the coset of `u` to the truncation of `u` modulo `p ^ n`. -/
@[simp]
theorem unitToZModPowQuotient_mk (n : ℕ) (u : ℤ_[p]ˣ) :
    unitToZModPowQuotient p n (u : ℤ_[p]ˣ ⧸ unitsPrincipal p n) =
      PadicInt.unitsToZModPow n u :=
  (rfl)

/-- The congruence quotient is the native first-isomorphism-theorem equivalence for truncation,
after identifying its kernel with the principal unit group. -/
theorem unitToZModPowQuotient_def (n : ℕ) :
    unitToZModPowQuotient p n =
      (QuotientGroup.quotientMulEquivOfEq (ker_unitsToZModPow p n).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _
          (PadicInt.unitsToZModPow_surjective n)) :=
  (rfl)

/-- The inverse of the congruence quotient sends the truncation of `u` modulo `p ^ n` to the coset
of `u`. -/
@[simp]
theorem unitToZModPowQuotient_symm_apply (n : ℕ) (u : ℤ_[p]ˣ) :
    (unitToZModPowQuotient p n).symm (PadicInt.unitsToZModPow n u) =
      (u : ℤ_[p]ˣ ⧸ unitsPrincipal p n) := by
  rw [MulEquiv.symm_apply_eq, unitToZModPowQuotient_mk]

/-- Two units have the same truncation modulo `p ^ n` exactly when they differ by an element of
`U^(n)`. -/
theorem unitsToZModPow_eq_iff {n : ℕ} {u v : ℤ_[p]ˣ} :
    PadicInt.unitsToZModPow n u = PadicInt.unitsToZModPow n v ↔ u⁻¹ * v ∈ unitsPrincipal p n := by
  rw [← unitToZModPowQuotient_mk, ← unitToZModPowQuotient_mk, EquivLike.apply_eq_iff_eq,
    QuotientGroup.eq]

/-! ### Functions factoring through a congruence quotient -/

variable {A : Type*}

/-- A function on `ℤ_pˣ` factors through truncation modulo `p ^ n` exactly when it is invariant
under right translation by the principal unit group `U^(n)`. -/
theorem exists_comp_unitsToZModPow_eq_iff {n : ℕ} {f : ℤ_[p]ˣ → A} :
    (∃ g : (ZMod (p ^ n))ˣ → A, g ∘ PadicInt.unitsToZModPow n = f) ↔
      ∀ u, ∀ k ∈ unitsPrincipal p n, f (u * k) = f u := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨g, rfl⟩ u k hk
    simp [unitsToZModPow_eq_one_iff.mpr hk]
  · have : Nonempty A := ⟨f 1⟩
    obtain ⟨g, hg⟩ := (Function.factorsThrough_iff f).mp fun u v huv ↦ by
      rw [← hf u (u⁻¹ * v) (unitsToZModPow_eq_iff.mp huv), mul_inv_cancel_left]
    exact ⟨g, hg.symm⟩

/-- A function that factors through truncation modulo `p ^ n` also factors through truncation
modulo `p ^ m` for every `m ≥ n`. -/
theorem exists_comp_unitsToZModPow_eq_of_le {n m : ℕ} (hnm : n ≤ m) {f : ℤ_[p]ˣ → A}
    (hf : ∃ g : (ZMod (p ^ n))ˣ → A, g ∘ PadicInt.unitsToZModPow n = f) :
    ∃ g : (ZMod (p ^ m))ˣ → A, g ∘ PadicInt.unitsToZModPow m = f := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨g ∘ ZMod.unitsMap (pow_dvd_pow p hnm), by
    ext u; simp⟩

end TauCeti

namespace IsLocallyConstant

open TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*}

/-- **Descent of locally constant functions on `ℤ_pˣ`.** Every locally constant function on
`ℤ_pˣ`, with values in any type, factors through truncation modulo `p ^ n` for some `n`. This
applies in particular to every continuous map to a discrete space, by
`IsLocallyConstant.iff_continuous`. -/
theorem exists_comp_unitsToZModPow_eq {f : ℤ_[p]ˣ → A} (hf : IsLocallyConstant f) :
    ∃ n, ∃ g : (ZMod (p ^ n))ˣ → A, g ∘ PadicInt.unitsToZModPow n = f := by
  -- The right-translation stabilizer of `f` is open, so it contains some `U^(n)`.
  obtain ⟨n, hn⟩ := exists_unitsPrincipal_le_of_isOpen (isOpen_rightTranslationStabilizer hf)
  exact ⟨n, exists_comp_unitsToZModPow_eq_iff.mpr fun u k hk ↦
    mem_rightTranslationStabilizer.mp (hn hk) u⟩

/-- Every locally constant homomorphism from `ℤ_pˣ` to a monoid factors through truncation
modulo `p ^ n`, for some `n`, by a homomorphism. This applies in particular to every continuous
homomorphism to a discrete monoid, by `IsLocallyConstant.iff_continuous`. -/
theorem exists_monoidHom_comp_unitsToZModPow_eq [Monoid A] {q : ℤ_[p]ˣ →* A}
    (hq : IsLocallyConstant q) :
    ∃ n, ∃ t : (ZMod (p ^ n))ˣ →* A,
      t.comp (PadicInt.unitsToZModPow n).toMonoidHom = q := by
  obtain ⟨n, hn⟩ := exists_unitsPrincipal_le_of_isOpen (isOpen_rightTranslationStabilizer hq)
  have hker : unitsPrincipal p n ≤ q.ker := fun k hk ↦ by
    simpa using mem_rightTranslationStabilizer.mp (hn hk) 1
  refine ⟨n, (QuotientGroup.lift _ q hker).comp (unitToZModPowQuotient p n).symm.toMonoidHom, ?_⟩
  ext u
  simp

end IsLocallyConstant

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*}

/-- A function on `ℤ_pˣ` is locally constant exactly when it factors through truncation modulo
`p ^ n` for some `n`. -/
theorem isLocallyConstant_iff_exists_comp_unitsToZModPow_eq {f : ℤ_[p]ˣ → A} :
    IsLocallyConstant f ↔ ∃ n, ∃ g : (ZMod (p ^ n))ˣ → A, g ∘ PadicInt.unitsToZModPow n = f := by
  refine ⟨IsLocallyConstant.exists_comp_unitsToZModPow_eq, ?_⟩
  rintro ⟨n, g, rfl⟩
  exact (IsLocallyConstant.of_discrete g).comp_continuous (PadicInt.unitsToZModPow n).continuous

/-- **Density of cylinder functions.** The continuous functions on `ℤ_pˣ` that factor through
truncation modulo `p ^ n` for some `n` are dense in `C(ℤ_pˣ, R)` for every uniform space `R`. -/
theorem dense_setOf_comp_unitsToZModPow (R : Type*) [UniformSpace R] :
    Dense {F : C(ℤ_[p]ˣ, R) |
      ∃ n, ∃ g : (ZMod (p ^ n))ˣ → R, g ∘ PadicInt.unitsToZModPow n = F} := by
  refine fun f ↦ (mem_closure_iff_nhds_basis
    (nhds_basis_uniformity' ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact)).mpr
    fun V hV ↦ ?_
  -- Approximate `f` within `V` by a function factoring through a finite discrete space.
  obtain ⟨N, c, h, hc, hch⟩ := ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal f
    (nhdsSet_diagonal_le_uniformity hV)
  have hloc : IsLocallyConstant (h ∘ c) :=
    (IsLocallyConstant.of_discrete h).comp_continuous hc
  exact ⟨⟨h ∘ c, hloc.continuous⟩, hloc.exists_comp_unitsToZModPow_eq, fun x ↦ hch x⟩

end TauCeti
