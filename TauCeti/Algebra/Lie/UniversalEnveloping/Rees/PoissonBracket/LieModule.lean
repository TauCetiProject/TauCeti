/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule

/-!
# Lie-module action, invariants, and grading for the zero-fibre Poisson bracket

Relates the zero-fibre Poisson bracket `reesZeroFiberBracket R L` on `SymmetricAlgebra R L` to the
adjoint Lie-module action `TauCeti.SymmetricAlgebra.lieModuleDerivation`, identifies its Poisson
centre with `TauCeti.SymmetricAlgebra.lieInvariants R L L`, shows that central elements of
`reesAlgebra R L` specialize to Lie invariants, and proves degree `-1` homogeneity.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_ι_left`,
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_ι_right`: bracketing with a generator
  agrees up to sign with `TauCeti.SymmetricAlgebra.lieModuleDerivation`.
* `TauCeti.UniversalEnvelopingAlgebra.forall_reesZeroFiberBracket_eq_zero_iff_mem_lieInvariants`:
  the Poisson centre of `reesZeroFiberBracket R L` equals `lieInvariants R L L`.
* `TauCeti.UniversalEnvelopingAlgebra.reesSpecializationZero_mem_lieInvariants_of_mem_center`:
  central Rees elements specialize to Lie invariants.
* `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_mem_homogeneousSubmodule`: degree `-1`
  homogeneity of `reesZeroFiberBracket R L`.

## References

* J. Dixmier, *Enveloping Algebras*, Graduate Studies in Mathematics 11, AMS (1996), §§2.3–2.4, for
  filtered enveloping algebras, their Rees algebras, and Lie invariants in the symmetric algebra.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

section LieModule

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] [Module.Free R L]

/-- Bracketing on the left with a generator `ι x` agrees with the adjoint Lie-module derivation
`⁅x, q⁆` of `TauCeti.SymmetricAlgebra.lieModuleDerivation`. -/
theorem reesZeroFiberBracket_ι_left (x : L) (q : SymmetricAlgebra R L) :
    reesZeroFiberBracket R L (SymmetricAlgebra.ι R L x) q = ⁅x, q⁆ := by
  rw [← reesZeroFiberDerivation_apply, TauCeti.SymmetricAlgebra.lie_eq_lieModuleDerivation]
  exact Derivation.congr_fun (SymmetricAlgebra.derivation_ext fun y ↦ by simp) q

/-- Bracketing on the right with a generator `ι y` is `-⁅y, p⁆`. -/
theorem reesZeroFiberBracket_ι_right (p : SymmetricAlgebra R L) (y : L) :
    reesZeroFiberBracket R L p (SymmetricAlgebra.ι R L y) = -⁅y, p⁆ := by
  rw [reesZeroFiberBracket_swap, reesZeroFiberBracket_ι_left]

/-- **Poisson centre equals Lie invariants.** An element of `SymmetricAlgebra R L` Poisson-commutes
with all of `SymmetricAlgebra R L` if and only if it belongs to
`TauCeti.SymmetricAlgebra.lieInvariants R L L`. -/
theorem forall_reesZeroFiberBracket_eq_zero_iff_mem_lieInvariants {p : SymmetricAlgebra R L} :
    (∀ q : SymmetricAlgebra R L, reesZeroFiberBracket R L p q = 0) ↔
      p ∈ TauCeti.SymmetricAlgebra.lieInvariants R L L := by
  rw [TauCeti.SymmetricAlgebra.mem_lieInvariants]
  refine ⟨fun h x ↦ ?_, fun hp q ↦ ?_⟩
  · have hx := h (SymmetricAlgebra.ι R L x)
    rw [reesZeroFiberBracket_ι_right, neg_eq_zero,
      TauCeti.SymmetricAlgebra.lie_eq_lieModuleDerivation] at hx
    exact hx
  · rw [← reesZeroFiberDerivation_apply]
    simpa using Derivation.congr_fun (SymmetricAlgebra.derivation_ext
      (D₁ := reesZeroFiberDerivation R L p) (D₂ := 0) fun x ↦ by
        simp [reesZeroFiberBracket_ι_right, hp x]) q

/-- Every central element of `reesAlgebra R L` specializes to a Lie-invariant (Poisson-central)
element of `SymmetricAlgebra R L`. -/
theorem reesSpecializationZero_mem_lieInvariants_of_mem_center {z : reesAlgebra R L}
    (hz : z ∈ Subalgebra.center R (reesAlgebra R L)) :
    reesSpecializationZero R L z ∈ TauCeti.SymmetricAlgebra.lieInvariants R L L := by
  rw [← forall_reesZeroFiberBracket_eq_zero_iff_mem_lieInvariants]
  intro q
  obtain ⟨b, rfl⟩ := reesSpecializationZero_surjective R L q
  exact reesZeroFiberBracket_reesSpecializationZero_eq_zero_of_commute R L
    (Subalgebra.mem_center_iff.mp hz b).symm

/-- **Degree `-1` homogeneity.** The zero-fibre Poisson bracket carries degrees `(m, n)` into degree
`m + n - 1` (with `0 - 1 = 0`, where the bracket with a scalar vanishes). -/
theorem reesZeroFiberBracket_mem_homogeneousSubmodule {m n : ℕ}
    {p q : SymmetricAlgebra R L}
    (hp : p ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R L m)
    (hq : q ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R L n) :
    reesZeroFiberBracket R L p q ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R L (m + n - 1) := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add p₁ p₂ k _ _ ih₁ ih₂ =>
    rw [LinearMap.map_add₂]
    exact Submodule.add_mem _ ih₁ ih₂
  | mem_mul a ha k p' hp' ih =>
    obtain ⟨x, rfl⟩ := ha
    rw [Nat.succ_add, Nat.succ_sub_one, reesZeroFiberBracket_mul_left,
      reesZeroFiberBracket_ι_left]
    refine Submodule.add_mem _ ?_ ?_
    · rcases Nat.eq_zero_or_pos (k + n) with hkn | hkn
      · obtain ⟨-, rfl⟩ := Nat.add_eq_zero_iff.mp hkn
        obtain ⟨r, rfl⟩ : q ∈ (1 : Submodule R (SymmetricAlgebra R L)) := by
          simpa [pow_zero] using hq
        simp
      · have hdeg : 1 + (k + n - 1) = k + n := by omega
        rw [← hdeg]
        exact SetLike.mul_mem_graded
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule R L x) ih
    · rw [add_comm k n]
      exact SetLike.mul_mem_graded
        (TauCeti.SymmetricAlgebra.lieModuleDerivation_mem_homogeneousSubmodule R L L x hq) hp'

end LieModule

end TauCeti.UniversalEnvelopingAlgebra
