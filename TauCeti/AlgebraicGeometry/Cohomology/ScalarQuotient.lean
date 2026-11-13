/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Modules.ScalarQuotient
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Cohomology of quotients by powers of a global function

For a sheaf of modules `M` and a global function `f`, the cokernel `M/fⁿM` and its reduction
maps are defined in `Modules.ScalarQuotient`. When multiplication by `f` on `M` is a
monomorphism, the coefficient sequence gives connecting maps
`Hⁱ(X, M/fⁿM) → Hⁱ⁺¹(X, M)`.
Their kernels are the images of `Hⁱ(X, M)` and their images are exactly the classes killed by
`fⁿ`. Reduction from exponent `n` to exponent `m ≤ n` multiplies the connecting class by
`f ^ (n - m)`, rather than leaving it unchanged.

These equations identify the obstruction to lifting sections of the infinitesimal quotients
with a scalar-multiplication inverse system in first cohomology. This is the cohomological
input to comparison of sections with formal sections. No coherence, Noetherianity, or
acyclicity assumption is needed. If a power of `f` annihilates the `f`-power torsion in the
next cohomology group, every member of a compatible family of quotient classes lifts to a
class on `M`; these lifts are not asserted to be compatible.

## References

* The Stacks Project, Lemma 52.12.7, Tag 0EII (formal-section comparison).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤))
variable [Mono (M.globalSectionsSmul f)]

/-- The connecting map for `0 → M → M → M/fⁿM → 0`, linear over global functions. -/
def scalarPowerδ (n i : ℕ) :
    Cohomology (M.scalarPowerQuotient f n) i →ₗ[Γ(X, ⊤)] Cohomology M (i + 1) :=
  cohomologyδLinear (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n)))
    i (i + 1) rfl

/-- The boundary is the connecting map of the coefficient short exact sequence. -/
lemma scalarPowerδ_apply (n i : ℕ)
    (x : Cohomology (M.scalarPowerQuotient f n) i) :
    M.scalarPowerδ f n i x =
      cohomologyδ (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n)))
        i (i + 1) rfl x := by
  exact cohomologyδLinear_apply
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n))) i (i + 1) rfl x

/-- The kernel of reduction to `M/fⁿM` on cohomology is the image of multiplication by `fⁿ`. -/
theorem exact_smul_cohomologyMapLinear (n i : ℕ) :
    Function.Exact (f ^ n • LinearMap.id : Cohomology M i →ₗ[Γ(X, ⊤)] Cohomology M i)
      (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ n))) i) := by
  have hs : ⇑(f ^ n • (LinearMap.id : Cohomology M i →ₗ[Γ(X, ⊤)] _)) =
      ⇑(cohomologyMap (M.globalSectionsSmul (f ^ n)) i) :=
    funext fun x ↦ (cohomologyMap_globalSectionsSmul_apply M i (f ^ n) x).symm
  rw [hs, coe_cohomologyMapLinear]
  exact exact_cohomologyMap_cohomologyMap
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n))) i

/-- A class on `M/fⁿM` has zero boundary exactly when it lifts to a class on `M`. -/
theorem exact_cohomologyMapLinear_scalarPowerδ (n i : ℕ) :
    Function.Exact (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ n))) i)
      (M.scalarPowerδ f n i) := by
  rw [coe_cohomologyMapLinear]
  have hδ := funext (M.scalarPowerδ_apply f n i)
  rw [hδ]
  exact exact_cohomologyMap_cohomologyδ
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n))) i (i + 1) rfl

/-- The image of the connecting map consists exactly of the classes annihilated by `fⁿ`. -/
theorem exact_scalarPowerδ_smul (n i : ℕ) :
    Function.Exact (M.scalarPowerδ f n i)
      (f ^ n • LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] Cohomology M (i + 1)) := by
  have hδ := funext (M.scalarPowerδ_apply f n i)
  have hs : ⇑(f ^ n • (LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] _)) =
      ⇑(cohomologyMap (M.globalSectionsSmul (f ^ n)) (i + 1)) :=
    funext fun x ↦ (cohomologyMap_globalSectionsSmul_apply M (i + 1) (f ^ n) x).symm
  rw [hδ, hs]
  exact exact_cohomologyδ_cohomologyMap
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n))) i (i + 1) rfl

/-- Under reduction from exponent `n` to `m`, the boundary is multiplied by `f ^ (n - m)`. -/
theorem scalarPowerδ_transition {m n : ℕ} (h : m ≤ n) (i : ℕ)
    (x : Cohomology (M.scalarPowerQuotient f n) i) :
    M.scalarPowerδ f m i
        (cohomologyMapLinear (M.scalarPowerQuotientTransition f h) i x) =
      f ^ (n - m) • M.scalarPowerδ f n i x := by
  rw [coe_cohomologyMapLinear, scalarPowerδ_apply, scalarPowerδ_apply]
  have hδ := cohomologyδ_naturality
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ n)))
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul (f ^ m)))
    (M.scalarPowerQuotientSequenceMap f h) i (i + 1) rfl x
  simp only [scalarPowerQuotientSequenceMap_τ₁, scalarPowerQuotientSequenceMap_τ₃] at hδ
  exact hδ.symm.trans
    (cohomologyMap_globalSectionsSmul_apply M (i + 1) (f ^ (n - m)) _)

/-- A class at level `n` lifts after reduction to level `m` if `f ^ (n - m)` kills the
`fⁿ`-torsion in the next cohomology group. -/
theorem exists_cohomologyMapLinear_eq_of_pow_smul_eq_zero {m n : ℕ} (h : m ≤ n)
    (i : ℕ) (x : Cohomology (M.scalarPowerQuotient f n) i)
    (hk : ∀ y : Cohomology M (i + 1), f ^ n • y = 0 → f ^ (n - m) • y = 0) :
    ∃ y : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ m))) i y =
        cohomologyMapLinear (M.scalarPowerQuotientTransition f h) i x := by
  apply (M.exact_cohomologyMapLinear_scalarPowerδ f m i _).mp
  rw [M.scalarPowerδ_transition f h i x]
  apply hk
  exact (M.exact_scalarPowerδ_smul f n i _).mpr ⟨x, rfl⟩

/-- If a power of `f` annihilates the `f`-power torsion in the next cohomology group, every
class in a compatible quotient family lifts at each level. The lifts need not be compatible. -/
theorem exists_cohomologyMapLinear_eq_of_scalarPowerQuotientTransition_of_pow_smul_eq_zero
    (i : ℕ) (x : ∀ n, Cohomology (M.scalarPowerQuotient f n) i)
    (hx : ∀ n, cohomologyMapLinear (M.scalarPowerQuotientTransition f n.le_succ) i
      (x (n + 1)) = x n)
    {k : ℕ} (hk : ∀ m (y : Cohomology M (i + 1)), f ^ m • y = 0 → f ^ k • y = 0)
    (n : ℕ) :
    ∃ y : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ n))) i y = x n := by
  have hiter (m n : ℕ) (h : m ≤ n) :
      cohomologyMapLinear (M.scalarPowerQuotientTransition f h) i (x n) = x m := by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n h ih =>
      rw [← M.scalarPowerQuotientTransition_comp f (Nat.le_succ n) h,
        cohomologyMapLinear_comp, LinearMap.comp_apply, hx, ih]
  have hk' : ∀ y : Cohomology M (i + 1),
      f ^ (n + k) • y = 0 → f ^ (n + k - n) • y = 0 := by
    simpa only [Nat.add_sub_cancel_left] using hk (n + k)
  simpa only [hiter] using
    M.exists_cohomologyMapLinear_eq_of_pow_smul_eq_zero f (Nat.le_add_right n k) i
      (x (n + k)) hk'

end AlgebraicGeometry.Scheme.Modules
