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
# Cohomology of quotients by global functions

For a sheaf of modules `M` and a global function `f`, the cokernel `M/fM` and its reduction
maps are defined in `Modules.ScalarQuotient`. When multiplication by `f` on `M` is a
monomorphism, the coefficient sequence gives connecting maps
`Hⁱ(X, M/fM) → Hⁱ⁺¹(X, M)`.
Their kernels are the images of `Hⁱ(X, M)` and their images are exactly the classes killed by
`f`. A factorization `g = f * c` makes reduction `M/gM → M/fM` multiply the connecting class
by `c`. In particular, reduction from exponent `n` to exponent `m ≤ n` multiplies it by
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

/-- The connecting map for `0 → M → M → M/fM → 0`, linear over global functions. -/
def scalarδ (i : ℕ) :
    Cohomology (M.scalarQuotient f) i →ₗ[Γ(X, ⊤)] Cohomology M (i + 1) :=
  cohomologyδLinear (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f))
    i (i + 1) rfl

/-- The boundary is the connecting map of the coefficient short exact sequence. -/
lemma scalarδ_apply (i : ℕ) (x : Cohomology (M.scalarQuotient f) i) :
    M.scalarδ f i x =
      cohomologyδ (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f))
        i (i + 1) rfl x := by
  exact cohomologyδLinear_apply
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f)) i (i + 1) rfl x

/-- The kernel of reduction to `M/fM` on cohomology is the image of multiplication by `f`. -/
theorem exact_smul_cohomologyMapLinear (i : ℕ) :
    Function.Exact (f • LinearMap.id : Cohomology M i →ₗ[Γ(X, ⊤)] Cohomology M i)
      (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul f)) i) := by
  have hs : ⇑(f • (LinearMap.id : Cohomology M i →ₗ[Γ(X, ⊤)] _)) =
      ⇑(cohomologyMap (M.globalSectionsSmul f) i) :=
    funext fun x ↦ (cohomologyMap_globalSectionsSmul_apply M i f x).symm
  rw [hs, coe_cohomologyMapLinear]
  exact exact_cohomologyMap_cohomologyMap
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f)) i

/-- A class on `M/fM` has zero boundary exactly when it lifts to a class on `M`. -/
theorem exact_cohomologyMapLinear_scalarδ (i : ℕ) :
    Function.Exact (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul f)) i)
      (M.scalarδ f i) := by
  rw [coe_cohomologyMapLinear]
  have hδ := funext (M.scalarδ_apply f i)
  rw [hδ]
  exact exact_cohomologyMap_cohomologyδ
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f)) i (i + 1) rfl

/-- The image of the connecting map consists exactly of the classes annihilated by `f`. -/
theorem exact_scalarδ_smul (i : ℕ) :
    Function.Exact (M.scalarδ f i)
      (f • LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] Cohomology M (i + 1)) := by
  have hδ := funext (M.scalarδ_apply f i)
  have hs : ⇑(f • (LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] _)) =
      ⇑(cohomologyMap (M.globalSectionsSmul f) (i + 1)) :=
    funext fun x ↦ (cohomologyMap_globalSectionsSmul_apply M (i + 1) f x).symm
  rw [hδ, hs]
  exact exact_cohomologyδ_cohomologyMap
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f)) i (i + 1) rfl

variable {f} {g c : Γ(X, ⊤)} [Mono (M.globalSectionsSmul g)]

/-- Under reduction from `M/gM` to `M/fM` for `g = f * c`, the boundary is multiplied by `c`. -/
theorem scalarδ_transition (h : g = f * c) (i : ℕ)
    (x : Cohomology (M.scalarQuotient g) i) :
    M.scalarδ f i (cohomologyMapLinear (M.scalarQuotientTransition ⟨c, h⟩) i x) =
      c • M.scalarδ g i x := by
  rw [coe_cohomologyMapLinear, scalarδ_apply, scalarδ_apply]
  have hδ := cohomologyδ_naturality
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul g))
    (TauCeti.cokernelSequence_shortExact (M.globalSectionsSmul f))
    (M.scalarQuotientSequenceMap h) i (i + 1) rfl x
  simp only [scalarQuotientSequenceMap_τ₁, scalarQuotientSequenceMap_τ₃] at hδ
  exact hδ.symm.trans (cohomologyMap_globalSectionsSmul_apply M (i + 1) c _)

/-- A class on `M/gM` lifts after reduction to `M/fM` if the factor `c` kills the
`g`-torsion in the next cohomology group. -/
theorem exists_cohomologyMapLinear_eq_of_smul_eq_zero (h : g = f * c)
    (i : ℕ) (x : Cohomology (M.scalarQuotient g) i)
    (hk : ∀ y : Cohomology M (i + 1), g • y = 0 → c • y = 0) :
    ∃ y : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul f)) i y =
        cohomologyMapLinear (M.scalarQuotientTransition ⟨c, h⟩) i x := by
  apply (M.exact_cohomologyMapLinear_scalarδ f i _).mp
  rw [M.scalarδ_transition h i x]
  apply hk
  exact (M.exact_scalarδ_smul g i _).mpr ⟨x, rfl⟩

variable (f)

/-- Under reduction from exponent `n` to `m`, the boundary is multiplied by `f ^ (n - m)`. -/
theorem scalarδ_scalarPowerQuotientTransition {m n : ℕ} (h : m ≤ n) (i : ℕ)
    (x : Cohomology (M.scalarPowerQuotient f n) i) :
    M.scalarδ (f ^ m) i
        (cohomologyMapLinear (M.scalarPowerQuotientTransition f h) i x) =
      f ^ (n - m) • M.scalarδ (f ^ n) i x :=
  M.scalarδ_transition (by rw [← pow_add, Nat.add_sub_of_le h]) i x

/-- A class at level `n` lifts after reduction to level `m` if `f ^ (n - m)` kills the
`fⁿ`-torsion in the next cohomology group. -/
theorem exists_cohomologyMapLinear_eq_of_pow_smul_eq_zero {m n : ℕ} (h : m ≤ n)
    (i : ℕ) (x : Cohomology (M.scalarPowerQuotient f n) i)
    (hk : ∀ y : Cohomology M (i + 1), f ^ n • y = 0 → f ^ (n - m) • y = 0) :
    ∃ y : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ m))) i y =
        cohomologyMapLinear (M.scalarPowerQuotientTransition f h) i x :=
  M.exists_cohomologyMapLinear_eq_of_smul_eq_zero
    (by rw [← pow_add, Nat.add_sub_of_le h]) i x hk

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
      dsimp only [scalarPowerQuotientTransition]
      rw [← M.scalarQuotientTransition_comp (pow_dvd_pow f (Nat.le_succ n))
        (pow_dvd_pow f h), cohomologyMapLinear_comp, LinearMap.comp_apply, hx, ih]
  have hk' : ∀ y : Cohomology M (i + 1),
      f ^ (n + k) • y = 0 → f ^ (n + k - n) • y = 0 := by
    simpa only [Nat.add_sub_cancel_left] using hk (n + k)
  simpa only [hiter] using
    M.exists_cohomologyMapLinear_eq_of_pow_smul_eq_zero f (Nat.le_add_right n k) i
      (x (n + k)) hk'

end AlgebraicGeometry.Scheme.Modules
