/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-!
# Cohomology of quotients by powers of a global function

For a sheaf of modules `M` and a global function `f`, this file constructs the cokernel
`M/fⁿM` and its reduction maps. When multiplication by `f` on `M` is a monomorphism, the
coefficient sequence gives connecting maps
`Hⁱ(X, M/fⁿM) → Hⁱ⁺¹(X, M)`.
Their kernels are the images of `Hⁱ(X, M)` and their images are exactly the classes killed by
`fⁿ`. Reduction from exponent `n + 1` to exponent `n` multiplies the connecting class by `f`,
rather than leaving it unchanged.

These equations identify the obstruction to lifting sections of the infinitesimal quotients
with a scalar-multiplication inverse system in first cohomology. This is the cohomological
input to comparison of sections with formal sections. No coherence, Noetherianity, or
acyclicity assumption is needed. If a power of `f` annihilates the next cohomology group,
every member of a compatible family of quotient classes lifts to a class on `M`; these lifts
are not asserted to be compatible.

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

/-- The sheaf quotient `M/fⁿM`, computed as the cokernel of multiplication by `fⁿ`. -/
abbrev scalarPowerQuotient (n : ℕ) : X.Modules :=
  cokernel (M.globalSectionsSmul (f ^ n))

/-- The canonical reduction `M/fⁿ⁺¹M → M/fⁿM`. -/
def scalarPowerQuotientTransition (n : ℕ) :
    M.scalarPowerQuotient f (n + 1) ⟶ M.scalarPowerQuotient f n :=
  cokernel.desc _ (cokernel.π (M.globalSectionsSmul (f ^ n))) (by
    rw [pow_succ, globalSectionsSmul_mul, Category.assoc, cokernel.condition,
      comp_zero])

/-- Reduction commutes with the quotient projections. -/
@[reassoc (attr := simp)]
lemma scalarPowerQuotientTransition_π (n : ℕ) :
    cokernel.π (M.globalSectionsSmul (f ^ (n + 1))) ≫
        M.scalarPowerQuotientTransition f n =
      cokernel.π (M.globalSectionsSmul (f ^ n)) :=
  cokernel.π_desc _ _ _

/-- Reduction of quotient sheaves is induced by multiplication by `f` on the left
coefficient and the identity on the middle coefficient. -/
private def scalarPowerQuotientSequenceMap (n : ℕ) :
    ShortComplex.cokernelSequence (M.globalSectionsSmul (f ^ (n + 1))) ⟶
      ShortComplex.cokernelSequence (M.globalSectionsSmul (f ^ n)) where
  τ₁ := M.globalSectionsSmul f
  τ₂ := 𝟙 M
  τ₃ := M.scalarPowerQuotientTransition f n
  comm₁₂ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.comp_id, pow_succ, globalSectionsSmul_mul]
  comm₂₃ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.id_comp, scalarPowerQuotientTransition_π]

/-- Regularity of `f` on the sheaf makes each coefficient sequence short exact. -/
theorem scalarPowerQuotient_shortExact [Mono (M.globalSectionsSmul f)] (n : ℕ) :
    (ShortComplex.cokernelSequence (M.globalSectionsSmul (f ^ n))).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (inferInstance : Mono (M.globalSectionsSmul (f ^ n))) inferInstance

variable [Mono (M.globalSectionsSmul f)]

/-- The connecting map for `0 → M → M → M/fⁿM → 0`, linear over global functions. -/
def scalarPowerδ (n i : ℕ) :
    Cohomology (M.scalarPowerQuotient f n) i →ₗ[Γ(X, ⊤)] Cohomology M (i + 1) :=
  cohomologyδLinear (M.scalarPowerQuotient_shortExact f n) i (i + 1) rfl

/-- The boundary is the connecting map of the coefficient short exact sequence. -/
lemma scalarPowerδ_apply (n i : ℕ)
    (x : Cohomology (M.scalarPowerQuotient f n) i) :
    M.scalarPowerδ f n i x =
      cohomologyδ (M.scalarPowerQuotient_shortExact f n) i (i + 1) rfl x := by
  exact cohomologyδLinear_apply (M.scalarPowerQuotient_shortExact f n) i (i + 1) rfl x

/-- A class on `M/fⁿM` has zero boundary exactly when it lifts to a class on `M`. -/
theorem exact_cohomologyMapLinear_scalarPowerδ (n i : ℕ) :
    Function.Exact (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ n))) i)
      (M.scalarPowerδ f n i) := by
  rw [coe_cohomologyMapLinear]
  have hδ := funext (M.scalarPowerδ_apply f n i)
  rw [hδ]
  exact exact_cohomologyMap_cohomologyδ (M.scalarPowerQuotient_shortExact f n)
    i (i + 1) rfl

/-- The image of the connecting map consists exactly of the classes annihilated by `fⁿ`. -/
theorem exact_scalarPowerδ_smul (n i : ℕ) :
    Function.Exact (M.scalarPowerδ f n i)
      (f ^ n • LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] Cohomology M (i + 1)) := by
  have hδ := funext (M.scalarPowerδ_apply f n i)
  have hs : ⇑(f ^ n • (LinearMap.id : Cohomology M (i + 1) →ₗ[Γ(X, ⊤)] _)) =
      ⇑(cohomologyMap (M.globalSectionsSmul (f ^ n)) (i + 1)) :=
    funext fun x ↦ (cohomologyMap_globalSectionsSmul_apply M (i + 1) (f ^ n) x).symm
  rw [hδ, hs]
  exact exact_cohomologyδ_cohomologyMap (M.scalarPowerQuotient_shortExact f n)
    i (i + 1) rfl

/-- Under reduction of the quotient exponent, the boundary class is multiplied by `f`. -/
theorem scalarPowerδ_transition (n i : ℕ)
    (x : Cohomology (M.scalarPowerQuotient f (n + 1)) i) :
    M.scalarPowerδ f n i
        (cohomologyMapLinear (M.scalarPowerQuotientTransition f n) i x) =
      f • M.scalarPowerδ f (n + 1) i x := by
  rw [coe_cohomologyMapLinear, scalarPowerδ_apply, scalarPowerδ_apply]
  exact (cohomologyδ_naturality (M.scalarPowerQuotient_shortExact f (n + 1))
    (M.scalarPowerQuotient_shortExact f n)
    (M.scalarPowerQuotientSequenceMap f n) i (i + 1) rfl x).symm.trans
      (cohomologyMap_globalSectionsSmul_apply M (i + 1) f _)

/-- If a power of `f` annihilates the next cohomology group, every class in a compatible
family on the quotients lifts at each finite level. This does not choose compatible lifts. -/
theorem exists_cohomology_lift_of_scalarPowerQuotient_compatible (i : ℕ)
    (x : ∀ n, Cohomology (M.scalarPowerQuotient f n) i)
    (hx : ∀ n, cohomologyMapLinear (M.scalarPowerQuotientTransition f n) i (x (n + 1)) = x n)
    {k : ℕ} (hk : ∀ y : Cohomology M (i + 1), f ^ k • y = 0) (n : ℕ) :
    ∃ y : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ n))) i y = x n := by
  have hstep (m : ℕ) : M.scalarPowerδ f m i (x m) =
      f • M.scalarPowerδ f (m + 1) i (x (m + 1)) := by
    rw [← hx m]
    exact M.scalarPowerδ_transition f m i (x (m + 1))
  have hiter (j : ℕ) : ∀ m, M.scalarPowerδ f m i (x m) =
      f ^ j • M.scalarPowerδ f (m + j) i (x (m + j)) := by
    induction j with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      rw [hstep m, ih (m + 1), smul_smul, ← pow_succ']
      have hindex : m + 1 + j = m + (j + 1) := by omega
      rw [hindex]
  have hzero : M.scalarPowerδ f n i (x n) = 0 := (hiter k n).trans (hk _)
  exact (M.exact_cohomologyMapLinear_scalarPowerδ f n i (x n)).mp hzero

end AlgebraicGeometry.Scheme.Modules
