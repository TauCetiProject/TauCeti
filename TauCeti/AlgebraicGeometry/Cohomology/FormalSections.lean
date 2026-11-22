/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ScalarQuotient
public import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction

/-!
# Completion of cohomology and formal sections

Let `M` be a module sheaf on a scheme `X` and `f` a global function acting injectively on `M`.
If the `f`-power torsion in `Hⁱ⁺¹(X, M)` is bounded, the `f`-adic completion of `Hⁱ(X, M)` is
canonically the inverse limit of `Hⁱ(X, M/fⁿ⁺¹M)`. In degree zero this compares completion of
sections with formal sections. No finiteness, coherence or Noetherian hypothesis is needed.

The comparison is induced by the quotient projections, not by arbitrary choices of lifts.
At each finite level it is injective. Bounded torsion kills the connecting classes of a
compatible family; the resulting lifts modulo `fⁿ⁺¹` are unique, hence compatible.
This treats the case where `f` is regular on the sheaf, not reduction by parameter-power
torsion for an arbitrary sheaf, nor algebraization of formal sheaves.

## References

* The Stacks Project, Lemma 52.12.7, Tag 0EII, formal-section comparison.
* The Stacks Project, Lemma 52.3.2, Tag 0BLD, completion and cohomology.
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits hiding limMap
open TauCeti.ModuleTower
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤)) (i : ℕ)

/-- The cohomology of the infinitesimal quotients, with terms `Hⁱ(X, M/fⁿ⁺¹M)` and the
canonical reduction maps as transitions. -/
-- Reducibility lets its terms carry their cohomology module structures in the comparison API.
abbrev scalarQuotientCohomologyTower : TauCeti.ModuleTower Γ(X, ⊤) where
  obj n := ModuleCat.of Γ(X, ⊤) (Cohomology (M.scalarPowerQuotient f (n.unop + 1)) i)
  map h := ModuleCat.ofHom (cohomologyMapLinear
    (M.scalarPowerQuotientTransition f (Nat.add_le_add_right (leOfHom h.unop) 1)) i)
  map_id n := by
    simp [scalarPowerQuotientTransition, cohomologyMapLinear_id]
  map_comp g h := by
    apply ModuleCat.hom_ext
    simp [scalarPowerQuotientTransition, ← cohomologyMapLinear_comp]

/-- The terms are cohomology groups of the power quotients. -/
@[simp]
lemma scalarQuotientCohomologyTower_obj (n : ℕ) :
    (M.scalarQuotientCohomologyTower f i).obj (op n) =
      ModuleCat.of Γ(X, ⊤) (Cohomology (M.scalarPowerQuotient f (n + 1)) i) :=
  (rfl)

/-- Transitions on formal cohomology are induced by reduction of quotient sheaves. -/
lemma scalarQuotientCohomologyTower_transition (n : ℕ) :
    (M.scalarQuotientCohomologyTower f i).transition n =
      cohomologyMapLinear (M.scalarPowerQuotientTransition f
        (Nat.add_le_add_right n.le_succ 1)) i := by
  rw [transition_def]
  rfl

/-- Composite transitions are induced by reduction between the corresponding power quotients. -/
lemma scalarQuotientCohomologyTower_transitionOfLE {m n : ℕ} (h : m ≤ n) :
    (M.scalarQuotientCohomologyTower f i).transitionOfLE h =
      cohomologyMapLinear (M.scalarPowerQuotientTransition f
        (Nat.add_le_add_right h 1)) i := by
  rw [transitionOfLE_def]
  rfl

/-- The image of a class in the next power quotient reduces to its image in the current one. -/
lemma scalarQuotientCohomologyTower_transition_cohomologyMapLinear (n : ℕ)
    (x : Cohomology M i) :
    (M.scalarQuotientCohomologyTower f i).transition n
      (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1 + 1)))) i x) =
        cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i x := by
  rw [scalarQuotientCohomologyTower_transition, ← LinearMap.comp_apply,
    ← cohomologyMapLinear_comp, π_comp_scalarQuotientTransition]

/-- A cohomology class defines a compatible family of classes on all infinitesimal quotients. -/
def toFormalCohomology : Cohomology M i →ₗ[Γ(X, ⊤)]
    (M.scalarQuotientCohomologyTower f i).lim :=
  (M.scalarQuotientCohomologyTower f i).limLift
    (fun n ↦ cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i)
    (fun n ↦ LinearMap.ext (M.scalarQuotientCohomologyTower_transition_cohomologyMapLinear f i n))

/-- The coordinates of a formal cohomology class obtained from an ordinary class. -/
@[simp]
lemma limπ_toFormalCohomology (n : ℕ) (x : Cohomology M i) :
    (M.scalarQuotientCohomologyTower f i).limπ n (M.toFormalCohomology f i x) =
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i x := by
  rw [toFormalCohomology, ← LinearMap.comp_apply, limπ_comp_limLift]

/-- The canonical comparison from reductions of cohomology to cohomology of reductions. -/
def cohomologyReductionToQuotient :
    reduction (Ideal.span {f}) (Cohomology M i) ⟶ M.scalarQuotientCohomologyTower f i :=
  NatTrans.ofOpSequence (fun n ↦ ModuleCat.ofHom <|
    quotientsLift _ _ n
      (cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i)
      (M.pow_smul_le_ker_cohomologyMapLinear_scalarPowerQuotient f i (n + 1))) (fun n ↦ by
        ext x
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
          quotientsLift_quotientsπ]
        rw [← transition_def, transition_quotientsπ, quotientsLift_quotientsπ,
          ← LinearMap.comp_apply, ← cohomologyMapLinear_comp,
          π_comp_scalarQuotientTransition])

/-- On a representative, the comparison is induced by the quotient projection of sheaves. -/
@[simp]
lemma cohomologyReductionToQuotient_app_reductionπ (n : ℕ) (x : Cohomology M i) :
    ((M.cohomologyReductionToQuotient f i).app (op n)).hom
      (reductionπ (Ideal.span {f}) (Cohomology M i) n x) =
        cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i x := by
  rw [cohomologyReductionToQuotient, NatTrans.ofOpSequence_app, ModuleCat.hom_ofHom]
  exact quotientsLift_quotientsπ _ _ _ _ _ _

variable [Mono (M.globalSectionsSmul f)]

/-- Reduction of cohomology embeds into the cohomology of the quotient sheaf. -/
lemma cohomologyReductionToQuotient_app_injective (n : ℕ) :
    Function.Injective ((M.cohomologyReductionToQuotient f i).app (op n)).hom := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := quotientsπ_surjective _ _ n x
  rw [cohomologyReductionToQuotient_app_reductionπ] at hx
  apply (quotientsπ_eq_zero_iff _ _).mpr
  rw [← M.ker_cohomologyMapLinear_scalarPowerQuotient f i (n + 1)]
  exact hx

omit [Mono (M.globalSectionsSmul f)] in
/-- The comparison on inverse limits extends the canonical map on cohomology. -/
@[simp]
lemma limMap_cohomologyReductionToQuotient_toLimReduction (x : Cohomology M i) :
    limMap (M.cohomologyReductionToQuotient f i)
      (toLimReduction (Ideal.span {f}) (Cohomology M i) x) =
        M.toFormalCohomology f i x := by
  apply Subtype.ext
  funext n
  rw [coe_limMap_apply, productMap_apply, toLimReduction, coe_toLimQuotients_apply,
    cohomologyReductionToQuotient_app_reductionπ, ← limπ_apply, limπ_toFormalCohomology]

/-- Bounded parameter-power torsion in the next cohomology group makes the comparison on
inverse limits bijective. Only torsion classes need be annihilated, not the whole group. -/
theorem limMap_cohomologyReductionToQuotient_bijective
    {k : ℕ} (hk : ∀ n (x : Cohomology M (i + 1)), f ^ n • x = 0 → f ^ k • x = 0) :
    Function.Bijective (limMap (M.cohomologyReductionToQuotient f i)) := by
  refine ⟨limMap_injective (M.cohomologyReductionToQuotient_app_injective f i), fun y ↦ ?_⟩
  -- A class far enough along the compatible family has zero boundary after reduction.
  have hpre (n : ℕ) : ∃ z : Cohomology M i,
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i z =
        (y : (M.scalarQuotientCohomologyTower f i).Product) n := by
    have hn := M.exists_cohomologyMapLinear_eq_of_pow_smul_eq_zero f
      (Nat.add_le_add_right (Nat.le_add_right n k) 1) i
      ((y : (M.scalarQuotientCohomologyTower f i).Product) (n + k))
      (by simpa only [Nat.add_sub_add_right, Nat.add_sub_cancel_left] using hk (n + k + 1))
    obtain ⟨a, ha⟩ := hn
    refine ⟨a, ha.trans ?_⟩
    rw [← M.scalarQuotientCohomologyTower_transitionOfLE f i (Nat.le_add_right n k)]
    exact (M.scalarQuotientCohomologyTower f i).transitionOfLE_coe_lim y _
  choose z hz using hpre
  let q n := reductionπ (Ideal.span {f}) (Cohomology M i) n (z n)
  have hq n : (reduction (Ideal.span {f}) (Cohomology M i)).transition n (q (n + 1)) = q n := by
    apply M.cohomologyReductionToQuotient_app_injective f i n
    rw [← LinearMap.comp_apply, app_comp_transition, LinearMap.comp_apply]
    dsimp only [q]
    rw [cohomologyReductionToQuotient_app_reductionπ,
      cohomologyReductionToQuotient_app_reductionπ, hz, hz]
    exact (M.scalarQuotientCohomologyTower f i).transition_coe_lim_succ y n
  refine ⟨⟨q, (reduction _ _).mem_lim.mpr hq⟩, ?_⟩
  apply Subtype.ext
  funext n
  rw [coe_limMap_apply, productMap_apply]
  exact (M.cohomologyReductionToQuotient_app_reductionπ f i n (z n)).trans (hz n)

/-- Completion of cohomology equals the inverse limit of the cohomology of infinitesimal
quotients if `f` is regular on the sheaf and power torsion in the next cohomology is bounded.
For `i = 0`, this identifies completed sections with formal sections. -/
def cohomologyCompletionEquiv {k : ℕ}
    (hk : ∀ n (x : Cohomology M (i + 1)), f ^ n • x = 0 → f ^ k • x = 0) :
    AdicCompletion (Ideal.span {f}) (Cohomology M i) ≃ₗ[Γ(X, ⊤)]
      (M.scalarQuotientCohomologyTower f i).lim :=
  (limReductionEquiv (Ideal.span {f}) (Cohomology M i)).symm.trans
    (LinearEquiv.ofBijective _ (M.limMap_cohomologyReductionToQuotient_bijective f i hk))

/-- The `n`-th formal coordinate is computed by any representative of the residue of the
completed class modulo `fⁿ⁺¹`. -/
lemma limπ_cohomologyCompletionEquiv {k : ℕ}
    (hk : ∀ n (x : Cohomology M (i + 1)), f ^ n • x = 0 → f ^ k • x = 0)
    {x : AdicCompletion (Ideal.span {f}) (Cohomology M i)} {n : ℕ} {a : Cohomology M i}
    (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    (M.scalarQuotientCohomologyTower f i).limπ n (M.cohomologyCompletionEquiv f i hk x) =
      cohomologyMapLinear (cokernel.π (M.globalSectionsSmul (f ^ (n + 1)))) i a := by
  dsimp only [cohomologyCompletionEquiv]
  rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    ← LinearMap.comp_apply, limπ_comp_limMap, LinearMap.comp_apply,
    limπ_limReductionEquiv_symm_apply (Ideal.span {f}) (Cohomology M i) ha,
    cohomologyReductionToQuotient_app_reductionπ]

/-- The completion comparison extends reduction of ordinary cohomology classes. -/
@[simp]
lemma cohomologyCompletionEquiv_of {k : ℕ}
    (hk : ∀ n (x : Cohomology M (i + 1)), f ^ n • x = 0 → f ^ k • x = 0)
    (x : Cohomology M i) :
    M.cohomologyCompletionEquiv f i hk (AdicCompletion.of (Ideal.span {f}) _ x) =
      M.toFormalCohomology f i x := by
  dsimp only [cohomologyCompletionEquiv]
  rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    ← limReductionEquiv_toLimReduction (Ideal.span {f}) (Cohomology M i) x,
    LinearEquiv.symm_apply_apply, limMap_cohomologyReductionToQuotient_toLimReduction]

/-- Complete cohomology classes are exactly compatible classes on infinitesimal quotients,
provided the next cohomology has bounded parameter-power torsion. -/
theorem toFormalCohomology_bijective [IsAdicComplete (Ideal.span {f}) (Cohomology M i)]
    {k : ℕ} (hk : ∀ n (x : Cohomology M (i + 1)), f ^ n • x = 0 → f ^ k • x = 0) :
    Function.Bijective (M.toFormalCohomology f i) := by
  have h := (M.limMap_cohomologyReductionToQuotient_bijective f i hk).comp
    (toLimReduction_bijective (Ideal.span {f}) (Cohomology M i))
  simpa only [Function.comp_def, limMap_cohomologyReductionToQuotient_toLimReduction] using h

end AlgebraicGeometry.Scheme.Modules
