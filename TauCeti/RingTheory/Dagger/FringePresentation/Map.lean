/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.FringePresentation.Basic

import TauCeti.Analysis.Normed.Ring.Finsupp
import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.RingTheory.Dagger.DaggerAlgebra.Continuity
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.DaggerAlgebra.WeakCompleteness
import TauCeti.RingTheory.Dagger.FringePresentation.Topology
import TauCeti.RingTheory.Dagger.Radius
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal

/-!
# Morphisms of dagger algebras respect fringe systems

Let `A` and `B` be `K`-algebras with fringe presentations `P` and `Q`, so that `A` and `B` are the
colimits of their stages `A_ρ = T_n(ρ) ⧸ (f)` and `B_ρ' = T_m(ρ') ⧸ (g)` as the radii decrease to
`1`. This file shows that every `K`-algebra homomorphism `ψ : A → B`, with no continuity assumed,
respects these ind-systems: for every radius `ρ` of `P`, the composite `A_ρ → A → B` factors
through the stage `B_ρ' → B` for every radius `ρ'` of `Q` close enough to `1`
(`eventually_exists_ofStage_comp_eq`). Consequently every fringe algebra of `A` is carried into
the fringe algebras of `B` of all radii close enough to `1` (`eventually_map_fringeAlgebra_le`),
finitely many fringe algebras of `A`, from any fringe presentations, lie in a common fringe
algebra of any other (`exists_forall_fringeAlgebra_le`), and two fringe presentations of the same
algebra give mutually cofinal ind-systems of stages.

The factorisation is evaluation of series of `T_n(ρ)` at elements of `B_ρ'`. The images
`bᵢ = ψ(Xᵢ)` of the variables have supremum seminorm at most `1`, so each is a root of a monic
polynomial over `W_m` whose coefficients have Gauss norm at most `1`
(`TauCeti.Dagger.washnitzerAlgebra.exists_monic_eval₂_eq_zero_of_supSeminorm_le_one`). At radii
`ρ'` close enough to `1` these coefficients have `ρ'`-Gauss norm at most `ρ`, and a lift `βᵢ` of
`bᵢ` to `B_ρ'` is a root of the same equation there. Its powers then grow at most like those of
`ρ` (`Polynomial.Monic.exists_norm_pow_le_mul_pow_of_eval_eq_zero`), although `βᵢ` itself may
have norm larger than `ρ`, as a nilpotent element may. Evaluation at arguments with bounded powers
(`RingHom.restrictedEval₂OfPowBound`) then gives a homomorphism `T_n(ρ) → B_ρ'` sending `Xᵢ` to
`βᵢ`. It is compatible with `ψ` because both composites into the completion of `B` are continuous
and agree on polynomials, and the completion map is injective. Finally the relations of `A_ρ`
map to elements of `B_ρ'` vanishing in `B`, hence vanishing at a smaller radius.

## Main results

* `TauCeti.Dagger.FringePresentation.eventually_exists_ofStage_comp_eq`: the composite of a stage
  map of `P` with `ψ` factors through the stage maps of `Q` at all radii close enough to `1`, and
  `exists_ofStage_comp_eq` gives one such radius.
* `TauCeti.Dagger.FringePresentation.eventually_map_fringeAlgebra_le` and
  `exists_map_fringeAlgebra_le`: fringe algebras map into fringe algebras.
* `TauCeti.Dagger.FringePresentation.exists_forall_fringeAlgebra_le`: finitely many fringe
  algebras lie in a common fringe algebra of any fringe presentation.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Lemma 1.8.
* A. Vezzani, *The Monsky–Washnitzer and the overconvergent realizations*, Int. Math. Res. Not.
  IMRN 2018, Appendix A, Proposition A.22.
-/

public section

namespace TauCeti.Dagger.FringePresentation

open Filter Topology _root_.MvPowerSeries Polynomial
open TauCeti.MvPowerSeries (isRestricted_subring_ringHom_ext_of_continuous)

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- The radii of fringe stages are positive, so that the stages carry their quotient Gauss norms. -/
private local instance fact_pos_coe {R : ℝ} (ρ : Set.Ioc (1 : ℝ) R) : Fact (0 < (ρ : ℝ)) :=
  ⟨zero_lt_one.trans ρ.property.1⟩

section Lift

variable (Q : FringePresentation K B)

omit [CompleteSpace K] in
/-- A monic polynomial over `W_m` whose coefficients are restricted at a radius `ρ` of `Q`, with
`ρ`-weighted coefficient norms below `μ`, and which vanishes at a series `g` modulo the stage ideal,
comes from a monic polynomial over `T_m(ρ)` with coefficients of norm at most `μ`, vanishing at `g`
modulo the stage ideal. -/
private theorem exists_monic_eval_mem_stageIdeal (ρ : Set.Ioc (1 : ℝ) Q.radius)
    {p : (washnitzerAlgebra (Fin Q.n) K)[X]} (hp : p.Monic) {μ : ℝ} (hμ : 0 ≤ μ)
    (hc : ∀ j ∈ p.support, IsRestricted (fun _ : Fin Q.n ↦ (ρ : ℝ))
      (p.coeff j : MvPowerSeries (Fin Q.n) K) ∧
        ∀ t, ‖coeff t (p.coeff j : MvPowerSeries (Fin Q.n) K)‖ * (ρ : ℝ) ^ t.degree < μ)
    {g : washnitzerAlgebra (Fin Q.n) K}
    (hg : IsRestricted (fun _ : Fin Q.n ↦ (ρ : ℝ)) (g : MvPowerSeries (Fin Q.n) K))
    (hpg : IsRestricted (fun _ : Fin Q.n ↦ (ρ : ℝ))
      ((p.eval g : washnitzerAlgebra (Fin Q.n) K) : MvPowerSeries (Fin Q.n) K))
    (hmem : ⟨_, hpg⟩ ∈ Q.stageIdeal ρ) :
    ∃ q : (IsRestricted.subring (R := K) (fun _ : Fin Q.n ↦ (ρ : ℝ)))[X], q.Monic ∧
      q.eval ⟨g, hg⟩ ∈ Q.stageIdeal ρ ∧ ∀ j, ‖q.coeff j‖ ≤ μ := by
  set ι := washnitzerAlgebra.ofRestricted (R := K) (c := fun _ : Fin Q.n ↦ (ρ : ℝ))
    ρ.property.1 fun _ ↦ le_rfl
  have hι : Function.Injective ι := washnitzerAlgebra.ofRestricted_injective _ _
  have hlifts : p ∈ Polynomial.lifts ι.toRingHom := by
    refine Polynomial.lifts_iff_coeff_lifts _ |>.mpr fun j ↦ ?_
    by_cases hj : j ∈ p.support
    · exact ⟨⟨_, (hc j hj).1⟩, Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _)⟩
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hj]⟩
  obtain ⟨q, hqp, -, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hqι (j : ℕ) : ι (q.coeff j) = p.coeff j := by
    rw [← hqp, Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  refine ⟨q, hq, ?_, fun j ↦ ?_⟩
  · convert hmem using 1
    refine hι ?_
    have h := Polynomial.eval₂_hom (p := q) ι.toRingHom ⟨g, hg⟩
    rw [← Polynomial.eval_map, hqp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    have hιg : ι ⟨g, hg⟩ = g := Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _)
    have hιp : ι ⟨_, hpg⟩ = p.eval g := Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _)
    exact h.symm.trans ((congrArg (fun x ↦ p.eval x) hιg).trans hιp.symm)
  by_cases hj : j ∈ p.support
  · refine _root_.MvPowerSeries.norm_le_iff.mpr fun t ↦ ?_
    rw [← washnitzerAlgebra.coe_ofRestricted ρ.property.1 (fun _ ↦ le_rfl) (q.coeff j), hqι,
      Finsupp.prod_pow_eq_pow_degree]
    exact ((hc j hj).2 t).le
  · have hq0 : q.coeff j = 0 := hι (by
      rw [hqι, map_zero]
      exact Polynomial.notMem_support_iff.mp hj)
    rw [hq0, norm_zero]
    exact hμ

/-- An element of `B` of supremum seminorm at most `1` lifts, at every radius close enough to `1`,
to an element of the stage whose powers grow at most like those of a given `μ > 1`. -/
private theorem eventually_exists_ofStage_eq_norm_pow_le {b : B} (hb : supSeminorm K b ≤ 1)
    {μ : ℝ} (hμ : 1 < μ) :
    ∀ᶠ ρ in atBot, ∃ β : Q.stage ρ, Q.ofStage ρ β = b ∧ ∃ D, ∀ k, ‖β ^ k‖ ≤ D * μ ^ k := by
  -- A small integral equation `p(b) = 0` over `W_m`, and a lift `g` of `b`.
  obtain ⟨p, hp, hpb, hpc⟩ :=
    washnitzerAlgebra.exists_monic_eval₂_eq_zero_of_supSeminorm_le_one Q.proj_surjective hb
  obtain ⟨g, rfl⟩ := Q.proj_surjective b
  have hpg : p.eval g ∈ Q.ideal := by
    rw [← Q.ker_proj, RingHom.mem_ker, ← hpb]
    exact (Polynomial.eval₂_at_apply (Q.proj : _ →+* B) g).symm
  have hcoeff (j : ℕ) (t) : ‖coeff t (p.coeff j : MvPowerSeries (Fin Q.n) K)‖ < μ :=
    ((washnitzerAlgebra.norm_coeff_le _ t).trans (hpc j)).trans_lt hμ
  -- At radii close to `1`, the equation descends to the stage, with small coefficients.
  filter_upwards [Q.eventually_atBot_of_nhdsGT (Q.eventually_mem_stageIdeal hpg),
    Q.eventually_atBot_of_nhdsGT (eventually_isRestricted_of_mem_washnitzerAlgebra g.property),
    Q.eventually_atBot_of_nhdsGT ((eventually_all_finset p.support).2 fun j _ ↦
      eventually_isRestricted_forall_norm_coeff_mul_pow_lt (p.coeff j).property (hcoeff j))]
    with ρ ⟨_, hpρ, hmem⟩ hgρ hcρ
  obtain ⟨q, hq, hqg, hqc⟩ := Q.exists_monic_eval_mem_stageIdeal ρ hp (zero_le_one.trans hμ.le)
    hcρ hgρ hpρ hmem
  set π := Ideal.Quotient.mk (Q.stageIdeal ρ)
  obtain ⟨D, hD⟩ := (hq.map π).exists_norm_pow_le_mul_pow_of_eval_eq_zero (x := π ⟨g, hgρ⟩)
    (by rw [Polynomial.eval_map, Polynomial.eval₂_hom, Ideal.Quotient.eq_zero_iff_mem.mpr hqg])
    (zero_lt_one.trans hμ) fun j hj ↦ by
      rw [Polynomial.coeff_map]
      exact (Ideal.Quotient.norm_mk_le _ _).trans ((hqc j).trans
        (le_self_pow₀ hμ.le (Nat.sub_ne_zero_of_lt hj)))
  refine ⟨π ⟨g, hgρ⟩, ?_, D, hD⟩
  rw [ofStage_mk]
  exact congrArg Q.proj (Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _))

end Lift

section Factorisation

variable (P : FringePresentation K A) (Q : FringePresentation K B) (ψ : A →ₐ[K] B)

/-- The series of `T_n(ρ)`, mapped to `B` through `A`, are evaluations at elements of a stage of
`Q`: there is a homomorphism `T_n(ρ) → B_ρ'` lifting `T_n(ρ) → W_n → A → B` at every radius
`ρ'` of `Q` close enough to `1`. -/
private theorem eventually_exists_ofStage_comp_eq_comp_ofRestricted
    (ρ : Set.Ioc (1 : ℝ) P.radius) :
    ∀ᶠ ρ' in atBot, ∃ Φ : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ)) →ₐ[K]
      Q.stage ρ', (Q.ofStage ρ').comp Φ = (ψ.comp P.proj).comp
        (washnitzerAlgebra.ofRestricted ρ.property.1 fun _ ↦ le_rfl) := by
  have : IsDaggerAlgebra K B :=
    IsDaggerAlgebra.of_surjective_washnitzerAlgebra Q.proj Q.proj_surjective
  -- The images of the variables lift to the stages, with powers growing at most like `ρ`.
  filter_upwards [eventually_all.2 fun i : Fin P.n ↦ Q.eventually_exists_ofStage_eq_norm_pow_le
    (washnitzerAlgebra.supSeminorm_apply_X_le_one (ψ.comp P.proj) i) ρ.property.1] with ρ' hρ'
  choose β hβ hβD using hρ'
  obtain ⟨D, hD⟩ := exists_forall_norm_prod_pow_le_mul_prod (c := fun _ : Fin P.n ↦ (ρ : ℝ))
    (fun _ ↦ zero_le_one.trans ρ.property.1.le) hβD
  -- Evaluation at these lifts.
  have hφ (r : K) : ‖algebraMap K (Q.stage ρ') r‖ ≤ ‖(1 : Q.stage ρ')‖ * ‖r‖ := by
    rw [norm_algebraMap, mul_comm]
  let Φ : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ)) →ₐ[K] Q.stage ρ' :=
    { (algebraMap K (Q.stage ρ')).restrictedEval₂OfPowBound β hφ hD with
      commutes' := RingHom.restrictedEval₂OfPowBound_algebraMap _ β hφ hD }
  have hΦ : Continuous Φ := RingHom.continuous_restrictedEval₂OfPowBound _ β hφ hD
  refine ⟨Φ, ?_⟩
  -- Both composites, followed by the injective completion map of `B`, are continuous and agree
  -- on constants and variables.
  suffices h : (toCompletion K B).comp ((Q.ofStage ρ').comp Φ) =
      (toCompletion K B).comp ((ψ.comp P.proj).comp
        (washnitzerAlgebra.ofRestricted ρ.property.1 fun _ ↦ le_rfl)) from
    AlgHom.ext fun f ↦ toCompletion_injective (AlgHom.congr_fun h f)
  have hΦX (i : Fin P.n) : Φ ⟨X i, isRestricted_X _ i⟩ = β i :=
    RingHom.restrictedEval₂OfPowBound_X _ β hφ hD i
  exact AlgHom.toRingHom_injective (isRestricted_subring_ringHom_ext_of_continuous
    ((Q.continuous_toCompletion_comp_ofStage ρ').comp hΦ)
    (continuous_toCompletion_comp_ofRestricted _ ρ.property.1) (fun r ↦ by simp)
    fun i ↦ by simp [hΦX, hβ, washnitzerAlgebra.ofRestricted_X])

/-- **Morphisms respect fringe systems** (Grosse-Klönne, Lemma 1.8). Let `ψ : A → B` be a
homomorphism of `K`-algebras with fringe presentations `P` and `Q`; no continuity is assumed. For
every radius `ρ` of `P`, the composite `A_ρ → A → B` factors through the stage map `B_ρ' → B` for
every radius `ρ'` of `Q` close enough to `1`. For two fringe presentations of the same algebra and
`ψ` the identity, this says that their ind-systems of stages are mutually cofinal. -/
theorem eventually_exists_ofStage_comp_eq (ρ : Set.Ioc (1 : ℝ) P.radius) :
    ∀ᶠ ρ' in atBot, ∃ Φ : P.stage ρ →ₐ[K] Q.stage ρ',
      (Q.ofStage ρ').comp Φ = ψ.comp (P.ofStage ρ) := by
  obtain ⟨ρ₀, Φ₀, hΦ₀⟩ := (P.eventually_exists_ofStage_comp_eq_comp_ofRestricted Q ψ ρ).exists
  have hΦ₀a (a) : Q.ofStage ρ₀ (Φ₀ a) = ψ (P.ofStage ρ (Ideal.Quotient.mk _ a)) := by
    rw [ofStage_mk]
    exact AlgHom.congr_fun hΦ₀ a
  -- The relations of `A_ρ` map to elements of `B_ρ₀` vanishing in `B`, hence at smaller radii.
  have hrel (k : Fin P.r) : ∀ᶠ ρ' in atBot, ∀ h : ρ' ≤ ρ₀, Q.stageMap h (Φ₀
      (TauCeti.MvPowerSeries.restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ.property.1.le)
        (fun _ ↦ ρ.property.2) (P.relation k))) = 0 := by
    have hk : TauCeti.MvPowerSeries.restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ.property.1.le)
        (fun _ ↦ ρ.property.2) (P.relation k) ∈ P.stageIdeal ρ := by
      rw [stageIdeal_def]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨ρ₁, h₁, hρ₁⟩ := Q.exists_stageMap_eq_zero _ (by
      rw [hΦ₀a, Ideal.Quotient.eq_zero_iff_mem.mpr hk, map_zero, map_zero])
    filter_upwards [eventually_le_atBot ρ₁] with ρ' hρ' h
    rw [← Q.stageMap_stageMap hρ' h₁, hρ₁, map_zero]
  filter_upwards [eventually_all.2 hrel, eventually_le_atBot ρ₀] with ρ' hρ' h₀
  have hker (a) (ha : a ∈ P.stageIdeal ρ) : ((Q.stageMap h₀).comp Φ₀) a = 0 := by
    rw [stageIdeal_def] at ha
    refine (Ideal.span_le (I := RingHom.ker ((Q.stageMap h₀).comp Φ₀))).mpr ?_ ha
    rintro _ ⟨k, rfl⟩
    exact hρ' k h₀
  refine ⟨Ideal.Quotient.liftₐ _ ((Q.stageMap h₀).comp Φ₀) hker, Ideal.Quotient.algHom_ext K ?_⟩
  rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, ← AlgHom.comp_assoc, ofStage_comp_stageMap]
  ext a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact hΦ₀a a

/-- **Morphisms respect fringe systems** (Grosse-Klönne, Lemma 1.8): for every radius `ρ` of `P`,
the composite `A_ρ → A → B` factors through some stage `B_ρ' → B` of `Q`. -/
theorem exists_ofStage_comp_eq (ρ : Set.Ioc (1 : ℝ) P.radius) :
    ∃ (ρ' : Set.Ioc (1 : ℝ) Q.radius) (Φ : P.stage ρ →ₐ[K] Q.stage ρ'),
      (Q.ofStage ρ').comp Φ = ψ.comp (P.ofStage ρ) :=
  (P.eventually_exists_ofStage_comp_eq Q ψ ρ).exists

/-- A homomorphism of `K`-algebras with fringe presentations carries each fringe algebra of `P`
into the fringe algebras of `Q` of all radii close enough to `1`. -/
theorem eventually_map_fringeAlgebra_le (ρ : Set.Ioc (1 : ℝ) P.radius) :
    ∀ᶠ ρ' in atBot, (P.fringeAlgebra ρ).map ψ ≤ Q.fringeAlgebra ρ' := by
  filter_upwards [P.eventually_exists_ofStage_comp_eq Q ψ ρ] with ρ' ⟨Φ, hΦ⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp hb
  obtain ⟨x, rfl⟩ := P.mem_fringeAlgebra.mp ha
  exact Q.mem_fringeAlgebra.mpr ⟨Φ x, by rw [← AlgHom.comp_apply, hΦ, AlgHom.comp_apply]⟩

/-- A homomorphism of `K`-algebras with fringe presentations carries each fringe algebra of `P`
into some fringe algebra of `Q`. -/
theorem exists_map_fringeAlgebra_le (ρ : Set.Ioc (1 : ℝ) P.radius) :
    ∃ ρ', (P.fringeAlgebra ρ).map ψ ≤ Q.fringeAlgebra ρ' :=
  (P.eventually_map_fringeAlgebra_le Q ψ ρ).exists

end Factorisation

/-- **Finitely many fringe algebras lie in a common fringe algebra.** Fringe algebras of finitely
many fringe presentations of `A`, at arbitrary radii, are all contained in one fringe algebra of
any fringe presentation `Q` of `A`. -/
theorem exists_forall_fringeAlgebra_le {ι : Type*} [Finite ι] (P : ι → FringePresentation K A)
    (ρ : ∀ i, Set.Ioc (1 : ℝ) (P i).radius) (Q : FringePresentation K A) :
    ∃ ρ', ∀ i, (P i).fringeAlgebra (ρ i) ≤ Q.fringeAlgebra ρ' := by
  obtain ⟨ρ', h⟩ := (eventually_all.2 fun i ↦
    (P i).eventually_map_fringeAlgebra_le Q (AlgHom.id K A) (ρ i)).exists
  exact ⟨ρ', fun i ↦ by simpa using h i⟩

end TauCeti.Dagger.FringePresentation
