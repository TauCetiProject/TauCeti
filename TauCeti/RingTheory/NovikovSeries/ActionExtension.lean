/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Residue
public import TauCeti.RingTheory.NovikovSeries.Localization
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Action-weighted Novikov series, localization, and action specialization

Let `G` be an additive monoid (or additive group) with energy homomorphism `E : G →+ ℝ` and
grading homomorphism `μ : G →+ B`. Adjoining a real action weight produces `G × ℝ` with period
`actionPeriod E (g, r) = E g + r` and degree `actionDegree μ (g, r) = μ g`, whose degree-zero
action monomials `T^r = single (0, r) 1` (`TauCeti.NovikovSeries.actionMonomial`) shift filtrations
without collapsing distinct classes of equal energy.

Specializing `TauCeti.RingTheory.NovikovSeries.Localization` to `ι = AddMonoidHom.inr G ℝ` shows
that `NovikovSeries R (G × ℝ) (actionPeriod E)` is the localization of its nonnegative subring at
`actionSubmonoid R E` (`TauCeti.NovikovSeries.isLocalization_actionSubmonoid`), with canonical
algebra equivalence `TauCeti.NovikovSeries.actionLocalizationAlgEquiv`. When `G` is an additive
group, projecting `(actionPeriod E).ker` onto the first coordinate identifies
`(nonnegSubring R (actionPeriod E)) ⧸ (posIdeal R (actionPeriod E))` with `AddMonoidAlgebra R G`
(`TauCeti.NovikovSeries.quotientActionPosIdealEquiv`). When `μ` has infinite range and `R` is
nontrivial, the dense graded subalgebra is proper
(`TauCeti.NovikovSeries.iSup_nonnegGradeBy_actionDegree_ne_top`).

Finally, `ρ : R →+* k` induces the continuous action specialization
`TauCeti.NovikovSeries.actionSpecialization ρ E` into `NovikovSeries k ℝ (AddMonoidHom.id ℝ)`
along `actionPeriod E`, restricting to `nonnegSubring`, mapping `actionSubmonoid R E` onto
`realActionSubmonoid k`, and factoring uniquely through the localization.

## Main definitions

* `TauCeti.NovikovSeries.actionPeriod E`, `TauCeti.NovikovSeries.actionDegree μ`: the period
  `(g, r) ↦ E g + r` and degree `(g, r) ↦ μ g` on `G × ℝ`.
* `TauCeti.NovikovSeries.actionMonomial`, `TauCeti.NovikovSeries.nonnegActionMonomial`,
  `TauCeti.NovikovSeries.actionSubmonoid`: the action monomials `T^r` and their nonnegative
  submonoid.
* `TauCeti.NovikovSeries.actionLocalizationAlgEquiv`: the canonical algebra isomorphism from
  `Localization (actionSubmonoid R E)` onto `NovikovSeries R (G × ℝ) (actionPeriod E)`.
* `TauCeti.NovikovSeries.actionInlRingHom`, `TauCeti.NovikovSeries.actionInlNonnegSubring`:
  injective continuous inclusions along `g ↦ (g, 0)`.
* `TauCeti.NovikovSeries.actionResidueRingHom`, `TauCeti.NovikovSeries.quotientActionPosIdealEquiv`,
  `TauCeti.NovikovSeries.quotientActionPosIdealAlgEquiv`: the post-extension residue isomorphism
  onto `AddMonoidAlgebra R G`.
* `TauCeti.NovikovSeries.actionSpecialization`, `TauCeti.NovikovSeries.nonnegActionSpecialization`:
  pushforward along `actionPeriod E` into `NovikovSeries k ℝ (AddMonoidHom.id ℝ)`.

## Main results

* `TauCeti.NovikovSeries.isLocalization_actionSubmonoid`: localization at `actionSubmonoid R E`
  recovers `NovikovSeries R (G × ℝ) (actionPeriod E)`.
* `TauCeti.NovikovSeries.not_isUnit_nonnegActionMonomial`: for `r > 0` over a nontrivial ring,
  `T^r` is not a unit of `nonnegSubring R (actionPeriod E)`.
* `TauCeti.NovikovSeries.iSup_nonnegGradeBy_actionDegree_ne_top`,
  `TauCeti.NovikovSeries.not_surjective_coeAlgHom_actionDegree`: properness of the dense graded
  subalgebra for infinite degree range.
* `TauCeti.NovikovSeries.eq_actionSpecialization_of_comp_nonneg`: uniqueness of
  `actionSpecialization` out of the localized ring.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46, 2009, Chapter 2 and Section 6.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovSeries

/-! ### The action-weighted extension `G × ℝ` -/

section ActionExtension

variable {S R G B : Type*}

section ActionPeriod

variable [AddZeroClass G]

/-- The action-weighted period homomorphism `(g, r) ↦ E g + r` on `G × ℝ`. -/
def actionPeriod (E : G →+ ℝ) : G × ℝ →+ ℝ := E.comp (.fst G ℝ) + .snd G ℝ

@[simp]
theorem actionPeriod_apply (E : G →+ ℝ) (p : G × ℝ) : actionPeriod E p = E p.1 + p.2 := (rfl)

theorem actionPeriod_inl (E : G →+ ℝ) (g : G) :
    actionPeriod E (AddMonoidHom.inl G ℝ g) = E g := by simp [actionPeriod]

theorem actionPeriod_inr (E : G →+ ℝ) (r : ℝ) :
    actionPeriod E (AddMonoidHom.inr G ℝ r) = r := by simp [actionPeriod]

/-- The extended degree homomorphism `(g, r) ↦ μ g` on `G × ℝ`, assigning degree `0` to the real
action factor. -/
def actionDegree [AddZeroClass B] (μ : G →+ B) : G × ℝ →+ B := μ.comp (.fst G ℝ)

@[simp]
theorem actionDegree_apply [AddZeroClass B] (μ : G →+ B) (p : G × ℝ) :
    actionDegree μ p = μ p.1 := (rfl)

theorem actionDegree_inr [AddZeroClass B] (μ : G →+ B) (r : ℝ) :
    actionDegree μ (AddMonoidHom.inr G ℝ r) = 0 := map_zero μ

end ActionPeriod

section Monomials

section Semiring

variable [Semiring R] [AddZeroClass G]

variable (R) in
/-- The degree-zero action monomial `T^r = single (0, r) 1` in
`NovikovSeries R (G × ℝ) (actionPeriod E)`. -/
def actionMonomial (E : G →+ ℝ) (r : ℝ) : NovikovSeries R (G × ℝ) (actionPeriod E) :=
  single (0, r) 1

theorem actionMonomial_def (E : G →+ ℝ) (r : ℝ) : actionMonomial R E r = single (0, r) 1 := (rfl)

@[simp]
theorem coeff_actionMonomial_same (E : G →+ ℝ) (r : ℝ) :
    (actionMonomial R E r).coeff (0, r) = 1 := coeff_single_same (0, r) 1

@[simp]
theorem coeff_actionMonomial_of_ne (E : G →+ ℝ) {r : ℝ} {p : G × ℝ} (hp : p ≠ (0, r)) :
    (actionMonomial R E r).coeff p = 0 := coeff_single_of_ne hp 1

theorem coeff_actionMonomial [DecidableEq G] (E : G →+ ℝ) (r : ℝ) :
    (actionMonomial R E r).coeff = Pi.single (0, r) 1 := coeff_single (0, r) 1

@[simp]
theorem actionMonomial_zero (E : G →+ ℝ) : actionMonomial R E 0 = 1 := by
  rw [actionMonomial_def, Prod.mk_zero_zero, single_zero_one]

@[simp]
theorem actionMonomial_mul (E : G →+ ℝ) (r s : ℝ) :
    actionMonomial R E r * actionMonomial R E s = actionMonomial R E (r + s) := by
  simp [actionMonomial_def, single_mul_single]

@[simp]
theorem actionMonomial_mul_single (E : G →+ ℝ) (r : ℝ) (p : G × ℝ) (c : R) :
    actionMonomial R E r * single p c = single (p.1, r + p.2) c := by
  rw [actionMonomial_def, single_mul_single, one_mul]; congr 1; ext <;> simp

@[simp]
theorem single_mul_actionMonomial (E : G →+ ℝ) (p : G × ℝ) (c : R) (r : ℝ) :
    single p c * actionMonomial R E r = single (p.1, p.2 + r) c := by
  rw [actionMonomial_def, single_mul_single, mul_one]; congr 1; ext <;> simp

/-- Multiplying on the left by the action monomial `T^r` shifts the real coordinate by `r`. -/
theorem coeff_actionMonomial_mul (E : G →+ ℝ) (r : ℝ)
    (a : NovikovSeries R (G × ℝ) (actionPeriod E)) (p : G × ℝ) :
    (actionMonomial R E r * a).coeff p = a.coeff (p.1, p.2 - r) := by
  rw [actionMonomial_def, coeff_mul_eq_sum (s := {((0, r), (p.1, p.2 - r))})
      (fun _ hq => by rw [Finset.mem_singleton.1 hq]; ext <;> simp)
      fun u v huv hu _ => ?_, Finset.sum_singleton, coeff_single_same, one_mul]
  obtain rfl : u = (0, r) := by_contra fun hne => hu (coeff_single_of_ne hne 1)
  rw [Finset.mem_singleton]
  exact Prod.ext rfl (Prod.ext (by simpa using congrArg Prod.fst huv)
    (eq_sub_of_add_eq' (congrArg Prod.snd huv)))

/-- Multiplying on the right by the action monomial `T^r` shifts the real coordinate by `r`. -/
theorem coeff_mul_actionMonomial (E : G →+ ℝ) (a : NovikovSeries R (G × ℝ) (actionPeriod E))
    (r : ℝ) (p : G × ℝ) : (a * actionMonomial R E r).coeff p = a.coeff (p.1, p.2 - r) := by
  rw [actionMonomial_def, coeff_mul_eq_sum (s := {((p.1, p.2 - r), (0, r))})
      (fun _ hq => by rw [Finset.mem_singleton.1 hq]; ext <;> simp)
      fun u v huv _ hv => ?_, Finset.sum_singleton, coeff_single_same, mul_one]
  obtain rfl : v = (0, r) := by_contra fun hne => hv (coeff_single_of_ne hne 1)
  rw [Finset.mem_singleton]
  exact Prod.ext (Prod.ext (by simpa using congrArg Prod.fst huv)
    (eq_sub_of_add_eq (congrArg Prod.snd huv))) rfl

theorem actionMonomial_mul_actionMonomial_neg (E : G →+ ℝ) (r : ℝ) :
    actionMonomial R E r * actionMonomial R E (-r) = 1 := by
  rw [actionMonomial_mul, add_neg_cancel, actionMonomial_zero]

theorem actionMonomial_neg_mul_actionMonomial (E : G →+ ℝ) (r : ℝ) :
    actionMonomial R E (-r) * actionMonomial R E r = 1 := by
  rw [actionMonomial_mul, neg_add_cancel, actionMonomial_zero]

/-- Every real action monomial `T^r` is homogeneous of degree `0` for `actionDegree μ`. -/
theorem actionMonomial_mem_gradeBy_zero [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B) (r : ℝ) :
    actionMonomial R E r ∈ gradeBy R (actionPeriod E) (actionDegree μ) 0 := by
  simpa [actionMonomial_def] using
    single_mem_gradeBy (N := actionPeriod E) (actionDegree μ) ((0 : G), r) (1 : R)

end Semiring

/-- Every real action monomial `T^r` is a unit of `NovikovSeries R (G × ℝ) (actionPeriod E)`,
with inverse `T^(-r)`. -/
theorem isUnit_actionMonomial [Semiring R] [AddMonoid G] (E : G →+ ℝ) (r : ℝ) :
    IsUnit (actionMonomial R E r) :=
  isUnit_iff_exists.2 ⟨actionMonomial R E (-r),
    actionMonomial_mul_actionMonomial_neg E r, actionMonomial_neg_mul_actionMonomial E r⟩

/-- Multiplying by `T^r` preserves every homogeneous degree piece for `actionDegree μ`. -/
theorem actionMonomial_mul_mem_gradeBy [Semiring R] [AddMonoid G] [AddMonoid B]
    (E : G →+ ℝ) (μ : G →+ B) (r : ℝ) {b : B} {a : NovikovSeries R (G × ℝ) (actionPeriod E)}
    (ha : a ∈ gradeBy R (actionPeriod E) (actionDegree μ) b) :
    actionMonomial R E r * a ∈ gradeBy R (actionPeriod E) (actionDegree μ) b := by
  simpa using SetLike.GradedMul.mul_mem (actionMonomial_mem_gradeBy_zero E μ r) ha

/-- Classes of distinct degrees remain distinct in `NovikovSeries R (G × ℝ) (actionPeriod E)`,
even when their energies `E g₁` and `E g₂` coincide. -/
theorem single_action_ne_of_degree_ne [Zero R] [AddZeroClass G]
    (E : G →+ ℝ) (μ : G → B) {g₁ g₂ : G} (hμ : μ g₁ ≠ μ g₂) (r₁ r₂ : ℝ) {c₁ c₂ : R}
    (hc₁ : c₁ ≠ 0) :
    (single (g₁, r₁) c₁ : NovikovSeries R (G × ℝ) (actionPeriod E)) ≠ single (g₂, r₂) c₂ := by
  intro heq
  have hp : (g₁, r₁) ≠ (g₂, r₂) := fun h => hμ (congrArg (μ ∘ Prod.fst) h)
  exact hc₁ <| by simpa [coeff_single_of_ne hp] using congrArg (·.coeff (g₁, r₁)) heq

section Ring

variable [Ring R] [AddMonoid G]

/-- Multiplying by `T^r` shifts the period filtration of `NovikovSeries R (G × ℝ) (actionPeriod E)`
by `r`. -/
theorem actionMonomial_mul_mem_periodFiltration_iff (E : G →+ ℝ) (r C : ℝ)
    {a : NovikovSeries R (G × ℝ) (actionPeriod E)} :
    actionMonomial R E r * a ∈ periodFiltration R (actionPeriod E) (r + C) ↔
      a ∈ periodFiltration R (actionPeriod E) C := by
  have hT : ∀ s : ℝ, actionMonomial R E s ∈ periodFiltration R (actionPeriod E) s := fun s => by
    simpa [actionMonomial_def] using
      single_mem_periodFiltration (R := R) (N := actionPeriod E) ((0 : G), s) (1 : R)
  refine ⟨fun ha => ?_, fun ha => mul_mem_periodFiltration (hT r) ha⟩
  have hmul := mul_mem_periodFiltration (hT (-r)) ha
  rwa [← mul_assoc, actionMonomial_neg_mul_actionMonomial, one_mul, neg_add_cancel_left] at hmul

variable (R) in
/-- The nonnegative action monomial `T^r` (`0 ≤ r`) in `nonnegSubring R (actionPeriod E)`. -/
def nonnegActionMonomial (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) : nonnegSubring R (actionPeriod E) :=
  nonnegPeriodSection R (actionPeriod_inr E) hr

@[simp]
theorem coe_nonnegActionMonomial (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (nonnegActionMonomial R E hr : NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionMonomial R E r :=
  coe_nonnegPeriodSection (actionPeriod_inr E) hr

@[simp]
theorem nonnegActionMonomial_zero (E : G →+ ℝ) : nonnegActionMonomial R E le_rfl = 1 :=
  nonnegPeriodSection_zero (actionPeriod_inr E)

@[simp]
theorem nonnegActionMonomial_mul (E : G →+ ℝ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    nonnegActionMonomial R E hr * nonnegActionMonomial R E hs =
      nonnegActionMonomial R E (add_nonneg hr hs) :=
  nonnegPeriodSection_mul (actionPeriod_inr E) hr hs

theorem nonnegActionMonomial_mem_posIdeal (E : G →+ ℝ) {r : ℝ} (hr : 0 < r) :
    nonnegActionMonomial R E hr.le ∈ posIdeal R (actionPeriod E) :=
  nonnegPeriodSection_mem_posIdeal (actionPeriod_inr E) hr

/-- For `r > 0` over a nontrivial ring, `T^r` is not a unit of
`nonnegSubring R (actionPeriod E)`, in contrast to `isUnit_actionMonomial` in the localized
ring. -/
theorem not_isUnit_nonnegActionMonomial [Nontrivial R] (E : G →+ ℝ) {r : ℝ} (hr : 0 < r) :
    ¬ IsUnit (nonnegActionMonomial R E hr.le) :=
  not_isUnit_nonnegPeriodSection_of_pos (actionPeriod_inr E) hr

theorem nonnegActionMonomial_mem_nonnegGradeBy_zero [CommSemiring S] [Algebra S R] [AddZeroClass B]
    (E : G →+ ℝ) (μ : G →+ B) {r : ℝ} (hr : 0 ≤ r) :
    nonnegActionMonomial R E hr ∈ nonnegGradeBy S R (actionPeriod E) (actionDegree μ) 0 := by
  rw [← coe_mem_gradeBy_iff, coe_nonnegActionMonomial]
  exact actionMonomial_mem_gradeBy_zero E μ r

variable (R) in
/-- The multiplicative submonoid `{T^r | 0 ≤ r}` of nonnegative action monomials in
`nonnegSubring R (actionPeriod E)`. -/
def actionSubmonoid (E : G →+ ℝ) : Submonoid (nonnegSubring R (actionPeriod E)) :=
  periodSectionSubmonoid R (actionPeriod_inr E)

@[simp]
theorem mem_actionSubmonoid {E : G →+ ℝ} {a : nonnegSubring R (actionPeriod E)} :
    a ∈ actionSubmonoid R E ↔ ∃ (r : ℝ) (hr : 0 ≤ r), a = nonnegActionMonomial R E hr :=
  mem_periodSectionSubmonoid (actionPeriod_inr E)

theorem nonnegActionMonomial_mem_actionSubmonoid (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    nonnegActionMonomial R E hr ∈ actionSubmonoid R E :=
  nonnegPeriodSection_mem_periodSectionSubmonoid (actionPeriod_inr E) hr

/-- `actionSubmonoid R E` equals the submonoid generated by the strictly positive action
monomials `{T^r | 0 < r}`. -/
theorem actionSubmonoid_eq_closure_pos (E : G →+ ℝ) :
    actionSubmonoid R E =
      Submonoid.closure {a | ∃ (r : ℝ) (hr : 0 < r), a = nonnegActionMonomial R E hr.le} :=
  periodSectionSubmonoid_eq_closure_pos (actionPeriod_inr E)

end Ring

section Localization

variable [AddCommMonoid G] [CommRing R]

/-- **Localization of the nonnegative action-weighted Novikov subring.** Localizing
`nonnegSubring R (actionPeriod E)` at `actionSubmonoid R E` recovers the full completed ring
`NovikovSeries R (G × ℝ) (actionPeriod E)`. -/
instance isLocalization_actionSubmonoid (E : G →+ ℝ) :
    IsLocalization (actionSubmonoid R E) (NovikovSeries R (G × ℝ) (actionPeriod E)) :=
  isLocalization_periodSectionSubmonoid (actionPeriod_inr E)

variable (R) in
/-- The canonical `nonnegSubring R (actionPeriod E)`-algebra isomorphism from
`Localization (actionSubmonoid R E)` onto `NovikovSeries R (G × ℝ) (actionPeriod E)`. -/
def actionLocalizationAlgEquiv (E : G →+ ℝ) :
    Localization (actionSubmonoid R E) ≃ₐ[nonnegSubring R (actionPeriod E)]
      NovikovSeries R (G × ℝ) (actionPeriod E) :=
  periodSectionLocalizationAlgEquiv R (actionPeriod_inr E)

theorem actionLocalizationAlgEquiv_algebraMap (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) :
    actionLocalizationAlgEquiv R E
      ((algebraMap (nonnegSubring R (actionPeriod E)) (Localization (actionSubmonoid R E)) :
        _ →+* _) a) = (a : NovikovSeries R (G × ℝ) (actionPeriod E)) :=
  periodSectionLocalizationAlgEquiv_algebraMap (actionPeriod_inr E) a

@[simp]
theorem actionLocalizationAlgEquiv_mk' (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E))
    (s : actionSubmonoid R E) :
    actionLocalizationAlgEquiv R E (IsLocalization.mk' (Localization (actionSubmonoid R E)) a s) =
      IsLocalization.mk' (NovikovSeries R (G × ℝ) (actionPeriod E)) a s :=
  periodSectionLocalizationAlgEquiv_mk' (actionPeriod_inr E) a s

@[simp]
theorem actionLocalizationAlgEquiv_symm_mk' (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E))
    (s : actionSubmonoid R E) :
    (actionLocalizationAlgEquiv R E).symm
      (IsLocalization.mk' (NovikovSeries R (G × ℝ) (actionPeriod E)) a s) =
      IsLocalization.mk' (Localization (actionSubmonoid R E)) a s :=
  periodSectionLocalizationAlgEquiv_symm_mk' (actionPeriod_inr E) a s

@[simp]
theorem actionLocalizationAlgEquiv_mk (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E))
    {r : ℝ} (hr : 0 ≤ r) :
    actionLocalizationAlgEquiv R E (Localization.mk a
      ⟨nonnegActionMonomial R E hr, nonnegActionMonomial_mem_actionSubmonoid E hr⟩) =
      (a : NovikovSeries R (G × ℝ) (actionPeriod E)) * actionMonomial R E (-r) :=
  periodSectionLocalizationAlgEquiv_mk (actionPeriod_inr E) a hr

@[simp]
theorem actionLocalizationAlgEquiv_symm_coe (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) :
    (actionLocalizationAlgEquiv R E).symm (a : NovikovSeries R (G × ℝ) (actionPeriod E)) =
      (algebraMap (nonnegSubring R (actionPeriod E)) (Localization (actionSubmonoid R E)) :
        _ →+* _) a :=
  periodSectionLocalizationAlgEquiv_symm_coe (actionPeriod_inr E) a

@[simp]
theorem actionLocalizationAlgEquiv_symm_actionMonomial_neg (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (actionLocalizationAlgEquiv R E).symm (actionMonomial R E (-r)) = Localization.mk 1
      ⟨nonnegActionMonomial R E hr, nonnegActionMonomial_mem_actionSubmonoid E hr⟩ :=
  periodSectionLocalizationAlgEquiv_symm_single_neg (actionPeriod_inr E) hr

theorem actionLocalizationAlgEquiv_symm_mul_actionMonomial_neg (E : G →+ ℝ)
    (a : nonnegSubring R (actionPeriod E)) {r : ℝ} (hr : 0 ≤ r) :
    (actionLocalizationAlgEquiv R E).symm
      ((a : NovikovSeries R (G × ℝ) (actionPeriod E)) * actionMonomial R E (-r)) = Localization.mk a
        ⟨nonnegActionMonomial R E hr, nonnegActionMonomial_mem_actionSubmonoid E hr⟩ :=
  periodSectionLocalizationAlgEquiv_symm_mul_single_neg (actionPeriod_inr E) a hr

end Localization

end Monomials

/-! ### Inclusion of base coefficients `G → G × ℝ` -/

section BaseInclusion

variable [AddMonoid G]

/-- The inclusion `AddMonoidHom.inl G ℝ : G →+ G × ℝ` preserves periods with rescale factor `1`. -/
theorem exists_period_rescale_inl (E : G →+ ℝ) :
    ∃ c > 0, ∀ g : G, actionPeriod E (AddMonoidHom.inl G ℝ g) = c * E g :=
  ⟨1, one_pos, fun g => by rw [one_mul, actionPeriod_inl]⟩

section Semiring

variable [Semiring R]

variable (R) in
/-- The unital ring homomorphism embedding `NovikovSeries R G E` into
`NovikovSeries R (G × ℝ) (actionPeriod E)` along `g ↦ (g, 0)`. -/
def actionInlRingHom (E : G →+ ℝ) :
    NovikovSeries R G E →+* NovikovSeries R (G × ℝ) (actionPeriod E) :=
  mapRingHom (RingHom.id R) (.inl G ℝ) (exists_period_rescale_inl E)

/-- `actionInlRingHom` is the pushforward `mapRingHom` along `AddMonoidHom.inl G ℝ`. -/
theorem actionInlRingHom_eq_mapRingHom (E : G →+ ℝ) :
    actionInlRingHom R E = mapRingHom (RingHom.id R) (.inl G ℝ) (exists_period_rescale_inl E) :=
  (rfl)

@[simp]
theorem coeff_actionInlRingHom_zero (E : G →+ ℝ) (a : NovikovSeries R G E) (g : G) :
    (actionInlRingHom R E a).coeff (g, 0) = a.coeff g := by
  simpa [actionInlRingHom_eq_mapRingHom, mapRingHom_apply] using
    coeff_map_of_injective (RingHom.id R : R →+ R) (.inl G ℝ) (exists_period_rescale_inl E)
      (Prod.mk_left_injective 0) a g

theorem coeff_actionInlRingHom_of_ne_zero (E : G →+ ℝ) (a : NovikovSeries R G E) (g : G) {r : ℝ}
    (hr : r ≠ 0) : (actionInlRingHom R E a).coeff (g, r) = 0 := by
  rw [actionInlRingHom_eq_mapRingHom, mapRingHom_apply]
  exact coeff_map_eq_zero_of_notMem_range _ _ _ a fun ⟨_, hg'⟩ => hr (congrArg Prod.snd hg').symm

@[simp]
theorem actionInlRingHom_single (E : G →+ ℝ) (g : G) (c : R) :
    actionInlRingHom R E (single g c) = single (g, 0) c := by simp [actionInlRingHom_eq_mapRingHom]

theorem coeff_actionMonomial_mul_actionInlRingHom (E : G →+ ℝ) (r : ℝ) (a : NovikovSeries R G E)
    (g : G) : (actionMonomial R E r * actionInlRingHom R E a).coeff (g, r) = a.coeff g := by
  rw [coeff_actionMonomial_mul, sub_self, coeff_actionInlRingHom_zero]

theorem actionInlRingHom_injective (E : G →+ ℝ) : Injective (actionInlRingHom R E) := fun _ _ h =>
  map_injective (RingHom.id R : R →+ R) (.inl G ℝ) (exists_period_rescale_inl E) injective_id
    (Prod.mk_left_injective 0) (by simpa [actionInlRingHom_eq_mapRingHom, mapRingHom_apply] using h)

/-- `actionInlRingHom` preserves and reflects homogeneity for `μ` and `actionDegree μ`. -/
@[simp]
theorem actionInlRingHom_mem_gradeBy_iff [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B) (b : B)
    {a : NovikovSeries R G E} :
    actionInlRingHom R E a ∈ gradeBy R (actionPeriod E) (actionDegree μ) b ↔
      a ∈ gradeBy R E μ b := by
  rw [mem_gradeBy_iff, mem_gradeBy_iff]
  refine ⟨fun ha g hg => ha <| by rwa [mem_support, coeff_actionInlRingHom_zero, ← mem_support],
    fun ha ⟨g, r⟩ hp => ?_⟩
  rcases eq_or_ne r 0 with rfl | hr
  · rw [Set.mem_preimage, actionDegree_apply]
    exact ha <| by rwa [mem_support, ← coeff_actionInlRingHom_zero E a g, ← mem_support]
  · exact absurd (coeff_actionInlRingHom_of_ne_zero E a g hr) (mem_support.1 hp)

end Semiring

section Ring

variable [Ring R]

@[fun_prop]
theorem continuous_actionInlRingHom (E : G →+ ℝ) : Continuous (actionInlRingHom R E) :=
  continuous_mapRingHom _ _ _

/-- `actionInlRingHom` preserves and reflects every period filtration cutoff `C`. -/
theorem actionInlRingHom_mem_periodFiltration_iff (E : G →+ ℝ) (C : ℝ) {a : NovikovSeries R G E} :
    actionInlRingHom R E a ∈ periodFiltration R (actionPeriod E) C ↔
      a ∈ periodFiltration R E C := by
  refine ⟨fun ha => mem_periodFiltration.2 fun g hg => ?_, fun ha => ?_⟩
  · rw [← coeff_actionInlRingHom_zero E a g]
    exact mem_periodFiltration.1 ha (g, 0) (by simpa using hg)
  · rw [actionInlRingHom_eq_mapRingHom, mapRingHom_apply]
    simpa using map_mem_periodFiltration (RingHom.id R : R →+ R) (.inl G ℝ)
      (exists_period_rescale_inl E) zero_le_one (fun g => by rw [one_mul, actionPeriod_inl]) ha

variable (R) in
/-- The ring homomorphism embedding `nonnegSubring R E` into `nonnegSubring R (actionPeriod E)`
along `g ↦ (g, 0)`. -/
def actionInlNonnegSubring (E : G →+ ℝ) :
    nonnegSubring R E →+* nonnegSubring R (actionPeriod E) :=
  mapNonnegSubring (RingHom.id R) (.inl G ℝ) (exists_period_rescale_inl E)

/-- `actionInlNonnegSubring` is the pushforward `mapNonnegSubring` along
`AddMonoidHom.inl G ℝ`. -/
theorem actionInlNonnegSubring_eq_mapNonnegSubring (E : G →+ ℝ) :
    actionInlNonnegSubring R E =
      mapNonnegSubring (RingHom.id R) (.inl G ℝ) (exists_period_rescale_inl E) := (rfl)

@[simp]
theorem coe_actionInlNonnegSubring (E : G →+ ℝ) (a : nonnegSubring R E) :
    (actionInlNonnegSubring R E a : NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionInlRingHom R E a := by
  rw [actionInlNonnegSubring_eq_mapNonnegSubring, coe_mapNonnegSubring,
    actionInlRingHom_eq_mapRingHom, mapRingHom_apply]

theorem actionInlNonnegSubring_injective (E : G →+ ℝ) : Injective (actionInlNonnegSubring R E) :=
  mapNonnegSubring_injective _ _ _ injective_id (Prod.mk_left_injective 0)

@[fun_prop]
theorem continuous_actionInlNonnegSubring (E : G →+ ℝ) : Continuous (actionInlNonnegSubring R E) :=
  continuous_mapNonnegSubring _ _ _

/-- `actionInlNonnegSubring` preserves and reflects membership in `posIdeal`. -/
theorem actionInlNonnegSubring_mem_posIdeal_iff (E : G →+ ℝ) {a : nonnegSubring R E} :
    actionInlNonnegSubring R E a ∈ posIdeal R (actionPeriod E) ↔ a ∈ posIdeal R E := by
  refine ⟨fun ha => mem_posIdeal.2 fun g hg => ?_, mapNonnegSubring_mem_posIdeal _ _ _⟩
  rw [← coeff_actionInlRingHom_zero E a.1 g, ← coe_actionInlNonnegSubring]
  exact mem_posIdeal.1 ha (g, 0) (by simpa using hg)

/-- `actionInlNonnegSubring` preserves and reflects homogeneity for `μ` and `actionDegree μ`. -/
theorem actionInlNonnegSubring_mem_nonnegGradeBy_iff [CommSemiring S] [Algebra S R]
    [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B) (b : B) {a : nonnegSubring R E} :
    actionInlNonnegSubring R E a ∈ nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b ↔
      a ∈ nonnegGradeBy S R E μ b := by
  rw [← coe_mem_gradeBy_iff, ← coe_mem_gradeBy_iff, coe_actionInlNonnegSubring,
    actionInlRingHom_mem_gradeBy_iff]

end Ring

end BaseInclusion

/-! ### Energy-zero residue after real action extension -/

section ActionResidue

variable [AddGroup G] [Ring R]

/-- The additive equivalence `(actionPeriod E).ker ≃+ G` given by first-coordinate projection,
whose inverse lifts `g` to the zero-energy element `(g, -E g)`. -/
def kerActionPeriodEquiv (E : G →+ ℝ) : (actionPeriod E).ker ≃+ G where
  toFun k := k.1.1
  invFun g := ⟨(g, -E g), by simp [actionPeriod]⟩
  left_inv := fun ⟨⟨_, _⟩, h⟩ => by
    rw [AddMonoidHom.mem_ker, actionPeriod_apply] at h
    exact Subtype.ext (Prod.ext rfl (eq_neg_of_add_eq_zero_right h).symm)
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem kerActionPeriodEquiv_apply (E : G →+ ℝ) (k : (actionPeriod E).ker) :
    kerActionPeriodEquiv E k = k.1.1 := (rfl)

@[simp]
theorem coe_kerActionPeriodEquiv_symm (E : G →+ ℝ) (g : G) :
    ((kerActionPeriodEquiv E).symm g : G × ℝ) = (g, -E g) := (rfl)

variable (R) in
/-- The energy-zero residue homomorphism after real action extension, mapping
`nonnegSubring R (actionPeriod E)` onto the full group ring `AddMonoidAlgebra R G` by reading the
coefficient at `(g, -E g)`. -/
def actionResidueRingHom (E : G →+ ℝ) : nonnegSubring R (actionPeriod E) →+* AddMonoidAlgebra R G :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (kerActionPeriodEquiv E)).toRingHom.comp
    (residueRingHom R (actionPeriod E))

@[simp]
theorem coeff_actionResidueRingHom (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) (g : G) :
    (actionResidueRingHom R E a).coeff g =
      (a : NovikovSeries R (G × ℝ) (actionPeriod E)).coeff (g, -E g) := by
  simp [actionResidueRingHom, Finsupp.equivMapDomain_apply]

variable (R) in
/-- The group-ring section `AddMonoidAlgebra R G →+* nonnegSubring R (actionPeriod E)` sending
`AddMonoidAlgebra.single g r` to `single (g, -E g) r`. -/
def ofActionResidue (E : G →+ ℝ) : AddMonoidAlgebra R G →+* nonnegSubring R (actionPeriod E) :=
  (ofKerAddMonoidAlgebra R (actionPeriod E)).comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (kerActionPeriodEquiv E).symm).toRingHom

@[simp]
theorem ofActionResidue_single (E : G →+ ℝ) (g : G) (r : R) :
    ofActionResidue R E (AddMonoidAlgebra.single g r) =
      ⟨single (g, -E g) r, single_mem_nonnegSubring (by simp [actionPeriod]) r⟩ := by
  simp [ofActionResidue]

@[simp]
theorem actionResidueRingHom_ofActionResidue (E : G →+ ℝ) (x : AddMonoidAlgebra R G) :
    actionResidueRingHom R E (ofActionResidue R E x) = x := by
  simp only [actionResidueRingHom, ofActionResidue, RingHom.comp_apply,
    residueRingHom_ofKerAddMonoidAlgebra, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (AddMonoidAlgebra.mapDomainRingEquiv R (kerActionPeriodEquiv E)).apply_symm_apply x

theorem actionResidueRingHom_surjective (E : G →+ ℝ) : Surjective (actionResidueRingHom R E) :=
  RightInverse.surjective (actionResidueRingHom_ofActionResidue E)

@[simp]
theorem ker_actionResidueRingHom (E : G →+ ℝ) :
    RingHom.ker (actionResidueRingHom R E) = posIdeal R (actionPeriod E) := by
  ext a
  rw [RingHom.mem_ker, actionResidueRingHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_zero_iff, residueRingHom_eq_zero_iff]

variable (R) in
/-- **Energy-zero residue after real action extension.** Quotienting
`nonnegSubring R (actionPeriod E)` by `posIdeal R (actionPeriod E)` gives the full group ring
`AddMonoidAlgebra R G`, via `g ↦ (g, -E g)`. -/
def quotientActionPosIdealEquiv (E : G →+ ℝ) :
    (nonnegSubring R (actionPeriod E) ⧸ posIdeal R (actionPeriod E)) ≃+* AddMonoidAlgebra R G :=
  (quotientPosIdealEquiv R (actionPeriod E)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv R (kerActionPeriodEquiv E))

@[simp]
theorem quotientActionPosIdealEquiv_mk (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) :
    quotientActionPosIdealEquiv R E (Ideal.Quotient.mk (posIdeal R (actionPeriod E)) a) =
      actionResidueRingHom R E a := by
  simp [quotientActionPosIdealEquiv, actionResidueRingHom]

@[simp]
theorem quotientActionPosIdealEquiv_symm_apply (E : G →+ ℝ) (x : AddMonoidAlgebra R G) :
    (quotientActionPosIdealEquiv R E).symm x =
      Ideal.Quotient.mk (posIdeal R (actionPeriod E)) (ofActionResidue R E x) := by
  simp [quotientActionPosIdealEquiv, ofActionResidue]

section Algebra

variable [CommSemiring S] [Algebra S R]

variable (S R) in
/-- The energy-zero residue isomorphism after real action extension as an `S`-algebra
equivalence. -/
def quotientActionPosIdealAlgEquiv (E : G →+ ℝ) :
    (nonnegSubring R (actionPeriod E) ⧸ posIdeal R (actionPeriod E)) ≃ₐ[S] AddMonoidAlgebra R G :=
  (quotientPosIdealAlgEquiv S R (actionPeriod E)).trans
    (AddMonoidAlgebra.domCongr S R (kerActionPeriodEquiv E))

@[simp]
theorem quotientActionPosIdealAlgEquiv_apply (E : G →+ ℝ)
    (q : nonnegSubring R (actionPeriod E) ⧸ posIdeal R (actionPeriod E)) :
    quotientActionPosIdealAlgEquiv S R E q = quotientActionPosIdealEquiv R E q := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [quotientActionPosIdealAlgEquiv, quotientActionPosIdealEquiv, AddMonoidAlgebra.domCongr]

@[simp]
theorem toRingEquiv_quotientActionPosIdealAlgEquiv (E : G →+ ℝ) :
    (quotientActionPosIdealAlgEquiv S R E).toRingEquiv = quotientActionPosIdealEquiv R E :=
  RingEquiv.ext (quotientActionPosIdealAlgEquiv_apply (S := S) E)

theorem quotientActionPosIdealAlgEquiv_mk (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) :
    quotientActionPosIdealAlgEquiv S R E (Ideal.Quotient.mk (posIdeal R (actionPeriod E)) a) =
      actionResidueRingHom R E a := by simp

@[simp]
theorem quotientActionPosIdealAlgEquiv_symm_apply (E : G →+ ℝ) (x : AddMonoidAlgebra R G) :
    (quotientActionPosIdealAlgEquiv S R E).symm x =
      Ideal.Quotient.mk (posIdeal R (actionPeriod E)) (ofActionResidue R E x) := by
  rw [AlgEquiv.symm_apply_eq, quotientActionPosIdealAlgEquiv_apply,
    quotientActionPosIdealEquiv_mk, actionResidueRingHom_ofActionResidue]

end Algebra

/-- The action-weighted residue map reflects units. -/
instance (E : G →+ ℝ) : IsLocalHom (actionResidueRingHom R E) where
  map_nonunit a hu := by
    rw [actionResidueRingHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, MulEquiv.isUnit_map] at hu
    exact isUnit_residueRingHom_iff.1 hu

/-- An element of `nonnegSubring R (actionPeriod E)` is a unit if and only if its energy-zero
residue in `AddMonoidAlgebra R G` is a unit. -/
theorem isUnit_actionResidueRingHom_iff (E : G →+ ℝ) {a : nonnegSubring R (actionPeriod E)} :
    IsUnit (actionResidueRingHom R E a) ↔ IsUnit a :=
  isUnit_map_iff (actionResidueRingHom R E) a

/-- The action-weighted residue map preserves the grading by `μ : G →+ B`. -/
theorem actionResidueRingHom_mem_gradeBy {S R : Type*} [CommSemiring S] [CommRing R] [Algebra S R]
    (E : G →+ ℝ) [AddZeroClass B] (μ : G →+ B) {b : B} {a : nonnegSubring R (actionPeriod E)}
    (ha : a ∈ nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b) :
    actionResidueRingHom R E a ∈ AddMonoidAlgebra.gradeBy R μ b := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro g hg
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_actionResidueRingHom] at hg
  exact mem_nonnegGradeBy_iff.1 ha (mem_support.2 hg)

end ActionResidue

/-! ### Properness of the dense graded subalgebra for infinite degree range -/

section InfiniteDegreeProperness

variable [CommSemiring S] [Ring R] [Nontrivial R] [Algebra S R] [AddMonoid G]

/-- When the degree homomorphism `μ : G →+ B` has infinite range and `R` is nontrivial, there
exists a series in `nonnegSubring R (actionPeriod E)` outside
`⨆ b, nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b`. -/
theorem exists_notMem_iSup_nonnegGradeBy_actionDegree [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B)
    (hμ : (range μ).Infinite) :
    ∃ a : nonnegSubring R (actionPeriod E),
      a ∉ ⨆ b, nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b := by
  let e : ℕ ↪ range μ := hμ.natEmbedding
  choose g hg using fun n : ℕ => (e n).2
  have hμg_inj : Injective fun n : ℕ => μ (g n) := fun m n hmn =>
    e.injective (Subtype.ext <| (hg m).symm.trans (hmn.trans (hg n)))
  -- Pair each chosen class `g n` with an action shift making the total period at least `n`.
  let p : ℕ → G × ℝ := fun n => (g n, (⌈(n : ℝ) - E (g n)⌉₊ : ℝ))
  have hp_inj : Injective p := fun _ _ hmn => hμg_inj (congrArg (μ ∘ Prod.fst) hmn)
  have hp_period : ∀ n : ℕ, (n : ℝ) ≤ actionPeriod E (p n) := fun n => by
    dsimp [p, actionPeriod]; linarith [Nat.le_ceil ((n : ℝ) - E (g n))]
  have hsum : Summable fun n : ℕ =>
      (single (p n) (1 : R) : NovikovSeries R (G × ℝ) (actionPeriod E)) :=
    summable_single_of_tendsto_period <| by
      rw [Nat.cofinite_eq_atTop, tendsto_atTop_atTop]
      exact fun C => ⟨⌈C⌉₊, fun n hn =>
        (Nat.le_ceil C).trans ((Nat.cast_le.2 hn).trans (hp_period n))⟩
  have hmem : (∑' n : ℕ, (single (p n) (1 : R) :
      NovikovSeries R (G × ℝ) (actionPeriod E))) ∈ nonnegSubring R (actionPeriod E) :=
    tsum_mem isClosed_nonnegSubring fun n =>
      single_mem_nonnegSubring ((Nat.cast_nonneg n).trans (hp_period n)) 1
  refine ⟨⟨_, hmem⟩, fun hw => (infinite_range_of_injective hμg_inj)
    ((finite_image_support_of_mem_iSup_nonnegGradeBy hw).subset ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨p k, by rw [mem_support, coeff_tsum_single_of_injective hp_inj hsum k]; exact one_ne_zero,
    rfl⟩

/-- When `μ : G →+ B` has infinite range and `R` is nontrivial, the dense graded submodule
`⨆ b, nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b` is a proper submodule of
`nonnegSubring R (actionPeriod E)`. -/
theorem iSup_nonnegGradeBy_actionDegree_ne_top [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B)
    (hμ : (range μ).Infinite) :
    ⨆ b, nonnegGradeBy S R (actionPeriod E) (actionDegree μ) b ≠ ⊤ := fun htop =>
  let ⟨_, ha⟩ := exists_notMem_iSup_nonnegGradeBy_actionDegree (S := S) (R := R) E μ hμ
  ha (htop ▸ Submodule.mem_top)

/-- When `μ : G →+ B` has infinite range and `R` is nontrivial, the canonical graded algebra
homomorphism `DirectSum.coeAlgHom` into `nonnegSubring R (actionPeriod E)` is not surjective,
even though its range is dense (`denseRange_coeAlgHom_nonnegGradeBy`). -/
theorem not_surjective_coeAlgHom_actionDegree [DecidableEq B] [AddMonoid B] (E : G →+ ℝ)
    (μ : G →+ B) (hμ : (range μ).Infinite) :
    ¬ Surjective (DirectSum.coeAlgHom (nonnegGradeBy S R (actionPeriod E) (actionDegree μ))) :=
  fun hsurj => iSup_nonnegGradeBy_actionDegree_ne_top (S := S) (R := R) E μ hμ <| by
    rw [Submodule.iSup_eq_toSubmodule_range, eq_top_iff]; exact fun a _ => hsurj a

end InfiniteDegreeProperness

end ActionExtension

/-! ### Action specialization into the real Novikov ring -/

section ActionSpecialization

variable {R k G : Type*}

/-- `actionPeriod E : G × ℝ →+ ℝ` preserves periods into `AddMonoidHom.id ℝ` with rescale factor
`1`. -/
theorem exists_period_rescale_actionPeriod [AddZeroClass G] (E : G →+ ℝ) :
    ∃ c > 0, ∀ p : G × ℝ, (AddMonoidHom.id ℝ) (actionPeriod E p) = c * actionPeriod E p :=
  ⟨1, one_pos, fun _ => (one_mul _).symm⟩

section Semiring

variable [Semiring R] [Semiring k] [AddMonoid G]

/-- **Action specialization.** Pushforward of action-weighted Novikov series along
`actionPeriod E : G × ℝ →+ ℝ` and a unital coefficient homomorphism `ρ : R →+* k`, summing the
mapped coefficients along each constant-energy slice `E g + r = t`. -/
def actionSpecialization (ρ : R →+* k) (E : G →+ ℝ) :
    NovikovSeries R (G × ℝ) (actionPeriod E) →+* NovikovSeries k ℝ (AddMonoidHom.id ℝ) :=
  mapRingHom ρ (actionPeriod E) (exists_period_rescale_actionPeriod E)

/-- `actionSpecialization` is the pushforward `mapRingHom` along `actionPeriod E`. -/
theorem actionSpecialization_eq_mapRingHom (ρ : R →+* k) (E : G →+ ℝ) :
    actionSpecialization ρ E =
      mapRingHom ρ (actionPeriod E) (exists_period_rescale_actionPeriod E) := (rfl)

theorem coeff_actionSpecialization (ρ : R →+* k) (E : G →+ ℝ)
    (a : NovikovSeries R (G × ℝ) (actionPeriod E)) (t : ℝ) :
    (actionSpecialization ρ E a).coeff t = ∑ᶠ p ∈ actionPeriod E ⁻¹' {t}, ρ (a.coeff p) := by
  rw [actionSpecialization_eq_mapRingHom, mapRingHom_apply, coeff_map]
  simp only [AddMonoidHom.coe_ofClass]

@[simp]
theorem actionSpecialization_single (ρ : R →+* k) (E : G →+ ℝ) (p : G × ℝ) (c : R) :
    actionSpecialization ρ E (single p c) = single (E p.1 + p.2) (ρ c) := by
  simp [actionSpecialization_eq_mapRingHom]

@[simp]
theorem actionSpecialization_actionMonomial (ρ : R →+* k) (E : G →+ ℝ) (r : ℝ) :
    actionSpecialization ρ E (actionMonomial R E r) = single r 1 := by simp [actionMonomial_def]

end Semiring

section Ring

variable [Ring R] [Ring k] [AddMonoid G]

@[fun_prop]
theorem continuous_actionSpecialization (ρ : R →+* k) (E : G →+ ℝ) :
    Continuous (actionSpecialization ρ E) := continuous_mapRingHom _ _ _

/-- The action specialization sends the period neighbourhood `U_C` into `U'_C`. -/
theorem actionSpecialization_mem_periodFiltration (ρ : R →+* k) (E : G →+ ℝ) {C : ℝ}
    {a : NovikovSeries R (G × ℝ) (actionPeriod E)}
    (ha : a ∈ periodFiltration R (actionPeriod E) C) :
    actionSpecialization ρ E a ∈ periodFiltration k (AddMonoidHom.id ℝ) C := by
  rw [actionSpecialization_eq_mapRingHom, mapRingHom_apply]
  simpa using map_mem_periodFiltration (ρ : R →+ k) (actionPeriod E)
    (exists_period_rescale_actionPeriod E) zero_le_one (fun _ => (one_mul _).symm) ha

/-- The restriction of `actionSpecialization` to the nonnegative subrings. -/
def nonnegActionSpecialization (ρ : R →+* k) (E : G →+ ℝ) :
    nonnegSubring R (actionPeriod E) →+* nonnegSubring k (AddMonoidHom.id ℝ) :=
  mapNonnegSubring ρ (actionPeriod E) (exists_period_rescale_actionPeriod E)

/-- `nonnegActionSpecialization` is the pushforward `mapNonnegSubring` along `actionPeriod E`. -/
theorem nonnegActionSpecialization_eq_mapNonnegSubring (ρ : R →+* k) (E : G →+ ℝ) :
    nonnegActionSpecialization ρ E =
      mapNonnegSubring ρ (actionPeriod E) (exists_period_rescale_actionPeriod E) := (rfl)

@[simp]
theorem coe_nonnegActionSpecialization (ρ : R →+* k) (E : G →+ ℝ)
    (a : nonnegSubring R (actionPeriod E)) :
    (nonnegActionSpecialization ρ E a : NovikovSeries k ℝ (AddMonoidHom.id ℝ)) =
      actionSpecialization ρ E a := by
  rw [nonnegActionSpecialization_eq_mapNonnegSubring, coe_mapNonnegSubring,
    actionSpecialization_eq_mapRingHom, mapRingHom_apply]

@[fun_prop]
theorem continuous_nonnegActionSpecialization (ρ : R →+* k) (E : G →+ ℝ) :
    Continuous (nonnegActionSpecialization ρ E) := continuous_mapNonnegSubring _ _ _

/-- `nonnegActionSpecialization` maps the positive ideal into the positive ideal. -/
theorem nonnegActionSpecialization_mem_posIdeal (ρ : R →+* k) (E : G →+ ℝ)
    {a : nonnegSubring R (actionPeriod E)} (ha : a ∈ posIdeal R (actionPeriod E)) :
    nonnegActionSpecialization ρ E a ∈ posIdeal k (AddMonoidHom.id ℝ) :=
  mapNonnegSubring_mem_posIdeal _ _ _ ha

@[simp]
theorem nonnegActionSpecialization_nonnegActionMonomial (ρ : R →+* k) (E : G →+ ℝ) {r : ℝ}
    (hr : 0 ≤ r) :
    nonnegActionSpecialization ρ E (nonnegActionMonomial R E hr) =
      ⟨single r 1, single_mem_nonnegSubring hr 1⟩ :=
  Subtype.ext <| by simp

/-- `nonnegActionSpecialization` maps every element of `actionSubmonoid R E` into
`realActionSubmonoid k`. -/
theorem nonnegActionSpecialization_mem_realActionSubmonoid (ρ : R →+* k) (E : G →+ ℝ)
    {a : nonnegSubring R (actionPeriod E)} (ha : a ∈ actionSubmonoid R E) :
    nonnegActionSpecialization ρ E a ∈ realActionSubmonoid k := by
  rcases mem_actionSubmonoid.1 ha with ⟨r, hr, rfl⟩
  rw [nonnegActionSpecialization_nonnegActionMonomial]
  exact single_mem_realActionSubmonoid hr

/-- The image of `actionSubmonoid R E` under `nonnegActionSpecialization ρ E` is
`realActionSubmonoid k`. -/
theorem map_actionSubmonoid_nonnegActionSpecialization (ρ : R →+* k) (E : G →+ ℝ) :
    Submonoid.map (nonnegActionSpecialization ρ E).toMonoidHom (actionSubmonoid R E) =
      realActionSubmonoid k := by
  ext b
  simp only [Submonoid.mem_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    mem_actionSubmonoid, mem_realActionSubmonoid]
  exact ⟨fun ⟨_, ⟨r, hr, h⟩, hb⟩ => ⟨r, hr, hb ▸ h ▸
      nonnegActionSpecialization_nonnegActionMonomial ρ E hr⟩,
    fun ⟨r, hr, hb⟩ => ⟨nonnegActionMonomial R E hr, ⟨r, hr, rfl⟩,
      hb ▸ nonnegActionSpecialization_nonnegActionMonomial ρ E hr⟩⟩

end Ring

/-- `actionSpecialization ρ E` is the unique ring homomorphism out of the localized ring
`NovikovSeries R (G × ℝ) (actionPeriod E)` extending `nonnegActionSpecialization ρ E`. -/
theorem eq_actionSpecialization_of_comp_nonneg [AddCommMonoid G] [CommRing R] [Ring k]
    (ρ : R →+* k) (E : G →+ ℝ)
    {φ : NovikovSeries R (G × ℝ) (actionPeriod E) →+* NovikovSeries k ℝ (AddMonoidHom.id ℝ)}
    (hφ : ∀ a : nonnegSubring R (actionPeriod E), φ a = nonnegActionSpecialization ρ E a) :
    φ = actionSpecialization ρ E :=
  IsLocalization.ringHom_ext (actionSubmonoid R E) <|
    RingHom.ext fun a => (hφ a).trans (coe_nonnegActionSpecialization ρ E a)

end ActionSpecialization

end TauCeti.NovikovSeries
