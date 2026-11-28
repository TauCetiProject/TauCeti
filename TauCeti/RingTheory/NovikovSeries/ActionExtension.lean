/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.HomogeneousComponents
public import TauCeti.RingTheory.NovikovSeries.ResidueRing
public import TauCeti.RingTheory.NovikovSeries.Localization

/-!
# Action-weighted Novikov monomials, graded properness, and action specialization

Let `G` be an additive monoid with energy homomorphism `E : G →+ ℝ` and degree map `μ : G → B`.
Adjoining a real action weight produces `G × ℝ` with period `E.coprod (AddMonoidHom.id ℝ)`
(`(g, r) ↦ E g + r`) and pulled-back degree `μ ∘ Prod.fst`. Its action monomials
`T^r = single (0, r) 1` (`TauCeti.NovikovSeries.actionMonomial`) shift the period filtration by
`r` without changing degrees or collapsing distinct classes of equal energy.

Localization of `nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))` at the nonnegative action
monomials and the post-extension residue equivalence onto `AddMonoidAlgebra R G` are established in
`TauCeti.RingTheory.NovikovSeries.Localization` (`isLocalization_monomialSubmonoid_map_inr`) and
`TauCeti.RingTheory.NovikovSeries.ResidueRing` (`residueEquivCoprodId`). Building on those and on
the nonnegative homogeneous components of `TauCeti.RingTheory.NovikovSeries.HomogeneousComponents`,
this file develops:

* **Action monomials and shifted period lattices**: coordinate shifts, invertibility of `T^r` in the
  localized ring versus non-invertibility in `nonnegSubring` for `r > 0`, homogeneity of degree
  `μ 0` (degree zero for additive `μ`), exact filtration shifts `T^r * a ∈ U_(r + C) ↔ a ∈ U_C`,
  and preservation/reflection of `periodFiltration`, `posIdeal`, and homogeneous pieces along the
  base inclusion `g ↦ (g, 0)`.
* **Properness of the dense graded subalgebra**: when `μ : G → B` has infinite range and `R` is
  nontrivial, `⨆ b, nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b` is a proper
  submodule of `nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))`
  (`TauCeti.NovikovSeries.iSup_nonnegGradeBy_coprodId_ne_top`); for an additive degree map
  `μ : G →+ B` into an additive monoid, `DirectSum.coeAlgHom` is therefore dense but not
  surjective (`TauCeti.NovikovSeries.not_surjective_coeAlgHom_nonnegGradeBy_coprodId`).
* **Action specialization**: specializing `TauCeti.NovikovSeries.periodSpecialization` and
  `TauCeti.NovikovSeries.nonnegPeriodSpecialization` (from
  `TauCeti.RingTheory.NovikovSeries.Functoriality`) to `E.coprod (AddMonoidHom.id ℝ)` sends `T^r`
  to `single r 1`, maps the nonnegative action-monomial submonoid onto the nonnegative real-monomial
  submonoid (`TauCeti.NovikovSeries.map_monomialSubmonoid_nonnegPeriodSpecialization_coprodId`), and
  extends uniquely from `nonnegSubring` to the localized ring
  (`TauCeti.NovikovSeries.eq_periodSpecialization_coprodId_of_comp_nonneg`).

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Chapter 2 and Section 6.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovSeries

/-! ### Action monomials `T^r` on `G × ℝ` -/

section Monomials

variable {S R G B : Type*}

section Semiring

variable [Semiring R] [AddMonoid G]

variable (R) in
/-- The action monomial `T^r = single (0, r) 1` in
`NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))`. -/
def actionMonomial (E : G →+ ℝ) (r : ℝ) :
    NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ)) :=
  single (0, r) 1

theorem actionMonomial_def (E : G →+ ℝ) (r : ℝ) : actionMonomial R E r = single (0, r) 1 :=
  (rfl)

@[simp]
theorem coeff_actionMonomial_same (E : G →+ ℝ) (r : ℝ) :
    (actionMonomial R E r).coeff (0, r) = 1 :=
  coeff_single_same (0, r) 1

@[simp]
theorem coeff_actionMonomial_of_ne (E : G →+ ℝ) {r : ℝ} {p : G × ℝ} (hp : p ≠ (0, r)) :
    (actionMonomial R E r).coeff p = 0 :=
  coeff_single_of_ne hp 1

theorem coeff_actionMonomial [DecidableEq G] (E : G →+ ℝ) (r : ℝ) :
    (actionMonomial R E r).coeff = Pi.single (0, r) 1 :=
  coeff_single (0, r) 1

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
  rw [actionMonomial_def, single_mul_single, one_mul]
  congr 1
  ext <;> simp

@[simp]
theorem single_mul_actionMonomial (E : G →+ ℝ) (p : G × ℝ) (c : R) (r : ℝ) :
    single p c * actionMonomial R E r = single (p.1, p.2 + r) c := by
  rw [actionMonomial_def, single_mul_single, mul_one]
  congr 1
  ext <;> simp

/-- Multiplying on the left by the action monomial `T^r` shifts the real coordinate by `r`. -/
theorem coeff_actionMonomial_mul (E : G →+ ℝ) (r : ℝ)
    (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) (p : G × ℝ) :
    (actionMonomial R E r * a).coeff p = a.coeff (p.1, p.2 - r) := by
  have hp : p = (0, r) + (p.1, p.2 - r) :=
    Prod.ext (zero_add p.1).symm (add_sub_cancel r p.2).symm
  have hreg : IsAddLeftRegular ((0 : G), r) := fun _ _ h =>
    Prod.ext (by simpa using congrArg Prod.fst h) (add_left_cancel (congrArg Prod.snd h))
  conv_lhs => rw [hp]
  rw [actionMonomial_def, coeff_single_mul_add hreg, one_mul]

/-- Multiplying on the right by the action monomial `T^r` shifts the real coordinate by `r`. -/
theorem coeff_mul_actionMonomial (E : G →+ ℝ)
    (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) (r : ℝ) (p : G × ℝ) :
    (a * actionMonomial R E r).coeff p = a.coeff (p.1, p.2 - r) := by
  have hp : p = (p.1, p.2 - r) + (0, r) :=
    Prod.ext (add_zero p.1).symm (sub_add_cancel p.2 r).symm
  have hreg : IsAddRightRegular ((0 : G), r) := fun _ _ h =>
    Prod.ext (by simpa using congrArg Prod.fst h) (add_right_cancel (congrArg Prod.snd h))
  conv_lhs => rw [hp]
  rw [actionMonomial_def, coeff_mul_single_add _ hreg, mul_one]

/-- Every real action monomial `T^r` is a unit of
`NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))`, with inverse `T^(-r)`. -/
theorem isUnit_actionMonomial (E : G →+ ℝ) (r : ℝ) : IsUnit (actionMonomial R E r) :=
  isUnit_iff_exists.2 ⟨actionMonomial R E (-r), by simp, by simp⟩

/-- Every real action monomial `T^r` is homogeneous of degree `μ 0` for any first-coordinate degree
map `μ : G → B`. -/
theorem actionMonomial_mem_gradeBy (E : G →+ ℝ) (μ : G → B) (r : ℝ) :
    actionMonomial R E r ∈ gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) (μ 0) :=
  single_mem_gradeBy (N := E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) ((0 : G), r) (1 : R)

/-- Every real action monomial `T^r` is homogeneous of degree `0` for any additive degree
homomorphism `μ : G →+ B`. -/
theorem actionMonomial_mem_gradeBy_zero [AddZeroClass B] (E : G →+ ℝ) (μ : G →+ B) (r : ℝ) :
    actionMonomial R E r ∈
      gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)) 0 := by
  simpa [actionMonomial_def] using
    single_mem_gradeBy (N := E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)) ((0 : G), r) (1 : R)

/-- Multiplying by `T^r` preserves every homogeneous degree piece for `μ.comp (.fst G ℝ)`. -/
theorem actionMonomial_mul_mem_gradeBy [AddMonoid B] (E : G →+ ℝ) (μ : G →+ B) (r : ℝ) {b : B}
    {a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))}
    (ha : a ∈ gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)) b) :
    actionMonomial R E r * a ∈
      gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)) b := by
  simpa using SetLike.GradedMul.mul_mem (actionMonomial_mem_gradeBy_zero E μ r) ha

end Semiring

section Ring

variable [Ring R] [AddMonoid G]

/-- Multiplying by `T^r` shifts the period filtration of
`NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))` by `r`. -/
theorem actionMonomial_mul_mem_periodFiltration_iff (E : G →+ ℝ) (r C : ℝ)
    {a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))} :
    actionMonomial R E r * a ∈ periodFiltration R (E.coprod (AddMonoidHom.id ℝ)) (r + C) ↔
      a ∈ periodFiltration R (E.coprod (AddMonoidHom.id ℝ)) C := by
  have hT : ∀ s : ℝ, actionMonomial R E s ∈
      periodFiltration R (E.coprod (AddMonoidHom.id ℝ)) s := fun s => by
    simpa [actionMonomial_def] using
      single_mem_periodFiltration (R := R) (N := E.coprod (AddMonoidHom.id ℝ)) ((0 : G), s) (1 : R)
  refine ⟨fun ha => ?_, fun ha => mul_mem_periodFiltration (hT r) ha⟩
  have hmul := mul_mem_periodFiltration (hT (-r)) ha
  rwa [← mul_assoc, actionMonomial_mul, neg_add_cancel, actionMonomial_zero, one_mul,
    neg_add_cancel_left] at hmul

variable (R) in
/-- The nonnegative action monomial `T^r` (`0 ≤ r`) in
`nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))`. -/
def nonnegActionMonomial (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)) :=
  ⟨actionMonomial R E r, single_mem_nonnegSubring (by simpa using hr) 1⟩

@[simp]
theorem coe_nonnegActionMonomial (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (nonnegActionMonomial R E hr : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) =
      actionMonomial R E r :=
  (rfl)

@[simp]
theorem nonnegActionMonomial_zero (E : G →+ ℝ) : nonnegActionMonomial R E le_rfl = 1 :=
  Subtype.ext (actionMonomial_zero E)

@[simp]
theorem nonnegActionMonomial_mul (E : G →+ ℝ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    nonnegActionMonomial R E hr * nonnegActionMonomial R E hs =
      nonnegActionMonomial R E (add_nonneg hr hs) :=
  Subtype.ext (actionMonomial_mul E r s)

theorem nonnegActionMonomial_mem_posIdeal (E : G →+ ℝ) {r : ℝ} (hr : 0 < r) :
    nonnegActionMonomial R E hr.le ∈ posIdeal R (E.coprod (AddMonoidHom.id ℝ)) :=
  single_mem_posIdeal (by simpa using hr) 1

/-- For `r > 0` over a nontrivial ring, `T^r` is not a unit of
`nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))`, in contrast to `isUnit_actionMonomial` in the
localized ring. -/
theorem not_isUnit_nonnegActionMonomial [Nontrivial R] (E : G →+ ℝ) {r : ℝ} (hr : 0 < r) :
    ¬ IsUnit (nonnegActionMonomial R E hr.le) :=
  not_isUnit_of_mem_posIdeal (nonnegActionMonomial_mem_posIdeal E hr)

theorem nonnegActionMonomial_mem_nonnegGradeBy_zero [CommSemiring S] [Algebra S R] [AddZeroClass B]
    (E : G →+ ℝ) (μ : G →+ B) {r : ℝ} (hr : 0 ≤ r) :
    nonnegActionMonomial R E hr ∈
      nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)) 0 := by
  rw [← coe_mem_gradeBy_iff, coe_nonnegActionMonomial]
  exact actionMonomial_mem_gradeBy_zero E μ r

/-- Every nonnegative action monomial `T^r` (`r ≥ 0`) belongs to the action-monomial submonoid
`monomialSubmonoid R (E.coprod (.id ℝ)) ((AddSubmonoid.nonneg ℝ).map (.inr G ℝ))`. -/
theorem nonnegActionMonomial_mem_monomialSubmonoid (E : G →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    nonnegActionMonomial R E hr ∈
      monomialSubmonoid R (E.coprod (AddMonoidHom.id ℝ))
        ((AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ)) :=
  mem_monomialSubmonoid.2 ⟨(0, r), AddSubmonoid.mem_map.2 ⟨r, hr, rfl⟩, actionMonomial_def E r⟩

end Ring

/-- Dividing a nonnegative series by `T^r` (`r ≥ 0`) in the localized action-weighted Novikov ring
multiplies it by `T^(-r)`. -/
@[simp]
theorem mk'_nonnegActionMonomial [CommRing R] [AddCommMonoid G] (E : G →+ ℝ)
    (a : nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    IsLocalization.mk' (NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) a
      ⟨nonnegActionMonomial R E hr, nonnegActionMonomial_mem_monomialSubmonoid E hr⟩ =
      (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) * actionMonomial R E (-r) := by
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp [Algebra.algebraMap_ofSubsemiring_apply, mul_assoc]

end Monomials

/-! ### Base inclusion `G → G × ℝ` along `g ↦ (g, 0)` -/

section BaseInclusion

variable {S R G B : Type*} [AddMonoid G]

section Semiring

variable [Semiring R]

@[simp]
theorem coeff_map_inl_zero (E : G →+ ℝ) (a : NovikovSeries R G E) (g : G) :
    (map (AddMonoidHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a).coeff (g, 0) =
      a.coeff g :=
  coeff_map_of_injective (AddMonoidHom.id R) (.inl G ℝ) exists_period_rescale_inl
    (Prod.mk_left_injective 0) a g

theorem coeff_map_inl_of_ne_zero (E : G →+ ℝ) (a : NovikovSeries R G E) (g : G) {r : ℝ}
    (hr : r ≠ 0) :
    (map (AddMonoidHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a).coeff (g, r) =
      0 :=
  coeff_map_eq_zero_of_notMem_range _ _ _ a fun ⟨_, hg'⟩ => hr (congrArg Prod.snd hg').symm

theorem coeff_actionMonomial_mul_mapRingHom_inl (E : G →+ ℝ) (r : ℝ) (a : NovikovSeries R G E)
    (g : G) :
    (actionMonomial R E r *
      mapRingHom (RingHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a).coeff (g, r) =
      a.coeff g := by
  rw [coeff_actionMonomial_mul, sub_self, mapRingHom_apply, RingHom.toAddMonoidHom_id,
    coeff_map_inl_zero]

/-- Pushing forward along `g ↦ (g, 0)` preserves and reflects homogeneity for `μ : G → B`. -/
@[simp]
theorem map_inl_mem_gradeBy_iff (E : G →+ ℝ) (μ : G → B) (b : B)
    {a : NovikovSeries R G E} :
    map (AddMonoidHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a ∈
      gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b ↔
      a ∈ gradeBy R E μ b := by
  rw [mem_gradeBy_iff, mem_gradeBy_iff]
  refine ⟨fun ha g hg => ha <| by rwa [mem_support, coeff_map_inl_zero, ← mem_support],
    fun ha ⟨g, r⟩ hp => ?_⟩
  rcases eq_or_ne r 0 with rfl | hr
  · exact ha <| by rwa [mem_support, ← coeff_map_inl_zero E a g, ← mem_support]
  · exact absurd (coeff_map_inl_of_ne_zero E a g hr) (mem_support.1 hp)

end Semiring

section Ring

variable [Ring R]

/-- Pushing forward along `g ↦ (g, 0)` preserves and reflects every period filtration cutoff `C`. -/
theorem mapRingHom_inl_mem_periodFiltration_iff (E : G →+ ℝ) (C : ℝ) {a : NovikovSeries R G E} :
    mapRingHom (RingHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a ∈
      periodFiltration R (E.coprod (AddMonoidHom.id ℝ)) C ↔
      a ∈ periodFiltration R E C := by
  refine ⟨fun ha => mem_periodFiltration.2 fun g hg => ?_, fun ha => ?_⟩
  · simpa using mem_periodFiltration.1 ha (g, 0) (by simpa using hg)
  · rw [mapRingHom_apply]
    simpa using map_mem_periodFiltration (RingHom.id R : R →+ R) (.inl G ℝ)
      exists_period_rescale_inl zero_le_one (fun g => by simp) ha

/-- Pushing forward along `g ↦ (g, 0)` preserves and reflects membership in `posIdeal`. -/
theorem mapNonnegSubring_inl_mem_posIdeal_iff (E : G →+ ℝ) {a : nonnegSubring R E} :
    mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a ∈
      posIdeal R (E.coprod (AddMonoidHom.id ℝ)) ↔ a ∈ posIdeal R E := by
  refine ⟨fun ha => mem_posIdeal.2 fun g hg => ?_, mapNonnegSubring_mem_posIdeal _ _ _⟩
  simpa using mem_posIdeal.1 ha (g, 0) (by simpa using hg)

/-- Pushing forward along `g ↦ (g, 0)` preserves and reflects nonnegative homogeneity for
`μ : G → B`. -/
theorem mapNonnegSubring_inl_mem_nonnegGradeBy_iff [CommSemiring S] [Algebra S R]
    (E : G →+ ℝ) (μ : G → B) (b : B) {a : nonnegSubring R E} :
    mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a ∈
      nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b ↔
      a ∈ nonnegGradeBy S R E μ b := by
  rw [← coe_mem_gradeBy_iff, ← coe_mem_gradeBy_iff, coe_mapNonnegSubring,
    RingHom.toAddMonoidHom_id, map_inl_mem_gradeBy_iff]

end Ring

end BaseInclusion

/-! ### Properness of the dense graded subalgebra for infinite degree range -/

section InfiniteDegreeProperness

variable {S R G B : Type*} [CommSemiring S] [Ring R] [Nontrivial R] [Algebra S R] [AddMonoid G]

/-- When `μ : G → B` has infinite range and `R` is nontrivial, there exists a series in
`nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))` outside
`⨆ b, nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b`. -/
theorem exists_notMem_iSup_nonnegGradeBy_coprodId (E : G →+ ℝ) (μ : G → B)
    (hμ : (range μ).Infinite) :
    ∃ a : nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)),
      a ∉ ⨆ b, nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b := by
  let e : ℕ ↪ range μ := hμ.natEmbedding
  choose g hg using fun n : ℕ => (e n).property
  have hμg_inj : Injective fun n : ℕ => μ (g n) := fun m n hmn =>
    e.injective (Subtype.ext <| (hg m).symm.trans (hmn.trans (hg n)))
  -- Pair each chosen class `g n` with an action shift making the total period at least `n`.
  let p : ℕ → G × ℝ := fun n => (g n, (⌈(n : ℝ) - E (g n)⌉₊ : ℝ))
  have hp_inj : Injective p := fun _ _ hmn => hμg_inj (congrArg (μ ∘ Prod.fst) hmn)
  have hp_period : ∀ n : ℕ, (n : ℝ) ≤ E.coprod (AddMonoidHom.id ℝ) (p n) := fun n => by
    dsimp [p]
    linarith [Nat.le_ceil ((n : ℝ) - E (g n))]
  let f : ℕ → NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ)) := fun n => single (p n) 1
  have hsum : Summable f :=
    isEnergyFiltration_periodFiltration.summable_of_mem
      (e := fun n : ℕ => E.coprod (AddMonoidHom.id ℝ) (p n))
      (fun n => single_mem_periodFiltration (p n) 1) <| by
        rw [Nat.cofinite_eq_atTop, tendsto_atTop_atTop]
        exact fun C => ⟨⌈C⌉₊, fun n hn =>
          (Nat.le_ceil C).trans ((Nat.cast_le.2 hn).trans (hp_period n))⟩
  have hmem : ∑' n, f n ∈ nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)) :=
    tsum_mem isClosed_nonnegSubring fun n =>
      single_mem_nonnegSubring ((Nat.cast_nonneg n).trans (hp_period n)) 1
  have hcoeff : ∀ k : ℕ, (∑' n, f n).coeff (p k) = 1 := fun k => by
    rw [coeff_eq_finsum_of_hasSum hsum.hasSum (p k),
      finsum_eq_single _ k fun n hnk => coeff_single_of_ne (hp_inj.ne hnk.symm) 1,
      coeff_single_same]
  refine ⟨⟨∑' n, f n, hmem⟩, fun hw => infinite_range_of_injective hμg_inj <|
    (mem_iSup_nonnegGradeBy_iff_finite.1 hw).subset ?_⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨p k, mem_support.2 (by rw [hcoeff k]; exact one_ne_zero), rfl⟩

/-- When `μ : G → B` has infinite range and `R` is nontrivial, the dense graded submodule
`⨆ b, nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b` is proper in
`nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))`. -/
theorem iSup_nonnegGradeBy_coprodId_ne_top (E : G →+ ℝ) (μ : G → B) (hμ : (range μ).Infinite) :
    ⨆ b, nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ ∘ Prod.fst) b ≠ ⊤ :=
  fun htop =>
    let ⟨_, ha⟩ := exists_notMem_iSup_nonnegGradeBy_coprodId (S := S) (R := R) E μ hμ
    ha (htop ▸ Submodule.mem_top)

/-- When `μ : G →+ B` has infinite range and `R` is nontrivial, the canonical graded algebra
homomorphism `DirectSum.coeAlgHom` into `nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))` is not
surjective, even though its range is dense (`denseRange_coeAlgHom_nonnegGradeBy`). -/
theorem not_surjective_coeAlgHom_nonnegGradeBy_coprodId [DecidableEq B] [AddMonoid B] (E : G →+ ℝ)
    (μ : G →+ B) (hμ : (range μ).Infinite) :
    ¬ Surjective
      (DirectSum.coeAlgHom
        (nonnegGradeBy S R (E.coprod (AddMonoidHom.id ℝ)) (μ.comp (.fst G ℝ)))) :=
  fun hsurj => iSup_nonnegGradeBy_coprodId_ne_top (S := S) (R := R) E μ hμ <| by
    rw [← AddMonoidHom.coe_fst (M := G) (N := ℝ), ← AddMonoidHom.coe_comp,
      Submodule.iSup_eq_toSubmodule_range, eq_top_iff]
    exact fun a _ => hsurj a

end InfiniteDegreeProperness

/-! ### Action specialization into the real Novikov ring -/

section ActionSpecialization

variable {R k G : Type*}

@[simp]
theorem periodSpecialization_actionMonomial [Semiring R] [Semiring k] [AddMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) (r : ℝ) :
    periodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ)) (actionMonomial R E r) = single r 1 := by
  simp [actionMonomial_def]

section Ring

variable [Ring R] [Ring k] [AddMonoid G]

@[simp]
theorem nonnegPeriodSpecialization_nonnegActionMonomial (ρ : R →+* k) (E : G →+ ℝ) {r : ℝ}
    (hr : 0 ≤ r) :
    nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ)) (nonnegActionMonomial R E hr) =
      ⟨single r 1, single_mem_nonnegSubring hr 1⟩ :=
  Subtype.ext <| by simp

/-- The image of the nonnegative action-monomial submonoid under
`nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ))` is the submonoid
`monomialSubmonoid k (AddMonoidHom.id ℝ) (AddSubmonoid.nonneg ℝ)` of nonnegative real monomials. -/
theorem map_monomialSubmonoid_nonnegPeriodSpecialization_coprodId (ρ : R →+* k) (E : G →+ ℝ) :
    Submonoid.map (nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ))).toMonoidHom
      (monomialSubmonoid R (E.coprod (AddMonoidHom.id ℝ))
        ((AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ))) =
      monomialSubmonoid k (AddMonoidHom.id ℝ) (AddSubmonoid.nonneg ℝ) := by
  ext b
  simp only [Submonoid.mem_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    mem_monomialSubmonoid, AddSubmonoid.mem_map, AddMonoidHom.inr_apply, AddSubmonoid.mem_nonneg]
  refine ⟨?_, fun ⟨r, hr, hb⟩ => ?_⟩
  · rintro ⟨a, ⟨_, ⟨r, hr, rfl⟩, ha⟩, rfl⟩
    have ha' : a = nonnegActionMonomial R E hr :=
      Subtype.ext (ha.trans (actionMonomial_def E r).symm)
    exact ⟨r, hr, by rw [ha', coe_nonnegPeriodSpecialization, coe_nonnegActionMonomial,
      periodSpecialization_actionMonomial]⟩
  · refine ⟨nonnegActionMonomial R E hr, ⟨(0, r), ⟨r, hr, rfl⟩, actionMonomial_def E r⟩,
      Subtype.ext ?_⟩
    rw [coe_nonnegPeriodSpecialization, coe_nonnegActionMonomial,
      periodSpecialization_actionMonomial, hb]

end Ring

/-- `periodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ))` is the unique ring homomorphism out of
the localized ring `NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))` extending
`nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ))`. -/
theorem eq_periodSpecialization_coprodId_of_comp_nonneg [AddCommMonoid G] [CommRing R] [Ring k]
    (ρ : R →+* k) (E : G →+ ℝ)
    {φ : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ)) →+*
      NovikovSeries k ℝ (AddMonoidHom.id ℝ)}
    (hφ : ∀ a : nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)),
      φ a = nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ)) a) :
    φ = periodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ)) :=
  IsLocalization.ringHom_ext
    (monomialSubmonoid R (E.coprod (AddMonoidHom.id ℝ))
      ((AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ))) <|
    RingHom.ext fun a => (hφ a).trans
      (coe_nonnegPeriodSpecialization ρ (E.coprod (AddMonoidHom.id ℝ)) a)

end ActionSpecialization

end TauCeti.NovikovSeries
