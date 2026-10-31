/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Factorization
public import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# A single step of Dirichlet stick breaking

Separate the coordinate `none` of a Dirichlet vector indexed by `Option ι`. It has a Beta
law and is independent of the remaining coordinates after renormalization. Conversely, an
independent Beta variable and Dirichlet vector reconstruct the original Dirichlet law by
allocating the remaining stick to the smaller vector.

The maps are total: splitting a vector with zero remaining sum returns zero in its second
component. For positive shapes and a nonempty remainder this branch is null. The inverse
identities are stated on their natural domains, so the split can be iterated without
discarding the independence information. A one-coordinate remainder is allowed.

The distributional argument uses the Gamma–Dirichlet factorization of the remaining
coordinates and the Gamma–Beta ratio identity.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Split off the `none` coordinate and renormalize the remaining coordinates. -/
def dirichletStickSplit (x : EuclideanSpace ℝ (Option ι)) : ℝ × EuclideanSpace ℝ ι :=
  (x none, dirichletNormalize fun i ↦ x (some i))

/-- Reconstruct a vector by allocating a fraction of the stick to `none` and distributing
the remainder according to the second component. -/
def dirichletStickInsert (z : ℝ × EuclideanSpace ℝ ι) : EuclideanSpace ℝ (Option ι) :=
  (EuclideanSpace.equiv (Option ι) ℝ).symm (Option.elim · z.1 fun i ↦ (1 - z.1) * z.2 i)

/-- The first component of the split is the distinguished coordinate. -/
@[simp]
theorem dirichletStickSplit_fst (x : EuclideanSpace ℝ (Option ι)) :
    (dirichletStickSplit x).1 = x none := (rfl)

/-- The remaining vector is obtained by normalizing the other coordinates. -/
@[simp]
theorem dirichletStickSplit_snd (x : EuclideanSpace ℝ (Option ι)) :
    (dirichletStickSplit x).2 = dirichletNormalize (fun i ↦ x (some i)) := (rfl)

omit [Fintype ι] in
/-- Insertion allocates the first component to the distinguished coordinate. -/
@[simp]
theorem dirichletStickInsert_none (z : ℝ × EuclideanSpace ℝ ι) :
    dirichletStickInsert z none = z.1 := (rfl)

omit [Fintype ι] in
/-- Insertion distributes the remaining mass over the smaller vector. -/
@[simp]
theorem dirichletStickInsert_some (z : ℝ × EuclideanSpace ℝ ι) (i : ι) :
    dirichletStickInsert z (some i) = (1 - z.1) * z.2 i := (rfl)

/-- The stick-splitting map is measurable, including its zero-denominator branch. -/
@[fun_prop]
theorem measurable_dirichletStickSplit : Measurable (dirichletStickSplit (ι := ι)) := by
  unfold dirichletStickSplit
  fun_prop

omit [Fintype ι] in
/-- The stick-insertion map is measurable. -/
@[fun_prop]
theorem measurable_dirichletStickInsert [Finite ι] :
    Measurable (dirichletStickInsert (ι := ι)) := by
  let _ := Fintype.ofFinite ι
  unfold dirichletStickInsert
  refine (EuclideanSpace.equiv (Option ι) ℝ).symm.continuous.measurable.comp
    (measurable_pi_iff.mpr fun i ↦ ?_)
  cases i <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop

/-- Inserting a split vector recovers it when its coordinates sum to one and its remaining
mass is nonzero. -/
@[simp]
theorem dirichletStickInsert_split {x : EuclideanSpace ℝ (Option ι)}
    (hx : ∑ i, x i = 1) (ht : ∑ i, x (some i) ≠ 0) :
    dirichletStickInsert (dirichletStickSplit x) = x := by
  have hsum : 1 - x none = ∑ i, x (some i) := by
    rw [Fintype.sum_option] at hx
    linarith
  ext i
  cases i with
  | none => simp
  | some i => simp [hsum, mul_div_cancel₀ _ ht]

/-- Splitting an inserted unit-sum vector recovers both components when some stick remains. -/
@[simp]
theorem dirichletStickSplit_insert {z : ℝ × EuclideanSpace ℝ ι}
    (hz : ∑ i, z.2 i = 1) (hv : z.1 ≠ 1) :
    dirichletStickSplit (dirichletStickInsert z) = z := by
  apply Prod.ext
  · simp
  · ext i
    simp [hz, sub_ne_zero.mpr (Ne.symm hv)]

variable [Nonempty ι]

/-- A Dirichlet vector splits into an independent Beta fraction and Dirichlet remainder.
The second Beta shape is the sum of the remaining concentration parameters. -/
theorem map_dirichletStickSplit_dirichletMeasure {a : Option ι → ℝ}
    (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map dirichletStickSplit =
      (betaMeasure (a none) (∑ i, a (some i))).prod
        (dirichletMeasure fun i ↦ a (some i)) := by
  -- Factor the remaining Gamma coordinates into independent proportions and total.
  let μ := Measure.pi fun i ↦ gammaMeasure (a (some i)) 1
  let ν := gammaMeasure (a none) 1
  let δ := dirichletMeasure fun i ↦ a (some i)
  let γ := gammaMeasure (∑ i, a (some i)) 1
  have hA : 0 < ∑ i, a (some i) :=
    Finset.sum_pos (fun i _ ↦ ha (some i)) Finset.univ_nonempty
  let _ := isProbabilityMeasure_gammaMeasure (ha none) one_pos
  let _ := isProbabilityMeasure_gammaMeasure hA one_pos
  let _ := isProbabilityMeasureBeta (ha none) hA
  let _ := isProbabilityMeasure_dirichletMeasure (fun i ↦ ha (some i))
  let _ i := isProbabilityMeasure_gammaMeasure (ha (some i)) one_pos
  have htail : μ.map (fun x ↦ (dirichletNormalize x, ∑ i, x i)) = δ.prod γ :=
    map_dirichletNormalize_sum_pi_gammaMeasure (fun i ↦ ha (some i)) one_pos
  -- Reassociate the three factors and apply the Gamma–Beta ratio law to the two totals.
  have hratio : ((δ.prod γ).prod ν).map
      (fun z ↦ (z.2 / (z.2 + z.1.2), z.1.1)) =
      (betaMeasure (a none) (∑ i, a (some i))).prod δ := by
    have hbeta : (γ.prod ν).map (fun z ↦ z.2 / (z.2 + z.1)) =
        betaMeasure (a none) (∑ i, a (some i)) := by
      rw [← Measure.prod_swap (μ := ν) (ν := γ),
        Measure.map_map (by fun_prop) measurable_swap]
      exact map_div_add_gammaMeasure (ha none) hA one_pos
    calc
      _ = (δ.prod (γ.prod ν)).map (fun z ↦ (z.2.2 / (z.2.2 + z.2.1), z.1)) := by
        rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = ((δ.prod (γ.prod ν)).map
          (Prod.map id (fun z : ℝ × ℝ ↦ z.2 / (z.2 + z.1)))).map Prod.swap := by
        rw [Measure.map_map measurable_swap (by fun_prop)]
        rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop),
          Measure.map_id, hbeta, Measure.prod_swap]
  rw [dirichletMeasure_of_pos ha, Measure.map_map measurable_dirichletStickSplit
    measurable_dirichletNormalize, ← Measure.pi_map_piOptionEquivProd]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  -- The measurable Option equivalence has no coordinate simp lemmas; identify its inverse
  -- once with the explicit coordinate insertion used in the normalization calculation.
  have he (z : (ι → ℝ) × ℝ) :
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι ↦ ℝ)).symm z =
        fun i ↦ i.elim z.2 z.1 := by
    funext i
    cases i <;> rfl
  have hp : (μ.prod ν).map
      (Prod.map (fun x ↦ (dirichletNormalize x, ∑ i, x i)) id) = (δ.prod γ).prod ν := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id, htail]
  rw [← hratio, ← hp, Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr ?_
  -- The original grand total is positive almost surely, so renormalizing the tail cancels it.
  have hpos : ∀ᵐ z ∂μ.prod ν, 0 < z.2 + ∑ i, z.1 i := by
    apply Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const (by fun_prop)) |>.mpr
    filter_upwards [ae_pos_sum_pi_gammaMeasure (fun i ↦ a (some i)) (fun _ ↦ 1)] with x hx
    filter_upwards [ae_pos_gammaMeasure (a none) 1] with y hy
    exact add_pos hy hx
  filter_upwards [hpos] with z hz
  have htotal : ∑ i, (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι ↦ ℝ)).symm z i =
      z.2 + ∑ i, z.1 i := by simp [he, Fintype.sum_option]
  apply Prod.ext
  · simp [Function.comp_def, dirichletNormalize_apply, he, Fintype.sum_option]
  · simp only [Function.comp_def, dirichletStickSplit_snd]
    simp only [dirichletNormalize_apply, htotal]
    simpa [div_eq_mul_inv, mul_comm, he] using
      dirichletNormalize_const_mul (inv_ne_zero hz.ne') z.1

/-- An independent Beta fraction and Dirichlet remainder reconstruct the Dirichlet law.
This is the recursive construction underlying stick breaking. -/
theorem map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure {a : Option ι → ℝ}
    (ha : ∀ i, 0 < a i) :
    ((betaMeasure (a none) (∑ i, a (some i))).prod
      (dirichletMeasure fun i ↦ a (some i))).map dirichletStickInsert = dirichletMeasure a := by
  rw [← map_dirichletStickSplit_dirichletMeasure ha,
    Measure.map_map measurable_dirichletStickInsert measurable_dirichletStickSplit]
  calc
    _ = (dirichletMeasure a).map id := by
      apply Measure.map_congr
      filter_upwards [ae_pos_dirichletMeasure ha, ae_sum_eq_one_dirichletMeasure ha] with x hx hs
      exact dirichletStickInsert_split hs
        (Finset.sum_pos (fun i _ ↦ hx (some i)) Finset.univ_nonempty).ne'
    _ = _ := Measure.map_id

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
  {P : Measure Ω} {a : Option ι → ℝ}

/-- Splitting a Dirichlet random vector gives the product of the Beta and remaining Dirichlet
laws. -/
theorem HasLaw.dirichletStickSplit {X : Ω → EuclideanSpace ℝ (Option ι)}
    (hX : HasLaw X (dirichletMeasure a) P) (ha : ∀ i, 0 < a i) :
    HasLaw (fun ω ↦ dirichletStickSplit (X ω))
      ((betaMeasure (a none) (∑ i, a (some i))).prod
        (dirichletMeasure fun i ↦ a (some i))) P :=
  (⟨measurable_dirichletStickSplit.aemeasurable,
    map_dirichletStickSplit_dirichletMeasure ha⟩ : HasLaw _ _ _).comp hX

/-- A Dirichlet coordinate is independent of the normalized remaining coordinates. -/
theorem HasLaw.indepFun_dirichletStickSplit {X : Ω → EuclideanSpace ℝ (Option ι)}
    (hX : HasLaw X (dirichletMeasure a) P) (ha : ∀ i, 0 < a i) :
    IndepFun (fun ω ↦ X ω none)
      (fun ω ↦ dirichletNormalize fun i ↦ X ω (some i)) P := by
  have hA : 0 < ∑ i, a (some i) :=
    Finset.sum_pos (fun i _ ↦ ha (some i)) Finset.univ_nonempty
  let _ := isProbabilityMeasureBeta (ha none) hA
  let _ := isProbabilityMeasure_dirichletMeasure (fun i ↦ ha (some i))
  have hjoint := hX.dirichletStickSplit ha
  let _ : IsProbabilityMeasure P := hjoint.isProbabilityMeasure
  have hfst : HasLaw Prod.fst (betaMeasure (a none) (∑ i, a (some i)))
      ((betaMeasure (a none) (∑ i, a (some i))).prod
        (dirichletMeasure fun i ↦ a (some i))) := measurePreserving_fst.hasLaw
  have hsnd : HasLaw Prod.snd (dirichletMeasure fun i ↦ a (some i))
      ((betaMeasure (a none) (∑ i, a (some i))).prod
        (dirichletMeasure fun i ↦ a (some i))) := measurePreserving_snd.hasLaw
  simpa only [Function.comp_def, dirichletStickSplit_fst, dirichletStickSplit_snd] using
    (indepFun_iff_hasLaw_prodMk_prod (hfst.comp hjoint) (hsnd.comp hjoint)).2 hjoint

/-- Independent Beta and Dirichlet variables give a larger Dirichlet vector by stick insertion.
-/
theorem IndepFun.hasLaw_dirichletStickInsert {V : Ω → ℝ} {Y : Ω → EuclideanSpace ℝ ι}
    (hVY : IndepFun V Y P) (ha : ∀ i, 0 < a i)
    (hV : HasLaw V (betaMeasure (a none) (∑ i, a (some i))) P)
    (hY : HasLaw Y (dirichletMeasure fun i ↦ a (some i)) P) :
    HasLaw (fun ω ↦ dirichletStickInsert (V ω, Y ω)) (dirichletMeasure a) P := by
  have hA : 0 < ∑ i, a (some i) :=
    Finset.sum_pos (fun i _ ↦ ha (some i)) Finset.univ_nonempty
  let _ := isProbabilityMeasureBeta (ha none) hA
  let _ : IsProbabilityMeasure P := hV.isProbabilityMeasure
  exact (⟨measurable_dirichletStickInsert.aemeasurable,
    map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure ha⟩ : HasLaw _ _ _).comp
      (hVY.hasLaw_prod hV hY)

end ProbabilityTheory
