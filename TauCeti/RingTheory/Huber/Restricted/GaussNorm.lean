/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.UnitWeight
public import TauCeti.RingTheory.MvPowerSeries.Rescale
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# The Gauss norm topology on restricted multivariate series

The trivial-weight Huber restricted-series ring and Mathlib's unit-radius restricted-series
subring have the same underlying power series. Their topologies also agree: the Huber topology
requires every coefficient to lie in a prescribed open additive subgroup, while the Gauss norm
measures the supremum of all coefficient norms.

The comparison below is an algebra equivalence continuous in both directions. Over a complete
base it identifies the completed Huber Tate algebra with the Banach algebra of restricted series.
This allows normed-ring results, including Weierstrass division, to be transported to the completed
topological algebra without changing its topology.

More generally, let each weight set be a single multiplicative unit `uᵢ`
(`TauCeti.IsNormMulUnit`), and let `cᵢ = ‖uᵢ‖⁻¹`. The Huber condition `aᵥ ∈ uᵛ · U` says that
`u⁻ᵛ aᵥ ∈ U`, and `‖u⁻ᵛ aᵥ‖ = ‖aᵥ‖ cᵛ`
(`MvPowerSeries.norm_coeff_rescale_units_inv`). So the Huber ring with the weights `{uᵢ}` is the
Gauss-normed ring at the radii `c`, again with the same topology. Radii that are not inverse
norms of multiplicative units of `R` are not reached by such singleton weights.

Over a nontrivially normed field the Gauss-normed algebra is itself a Tate ring, at any positive
polyradii: a constant of norm strictly between `0` and `1` is a pseudouniformiser. At unit radius
its Gauss unit ball is its power-bounded subring, so transporting across the topological ring
comparison identifies the power-bounded subring of `K⟨X₁, …, Xₙ⟩` with `K°⟨X₁, …, Xₙ⟩`, and over
complete `K` identifies the completed integral restricted-series ring `𝒪[K]⟨X₁, …, Xₙ⟩`
bicontinuously with the Gauss unit ball `K⟨X₁, …, Xₙ⟩°`.
For an ultrametric normed algebra `A` over such a field, the structure map `A → A⟨X⟩ ⧸ I` to a
quotient of the unit-radius algebra is then adic for the quotient topology.

The normed series are Mathlib's `MvPowerSeries.IsRestricted.subring`, with the Gauss norm
constructed using William Coram's `MvPowerSeries.gaussNorm` infrastructure; no second series
type or norm is introduced here.

## Main results

* `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`: the identity ring equivalence between
  Huber restricted series and Gauss-normed restricted series, continuous in both directions.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`: the resulting topological
  ring comparison for the Huber completion over a complete coefficient ring.
* `TauCeti.Huber.restrictedMvPowerSeriesGaussAlgEquiv` and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv`: the same comparisons as
  coefficient-algebra equivalences.
* `TauCeti.Huber.isWeightedRestricted_units_iff_isRestricted`: for weights given by
  multiplicative units `uᵢ` with `‖uᵢ‖ * cᵢ = 1`, weighted restrictedness is restrictedness at
  the radii `c`.
* `TauCeti.Huber.weightedRestrictedGaussAlgEquiv`: the identity algebra equivalence between the
  Huber ring with these weights and the Gauss-normed ring at the radii `c`, continuous in both
  directions.
* `TauCeti.Huber.IsTateRing.isRestricted_subring`: over a nontrivially normed field with an
  ultrametric norm, the Gauss-normed algebra of restricted series is a Tate ring.
* `TauCeti.Huber.weightedSubring_powerBoundedSubring_eq`: over a nontrivially normed ultrametric
  field `K`, the power-bounded subring of `K⟨X₁, …, Xₙ⟩` is `K°⟨X₁, …, Xₙ⟩`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionIntegerEquiv`: over a complete nontrivially
  normed ultrametric field `K`, the bicontinuous ring equivalence
  `restrictedMvPowerSeriesCompletion n 𝒪[K] ≃+* Subring.unitClosedBall (K⟨X₁, …, Xₙ⟩)`.
* `RingHom.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion`: unique extension of a
  `K`-compatible homomorphism `𝒪[K]⟨X₁, …, Xₙ⟩ →+* A` to `K⟨X₁, …, Xₙ⟩ →ₐ[K] A`.
* `TauCeti.MvPowerSeries.isAdicHom_algebraMap_isRestrictedSubring_quotient`: for an ultrametric
  normed algebra `A` over a nontrivially normed field, the structure map `A → A⟨X⟩ ⧸ I` is adic
  for the quotient topology.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1, §5.1.3, and §5.2.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138), for the integral-presentation comparison and unique
  extension theorem.
* T. Wedhorn, *Adic Spaces*, §5.6, for the restricted-series topology.
-/

public section

namespace TauCeti.Huber

open Filter
open scoped Topology

section Predicate

variable {n : ℕ} {R : Type*} [NormedRing R]

/-- The topological restrictedness condition is Mathlib's normed restrictedness condition at
unit polyradius. -/
theorem isRestricted_iff_isRestricted_one {f : MvPowerSeries (Fin n) R} :
    IsRestricted f ↔ MvPowerSeries.IsRestricted (fun _ ↦ 1) f := by
  rw [isRestricted_iff_coeff, MvPowerSeries.IsRestricted]
  simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
  exact tendsto_zero_iff_norm_tendsto_zero

end Predicate

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The trivial-weight Huber subring is Mathlib's subring of unit-radius restricted series.
This is an equality of subrings; their topological structures are compared separately below. -/
theorem weightedRestrictedSubring_eq_isRestricted_subring :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight =
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ ↦ 1) := by
  rw [weightedRestrictedSubring_one_weight]
  ext f
  rw [mem_restrictedMvPowerSeriesSubring]
  exact isRestricted_iff_isRestricted_one (f := f)

/-- The identity on underlying series identifies the trivial-weight Huber ring with the
Gauss-normed unit-radius restricted-series ring. -/
noncomputable def restrictedMvPowerSeriesGaussEquiv :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight ≃+*
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  RingEquiv.subringCongr weightedRestrictedSubring_eq_isRestricted_subring

/-- The Gauss comparison preserves the underlying formal power series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussEquiv
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesGaussEquiv f : MvPowerSeries (Fin n) R) = f :=
  RingEquiv.coe_subringCongr_apply weightedRestrictedSubring_eq_isRestricted_subring f

/-- The inverse Gauss comparison also preserves the underlying formal power series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussEquiv_symm
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1)) :
    (restrictedMvPowerSeriesGaussEquiv.symm f : MvPowerSeries (Fin n) R) = f :=
  RingEquiv.coe_subringCongr_apply weightedRestrictedSubring_eq_isRestricted_subring.symm f

/-- The Gauss comparison sends the Huber constant `r` to the constant `r`. -/
@[simp]
theorem restrictedMvPowerSeriesGaussEquiv_weightedC (r : R) :
    restrictedMvPowerSeriesGaussEquiv (n := n)
      (weightedC _ isWeightFamily_one_weight r) = algebraMap R _ r :=
  Subtype.ext (by simp)

/-- The Gauss comparison sends the Huber variable `Xᵢ` to the variable `Xᵢ`. -/
@[simp]
theorem restrictedMvPowerSeriesGaussEquiv_weightedX (i : Fin n) :
    restrictedMvPowerSeriesGaussEquiv (R := R)
      (weightedX _ isWeightFamily_one_weight i) =
        ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ :=
  Subtype.ext (by simp)

/-- The Gauss comparison sends the Huber inclusion of a polynomial to the Gauss-normed
inclusion of the same polynomial. -/
@[simp]
theorem restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom (p : MvPolynomial (Fin n) R) :
    restrictedMvPowerSeriesGaussEquiv (weightedPolynomialHom _ isWeightFamily_one_weight p) =
      TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : Fin n ↦ (1 : ℝ)) p :=
  Subtype.ext (by simp)

/-- The identity Gauss comparison also respects the coefficient-algebra structure. -/
noncomputable def restrictedMvPowerSeriesGaussAlgEquiv :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  AlgEquiv.ofRingEquiv (f := restrictedMvPowerSeriesGaussEquiv) fun r ↦
    Subtype.ext (by simp only [coe_restrictedMvPowerSeriesGaussEquiv,
      algebraMap_weightedRestrictedSubring, coe_weightedC,
      MvPowerSeries.coe_algebraMap_isRestrictedSubring])

/-- The algebra Gauss comparison has the same underlying map as the ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussAlgEquiv :
    ⇑(restrictedMvPowerSeriesGaussAlgEquiv (n := n) (R := R)) =
      ⇑(restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)) := (rfl)

/-- The inverse algebra Gauss comparison has the same map as the inverse ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesGaussAlgEquiv (n := n) (R := R)).symm =
      ⇑(restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)).symm := (rfl)

/-- The Huber restricted-series topology makes the comparison to the Gauss topology continuous.
All coefficients in a sufficiently small open subgroup give a uniformly small Gauss norm. -/
theorem continuous_restrictedMvPowerSeriesGaussEquiv :
    Continuous (restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)) := by
  refine continuous_of_continuousAt_zero restrictedMvPowerSeriesGaussEquiv ?_
  rw [ContinuousAt, map_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let U := IsUltrametricDist.ball_openAddSubgroup R (half_pos hε)
  filter_upwards [(hasBasis_nhds_zero_weightedTopology
    (k := n) (A := R) isWeightFamily_one_weight).mem_of_mem (i := U) trivial] with f hf
  refine lt_of_le_of_lt (MvPowerSeries.norm_le_iff.mpr ?_)
    (half_lt_self hε)
  intro ν
  have h := mem_weightedNhd.mp hf ν
  rw [weightMul_one_weight] at h
  simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
    Finset.prod_const_one, mul_one, dist_zero_right] using (Metric.mem_ball.mp h).le

/-- The inverse comparison is continuous for the Gauss topology. A small Gauss norm places
every coefficient in any prescribed open additive subgroup of the coefficient ring. -/
theorem continuous_restrictedMvPowerSeriesGaussEquiv_symm :
    Continuous (restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)).symm := by
  refine continuous_of_continuousAt_zero restrictedMvPowerSeriesGaussEquiv.symm ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology
    (k := n) (A := R) isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  obtain ⟨ε, hε, hU⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp
    (U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem hε] with f hf
  rw [SetLike.mem_coe, mem_weightedNhd]
  intro ν
  rw [weightMul_one_weight, coe_restrictedMvPowerSeriesGaussEquiv_symm]
  apply hU
  simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, Set.mem_ofPred_eq] using
    (MvPowerSeries.norm_coeff_mul_prod_le f ν).trans_lt hf

section Complete

variable [CompleteSpace R]

/-- Over a complete nonarchimedean normed ring, the completed Huber Tate algebra is the
Gauss-normed ring of unit-radius restricted series. The equivalence is continuous in both
directions by the theorems below. -/
noncomputable def restrictedMvPowerSeriesCompletionGaussEquiv :
    restrictedMvPowerSeriesCompletion n R ≃+*
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesCompletionEquiv n R).trans restrictedMvPowerSeriesGaussEquiv

/-- Over a complete coefficient ring, the completed Gauss comparison is an algebra equivalence.
It composes the completion's coefficient-algebra comparison with the identity on series. -/
noncomputable def restrictedMvPowerSeriesCompletionGaussAlgEquiv :
    restrictedMvPowerSeriesCompletion n R ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesCompletionAlgEquiv n R).trans restrictedMvPowerSeriesGaussAlgEquiv

/-- The completed algebra Gauss comparison has the same map as the completed ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv :
    ⇑(restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := R)) =
      ⇑(restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)) := by
  simp [restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    restrictedMvPowerSeriesCompletionGaussEquiv, AlgEquiv.coe_trans, RingEquiv.coe_trans]

/-- The inverse completed algebra Gauss comparison agrees with the inverse ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := R)).symm =
      ⇑(restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm := by
  funext f
  simp [restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    restrictedMvPowerSeriesCompletionGaussEquiv]

/-- On a series in the dense subring, the completed comparison is the identity on formal
power series, regarded as a unit-radius restricted series. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (f : restrictedMvPowerSeriesCompletion n R) = restrictedMvPowerSeriesGaussEquiv f := by
  simp [restrictedMvPowerSeriesCompletionGaussEquiv]

/-- The inverse completed comparison takes a Gauss-normed restricted series to its canonical
image in the Huber completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1)) :
    restrictedMvPowerSeriesCompletionGaussEquiv.symm f =
      (restrictedMvPowerSeriesGaussEquiv.symm f : restrictedMvPowerSeriesCompletion n R) := by
  simp [restrictedMvPowerSeriesCompletionGaussEquiv]

/-- The completed comparison is continuous from the canonical completion topology to the
Gauss norm topology. -/
theorem continuous_restrictedMvPowerSeriesCompletionGaussEquiv :
    Continuous (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)) :=
  continuous_restrictedMvPowerSeriesGaussEquiv.comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous

/-- The inverse completed comparison is continuous from the Gauss norm topology to the
canonical completion topology. -/
theorem continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm :
    Continuous (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm :=
  uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous.comp
    continuous_restrictedMvPowerSeriesGaussEquiv_symm

/-- Under the completed Gauss comparison, the polynomials in the completed Huber algebra are the
Gauss-normed polynomial inclusion. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_comp_weightedPolynomialHom :
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).toRingHom.comp
        (UniformSpace.Completion.coeRingHom.comp
          (weightedPolynomialHom _ isWeightFamily_one_weight)) =
      (TauCeti.MvPowerSeries.polynomialToRestricted (R := R) fun _ : Fin n ↦ (1 : ℝ)).toRingHom :=
  RingHom.ext fun p ↦ by simp [UniformSpace.Completion.coeRingHom]

/-- The inverse completed Gauss comparison sends the Gauss-normed polynomial inclusion to the
polynomials in the completed Huber algebra. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_polynomialToRestricted :
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm.toRingHom.comp
        (TauCeti.MvPowerSeries.polynomialToRestricted (R := R)
          fun _ : Fin n ↦ (1 : ℝ)).toRingHom =
      UniformSpace.Completion.coeRingHom.comp
        (weightedPolynomialHom (k := n) (A := R) _ isWeightFamily_one_weight) := by
  rw [← restrictedMvPowerSeriesCompletionGaussEquiv_comp_weightedPolynomialHom,
    ← RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

/-- The completed Gauss comparison commutes with the coefficient algebra maps. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap :
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).toRingHom.comp
        (algebraMap R (restrictedMvPowerSeriesCompletion n R)) =
      algebraMap R (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1)) :=
  RingHom.ext fun _ ↦ by simp

/-- The inverse completed Gauss comparison commutes with the coefficient algebra maps. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap :
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm.toRingHom.comp
        (algebraMap R (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1))) =
      algebraMap R (restrictedMvPowerSeriesCompletion n R) := by
  rw [← restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap, ← RingHom.comp_assoc,
    RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

/-- The completed Tate algebra over a complete nonarchimedean normed domain is a domain. -/
instance isDomain_restrictedMvPowerSeriesCompletion [IsDomain R] :
    IsDomain (restrictedMvPowerSeriesCompletion n R) :=
  restrictedMvPowerSeriesCompletionGaussEquiv.toMulEquiv.isDomain _

end Complete

section UnitWeight

/-! ### Weights given by multiplicative units

Let each `u i` be a multiplicative unit (`TauCeti.IsNormMulUnit`) and let `‖u i‖ * c i = 1`.
The Huber ring with the weights `Tᵢ = {u i}` and the Gauss-normed ring at the radii `c` then
have the same underlying power series and the same topology. -/

variable (u : Fin n → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin n → ℝ}
  (hc : ∀ i, ‖(u i : R)‖ * c i = 1)

include hu hc in
/-- **Unit weights encode radii.** A series is restricted for the weights `Tᵢ = {u i}` exactly
when it is restricted at the radii `c`. -/
theorem isWeightedRestricted_units_iff_isRestricted {f : MvPowerSeries (Fin n) R} :
    IsWeightedRestricted (fun i ↦ ({(u i : R)} : Set R)) f ↔ MvPowerSeries.IsRestricted c f := by
  rw [isWeightedRestricted_units_iff, isWeightedRestricted_one_weight_iff,
    tendsto_zero_iff_norm_tendsto_zero, MvPowerSeries.IsRestricted]
  simp only [MvPowerSeries.norm_coeff_rescale_units_inv u hu hc]

include hu hc in
/-- The Huber subring with the unit weights `Tᵢ = {u i}` is Mathlib's subring of series
restricted at the radii `c`. This is an equality of subrings; their topologies are compared
below. -/
theorem weightedRestrictedSubring_units_eq_isRestricted_subring :
    weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u) =
      MvPowerSeries.IsRestricted.subring (R := R) c := by
  ext f
  rw [mem_weightedRestrictedSubring, MvPowerSeries.IsRestricted.mem_subring]
  exact isWeightedRestricted_units_iff_isRestricted u hu hc

/-- The identity on underlying series identifies the Huber ring with the unit weights
`Tᵢ = {u i}` with the Gauss-normed ring of series restricted at the radii `c`, as
coefficient algebras. -/
noncomputable def weightedRestrictedGaussAlgEquiv :
    weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u) ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) c :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.subringCongr (weightedRestrictedSubring_units_eq_isRestricted_subring u hu hc))
    fun r ↦ Subtype.ext (by simp)

/-- The unit-weight Gauss comparison preserves the underlying formal power series. -/
@[simp]
theorem coe_weightedRestrictedGaussAlgEquiv
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    (weightedRestrictedGaussAlgEquiv u hu hc f : MvPowerSeries (Fin n) R) = f := by
  simp [weightedRestrictedGaussAlgEquiv, RingEquiv.coe_subringCongr_apply]

/-- The inverse unit-weight Gauss comparison preserves the underlying formal power series. -/
@[simp]
theorem coe_weightedRestrictedGaussAlgEquiv_symm
    (f : MvPowerSeries.IsRestricted.subring (R := R) c) :
    ((weightedRestrictedGaussAlgEquiv u hu hc).symm f : MvPowerSeries (Fin n) R) = f := by
  simp [weightedRestrictedGaussAlgEquiv, RingEquiv.coe_subringCongr_apply]

/-- The unit-weight Gauss comparison sends the Huber constant `r` to the constant `r`. -/
@[simp]
theorem weightedRestrictedGaussAlgEquiv_weightedC (r : R) :
    weightedRestrictedGaussAlgEquiv u hu hc (weightedC _ (isWeightFamily_units u) r) =
      algebraMap R _ r :=
  Subtype.ext (by simp)

/-- The unit-weight Gauss comparison sends the Huber variable `Xᵢ` to the variable `Xᵢ`. -/
@[simp]
theorem weightedRestrictedGaussAlgEquiv_weightedX (i : Fin n) :
    weightedRestrictedGaussAlgEquiv u hu hc (weightedX _ (isWeightFamily_units u) i) =
      ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ :=
  Subtype.ext (by simp)

variable [∀ i, Fact (0 < c i)]

/-- The unit-weight Gauss comparison is continuous from the Huber topology to the Gauss norm
topology: coefficients of `f(u⁻¹ X)` in a small ball give a small Gauss norm. -/
theorem continuous_weightedRestrictedGaussAlgEquiv :
    Continuous (weightedRestrictedGaussAlgEquiv u hu hc) := by
  refine continuous_of_continuousAt_zero (weightedRestrictedGaussAlgEquiv u hu hc) ?_
  rw [ContinuousAt, map_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let U := IsUltrametricDist.ball_openAddSubgroup R (half_pos hε)
  filter_upwards [(hasBasis_nhds_zero_weightedTopology (isWeightFamily_units u)).mem_of_mem
    (i := U) trivial] with f hf
  refine lt_of_le_of_lt (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
    (half_lt_self hε)
  have h := (mem_weightedNhd_units_iff u).mp hf ν
  rw [coe_weightedRestrictedGaussAlgEquiv,
    ← MvPowerSeries.norm_coeff_rescale_units_inv u hu hc]
  exact (mem_ball_zero_iff.mp h).le

/-- The inverse unit-weight Gauss comparison is continuous: a small Gauss norm places every
coefficient of `f(u⁻¹ X)` in any prescribed open additive subgroup. -/
theorem continuous_weightedRestrictedGaussAlgEquiv_symm :
    Continuous (weightedRestrictedGaussAlgEquiv u hu hc).symm := by
  refine continuous_of_continuousAt_zero (weightedRestrictedGaussAlgEquiv u hu hc).symm ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology (isWeightFamily_units u)).tendsto_right_iff]
  intro U _
  obtain ⟨ε, hε, hU⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp
    (U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem hε] with f hf
  refine (mem_weightedNhd_units_iff u).mpr fun ν ↦ hU ?_
  rw [Set.mem_ofPred_eq, coe_weightedRestrictedGaussAlgEquiv_symm,
    MvPowerSeries.norm_coeff_rescale_units_inv u hu hc]
  exact (MvPowerSeries.norm_coeff_mul_prod_le f ν).trans_lt hf

end UnitWeight

section Tate

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- **The Gauss-normed Tate algebra over a nontrivially normed field is a Tate ring.** Over a
field `K` with a nontrivial ultrametric norm, the ring `K⟨X/c⟩` of restricted power series with
its Gauss norm at positive polyradii `c` is a Tate ring; every constant `ϖ` with `0 < ‖ϖ‖ < 1` is
a pseudouniformiser. -/
instance IsTateRing.isRestricted_subring :
    IsTateRing (MvPowerSeries.IsRestricted.subring (R := K) c) := by
  -- a constant keeps its norm and stays a unit
  obtain ⟨ϖ, h0, h1⟩ := NormedField.exists_norm_lt_one K
  refine IsTateRing.of_isUnit_norm_lt_one
    ((isUnit_iff_ne_zero.mpr (norm_pos_iff.mp h0)).map (algebraMap K _)) ?_
  rwa [norm_algebraMap']

/-- Over a nontrivially normed ultrametric field `K`, the power-bounded subring of `K⟨X₁, …, Xₙ⟩`
is the subring `K°⟨X₁, …, Xₙ⟩` of series with power-bounded coefficients. -/
theorem weightedSubring_powerBoundedSubring_eq (n : ℕ) :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) =
      powerBoundedSubring
        (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) := by
  ext f
  rw [mem_weightedSubring, mem_weightedNhd, mem_powerBoundedSubring,
    ← isPowerBounded_ringEquiv_iff restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv_symm,
    ← mem_powerBoundedSubring, TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall,
    TauCeti.MvPowerSeries.mem_unitClosedBall_iff]
  simp only [weightMul_one_weight, Subring.mem_toAddSubgroup, mem_powerBoundedSubring,
    isPowerBounded_iff_norm_le_one, coe_restrictedMvPowerSeriesGaussEquiv]

end Tate

section IntegerEquiv

/-! ### Comparison with completed integral series and unique extension

Following Bosch, *Lectures on Formal and Rigid Geometry*, §6.4, proof of Lemma 5 (pp. 137–138),
identifying the completed integral restricted-series ring `𝒪[K]⟨X₁, …, Xₙ⟩` with the Gauss unit
ball `K⟨X₁, …, Xₙ⟩°` lets any `K`-compatible ring homomorphism out of `𝒪[K]⟨X₁, …, Xₙ⟩` extend
uniquely to a `K`-algebra homomorphism out of `K⟨X₁, …, Xₙ⟩`. -/

open _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Completed integral restricted series agree with the Gauss unit ball** (Bosch, *Lectures on
Formal and Rigid Geometry*, §6.4, proof of Lemma 5, pp. 137–138). Over a complete nontrivially
normed ultrametric field `K`, `restrictedMvPowerSeriesCompletion n 𝒪[K]` is identified with
`Subring.unitClosedBall (K⟨X₁, …, Xₙ⟩)`, preserving scalar constants from `𝒪[K]`. -/
noncomputable def restrictedMvPowerSeriesCompletionIntegerEquiv (n : ℕ) :
    restrictedMvPowerSeriesCompletion n 𝒪[K] ≃+*
      Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K])).trans restrictedIntegerEquiv

/-- Unfolding `restrictedMvPowerSeriesCompletionIntegerEquiv` as the composite of the completed
Gauss comparison over `𝒪[K]` and `restrictedIntegerEquiv`. -/
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_apply (n : ℕ)
    (f : restrictedMvPowerSeriesCompletion n 𝒪[K]) :
    restrictedMvPowerSeriesCompletionIntegerEquiv n f =
      restrictedIntegerEquiv
        (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K]) f) := (rfl)

/-- On the dense uncompleted subring, `restrictedMvPowerSeriesCompletionIntegerEquiv` acts by
`restrictedIntegerEquiv ∘ restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_coe (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set 𝒪[K]))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionIntegerEquiv n
        (f : restrictedMvPowerSeriesCompletion n 𝒪[K]) =
      restrictedIntegerEquiv (restrictedMvPowerSeriesGaussEquiv (n := n) (R := 𝒪[K]) f) := by
  simp [restrictedMvPowerSeriesCompletionIntegerEquiv]

/-- On the dense uncompleted subring, `restrictedMvPowerSeriesCompletionIntegerEquiv` includes each
coefficient from `𝒪[K]` into `K`. -/
theorem coeff_restrictedMvPowerSeriesCompletionIntegerEquiv_coe (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set 𝒪[K]))
      isWeightFamily_one_weight) (t : Fin n →₀ ℕ) :
    coeff t
        ((restrictedMvPowerSeriesCompletionIntegerEquiv n
            (f : restrictedMvPowerSeriesCompletion n 𝒪[K]) :
          IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) : MvPowerSeries (Fin n) K) =
      coeff t (f : MvPowerSeries (Fin n) 𝒪[K]) := by
  simp

/-- The inverse of `restrictedMvPowerSeriesCompletionIntegerEquiv` takes a series in the Gauss unit
ball to its canonical image in `restrictedMvPowerSeriesCompletion n 𝒪[K]`. -/
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_symm_apply (n : ℕ)
    (f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))) :
    (restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f =
      ((restrictedMvPowerSeriesGaussEquiv (n := n) (R := 𝒪[K])).symm
          (restrictedIntegerEquiv.symm f) :
        restrictedMvPowerSeriesCompletion n 𝒪[K]) := by
  simp [restrictedMvPowerSeriesCompletionIntegerEquiv]

/-- `restrictedMvPowerSeriesCompletionIntegerEquiv` maps constants in `𝒪[K]` to constant series in
`K⟨X₁, …, Xₙ⟩°`. -/
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap (n : ℕ) (c : 𝒪[K]) :
    restrictedMvPowerSeriesCompletionIntegerEquiv n (algebraMap 𝒪[K] _ c) =
      unitClosedBallCoeffHom (integerUnitClosedBallEquiv c) := by
  simp

/-- The inverse of `restrictedMvPowerSeriesCompletionIntegerEquiv` sends constant series in
`K⟨X₁, …, Xₙ⟩°` back to constants in `𝒪[K]`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_symm_unitClosedBallCoeffHom (n : ℕ)
    (c : Subring.unitClosedBall K) :
    (restrictedMvPowerSeriesCompletionIntegerEquiv n).symm
        (unitClosedBallCoeffHom (σ := Fin n) c) =
      algebraMap 𝒪[K] _ (integerUnitClosedBallEquiv.symm c) := by
  apply (restrictedMvPowerSeriesCompletionIntegerEquiv n).injective
  rw [RingEquiv.apply_symm_apply, restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap,
    RingEquiv.apply_symm_apply]

/-- Under `restrictedMvPowerSeriesCompletionIntegerEquiv`, the polynomial inclusion into
`𝒪[K]⟨X₁, …, Xₙ⟩` corresponds to `restrictedIntegerEquiv ∘ polynomialToRestricted`. -/
theorem restrictedMvPowerSeriesCompletionIntegerEquiv_comp_weightedPolynomialHom (n : ℕ) :
    (restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).toRingHom.comp
        (UniformSpace.Completion.coeRingHom.comp
          (weightedPolynomialHom _ isWeightFamily_one_weight)) =
      (restrictedIntegerEquiv (σ := Fin n) (K := K)).toRingHom.comp
        (polynomialToRestricted (R := 𝒪[K]) fun _ : Fin n ↦ (1 : ℝ)).toRingHom :=
  RingHom.ext fun p ↦ by
    simp [restrictedMvPowerSeriesCompletionIntegerEquiv_apply, UniformSpace.Completion.coeRingHom]

/-- `restrictedMvPowerSeriesCompletionIntegerEquiv` is continuous from the completion topology on
`𝒪[K]⟨X₁, …, Xₙ⟩` to the subspace Gauss-norm topology on `K⟨X₁, …, Xₙ⟩°`. -/
theorem continuous_restrictedMvPowerSeriesCompletionIntegerEquiv (n : ℕ) :
    Continuous (restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n) := by
  have hisom : Isometry (restrictedIntegerEquiv (σ := Fin n) (K := K)) :=
    AddMonoidHomClass.isometry_of_norm _ fun f ↦ by
      rw [AddSubgroupClass.coe_norm, norm_restrictedIntegerEquiv]
  exact hisom.continuous.comp
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K]))

/-- The inverse of `restrictedMvPowerSeriesCompletionIntegerEquiv` is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionIntegerEquiv_symm (n : ℕ) :
    Continuous (restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).symm := by
  have hisom : Isometry (restrictedIntegerEquiv (σ := Fin n) (K := K)).symm :=
    AddMonoidHomClass.isometry_of_norm _ fun f ↦ by
      rw [← norm_restrictedIntegerEquiv, RingEquiv.apply_symm_apply, AddSubgroupClass.coe_norm]
  exact (continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm (n := n) (R := 𝒪[K])).comp
    hisom.continuous

/-- **Unique extension of an integral presentation to a `K`-algebra Tate homomorphism** (Bosch,
*Lectures on Formal and Rigid Geometry*, §6.4, proof of Lemma 5, pp. 137–138). Let `K` be a
complete nontrivially normed ultrametric field, `A` a commutative `K`-algebra, and
`φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A` a ring homomorphism compatible with
`algebraMap K A` on `𝒪[K]`. Then there is a unique `K`-algebra homomorphism
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` extending
`φ ∘ (restrictedMvPowerSeriesCompletionIntegerEquiv n).symm` on `K⟨X₁, …, Xₙ⟩°`, and its Gauss
unit-ball image `(Subring.unitClosedBall _).map π.toRingHom` equals `φ.range`. -/
theorem _root_.RingHom.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A]
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A)
    (hφ_alg : ∀ c : 𝒪[K], φ (algebraMap 𝒪[K] _ c) = algebraMap K A c) :
    ∃! π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A,
      (∀ f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
        π f = φ ((restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f)) ∧
      (Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map
          π.toRingHom = φ.range := by
  -- Transport `φ` to a `K°`-compatible ring homomorphism on `K⟨X₁, …, Xₙ⟩°`.
  let e := restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n
  let ψ : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) →+* A :=
    φ.comp e.symm.toRingHom
  have hψ (c : Subring.unitClosedBall K) :
      ψ (unitClosedBallCoeffHom c) = algebraMap K A (c : K) := by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedMvPowerSeriesCompletionIntegerEquiv_symm_unitClosedBallCoeffHom,
      hφ_alg, coe_integerUnitClosedBallEquiv_symm]
  -- Extend uniquely from `K⟨X₁, …, Xₙ⟩°` to `K⟨X₁, …, Xₙ⟩` and compute the unit-ball image.
  obtain ⟨π, hπ_ball, hπ_uniq⟩ := ψ.existsUnique_algHom_of_unitClosedBall hψ
  have hπ_eq (f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))) :
      π f = φ (e.symm f) := by
    simpa only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using hπ_ball f
  have hmap :
      (Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map
          π.toRingHom = φ.range := by
    ext a
    simp only [Subring.mem_map, RingHom.mem_range]
    refine ⟨fun ⟨f, hf, hfa⟩ ↦ ⟨e.symm ⟨f, hf⟩, by
        simpa only [← hfa, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using (hπ_eq ⟨f, hf⟩).symm⟩,
      fun ⟨w, hw⟩ ↦ ⟨e w, (e w).property, by
        simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e.symm_apply_apply, hw] using
          hπ_eq (e w)⟩⟩
  exact ⟨π, ⟨hπ_eq, hmap⟩, fun π' ⟨hπ', _⟩ ↦ hπ_uniq π' fun f ↦ by
    simpa only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using hπ' f⟩

end IntegerEquiv

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

variable (K : Type*) [NontriviallyNormedField K] {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
  [IsUltrametricDist A] {m : ℕ}

include K in
/-- The structure map `A → A⟨X₁, …, Xₘ⟩ ⧸ I` is adic for the quotient topology. This supplies
the adicness hypotheses under which `TauCeti.Huber.CompletedTensor` forms the completed tensor
product of two such quotients over `A`. -/
theorem isAdicHom_algebraMap_isRestrictedSubring_quotient
    (I : Ideal (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1))) :
    IsAdicHom (algebraMap A (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ I)) := by
  have : IsTateRing A := IsTateRing.of_normedAlgebra K A
  have : IsTateRing (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)) :=
    IsTateRing.of_normedAlgebra K _
  rw [IsScalarTower.algebraMap_eq A (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)),
    Ideal.Quotient.algebraMap_eq]
  exact (IsAdicHom.of_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk _)).comp
    (IsAdicHom.of_isTateRing isometry_algebraMap_isRestrictedSubring.continuous)

end TauCeti.MvPowerSeries
