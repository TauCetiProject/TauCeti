/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Orthonormal bases of nonarchimedean normed modules

Let `R` be a normed ring and `M` a normed `R`-module. A family `e : I → M` is *orthonormal*
(`TauCeti.IsOrthonormalFamily R e`) if the norm of every finite linear combination is the maximum
of the norms of its coefficients:

`‖∑ i ∈ s, a i • e i‖ = max_{i ∈ s} ‖a i‖`,

with the empty maximum zero. The condition is on the norms of the scalar coefficients, not on the
norms of the terms `a i • e i`; over a ring the latter, weaker, condition would allow torsion. An
*orthonormal basis* (`TauCeti.IsOrthonormalBasis R e`) is an orthonormal family whose span is
dense. This is neither a Hamel basis nor an orthonormal basis of an inner product space: the
vectors of `M` are the convergent infinite combinations of the `e i`.

The model example is the family of unit coordinate vectors `single i 1` of `C₀(I, R)`
(`TauCeti.isOrthonormalBasis_single_one`), and every orthonormal basis is of this form: over a
complete ring `R` and for a complete ultrametric module `M` with contractive scalar action,

* an orthonormal family `e` defines the linear isometry
  `IsOrthonormalFamily.linearIsometry : C₀(I, R) →ₗᵢ[R] M`, `a ↦ ∑' i, a i • e i`;
* for an orthonormal basis it is surjective, and its inverse
  `IsOrthonormalBasis.repr : M ≃ₗᵢ[R] C₀(I, R)` sends `x` to its coefficients: `x` is the
  unconditional sum of the `repr x i • e i` (`IsOrthonormalBasis.hasSum_repr_smul`), these are its
  only unconditional expansion in the `e i` (`IsOrthonormalBasis.repr_apply_of_hasSum`), and
  `repr (e i) = single i 1`;
* conversely a linear isometry `c : M ≃ₗᵢ[R] C₀(I, R)` pulls the coordinate vectors back to the
  orthonormal basis `i ↦ c.symm (single i 1)`, whose coefficient isometry is `c` again.

Thus a chosen basis and a chosen model isometry determine each other
(`TauCeti.exists_isOrthonormalBasis_iff`), and a module is *orthonormalisable*
(`TauCeti.IsONable R M`), that is linearly isometric to some `C₀(I, R)`, exactly when it has an
orthonormal basis (`TauCeti.isONable_iff_exists_isOrthonormalBasis`); the model spaces themselves
are orthonormalisable for index types in every universe (`TauCeti.isONable_zeroAtInfty`).
Completeness is essential: the finitely supported families in `C₀(ℕ, ℚ_[p])` contain the
coordinate vectors, which are orthonormal with dense span, but they do not form a complete space:
the partial sums of `∑' n, p ^ n • single n 1` are finitely supported, but their limit is not.
Some nondiscreteness of `R` is needed here: over a finite field with the trivial norm, every
family tending to zero is finitely supported.

These characterisations need neither commutativity of `R` nor a norm-one or ultrametric
hypothesis on `R`; the ultrametric inequality is assumed on `M`, where it makes the series
`∑' i, a i • e i` converge.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §2.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ENNReal NNReal ZeroAtInfty

universe u

namespace TauCeti

variable {R I M N : Type*}

section Defs

variable [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M]

variable (R) in
/-- A family `e : I → M` is **orthonormal** if the norm of every finite linear combination
`∑ i ∈ s, a i • e i` is the maximum `s.sup fun i ↦ ‖a i‖₊` of the norms of its coefficients,
with the empty maximum zero. -/
def IsOrthonormalFamily (e : I → M) : Prop :=
  ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊

/-- An orthonormal family is characterized by the norm formula for every finite linear
combination. This is the introduction and elimination interface for `IsOrthonormalFamily`. -/
theorem isOrthonormalFamily_def {e : I → M} :
    IsOrthonormalFamily R e ↔
      ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊ :=
  Iff.rfl

variable (R) in
/-- An **orthonormal basis** of a normed module is an orthonormal family whose span is dense. -/
structure IsOrthonormalBasis (e : I → M) : Prop where
  /-- An orthonormal basis is an orthonormal family. -/
  isOrthonormalFamily : IsOrthonormalFamily R e
  /-- The span of an orthonormal basis is dense. -/
  dense_span : Dense (Submodule.span R (Set.range e) : Set M)

variable (R) in
/-- A normed module is **orthonormalisable** if it is linearly isometric to a model space
`C₀(I, R)` of families on a discrete index type tending to zero along the cofinite filter. -/
def IsONable (M : Type u) [SeminormedAddCommGroup M] [Module R M] : Prop :=
  ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃ₗᵢ[R] C₀(I, R))

variable (R) in
/-- A module is orthonormalisable exactly when it is linearly isometric to `C₀(I, R)` for
some discrete index type `I`. This is the introduction and elimination interface for `IsONable`. -/
theorem isONable_def (M : Type u) [SeminormedAddCommGroup M] [Module R M] :
    IsONable R M ↔
      ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I),
        Nonempty (M ≃ₗᵢ[R] C₀(I, R)) :=
  Iff.rfl

variable (I) in
/-- A model space `C₀(I, R)` is orthonormalisable, for an index type `I` in any universe. -/
theorem isONable_zeroAtInfty [TopologicalSpace I] [DiscreteTopology I] : IsONable R C₀(I, R) :=
  (isONable_def R _).2
    ⟨ULift I, inferInstance, inferInstance, ⟨congrLeft R R Homeomorph.ulift.symm⟩⟩

end Defs

namespace IsOrthonormalFamily

section Seminormed

variable [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M] {e : I → M}

/-- The norm of a finite linear combination of an orthonormal family, as a real number. -/
theorem norm_sum_smul (he : IsOrthonormalFamily R e) (s : Finset I) (a : I → R) :
    ‖∑ i ∈ s, a i • e i‖ = (s.sup fun i ↦ ‖a i‖₊ : ℝ≥0) := by
  rw [← coe_nnnorm, he s a]

/-- A coefficient of a finite linear combination of an orthonormal family has norm at most the
norm of the combination. -/
theorem norm_le_norm_sum_smul (he : IsOrthonormalFamily R e) {s : Finset I} (a : I → R) {i : I}
    (hi : i ∈ s) : ‖a i‖ ≤ ‖∑ i ∈ s, a i • e i‖ := by
  rw [he.norm_sum_smul]
  exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i ↦ ‖a i‖₊) hi)

/-- A multiple of a vector of an orthonormal family has the norm of its coefficient. -/
theorem norm_smul (he : IsOrthonormalFamily R e) (i : I) (r : R) : ‖r • e i‖ = ‖r‖ := by
  simpa using he.norm_sum_smul {i} fun _ ↦ r

/-- A vector of an orthonormal family has the norm of `1 : R`. -/
theorem norm_apply (he : IsOrthonormalFamily R e) (i : I) : ‖e i‖ = ‖(1 : R)‖ := by
  simpa using he.norm_smul i 1

/-- Over a norm-one ring, the vectors of an orthonormal family are unit vectors. -/
theorem norm_apply_eq_one [NormOneClass R] (he : IsOrthonormalFamily R e) (i : I) :
    ‖e i‖ = 1 := by
  rw [he.norm_apply, norm_one]

/-- The image of an orthonormal family under a linear isometry is orthonormal. -/
theorem map [SeminormedAddCommGroup N] [Module R N] (he : IsOrthonormalFamily R e)
    (u : M →ₗᵢ[R] N) : IsOrthonormalFamily R (u ∘ e) := fun s a ↦ by
  simpa [map_sum, map_smul, he s a] using u.nnnorm_map (∑ i ∈ s, a i • e i)

end Seminormed

/-- An orthonormal family over a normed ring is linearly independent. -/
theorem linearIndependent [NormedRing R] [SeminormedAddCommGroup M] [Module R M] {e : I → M}
    (he : IsOrthonormalFamily R e) : LinearIndependent R e := by
  refine linearIndependent_iff'.2 fun s a h i hi ↦ ?_
  have : (s.sup fun i ↦ ‖a i‖₊) = 0 := by rw [← he s a, h, nnnorm_zero]
  exact nnnorm_eq_zero.1 (nonpos_iff_eq_zero.1 (this ▸ Finset.le_sup (f := fun i ↦ ‖a i‖₊) hi))

section LinearIsometry

variable [SeminormedRing R] [NormedAddCommGroup M] [Module R M] {e : I → M}
  (he : IsOrthonormalFamily R e)

include he in
/-- An orthonormal family is bounded. -/
theorem memℓp_infty : Memℓp e ∞ :=
  _root_.memℓp_infty ⟨‖(1 : R)‖, by rintro _ ⟨i, rfl⟩; exact (he.norm_apply i).le⟩

variable [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] [TopologicalSpace I]
  [DiscreteTopology I]

include he in
/-- **Isometric coefficient expansion**: for an orthonormal family `e` and a family `a` tending to
zero, the norm of `∑' i, a i • e i` is the sup norm of `a`. -/
theorem norm_tsum_smul (a : C₀(I, R)) : ‖∑' i, a i • e i‖ = ‖a‖ := by
  have hT : Tendsto (fun s : Finset I ↦ ((s.sup fun i ↦ ‖a i‖₊ : ℝ≥0) : ℝ)) atTop
      (𝓝 ‖∑' i, a i • e i‖) := by
    simpa only [he.norm_sum_smul, SummationFilter.unconditional_filter,
      linearCombination_apply] using
      (hasSum_linearCombination (R := R) ⟨e, he.memℓp_infty⟩ a).norm
  refine le_antisymm (le_of_tendsto' hT fun s ↦ ?_)
    ((norm_le (norm_nonneg _)).2 fun j ↦ ge_of_tendsto hT ?_)
  · rw [← coe_nnnorm a, NNReal.coe_le_coe]
    exact Finset.sup_le fun i _ ↦ NNReal.coe_le_coe.1 (norm_coe_le_norm a i)
  · filter_upwards [eventually_ge_atTop {j}] with s hs
    exact NNReal.coe_le_coe.2 <|
      Finset.le_sup (f := fun i ↦ ‖a i‖₊) (hs (Finset.mem_singleton_self j))

/-- The **coefficient isometry** of an orthonormal family `e` in a complete ultrametric module:
the linear isometry `C₀(I, R) →ₗᵢ[R] M` sending `a` to `∑' i, a i • e i`. Its underlying
continuous linear map is `ZeroAtInftyContinuousMap.linearCombination`. -/
noncomputable def linearIsometry : C₀(I, R) →ₗᵢ[R] M where
  toLinearMap := (linearCombination R ⟨e, he.memℓp_infty⟩).toLinearMap
  norm_map' a := by
    rw [ContinuousLinearMap.coe_coe, linearCombination_apply]
    exact he.norm_tsum_smul a

/-- The coefficient isometry of an orthonormal family is its linear combination map. -/
theorem toContinuousLinearMap_linearIsometry :
    he.linearIsometry.toContinuousLinearMap = linearCombination R ⟨e, he.memℓp_infty⟩ :=
  (rfl)

/-- The value of the coefficient isometry is the sum `∑' i, a i • e i`. -/
theorem linearIsometry_apply (a : C₀(I, R)) : he.linearIsometry a = ∑' i, a i • e i :=
  linearCombination_apply (R := R) ⟨e, he.memℓp_infty⟩ a

/-- The coefficient isometry `he.linearIsometry a` is the unconditional sum of the `a i • e i`. -/
theorem hasSum_linearIsometry (a : C₀(I, R)) :
    HasSum (fun i ↦ a i • e i) (he.linearIsometry a) :=
  hasSum_linearCombination (R := R) ⟨e, he.memℓp_infty⟩ a

/-- The coefficient isometry sends the coordinate vector `single i r` to `r • e i`. -/
@[simp]
theorem linearIsometry_single [DecidableEq I] (i : I) (r : R) :
    he.linearIsometry (single i r) = r • e i :=
  linearCombination_single (R := R) ⟨e, he.memℓp_infty⟩ i r

end LinearIsometry

end IsOrthonormalFamily

namespace IsOrthonormalBasis

/-- The image of an orthonormal basis under a linear isometry equivalence is an orthonormal
basis. -/
theorem map [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module R N] {e : I → M} (he : IsOrthonormalBasis R e)
    (u : M ≃ₗᵢ[R] N) : IsOrthonormalBasis R (u ∘ e) where
  isOrthonormalFamily := he.isOrthonormalFamily.map u.toLinearIsometry
  dense_span := by
    rw [Set.range_comp]
    exact (u.toHomeomorph.isDenseEmbedding.dense_image.2 he.dense_span).mono
      (Submodule.image_span_subset_span u.toLinearEquiv.toLinearMap _)

section Repr

variable [NormedRing R] [CompleteSpace R] [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] [TopologicalSpace I]
  [DiscreteTopology I] {e : I → M} (he : IsOrthonormalBasis R e)

include he in
/-- Over a complete ring, the coefficient isometry of an orthonormal basis is surjective. -/
theorem surjective_linearIsometry : Function.Surjective he.isOrthonormalFamily.linearIsometry := by
  classical
  set f := he.isOrthonormalFamily.linearIsometry
  have hclosed : IsClosed (LinearMap.range f.toLinearMap : Set M) := by
    rw [LinearMap.coe_range]
    exact f.isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span R (Set.range e) ≤ LinearMap.range f.toLinearMap :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun i ↦ ⟨single i 1, by simp [f]⟩
  exact fun x ↦ hclosed.closure_subset_iff.2 hspan (he.dense_span x)

/-- The **coefficient isometry** of an orthonormal basis `e` of a complete ultrametric module
over a complete ring: the linear isometry equivalence `M ≃ₗᵢ[R] C₀(I, R)` sending a vector to
the family of its coefficients in the basis. It is inverse to `a ↦ ∑' i, a i • e i`. -/
noncomputable def repr : M ≃ₗᵢ[R] C₀(I, R) :=
  (LinearIsometryEquiv.ofSurjective he.isOrthonormalFamily.linearIsometry
    he.surjective_linearIsometry).symm

/-- The inverse of the coefficient isometry is the sum `a ↦ ∑' i, a i • e i`. -/
theorem repr_symm_apply (a : C₀(I, R)) :
    he.repr.symm a = he.isOrthonormalFamily.linearIsometry a :=
  (rfl)

/-- **Unconditional expansion in an orthonormal basis**: every vector `x` is the unconditional
sum of the `he.repr x i • e i`. -/
theorem hasSum_repr_smul (x : M) : HasSum (fun i ↦ he.repr x i • e i) x := by
  simpa only [← he.repr_symm_apply, LinearIsometryEquiv.symm_apply_apply] using
    he.isOrthonormalFamily.hasSum_linearIsometry (he.repr x)

/-- The coefficients of the basis vector `e i` are those of the coordinate vector
`single i 1`. -/
@[simp]
theorem repr_self [DecidableEq I] (i : I) : he.repr (e i) = single i 1 :=
  he.repr.symm.injective <| by simp [repr_symm_apply]

/-- **Uniqueness of the expansion in an orthonormal basis**: if `x` is the unconditional sum of
the `a i • e i` for some family `a : I → R`, then `a` is the family of coefficients of `x`. -/
theorem repr_apply_of_hasSum {a : I → R} {x : M} (h : HasSum (fun i ↦ a i • e i) x) (i : I) :
    he.repr x i = a i := by
  have ha : Tendsto a cofinite (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simpa [he.isOrthonormalFamily.norm_smul] using
      tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero
  have hx : he.isOrthonormalFamily.linearIsometry (mkOfDiscrete a ha) = x :=
    (he.isOrthonormalFamily.hasSum_linearIsometry _).unique (by simpa only [coe_mkOfDiscrete])
  rw [← hx, ← he.repr_symm_apply, LinearIsometryEquiv.apply_symm_apply, coe_mkOfDiscrete]

end Repr

end IsOrthonormalBasis

section Model

variable [SeminormedRing R] [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- The unit coordinate vectors `single i 1` form an orthonormal basis of the model space
`C₀(I, R)`. -/
theorem isOrthonormalBasis_single_one : IsOrthonormalBasis R fun i : I ↦ single i (1 : R) where
  isOrthonormalFamily s a := by simpa only [smul_single_one] using nnnorm_sum_single s a
  dense_span := dense_span_single_one

/-- The pullback `i ↦ c.symm (single i 1)` of the coordinate vectors along a linear isometry
`c : M ≃ₗᵢ[R] C₀(I, R)` is an orthonormal basis of `M`. -/
theorem _root_.LinearIsometryEquiv.isOrthonormalBasis_symm_single [SeminormedAddCommGroup M]
    [Module R M] (c : M ≃ₗᵢ[R] C₀(I, R)) : IsOrthonormalBasis R fun i ↦ c.symm (single i 1) :=
  isOrthonormalBasis_single_one.map c.symm

end Model

section ModelRepr

variable [NormedRing R] [CompleteSpace R] [TopologicalSpace I] [DiscreteTopology I]
  [DecidableEq I]

/-- Over a complete ultrametric ring, the coefficient isometry of the coordinate vectors of
`C₀(I, R)` is the identity. -/
@[simp]
theorem repr_isOrthonormalBasis_single_one [IsUltrametricDist R] :
    (isOrthonormalBasis_single_one (R := R) (I := I)).repr = LinearIsometryEquiv.refl R _ := by
  refine LinearIsometryEquiv.ext fun x ↦ ?_
  apply (isOrthonormalBasis_single_one (R := R) (I := I)).repr.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.coe_refl, id,
    IsOrthonormalBasis.repr_symm_apply]
  have h₁ := isOrthonormalBasis_single_one.isOrthonormalFamily.hasSum_linearIsometry (R := R) x
  have h₂ : HasSum (fun i ↦ x i • single i (1 : R)) x := hasSum_smul_single_one x
  exact (h₁.unique h₂).symm

variable [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
  [CompleteSpace M]

/-- The coefficient isometry of the pullback of the coordinate vectors along a linear isometry
`c : M ≃ₗᵢ[R] C₀(I, R)` is `c` itself. -/
@[simp]
theorem _root_.LinearIsometryEquiv.repr_isOrthonormalBasis_symm_single (c : M ≃ₗᵢ[R] C₀(I, R)) :
    c.isOrthonormalBasis_symm_single.repr = c := by
  refine LinearIsometryEquiv.ext fun x ↦ ?_
  apply c.isOrthonormalBasis_symm_single.repr.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, IsOrthonormalBasis.repr_symm_apply]
  refine ((c.isOrthonormalBasis_symm_single.isOrthonormalFamily.hasSum_linearIsometry
    (c x)).unique ?_).symm
  simpa using c.symm.toLinearIsometry.toContinuousLinearMap.hasSum (hasSum_smul_single_one (c x))

end ModelRepr

/-- **Orthonormal bases are model isometries**: over a complete ring, a complete ultrametric
module with contractive scalar action has an orthonormal basis indexed by `I` exactly when it is
linearly isometric to `C₀(I, R)`. -/
theorem exists_isOrthonormalBasis_iff [NormedRing R] [CompleteSpace R] [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] [TopologicalSpace I]
    [DiscreteTopology I] :
    (∃ e : I → M, IsOrthonormalBasis R e) ↔ Nonempty (M ≃ₗᵢ[R] C₀(I, R)) := by
  classical
  exact ⟨fun ⟨_, he⟩ ↦ ⟨he.repr⟩, fun ⟨c⟩ ↦ ⟨_, c.isOrthonormalBasis_symm_single⟩⟩

/-- **Orthonormalisable modules are those with an orthonormal basis**: over a complete ring, a
complete ultrametric module with contractive scalar action is linearly isometric to a model
space `C₀(I, R)` exactly when it has an orthonormal basis. -/
theorem isONable_iff_exists_isOrthonormalBasis [NormedRing R] [CompleteSpace R]
    {M : Type u} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
    [CompleteSpace M] :
    IsONable R M ↔ ∃ (I : Type u) (e : I → M), IsOrthonormalBasis R e := by
  constructor
  · rintro ⟨I, _, _, hc⟩
    obtain ⟨e, he⟩ := exists_isOrthonormalBasis_iff.2 hc
    exact ⟨I, e, he⟩
  · rintro ⟨I, e, he⟩
    let : TopologicalSpace I := ⊥
    have : DiscreteTopology I := ⟨rfl⟩
    exact ⟨I, _, inferInstance, exists_isOrthonormalBasis_iff.1 ⟨e, he⟩⟩

end TauCeti
