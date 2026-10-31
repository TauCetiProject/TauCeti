/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.Polar.Isometry
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Transport
public import TauCeti.RepresentationTheory.Compact.UnitaryModel

/-!
# Polar normalization and invariant compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real inner product space `V`. The inner
product represents `ω` by the skew-adjoint operator `A = ω.innerOperator`, with
`⟪A u, v⟫ = ω u v`. Its polar decomposition `A = J |A|` has a positive invertible modulus
`|A| = √(-A²)` commuting with `A`, and its polar factor `J` is an orthogonal complex structure:
`J² = -1`. This **polar normalization** `ω.polarComplexStructure` is compatible with `ω`, and its
compatible metric is `ω(u, J v) = ⟪|A| u, v⟫`. When the inner product already is the metric
`ω(·, J ·)` of a compatible `J`, polar normalization returns that `J`.

Unlike the hyperbolic-pair construction of `TauCeti.SymplecticForm.exists_compatible`, polar
normalization involves no choices: it is natural for linear isometries. A linear isometric
equivalence `e : V ≃ₗᵢ[ℝ] W` with `e^* ω₂ = ω₁` intertwines the two polar complex structures.
This is what makes it the right tool for symmetric situations: averaging an arbitrary
compatible `J` over a group does not preserve `J² = -1`, but averaging the inner product does
preserve positivity, and the polar normalization of an invariant inner product is invariant.

Combined with Weyl's unitarian trick, this gives the main result: for a continuous linear action
`π` of a compact group `G` preserving a symplectic form `ω` on a finite-dimensional real normed
space `E`, with no inner product given, there is a compatible complex structure `J` for which
every `π g` is complex linear. The compatible metric `ω(·, J ·)` is then `G`-invariant too, by
`TauCeti.SymplecticForm.associatedBilinForm_apply_apply_of_isComplexLinearMap`. So `π` becomes a
unitary representation on the complex vector space `(E, J)`; this is the linear input for the
weight decomposition of the isotropy representation of a compact torus at a fixed point.

## Main definitions

* `TauCeti.SymplecticForm.innerOperator ω`: the operator `A` with `⟪A u, v⟫ = ω u v`.
* `TauCeti.SymplecticForm.polarComplexStructure ω`: the polar factor of `A`, an almost complex
  structure compatible with `ω`.

## Main results

* `TauCeti.SymplecticForm.compatible_polarComplexStructure`: the polar normalization is
  compatible with `ω`.
* `TauCeti.SymplecticForm.apply_polarComplexStructure`: its compatible metric is `⟪|A| ·, ·⟫`.
* `TauCeti.SymplecticForm.polarComplexStructure_eq_of_apply_eq_inner`: polar normalization fixes
  a compatible structure whose metric is the inner product.
* `TauCeti.SymplecticForm.innerOperator_transport`,
  `TauCeti.SymplecticForm.polarComplexStructure_transport`,
  `TauCeti.SymplecticForm.IsSymplectomorphism.polarComplexStructure_apply`: naturality under
  linear isometric equivalences.
* `TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap`: a symplectic continuous
  representation of a compact group preserves some compatible complex structure.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 2.5 (compatible complex structures from a metric by polar
  decomposition, and their naturality).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 12 (compatible linear structures by polar decomposition).
* D. Bump, *Lie Groups*, second edition, Graduate Texts in Mathematics 225, Springer, 2013,
  Chapter 2 (invariant inner products for compact groups).
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-! ### The operator of a symplectic form -/

/-- The operator `A` representing a symplectic form through the inner product:
`⟪A u, v⟫ = ω u v` (`TauCeti.SymplecticForm.inner_innerOperator_apply`). It is skew-adjoint
and injective. -/
noncomputable def innerOperator (ω : SymplecticForm V) : V →ₗ[ℝ] V :=
  ω.toBilinForm.symmCompOfNondegenerate (innerₗ V) nondegenerate_inner

/-- The defining property of the operator of `ω`: `⟪A u, v⟫ = ω u v`. -/
@[simp]
theorem inner_innerOperator_apply (ω : SymplecticForm V) (u v : V) :
    ⟪ω.innerOperator u, v⟫ = ω u v := by
  rw [← innerₗ_apply_apply]
  exact ω.toBilinForm.symmCompOfNondegenerate_left_apply nondegenerate_inner v u

/-- The operator of `ω` is the only operator `A` with `⟪A u, v⟫ = ω u v`. -/
theorem eq_innerOperator_iff (ω : SymplecticForm V) {A : V →ₗ[ℝ] V} :
    A = ω.innerOperator ↔ ∀ u v, ⟪A u, v⟫ = ω u v := by
  refine ⟨fun h u v ↦ by rw [h, inner_innerOperator_apply], fun h ↦ ?_⟩
  exact LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by rw [h, inner_innerOperator_apply]

/-- The operator of `ω` on the right of the inner product: `⟪u, A v⟫ = -ω u v`. -/
@[simp]
theorem inner_apply_innerOperator (ω : SymplecticForm V) (u v : V) :
    ⟪u, ω.innerOperator v⟫ = -ω u v := by
  rw [real_inner_comm, inner_innerOperator_apply, ω.neg_eq]

/-- The operator of a symplectic form is skew-adjoint. -/
theorem adjoint_innerOperator (ω : SymplecticForm V) :
    LinearMap.adjoint ω.innerOperator = -ω.innerOperator :=
  LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    rw [LinearMap.adjoint_inner_left, inner_apply_innerOperator, LinearMap.neg_apply,
      inner_neg_left, inner_innerOperator_apply]

/-- The operator of a symplectic form is injective, by nondegeneracy. -/
theorem innerOperator_injective (ω : SymplecticForm V) : Function.Injective ω.innerOperator := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  refine fun u hu ↦ ω.separatingLeft u fun v ↦ ?_
  have h := (ω.inner_innerOperator_apply u v).symm
  rwa [hu, inner_zero_left] at h

/-! ### Polar normalization

Write `A` for the operator of `ω`, `P = |A|` for its modulus and `U` for its polar factor, so
that `U P = A`. Since `A` is skew-adjoint and injective, `P² = A† A = -A²` is invertible, `U`
commutes with `P` and with `A`, and `U² = -1`
(`LinearMap.polarFactor_mul_self_of_adjoint_eq_neg`). -/

/-- The **polar normalization** of a symplectic form: the polar factor `J` of its operator `A`,
so that `A = J |A|`. It is an almost complex structure compatible with `ω`
(`TauCeti.SymplecticForm.compatible_polarComplexStructure`) and orthogonal for the inner
product. It depends on the inner product of `V`, naturally under linear isometries
(`TauCeti.SymplecticForm.polarComplexStructure_transport`). -/
noncomputable def polarComplexStructure (ω : SymplecticForm V) : AlmostComplexStructure V where
  toLinearMap := ω.innerOperator.polarFactor
  square_neg := by
    rw [← Module.End.mul_eq_comp, LinearMap.polarFactor_mul_self_of_adjoint_eq_neg
      ω.innerOperator_injective ω.adjoint_innerOperator, Module.End.one_eq_id]

/-- The polar normalization of `ω` is the polar factor of the operator of `ω`. -/
theorem polarComplexStructure_toLinearMap (ω : SymplecticForm V) :
    ω.polarComplexStructure.toLinearMap = ω.innerOperator.polarFactor :=
  (rfl)

/-- The polar decomposition `A = J |A|` of the operator of `ω`. -/
@[simp]
theorem polarComplexStructure_apply_operatorAbs (ω : SymplecticForm V) (v : V) :
    ω.polarComplexStructure (ω.innerOperator.operatorAbs v) = ω.innerOperator v :=
  LinearMap.congr_fun ω.innerOperator.polarFactor_comp_operatorAbs v

/-- The polar normalization of `ω` commutes with the operator of `ω`. -/
theorem polarComplexStructure_apply_innerOperator (ω : SymplecticForm V) (v : V) :
    ω.polarComplexStructure (ω.innerOperator v) = ω.innerOperator (ω.polarComplexStructure v) :=
  LinearMap.congr_fun
    (LinearMap.commute_polarFactor_of_commute
      (LinearMap.commute_operatorAbs_of_adjoint_eq_neg ω.adjoint_innerOperator)).eq v

/-- The polar normalization is orthogonal: `⟪J u, J v⟫ = ⟪u, v⟫`. -/
@[simp]
theorem inner_polarComplexStructure_apply_apply (ω : SymplecticForm V) (u v : V) :
    ⟪ω.polarComplexStructure u, ω.polarComplexStructure v⟫ = ⟪u, v⟫ := by
  rw [polarComplexStructure_toLinearMap,
    ← LinearMap.coe_polarIsometry _ ω.innerOperator_injective]
  exact (ω.innerOperator.polarIsometry ω.innerOperator_injective).inner_map_map u v

/-- The compatible metric of the polar normalization is the modulus of the operator of `ω`:
`ω(u, J v) = ⟪|A| u, v⟫`. -/
theorem apply_polarComplexStructure (ω : SymplecticForm V) (u v : V) :
    ω u (ω.polarComplexStructure v) = ⟪ω.innerOperator.operatorAbs u, v⟫ := by
  rw [← inner_innerOperator_apply, ← polarComplexStructure_apply_operatorAbs,
    inner_polarComplexStructure_apply_apply]

/-- **Polar normalization is compatible.** The polar factor of the operator of `ω` is an almost
complex structure compatible with `ω`. -/
theorem compatible_polarComplexStructure (ω : SymplecticForm V) :
    ω.Compatible ω.polarComplexStructure := by
  refine Compatible.of_tames ((ω.invariant_iff _).mpr fun u v ↦ ?_) fun v hv ↦ ?_
  · rw [← inner_innerOperator_apply, ← polarComplexStructure_apply_innerOperator,
      inner_polarComplexStructure_apply_apply, inner_innerOperator_apply]
  · -- `ω(v, J v) = ⟪|A| v, v⟫ = ‖√|A| v‖²`, and `√|A| v ≠ 0` since `|A|` is injective.
    have hP := ω.innerOperator.isPositive_operatorAbs
    have hsqrt : hP.sqrt v ≠ 0 := by
      rw [ne_eq, ← LinearMap.mem_ker, hP.ker_sqrt, LinearMap.ker_operatorAbs,
        LinearMap.ker_eq_bot.mpr ω.innerOperator_injective, Submodule.mem_bot]
      exact hv
    rw [apply_polarComplexStructure, ← RCLike.re_to_real (x := ⟪_, _⟫), ← hP.norm_sqrt_apply_sq]
    positivity

/-- **Polar normalization fixes metric structures.** If the inner product of `V` is the
compatible metric `ω(·, J ·)` of an almost complex structure `J`, then the polar normalization
of `ω` is `J`. -/
theorem polarComplexStructure_eq_of_apply_eq_inner (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (h : ∀ u v, ω u (J v) = ⟪u, v⟫) :
    ω.polarComplexStructure = J := by
  -- The operator of `ω` is `J` itself, so its modulus is `√(-J²) = 1`.
  have hA : J.toLinearMap = ω.innerOperator := (ω.eq_innerOperator_iff).mpr fun u v ↦ by
    have hJ : ω v (J (J u)) = -ω v u := by rw [J.apply_apply]; exact map_neg (ω.toBilinForm v) u
    rw [real_inner_comm, ← h, hJ, ω.neg_eq]
  have hP : ω.innerOperator.operatorAbs = 1 := by
    refine (LinearMap.IsPositive.eq_operatorAbs LinearMap.isPositive_one ?_).symm
    rw [adjoint_innerOperator, LinearMap.neg_comp, ← hA, J.square_neg, neg_neg,
      Module.End.one_eq_id, LinearMap.id_comp]
  refine AlmostComplexStructure.toLinearMap_injective ?_
  rw [polarComplexStructure_toLinearMap, hA]
  calc ω.innerOperator.polarFactor = ω.innerOperator.polarFactor * ω.innerOperator.operatorAbs := by
        rw [hP, mul_one]
    _ = ω.innerOperator := ω.innerOperator.polarFactor_comp_operatorAbs

/-! ### Naturality -/

/-- The operator of a symplectic form transported along a linear isometric equivalence `e` is
the conjugate by `e` of the operator of the form. -/
theorem innerOperator_transport (ω : SymplecticForm V) (e : V ≃ₗᵢ[ℝ] W) :
    (ω.transport e.toLinearEquiv).innerOperator = e.toLinearEquiv.conj ω.innerOperator := by
  refine (((ω.transport e.toLinearEquiv).eq_innerOperator_iff).mpr fun w w' ↦ ?_).symm
  rw [LinearEquiv.conj_apply_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearIsometryEquiv.inner_map_eq_flip,
    inner_innerOperator_apply, ω.transport_apply, LinearIsometryEquiv.coe_symm_toLinearEquiv]

/-- **Naturality of polar normalization.** Transporting a symplectic form along a linear
isometric equivalence transports its polar normalization. -/
theorem polarComplexStructure_transport (ω : SymplecticForm V) (e : V ≃ₗᵢ[ℝ] W) :
    (ω.transport e.toLinearEquiv).polarComplexStructure =
      ω.polarComplexStructure.transport e.toLinearEquiv := by
  refine AlmostComplexStructure.toLinearMap_injective ?_
  rw [polarComplexStructure_toLinearMap, innerOperator_transport, LinearMap.polarFactor_conj,
    AlmostComplexStructure.transport_toLinearMap, polarComplexStructure_toLinearMap]

/-- **Naturality of polar normalization**, pointwise: a linear isometric equivalence which is
a symplectomorphism intertwines the polar normalizations, `J₂ (e v) = e (J₁ v)`. -/
theorem IsSymplectomorphism.polarComplexStructure_apply {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm W} {e : V ≃ₗᵢ[ℝ] W} (h : IsSymplectomorphism ω₁ ω₂ e.toLinearEquiv)
    (v : V) : ω₂.polarComplexStructure (e v) = e (ω₁.polarComplexStructure v) := by
  rw [← isSymplectomorphism_iff_transport_eq.mp h, polarComplexStructure_transport,
    AlmostComplexStructure.transport_apply]
  simp

/-! ### Invariant compatible structures for compact groups -/

/-- **Invariant compatible complex structures.** A continuous linear representation `π` of a
compact group on a finite-dimensional real normed space preserving a symplectic form `ω`
preserves some compatible almost complex structure: every `π g` is complex linear for it. -/
theorem exists_compatible_forall_isComplexLinearMap {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (ω : SymplecticForm E) (π : ContRepresentation ℝ G E)
    (hπ : Continuous π) (hω : ∀ g u v, ω (π g u) (π g v) = ω u v) :
    ∃ J : AlmostComplexStructure E, ω.Compatible J ∧
      ∀ g, IsComplexLinearMap J J (π g : E →ₗ[ℝ] E) := by
  -- Choose a linear isomorphism `k` with a Euclidean space for which Weyl's unitarian trick makes
  -- the transported representation `ρ = k π k⁻¹` unitary. Then `ρ` preserves the transported
  -- symplectic form, hence its polar normalization, which transports back along `k`.
  borelize G
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let f : E ≃L[ℝ] F := (LinearEquiv.ofFinrankEq E F (by simp [F])).toContinuousLinearEquiv
  obtain ⟨e, he⟩ := (ContinuousLinearEquiv.congr f π).exists_isUnitary_congr
    (ContinuousLinearEquiv.continuous_congr f hπ)
  set k := f.trans e
  set ρ := ContinuousLinearEquiv.congr e (ContinuousLinearEquiv.congr f π)
  have hρ : ∀ g x, ρ g x = k (π g (k.symm x)) := fun g x ↦ by
    simp [ρ, k]
  set ω' := ω.transport k.toLinearEquiv
  set J' := ω'.polarComplexStructure
  -- Each `ρ g` is a linear isometric equivalence preserving `ω'`, so it commutes with `J'`.
  have hρω : ∀ g y z, ω' (ρ g y) (ρ g z) = ω' y z := fun g y z ↦ by
    simp [ω', hρ, hω]
  have hJ' : ∀ g x, J' (ρ g x) = ρ g (J' x) := fun g x ↦
    IsSymplectomorphism.polarComplexStructure_apply
      (e := LinearIsometryEquiv.ofSurjective
        { toLinearMap := (ρ g : F →ₗ[ℝ] F), norm_map' := he.norm_map g }
        fun y ↦ ⟨ρ g⁻¹ y, Representation.self_inv_apply ρ.toRepresentation g y⟩)
      (isSymplectomorphism_iff.mpr (hρω g)) x
  refine ⟨J'.transport k.symm.toLinearEquiv, ?_, fun g ↦ ?_⟩
  · have h := (ω'.compatible_polarComplexStructure).transport k.symm.toLinearEquiv
    rwa [ContinuousLinearEquiv.toLinearEquiv_symm, transport_symm_transport] at h
  · rw [isComplexLinearMap_iff_apply]
    intro v
    have h := hJ' g (k v)
    simp only [hρ, ContinuousLinearEquiv.symm_apply_apply] at h
    simp [h]

end TauCeti.SymplecticForm
