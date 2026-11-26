/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain
public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Adjoint
public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Density

/-!
# The weak exterior derivative and codifferential on `L²` forms

A linear map `T` between compactly supported smooth forms defines a densely defined partial
linear map `TauCeti.compactlySupportedForms.toL2Operator T` between the spaces `L²Ωᵏ(M)` of
square-integrable forms, whose domain is the image of the compactly supported smooth forms. For
the exterior derivative `d` and the codifferential `d*` these are the unbounded operators of
the `L²` de Rham complex on their smallest natural domain.

Their adjoints are the **weak** operators of distribution theory:

* `TauCeti.L2Form.weakExtDeriv o hkl`, the adjoint of the codifferential on compactly supported
  smooth forms: `dω = η` weakly when `⟪η, β⟫ = ⟪ω, d*β⟫` for every compactly supported smooth
  form `β` (`TauCeti.L2Form.mem_graph_weakExtDeriv_iff`);
* `TauCeti.L2Form.weakCodifferential I M k`, the adjoint of the exterior derivative on
  compactly supported smooth forms: `d*ω = η` weakly when `⟪η, α⟫ = ⟪ω, dα⟫` for every
  compactly supported smooth form `α` (`TauCeti.L2Form.mem_graph_weakCodifferential_iff`).

As adjoints they are closed, and on an oriented boundaryless manifold they are densely defined
and extend `d` and `d*` on compactly supported smooth forms, because `d*` is formally adjoint to
`d` there (`TauCeti.compactlySupportedForms.inner_toL2Form_mextDerivₗ`). The weak exterior
derivative still squares to zero on smooth exact forms
(`TauCeti.L2Form.range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv`), so these operators form a
Hilbert complex, whose Hodge decomposition is in
`TauCeti.Geometry.Manifold.Riemannian.L2Form.HodgeDecomposition`. A compactly supported smooth
form is weakly closed or weakly coclosed exactly when it is closed or coclosed
(`TauCeti.L2Form.toL2Form_mem_ker_weakExtDeriv_iff`,
`TauCeti.L2Form.toL2Form_mem_ker_weakCodifferential_iff`).

The weak codifferential is defined without an orientation, for a continuous metric; the weak
exterior derivative is defined through the codifferential of an orientation `o`. On a manifold
with boundary the compactly supported test forms need not vanish on the boundary, so there these
adjoints also impose a boundary condition; the results relating them to `d` and `d*` assume a
boundaryless manifold.

## Main definitions

* `TauCeti.compactlySupportedForms.toL2Operator`: the partial linear map on `L²` forms induced
  by a linear map of compactly supported smooth forms.
* `TauCeti.L2Form.weakExtDeriv`: the weak exterior derivative `L²Ωᵏ(M) → L²Ωᵏ⁺¹(M)`.
* `TauCeti.L2Form.weakCodifferential`: the weak codifferential `L²Ωᵏ⁺¹(M) → L²Ωᵏ(M)`.

## References

* K. Kodaira, *Harmonic fields in Riemannian manifolds (generalized potential theory)*, Ann. of
  Math. 50 (1949), 587–665.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992), §3.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {k k' : ℕ}

/-! ### Partial operators on `L²` forms from operators on compactly supported forms -/

namespace compactlySupportedForms

section Operator

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  (T : compactlySupportedForms I M k →ₗ[ℝ] compactlySupportedForms I M k')

/-- The partial linear map `L²Ωᵏ(M) → L²Ωᵏ'(M)` induced by a linear map `T` of compactly
supported smooth forms: its domain is the image of the compactly supported smooth `k`-forms in
`L²Ωᵏ(M)`, and it sends the class of `α` to the class of `T α`. -/
def toL2Operator : L2Form I M k →ₗ.[ℝ] L2Form I M k' :=
  (toL2Form I M k).domainOperator (toL2Form I M k' ∘ₗ T) toL2Form_injective

/-- The domain of `toL2Operator T` is the image of the compactly supported smooth forms. -/
@[simp]
theorem domain_toL2Operator : (toL2Operator T).domain = LinearMap.range (toL2Form I M k) :=
  LinearMap.domain_domainOperator _ _ _

/-- The class of a compactly supported smooth form lies in the domain of `toL2Operator T`. -/
theorem toL2Form_mem_domain_toL2Operator (α : compactlySupportedForms I M k) :
    toL2Form I M k α ∈ (toL2Operator T).domain :=
  LinearMap.apply_mem_domain_domainOperator _ _ _ α

/-- `toL2Operator T` sends the class of a compactly supported smooth form `α` to the class
of `T α`. -/
@[simp]
theorem toL2Operator_apply (α : compactlySupportedForms I M k)
    (h : toL2Form I M k α ∈ (toL2Operator T).domain) :
    toL2Operator T ⟨toL2Form I M k α, h⟩ = toL2Form I M k' (T α) :=
  LinearMap.domainOperator_apply_mk _ _ _ α h

/-- The graph of `toL2Operator T` consists of the pairs of classes of `α` and `T α`. -/
theorem mem_graph_toL2Operator_iff {u : L2Form I M k} {v : L2Form I M k'} :
    (u, v) ∈ (toL2Operator T).graph ↔
      ∃ α, toL2Form I M k α = u ∧ toL2Form I M k' (T α) = v :=
  LinearMap.mem_graph_domainOperator_iff _ _ _

/-- The range of `toL2Operator T` is the image of the classes of `T α`. -/
theorem range_toL2Operator :
    LinearMap.range (toL2Operator T).toFun = LinearMap.range (toL2Form I M k' ∘ₗ T) :=
  LinearMap.range_domainOperator _ _ _

/-- If `T` and `S` are formally adjoint for the `L²` inner product on compactly supported smooth
forms, then so are the partial linear maps they induce. -/
theorem isFormalAdjoint_toL2Operator
    {S : compactlySupportedForms I M k' →ₗ[ℝ] compactlySupportedForms I M k}
    (h : ∀ α β, ⟪toL2Form I M k' (T α), toL2Form I M k' β⟫_ℝ =
      ⟪toL2Form I M k α, toL2Form I M k (S β)⟫_ℝ) :
    (toL2Operator T).IsFormalAdjoint (toL2Operator S) :=
  LinearMap.isFormalAdjoint_domainOperator_iff.2 h

end Operator

section Adjoint

variable [IsManifold I ∞ M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [T2Space M] (T : compactlySupportedForms I M k →ₗ[ℝ] compactlySupportedForms I M k')

/-- `toL2Operator T` is densely defined, since compactly supported smooth forms are dense in
`L²`. -/
theorem dense_domain_toL2Operator :
    Dense ((toL2Operator T).domain : Set (L2Form I M k)) := by
  rw [domain_toL2Operator, LinearMap.coe_range]
  exact denseRange_toL2Form

/-- `(u, v)` lies on the graph of the adjoint of `toL2Operator T` exactly when
`⟪v, α⟫ = ⟪u, T α⟫` for every compactly supported smooth form `α`: the adjoint is the weak, or
distributional, extension of the formal adjoint of `T`. -/
theorem mem_graph_adjoint_toL2Operator_iff {u : L2Form I M k'} {v : L2Form I M k} :
    (u, v) ∈ (toL2Operator T)†.graph ↔ ∀ α : compactlySupportedForms I M k,
      ⟪v, toL2Form I M k α⟫_ℝ = ⟪u, toL2Form I M k' (T α)⟫_ℝ := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_domain_toL2Operator T),
    Submodule.mem_adjoint_iff]
  simp only [mem_graph_toL2Operator_iff, sub_eq_zero]
  constructor
  · intro h α
    simpa only [real_inner_comm] using (h _ _ ⟨α, rfl, rfl⟩).symm
  · intro h a b hab
    obtain ⟨α, rfl, rfl⟩ := hab
    simpa only [real_inner_comm] using (h α).symm

/-- The kernel of the adjoint of `toL2Operator T` is the orthogonal complement of the classes of
`T α`. -/
theorem ker_adjoint_toL2Operator :
    (toL2Operator T)†.ker = (LinearMap.range (toL2Form I M k' ∘ₗ T))ᗮ := by
  rw [← LinearPMap.orthogonal_range_eq_ker_adjoint (dense_domain_toL2Operator T),
    range_toL2Operator]

end Adjoint

end compactlySupportedForms

/-! ### The weak codifferential -/

namespace L2Form

open compactlySupportedForms

section Codifferential

variable [IsManifold I ∞ M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M k) in
/-- The **weak codifferential** `L²Ωᵏ⁺¹(M) → L²Ωᵏ(M)` on a Riemannian manifold: the adjoint of
the exterior derivative of compactly supported smooth `k`-forms. An `L²` form `ω` has weak
codifferential `η` when `⟪η, α⟫ = ⟪ω, dα⟫` for every compactly supported smooth `k`-form `α`. -/
def weakCodifferential : L2Form I M (k + 1) →ₗ.[ℝ] L2Form I M k :=
  (toL2Operator (compactlySupportedForms.mextDerivₗ I M k))†

/-- The weak codifferential is the adjoint of the exterior derivative of compactly supported
smooth forms. -/
theorem weakCodifferential_def :
    weakCodifferential I M k = (toL2Operator (compactlySupportedForms.mextDerivₗ I M k))† :=
  (rfl)

variable [T2Space M]

/-- The weak codifferential is a closed operator. -/
theorem isClosed_weakCodifferential : (weakCodifferential I M k).IsClosed :=
  LinearPMap.adjoint_isClosed (dense_domain_toL2Operator _)

/-- **The weak codifferential**: `(ω, η)` lies on the graph of the weak codifferential exactly
when `⟪η, α⟫ = ⟪ω, dα⟫` for every compactly supported smooth `k`-form `α`. -/
theorem mem_graph_weakCodifferential_iff {u : L2Form I M (k + 1)} {v : L2Form I M k} :
    (u, v) ∈ (weakCodifferential I M k).graph ↔ ∀ α : compactlySupportedForms I M k,
      ⟪v, toL2Form I M k α⟫_ℝ =
        ⟪u, toL2Form I M (k + 1) (compactlySupportedForms.mextDerivₗ I M k α)⟫_ℝ :=
  mem_graph_adjoint_toL2Operator_iff _

/-- An `L²` form is weakly coclosed exactly when it is orthogonal to the exterior derivatives
of all compactly supported smooth forms. -/
theorem ker_weakCodifferential :
    (weakCodifferential I M k).ker = (LinearMap.range
      (toL2Form I M (k + 1) ∘ₗ compactlySupportedForms.mextDerivₗ I M k))ᗮ :=
  ker_adjoint_toL2Operator _

end Codifferential

/-! ### The weak exterior derivative -/

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m l : ℕ}

/-- The Riemannian volume and the `L²` metric need only a continuous metric. -/
local instance instIsContinuousRiemannianBundleTangentSpaceWeak :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- The **weak exterior derivative** `L²Ωᵏ(M) → L²Ωᵏ⁺¹(M)` on an oriented Riemannian manifold of
dimension `m = k + 1 + l`: the adjoint of the codifferential of compactly supported smooth
`(k + 1)`-forms. An `L²` form `ω` has weak exterior derivative `η` when `⟪η, β⟫ = ⟪ω, d*β⟫` for
every compactly supported smooth `(k + 1)`-form `β`. -/
def weakExtDeriv (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    L2Form I M k →ₗ.[ℝ] L2Form I M (k + 1) :=
  (toL2Operator (codifferential o hkl))†

/-- The weak exterior derivative is the adjoint of the codifferential of compactly supported
smooth forms. -/
theorem weakExtDeriv_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    weakExtDeriv o hkl = (toL2Operator (codifferential o hkl))† :=
  (rfl)

variable [T2Space M]

/-- The weak exterior derivative is a closed operator. -/
theorem isClosed_weakExtDeriv (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    (weakExtDeriv o hkl).IsClosed :=
  LinearPMap.adjoint_isClosed (dense_domain_toL2Operator _)

/-- **The weak exterior derivative**: `(ω, η)` lies on the graph of the weak exterior derivative
exactly when `⟪η, β⟫ = ⟪ω, d*β⟫` for every compactly supported smooth `(k + 1)`-form `β`. -/
theorem mem_graph_weakExtDeriv_iff (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    {u : L2Form I M k} {v : L2Form I M (k + 1)} :
    (u, v) ∈ (weakExtDeriv o hkl).graph ↔ ∀ β : compactlySupportedForms I M (k + 1),
      ⟪v, toL2Form I M (k + 1) β⟫_ℝ = ⟪u, toL2Form I M k (codifferential o hkl β)⟫_ℝ :=
  mem_graph_adjoint_toL2Operator_iff _

/-- An `L²` form is weakly closed exactly when it is orthogonal to the codifferentials of all
compactly supported smooth forms. -/
theorem ker_weakExtDeriv (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    (weakExtDeriv o hkl).ker =
      (LinearMap.range (toL2Form I M k ∘ₗ codifferential o hkl))ᗮ :=
  ker_adjoint_toL2Operator _

variable [BoundarylessManifold I M]

/-- On an oriented boundaryless manifold, the weak exterior derivative extends the exterior
derivative of compactly supported smooth forms. -/
theorem toL2Operator_mextDerivₗ_le_weakExtDeriv (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) :
    toL2Operator (compactlySupportedForms.mextDerivₗ I M k) ≤ weakExtDeriv o hkl :=
  ((isFormalAdjoint_toL2Operator _ fun α β ↦
    inner_toL2Form_mextDerivₗ o hkl α β).symm).le_adjoint (dense_domain_toL2Operator _)

/-- On an oriented boundaryless manifold, the weak codifferential extends the codifferential of
compactly supported smooth forms. -/
theorem toL2Operator_codifferential_le_weakCodifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) :
    toL2Operator (codifferential o hkl) ≤ weakCodifferential I M k :=
  (isFormalAdjoint_toL2Operator _ fun α β ↦
    inner_toL2Form_mextDerivₗ o hkl α β).le_adjoint (dense_domain_toL2Operator _)

/-- On an oriented boundaryless manifold, the class of a compactly supported smooth form lies in
the domain of the weak exterior derivative. -/
theorem toL2Form_mem_domain_weakExtDeriv (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (α : compactlySupportedForms I M k) :
    toL2Form I M k α ∈ (weakExtDeriv o hkl).domain :=
  (toL2Operator_mextDerivₗ_le_weakExtDeriv o hkl).1 (toL2Form_mem_domain_toL2Operator _ α)

/-- On an oriented boundaryless manifold, the class of a compactly supported smooth form lies in
the domain of the weak codifferential. -/
theorem toL2Form_mem_domain_weakCodifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (β : compactlySupportedForms I M (k + 1)) :
    toL2Form I M (k + 1) β ∈ (weakCodifferential I M k).domain :=
  (toL2Operator_codifferential_le_weakCodifferential o hkl).1
    (toL2Form_mem_domain_toL2Operator _ β)

/-- On an oriented boundaryless manifold, the weak exterior derivative of the class of a
compactly supported smooth form is the class of its exterior derivative. -/
@[simp]
theorem weakExtDeriv_toL2Form (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (α : compactlySupportedForms I M k) (h : toL2Form I M k α ∈ (weakExtDeriv o hkl).domain) :
    weakExtDeriv o hkl ⟨toL2Form I M k α, h⟩ =
      toL2Form I M (k + 1) (compactlySupportedForms.mextDerivₗ I M k α) := by
  rw [← toL2Operator_apply _ α (toL2Form_mem_domain_toL2Operator _ α)]
  exact ((toL2Operator_mextDerivₗ_le_weakExtDeriv o hkl).2 rfl).symm

/-- On an oriented boundaryless manifold, the weak codifferential of the class of a compactly
supported smooth form is the class of its codifferential. -/
theorem weakCodifferential_toL2Form (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (β : compactlySupportedForms I M (k + 1))
    (h : toL2Form I M (k + 1) β ∈ (weakCodifferential I M k).domain) :
    weakCodifferential I M k ⟨toL2Form I M (k + 1) β, h⟩ =
      toL2Form I M k (codifferential o hkl β) := by
  rw [← toL2Operator_apply _ β (toL2Form_mem_domain_toL2Operator _ β)]
  exact ((toL2Operator_codifferential_le_weakCodifferential o hkl).2 rfl).symm

/-- On an oriented boundaryless manifold, the weak exterior derivative is densely defined. -/
theorem dense_domain_weakExtDeriv (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    Dense ((weakExtDeriv o hkl).domain : Set (L2Form I M k)) :=
  (dense_domain_toL2Operator _).mono (toL2Operator_mextDerivₗ_le_weakExtDeriv o hkl).1

/-- On an oriented boundaryless manifold, the weak codifferential is densely defined. -/
theorem dense_domain_weakCodifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) :
    Dense ((weakCodifferential I M k).domain : Set (L2Form I M (k + 1))) :=
  (dense_domain_toL2Operator _).mono (toL2Operator_codifferential_le_weakCodifferential o hkl).1

/-- On an oriented boundaryless manifold, a compactly supported smooth form is weakly closed
exactly when it is closed. -/
@[simp]
theorem toL2Form_mem_ker_weakExtDeriv_iff (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (α : compactlySupportedForms I M k) :
    toL2Form I M k α ∈ (weakExtDeriv o hkl).ker ↔
      compactlySupportedForms.mextDerivₗ I M k α = 0 := by
  rw [LinearPMap.coe_mem_ker_iff (x := ⟨_, toL2Form_mem_domain_weakExtDeriv o hkl α⟩),
    weakExtDeriv_toL2Form, LinearMap.map_eq_zero_iff _ toL2Form_injective]

/-- On an oriented boundaryless manifold, a compactly supported smooth form is weakly coclosed
exactly when it is coclosed. -/
theorem toL2Form_mem_ker_weakCodifferential_iff (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (β : compactlySupportedForms I M (k + 1)) :
    toL2Form I M (k + 1) β ∈ (weakCodifferential I M k).ker ↔ codifferential o hkl β = 0 := by
  rw [LinearPMap.coe_mem_ker_iff (x := ⟨_, toL2Form_mem_domain_weakCodifferential o hkl β⟩),
    weakCodifferential_toL2Form o hkl, LinearMap.map_eq_zero_iff _ toL2Form_injective]

/-- **`d ∘ d = 0` weakly**: on an oriented boundaryless manifold, the weak exterior derivative
vanishes on the exterior derivatives of compactly supported smooth forms. -/
theorem range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) :
    LinearMap.range (toL2Operator (compactlySupportedForms.mextDerivₗ I M k)).toFun ≤
      (weakExtDeriv o hkl).ker := by
  rw [range_toL2Operator]
  rintro _ ⟨α, rfl⟩
  rw [LinearMap.comp_apply, toL2Form_mem_ker_weakExtDeriv_iff, ← LinearMap.comp_apply,
    compactlySupportedForms.mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply]

end L2Form

end TauCeti
