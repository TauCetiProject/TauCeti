/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

/-!
# The Kirillov–Kostant–Souriau form and the Lie–Poisson structure

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, fix `ν ∈ 𝔤*`, and let `O = G ⧸ G_ν` be its coadjoint orbit, with the
Kirillov–Kostant–Souriau form `ω_ν` (`Module.Dual.coadjointOrbitForm`) and the injective immersion
`ι : O → 𝔤*`, `[g] ↦ Ad*_g ν` (`Representation.orbitMap` of the coadjoint representation). Write
`dι_x : T_x O → 𝔤*` for its differential at `x` (`TauCeti.SmoothTwoForm.IsMomentMap.differential`
of the moment map `ι`).

The dual space `𝔤*` carries the positive Lie–Poisson structure `{ℓ_α, ℓ_β} = ℓ_⁅α, β⁆`, where
`ℓ_α(μ) = μ α` is the linear function of `α ∈ 𝔤`. Covectors at `μ ∈ 𝔤*` are elements of
`(𝔤*)* = 𝔤`, the tensor is `π_μ(α, β) = μ ⁅α, β⁆`, which is the Kirillov form of `μ`
(`Module.Dual.kirillovForm`), and its sharp map, defined by `β(π♯_μ α) = π_μ(α, β)`, is
`α ↦ μ.kirillovForm α`. This file proves that, at every point of the orbit, `ω_ν` inverts the
Lie–Poisson tensor on the tangent image of the orbit, with these signs.

* **Derivative formula.** The generator `ξ_O` of `ξ ∈ 𝔤` satisfies `dι_x(ξ_O(x)) = -π♯_μ ξ`, the
  coadjoint action `⁅ξ, μ⁆` of `ξ` on `μ = ι x`
  (`Module.Dual.differential_orbitMap_coadjointRepresentation_fundamentalVectorField`). Since
  `dι_x` is injective, the vector of `T_x O` lifting `π♯_μ α` is `(-α)_O(x)`
  (`Module.Dual.differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff`). In
  particular every sharp image `π♯_μ α` is tangent to the orbit, and its lift is unique.
* **The tangent image is the sharp image.** Conversely, every tangent vector of the orbit is a
  generator, so the differential of the orbit map carries `T_x O` onto `π♯_μ(𝔤)`
  (`Module.Dual.range_differential_orbitMap_coadjointRepresentation`). This image is the
  annihilator `𝔤_μ^0` of the coadjoint stabilizer
  (`Module.Dual.range_differential_orbitMap_coadjointRepresentation_eq_dualAnnihilator`), and the
  rank of the Lie–Poisson tensor at every point of the orbit is the orbit dimension
  (`Module.Dual.finrank_range_kirillovForm_orbitMap_coadjointRepresentation`).
* **The KKS/sharp identity.** For `α, β ∈ 𝔤`,
  `ω_ν((dι_x)⁻¹ π♯_μ α, (dι_x)⁻¹ π♯_μ β) = π_μ(α, β)`, stated as: if `dι_x v = π♯_μ α` and
  `dι_x w = π♯_μ β` then `ω_ν(v, w) = μ ⁅α, β⁆`
  (`Module.Dual.eval₂_coadjointOrbitForm_eq_kirillovForm`). Equivalently, after applying `dι_x` to
  the second argument only, `ω_ν(v, w) = -⟨dι_x w, α⟩` for every `w`
  (`Module.Dual.eval₂_coadjointOrbitForm_eq_neg_differential_of_eq_kirillovForm`).
* **The positive Lie–Poisson convention.** With the conventions `ι_(X_f) ω = df` and
  `{f, g} = ω(X_f, X_g)`, the restrictions of linear functions satisfy
  `{ℓ_ξ ∘ ι, ℓ_η ∘ ι} = ℓ_⁅ξ, η⁆ ∘ ι`
  (`Module.Dual.poissonBracket_orbitMap_coadjointRepresentation_apply`).
  More generally the orbit map, like every moment map whose cocycle vanishes, is a Poisson map:
  restrictions `F ∘ ι` and `G ∘ ι` of functions with derivatives `α` and `β` at `μ` have Poisson
  bracket `π_μ(α, β)` at `x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_apply_lie_of_mvfderiv_eq`).

These are pointwise statements about the orbit through `ν`: they identify the tangent image
`T_μ(G · ν)` with the sharp image `π♯_μ(T*_μ 𝔤*)`, but they do not identify the symplectic leaves
of the Lie–Poisson structure with the coadjoint orbits. The algebraic counterpart on the
tangent model `𝔤 ⧸ 𝔤_ν` is `Module.Dual.kksForm_eq_kirillovForm_of_coadjointTangentMap_eq`.

## Main results

* `Module.Dual.differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff`: the
  Lie–Poisson sharp image `π♯_μ α` is tangent to the orbit, with lift `(-α)_O`.
* `Module.Dual.range_differential_orbitMap_coadjointRepresentation`: the tangent image of the orbit
  is the Lie–Poisson sharp image `π♯_μ(𝔤)`.
* `Module.Dual.range_differential_orbitMap_coadjointRepresentation_eq_dualAnnihilator`: the tangent
  image of the orbit is `𝔤_μ^0`.
* `Module.Dual.finrank_range_kirillovForm_orbitMap_coadjointRepresentation`: the rank of the
  Lie–Poisson tensor along the orbit is the orbit dimension.
* `Module.Dual.eval₂_coadjointOrbitForm_eq_kirillovForm`: the KKS form inverts the Lie–Poisson
  sharp map.
* `Module.Dual.poissonBracket_orbitMap_coadjointRepresentation_apply`: the restrictions of linear
  functions obey the positive Lie–Poisson convention.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 10.1 and 14.3 (the Lie–Poisson bracket, and the
  coadjoint orbit symplectic structure as the symplectic structure of its leaves).
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {ν : Module.Dual ℝ (GroupLieAlgebra I G)}

/-! ### The differential of the orbit map and the sharp map -/

/-- **The derivative formula for the orbit map.** At a point `x` of the coadjoint orbit with image
`μ = ι x`, the differential of the orbit map carries the generator `ξ_O(x)` to the coadjoint
action `⁅ξ, μ⁆ = -π♯_μ ξ`, the negative of the Lie–Poisson sharp image `μ.kirillovForm ξ`. -/
theorem differential_orbitMap_coadjointRepresentation_fundamentalVectorField
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ : GroupLieAlgebra I G) :
    ν.isEquivariantMomentMap_coadjointOrbitForm.differential x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x) =
      -((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm ξ := by
  have h := ν.isEquivariantMomentMap_coadjointOrbitForm
  rw [← InfinitesimalAction.fundamental_apply,
    h.differential_apply_of_momentCocycle_eq_zero (h.momentCocycle_eq_zero x)]
  ext η
  rw [LinearMap.neg_apply, kirillovForm_eq_neg_lie_apply, neg_neg]

/-- **The lift of a sharp image.** A tangent vector `v` of the coadjoint orbit at `x` is carried
by the differential of the orbit map to the Lie–Poisson sharp image `π♯_μ α = μ.kirillovForm α`
of `α ∈ 𝔤` at `μ = ι x` exactly when `v` is the generator `(-α)_O(x)`. -/
theorem differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}
    {v : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x}
    {α : GroupLieAlgebra I G} :
    ν.isEquivariantMomentMap_coadjointOrbitForm.differential x v =
        ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm α ↔
      v = fundamentalVectorField
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (-α) x := by
  rw [← (ν.injective_differential_orbitMap_coadjointRepresentation x).eq_iff,
    differential_orbitMap_coadjointRepresentation_fundamentalVectorField, map_neg, neg_neg]

/-! ### The tangent image is the sharp image -/

/-- **The tangent spaces of a coadjoint orbit are the Lie–Poisson sharp images.** At a point `x` of
the coadjoint orbit with image `μ = ι x`, the differential of the orbit map carries `T_x O` onto
the image `π♯_μ(𝔤) = {μ.kirillovForm α}` of the Lie–Poisson sharp map: every tangent vector is a
generator `ξ_O(x)`, which is carried to `π♯_μ(-ξ)`. -/
theorem range_differential_orbitMap_coadjointRepresentation
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    LinearMap.range (ν.isEquivariantMomentMap_coadjointOrbitForm.differential x) =
      LinearMap.range ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm := by
  refine le_antisymm ?_ fun _ ⟨α, hα⟩ ↦
    ⟨_, (differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff.2 rfl).trans hα⟩
  rintro _ ⟨v, rfl⟩
  obtain ⟨ξ, rfl⟩ := Subgroup.surjective_fundamentalVectorField (I := I)
    (isClosed_stabilizer_coadjointRepresentation I ν) x v
  exact ⟨-ξ, by rw [differential_orbitMap_coadjointRepresentation_fundamentalVectorField, map_neg]⟩

/-- **The tangent image of a coadjoint orbit is the annihilator of the stabilizer.** At a point `x`
of the coadjoint orbit with image `μ = ι x`, the image of the differential of the orbit map is
`𝔤_μ^0`, the covectors vanishing on the coadjoint stabilizer `𝔤_μ = {ξ | ⁅ξ, μ⁆ = 0}`. -/
theorem range_differential_orbitMap_coadjointRepresentation_eq_dualAnnihilator
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    LinearMap.range (ν.isEquivariantMomentMap_coadjointOrbitForm.differential x) =
      (lieAnnihilator ℝ (GroupLieAlgebra I G)
        ((coadjointRepresentation ℝ I G).orbitMap ν x)).toSubmodule.dualAnnihilator := by
  rw [range_differential_orbitMap_coadjointRepresentation, range_kirillovForm]

/-- **The rank of the Lie–Poisson tensor along a coadjoint orbit is the orbit dimension.** At every
point `μ = ι x` of the orbit, the image of the Lie–Poisson sharp map `π♯_μ` has the dimension of
the orbit `G ⧸ G_ν`. -/
theorem finrank_range_kirillovForm_orbitMap_coadjointRepresentation
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    finrank ℝ (LinearMap.range ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm) =
      finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) := by
  rw [← range_differential_orbitMap_coadjointRepresentation,
    LinearMap.finrank_range_of_inj (ν.injective_differential_orbitMap_coadjointRepresentation x),
    TauCeti.finrank_tangentSpace]

/-! ### The KKS form inverts the sharp map -/

/-- **The KKS/sharp identity, after applying the differential of the orbit map.** If the
differential of the orbit map carries `v` to the Lie–Poisson sharp image `π♯_μ α` at `μ = ι x`,
then `ω_ν(v, w) = -⟨dι_x w, α⟩` for every tangent vector `w`. -/
theorem eval₂_coadjointOrbitForm_eq_neg_differential_of_eq_kirillovForm
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}
    {v : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x}
    {α : GroupLieAlgebra I G}
    (hv : ν.isEquivariantMomentMap_coadjointOrbitForm.differential x v =
      ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm α)
    (w : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x v w =
      -ν.isEquivariantMomentMap_coadjointOrbitForm.differential x w α := by
  rw [differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff.1 hv,
    ← InfinitesimalAction.fundamental_apply,
    ← ν.isEquivariantMomentMap_coadjointOrbitForm.differential_apply_eq_eval₂, map_neg]

/-- **The Kirillov–Kostant–Souriau form inverts the Lie–Poisson sharp map.** At a point `x` of the
coadjoint orbit with image `μ = ι x`, if the differential of the orbit map carries `v` and `w` to
the Lie–Poisson sharp images `π♯_μ α` and `π♯_μ β`, then
`ω_ν(v, w) = π_μ(α, β) = μ ⁅α, β⁆`. That is,
`ω_ν((dι_x)⁻¹ π♯_μ α, (dι_x)⁻¹ π♯_μ β) = π_μ(α, β)`; every sharp image has a unique lift to the
tangent space of the orbit
(`Module.Dual.differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff`). -/
theorem eval₂_coadjointOrbitForm_eq_kirillovForm
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}
    {v w : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x}
    {α β : GroupLieAlgebra I G}
    (hv : ν.isEquivariantMomentMap_coadjointOrbitForm.differential x v =
      ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm α)
    (hw : ν.isEquivariantMomentMap_coadjointOrbitForm.differential x w =
      ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm β) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x v w =
      ((coadjointRepresentation ℝ I G).orbitMap ν x).kirillovForm α β := by
  rw [differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff.1 hv,
    differential_orbitMap_coadjointRepresentation_eq_kirillovForm_iff.1 hw,
    eval₂_coadjointOrbitForm_fundamentalVectorField, kirillovForm_apply, neg_lie, lie_neg, neg_neg]

/-! ### The positive Lie–Poisson convention -/

/-- **The positive Lie–Poisson convention on a coadjoint orbit.** The restrictions to the orbit of
the linear functions `ℓ_ξ(μ) = μ ξ` on `𝔤*` satisfy `{ℓ_ξ ∘ ι, ℓ_η ∘ ι} = ℓ_⁅ξ, η⁆ ∘ ι` for the
KKS form. More generally the orbit map is a Poisson map
(`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_apply_lie_of_mvfderiv_eq`). -/
theorem poissonBracket_orbitMap_coadjointRepresentation_apply (ξ η : GroupLieAlgebra I G)
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    ν.coadjointOrbitForm.poissonBracket (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y ξ)
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y η) x =
      (coadjointRepresentation ℝ I G).orbitMap ν x ⁅ξ, η⁆ :=
  have h := ν.isEquivariantMomentMap_coadjointOrbitForm
  h.poissonBracket_eq_apply_lie_of_mvfderiv_eq ν.isSymplectic_coadjointOrbitForm.isNondegenerate
    (h.momentCocycle_eq_zero x) (fun v ↦ (h.differential_apply x v ξ).symm)
    (fun v ↦ (h.differential_apply x v η).symm)

end Module.Dual
