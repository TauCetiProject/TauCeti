/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Hessian
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Critical points and Hessians of heights on a coadjoint orbit

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, fix `ν ∈ 𝔤*`, and let `O = G ⧸ G_ν` be its coadjoint orbit, with the
Kirillov–Kostant–Souriau form `ω` (`Module.Dual.coadjointOrbitForm`) and the orbit map
`μ : O → 𝔤*`, `[g] ↦ Ad*_g ν` (`Representation.orbitMap` of `coadjointRepresentation ℝ I G`).
For `X ∈ 𝔤` the **height** `f_X = ⟨μ, X⟩` is a smooth function on `O`, and since `μ` is a moment
map, `df_X = ι_(X_O) ω`,
where `ξ_O` is the generator of `ξ` for the action of `G` on `O` by left multiplication.

This file computes the critical points of `f_X` and its Hessian there, on the actual orbit
manifold and with Tau Ceti's intrinsic critical Hessian (`TauCeti.criticalHessian`), so that
nondegeneracy and the Morse index are the native `TauCeti.IsManifoldNondegenerateCriticalPoint`
and `TauCeti.manifoldMorseIndex`.

* The differential of the orbit map sends the generator `ξ_O(x)` to the infinitesimal coadjoint
  action `⁅ξ, μ x⁆`, and it is injective, so `ξ_O` vanishes at `x` exactly when `⁅ξ, μ x⁆ = 0`:
  the isotropy algebra of `x` is the coadjoint stabilizer `𝔤_(μ x)`
  (`Module.Dual.isotropy_fundamental_eq_lieAnnihilator_orbitMap_coadjointRepresentation`).
* As for every moment map component, `x` is a critical point of `f_X` exactly when `X_O(x) = 0`, so
  **`Crit(f_X) = {x | ⁅X, μ x⁆ = 0}`**
  (`Module.Dual.criticalPoints_orbitMap_coadjointRepresentation_apply`).
* At a critical point `x` the Hessian of `f_X` on generators is
  **`Hess f_X (x) (ξ_O, η_O) = μ(x)(⁅⁅X, η⁆, ξ⁆)`**
  (`Module.Dual.criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField`).
  This is the case of a coadjoint orbit of the general identity
  `Hess μ^X (Z_M, Y_M) = μ(⁅⁅X, Y⁆, Z⁆)` for infinitesimally equivariant moment maps of closed forms
  (`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_apply_eq_lie_lie`): differentiating
  `df_X(η_O) = ω(X_O, η_O) = f_⁅X, η⁆` along `ξ_O` gives `ω(⁅X, η⁆_O, ξ_O)`.
* The generators span every tangent space of `O` (`Subgroup.surjective_fundamentalVectorField`),
  so the Hessian is determined by the bilinear form `(ξ, η) ↦ μ(x)(⁅⁅X, η⁆, ξ⁆)` on `𝔤`. Hence
  `x` is a nondegenerate critical point exactly when the radical of this form is the stabilizer
  `𝔤_(μ x)`
  (`Module.Dual.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff`),
  and the Morse index of `f_X` at `x` is the negative index of inertia of the quadratic form
  `ξ ↦ μ(x)(⁅⁅X, ξ⁆, ξ⁆)` on `𝔤`
  (`Module.Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply`).

Everything is stated on `𝔤*`, for an arbitrary Lie group, with no invariant inner product. For a
compact group with an `Ad`-invariant inner product `B` and `μ x = B(p, ·)`, invariance of `B`
turns `⁅X, μ x⁆ = 0` into `⁅X, p⁆ = 0` and the quadratic form above into
`ξ ↦ -B(⁅ξ, p⁆, ⁅ξ, X⁆)`, the second derivative of `t ↦ B(Ad_(exp (t ξ)) p, X)` at `t = 0`; that
translation through `B` is not carried out in this file.

## Main results

* `Module.Dual.isotropy_fundamental_eq_lieAnnihilator_orbitMap_coadjointRepresentation`: the
  isotropy algebra of a point of the orbit is the coadjoint stabilizer of its image.
* `Module.Dual.criticalPoints_orbitMap_coadjointRepresentation_apply`:
  `Crit(f_X) = {x | ⁅X, μ x⁆ = 0}`.
* `Module.Dual.criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField`: the
  Hessian of `f_X` on generators at a critical point.
* `Module.Dual.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff`:
  nondegenerate critical points.
* `Module.Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply`: the Morse index as an
  index of inertia on `𝔤`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* R. Bott, *An application of the Morse theory to the topology of Lie groups*, Bull. Soc. Math.
  France 84 (1956), 251–281 (the Morse theory of heights on adjoint orbits).
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398 (critical points and Hessians of heights on orbits).
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
  (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-! ### Generators and isotropy -/

/-- **The isotropy algebras of a coadjoint orbit.** The generators `ξ_O` vanishing at a point `x`
of the coadjoint orbit are those of the coadjoint stabilizer `𝔤_(μ x)` of its image
`μ x = Ad*_g ν`. -/
theorem isotropy_fundamental_eq_lieAnnihilator_orbitMap_coadjointRepresentation
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    (InfinitesimalAction.fundamental I G
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)).isotropy x =
      lieAnnihilator ℝ (GroupLieAlgebra I G) ((coadjointRepresentation ℝ I G).orbitMap ν x) := by
  have h := ν.isEquivariantMomentMap_coadjointOrbitForm
  have hc := h.momentCocycle_eq_zero x
  refine le_antisymm (SmoothTwoForm.isotropy_le_lieAnnihilator_of_momentCocycle_eq_zero hc)
    fun ξ hξ ↦ ?_
  -- The differential of the orbit map is injective and sends `ξ_O x` to `⁅ξ, μ x⁆ = 0`.
  rw [InfinitesimalAction.mem_isotropy_iff]
  refine ν.injective_differential_orbitMap_coadjointRepresentation x ?_
  rw [h.differential_apply_of_momentCocycle_eq_zero hc, map_zero]
  exact (mem_lieAnnihilator ℝ (GroupLieAlgebra I G)).1 hξ

/-- The generator `ξ_O` vanishes at a point `x` of the coadjoint orbit exactly when `ξ` fixes the
image `μ x` infinitesimally, `⁅ξ, μ x⁆ = 0`. -/
theorem fundamentalVectorField_eq_zero_iff_lie_orbitMap_coadjointRepresentation_eq_zero
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ : GroupLieAlgebra I G) :
    fundamentalVectorField
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x =
          0 ↔
      ⁅ξ, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0 := by
  rw [← InfinitesimalAction.fundamental_apply, ← InfinitesimalAction.mem_isotropy_iff,
    isotropy_fundamental_eq_lieAnnihilator_orbitMap_coadjointRepresentation, mem_lieAnnihilator]

/-! ### Critical points of heights -/

/-- **The critical points of a height on a coadjoint orbit.** A point `x` of the orbit is a
critical point of the height `f_X = ⟨μ, X⟩` exactly when `X` fixes `μ x` infinitesimally,
`⁅X, μ x⁆ = 0`. -/
theorem mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff (X : GroupLieAlgebra I G)
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    x ∈ criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) ↔
      ⁅X, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0 := by
  rw [ν.isEquivariantMomentMap_coadjointOrbitForm.mem_criticalPoints_iff_mem_isotropy
      (ν.isSymplectic_coadjointOrbitForm.isNondegenerate.nondegenerate_bilinFormAt x),
    isotropy_fundamental_eq_lieAnnihilator_orbitMap_coadjointRepresentation, mem_lieAnnihilator]

/-- **The critical set of a height on a coadjoint orbit** is
`Crit(f_X) = {x | ⁅X, μ x⁆ = 0}`. -/
theorem criticalPoints_orbitMap_coadjointRepresentation_apply (X : GroupLieAlgebra I G) :
    criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) =
      {x | ⁅X, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0} :=
  Set.ext (ν.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff X)

/-! ### Hessians of heights -/

variable {ν} {X : GroupLieAlgebra I G} {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}

/-- **The Hessian of a height on a coadjoint orbit.** At a critical point `x` of the height
`f_X = ⟨μ, X⟩`, where `⁅X, μ x⁆ = 0`, the Hessian of `f_X` pairs the generators `ξ_O` and `η_O`
to `μ(x)(⁅⁅X, η⁆, ξ⁆)`. -/
theorem criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField
    (hx : ⁅X, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0) (ξ η : GroupLieAlgebra I G) :
    criticalHessian
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x)
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) η x) =
      (coadjointRepresentation ℝ I G).orbitMap ν x ⁅⁅X, η⁆, ξ⁆ := by
  have h := ν.isEquivariantMomentMap_coadjointOrbitForm
  simpa only [InfinitesimalAction.fundamental_apply] using
    h.criticalHessian_apply_apply_eq_lie_lie ν.isSymplectic_coadjointOrbitForm.isClosed
      ((ν.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff X x).2 hx)
      (h.momentCocycle_eq_zero x) ξ η

/-- **Nondegenerate critical points of a height on a coadjoint orbit.** A critical point `x` of
`f_X = ⟨μ, X⟩` is nondegenerate exactly when every `ξ` with `μ(x)(⁅⁅X, η⁆, ξ⁆) = 0` for all `η`
lies in the coadjoint stabilizer of `μ x`: the radical of the bilinear form
`(ξ, η) ↦ μ(x)(⁅⁅X, η⁆, ξ⁆)` on `𝔤` is `𝔤_(μ x)`. -/
theorem isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff
    (hx : ⁅X, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0) :
    IsManifoldNondegenerateCriticalPoint
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x ↔
      ∀ ξ : GroupLieAlgebra I G,
        (∀ η : GroupLieAlgebra I G, (coadjointRepresentation ℝ I G).orbitMap ν x ⁅⁅X, η⁆, ξ⁆ = 0) →
          ⁅ξ, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0 := by
  have hsurj := Subgroup.surjective_fundamentalVectorField (I := I)
    (isClosed_stabilizer_coadjointRepresentation I ν) x
  have hcrit := (ν.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff X x).2 hx
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  rw [isManifoldNondegenerateCriticalPoint_iff_criticalHessian]
  simp only [(ν.contMDiff_orbitMap_coadjointRepresentation_apply X).of_le h2 x,
    mem_criticalPoints.1 hcrit, true_and]
  constructor
  · -- A generator in the kernel of the Hessian vanishes, by injectivity of the Hessian.
    refine fun hinv ξ hξ ↦
      (fundamentalVectorField_eq_zero_iff_lie_orbitMap_coadjointRepresentation_eq_zero ν x ξ).1
        (hinv.injective ?_)
    refine ContinuousLinearMap.ext fun w ↦ ?_
    obtain ⟨η, rfl⟩ := hsurj w
    rw [map_zero, zero_apply,
      criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField hx, hξ η]
  · -- Conversely, the Hessian is injective, hence invertible in finite dimension.
    refine fun H ↦ criticalHessian_isInvertible_of_injective
      ((injective_iff_map_eq_zero _).2 fun v hv ↦ ?_)
    obtain ⟨ξ, rfl⟩ := hsurj v
    refine (fundamentalVectorField_eq_zero_iff_lie_orbitMap_coadjointRepresentation_eq_zero ν x ξ).2
      (H ξ fun η ↦ ?_)
    rw [← criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField hx, hv,
      zero_apply]

/-- **The Morse index of a height on a coadjoint orbit.** At a critical point `x` of
`f_X = ⟨μ, X⟩`, the Morse index of `f_X` is the negative index of inertia of any quadratic form
`Q` on `𝔤` with `Q ξ = μ(x)(⁅⁅X, ξ⁆, ξ⁆)`: the Hessian of `f_X` pulled back along the surjection
`ξ ↦ ξ_O(x)`. -/
theorem manifoldMorseIndex_orbitMap_coadjointRepresentation_apply
    (hx : ⁅X, (coadjointRepresentation ℝ I G).orbitMap ν x⁆ = 0)
    (Q : QuadraticForm ℝ (GroupLieAlgebra I G))
    (hQ : ∀ ξ, Q ξ = (coadjointRepresentation ℝ I G).orbitMap ν x ⁅⁅X, ξ⁆, ξ⁆) :
    manifoldMorseIndex
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x =
      sigNeg Q := by
  let a := InfinitesimalAction.fundamental I G
    𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
    (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
  have hsurj : Surjective (a.eval x) := fun v ↦ by
    obtain ⟨ξ, hξ⟩ := Subgroup.surjective_fundamentalVectorField (I := I)
      (isClosed_stabilizer_coadjointRepresentation I ν) x v
    exact ⟨ξ, by simpa [a] using hξ⟩
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian,
    ← QuadraticForm.sigNeg_comp_of_surjective _ hsurj]
  congr 1
  ext ξ
  simpa [a] using
    (criticalHessian_orbitMap_coadjointRepresentation_apply_fundamentalVectorField hx ξ ξ).trans
      (hQ ξ).symm

end Module.Dual
