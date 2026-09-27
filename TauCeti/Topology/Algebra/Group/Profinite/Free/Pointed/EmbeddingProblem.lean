/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.ContinuousMonoidHom
import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Basic

/-!
# The free pro-`p` group on a pointed space is projective

Let `F = F_p(X, x₀)` be the free pro-`p` group on a pointed topological space, that is the free
pro-`C` group `TauCeti.freeProCPointed C x₀` for `C` the class of finite `p`-groups. A finite
embedding problem for `F` with `p`-group kernel is a continuous surjection `π : F ↠ Q` onto a
finite group together with a surjection `α : E ↠ Q` of finite groups whose kernel is a `p`-group.
Since `Q` is a continuous finite quotient of the pro-`p` group `F`, it is a `p`-group, and then so
is `E`. A set-theoretic section of `α` normalised at `1`, composed with `π ∘ of`, is a continuous
map `X → E` killing `x₀`, because `Q` and `E` are discrete; the universal property of `F` extends
it to a continuous homomorphism `F → E`, which solves the problem because both composites agree on
the generators. So `F` solves every finite embedding problem with `p`-group kernel, and the
inverse-limit assembly of compatible finite solutions makes it projective: every continuous
homomorphism from `F` into a quotient of a profinite pro-`p` group lifts continuously.

Neither compactness of `X` nor any bound on its size is used: the universal property of
`freeProCPointed` holds for every pointed topological space. For the free pro-`p` group on a
discrete type the same statements are `TauCeti.hasPGroupSolutions_freeProP` and its corollary.

## Main results

* `TauCeti.hasPGroupSolutions_freeProCPointed`: `F_p(X, x₀)` solves every finite embedding problem
  with `p`-group kernel.
* `TauCeti.isProjective_freeProCPointed`: `F_p(X, x₀)` is projective.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §5.9.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Chapter 7.
-/

public section

namespace TauCeti

universe u v w

open freeProCPointed

variable (p : ℕ) {X : Type u} [TopologicalSpace X] (x₀ : X)

/-- **The free pro-`p` group on a pointed space solves the finite embedding problems with
`p`-group kernel**: for every continuous surjection `π : F_p(X, x₀) ↠ Q` onto a finite group and
every surjection `α : E ↠ Q` of finite groups with `ker α` a `p`-group, some continuous
homomorphism `β : F_p(X, x₀) → E` satisfies `α ∘ β = π`. -/
theorem hasPGroupSolutions_freeProCPointed :
    HasPGroupSolutions p (freeProCPointed (finiteGroupClassP.{u} p) x₀) := by
  classical
  apply hasPGroupSolutions_iff.mpr
  intro P hP
  let _ : TopologicalSpace P.Q := ⊥
  let _ : TopologicalSpace P.E := ⊥
  have : DiscreteTopology P.Q := ⟨rfl⟩
  have : DiscreteTopology P.E := ⟨rfl⟩
  have hF : IsProP p (freeProCPointed (finiteGroupClassP.{u} p) x₀) :=
    isProC_finiteGroupClassP_iff.mp (isProC_freeProCPointed (finiteGroupClassP.{u} p) x₀)
  have hπ : Continuous P.π := P.π.continuous_iff_isOpen_ker.mpr P.isOpen_ker_π
  have hQ : IsPGroup p P.Q := isProP_iff_isPGroup.mp (hF.of_surjective P.π hπ P.π_surjective)
  have hE : IsPGroup p P.E := IsPGroup.of_subgroup_of_quotient hP
    (hQ.of_equiv (QuotientGroup.quotientKerEquivOfSurjective P.α P.α_surjective).symm)
  have hE' : IsProC (finiteGroupClassP.{u} p) P.E := isProC_finiteGroupClassP_iff.mpr hE.isProP
  -- A set-theoretic section of `α`, normalised at `1`.
  set σ : P.Q → P.E :=
    fun q ↦ Function.surjInv P.α_surjective q * (Function.surjInv P.α_surjective 1)⁻¹ with hσ_def
  have hσ : ∀ q, P.α (σ q) = q := fun q ↦ by simp [hσ_def, Function.surjInv_eq]
  -- Composed with `π ∘ of`, it is continuous and kills the base point.
  set t : X → P.E := σ ∘ P.π ∘ of (finiteGroupClassP.{u} p) x₀ with ht_def
  have ht : Continuous t := continuous_of_discreteTopology.comp (hπ.comp (continuous_of _ x₀))
  have ht₀ : t x₀ = 1 := by simp [ht_def, hσ_def, of_basePoint]
  have hcomp : (⟨P.α, continuous_of_discreteTopology⟩ : P.E →ₜ* P.Q).comp (lift hE' t ht ht₀) =
      ⟨P.π, hπ⟩ := by
    apply hom_ext
    intro x
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_mk P.α,
      ContinuousMonoidHom.coe_mk P.π, lift_of]
    exact hσ _
  exact ⟨(lift hE' t ht ht₀).toMonoidHom, FiniteEmbeddingProblem.isSolution_iff.mpr
    ⟨(lift hE' t ht ht₀).toMonoidHom.continuous_iff_isOpen_ker.mp (lift hE' t ht ht₀).continuous,
      MonoidHom.ext fun g ↦ DFunLike.congr_fun hcomp g⟩⟩

/-- **The free pro-`p` group on a pointed space is projective**: every continuous homomorphism
from `F_p(X, x₀)` into a quotient of a profinite pro-`p` group lifts continuously, with the
covering group and the quotient in arbitrary universes. -/
theorem isProjective_freeProCPointed :
    IsProjective.{u, v, w} p (freeProCPointed (finiteGroupClassP.{u} p) x₀) :=
  isProjective_of_hasPGroupSolutions (hasPGroupSolutions_freeProCPointed p x₀)

end TauCeti
