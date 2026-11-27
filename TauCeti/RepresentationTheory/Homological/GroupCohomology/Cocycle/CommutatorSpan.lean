/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Spanning by commutator values of one-cocycles

If `c` is a one-cocycle vanishing at an element `z` acting by a scalar `r`, its value at
`⁅g, z⁆` is `(1 - r) • c g`. If `1 - r` is a unit, these commutator values span the same submodule
as all the cocycle values. In particular, if the action spans the linear endomorphisms and some
cocycle value has a unit coordinate, the commutator values span the whole coefficient module.

This is the spanning form of the commutator argument used for normalized Selmer cocycles in
`New.Selmer.SelmerDatum.span_image_sahGroup_eq_top` in [grh-lean](https://github.com/lsernau/grh-lean)
(`grh/src/New/Congruences/Selmer/SelmerData.lean`, revision `72fead1`).
-/

public section

open scoped commutatorElement Pointwise

namespace groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] {c : G → M}

/-- If `c z = 0`, the value of a one-cocycle at `⁅g, z⁆` is the difference between `c g` and
its translate by the conjugate `g * z * g⁻¹`. -/
theorem IsCocycle₁.apply_commutatorElement_of_apply_eq_zero (hc : IsCocycle₁ c) {z : G}
    (hz : c z = 0) (g : G) : c ⁅g, z⁆ = c g - (g * z * g⁻¹) • c g := by
  have hconj : c (g * z * g⁻¹) = c ⁅g, z⁆ := by
    simpa [MulAut.conj_apply, hc ⁅g, z⁆ z, hz] using
      congrArg c (conj_eq_commutatorElement_mul (g₁ := g) (g₂ := z))
  have h := hc (g * z * g⁻¹) g
  simp only [inv_mul_cancel_right, hc g z, hz, smul_zero, zero_add, hconj] at h
  exact eq_sub_of_add_eq ((add_comm _ _).trans h.symm)

variable {R : Type*}

/-- If `z` acts as a scalar `r` with `1 - r` a unit and `c z = 0`, the values of `c` at the
commutators `⁅g, z⁆` span the same submodule as its full range. -/
theorem IsCocycle₁.span_range_commutatorElement_eq [CommRing R] [Module R M] [SMulCommClass G R M]
    (hc : IsCocycle₁ c) {z : G} {r : R}
    (hscalar : ∀ v : M, z • v = r • v) (hr : IsUnit (1 - r)) (hz : c z = 0) :
    Submodule.span R (Set.range fun g : G => c ⁅g, z⁆) = Submodule.span R (Set.range c) := by
  have h (g : G) : c ⁅g, z⁆ = (1 - r) • c g := by
    have hact : (g * z * g⁻¹) • c g = r • c g := by
      rw [mul_smul, mul_smul, hscalar, smul_comm g r, smul_inv_smul]
    rw [hc.apply_commutatorElement_of_apply_eq_zero hz, hact, sub_smul, one_smul]
  simp_rw [h]
  rw [Set.range_smul, Submodule.span_smul_eq_of_isUnit _ _ hr]

/-- If the action spans the linear endomorphisms and some cocycle value admits a
linear functional taking the value `1` there, the cocycle values span the coefficient module. -/
theorem IsCocycle₁.span_range_eq_top_of_isUnimodular [CommRing R] [Module R M]
    [SMulCommClass G R M] (hc : IsCocycle₁ c)
    (hspan : Submodule.span R (Set.range (DistribSMul.toLinearMap R M : G → Module.End R M)) = ⊤)
    {g : G} (hg : Module.IsUnimodular R (c g)) : Submodule.span R (Set.range c) = ⊤ := by
  obtain ⟨ℓ, hℓ⟩ := Module.isUnimodular_iff.mp hg
  refine Submodule.eq_top_iff'.2 fun v => ?_
  let P := Submodule.span R (Set.range c)
  let ev : Module.End R M →ₗ[R] M := LinearMap.applyₗ (c g)
  have hmap : (Submodule.span R (Set.range (DistribSMul.toLinearMap R M : G → Module.End R M))).map
      ev ≤ P := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [ev, LinearMap.applyₗ_apply_apply, DistribSMul.toLinearMap_apply]
    rw [← sub_eq_of_eq_add (hc k g)]
    have hmem (a : G) : c a ∈ P := Submodule.subset_span (Set.mem_range_self a)
    exact P.sub_mem (hmem (k * g)) (hmem k)
  rw [hspan, Submodule.map_top] at hmap
  exact hmap ⟨ℓ.smulRight v, by simp [ev, LinearMap.smulRight_apply, hℓ]⟩

/-- A set containing the commutators with `z` supplies a spanning family of cocycle values if the
action spans all endomorphisms, `z` acts by a scalar differing from `1` by a unit, the cocycle
vanishes at `z`, and some value is unimodular. The containing set need not itself be a normal
subgroup. -/
theorem IsCocycle₁.span_image_eq_top_of_commutatorElement_mem [CommRing R] [Module R M]
    [SMulCommClass G R M] (hc : IsCocycle₁ c) {S : Set G} {z : G} {r : R} (hS : ∀ g : G, ⁅g, z⁆ ∈ S)
    (hscalar : ∀ v : M, z • v = r • v) (hr : IsUnit (1 - r)) (hz : c z = 0)
    (hspan : Submodule.span R (Set.range (DistribSMul.toLinearMap R M : G → Module.End R M)) = ⊤)
    {g : G} (hg : Module.IsUnimodular R (c g)) : Submodule.span R (c '' S) = ⊤ := by
  have hle : Submodule.span R (Set.range fun k : G => c ⁅k, z⁆) ≤
      Submodule.span R (c '' S) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hS k, rfl⟩
  rw [hc.span_range_commutatorElement_eq hscalar hr hz,
    hc.span_range_eq_top_of_isUnimodular hspan hg] at hle
  exact top_unique hle

end groupCohomology
