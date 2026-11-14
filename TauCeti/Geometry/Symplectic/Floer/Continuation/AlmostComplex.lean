/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The continuation homotopy of almost complex structures

A Floer continuation cylinder, or a continuation neck inserted into the end of a Floer domain,
carries an `s`-dependent family of Hamiltonians `TauCeti.Floer.continuationHomotopy` and a matching
family of almost complex structures interpolating between those of its two ends. This file
constructs that family.

Fix an `ω`-compatible base structure `J₀`. The Cayley transform at `J₀` identifies the `ω`-tame
structures with the convex Cayley ball, and the `ω`-compatible ones with the convex compatible
Cayley ball. Given families `J₁ t x` and `J₂ t x` of tame structures, the *continuation homotopy*
`TauCeti.Floer.continuationAlmostComplex` is the structure whose Cayley coordinate at `(s, t)` is

`(1 - β(s)) • cayley (J₁ t x) + β(s) • cayley (J₂ t x)`,

where `β` is the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. It is `J₁` for
`s ≤ 0` and `J₂` for `s ≥ 1`, tame, compatible when `J₁` and `J₂` are, has period one in `t` when
`J₁` and `J₂` do, and is smooth jointly in `(s, t)` and the external point `x` when they are. It is
the almost complex structure of a continuation cylinder, just as
`TauCeti.Floer.continuationHomotopy` is its Hamiltonian.

The structures act on a fixed symplectic vector space `(V, ω)`; the external point may be a target
point (for a vector space target, `M = V`).

## Main definitions

* `TauCeti.Floer.continuationAlmostComplex`: the continuation homotopy of almost complex
  structures.

## Main results

* `TauCeti.Floer.cayley_continuationAlmostComplex`: its Cayley coordinate.
* `TauCeti.Floer.tames_continuationAlmostComplex`,
  `TauCeti.Floer.compatible_continuationAlmostComplex`: tameness and compatibility.
* `TauCeti.Floer.continuationAlmostComplex_of_nonpos`,
  `TauCeti.Floer.continuationAlmostComplex_of_one_le`: its two ends.
* `TauCeti.Floer.contMDiff_continuationAlmostComplex`: joint smoothness.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the spaces of tame and compatible structures.
-/

public noncomputable section

open Set Real Manifold Topology Function

namespace TauCeti.Floer

variable {M : Type*}

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

variable {J₁ J₂ : ℝ → M → AlmostComplexStructure V} {hJ₁ : ∀ t x, ω.Tames (J₁ t x)}
  {hJ₂ : ∀ t x, ω.Tames (J₂ t x)}

/-- The continuation homotopy of almost complex structures from the family `J₁ t x` to the family
`J₂ t x` of `ω`-tame structures, relative to an `ω`-compatible base structure `J₀`. At
`z = (s, t)` and `x ∈ M` it is the inverse Cayley transform, relative to `J₀`, of
`(1 - β(s)) • cayley (J₁ t x) + β(s) • cayley (J₂ t x)`, where `β` is the smooth transition
function. It is `J₁ t x` for `s ≤ 0` and `J₂ t x` for `s ≥ 1`. -/
def continuationAlmostComplex (h₀ : ω.Compatible J₀) (J₁ J₂ : ℝ → M → AlmostComplexStructure V)
    (hJ₁ : ∀ t x, ω.Tames (J₁ t x)) (hJ₂ : ∀ t x, ω.Tames (J₂ t x)) (z : ℝ × ℝ) (x : M) :
    AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨(1 - smoothTransition z.1) • J₀.cayley (J₁ z.2 x) +
        smoothTransition z.1 • J₀.cayley (J₂ z.2 x),
      h₀.tames.convex_cayleyBall (h₀.cayley_mem_cayleyBall (hJ₁ z.2 x))
        (h₀.cayley_mem_cayleyBall (hJ₂ z.2 x)) (sub_nonneg.2 (smoothTransition.le_one _))
        (smoothTransition.nonneg _) (sub_add_cancel _ _)⟩

/-- The continuation homotopy is tamed by `ω`. -/
theorem tames_continuationAlmostComplex (h₀ : ω.Compatible J₀) (z : ℝ × ℝ) (x : M) :
    ω.Tames (continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the continuation homotopy, relative to `J₀`, at `z = (s, t)` is
`(1 - β(s)) • cayley (J₁ t x) + β(s) • cayley (J₂ t x)`. This characterizes the structure, since
the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_continuationAlmostComplex (h₀ : ω.Compatible J₀) (z : ℝ × ℝ) (x : M) :
    J₀.cayley (continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x) =
      (1 - smoothTransition z.1) • J₀.cayley (J₁ z.2 x) +
        smoothTransition z.1 • J₀.cayley (J₂ z.2 x) := by
  rw [continuationAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The continuation homotopy is `ω`-compatible when the two families are. -/
theorem compatible_continuationAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ₁c : ∀ t x, ω.Compatible (J₁ t x)) (hJ₂c : ∀ t x, ω.Compatible (J₂ t x)) (z : ℝ × ℝ)
    (x : M) : ω.Compatible (continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x) := by
  refine (h₀.cayley_mem_compatibleCayleyBall_iff (tames_continuationAlmostComplex h₀ z x)).mp ?_
  rw [cayley_continuationAlmostComplex]
  exact h₀.tames.convex_compatibleCayleyBall
    ((h₀.cayley_mem_compatibleCayleyBall_iff (hJ₁ z.2 x)).mpr (hJ₁c z.2 x))
    ((h₀.cayley_mem_compatibleCayleyBall_iff (hJ₂ z.2 x)).mpr (hJ₂c z.2 x))
    (sub_nonneg.2 (smoothTransition.le_one _)) (smoothTransition.nonneg _) (sub_add_cancel _ _)

/-- The continuation homotopy is `J₁ t x` for `s ≤ 0`. -/
@[simp]
theorem continuationAlmostComplex_of_nonpos (h₀ : ω.Compatible J₀) {z : ℝ × ℝ} (hz : z.1 ≤ 0)
    (x : M) : continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x = J₁ z.2 x :=
  h₀.eq_of_cayley_eq (tames_continuationAlmostComplex h₀ z x) (hJ₁ z.2 x) (by
    simp [smoothTransition.zero_of_nonpos hz])

/-- The continuation homotopy is `J₂ t x` for `s ≥ 1`. -/
@[simp]
theorem continuationAlmostComplex_of_one_le (h₀ : ω.Compatible J₀) {z : ℝ × ℝ} (hz : 1 ≤ z.1)
    (x : M) : continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x = J₂ z.2 x :=
  h₀.eq_of_cayley_eq (tames_continuationAlmostComplex h₀ z x) (hJ₂ z.2 x) (by
    simp [smoothTransition.one_of_one_le hz])

/-- The continuation homotopy from a family to itself is that family at every `s`. -/
@[simp]
theorem continuationAlmostComplex_self (h₀ : ω.Compatible J₀) (z : ℝ × ℝ) (x : M) :
    continuationAlmostComplex h₀ J₁ J₁ hJ₁ hJ₁ z x = J₁ z.2 x :=
  h₀.eq_of_cayley_eq (tames_continuationAlmostComplex h₀ z x) (hJ₁ z.2 x) (by
    rw [cayley_continuationAlmostComplex, ← add_smul, sub_add_cancel, one_smul])

/-- The continuation homotopy of two families of period one in `t` has period one in `t`. -/
theorem periodic_continuationAlmostComplex (h₀ : ω.Compatible J₀) (hJ₁p : Periodic J₁ 1)
    (hJ₂p : Periodic J₂ 1) (s : ℝ) (x : M) :
    Periodic (fun t => continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ (s, t) x) 1 := fun t =>
  h₀.eq_of_cayley_eq (tames_continuationAlmostComplex h₀ _ x)
    (tames_continuationAlmostComplex h₀ _ x) (by simp [hJ₁p t, hJ₂p t])


end Algebraic

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The Cayley transform of the continuation homotopy, as a continuous endomorphism, is the
`β`-weighted combination of the Cayley transforms of the two families. -/
theorem toContinuousLinearMap_cayley_continuationAlmostComplex (h₀ : ω.Compatible J₀)
    {J₁ J₂ : ℝ → M → AlmostComplexStructure V} {hJ₁ : ∀ t x, ω.Tames (J₁ t x)}
    {hJ₂ : ∀ t x, ω.Tames (J₂ t x)} (z : ℝ × ℝ) (x : M) :
    LinearMap.toContinuousLinearMap (J₀.cayley (continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ z x)) =
      (1 - smoothTransition z.1) • LinearMap.toContinuousLinearMap (J₀.cayley (J₁ z.2 x)) +
        smoothTransition z.1 • LinearMap.toContinuousLinearMap (J₀.cayley (J₂ z.2 x)) := by
  rw [cayley_continuationAlmostComplex, map_add, map_smul, map_smul]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The continuation homotopy is smooth.** For families `J₁ t x` and `J₂ t x` of `ω`-tame
structures which are `C^n` on `ℝ × M`, the continuation homotopy is `C^n` jointly in
`z = (s, t)` and `x`. -/
theorem contMDiff_continuationAlmostComplex (h₀ : ω.Compatible J₀)
    {J₁ J₂ : ℝ → M → AlmostComplexStructure V} {hJ₁ : ∀ t x, ω.Tames (J₁ t x)}
    {hJ₂ : ∀ t x, ω.Tames (J₂ t x)} {n : ℕ∞}
    (hJ₁s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJ₂s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : (ℝ × ℝ) × M =>
        LinearMap.toContinuousLinearMap
          (continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ p.1 p.2).toLinearMap) := by
  refine h₀.contMDiff_of_contMDiff_cayley (fun _ => tames_continuationAlmostComplex h₀ _ _) ?_
  simp only [toContinuousLinearMap_cayley_continuationAlmostComplex]
  -- Each Cayley transform is smooth in `(t, x)`, and the weights are smooth in `s`.
  have hst : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ).prod I) n
      (fun p : (ℝ × ℝ) × M => (p.1.2, p.2)) :=
    (contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hβ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n
      (fun p : (ℝ × ℝ) × M => smoothTransition p.1.1) :=
    (smoothTransition.contDiff.comp contDiff_fst).contMDiff.comp contMDiff_fst
  have h₁ := (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J₁ p.1 p.2)
    (fun p => hJ₁ p.1 p.2) hJ₁s).comp hst
  have h₂ := (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J₂ p.1 p.2)
    (fun p => hJ₂ p.1 p.2) hJ₂s).comp hst
  exact ((contMDiff_const.sub hβ).smul h₁).add (hβ.smul h₂)

end Smooth

end TauCeti.Floer
