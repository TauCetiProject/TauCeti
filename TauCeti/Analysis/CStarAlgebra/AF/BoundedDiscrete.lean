/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import TauCeti.Topology.ContinuousMap.Bounded.Nonseparable
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded functions on a discrete space: locally finite-dimensional, not AF

For a discrete space `X`, the C⋆-algebra `X →ᵇ ℂ` (for `X = ℕ`, the algebra `ℓ∞`) satisfies the
local approximation condition for AF algebras: finitely many elements are approximated, to any
tolerance, by finite-valued functions, and the functions constant on the fibres of the joint
finite-valued map form a finite-dimensional C⋆-subalgebra
(`BoundedContinuousFunction.exists_finiteDimensional_approx_of_discrete`). But for infinite `X`,
`X →ᵇ ℂ` is not separable (`BoundedContinuousFunction.not_separableSpace_of_infinite`). So it is
not AF (`TauCeti.not_isAF_boundedContinuousFunction_of_infinite`; for `X = ℕ`, `ℓ∞` is not AF),
and separability is a genuine hypothesis of the local characterization of AF algebras.

## Main statements

* `BoundedContinuousFunction.exists_finiteDimensional_approx_of_discrete`: the local
  approximation condition for `X →ᵇ ℂ`, `X` discrete.
* `TauCeti.not_isAF_boundedContinuousFunction_of_infinite`: `X →ᵇ ℂ` is not AF for `X`
  infinite and discrete; in particular `ℓ∞ = ℕ →ᵇ ℂ` is not AF.
-/

public section

open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

/-- The bounded functions on `X` that are constant on the fibres of `π`, a star subalgebra of
`X →ᵇ ℂ`. -/
private def fibreConstant {X ι : Type*} [TopologicalSpace X] (π : X → ι) :
    NonUnitalStarSubalgebra ℂ (X →ᵇ ℂ) where
  carrier := {b | ∀ x y, π x = π y → b x = b y}
  add_mem' ha hb x y h := by simp [ha x y h, hb x y h]
  zero_mem' _ _ _ := rfl
  mul_mem' ha hb x y h := by simp [ha x y h, hb x y h]
  smul_mem' c _ ha x y h := by simp [ha x y h]
  star_mem' ha x y h := by simp [ha x y h]

/-- If `π` takes finitely many values, the functions constant on its fibres form a
finite-dimensional space: such a function is determined by its values on chosen points of the
fibres. -/
private theorem finiteDimensional_fibreConstant {X ι : Type*} [TopologicalSpace X] (π : X → ι)
    (hπ : (Set.range π).Finite) : FiniteDimensional ℂ (fibreConstant π) := by
  have : Finite (Set.range π) := hπ.to_subtype
  let L : fibreConstant π →ₗ[ℂ] Set.range π → ℂ :=
    { toFun b p := (b : X →ᵇ ℂ) p.property.choose
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective L fun b c h ↦ Subtype.ext (ext fun x ↦ ?_)
  have hx : π (Set.mem_range_self x : π x ∈ Set.range π).choose = π x :=
    (Set.mem_range_self x : π x ∈ Set.range π).choose_spec
  have := congrFun h ⟨π x, Set.mem_range_self x⟩
  rwa [← b.prop _ _ hx, ← c.prop _ _ hx]

/-- **The local approximation condition for bounded functions on a discrete space**: finitely
many elements of `X →ᵇ ℂ` are approximated, to any tolerance, inside a finite-dimensional
C⋆-subalgebra. -/
theorem exists_finiteDimensional_approx_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] (F : Finset (X →ᵇ ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : NonUnitalStarSubalgebra ℂ (X →ᵇ ℂ), FiniteDimensional ℂ S ∧
      ∀ a ∈ F, ∃ b ∈ S, ‖a - b‖ < ε := by
  -- Approximate the real and imaginary parts of each `a` within `ε / 4` by finite-valued
  -- functions, so that `a` is within `ε / 2` of a finite-valued function.
  have hpart (a : X →ᵇ ℂ) (p : ℂ → ℝ) (hp : ∀ z, |p z| ≤ ‖z‖) (hp' : ∀ z w, p (z - w) = p z - p w) :
      ∃ g : X → ℝ, (Set.range g).Finite ∧ ∀ x, |p (a x) - g x| < ε / 4 := by
    obtain ⟨g, hg, hd⟩ := exists_finite_range_dist_lt (mkOfDiscrete (fun x ↦ p (a x)) (2 * ‖a‖)
      fun x y ↦ by
        rw [Real.dist_eq, ← hp']
        refine (hp _).trans ((norm_sub_le _ _).trans ?_)
        linarith [a.norm_coe_le_norm x, a.norm_coe_le_norm y]) (by positivity : 0 < ε / 4)
    refine ⟨g, hg, fun x ↦ ?_⟩
    simpa [Real.dist_eq] using (dist_coe_le_dist x).trans_lt hd
  have happrox (a : X →ᵇ ℂ) : ∃ g h : X → ℝ, (Set.range g).Finite ∧ (Set.range h).Finite ∧
      ∀ x, ‖a x - (g x + h x * Complex.I)‖ ≤ ε / 2 := by
    obtain ⟨g, hg, hga⟩ := hpart a Complex.re Complex.abs_re_le_norm Complex.sub_re
    obtain ⟨h, hh, hha⟩ := hpart a Complex.im Complex.abs_im_le_norm Complex.sub_im
    refine ⟨g, h, hg, hh, fun x ↦ (Complex.norm_le_abs_re_add_abs_im _).trans ?_⟩
    simp
    linarith [hga x, hha x]
  choose G H hG hH hGH using happrox
  -- The joint finite-valued map; the approximants are constant on its fibres.
  let π : X → (F → ℝ × ℝ) := fun x a ↦ (G a x, H a x)
  have hπ : (Set.range π).Finite :=
    (Set.Finite.pi (t := fun a : F ↦ Set.range (G a) ×ˢ Set.range (H a))
      fun a ↦ (hG a).prod (hH a)).subset (by rintro _ ⟨x, rfl⟩ a -; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)
  refine ⟨fibreConstant π, finiteDimensional_fibreConstant π hπ, fun a ha ↦ ?_⟩
  have hb (x : X) : ‖(G a x + H a x * Complex.I : ℂ)‖ ≤ ‖a‖ + ε / 2 := by
    have := norm_sub_le (a x) (a x - (G a x + H a x * Complex.I))
    rw [sub_sub_cancel] at this
    linarith [hGH a x, a.norm_coe_le_norm x]
  refine ⟨mkOfDiscrete (fun x ↦ G a x + H a x * Complex.I) (2 * (‖a‖ + ε / 2)) fun x y ↦
    (dist_le_norm_add_norm _ _).trans (by linarith [hb x, hb y]), fun x y hxy ↦ ?_, ?_⟩
  · have := congrFun hxy ⟨a, ha⟩
    simp only [π, Prod.mk.injEq] at this
    simp [this.1, this.2]
  · refine lt_of_le_of_lt ((norm_le (C := ε / 2) (by positivity)).2 fun x ↦ ?_) (by linarith)
    simpa using hGH a x

end BoundedContinuousFunction

namespace TauCeti

/-- **Bounded functions on an infinite discrete space are not AF**: an AF algebra is separable,
and `X →ᵇ ℂ` is not. For `X = ℕ` this says that `ℓ∞` is not AF. -/
theorem not_isAF_boundedContinuousFunction_of_infinite {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [Infinite X] : ¬ IsAF (X →ᵇ ℂ) :=
  fun h ↦ BoundedContinuousFunction.not_separableSpace_of_infinite h.separableSpace

end TauCeti
