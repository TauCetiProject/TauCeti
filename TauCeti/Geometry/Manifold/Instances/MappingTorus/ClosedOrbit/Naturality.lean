/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Iterate.Basic
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Map

/-!
# Covers, conjugacies and iterates of closed suspension orbits

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism with smooth mapping torus `Y_φ`, and let
`γ : ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`, be the closed orbit of the suspension flow through a point `x`
of period `d` (`TauCeti.SmoothMappingTorus.closedOrbit`). This file records how closed orbits and
their orbit tori `(s, θ) ↦ (s, γ θ)` behave under the three natural operations on periodic orbits.

* **Multiple covers.** For positive periods `d` and `m` with `m` a multiple of `d`, the point `x`
  also has period `m`, and its closed orbit of period `m` is the closed orbit of period `d`
  precomposed with the covering map
  `ℝ / mℤ → ℝ / dℤ` (`AddCircle.coverMap`). That covering map is an orientation-preserving local
  diffeomorphism of degree `m / d`, so the closed orbit of period `m` is the `m / d`-fold cover of
  the closed orbit of period `d`; the same holds for the orbit tori.
* **Conjugacies.** A map `g : M → N` intertwining `φ` and `ψ : N ≃ₘ^n⟮J, J⟯ N` induces the map
  `[t, x] ↦ [t, g x]` of mapping tori (`TauCeti.SmoothMappingTorus.map`). It sends the closed orbit
  through `x` to the closed orbit through `g x`, with the same parametrization, and likewise for
  the orbit tori. The diffeomorphism of mapping tori induced by a conjugacy is a special case.
* **Iterates.** For `k : ℤ`, a point `x` of period `d` for `φ ^ k` has period `k.natAbs * d`
  for `φ`. The natural map `Y_(φ^k) → Y_φ`, `[t, x] ↦ [k t, x]`
  (`TauCeti.SmoothMappingTorus.iterateMap`), sends the closed orbit of `φ ^ k` through `x` to the
  closed orbit of `φ` through `x`. When `k ≠ 0` and `d ≠ 0`, the parameter map is the signed
  rescaling `ℝ / dℤ ≃ ℝ / (k.natAbs * d)ℤ`, `[t] ↦ [k t]`, reversing orientation for negative `k`.
  For any `d`, the two orbit images agree when `k ≠ 0`.

## Main results

* `TauCeti.SmoothMappingTorus.closedOrbit_coverMap`,
  `TauCeti.SmoothMappingTorus.orbitTorus_comp_prodMap_coverMap`: closed orbits and orbit tori of a
  multiple period factor through the covering map of the parameter circles.
* `TauCeti.SmoothMappingTorus.map_closedOrbit`,
  `TauCeti.SmoothMappingTorus.image_map_range_closedOrbit`,
  `TauCeti.SmoothMappingTorus.prodMap_map_orbitTorus`: induced maps of mapping tori send closed
  orbits and orbit tori to closed orbits and orbit tori.
* `TauCeti.SmoothMappingTorus.iterateMap_closedOrbit_coe`,
  `TauCeti.SmoothMappingTorus.iterateMap_comp_closedOrbit`,
  `TauCeti.SmoothMappingTorus.image_iterateMap_range_closedOrbit`: the iterate map sends closed
  orbits of `φ ^ k` to closed orbits of `φ`, with target period `k.natAbs * d`. The parameter
  rescaling requires nonzero `k` and `d`; the image equality requires only nonzero `k`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (closed orbits of the mapping torus, their
  multiple covers, and the periodic orbits of the monodromy).
-/

public noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {φ : M ≃ₘ^n⟮I, I⟯ M} {d m : ℕ} {x : M}

/-! ### Multiple covers -/

section Cover

variable (h : IsPeriodicPt φ d x) (hm : IsPeriodicPt φ m x)
  (hdm : (m : ℝ) ∈ AddSubgroup.zmultiples (d : ℝ))

/-- For a multiple `m` of the period `d`, the closed orbit of period `m` is the closed orbit of
period `d` precomposed with the covering map `ℝ / mℤ → ℝ / dℤ`. -/
theorem closedOrbit_coverMap (θ : AddCircle (m : ℝ)) :
    closedOrbit φ h (AddCircle.coverMap hdm θ) = closedOrbit φ hm θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H t => rw [AddCircle.coverMap_coe, closedOrbit_coe, closedOrbit_coe]

/-- For a multiple `m` of the period `d`, the orbit torus of period `m` is the orbit torus of
period `d` precomposed with the covering map `ℝ / mℤ → ℝ / dℤ` of the second circle. -/
theorem orbitTorus_comp_prodMap_coverMap :
    orbitTorus φ h ∘ Prod.map id (AddCircle.coverMap hdm) = orbitTorus φ hm :=
  funext fun p ↦ by simp [closedOrbit_coverMap h hm hdm]

end Cover

/-! ### Conjugacies -/

section Map

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] {ψ : N ≃ₘ^n⟮J, J⟯ N} (g : M → N) (hg : Semiconj g φ ψ)
  (h : IsPeriodicPt φ d x)

/-- The map of mapping tori induced by a map `g` intertwining `φ` and `ψ` sends the closed orbit
through `x` to the closed orbit through `g x`, with the same parametrization. -/
@[simp]
theorem map_closedOrbit (θ : AddCircle (d : ℝ)) :
    map φ ψ g hg (closedOrbit φ h θ) = closedOrbit ψ (h.map hg) θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H t => rw [closedOrbit_coe, map_mk, closedOrbit_coe]

/-- The map of mapping tori induced by a map `g` intertwining `φ` and `ψ` sends the image of the
closed orbit through `x` onto the image of the closed orbit through `g x`. -/
theorem image_map_range_closedOrbit :
    map φ ψ g hg '' range (closedOrbit φ h) = range (closedOrbit ψ (h.map hg)) := by
  rw [← range_comp]
  exact congrArg range (funext (map_closedOrbit g hg h))

/-- The map `(s, [t, y]) ↦ (s, [t, g y])` induced by a map `g` intertwining `φ` and `ψ` sends the
orbit torus through `x` to the orbit torus through `g x`, with the same parametrization. -/
theorem prodMap_map_orbitTorus (p : UnitAddCircle × AddCircle (d : ℝ)) :
    Prod.map id (map φ ψ g hg) (orbitTorus φ h p) = orbitTorus ψ (h.map hg) p := by
  simp

end Map

/-! ### Iterates -/

section Iterate

variable (k : ℤ) (hx : IsPeriodicPt (φ ^ k) d x) (hx' : IsPeriodicPt φ (k.natAbs * d) x)

/-- The iterate map `Y_(φ^k) → Y_φ` sends the point `[t, x]` of the closed orbit of `φ ^ k` through
`x` to the point `[k t, x]` of the closed orbit of `φ` through `x`. -/
theorem iterateMap_closedOrbit_coe (t : ℝ) :
    iterateMap φ k (closedOrbit (φ ^ k) hx t) = closedOrbit φ hx' ((k : ℝ) * t : ℝ) := by
  rw [closedOrbit_coe, iterateMap_mk, closedOrbit_coe]

/-- When `d` and `k.natAbs * d` are nonzero, the iterate map `Y_(φ^k) → Y_φ` sends the closed
orbit of `φ ^ k` through `x` to the closed orbit of `φ` through `x`, after the signed rescaling
`ℝ / dℤ ≃ ℝ / (k.natAbs * d)ℤ`, `[t] ↦ [k t]`. For negative `k`, the factor `k.sign • θ`
reverses the parameter before the positive rescaling. -/
theorem iterateMap_comp_closedOrbit (hd : (d : ℝ) ≠ 0)
    (hkd : ((k.natAbs * d : ℕ) : ℝ) ≠ 0) :
    iterateMap φ k ∘ closedOrbit (φ ^ k) hx =
      closedOrbit φ hx' ∘ AddCircle.equivAddCircle (d : ℝ) ((k.natAbs * d : ℕ) : ℝ) hd hkd ∘
        (fun θ ↦ k.sign • θ) := by
  funext θ
  induction θ using QuotientAddGroup.induction_on with | H t => ?_
  simp only [comp_apply, iterateMap_closedOrbit_coe k hx hx', ← AddCircle.coe_zsmul,
    AddCircle.equivAddCircle_apply_mk, zsmul_eq_mul, Nat.cast_mul]
  congr 2
  have hsign : (k.sign : ℝ) * (k.natAbs : ℝ) = (k : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using
      congrArg (fun j : ℤ ↦ (j : ℝ)) k.sign_mul_natAbs
  rw [← hsign]
  field_simp

/-- For nonzero `k`, the iterate map `Y_(φ^k) → Y_φ` sends the image of the closed orbit of
`φ ^ k` through `x` onto the image of the closed orbit of `φ` through `x`. -/
theorem image_iterateMap_range_closedOrbit (hk : k ≠ 0) :
    iterateMap φ k '' range (closedOrbit (φ ^ k) hx) = range (closedOrbit φ hx') := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [← range_comp]
  ext y
  constructor
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with
    | H t => exact ⟨((k : ℝ) * t : ℝ), (iterateMap_closedOrbit_coe k hx hx' t).symm⟩
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with
    | H t =>
      refine ⟨((t / k : ℝ) : AddCircle (d : ℝ)), ?_⟩
      rw [comp_apply, iterateMap_closedOrbit_coe k hx hx', mul_div_cancel₀ t hk']

end Iterate

end TauCeti.SmoothMappingTorus
