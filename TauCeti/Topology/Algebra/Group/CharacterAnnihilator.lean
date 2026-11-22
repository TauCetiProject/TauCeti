/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.Group.AddSubgroup.CharacterAnnihilator

/-!
# Topology of character annihilators

For a character pairing `(v, w) ↦ ψ (L v w)` and an additive subgroup `U` of `V`, this file
proves that the annihilator `U.characterAnnihilator ψ L` is closed when each `ψ (L u ·)` is
continuous, and open when `U` is compact, `ψ` is circle-valued and the pairing is jointly
continuous on `U × W`. At a finite place of a local field this makes the annihilator of a
compact open lattice open and closed (its compactness also needs a nondegenerate pairing and
is not proved here), and it is what makes the Fourier transform of a compactly supported
function locally constant.

The openness argument is the classical one. If `w₀` lies in the annihilator, the open set of
pairs `(v, w)` with `ψ (L v w)` in the right half of the circle contains `U × {w₀}`, so the tube
lemma gives a neighbourhood `B` of `w₀` with `U × B` inside it. For `w ∈ B` the homomorphism
`u ↦ ψ (L u w)` maps the group `U` into the right half of the circle, and the only such subgroup
of the circle is trivial (Mathlib's `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two`).
The same argument applied to the quotients `ψ (L v w) / ψ (L v w₀)` shows that every coset
`w₀ + U.characterAnnihilator ψ L` is open, without any assumption on the topology of addition
in `W`.

Compactness of `U` cannot be dropped: over `ℝ` with `ψ x = exp (2πix)` the annihilator of `ℤ`
is `ℤ`, which is closed but not open.

## Main results

* `AddSubgroup.isClosed_characterAnnihilator`: the annihilator is closed.
* `AddSubgroup.isOpen_setOf_sub_mem_characterAnnihilator`: for compact `U`, each coset of the
  annihilator is open.
* `AddSubgroup.isOpen_characterAnnihilator`: for compact `U`, the annihilator is open.
* `AddSubgroup.isLocallyConstant_characterPairing`: the restricted character is locally constant
  as a function of the frequency.
-/

public section

open Real Set

variable {R V W : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

namespace AddSubgroup

/-- The annihilator is closed as soon as every `w ↦ ψ (L u w)` with `u ∈ U` is continuous and
points are closed in the codomain of `ψ`. -/
theorem isClosed_characterAnnihilator {M : Type*} [Monoid M] [TopologicalSpace M] [T1Space M]
    [TopologicalSpace W] (U : AddSubgroup V) {ψ : AddChar R M} {L : V →ₗ[R] W →ₗ[R] R}
    (hψL : ∀ u ∈ U, Continuous fun w ↦ ψ (L u w)) :
    IsClosed (U.characterAnnihilator ψ L : Set W) := by
  have h : (U.characterAnnihilator ψ L : Set W) = ⋂ u ∈ U, (fun w ↦ ψ (L u w)) ⁻¹' {1} := by
    ext
    simp
  rw [h]
  exact isClosed_biInter fun u hu ↦ isClosed_singleton.preimage (hψL u hu)

variable {U : AddSubgroup V} {ψ : AddChar R Circle} {L : V →ₗ[R] W →ₗ[R] R}

/-- A circle-valued character pairing turns a difference in the second variable into a
quotient. -/
private lemma map_sub_right_eq_div (u : V) (w w₀ : W) :
    ψ (L u (w - w₀)) = ψ (L u w) / ψ (L u w₀) :=
  by rw [eq_div_iff_mul_eq', ← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel]

variable [TopologicalSpace V] [TopologicalSpace W]

/-- For a compact subgroup `U` and a circle-valued pairing continuous on `U × W`, every coset
`{w | w - w₀ ∈ U.characterAnnihilator ψ L}` is open. No compatibility between the topology and
the addition of `W` is needed. -/
theorem isOpen_setOf_sub_mem_characterAnnihilator (hU : IsCompact (U : Set V))
    (hψL : Continuous fun p : U × W ↦ ψ (L p.1 p.2)) (w₀ : W) :
    IsOpen {w | w - w₀ ∈ U.characterAnnihilator ψ L} := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  -- The pairs whose quotient phase against `w₀` lies in the right half of the circle.
  set S : Set (U × W) :=
    (fun p : U × W ↦ ψ (L p.1 p.2) / ψ (L p.1 w₀)) ⁻¹' Circle.centeredArc (π / 2) with hS
  have hSo : IsOpen S :=
    (Circle.isOpen_centeredArc _).preimage
      (hψL.div' (hψL.comp (continuous_fst.prodMk continuous_const)))
  have hone : (1 : Circle) ∈ Circle.centeredArc (π / 2) :=
    ⟨0, by simp [pi_pos], Circle.exp_zero⟩
  refine isOpen_iff_forall_mem_open.mpr fun w₁ hw₁ ↦ ?_
  have hsub : (univ : Set U) ×ˢ ({w₁} : Set W) ⊆ S := by
    rintro ⟨u, w⟩ ⟨-, rfl⟩
    simpa [hS, ← map_sub_right_eq_div, (mem_characterAnnihilator.mp hw₁) u u.property] using hone
  obtain ⟨A, B, -, hBo, hUA, hw₁B, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hSo hsub
  refine ⟨B, fun w hw ↦ mem_characterAnnihilator.mpr fun u hu ↦ ?_, hBo,
    hw₁B (mem_singleton w₁)⟩
  -- `n ↦ ψ (L (n • u) (w - w₀))` is the sequence of powers of `ψ (L u (w - w₀))`, and all of
  -- them lie in the right half of the circle.
  refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
  have hn := hAB (mk_mem_prod (hUA (mem_univ (⟨n • u, U.nsmul_mem hu n⟩ : U))) hw)
  rwa [mem_preimage, ← map_sub_right_eq_div, map_nsmul, LinearMap.smul_apply,
    AddChar.map_nsmul_eq_pow] at hn

/-- For a compact subgroup `U` and a circle-valued pairing continuous on `U × W`, the annihilator
`U.characterAnnihilator ψ L` is open. -/
theorem isOpen_characterAnnihilator (hU : IsCompact (U : Set V))
    (hψL : Continuous fun p : U × W ↦ ψ (L p.1 p.2)) :
    IsOpen (U.characterAnnihilator ψ L : Set W) := by
  simpa [coe_characterAnnihilator] using isOpen_setOf_sub_mem_characterAnnihilator hU hψL 0

/-- For a compact subgroup `U` and a circle-valued pairing continuous on `U × W`, the
restricted character on `U` is locally constant as a function of the frequency. -/
theorem isLocallyConstant_characterPairing (U : AddSubgroup V) (hU : IsCompact (U : Set V))
    (hψL : Continuous fun p : U × W ↦ ψ (L p.1 p.2)) :
    IsLocallyConstant (fun w (u : U) ↦ ψ (L u w)) := by
  refine IsLocallyConstant.iff_isOpen_fiber_apply.mpr fun w₀ ↦ ?_
  convert isOpen_setOf_sub_mem_characterAnnihilator hU hψL w₀ using 1
  ext w
  simp only [mem_preimage, mem_singleton_iff, funext_iff, mem_ofPred_eq,
    mem_characterAnnihilator, map_sub_right_eq_div, div_eq_one, Subtype.forall]

end AddSubgroup
