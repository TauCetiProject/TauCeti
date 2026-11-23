/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinCInclusion
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SphereSection
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Orbit

/-!
# Topology of the lower-rank subgroup `Spinᶜ(n) ⊆ Spinᶜ(n + 1)`

The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`, `[s, z] ↦ [s, z]`
(`CliffordAlgebra.realCliffordSpinCInclusion`), is continuous for the quotient topologies. Since
`Spinᶜ(n)` is compact and `Spinᶜ(n + 1)` is Hausdorff, it is a closed embedding
(`CliffordAlgebra.isClosedEmbedding_realCliffordSpinCInclusion`), so `Spinᶜ(n)` is isomorphic as a
topological group to the stabilizer of the last coordinate vector in `Spinᶜ(n + 1)`
(`CliffordAlgebra.realCliffordSpinCContinuousMulEquivLastStabilizer`), which is closed.

The rotation of `Spinᶜ(n + 1)` moves the last coordinate vector `eₙ` to every unit vector, with
continuous local choices: near any unit vector `u₀` there is a map `g` to `Spinᶜ(n + 1)`,
continuous near `u₀`, whose rotation sends `eₙ` to `u` for every `u` near `u₀`
(`CliffordAlgebra.exists_continuousOn_realCliffordSpinC_toSpecialOrthogonal_last`). Near `eₙ`
itself, `g` is the reflection-pair section of `Spin(n + 1) → Sⁿ`
(`TauCeti.realCliffordSpinLastLocalSection`) followed by `s ↦ [s, 1]`; elsewhere it is translated
by a fixed element carrying `eₙ` to `u₀`.

With the algebraic stabilizer computation, these are the facts about structure groups behind the
restriction of a `Spinᶜ(n + 1)` structure on `E' ⊕ ℝν` to a `Spinᶜ(n)` structure on `E'`: the
points whose frames send `eₙ` to the unit normal `ν` form a principal bundle for the stabilizer,
locally trivialized by correcting a local section with `g`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinCContinuousMulEquivLastStabilizer`: `Spinᶜ(n)` is isomorphic
  as a topological group to the last-vector stabilizer in `Spinᶜ(n + 1)`.

## Main results

* `CliffordAlgebra.spinCGroup.continuous_ofSpin`: `s ↦ [s, 1]` is continuous.
* `CliffordAlgebra.continuous_realCliffordSpinCInclusion`,
  `CliffordAlgebra.isClosedEmbedding_realCliffordSpinCInclusion`: the inclusion is a continuous
  closed embedding.
* `CliffordAlgebra.isClosed_realCliffordSpinCLastStabilizer`: the stabilizer is closed.
* `CliffordAlgebra.exists_continuousOn_realCliffordSpinC_toSpecialOrthogonal_last`: continuous
  local choices of rotations carrying the last coordinate vector to a varying unit vector.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter I, §2
  and Appendix D.
-/

public section

noncomputable section

open TauCeti Topology

namespace CliffordAlgebra

/-- `Spinᶜ(n)` is compact, as a quotient of `Spin(n) × U(1)`. -/
instance instCompactSpaceRealCliffordSpinCGroup (n : ℕ) [NeZero n] :
    CompactSpace (realCliffordSpinCGroup n) :=
  spinCGroup.compactSpace_of_posDef_or_negDef _ _ (.inl (posDef_realCliffordForm_zero n))

/-- The inclusion `Spin(Q) → Spinᶜ(Q)`, `s ↦ [s, 1]`, is continuous for the quotient topology. -/
@[fun_prop]
theorem spinCGroup.continuous_ofSpin {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (hQ : Q ≠ 0) : Continuous (spinCGroup.ofSpin Q hQ) := by
  have h : Continuous (fun s : spinGroup Q ↦ spinCGroup.mk Q hQ (s, 1)) := by
    simpa only [spinCGroup.coe_mk, Function.comp_def, id_eq] using
      (QuotientGroup.isQuotientMap_mk _).continuous.comp (continuous_id.prodMk continuous_const)
  exact h.congr fun s ↦ (spinCGroup.ofSpin_apply Q hQ s).symm

variable (n : ℕ) [NeZero n]

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is continuous** for the quotient topologies. -/
@[fun_prop]
theorem continuous_realCliffordSpinCInclusion :
    Continuous (realCliffordSpinCInclusion n) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, realCliffordSpinCInclusion_mk]
  have h : Continuous (fun p : realCliffordSpinGroupZero n × Circle ↦
      spinCGroup.mk (realCliffordForm (n + 1) 0) (nondegenerate_realCliffordForm (n + 1) 0).ne_zero
        (realCliffordSpinInclusion n p.1, p.2)) := by
    simpa only [spinCGroup.coe_mk, Function.comp_def] using
      (QuotientGroup.isQuotientMap_mk _).continuous.comp
        (((continuous_realCliffordSpinInclusion n).comp continuous_fst).prodMk continuous_snd)
  exact h

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is a closed embedding**: it is a continuous
injection from a compact space to a Hausdorff space. -/
theorem isClosedEmbedding_realCliffordSpinCInclusion :
    IsClosedEmbedding (realCliffordSpinCInclusion n) :=
  (continuous_realCliffordSpinCInclusion n).isClosedEmbedding
    (realCliffordSpinCInclusion_injective n)

/-- The last-vector stabilizer in `Spinᶜ(n + 1)` is closed. -/
theorem isClosed_realCliffordSpinCLastStabilizer :
    IsClosed (realCliffordSpinCLastStabilizer n : Set (realCliffordSpinCGroup (n + 1))) := by
  rw [← range_realCliffordSpinCInclusion, MonoidHom.coe_range]
  exact (isClosedEmbedding_realCliffordSpinCInclusion n).isClosed_range

/-- **`Spinᶜ(n)` is isomorphic as a topological group to the last-vector stabilizer in
`Spinᶜ(n + 1)`**, through the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
def realCliffordSpinCContinuousMulEquivLastStabilizer :
    realCliffordSpinCGroup n ≃ₜ* realCliffordSpinCLastStabilizer n :=
  ContinuousMulEquiv.mk'
    (((isClosedEmbedding_realCliffordSpinCInclusion n).isEmbedding.codRestrict _
        (realCliffordSpinCInclusion_mem_lastStabilizer n)).toHomeomorphOfSurjective
      fun y ↦ by
        obtain ⟨x, rfl⟩ := (realCliffordSpinCEquivLastStabilizer n).surjective y
        exact ⟨x, Subtype.ext (coe_realCliffordSpinCEquivLastStabilizer_apply n x).symm⟩)
    fun x y ↦ Subtype.ext (map_mul (realCliffordSpinCInclusion n) x y)

/-- The topological stabilizer isomorphism is the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
@[simp]
theorem coe_realCliffordSpinCContinuousMulEquivLastStabilizer_apply
    (x : realCliffordSpinCGroup n) :
    (realCliffordSpinCContinuousMulEquivLastStabilizer n x : realCliffordSpinCGroup (n + 1)) =
      realCliffordSpinCInclusion n x :=
  (rfl)

/-- **Continuous local rotations onto the unit sphere.** Near every unit vector `u₀` of `ℝⁿ⁺¹`
there is a map `g` to `Spinᶜ(n + 1)`, continuous near `u₀`, whose rotation carries the last
coordinate vector to `u` for every unit vector `u` near `u₀`. -/
theorem exists_continuousOn_realCliffordSpinC_toSpecialOrthogonal_last
    (u₀ : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}) :
    ∃ U : Set {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1},
      IsOpen U ∧ u₀ ∈ U ∧
      ∃ g : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} →
          realCliffordSpinCGroup (n + 1),
        ContinuousOn g U ∧ ∀ u ∈ U,
          (spinCGroup.toSpecialOrthogonal _ _ (g u) :
              (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Pi.single (Fin.last n) 1) = u.val := by
  have hrank : 2 ≤ Module.finrank ℝ (Fin (n + 1) → ℝ) := by
    rw [Module.finrank_fin_fun]
    have := NeZero.ne n
    omega
  obtain ⟨s, hs⟩ := exists_spinVectorAction_eq_of_posDef (realCliffordForm (n + 1) 0)
    (posDef_realCliffordForm_zero (n + 1)) hrank
    ((realCliffordForm_zero_single_one (n + 1) (Fin.last n)).trans u₀.property.symm)
  -- Move a unit vector back by `s⁻¹`; the result is still a unit vector.
  let φ : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} →
      {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} := fun u ↦
    ⟨spinVectorAction _ s⁻¹ u.val, (spinVectorAction_map_app _ _ _).trans u.property⟩
  have hφ : Continuous φ :=
    (((spinVectorAction (realCliffordForm (n + 1) 0) s⁻¹).toLinearMap
      |>.continuous_of_finiteDimensional).comp continuous_subtypeVal).subtype_mk _
  have hφs (u) : spinVectorAction _ s (φ u).val = u.val := by
    simp only [φ, ← mul_apply_eq_comp, ← spinVectorAction_mul, mul_inv_cancel,
      spinVectorAction_one, LinearEquiv.refl_apply]
  refine ⟨φ ⁻¹' realCliffordSpinLastUnitNeighborhood n,
    (isOpen_realCliffordSpinLastUnitNeighborhood n).preimage hφ, ?_,
    fun u ↦ spinCGroup.ofSpin _ _ (s * realCliffordSpinLastLocalSection n (φ u)), ?_, ?_⟩
  · have hφ₀ : (φ u₀).val = Pi.single (Fin.last n) 1 := by
      simp only [φ, ← hs, ← mul_apply_eq_comp, ← spinVectorAction_mul, inv_mul_cancel,
        spinVectorAction_one, LinearEquiv.refl_apply]
    rw [Set.mem_preimage, mem_realCliffordSpinLastUnitNeighborhood, hφ₀]
    intro h
    have h1 := congrFun h (Fin.last n)
    simp only [Pi.single_eq_same, Pi.neg_apply] at h1
    linarith
  · exact (spinCGroup.continuous_ofSpin _ _).comp_continuousOn
      (continuousOn_const.mul ((continuousOn_realCliffordSpinLastLocalSection n).comp
        hφ.continuousOn fun _ hu ↦ hu))
  · intro u hu
    rw [spinCGroup.toSpecialOrthogonal_ofSpin, coe_spinToSpecialOrthogonal_apply,
      spinVectorAction_mul, mul_apply_eq_comp, realCliffordSpinLastLocalSection_action _ hu,
      hφs]

end CliffordAlgebra
