/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Topology.Homotopy.Path

/-!
# A cofibration which is a homotopy equivalence is a strong deformation retract

Let `A ⊆ X` have the homotopy extension property.  If the inclusion `A → X` is a homotopy
equivalence, then `A` is a strong deformation retract of `X`: there is a retraction
`r : X → A` together with a homotopy from the identity of `X` to `r` followed by the inclusion
which fixes every point of `A` throughout.  Conversely a strong deformation retract always
includes as a homotopy equivalence, so for such subsets the two notions agree.

This is the form in which cofibrations upgrade homotopy equivalences to deformations: for
instance, when `f : X → Y` is a homotopy equivalence, the inclusion of `X` into the mapping
cylinder of `f` has the homotopy extension property and is a homotopy equivalence, so `X` is a
strong deformation retract of the cylinder.

No closedness assumption on `A` is needed.

## Main declarations

* `TauCeti.HasHomotopyExtensionProperty.exists_retraction_homotopic`: a homotopy left inverse of
  the inclusion of a subset with the homotopy extension property is homotopic to a retraction.
* `TauCeti.HasHomotopyExtensionProperty.homotopicRel_of_retraction`: a retraction onto a subset
  with the homotopy extension property whose composite with the inclusion is homotopic to the
  identity is homotopic to the identity relative to the subset.
* `TauCeti.HasHomotopyExtensionProperty.exists_strong_deformation_retraction`: **if a subset with
  the homotopy extension property includes as a homotopy equivalence, it is a strong deformation
  retract.**
* `TauCeti.HasHomotopyExtensionProperty.exists_strong_deformation_retraction_iff`: the
  characterisation of strong deformation retracts among such subsets.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19; Hatcher's "deformation retraction" is stationary on the subspace,
  which is the strong notion used here.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap Set unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A homotopy left inverse `g : X → A` of the inclusion of a subset with the homotopy extension
property is homotopic to a retraction of `X` onto `A`. -/
theorem HasHomotopyExtensionProperty.exists_retraction_homotopic
    (hA : HasHomotopyExtensionProperty A) (g : C(X, A))
    (hg : (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A)) :
    ∃ r : C(X, A), (∀ a : A, r a = a) ∧ r.Homotopic g := by
  obtain ⟨H⟩ := hg
  obtain ⟨G, hG₀, hG₁⟩ := hA.exists_extension g H.toContinuousMap fun a => H.apply_zero a
  refine ⟨⟨fun x => G (1, x), by fun_prop⟩, fun a => ?_, ⟨Homotopy.symm ?_⟩⟩
  · simpa using hG₁ 1 a
  · exact { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ => rfl }

/-- The tent map `t ↦ min (2 t) (2 - 2 t)` on the unit interval, which rises from `0` to `1` on
`[0, 1/2]` and falls back to `0` on `[1/2, 1]`. -/
private def tent (t : I) : I :=
  ⟨min (2 * t) (2 - 2 * t), le_min (by linarith [t.2.1]) (by linarith [t.2.2]),
    min_le_iff.2 <| (le_total (t : ℝ) (1 / 2)).imp (fun h => by linarith) fun h => by linarith⟩

private lemma continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

private lemma tent_zero : tent 0 = 0 := by
  ext
  simp [tent]

private lemma tent_one : tent 1 = 0 := by
  ext
  norm_num [tent]

section Relative

variable {r : C(X, A)} (hr : ∀ a : A, r a = a)
  (h : (ContinuousMap.id X).Homotopy ((subtypeVal A).comp r))

/-- The path which runs along the homotopy `h` from `x` to `r x`, and then back along `h` from
`r x` to itself. -/
private def outAndBack (x : X) : Path (ContinuousMap.id X x) (r x) :=
  (h.evalAt x).trans ((h.evalAt (r x)).symm.cast (by simp [hr]) (ContinuousMap.id_apply _).symm)

private lemma continuous_outAndBack : Continuous ↿(outAndBack hr h) :=
  Path.trans_continuous_family _ (h.continuous.comp continuous_swap) _
    (h.continuous.comp ((continuous_symm.comp continuous_snd).prodMk
      (continuous_subtype_val.comp (r.continuous.comp continuous_fst))))

/-- For a point `x` of `A`, the path `outAndBack hr h x` is `λ * λ⁻¹`, with `λ` the loop
`t ↦ h (t, x)`, so it is `λ` reparametrised by the tent map. -/
private lemma outAndBack_apply_of_mem {x : X} (hx : x ∈ A) (t : I) :
    outAndBack hr h x t = h (tent t, x) := by
  have hrx : (r x : X) = x := congrArg Subtype.val (hr ⟨x, hx⟩)
  rw [outAndBack, Path.trans_apply]
  split_ifs with ht
  · rw [Homotopy.evalAt_apply]
    congr 2
    ext
    simp [tent, min_eq_left (by linarith : (2 : ℝ) * t ≤ 2 - 2 * t)]
  · simp only [Path.cast_coe, Path.symm_apply, Function.comp_apply, Homotopy.evalAt_apply, hrx]
    congr 2
    ext
    simp only [tent, coe_symm_eq]
    rw [min_eq_right (by linarith)]
    ring

/-- The contraction of the paths `outAndBack hr h a`, for `a ∈ A`, onto the constant paths.  At
time `u` it follows the loop `t ↦ h (t, a)` only up to time `tent t - u`, so it is constant at
`a` wherever `u ≥ tent t`. -/
private def contraction : C(I × A, C(I, X)) :=
  ContinuousMap.curry
    ⟨fun p : (I × A) × I => h (projIcc 0 1 zero_le_one ((tent p.2 : ℝ) - p.1.1), p.1.2), by
      have := continuous_tent
      fun_prop⟩

private lemma contraction_apply (u : I) (a : A) (t : I) :
    contraction h (u, a) t = h (projIcc 0 1 zero_le_one ((tent t : ℝ) - u), a) :=
  rfl

end Relative

/-- A retraction `r` of `X` onto a subset `A` with the homotopy extension property whose
composite with the inclusion is homotopic to the identity of `X` is homotopic to the identity
relative to `A`. -/
theorem HasHomotopyExtensionProperty.homotopicRel_of_retraction
    (hA : HasHomotopyExtensionProperty A) {r : C(X, A)} (hr : ∀ a : A, r a = a)
    (hr' : ((subtypeVal A).comp r).Homotopic (ContinuousMap.id X)) :
    (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A := by
  obtain ⟨h⟩ := hr'.symm
  obtain ⟨G, hG₀, hG₁⟩ := hA.exists_extension
    (ContinuousMap.curry ⟨↿(outAndBack hr h), continuous_outAndBack hr h⟩) (contraction h)
    fun a => ContinuousMap.ext fun t => by
      rw [contraction_apply, Set.Icc.coe_zero, sub_zero, projIcc_val]
      exact (outAndBack_apply_of_mem hr h a.2 t).symm
  -- Read the extended contraction off along the path `s ↦ (tent s, s)` in the square.
  refine ⟨{ toFun := fun p => G (tent p.1, p.2) p.1
            continuous_toFun := by
              have := continuous_tent
              fun_prop
            map_zero_left := fun x => ?_
            map_one_left := fun x => ?_
            prop' := fun s x hx => ?_ }⟩
  · rw [tent_zero, hG₀, curry_apply]
    exact (outAndBack hr h x).source
  · rw [tent_one, hG₀, curry_apply]
    exact (outAndBack hr h x).target
  · simp only [ContinuousMap.coe_mk, id_apply]
    rw [hG₁ _ ⟨x, hx⟩, contraction_apply, sub_self,
      projIcc_of_le_left _ le_rfl]
    exact h.apply_zero x

/-- **A cofibration which is a homotopy equivalence is a strong deformation retract.**  If the
inclusion of a subset `A` with the homotopy extension property is a homotopy equivalence, with
homotopy inverse `g`, then there is a retraction `r : X → A` such that the identity of `X` is
homotopic, relative to `A`, to `r` followed by the inclusion. -/
theorem HasHomotopyExtensionProperty.exists_strong_deformation_retraction
    (hA : HasHomotopyExtensionProperty A) (g : C(X, A))
    (hg₁ : (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A))
    (hg₂ : ((subtypeVal A).comp g).Homotopic (ContinuousMap.id X)) :
    ∃ r : C(X, A), (∀ a : A, r a = a) ∧
      (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A := by
  obtain ⟨r, hr, hrg⟩ := hA.exists_retraction_homotopic g hg₁
  exact ⟨r, hr, hA.homotopicRel_of_retraction hr (((Homotopic.refl _).comp hrg).trans hg₂)⟩

/-- A subset with the homotopy extension property is a strong deformation retract exactly when its
inclusion is a homotopy equivalence. -/
theorem HasHomotopyExtensionProperty.exists_strong_deformation_retraction_iff
    (hA : HasHomotopyExtensionProperty A) :
    (∃ r : C(X, A), (∀ a : A, r a = a) ∧
      (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A) ↔
      ∃ g : C(X, A), (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A) ∧
        ((subtypeVal A).comp g).Homotopic (ContinuousMap.id X) := by
  refine ⟨fun ⟨r, hr, hrel⟩ => ⟨r, ?_, hrel.homotopic.symm⟩,
    fun ⟨g, hg₁, hg₂⟩ => hA.exists_strong_deformation_retraction g hg₁ hg₂⟩
  have hri : r.comp (subtypeVal A) = ContinuousMap.id A := ContinuousMap.ext hr
  rw [hri]

end TauCeti
