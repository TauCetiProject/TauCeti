/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Rotational invariant curves of annulus maps

For a self-map `f` of an annulus `AddCircle ℓ × Y`, where `Y` is a topological space (in the
applications an interval of `ℝ`), a *rotational invariant curve* is a set `C` with `f '' C = C`
that is the image of a continuous injective map `c : Circle → AddCircle ℓ × Y` which is not
null-homotopic (`TauCeti.IsRotationalInvariantCurve`). Non-null-homotopy excludes the invariant
curves bounding a disc in the annulus, such as a small circle around a fixed point. For a genuine
annulus, with `ℓ ≠ 0` and `Y` a nonempty interval of `ℝ`, the second factor is contractible, so a
loop that is not null-homotopic winds around the circle factor; for an arbitrary `Y` the
nontrivial homotopy class may come from `Y` instead. This is the notion of Birkhoff's theorem on invariant
curves of twist maps, and of the rotational caustics of convex billiards (Bialy–Mironov).

The definition asks only `f '' C = C` of an arbitrary self-map `f`. We record:

* conjugating `f` by a homeomorphism `e` of the annulus carries rotational invariant curves of `f`
  to rotational invariant curves of `e ∘ f ∘ e⁻¹`
  (`TauCeti.IsRotationalInvariantCurve.image_homeomorph`); for instance a fibre reflection `I`, an
  involution, carries rotational invariant curves of `f` to those of `I ∘ f ∘ I`;
* a rotational invariant curve is nonempty and compact
  (`TauCeti.IsRotationalInvariantCurve.nonempty`, `TauCeti.IsRotationalInvariantCurve.isCompact`),
  so if it lies in an open band `a < φ y < b` for a continuous `φ : Y → ℝ`, it lies in a closed
  band `a' ≤ φ y ≤ b'` with `a < a' ≤ b' < b`
  (`TauCeti.IsRotationalInvariantCurve.exists_subset_Icc`).

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric
  billiard tables*, Ann. of Math. 196 (2022), Theorem 1.1.
-/

public section

open Set

namespace TauCeti

variable {ℓ : ℝ} {Y : Type*} [TopologicalSpace Y]

/-- A rotational invariant curve of a self-map `f` of the annulus `AddCircle ℓ × Y`: a set `C`
with `f '' C = C` that is the image of a continuous injective map from `Circle` which is not
null-homotopic (Bialy–Mironov, Theorem 1.1). -/
structure IsRotationalInvariantCurve (f : AddCircle ℓ × Y → AddCircle ℓ × Y)
    (C : Set (AddCircle ℓ × Y)) : Prop where
  /-- The curve is invariant: `f '' C = C`. -/
  image_eq : f '' C = C
  /-- The curve is the image of a continuous injective loop that is not null-homotopic. -/
  exists_curve : ∃ c : C(Circle, AddCircle ℓ × Y),
    Function.Injective c ∧ range c = C ∧ ¬ c.Nullhomotopic

namespace IsRotationalInvariantCurve

variable {f : AddCircle ℓ × Y → AddCircle ℓ × Y} {C : Set (AddCircle ℓ × Y)}

/-- Conjugating by a homeomorphism `e` of the annulus carries a rotational invariant curve `C` of
`f` to the rotational invariant curve `e '' C` of `e ∘ f ∘ e⁻¹`. -/
theorem image_homeomorph (hC : IsRotationalInvariantCurve f C)
    (e : AddCircle ℓ × Y ≃ₜ AddCircle ℓ × Y) :
    IsRotationalInvariantCurve (e ∘ f ∘ e.symm) (e '' C) := by
  obtain ⟨c, hci, hcr, hcn⟩ := hC.exists_curve
  refine ⟨?_, (e : C(AddCircle ℓ × Y, AddCircle ℓ × Y)).comp c, e.injective.comp hci, ?_,
    fun h => hcn ?_⟩
  · have he : e.symm '' (e '' C) = C := by simp [image_image]
    rw [image_comp, image_comp, he, hC.image_eq]
  · rw [ContinuousMap.coe_comp, range_comp, hcr]
    rfl
  · have h' := h.comp_right (e.symm : C(AddCircle ℓ × Y, AddCircle ℓ × Y))
    rwa [← ContinuousMap.comp_assoc, ← Homeomorph.coe_trans, Homeomorph.self_trans_symm,
      Homeomorph.coe_refl, ContinuousMap.id_comp] at h'

/-- A rotational invariant curve is nonempty. -/
theorem nonempty (hC : IsRotationalInvariantCurve f C) : C.Nonempty := by
  obtain ⟨c, -, rfl, -⟩ := hC.exists_curve
  exact range_nonempty c

/-- A rotational invariant curve is compact. -/
theorem isCompact (hC : IsRotationalInvariantCurve f C) : IsCompact C := by
  obtain ⟨c, -, rfl, -⟩ := hC.exists_curve
  exact isCompact_range c.continuous

/-- A rotational invariant curve in an open band `a < φ y < b`, for a continuous `φ : Y → ℝ`, lies
in a closed band `a' ≤ φ y ≤ b'` with `a < a' ≤ b' < b`. -/
theorem exists_subset_Icc (hC : IsRotationalInvariantCurve f C) {φ : Y → ℝ} (hφ : Continuous φ)
    {a b : ℝ} (hCab : ∀ x ∈ C, φ x.2 ∈ Ioo a b) :
    ∃ a' b', a < a' ∧ a' ≤ b' ∧ b' < b ∧ ∀ x ∈ C, φ x.2 ∈ Icc a' b' := by
  have hcont : ContinuousOn (fun x : AddCircle ℓ × Y => φ x.2) C :=
    (hφ.comp continuous_snd).continuousOn
  obtain ⟨p, hp, hpmin⟩ := hC.isCompact.exists_isMinOn hC.nonempty hcont
  obtain ⟨q, hq, hqmax⟩ := hC.isCompact.exists_isMaxOn hC.nonempty hcont
  exact ⟨φ p.2, φ q.2, (hCab p hp).1, hpmin hq, (hCab q hq).2,
    fun x hx => ⟨hpmin hx, hqmax hx⟩⟩

end IsRotationalInvariantCurve

end TauCeti
