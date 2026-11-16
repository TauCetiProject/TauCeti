/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic
import TauCeti.Data.Set.Function

/-!
# Restriction of ambient isotopies

An ambient isotopy preserving a subset at every time restricts to an ambient isotopy of that
subset, with its subspace topology. No openness or closedness is required: the inverse total map
restricts as well. This allows an isotopy supported in a closed ball to be read as an isotopy of
the ball itself.
-/

public section

open Set unitInterval

namespace TauCeti.AmbientIsotopy

variable {X : Type*} [TopologicalSpace X]

/-- An ambient isotopy whose time-`t` slice fixes every point outside `s` preserves `s` in both
directions at time `t`, since the slice is injective. This supplies the hypothesis of
`TauCeti.AmbientIsotopy.restrict` for isotopies supported in `s`. -/
theorem apply_mem_iff_of_forall_notMem (Φ : AmbientIsotopy X) {s : Set X} {t : I}
    (hs : ∀ x ∉ s, Φ.toContinuousMap (t, x) = x) (x : X) :
    Φ.toContinuousMap (t, x) ∈ s ↔ x ∈ s :=
  ⟨fun h => by_contra fun hx => hx (hs x hx ▸ h),
    fun hx => (Φ.isHomeomorph_apply t).injective.mapsTo_of_eq_self hs hx⟩

/-- Restrict an ambient isotopy to a subset preserved by each time slice in both directions. -/
def restrict (Φ : AmbientIsotopy X) (s : Set X)
    (hs : ∀ t x, Φ.toContinuousMap (t, x) ∈ s ↔ x ∈ s) : AmbientIsotopy s where
  toFun p := ⟨Φ.toContinuousMap (p.1, p.2), (hs _ _).mpr p.2.2⟩
  continuous_toFun := by fun_prop
  map_zero_left' x := Subtype.ext (Φ.map_zero_left x)
  isHomeomorph_total' := by
    have hsi (t : I) (x : s) : Φ.symm.toContinuousMap (t, x) ∈ s :=
      (hs t _).mp (by simpa only [apply_symm_apply_slice] using x.2)
    let H : I × s ≃ₜ I × s :=
      { toFun := fun p => (p.1, ⟨Φ.toContinuousMap (p.1, p.2), (hs _ _).mpr p.2.2⟩)
        invFun := fun p => (p.1, ⟨Φ.symm.toContinuousMap (p.1, p.2), hsi _ _⟩)
        left_inv := fun p => Prod.ext rfl (Subtype.ext (Φ.symm_apply_apply_slice _ _))
        right_inv := fun p => Prod.ext rfl (Subtype.ext (Φ.apply_symm_apply_slice _ _))
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact H.isHomeomorph

/-- Restriction leaves the underlying pointwise motion unchanged. -/
@[simp]
theorem coe_restrict_apply (Φ : AmbientIsotopy X) (s : Set X)
    (hs : ∀ t x, Φ.toContinuousMap (t, x) ∈ s ↔ x ∈ s) (p : I × s) :
    ((Φ.restrict s hs).toContinuousMap p : X) = Φ.toContinuousMap (p.1, p.2) :=
  (rfl)

end TauCeti.AmbientIsotopy
