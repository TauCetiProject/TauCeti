/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Topology.Homotopy.AmbientIsotopic

/-!
# Conjugating ambient isotopies by homeomorphisms

The geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, "Encoding
conventions") mandates that isotopy and ambient isotopy be *"defined generally, then
specialised ... in full generality"*, with the single general construction underlying locally
flat isotopy (layer 2), diffeotopies (layer 3), and concordance (layer 6) -- *"none of those
should re-define it"*. This file records one such general closure property: an ambient isotopy
can be transported through a change of coordinates on its ambient space.

Given an ambient isotopy `Φ` of `Y` and a self-homeomorphism `h : Y ≃ₜ Y`, `Φ.conj h` runs `Φ`
in the coordinates moved by `h`. Its total map is obtained by pre- and post-composing `Φ`'s
total homeomorphism with `id ×ₜ h⁻¹` and `id ×ₜ h`, so it is again an ambient isotopy. The
endpoint formula records that the final homeomorphism is conjugated by `h`; downstream
specialisations to smooth or locally flat settings can add their own structure on top of this
point-set statement.

## Main definitions

* `TauCeti.AmbientIsotopy.conj`: the ambient isotopy `Φ` conjugated by a homeomorphism `h`, with
  total map `(t, y) ↦ (t, h (Φ (t, h⁻¹ y)))`.

## Main results

* `TauCeti.AmbientIsotopy.conj_finalHomeomorph`: the final homeomorphism of `Φ.conj h` is the
  conjugate `h * Φ.finalHomeomorph * h⁻¹`.
-/

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {Y : Type*} [TopologicalSpace Y]

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- **Conjugation of an ambient isotopy** by a self-homeomorphism `h`: at each time `t` run the
homeomorphism `Φ t` in the coordinates moved by `h`, giving `y ↦ h (Φ (t, h⁻¹ y))`. The total map
is a homeomorphism because it is `Φ`'s total homeomorphism pre- and post-composed with the
product homeomorphisms `id ×ₜ h⁻¹` and `id ×ₜ h`. -/
noncomputable def conj (h : Y ≃ₜ Y) : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => h (Φ.toContinuousMap (p.1, h.symm p.2)), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, h (Φ.toContinuousMap (p.1, h.symm p.2))))
        = ⇑((Homeomorph.refl I).prodCongr h) ∘ Φ.totalMap ∘
          ⇑((Homeomorph.refl I).prodCongr h.symm) := by
      funext p
      obtain ⟨t, y⟩ := p
      simp [Homeomorph.coe_prodCongr, Function.comp_def, totalMap]
    rw [heq]
    exact (((Homeomorph.refl I).prodCongr h).isHomeomorph.comp Φ.isHomeomorph_total).comp
      ((Homeomorph.refl I).prodCongr h.symm).isHomeomorph
  map_zero_left' y := by
    change h (Φ.toContinuousMap (0, h.symm y)) = y
    rw [Φ.map_zero_left, h.apply_symm_apply]

@[simp]
theorem conj_apply (h : Y ≃ₜ Y) (p : I × Y) :
    (Φ.conj h).toContinuousMap p = h (Φ.toContinuousMap (p.1, h.symm p.2)) := rfl

@[simp]
theorem conj_final (h : Y ≃ₜ Y) (y : Y) : (Φ.conj h).final y = h (Φ.final (h.symm y)) := rfl

/-- The final homeomorphism of a conjugated ambient isotopy is the conjugate of the final
homeomorphism: `(Φ.conj h).finalHomeomorph = h * Φ.finalHomeomorph * h⁻¹`. -/
theorem conj_finalHomeomorph (h : Y ≃ₜ Y) :
    (Φ.conj h).finalHomeomorph = h * Φ.finalHomeomorph * h⁻¹ := by
  ext y
  simp only [finalHomeomorph_apply, conj_final, Homeomorph.mul_apply, Homeomorph.inv_apply]

end AmbientIsotopy

end TauCeti
