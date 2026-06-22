/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import TauCeti.Topology.Homotopy.AmbientIsotopic

/-!
# The subgroup of homeomorphisms isotopic to the identity

Mathlib makes the self-homeomorphisms `Y ≃ₜ Y` of a space into a group
(`Homeomorph.instGroup`, with `f * g = g.trans f`). An ambient isotopy `Φ : AmbientIsotopy Y`
produces, at time `1`, such a self-homeomorphism `Φ.finalHomeomorph`; the functoriality lemmas
`AmbientIsotopy.finalHomeomorph_refl` / `finalHomeomorph_trans` / `finalHomeomorph_symm` (in
`TauCeti.Topology.Homotopy.Isotopy`) say this endpoint map carries the constant, composite, and
inverse ambient isotopies to the unit, product, and inverse homeomorphisms. So the
homeomorphisms of the form `Φ.finalHomeomorph` are closed under the group operations: this file
packages them as a subgroup `TauCeti.isotopicToId Y` of `Y ≃ₜ Y`, the **homeomorphisms isotopic
to the identity**.

This is the point-set precursor of the identity component of the homeomorphism group, and the
denominator of the mapping class group `MCG(Y) = (Y ≃ₜ Y) / isotopicToId Y`: the main result
here, `isotopicToId Y` is a *normal* subgroup, is exactly what makes that quotient a group. The
geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 3) asks the
general isotopy notion to be built once and specialised; the normal subgroup of isotopically
trivial homeomorphisms is the group-theoretic shadow of that construction, the continuous
topological analogue of the `Diff₀(M) ◁ Diff(M)` whose homotopy type the Smale conjecture is
about.

Normality is powered by a new closure operation, `AmbientIsotopy.conj`, conjugating an ambient
isotopy by a homeomorphism `h`: running `Φ` in the coordinates moved by `h`. Its final
homeomorphism is the conjugate `h * Φ.finalHomeomorph * h⁻¹`, which is what realises the
conjugate of an isotopically trivial homeomorphism as again isotopically trivial.

## Main definitions

* `TauCeti.AmbientIsotopy.conj`: the ambient isotopy `Φ` conjugated by a homeomorphism `h`, with
  total map `(t, y) ↦ (t, h (Φ (t, h⁻¹ y)))`.
* `TauCeti.isotopicToId Y`: the subgroup of `Y ≃ₜ Y` of homeomorphisms arising as the final
  homeomorphism of some ambient isotopy of `Y`.

## Main results

* `TauCeti.AmbientIsotopy.conj_finalHomeomorph`: the final homeomorphism of `Φ.conj h` is the
  conjugate `h * Φ.finalHomeomorph * h⁻¹`.
* `TauCeti.mem_isotopicToId` / `TauCeti.finalHomeomorph_mem_isotopicToId`: membership of the
  subgroup is exactly "being some ambient isotopy's final homeomorphism".
* `TauCeti.mem_isotopicToId_iff_ambientIsotopic`: a homeomorphism lies in `isotopicToId Y`
  exactly when it is ambient isotopic, as a map, to the identity.
* `TauCeti.isotopicToId_normal`: `isotopicToId Y` is a normal subgroup of `Y ≃ₜ Y`.
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

variable (Y) in
/-- The **homeomorphisms isotopic to the identity**: the subgroup of `Y ≃ₜ Y` consisting of the
homeomorphisms that arise as the final homeomorphism `Φ.finalHomeomorph` of some ambient isotopy
`Φ` of `Y`. Closure under the group operations is the functoriality of `finalHomeomorph` under the
constant (`AmbientIsotopy.refl`), composite (`AmbientIsotopy.trans`), and inverse
(`AmbientIsotopy.symm`) ambient isotopies. -/
def isotopicToId : Subgroup (Y ≃ₜ Y) where
  carrier := Set.range fun Φ : AmbientIsotopy Y => Φ.finalHomeomorph
  one_mem' := ⟨AmbientIsotopy.refl Y, AmbientIsotopy.finalHomeomorph_refl⟩
  mul_mem' := by
    rintro _ _ ⟨Φ, rfl⟩ ⟨Ψ, rfl⟩
    exact ⟨Ψ.trans Φ, AmbientIsotopy.finalHomeomorph_trans Ψ Φ⟩
  inv_mem' := by
    rintro _ ⟨Φ, rfl⟩
    exact ⟨Φ.symm, AmbientIsotopy.finalHomeomorph_symm Φ⟩

/-- Membership of `isotopicToId Y` is being the final homeomorphism of some ambient isotopy. -/
theorem mem_isotopicToId {e : Y ≃ₜ Y} :
    e ∈ isotopicToId Y ↔ ∃ Φ : AmbientIsotopy Y, Φ.finalHomeomorph = e := Iff.rfl

/-- Every final homeomorphism of an ambient isotopy is isotopic to the identity. -/
theorem finalHomeomorph_mem_isotopicToId (Φ : AmbientIsotopy Y) :
    Φ.finalHomeomorph ∈ isotopicToId Y := ⟨Φ, rfl⟩

/-- A self-homeomorphism is isotopic to the identity exactly when it is ambient isotopic, as a
continuous map, to the identity map of `Y`. This identifies the subgroup with one coset of the
ambient-isotopy relation on `C(Y, Y)`. -/
theorem mem_isotopicToId_iff_ambientIsotopic {e : Y ≃ₜ Y} :
    e ∈ isotopicToId Y ↔ AmbientIsotopic (ContinuousMap.id Y) (e : C(Y, Y)) := by
  rw [mem_isotopicToId]
  refine ⟨fun ⟨Φ, hΦ⟩ => ⟨Φ, ?_⟩, fun ⟨Φ, hΦ⟩ => ⟨Φ, ?_⟩⟩
  · ext y
    have := DFunLike.congr_fun hΦ y
    simpa using this
  · ext y
    have := DFunLike.congr_fun hΦ y
    simpa using this

/-- The homeomorphisms isotopic to the identity form a **normal** subgroup of `Y ≃ₜ Y`: a
conjugate `g * e * g⁻¹` of an isotopically trivial `e = Φ.finalHomeomorph` is again isotopically
trivial, realised by the conjugated ambient isotopy `Φ.conj g`. This is what makes the mapping
class group `(Y ≃ₜ Y) / isotopicToId Y` a group. -/
instance isotopicToId_normal : (isotopicToId Y).Normal where
  conj_mem := by
    rintro _ ⟨Φ, rfl⟩ g
    exact ⟨Φ.conj g, AmbientIsotopy.conj_finalHomeomorph Φ g⟩

end TauCeti
