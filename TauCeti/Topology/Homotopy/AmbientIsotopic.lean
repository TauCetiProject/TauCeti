/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Topology.Homotopy.Isotopy

/-!
# The ambient-isotopy equivalence relation

Building on `TauCeti.AmbientIsotopy` (an ambient isotopy of a space `Y`: a homotopy from the
identity whose level-preserving total map `I × Y → I × Y` is a homeomorphism), this file makes
ambient isotopy a relation between maps and shows it is an equivalence relation. Two maps
`f g : C(X, Y)` are **ambient isotopic** when some ambient isotopy `Φ` of `Y` carries `f` to `g`,
meaning its final homeomorphism postcomposes `f` to `g`. This is the relation the geometric-topology
roadmap (`TauCetiRoadmap/GeometricTopology`, encoding conventions) intends to specialise to smooth
embeddings `S¹ ↪ M` to obtain knot equivalence: "isotopy is defined generally, then specialised".

The reflexivity, symmetry, and transitivity of the relation are powered by three closure operations
on ambient isotopies themselves, each of which keeps the total map a homeomorphism for free:

* `AmbientIsotopy.refl` (already available): the constant ambient isotopy, total map the identity.
* `AmbientIsotopy.trans Φ Ψ`: the pointwise composition `t ↦ Ψ_t ∘ Φ_t`, total map
  `Ψ.totalMap ∘ Φ.totalMap`.
* `AmbientIsotopy.symm Φ`: the pointwise inverse `t ↦ Φ_t⁻¹`, total map `Φ.totalMap⁻¹`.

Because each total map is a composition or inverse of homeomorphisms, none of the closure
operations needs the closed-cover gluing that `Isotopy.trans` requires; the definitions follow
Burde--Zieschang, *Knots*, Chapter 1, where ambient isotopy of `Sⁿ` is exactly this relation.

## Main definitions

* `TauCeti.AmbientIsotopy.trans` / `TauCeti.AmbientIsotopy.symm`: composition and inverse of
  ambient isotopies.
* `TauCeti.AmbientIsotopic f g`: the proposition that some ambient isotopy of `Y` carries `f` to
  `g`.
* `TauCeti.ambientIsotopicSetoid`: the equivalence relation packaged as a `Setoid`.

## Main results

* `TauCeti.AmbientIsotopy.final_trans` / `final_symm_final`: the final maps of the composite and
  inverse ambient isotopies.
* `TauCeti.AmbientIsotopic.refl` / `symm` / `trans` and `ambientIsotopic_equivalence`: ambient
  isotopy is an equivalence relation on `C(X, Y)`.
* `TauCeti.AmbientIsotopic.isotopic`: ambient isotopic embeddings are isotopic, specialising the
  ambient relation to the general isotopy relation of `Isotopy.lean`.
-/

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace AmbientIsotopy

variable (Φ Ψ : AmbientIsotopy Y)

/-- The level-preserving total map of an ambient isotopy, bundled as a self-homeomorphism of
`I × Y`. -/
noncomputable def totalHomeomorph : (I × Y) ≃ₜ (I × Y) :=
  IsHomeomorph.homeomorph Φ.totalMap Φ.isHomeomorph_total

@[simp]
theorem totalHomeomorph_apply (p : I × Y) :
    Φ.totalHomeomorph p = (p.1, Φ.toContinuousMap p) := rfl

/-- The inverse total homeomorphism preserves the time coordinate. -/
theorem totalHomeomorph_symm_fst (p : I × Y) : (Φ.totalHomeomorph.symm p).1 = p.1 := by
  have h := Φ.totalHomeomorph.apply_symm_apply p
  rw [totalHomeomorph_apply] at h
  exact (Prod.ext_iff.mp h).1

/-- **Composition of ambient isotopies**: follow `Φ_t` then `Ψ_t` at each time `t`. The total map
is `Ψ.totalMap ∘ Φ.totalMap`, hence a homeomorphism, so no gluing is needed. -/
def trans : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => Ψ.toContinuousMap (p.1, Φ.toContinuousMap p), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, Ψ.toContinuousMap (p.1, Φ.toContinuousMap p)))
        = ⇑Ψ.totalMap ∘ ⇑Φ.totalMap := by
      funext p
      simp [Function.comp, totalMap_apply]
    rw [heq]
    exact Ψ.isHomeomorph_total.comp Φ.isHomeomorph_total
  map_zero_left' y := by
    change Ψ.toContinuousMap (0, Φ.toContinuousMap (0, y)) = y
    rw [Φ.map_zero_left, Ψ.map_zero_left]

@[simp]
theorem trans_apply (p : I × Y) :
    (Φ.trans Ψ).toContinuousMap p = Ψ.toContinuousMap (p.1, Φ.toContinuousMap p) := rfl

@[simp]
theorem final_trans (y : Y) : (Φ.trans Ψ).final y = Ψ.final (Φ.final y) := rfl

/-- **Inverse of an ambient isotopy**: undo `Φ_t` at each time `t`. The total map is
`Φ.totalMap⁻¹`, hence a homeomorphism. -/
noncomputable def symm : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => (Φ.totalHomeomorph.symm p).2,
    continuous_snd.comp Φ.totalHomeomorph.symm.continuous⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, (Φ.totalHomeomorph.symm p).2))
        = ⇑Φ.totalHomeomorph.symm := by
      funext p
      exact Prod.ext (Φ.totalHomeomorph_symm_fst p).symm rfl
    rw [heq]
    exact Φ.totalHomeomorph.symm.isHomeomorph
  map_zero_left' y := by
    have h0 : Φ.totalHomeomorph (0, y) = (0, y) := by
      rw [totalHomeomorph_apply, Φ.map_zero_left]
    change (Φ.totalHomeomorph.symm (0, y)).2 = y
    rw [Φ.totalHomeomorph.symm_apply_eq.mpr h0.symm]

@[simp]
theorem symm_apply (p : I × Y) :
    Φ.symm.toContinuousMap p = (Φ.totalHomeomorph.symm p).2 := rfl

/-- The inverse ambient isotopy undoes the original: its final map is a left inverse of the
original final map. -/
theorem final_symm_final (y : Y) : Φ.symm.final (Φ.final y) = y := by
  have h1 : Φ.totalHomeomorph (1, y) = (1, Φ.final y) := by
    rw [totalHomeomorph_apply, final_apply]
  change (Φ.totalHomeomorph.symm (1, Φ.final y)).2 = y
  rw [Φ.totalHomeomorph.symm_apply_eq.mpr h1.symm]

/-- The original ambient isotopy undoes its inverse: the original final map is a left inverse of
the inverse final map. -/
theorem final_final_symm (y : Y) : Φ.final (Φ.symm.final y) = y := by
  have hfst : (Φ.totalHomeomorph.symm (1, y)).1 = 1 := Φ.totalHomeomorph_symm_fst (1, y)
  have happ := Φ.totalHomeomorph.apply_symm_apply (1, y)
  rw [totalHomeomorph_apply] at happ
  have hpair : ((1 : I), (Φ.totalHomeomorph.symm (1, y)).2) = Φ.totalHomeomorph.symm (1, y) :=
    Prod.ext hfst.symm rfl
  change Φ.toContinuousMap (1, (Φ.totalHomeomorph.symm (1, y)).2) = y
  rw [hpair]
  exact (Prod.ext_iff.mp happ).2

end AmbientIsotopy

/-- Two maps `f g : C(X, Y)` are **ambient isotopic** if some ambient isotopy of the codomain `Y`
carries `f` to `g`, that is, its final homeomorphism postcomposes `f` to `g`. Specialised to
smooth embeddings `S¹ ↪ M` this is knot equivalence (ambient isotopy of knots). -/
def AmbientIsotopic (f g : C(X, Y)) : Prop :=
  ∃ Φ : AmbientIsotopy Y, Φ.final.comp f = g

namespace AmbientIsotopic

variable {f g h : C(X, Y)}

/-- An ambient isotopy carrying `f` to `g` witnesses that `f` and `g` are ambient isotopic. -/
theorem of_ambientIsotopy (Φ : AmbientIsotopy Y) {f : C(X, Y)} :
    AmbientIsotopic f (Φ.final.comp f) := ⟨Φ, rfl⟩

/-- Ambient isotopy is reflexive: the constant ambient isotopy fixes every map. -/
@[refl]
theorem refl (f : C(X, Y)) : AmbientIsotopic f f :=
  ⟨AmbientIsotopy.refl Y, by ext x; rfl⟩

/-- Ambient isotopy is symmetric, via the inverse ambient isotopy. -/
@[symm]
theorem symm (hfg : AmbientIsotopic f g) : AmbientIsotopic g f := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact ⟨Φ.symm, by ext x; exact Φ.final_symm_final (f x)⟩

/-- Ambient isotopy is transitive, via the composite ambient isotopy. -/
@[trans]
theorem trans (hfg : AmbientIsotopic f g) (hgh : AmbientIsotopic g h) : AmbientIsotopic f h := by
  obtain ⟨Φ, rfl⟩ := hfg
  obtain ⟨Ψ, rfl⟩ := hgh
  exact ⟨Φ.trans Ψ, by ext x; exact Φ.final_trans Ψ (f x)⟩

/-- Ambient isotopic embeddings are isotopic: this specialises the ambient relation to the general
isotopy relation, the "ambient isotopy implies isotopy" direction at the level of maps. -/
theorem isotopic (hfg : AmbientIsotopic f g) (hf : IsEmbedding f) : Isotopic f g := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact Φ.isotopic hf

end AmbientIsotopic

/-- Ambient isotopy is an equivalence relation on `C(X, Y)`. -/
theorem ambientIsotopic_equivalence :
    Equivalence (AmbientIsotopic (X := X) (Y := Y)) :=
  ⟨AmbientIsotopic.refl, AmbientIsotopic.symm, AmbientIsotopic.trans⟩

/-- The ambient-isotopy equivalence relation on `C(X, Y)`, packaged as a `Setoid`. -/
def ambientIsotopicSetoid (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid (C(X, Y)) where
  r := AmbientIsotopic
  iseqv := ambientIsotopic_equivalence

end TauCeti
