/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Topology.Order.Interval

/-!
# Rotational invariant curves of annulus maps

For a self-map `f` of an annulus `AddCircle ℓ × Y`, where `Y` is a topological space (in the
applications an interval of `ℝ`), a *rotational invariant curve* is a set `C` with `f '' C = C`
that is a Jordan curve (`TauCeti.IsJordanCurve`) with a parametrization
`TauCeti.jordanParam e : Circle → AddCircle ℓ × Y` which is not null-homotopic
(`TauCeti.IsRotationalInvariantCurve`). Non-null-homotopy excludes the invariant curves bounding
a disc in the annulus, such as a small circle around a fixed point. For a genuine
annulus, with `ℓ ≠ 0` and `Y` a nonempty interval of `ℝ`, the second factor is contractible, so a
loop that is not null-homotopic winds around the circle factor; for an arbitrary `Y` the
nontrivial homotopy class may come from `Y` instead. This is the notion of Birkhoff's theorem on
invariant curves of twist maps, and of the rotational caustics of convex billiards
(Bialy–Mironov).

The definition asks only `f '' C = C` of an arbitrary self-map `f`. We record:

* the parametrization `TauCeti.jordanParam e` is not null-homotopic for *every* homeomorphism
  `e : C ≃ₜ Circle` (`TauCeti.IsRotationalInvariantCurve.not_nullhomotopic`), and, when `Y` is
  Hausdorff, the predicate holds exactly when `C` is the range of an injective continuous map
  `c : C(Circle, AddCircle ℓ × Y)` that is not null-homotopic
  (`TauCeti.IsRotationalInvariantCurve.of_injective`, `TauCeti.isRotationalInvariantCurve_iff`);
* conjugating `f` by a homeomorphism `e` of the annulus carries rotational invariant curves of `f`
  to rotational invariant curves of `e ∘ f ∘ e⁻¹`
  (`TauCeti.IsRotationalInvariantCurve.image_homeomorph`, with the iff form
  `TauCeti.isRotationalInvariantCurve_image_homeomorph_iff`); for instance a fibre reflection
  `I`, an involution, carries rotational invariant curves of `f` to those of `I ∘ f ∘ I`;
* a rotational invariant curve is a Jordan curve
  (`TauCeti.IsRotationalInvariantCurve.isJordanCurve`), hence nonempty and compact, so if it lies
  in an open band `a < φ y < b`, for `φ : Y → ℝ` with `φ ∘ Prod.snd` continuous on the curve, it
  lies in a closed band `a' ≤ φ y ≤ b'` with `a < a' ≤ b' < b`
  (`TauCeti.IsRotationalInvariantCurve.exists_subset_Icc`, from `IsCompact.exists_Icc_between`).

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric
  billiard tables*, Ann. of Math. 196 (2022), Theorem 1.1.
-/

public section

open Set

namespace TauCeti

variable {ℓ : ℝ} {Y : Type*} [TopologicalSpace Y]

/-- A rotational invariant curve of a self-map `f` of the annulus `AddCircle ℓ × Y`: a set `C`
with `f '' C = C` that is a Jordan curve with a parametrization by the circle which is not
null-homotopic (Bialy–Mironov, Theorem 1.1). -/
structure IsRotationalInvariantCurve (f : AddCircle ℓ × Y → AddCircle ℓ × Y)
    (C : Set (AddCircle ℓ × Y)) : Prop where
  /-- The curve is invariant: `f '' C = C`. -/
  image_eq : f '' C = C
  /-- The curve is a Jordan curve whose parametrization `TauCeti.jordanParam e` by the circle is
  not null-homotopic. -/
  exists_not_nullhomotopic : ∃ e : C ≃ₜ Circle,
    ¬ (⟨jordanParam e, continuous_jordanParam e⟩ : C(Circle, AddCircle ℓ × Y)).Nullhomotopic

variable {f : AddCircle ℓ × Y → AddCircle ℓ × Y} {C : Set (AddCircle ℓ × Y)}

namespace IsRotationalInvariantCurve

/-- A rotational invariant curve is a Jordan curve. -/
theorem isJordanCurve (hC : IsRotationalInvariantCurve f C) : IsJordanCurve C :=
  let ⟨e, _⟩ := hC.exists_not_nullhomotopic
  isJordanCurve_iff.2 ⟨e⟩

/-- The parametrization `TauCeti.jordanParam e` of a rotational invariant curve is not
null-homotopic for every homeomorphism `e : C ≃ₜ Circle`, not only for the one supplied by the
definition: two parametrizations differ by a homeomorphism of the circle. -/
theorem not_nullhomotopic (hC : IsRotationalInvariantCurve f C) (e : C ≃ₜ Circle) :
    ¬ (⟨jordanParam e, continuous_jordanParam e⟩ : C(Circle, AddCircle ℓ × Y)).Nullhomotopic := by
  obtain ⟨g, hg⟩ := hC.exists_not_nullhomotopic
  intro h
  refine hg ?_
  convert h.comp_left (g.symm.trans e : C(Circle, Circle)) using 1
  ext1 u
  simp

/-- An invariant set `C` that is the range of an injective continuous map
`c : C(Circle, AddCircle ℓ × Y)` which is not null-homotopic is a rotational invariant curve. The
fibre `Y` is Hausdorff, so that `c` is a homeomorphism onto `C`. -/
theorem of_injective [T2Space Y] (hf : f '' C = C) (c : C(Circle, AddCircle ℓ × Y))
    (hc : Function.Injective c) (hcr : range c = C) (hnc : ¬ c.Nullhomotopic) :
    IsRotationalInvariantCurve f C := by
  subst hcr
  let e : range c ≃ₜ Circle := (c.continuous.isClosedEmbedding hc).isEmbedding.toHomeomorph.symm
  refine ⟨hf, e, ?_⟩
  convert hnc using 2
  ext1 u
  simp [e]

/-- Conjugating by a homeomorphism `e` of the annulus carries a rotational invariant curve `C` of
`f` to the rotational invariant curve `e '' C` of `e ∘ f ∘ e⁻¹`. -/
theorem image_homeomorph (hC : IsRotationalInvariantCurve f C)
    (e : AddCircle ℓ × Y ≃ₜ AddCircle ℓ × Y) :
    IsRotationalInvariantCurve (e ∘ f ∘ e.symm) (e '' C) := by
  obtain ⟨g, hg⟩ := hC.exists_not_nullhomotopic
  refine ⟨?_, (e.image C).symm.trans g, fun h => hg ?_⟩
  · have he : e.symm '' (e '' C) = C := by simp [image_image]
    rw [image_comp, image_comp, he, hC.image_eq]
  · have hcomp : (⟨jordanParam ((e.image C).symm.trans g), continuous_jordanParam _⟩ :
        C(Circle, AddCircle ℓ × Y)) =
        (e : C(AddCircle ℓ × Y, AddCircle ℓ × Y)).comp
          ⟨jordanParam g, continuous_jordanParam g⟩ := by
      ext1 u
      simp
    rw [hcomp] at h
    simpa [← ContinuousMap.comp_assoc] using
      h.comp_right (e.symm : C(AddCircle ℓ × Y, AddCircle ℓ × Y))

/-- A rotational invariant curve is nonempty. -/
theorem nonempty (hC : IsRotationalInvariantCurve f C) : C.Nonempty :=
  hC.isJordanCurve.nonempty

/-- A rotational invariant curve is compact. -/
theorem isCompact (hC : IsRotationalInvariantCurve f C) : IsCompact C :=
  hC.isJordanCurve.isCompact

/-- A rotational invariant curve in an open band `a < φ y < b`, for a function `φ : Y → ℝ` such
that `φ ∘ Prod.snd` is continuous on the curve, lies in a closed band `a' ≤ φ y ≤ b'` with
`a < a' ≤ b' < b`. -/
theorem exists_subset_Icc (hC : IsRotationalInvariantCurve f C) {φ : Y → ℝ}
    (hφ : ContinuousOn (fun x : AddCircle ℓ × Y => φ x.2) C) {a b : ℝ}
    (hCab : ∀ x ∈ C, φ x.2 ∈ Ioo a b) :
    ∃ a' b', a < a' ∧ a' ≤ b' ∧ b' < b ∧ ∀ x ∈ C, φ x.2 ∈ Icc a' b' := by
  obtain ⟨c, d, hK, hcd⟩ := (hC.isCompact.image_of_continuousOn hφ).exists_Icc_between
    (hC.nonempty.image _) (image_subset_iff.2 hCab)
  obtain ⟨x, hx⟩ := hC.nonempty
  have hlt : c < d := (hK ⟨x, hx, rfl⟩).1.trans (hK ⟨x, hx, rfl⟩).2
  exact ⟨c, d, (hcd ⟨le_rfl, hlt.le⟩).1, hlt.le, (hcd ⟨hlt.le, le_rfl⟩).2,
    fun y hy => Ioo_subset_Icc_self (hK ⟨y, hy, rfl⟩)⟩

end IsRotationalInvariantCurve

/-- For a Hausdorff fibre `Y`, a rotational invariant curve of `f` is an invariant set that is the
range of an injective continuous map `c : C(Circle, AddCircle ℓ × Y)` which is not
null-homotopic. -/
theorem isRotationalInvariantCurve_iff [T2Space Y] :
    IsRotationalInvariantCurve f C ↔ f '' C = C ∧ ∃ c : C(Circle, AddCircle ℓ × Y),
      Function.Injective c ∧ range c = C ∧ ¬ c.Nullhomotopic := by
  refine ⟨fun hC => ?_, fun ⟨hf, c, hc, hcr, hnc⟩ => .of_injective hf c hc hcr hnc⟩
  obtain ⟨e, he⟩ := hC.exists_not_nullhomotopic
  exact ⟨hC.image_eq, _, jordanParam_injective e, range_jordanParam e, he⟩

/-- For a homeomorphism `e` of the annulus, `e '' C` is a rotational invariant curve of
`e ∘ f ∘ e⁻¹` if and only if `C` is a rotational invariant curve of `f`. -/
@[simp]
theorem isRotationalInvariantCurve_image_homeomorph_iff (e : AddCircle ℓ × Y ≃ₜ AddCircle ℓ × Y) :
    IsRotationalInvariantCurve (e ∘ f ∘ e.symm) (e '' C) ↔ IsRotationalInvariantCurve f C := by
  refine ⟨fun h => ?_, fun h => h.image_homeomorph e⟩
  simpa [Function.comp_def, image_image] using h.image_homeomorph e.symm

end TauCeti
