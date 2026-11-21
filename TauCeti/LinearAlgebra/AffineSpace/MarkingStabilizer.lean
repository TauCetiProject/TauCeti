/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Perm
public import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.GroupTheory.Coset.Card
import TauCeti.LinearAlgebra.AffineSpace.AffineMap

/-!
# Automorphisms of the sphere preserving an unordered marking

A component of a genus-zero curve with fewer than three special points is not a stable pointed
curve: the Möbius transformations fixing its special points form a positive-dimensional group. In
the virtual constructions of moduli spaces of pseudoholomorphic curves (Pardon) such a component is
stabilized by adding the full preimage `u⁻¹(D)` of a target cut `D` to the domain as an
*unordered* set of further marked points (see `TauCeti.Analysis.Complex.TargetCut` for the
finiteness of this preimage). This file proves the group-theoretic facts that make this
stabilization work, for a sphere with a special point at `∞`.

Write the sphere as `K ∪ {∞}` for a field `K` (for curves, `K = ℂ`). The Möbius transformations
fixing `∞` are the affine automorphisms `z ↦ a z + b` of `K`, the group `K ≃ᵃ[K] K`. A component
with special points `∞` and `P ⊆ K`, for instance `P = ∅` or `P = {0}`, is a map `u : K → X`.

* **Stability of the stabilized domain.** The automorphisms of the sphere fixing `∞` and every
  point of `P`, and mapping a finite set `C` onto itself, form the subgroup
  `TauCeti.markingStabilizer P C` of `AffineEquiv.fixingSubgroup K P`
  (`TauCeti.markingStabilizer_le_fixingSubgroup`). Each of them permutes `C`
  (`TauCeti.markingPerm`), and when `P ∪ C` contains two distinct points this permutation
  determines it (`TauCeti.markingPerm_injective`), because an affine automorphism fixing two
  distinct points is the identity (`AffineMap.ext_of_ne`). So the sphere with the
  special point `∞`, the marked points `P` and the unordered marking `C` has finitely many
  automorphisms, whose number divides `|C|!`
  (`TauCeti.card_markingStabilizer_dvd_factorial`). With an ordering of `C` it has none but the
  identity.
* **Forgetting the cut points does not change the isotropy.** The isotropy of `u`,
  `TauCeti.markedIsotropy u P`, consists of the affine automorphisms `f` fixing every point of
  `P` with `u ∘ f = u`. Every such `f` maps the full preimage `u⁻¹(D)` of any set `D` onto itself
  (`TauCeti.image_preimage_eq_of_mem_markedIsotropy`), so the isotropy is contained in the
  stabilizer of the unordered marking `u⁻¹(D)` (`TauCeti.markedIsotropy_le_markingStabilizer`): the
  isotropy of the stabilized map, with its unordered cut marking, is the isotropy of `u`. In
  particular the isotropy of `u` is finite of order dividing `|u⁻¹(D)|!` as soon as `u⁻¹(D)` is
  finite and `P ∪ u⁻¹(D)` contains two distinct points
  (`TauCeti.card_markedIsotropy_dvd_factorial`). This is why the preimage must be taken in full and
  unordered: a chosen subset or an ordering would not be preserved by the isotropy.

Nothing here uses that `u` is pseudoholomorphic: for a nonconstant pseudoholomorphic sphere the
finiteness of the isotropy also follows from `MDifferentiable.finite_setOf_comp_eq_iff_exists_ne`,
but the stabilization by a cut bounds its order and identifies it with the automorphism group of
a stable pointed domain.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on stabilization by the full
  preimage of a codimension-two submanifold transverse to the map.
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, on stabilizing domains by the intersection
  points with a hypersurface.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 5.1,
  on stable maps and their automorphisms.
-/

public section

open Set
open scoped Nat

namespace TauCeti

/-! ### Automorphisms of the sphere preserving a marking -/

section Marking

variable {K : Type*} [Field K] {P C : Set K} {f : K ≃ᵃ[K] K}

/-- The automorphisms of the sphere `K ∪ {∞}` fixing `∞`, fixing each point of `P` and mapping
the unordered marking `C` onto itself: the affine automorphisms `f` of `K` with `f p = p` for
`p ∈ P` and `f '' C = C`. -/
def markingStabilizer (P C : Set K) : Subgroup (K ≃ᵃ[K] K) where
  carrier := {f | (∀ p ∈ P, f p = p) ∧ f '' C = C}
  mul_mem' {f g} hf hg := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 <|
    mul_mem (AffineEquiv.mem_fixingSubgroup_iff.2 hf.1)
      (AffineEquiv.mem_fixingSubgroup_iff.2 hg.1), by
    rw [AffineEquiv.coe_mul, Set.image_comp, hg.2, hf.2]⟩
  one_mem' := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 (one_mem _), by simp⟩
  inv_mem' {f} hf := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 <|
    inv_mem (AffineEquiv.mem_fixingSubgroup_iff.2 hf.1),
    by
      calc (f⁻¹ : K ≃ᵃ[K] K) '' C = f.symm '' (f '' C) := by rw [hf.2, AffineEquiv.inv_def]
        _ = C := by simp [Set.image_image]⟩

@[simp]
theorem mem_markingStabilizer_iff :
    f ∈ markingStabilizer P C ↔ (∀ p ∈ P, f p = p) ∧ f '' C = C :=
  Iff.rfl

/-- The stabilizer of a marking fixes each point of `P`. -/
theorem markingStabilizer_le_fixingSubgroup :
    markingStabilizer P C ≤ AffineEquiv.fixingSubgroup K P :=
  fun _ hf ↦ AffineEquiv.mem_fixingSubgroup_iff.2 hf.1

/-- An element of the stabilizer of a marking maps marked points, and only those, to marked
points. -/
theorem apply_mem_iff_of_mem_markingStabilizer (hf : f ∈ markingStabilizer P C) {a : K} :
    f a ∈ C ↔ a ∈ C := by
  conv_lhs => rw [← hf.2]
  exact f.injective.mem_set_image

/-- The permutation of the marking `C` induced by an automorphism preserving it. -/
def markingPerm (P C : Set K) : markingStabilizer P C →* Equiv.Perm C where
  toFun f := f.1.toEquiv.subtypeEquiv fun _ ↦ (apply_mem_iff_of_mem_markingStabilizer f.2).symm
  map_one' := by ext; simp
  map_mul' f g := by ext; simp

@[simp]
theorem coe_markingPerm_apply (f : markingStabilizer P C) (c : C) :
    (markingPerm P C f c : K) = f.1 c :=
  (rfl)

/-- An automorphism of the sphere fixing `∞` and each point of `P`, and preserving the marking
`C`, is determined by the permutation of `C` it induces, provided `P ∪ C` contains two distinct
points. -/
theorem markingPerm_injective (h : (P ∪ C).Nontrivial) :
    Function.Injective (markingPerm P C) := by
  refine (injective_iff_map_eq_one _).2 fun f hf ↦ ?_
  have hfix : ∀ a ∈ P ∪ C, f.1 a = a := by
    rintro a (ha | ha)
    · exact f.2.1 a ha
    · simpa using congrArg Subtype.val (DFunLike.congr_fun hf ⟨a, ha⟩)
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  exact Subtype.ext (AffineEquiv.toAffineMap_injective
    (AffineMap.ext_of_ne hpq (hfix p hp) (hfix q hq)))

/-- **Stability of the stabilized domain.** If the marking `C` is finite and `P ∪ C` contains two
distinct points, the sphere with the special point `∞`, the marked points `P` and the unordered
marking `C` has finitely many automorphisms, and their number divides `|C|!`. -/
theorem card_markingStabilizer_dvd_factorial (hC : C.Finite)
    (h : (P ∪ C).Nontrivial) :
    Nat.card (markingStabilizer P C) ∣ (Nat.card C)! := by
  have := hC.to_subtype
  rw [← Nat.card_perm]
  exact Subgroup.card_dvd_of_injective _ (markingPerm_injective h)

/-- If the marking `C` is finite and `P ∪ C` contains two distinct points, the sphere with the
special point `∞`, the marked points `P` and the unordered marking `C` has finitely many
automorphisms. -/
theorem finite_markingStabilizer (hC : C.Finite) (h : (P ∪ C).Nontrivial) :
    Finite (markingStabilizer P C) :=
  Nat.finite_of_card_ne_zero <| ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _)
    (card_markingStabilizer_dvd_factorial hC h)

end Marking

/-! ### The isotropy of a map and its full preimage markings -/

section Isotropy

variable {K : Type*} [Field K] {X : Type*} {u : K → X} {P : Set K} {f : K ≃ᵃ[K] K}

/-- The isotropy group of a map `u` of the sphere `K ∪ {∞}` with the special point `∞` and the
marked points `P`: the affine automorphisms `f` of `K` fixing each point of `P` with
`u ∘ f = u`. -/
def markedIsotropy (u : K → X) (P : Set K) : Subgroup (K ≃ᵃ[K] K) where
  carrier := {f | (∀ p ∈ P, f p = p) ∧ u ∘ f = u}
  mul_mem' {f g} hf hg := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 <|
    mul_mem (AffineEquiv.mem_fixingSubgroup_iff.2 hf.1)
      (AffineEquiv.mem_fixingSubgroup_iff.2 hg.1), by
    rw [AffineEquiv.coe_mul, ← Function.comp_assoc, hf.2, hg.2]⟩
  one_mem' := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 (one_mem _), rfl⟩
  inv_mem' {f} hf := ⟨AffineEquiv.mem_fixingSubgroup_iff.1 <|
    inv_mem (AffineEquiv.mem_fixingSubgroup_iff.2 hf.1),
    by
      funext z
      simpa [AffineEquiv.inv_def] using congrFun hf.2 (f.symm z) |>.symm⟩

@[simp]
theorem mem_markedIsotropy_iff : f ∈ markedIsotropy u P ↔ (∀ p ∈ P, f p = p) ∧ u ∘ f = u :=
  Iff.rfl

/-- The isotropy of `u` with the marked points `P` fixes each point of `P`. -/
theorem markedIsotropy_le_fixingSubgroup : markedIsotropy u P ≤ AffineEquiv.fixingSubgroup K P :=
  fun _ hf ↦ AffineEquiv.mem_fixingSubgroup_iff.2 hf.1

/-- Without marked points besides `∞`, the isotropy is the set of affine automorphisms `f` with
`u ∘ f = u`. -/
@[simp]
theorem coe_markedIsotropy_empty :
    (markedIsotropy u ∅ : Set (K ≃ᵃ[K] K)) = {f : K ≃ᵃ[K] K | u ∘ f = u} := by
  ext f
  simp

/-- An element of the isotropy of `u` maps the full preimage `u⁻¹(D)` of any set onto itself. -/
theorem image_preimage_eq_of_mem_markedIsotropy (hf : f ∈ markedIsotropy u P) (D : Set X) :
    f '' (u ⁻¹' D) = u ⁻¹' D := by
  have h : f ⁻¹' (u ⁻¹' D) = u ⁻¹' D := by rw [← Set.preimage_comp, hf.2]
  conv_lhs => rw [← h]
  exact Set.image_preimage_eq _ f.surjective

/-- **Forgetting the cut points.** The isotropy of `u` preserves the unordered marking by the full
preimage of any set `D`, so the isotropy of the map with this marking is the isotropy of `u`. -/
theorem markedIsotropy_le_markingStabilizer (D : Set X) :
    markedIsotropy u P ≤ markingStabilizer P (u ⁻¹' D) :=
  fun _ hf ↦ ⟨hf.1, image_preimage_eq_of_mem_markedIsotropy hf D⟩

/-- **Stabilization bounds the isotropy.** If the full preimage `u⁻¹(D)` is finite and
`P ∪ u⁻¹(D)` contains two distinct points, the isotropy of `u` is finite of order dividing
`|u⁻¹(D)|!`. -/
theorem card_markedIsotropy_dvd_factorial {D : Set X} (hD : (u ⁻¹' D).Finite)
    (h : (P ∪ u ⁻¹' D).Nontrivial) :
    Nat.card (markedIsotropy u P) ∣ (Nat.card (u ⁻¹' D))! :=
  (Subgroup.card_dvd_of_le (markedIsotropy_le_markingStabilizer D)).trans
    (card_markingStabilizer_dvd_factorial hD h)

/-- If the full preimage `u⁻¹(D)` is finite and `P ∪ u⁻¹(D)` contains two distinct points, the
isotropy of `u` is finite. -/
theorem finite_markedIsotropy {D : Set X} (hD : (u ⁻¹' D).Finite)
    (h : (P ∪ u ⁻¹' D).Nontrivial) :
    Finite (markedIsotropy u P) :=
  Nat.finite_of_card_ne_zero <| ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _)
    (card_markedIsotropy_dvd_factorial hD h)

end Isotropy

end TauCeti
