/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import TauCeti.GroupTheory.Divisible.Extension

/-!
# Continuous extension from an open subgroup

A character on an open subgroup `H` extends to a character of the entire group killing a
prescribed subgroup `N` exactly when it kills `H ∩ N`. For a divisible abelian target, the
extension is obtained in the abstract quotient by `N`; continuity follows from the restriction
to the open subgroup. Neither closedness of `N` nor finite index is needed.

This is the extension step for prescribed local and archimedean data in the construction of
Hecke characters; see A. Raghuram, *Notes on the Arithmetic of Hecke L-Functions*, §4, and
`New.AutChar.exists_hasWeight_of_prod_eq_one` in `Lib/ClassField/HeckeCharacter/Basic` of
lsernau/grh-lean (`72fead1`) for the norm-one torus application.
-/

public section

namespace MonoidHom

/-- A group homomorphism is continuous if its restriction to an open subgroup is continuous. -/
theorem continuous_iff_continuous_domRestrict_of_isOpen {G A : Type*}
    [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [MulOneClass A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (ψ : G →* A) {H : Subgroup G} (hH : IsOpen (H : Set G)) :
    Continuous ψ ↔ Continuous (ψ.domRestrict H) := by
  refine ⟨fun h ↦ h.comp continuous_subtypeVal, fun h ↦ ?_⟩
  have h₁ : ContinuousAt ψ 1 :=
    ((continuousWithinAt_iff_continuousAt_domRestrict ψ H.one_mem).mpr
      (h.continuousAt (x := 1))).continuousAt (hH.mem_nhds H.one_mem)
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  have htranslate : ContinuousAt (fun y ↦ x⁻¹ * y) x :=
    (continuous_const_mul _).continuousAt
  have h₁' : ContinuousAt ψ (x⁻¹ * x) := by simpa using h₁
  have hpull := h₁'.comp htranslate
  simpa [Function.comp_def, ← map_mul, mul_assoc] using
    (continuous_const_mul (ψ x)).continuousAt.comp hpull

variable {G A : Type*} [CommGroup G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [CommGroup A] [TopologicalSpace A] [SeparatelyContinuousMul A] {H N : Subgroup G}

/-- A character on an open subgroup extends continuously and trivially on `N` exactly when it
is continuous and kills `H ∩ N`, provided the target group is divisible. -/
theorem exists_continuous_domRestrict_eq_iff_of_isOpen [RootableBy A ℕ] (χ : H →* A)
    (hH : IsOpen (H : Set G)) :
    (∃ ψ : G →* A, Continuous ψ ∧ ψ.domRestrict H = χ ∧ N ≤ ψ.ker) ↔
      Continuous χ ∧ N.subgroupOf H ≤ χ.ker := by
  refine ⟨?_, fun ⟨hc, hχ⟩ ↦ ?_⟩
  · rintro ⟨ψ, hc, rfl, hN⟩
    exact ⟨(ψ.continuous_iff_continuous_domRestrict_of_isOpen hH).mp hc,
      fun x hx ↦ hN (Subgroup.mem_subgroupOf.mp hx)⟩
  let f := (QuotientGroup.mk' N).comp H.subtype
  have hf : f.ker = N.subgroupOf H := by
    rw [← comap_ker, QuotientGroup.ker_mk']
    rfl
  obtain ⟨φ, hφ⟩ := (f.exists_comp_eq_iff_ker_le_ker_of_rootableBy χ).mpr (hf ▸ hχ)
  let ψ := φ.comp (QuotientGroup.mk' N)
  have hψ : ψ.domRestrict H = χ := hφ
  refine ⟨ψ, (ψ.continuous_iff_continuous_domRestrict_of_isOpen hH).mpr (hψ ▸ hc), hψ, ?_⟩
  intro x hx
  simp [ψ, (QuotientGroup.eq_one_iff x).mpr hx]

end MonoidHom
