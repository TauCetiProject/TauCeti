/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Conj
public import TauCeti.Analysis.Complex.Fuchsian.LimitSet
public import TauCeti.Analysis.Complex.UpperHalfPlane.ConvexHull
import Mathlib.Topology.LocalAtTarget

/-!
# The Nielsen hull and its coarse quotient

The closed Nielsen hull of a subgroup of `PSL(2, ℝ)` is the ideal convex hull of its limit set.
It is invariant under the subgroup and equivariant under conjugation. If the limit set has
more than two points, the hull has nonempty interior, the open Nielsen region.

The coarse Nielsen core is the image of the hull in the ambient orbit space. Its subspace topology
is the quotient topology from the hull, and its ambient frontier is the image of the frontier of
the hull.

See W. Duke, Ö. Imamoglu and Á. Tóth, *Geometric invariants for real quadratic fields*,
Ann. of Math. 184 (2016), 949–990, §2, for the Nielsen region and the convex core.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane TauCeti.UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ))

/-- The closed Nielsen hull of `Γ` is the hyperbolic convex hull of its limit set. -/
def nielsenHull : Set ℍ :=
  idealConvexHull Γ.limitSet

/-- The Nielsen hull in terms of the ideal convex hull. -/
theorem nielsenHull_def : Γ.nielsenHull = idealConvexHull Γ.limitSet := (rfl)

/-- The Nielsen hull is closed in the upper half-plane. -/
theorem isClosed_nielsenHull : IsClosed Γ.nielsenHull :=
  isClosed_idealConvexHull _

/-- For a nonelementary subgroup, the open Nielsen region is nonempty. -/
theorem interior_nielsenHull_nonempty (hΓ : 3 ≤ Γ.limitSet.encard) :
    (interior Γ.nielsenHull).Nonempty :=
  interior_idealConvexHull_nonempty hΓ

/-- The Nielsen hull fills the upper half-plane exactly when the limit set is the whole circle. -/
theorem nielsenHull_eq_univ_iff : Γ.nielsenHull = univ ↔ Γ.limitSet = univ :=
  idealConvexHull_eq_univ_iff Γ.isClosed_limitSet

/-- A conjugate subgroup has the translated Nielsen hull. -/
theorem nielsenHull_conjAct_smul (g : PSL(2, ℝ)) :
    (ConjAct.toConjAct g • Γ).nielsenHull = g • Γ.nielsenHull := by
  rw [nielsenHull_def, nielsenHull_def, limitSet_conjAct_smul, idealConvexHull_smul]

/-- The normalizer of `Γ` preserves its Nielsen hull. -/
theorem smul_nielsenHull {g : PSL(2, ℝ)} (hg : g ∈ normalizer Γ) :
    g • Γ.nielsenHull = Γ.nielsenHull := by
  rw [← nielsenHull_conjAct_smul, conjAct_pointwise_smul_eq_self hg]

/-- Membership in the Nielsen hull is invariant under `Γ`. -/
@[simp]
theorem smul_mem_nielsenHull_iff (g : Γ) (z : ℍ) :
    g • z ∈ Γ.nielsenHull ↔ z ∈ Γ.nielsenHull := by
  rw [Subgroup.smul_def]
  calc
    _ ↔ (g : PSL(2, ℝ)) • z ∈ (g : PSL(2, ℝ)) • Γ.nielsenHull := by
      rw [Γ.smul_nielsenHull (le_normalizer g.property)]
    _ ↔ _ := Set.smul_mem_smul_set_iff

/-- The coarse Nielsen core, regarded as a subset of the full orbit space. As a type it carries
the inherited subspace topology, which equals the topology of the quotient of the hull. -/
def nielsenCore : Set (orbitRel.Quotient Γ ℍ) :=
  Quotient.mk (orbitRel Γ ℍ) '' Γ.nielsenHull

/-- The Nielsen core is the image of the hull under the orbit projection. -/
theorem nielsenCore_def :
    Γ.nielsenCore = Quotient.mk (orbitRel Γ ℍ) '' Γ.nielsenHull := (rfl)

/-- An orbit lies in the core exactly when its representative lies in the hull. -/
@[simp]
theorem quotientMk_mem_nielsenCore_iff (z : ℍ) :
    Quotient.mk (orbitRel Γ ℍ) z ∈ Γ.nielsenCore ↔ z ∈ Γ.nielsenHull := by
  rw [nielsenCore_def]
  constructor
  · rintro ⟨w, hw, heq⟩
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact heq.symm))
    exact (Γ.smul_mem_nielsenHull_iff g w).2 hw
  · exact mem_image_of_mem _

/-- The inverse image of the core under the orbit projection is the entire Nielsen hull. -/
@[simp]
theorem preimage_quotientMk_nielsenCore :
    Quotient.mk (orbitRel Γ ℍ) ⁻¹' Γ.nielsenCore = Γ.nielsenHull :=
  Set.ext (Γ.quotientMk_mem_nielsenCore_iff)

/-- The coarse Nielsen core is closed in the ambient orbit space. -/
theorem isClosed_nielsenCore : IsClosed Γ.nielsenCore := by
  have h := MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := ℍ)
  rw [← h.isQuotientMap.isCoinducing.isClosed_preimage, preimage_quotientMk_nielsenCore]
  exact Γ.isClosed_nielsenHull

/-- The projection of the Nielsen hull onto the coarse core. -/
def nielsenCoreProjection (z : Γ.nielsenHull) : Γ.nielsenCore :=
  ⟨Quotient.mk (orbitRel Γ ℍ) z.val, (Γ.quotientMk_mem_nielsenCore_iff z.val).2 z.property⟩

/-- The core projection sends a point of the hull to its orbit in the full orbit space. -/
@[simp]
theorem coe_nielsenCoreProjection (z : Γ.nielsenHull) :
    (Γ.nielsenCoreProjection z).val = Quotient.mk (orbitRel Γ ℍ) z.val := (rfl)

/-- The core projection equips the coarse core with the quotient topology of the hull. -/
theorem isOpenQuotientMap_nielsenCoreProjection : IsOpenQuotientMap Γ.nielsenCoreProjection := by
  have h := (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := ℍ)).restrictPreimage
    Γ.nielsenCore
  let e := Homeomorph.setCongr Γ.preimage_quotientMk_nielsenCore.symm
  convert h.comp e.isOpenQuotientMap using 1
  funext z
  apply Subtype.ext
  rw [coe_nielsenCoreProjection]
  rfl

/-- The fibres of the core projection are exactly the `Γ`-orbits in the hull. -/
theorem nielsenCoreProjection_eq_iff {z w : Γ.nielsenHull} :
    Γ.nielsenCoreProjection z = Γ.nielsenCoreProjection w ↔ ∃ g : Γ, g • w.val = z.val := by
  rw [Subtype.ext_iff, coe_nielsenCoreProjection, coe_nielsenCoreProjection, Quotient.eq,
    orbitRel_apply, mem_orbit_iff]

/-- The frontier of the coarse core in the ambient orbit space is the image of the upstairs
frontier. -/
theorem frontier_nielsenCore :
    frontier Γ.nielsenCore = Quotient.mk (orbitRel Γ ℍ) '' frontier Γ.nielsenHull := by
  have h := MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := ℍ)
  have hpre := h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous Γ.nielsenCore
  rw [preimage_quotientMk_nielsenCore] at hpre
  rw [← hpre, Set.image_preimage_eq _ h.surjective]

variable {Γ} {Γ' : Subgroup PSL(2, ℝ)} {g : PSL(2, ℝ)}

/-- The ambient homeomorphism of conjugate quotients sends the source core onto the target core. -/
theorem image_quotientConjHomeomorph_nielsenCore (h : ConjAct.toConjAct g • Γ = Γ') :
    quotientConjHomeomorph h '' Γ.nielsenCore = Γ'.nielsenCore := by
  have hHull := Γ.nielsenHull_conjAct_smul g
  rw [h, ← Set.image_smul] at hHull
  rw [nielsenCore_def, nielsenCore_def, hHull]
  simp only [Set.image_image, quotientConjHomeomorph_mk]

/-- Conjugation induces a homeomorphism between the coarse Nielsen cores. -/
def nielsenCoreConjHomeomorph (h : ConjAct.toConjAct g • Γ = Γ') :
    Γ.nielsenCore ≃ₜ Γ'.nielsenCore :=
  ((quotientConjHomeomorph h).image _).trans
    (Homeomorph.setCongr (image_quotientConjHomeomorph_nielsenCore h))

/-- The core homeomorphism is the restriction of the ambient quotient homeomorphism. -/
@[simp]
theorem coe_nielsenCoreConjHomeomorph (h : ConjAct.toConjAct g • Γ = Γ') (q : Γ.nielsenCore) :
    (nielsenCoreConjHomeomorph h q).val = quotientConjHomeomorph h q.val := by
  simp [nielsenCoreConjHomeomorph]

end Subgroup
