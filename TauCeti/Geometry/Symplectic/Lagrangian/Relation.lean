/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.LinearAlgebra.Submodule.Relation.FiberProduct

/-!
# Composition of linear Lagrangian relations

A linear canonical relation from `(V, ω₁)` to `(W, ω₂)` is a Lagrangian subspace
of `V × W` for `ω₁ ⊖ ω₂`. Composition is ordinary relational composition of
submodules, with the intermediate vector eliminated. In finite dimension it is
again Lagrangian, even when the matching intersection is not transverse and the
projection is not injective. The diagonal and symplectic graphs are the identity
and invertible examples from `TauCeti.Geometry.Symplectic.Lagrangian.Constructions`.

This is the tangent-space calculation for geometric composition of smooth
Lagrangian correspondences. It does not supply smoothness or embeddedness of a
set-theoretic geometric composite.

The proof intersects the product relation with the matching subspace, then
eliminates its characteristic directions. Orthogonal complementation exchanges
intersection and sum, so no transversality or dimension-of-intersection assumption
is needed in this linear calculation.

Transversality instead controls the excess of the composition: the directions `w` with
`(0, w) ∈ L` and `(w, 0) ∈ K`, which the composite map kills. For isotropic relations, if the
projections of `L` and `K` to the middle factor span it, there is no nonzero excess direction
(`TauCeti.SymplecticForm.IsIsotropic.eq_zero_of_map_snd_sup_map_fst_eq_top`). For linear
canonical relations the converse holds too
(`TauCeti.SymplecticForm.IsLagrangian.map_snd_sup_map_fst_eq_top_iff`).

The matching-space quotient and its excess are defined for arbitrary linear relations in
`TauCeti.LinearAlgebra.Submodule.Relation.FiberProduct`. For Lagrangian relations the excess is
the symplectic orthogonal of the sum of the middle projections, in any dimension
(`TauCeti.SymplecticForm.IsLagrangian.orthogonal_map_snd_sup_map_fst_eq_relCompExcess`). When
`W` is finite-dimensional, the endpoint projection is therefore injective exactly when those
projections span the middle space. In finite dimension the matching dimension is half the outer
dimension plus the excess dimension; its quotient is the Lagrangian composite.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

namespace TauCeti.SymplecticForm

variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]
  {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {ω₃ : SymplecticForm U}
  {L : Submodule ℝ (V × W)} {K : Submodule ℝ (W × U)}

/-- Composition of isotropic linear relations is isotropic. No finite-dimensionality
or transversality hypothesis is needed. -/
theorem IsIsotropic.relComp (hL : (ω₁.twistedProd ω₂).IsIsotropic L)
    (hK : (ω₂.twistedProd ω₃).IsIsotropic K) :
    (ω₁.twistedProd ω₃).IsIsotropic (L.relComp K) := by
  rw [isIsotropic_iff] at hL hK ⊢
  simp only [Submodule.mem_relComp]
  rintro x ⟨y, hxy, hyx⟩ z ⟨w, hzw, hwz⟩
  have h₁ := hL (x.1, y) hxy (z.1, w) hzw
  have h₂ := hK (y, x.2) hyx (w, z.2) hwz
  simp only [twistedProd_apply] at h₁ h₂ ⊢
  linarith

/-- The characteristic directions of the middle-coordinate matching condition used by
`Submodule.relCompFiberProduct` have zero outer coordinates and equal middle coordinates. -/
private lemma eq_of_forall_matching_twistedProd_eq_zero {z : (V × W) × (W × U)}
    (h : ∀ y : (V × W) × (W × U), y.1.2 = y.2.1 →
      ω₁ y.1.1 z.1.1 - ω₂ y.1.2 z.1.2 + (ω₂ y.2.1 z.2.1 - ω₃ y.2.2 z.2.2) = 0) :
    z.1.1 = 0 ∧ z.1.2 = z.2.1 ∧ z.2.2 = 0 := by
  refine ⟨ω₁.separatingRight _ fun v ↦ ?_, sub_eq_zero.mp <| ω₂.separatingRight _ fun w ↦ ?_,
    ω₃.separatingRight _ fun u ↦ ?_⟩
  · simpa using h ((v, 0), (0, 0)) rfl
  · have := h ((0, w), (w, 0)) rfl
    simp only [map_zero, LinearMap.zero_apply, zero_sub, sub_zero, map_sub] at this ⊢
    linarith
  · simpa using h ((0, 0), (0, u)) rfl

/-- Composition of finite-dimensional linear Lagrangian relations is Lagrangian,
including compositions with excess matching directions. -/
theorem IsLagrangian.relComp [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ U] (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    (ω₁.twistedProd ω₃).IsLagrangian (L.relComp K) := by
  let Ω := (ω₁.twistedProd ω₂).prod (ω₂.twistedProd ω₃)
  rw [isLagrangian_iff]
  refine ⟨hL.isIsotropic.relComp hK.isIsotropic, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  let z : (V × W) × (W × U) := ((x.1, 0), (0, x.2))
  have hz : z ∈ Ω.orthogonal (L.relCompFiberProduct K) := by
    rw [mem_orthogonal_iff]
    intro y hy
    obtain ⟨hyL, hyK, hmatch⟩ := Submodule.mem_relCompFiberProduct.mp hy
    have hcomp : (y.1.1, y.2.2) ∈ L.relComp K :=
      Submodule.mem_relComp.mpr ⟨y.1.2, hyL, hmatch ▸ hyK⟩
    have hzero := (mem_orthogonal_iff.mp hx) _ hcomp
    simpa [Ω, z, sub_eq_add_neg] using hzero
  -- Orthogonality puts the lift in the product relation plus a characteristic direction.
  have hprod : Ω.orthogonal (L.prod K) = L.prod K :=
    le_antisymm (isCoisotropic_iff_le.mp (hL.prod hK).isCoisotropic)
      (isIsotropic_iff_le.mp (hL.prod hK).isIsotropic)
  rw [Submodule.relCompFiberProduct_def, Ω.orthogonal_inf, hprod] at hz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  obtain ⟨hbv, hbw, hbu⟩ := eq_of_forall_matching_twistedProd_eq_zero fun y hy ↦ by
    simpa only [Ω, prod_apply, twistedProd_apply] using
      mem_orthogonal_iff.mp hb y (LinearMap.mem_eqLocus.mpr hy)
  have hav : a.1.1 = x.1 := by
    simpa [z, hbv] using congrArg (fun p : (V × W) × (W × U) ↦ p.1.1) hab
  have hau : a.2.2 = x.2 := by
    simpa [z, hbu] using congrArg (fun p : (V × W) × (W × U) ↦ p.2.2) hab
  have haw : a.1.2 = a.2.1 := by
    have h₁ := congrArg (fun p : (V × W) × (W × U) ↦ p.1.2) hab
    have h₂ := congrArg (fun p : (V × W) × (W × U) ↦ p.2.1) hab
    dsimp [z] at h₁ h₂
    rw [← hbw] at h₂
    exact add_right_cancel (h₁.trans h₂.symm)
  apply Submodule.mem_relComp.mpr
  exact ⟨a.1.2, hav ▸ ha.1, hau ▸ haw ▸ ha.2⟩

/-! ### Transversality and excess -/

/-- For isotropic relations, every excess direction is symplectically orthogonal to both middle
projections. -/
theorem IsIsotropic.relCompExcess_le_orthogonal_map_snd_sup_map_fst
    (hL : (ω₁.twistedProd ω₂).IsIsotropic L) (hK : (ω₂.twistedProd ω₃).IsIsotropic K) :
    L.relCompExcess K ≤
      ω₂.orthogonal (L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)) := by
  intro w hw
  obtain ⟨hwL, hwK⟩ := Submodule.mem_relCompExcess.mp hw
  refine mem_orthogonal_iff.mpr fun v hv ↦ ?_
  obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  have h₁ := (isIsotropic_iff.mp hL) y hy _ hwL
  have h₂ := (isIsotropic_iff.mp hK) z hz _ hwK
  simp only [twistedProd_apply, map_zero, zero_sub, sub_zero, neg_eq_zero] at h₁ h₂
  simp [h₁, h₂]

/-- For coisotropic relations, every direction symplectically orthogonal to both middle
projections is an excess direction. -/
theorem IsCoisotropic.orthogonal_map_snd_sup_map_fst_le_relCompExcess
    (hL : (ω₁.twistedProd ω₂).IsCoisotropic L) (hK : (ω₂.twistedProd ω₃).IsCoisotropic K) :
    ω₂.orthogonal (L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)) ≤
      L.relCompExcess K := by
  intro w hw
  refine Submodule.mem_relCompExcess.mpr ⟨?_, ?_⟩
  · refine isCoisotropic_iff.mp hL _ (mem_orthogonal_iff.mpr fun y hy ↦ ?_)
    have : ω₂ y.2 w = 0 := mem_orthogonal_iff.mp hw _
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hy))
    simp [twistedProd_apply, this]
  · refine isCoisotropic_iff.mp hK _ (mem_orthogonal_iff.mpr fun z hz ↦ ?_)
    have : ω₂ z.1 w = 0 := mem_orthogonal_iff.mp hw _
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem hz))
    simp [twistedProd_apply, this]

/-- **Transverse composition has no excess.** If the projections of isotropic relations `L` and
`K` to their common factor `W` span it, then no nonzero `w` has `(0, w) ∈ L` and `(w, 0) ∈ K`.
Such `w` are the excess directions of the composition: matching pairs that the composite map
sends to zero. -/
theorem IsIsotropic.eq_zero_of_map_snd_sup_map_fst_eq_top
    (hL : (ω₁.twistedProd ω₂).IsIsotropic L) (hK : (ω₂.twistedProd ω₃).IsIsotropic K)
    (htr : L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U) = ⊤) {w : W}
    (hwL : (0, w) ∈ L) (hwK : (w, 0) ∈ K) : w = 0 := by
  have hw := hL.relCompExcess_le_orthogonal_map_snd_sup_map_fst hK
    (Submodule.mem_relCompExcess.mpr ⟨hwL, hwK⟩)
  rw [htr] at hw
  exact ω₂.separatingRight w fun v ↦ mem_orthogonal_iff.mp hw v Submodule.mem_top

/-- **Relations without excess compose transversally.** If `L` and `K` are coisotropic relations
and no nonzero `w` has `(0, w) ∈ L` and `(w, 0) ∈ K`, then the projections of `L` and `K` to
their common finite-dimensional factor `W` span it. -/
theorem IsCoisotropic.map_snd_sup_map_fst_eq_top [FiniteDimensional ℝ W]
    (hL : (ω₁.twistedProd ω₂).IsCoisotropic L) (hK : (ω₂.twistedProd ω₃).IsCoisotropic K)
    (h : ∀ w, (0, w) ∈ L → (w, 0) ∈ K → w = 0) :
    L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U) = ⊤ := by
  set S := L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)
  -- The symplectic complement of `S` consists of excess directions, so it vanishes.
  suffices hS : ω₂.orthogonal S = ⊥ by
    rw [← ω₂.orthogonal_orthogonal S, hS, orthogonal_bot]
  refine (Submodule.eq_bot_iff _).mpr fun w hw ↦ ?_
  obtain ⟨hwL, hwK⟩ :=
    Submodule.mem_relCompExcess.mp (hL.orthogonal_map_snd_sup_map_fst_le_relCompExcess hK hw)
  exact h w hwL hwK

/-- For linear canonical relations, transversality of the composition and absence of excess are
equivalent: the projections of `L` and `K` to `W` span it exactly when the excess
`L.relCompExcess K`, the set of `w` with `(0, w) ∈ L` and `(w, 0) ∈ K`, is trivial. -/
theorem IsLagrangian.map_snd_sup_map_fst_eq_top_iff [FiniteDimensional ℝ W]
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L) (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U) = ⊤ ↔ L.relCompExcess K = ⊥ := by
  simp only [Submodule.eq_bot_iff, Submodule.mem_relCompExcess, and_imp]
  exact ⟨fun htr _ ↦ hL.isIsotropic.eq_zero_of_map_snd_sup_map_fst_eq_top hK.isIsotropic htr,
    hL.isCoisotropic.map_snd_sup_map_fst_eq_top hK.isCoisotropic⟩

/-- The excess of two linear Lagrangian relations is the symplectic orthogonal of the sum of
their middle projections. Thus the failure of transversality and the kernel of endpoint
projection are dual manifestations of the same excess. This identity needs no finite dimension. -/
theorem IsLagrangian.orthogonal_map_snd_sup_map_fst_eq_relCompExcess
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    ω₂.orthogonal (L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)) =
      L.relCompExcess K :=
  le_antisymm (hL.isCoisotropic.orthogonal_map_snd_sup_map_fst_le_relCompExcess hK.isCoisotropic)
    (hL.isIsotropic.relCompExcess_le_orthogonal_map_snd_sup_map_fst hK.isIsotropic)

/-- The endpoint projection of matching linear Lagrangian relations is injective exactly
when the two middle projections are transverse. -/
theorem IsLagrangian.relCompProjection_injective_iff [FiniteDimensional ℝ W]
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    Function.Injective (L.relCompProjection K) ↔
      L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U) = ⊤ := by
  rw [Submodule.relCompProjection_injective_iff, hL.map_snd_sup_map_fst_eq_top_iff hK]

/-- The dimension of the matching space is half the outer symplectic dimension plus
the excess dimension. Quotienting the excess leaves precisely a Lagrangian dimension. -/
theorem IsLagrangian.two_mul_finrank_relCompFiberProduct [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] [FiniteDimensional ℝ U]
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    2 * Module.finrank ℝ (L.relCompFiberProduct K) =
      Module.finrank ℝ V + Module.finrank ℝ U + 2 * Module.finrank ℝ (L.relCompExcess K) := by
  have hdim := L.finrank_relComp_add_finrank_relCompExcess K
  have hlag := (hL.relComp hK).two_mul_finrank
  rw [Module.finrank_prod] at hlag
  omega

/-- The dimension of the excess also equals the codimension of the sum of the middle
projections. Only the middle symplectic space needs to be finite-dimensional. -/
theorem IsLagrangian.finrank_map_snd_sup_map_fst_add_finrank_relCompExcess
    [FiniteDimensional ℝ W]
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    Module.finrank ℝ ↥(L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)) +
      Module.finrank ℝ (L.relCompExcess K) = Module.finrank ℝ W := by
  rw [← hL.orthogonal_map_snd_sup_map_fst_eq_relCompExcess hK]
  exact ω₂.finrank_add_finrank_orthogonal _

end TauCeti.SymplecticForm
