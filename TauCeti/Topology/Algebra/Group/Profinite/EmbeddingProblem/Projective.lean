/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Maps.Proper.Basic

public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Lift

/-!
# Projectivity from finite embedding problems

Closed subgroups of `A × G` that project onto `G` form lift relations. Compactness of
their fibers preserves surjectivity along decreasing chains. Finite `p`-kernel
embedding problems refine a relation at any open-normal quotient of `A`.

A minimal relation (`Subgroup.exists_minimal_isClosed_le`) therefore supplies compatible
finite-level solutions. The existing inverse-limit assembly gives
`isProjective_of_hasPGroupSolutions`, without finite generation of `G`. Compactness is applied to
fibers in `A`; the sets of level solutions need not be finite.
-/

public section

namespace TauCeti

universe u v w

/-- Every continuous map to a quotient of a profinite pro-`p` group lifts continuously.
The source, the covering group and the quotient may lie in independent universes. -/
def IsProjective (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (A : Type v) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (B : Type w) [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B],
    IsProP p A → ∀ (α : A →ₜ* B), Function.Surjective α →
      ∀ f : G →ₜ* B, ∃ φ : G →ₜ* A, α.comp φ = f

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [CompactSpace A]

/-- A surjective closed relation admits a continuous selection in each finite quotient. -/
private theorem exists_quotient_map_in_relation {p : ℕ} (hG : HasPGroupSolutions p G)
    (hA : IsProP p A) (H : Subgroup (A × G)) (hclosed : IsClosed (H : Set (A × G)))
    (hsurj : ∀ g : G, ∃ a : A, (a, g) ∈ H) (U : OpenNormalSubgroup A) :
    ∃ δ : G →ₜ* A ⧸ U.toSubgroup,
      ∀ g : G, ∃ a : A, (a, g) ∈ H ∧ QuotientGroup.mk' U.toSubgroup a = δ g := by
  classical
  -- Stage 1: the projection `s : H → G` is surjective and, as `A` is compact, a closed map,
  -- hence a quotient map.
  let s : H →* G := (MonoidHom.snd A G).comp H.subtype
  have hs_apply (x : H) : s x = (x : A × G).2 := by
    simp only [s, MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.coe_snd]
  have hs : Function.Surjective s := by
    intro g
    obtain ⟨a, ha⟩ := hsurj g
    exact ⟨⟨(a, g), ha⟩, hs_apply _⟩
  have hscont : Continuous s := continuous_snd.comp continuous_subtype_val
  have hsquot : Topology.IsQuotientMap s :=
    (isClosedMap_snd_of_compactSpace.comp hclosed.isClosedMap_subtype_val).isQuotientMap
      hscont hs
  -- Stage 2: reduce the first coordinate modulo `U`, giving `t : H → A ⧸ U` with range
  -- `t.range`, and quotient `t.range` further by the image `K` of `ker s`; the composite
  -- `π : H → t.range ⧸ K` is continuous into a finite discrete group.
  let t : H →* A ⧸ U.toSubgroup :=
    (QuotientGroup.mk' U.toSubgroup).comp ((MonoidHom.fst A G).comp H.subtype)
  let τ := t.rangeRestrict
  let K := s.ker.map τ
  have : K.Normal := Subgroup.Normal.map inferInstance τ t.rangeRestrict_surjective
  have : DiscreteTopology (t.range ⧸ K) := QuotientGroup.discreteTopology (isOpen_discrete _)
  let π := (QuotientGroup.mk' K).comp τ
  have hle : s.ker ≤ π.ker := by
    intro h hh
    exact (QuotientGroup.eq_one_iff (τ h)).mpr (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
  -- Stage 3: `π` kills `ker s`, so it descends along the quotient map `s` to a continuous
  -- `β : G → t.range ⧸ K`.
  let β := s.liftOfSurjective hs ⟨π, hle⟩
  have hβ (h : H) : β (s h) = π h := by
    simp only [β, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  have hπcont : Continuous π :=
    QuotientGroup.continuous_mk.comp
      ((QuotientGroup.continuous_mk.comp
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _)
  have hβcont : Continuous β := hsquot.continuous_iff.mpr <| by
    have heq : (β : G → _) ∘ s = π := funext hβ
    rw [heq]
    exact hπcont
  -- Stage 4: `K` is a `p`-group inside the `p`-group `A ⧸ U`, so `HasPGroupSolutions` lifts `β`
  -- through `t.range ↠ t.range ⧸ K` to `γ : G → t.range`; `δ` is `γ` followed by the inclusion.
  obtain ⟨γ, hγ, hγβ⟩ := hG.exists_comp_eq (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K)
    (((isProP_iff.mp hA U).to_subgroup t.range).to_subgroup _) β
    ((MonoidHom.continuous_iff_isOpen_ker _).mp hβcont)
  let δ : G →ₜ* A ⧸ U.toSubgroup :=
    ⟨t.range.subtype.comp γ,
      continuous_subtype_val.comp (γ.continuous_iff_isOpen_ker.mpr hγ)⟩
  refine ⟨δ, ?_⟩
  intro g
  -- Stage 5: over `g`, pick `h ∈ H` with `s h = g`; then `τ h` and `γ g` agree modulo
  -- `K = τ (ker s)`, so correcting `h` by an element of `ker s` gives a point of `H` over `g`
  -- whose first coordinate reduces to `δ g`.
  obtain ⟨h, hh⟩ := hs g
  have hquot : QuotientGroup.mk' K (τ h) = QuotientGroup.mk' K (γ g) := by
    calc
      QuotientGroup.mk' K (τ h) = β (s h) := (hβ h).symm
      _ = β g := congrArg β hh
      _ = QuotientGroup.mk' K (γ g) := (DFunLike.congr_fun hγβ g).symm
  obtain ⟨k, hk, hkτ⟩ := Subgroup.mem_map.mp (QuotientGroup.eq.mp hquot)
  have hsg : s (h * k) = g := by
    rw [map_mul, hh, MonoidHom.mem_ker.mp hk, mul_one]
  refine ⟨(h * k).1.1, ?_, ?_⟩
  · have hm := (h * k).2
    rwa [← hsg, hs_apply, Prod.mk.eta]
  · have ht : τ (h * k) = γ g := by
      rw [map_mul, hkτ, mul_inv_cancel_left]
    exact congrArg Subtype.val ht

variable {B : Type w} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- Finite `p`-kernel solvability supplies compatible level solutions without finite generation. -/
theorem HasPGroupSolutions.exists_compatible_levelSolutions {p : ℕ}
    (hG : HasPGroupSolutions p G) (hA : IsProP p A)
    (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B) :
    ∃ β : ∀ U, LevelSolution α hα f U,
      ∀ ⦃V U : OpenNormalSubgroup A⦄ (hVU : V ≤ U),
        levelSolutionMap α hα f hVU (β V) = β U := by
  classical
  let R := (α.toMonoidHom.comp (MonoidHom.fst A G)).eqLocus
    (f.toMonoidHom.comp (MonoidHom.snd A G))
  have hRclosed : IsClosed (R : Set (A × G)) :=
    isClosed_eq (α.continuous.comp continuous_fst) (f.continuous.comp continuous_snd)
  have hRsurj : ∀ g : G, ∃ a : A, (a, g) ∈ R := fun g ↦ hα (f g)
  obtain ⟨H, hH⟩ := Subgroup.exists_minimal_isClosed_le R hRclosed hRsurj
  obtain ⟨hHR, hHclosed, hHsurj⟩ := hH.prop
  have hlevels (U : OpenNormalSubgroup A) :
      ∃ δ : G →ₜ* A ⧸ U.toSubgroup,
        ∀ a g, (a, g) ∈ H → QuotientGroup.mk' U.toSubgroup a = δ g := by
    obtain ⟨δ, hδ⟩ := exists_quotient_map_in_relation hG hA H hHclosed hHsurj U
    let K := H ⊓ ((QuotientGroup.mk' U.toSubgroup).comp (MonoidHom.fst A G)).eqLocus
      (δ.toMonoidHom.comp (MonoidHom.snd A G))
    have hKclosed : IsClosed (K : Set (A × G)) :=
      hHclosed.inter (isClosed_eq (QuotientGroup.continuous_mk.comp continuous_fst)
        (δ.continuous.comp continuous_snd))
    have hKsurj : ∀ g : G, ∃ a : A, (a, g) ∈ K := by
      intro g
      obtain ⟨a, ha, hδa⟩ := hδ g
      exact ⟨a, ha, hδa⟩
    exact ⟨δ, fun a g ha ↦ (hH.le_of_le ⟨inf_le_left.trans hHR, hKclosed, hKsurj⟩ inf_le_left ha).2⟩
  choose δ hδ using hlevels
  let β : ∀ U, LevelSolution α hα f U := fun U ↦ ⟨δ U, by
    intro g
    obtain ⟨a, ha⟩ := hHsurj g
    rw [← hδ U a g ha, QuotientGroup.mk'_apply, levelMap_mk]
    exact congrArg (QuotientGroup.mk' (levelImage α hα U).toSubgroup) (hHR ha)⟩
  refine ⟨β, ?_⟩
  intro V U hVU
  apply Subtype.ext
  ext g
  simp only [levelSolutionMap_apply, β]
  obtain ⟨a, ha⟩ := hHsurj g
  rw [← hδ V a g ha, ← hδ U a g ha]
  exact DFunLike.congr_fun (QuotientGroup.mapOfLE_comp_mk' hVU) a

variable [TotallyDisconnectedSpace A]

omit [IsTopologicalGroup G] in
/-- Apply projectivity to a continuous map and a surjection from a profinite pro-`p` group. -/
theorem IsProjective.exists_continuous_lift {p : ℕ} (hG : IsProjective.{u, v, w} p G)
    (hA : IsProP p A) (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B) :
    ∃ φ : G →ₜ* A, α.comp φ = f :=
  hG A B hA α hα f

/-- Solving all finite embedding problems with `p`-group kernel implies projectivity,
with no rank or finite-generation restriction on the source. -/
theorem isProjective_of_hasPGroupSolutions {p : ℕ} (hG : HasPGroupSolutions p G) :
    IsProjective.{u, v, w} p G := by
  intro A _ _ _ _ _ B _ _ _ _ hA α hα f
  obtain ⟨β, hβ⟩ := hG.exists_compatible_levelSolutions hA α hα f
  obtain ⟨φ, hφ, _⟩ := exists_continuous_lift_of_compatible_levelSolutions α hα f β hβ
  exact ⟨φ, hφ⟩

universe u'

omit [IsTopologicalGroup G] in
/-- Projectivity is invariant under topological group isomorphism. -/
theorem IsProjective.of_equiv {p : ℕ} (hG : IsProjective.{u, v, w} p G) {H : Type u'} [Group H]
    [TopologicalSpace H] (e : G ≃ₜ* H) : IsProjective.{u', v, w} p H := by
  intro A _ _ _ _ _ B _ _ _ _ hA α hα f
  obtain ⟨φ, hφ⟩ := hG A B hA α hα (f.comp (e : G →ₜ* H))
  refine ⟨φ.comp (e.symm : H →ₜ* G), ContinuousMonoidHom.ext fun h ↦ ?_⟩
  simpa using DFunLike.congr_fun hφ (e.symm h)

end TauCeti
