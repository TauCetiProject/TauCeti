/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.Shrink
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

Conversely, a projective pro-`p` group solves every finite embedding problem with `p`-group kernel
(`hasPGroupSolutions_of_isProjective`): its finite quotients are `p`-groups, so such a problem is a
lifting problem against a surjection of finite `p`-groups. For a pro-`p` group the two conditions
are therefore equivalent (`isProjective_iff_hasPGroupSolutions`), and projectivity does not depend
on the universes of the groups it quantifies over.

## Main definitions

* `TauCeti.IsProjective`: every continuous homomorphism into a quotient of a profinite pro-`p`
  group lifts continuously.

## Main results

* `TauCeti.isProjective_of_hasPGroupSolutions`: solving the finite embedding problems with
  `p`-group kernel gives projectivity.
* `TauCeti.hasPGroupSolutions_of_isProjective`: a projective pro-`p` group solves the finite
  embedding problems with `p`-group kernel.
* `TauCeti.isProjective_iff_hasPGroupSolutions`: for a pro-`p` group, projectivity is equivalent
  to solving the finite embedding problems with `p`-group kernel.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4 and §5.9.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 7.6.
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

/-! ### The converse for pro-`p` groups -/

/-- **A projective pro-`p` group solves every finite embedding problem with `p`-group kernel.**
The universes `v` and `w` in which `G` is assumed projective are arbitrary.

The pro-`p` hypothesis cannot be dropped. `G = PSL₂(𝔽₅)` is perfect, so every continuous
homomorphism from it to a pro-`2` group is trivial and `G` is projective at `p = 2`; but the
problem given by `SL₂(𝔽₅) ↠ G`, with kernel of order `2` and `π = id`, has no solution, since
`-1` is the only involution of `SL₂(𝔽₅)` while `G` has involutions. -/
theorem hasPGroupSolutions_of_isProjective {p : ℕ} (hGp : IsProP p G)
    (hG : IsProjective.{u, v, w} p G) : HasPGroupSolutions p G := by
  refine hasPGroupSolutions_iff.mpr fun P hP ↦ ?_
  -- `E` is a finite `p`-group, so the problem is a lifting problem against `α`.
  have hE : IsPGroup p P.E := P.isPGroup_E hGp hP
  let _ : TopologicalSpace P.Q := ⊥
  have : DiscreteTopology P.Q := ⟨rfl⟩
  have hπ : Continuous P.π := P.π.continuous_iff_isOpen_ker.mpr P.isOpen_ker_π
  -- Move `E` and `Q` into the universes `v` and `w`, with the discrete topology, and lift `π`
  -- against `α` there.
  let eE : Shrink.{v} P.E ≃* P.E := Shrink.mulEquiv
  let eQ : Shrink.{w} P.Q ≃* P.Q := Shrink.mulEquiv
  let _ : TopologicalSpace (Shrink.{v} P.E) := ⊥
  have : DiscreteTopology (Shrink.{v} P.E) := ⟨rfl⟩
  have : Finite (Shrink.{v} P.E) := Finite.of_equiv P.E eE.symm.toEquiv
  let _ : TopologicalSpace (Shrink.{w} P.Q) := ⊥
  have : DiscreteTopology (Shrink.{w} P.Q) := ⟨rfl⟩
  let α : Shrink.{v} P.E →ₜ* Shrink.{w} P.Q :=
    ⟨eQ.symm.toMonoidHom.comp (P.α.comp eE.toMonoidHom), continuous_of_discreteTopology⟩
  let f : G →ₜ* Shrink.{w} P.Q :=
    ⟨eQ.symm.toMonoidHom.comp P.π, (continuous_of_discreteTopology (f := eQ.symm)).comp hπ⟩
  obtain ⟨φ, hφ⟩ := hG.exists_continuous_lift (hE.of_equiv eE.symm).isProP α
    (eQ.symm.surjective.comp (P.α_surjective.comp eE.surjective)) f
  refine ⟨eE.toMonoidHom.comp φ.toMonoidHom,
    FiniteEmbeddingProblem.isSolution_iff.mpr ⟨?_, ?_⟩⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ eE.injective]
    exact (MonoidHom.continuous_iff_isOpen_ker _).mp φ.continuous
  · ext g
    have h := DFunLike.congr_fun hφ g
    simp only [α, f, ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_mk,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    exact eQ.symm.injective h

/-- **Projectivity of a pro-`p` group is solvability of its finite `p`-embedding problems.** A
pro-`p` group is projective exactly when it solves every finite embedding problem with `p`-group
kernel. Since the right-hand side does not mention the universes `v` and `w`, neither does
projectivity of a pro-`p` group. -/
theorem isProjective_iff_hasPGroupSolutions {p : ℕ} (hGp : IsProP p G) :
    IsProjective.{u, v, w} p G ↔ HasPGroupSolutions p G :=
  ⟨hasPGroupSolutions_of_isProjective hGp, isProjective_of_hasPGroupSolutions⟩

end TauCeti
