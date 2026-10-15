/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Comparison
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# Free class-module extensions over their presented quotient

Let `g : ι → G` generate a profinite group topologically, `F` be the free profinite group on
`ι`, and `R = ker(lift g)`. The first isomorphism theorem identifies `F/R` with `G`. Transporting
the quotient action on `Rᵃᵇ(p)` and the class-module extension along this identification gives
an extension over `G`, with projection induced by `lift g`.

When `G = H/W`, choosing lifts of `g` in `H` gives a continuous comparison with the
class-module extension of `H` at `W`. After the identification above this comparison covers
the identity of `H/W`. Thus both extensions can be used in the extension-lifting criterion
over a common quotient, with their prescribed conjugation actions.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti.freeProfiniteGroup

universe u

variable (p : ℕ) {ι G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {g : ι → G}
  (hg : Dense (Subgroup.closure (Set.range g) : Set G))

/-- The action of the presented group on its pro-`p` relation group, transported from
the conjugation action of `F/ker(lift g)` along the first isomorphism theorem. -/
abbrev presentationClassModuleAction :
    MulDistribMulAction G
      (abelianizationProP p (freeProfiniteGroup ι) (lift g : freeProfiniteGroup ι →* G).ker) :=
  MulDistribMulAction.compHom _
    ((lift g).quotientKerEquivOfSurjective (lift_surjective hg)).symm.toMulEquiv.toMonoidHom

/-- The transported action is conjugation by the corresponding class in `F/ker(lift g)`. -/
theorem presentationClassModuleAction_smul (h : G)
    (x : abelianizationProP p (freeProfiniteGroup ι) (lift g : freeProfiniteGroup ι →* G).ker) :
    letI := presentationClassModuleAction p hg
    h • x = ((lift g).quotientKerEquivOfSurjective (lift_surjective hg)).symm h • x :=
  (rfl)

/-- The image of a free-group element acts by its class in `F/ker(lift g)`. -/
@[simp]
theorem presentationClassModuleAction_lift_smul (f : freeProfiniteGroup ι)
    (x : abelianizationProP p (freeProfiniteGroup ι) (lift g : freeProfiniteGroup ι →* G).ker) :
    letI := presentationClassModuleAction p hg
    lift g f • x =
      (QuotientGroup.mk f :
        freeProfiniteGroup ι ⧸ (lift g : freeProfiniteGroup ι →* G).ker) • x := by
  rw [presentationClassModuleAction_smul,
    ContinuousMonoidHom.quotientKerEquivOfSurjective_symm_apply]

/-- The transported conjugation action on the pro-`p` relation group is jointly continuous. -/
theorem continuousSMul_presentationClassModuleAction :
    letI := presentationClassModuleAction p hg
    ContinuousSMul G
      (abelianizationProP p (freeProfiniteGroup ι) (lift g : freeProfiniteGroup ι →* G).ker) :=
  MulAction.continuousSMul_compHom
    ((lift g).quotientKerEquivOfSurjective (lift_surjective hg)).symm.continuous

/-- The class-module extension of a free presentation, with quotient the presented group.
Its total group remains the canonical quotient `F/ker(R → Rᵃᵇ(p))`. -/
abbrev presentationProfiniteExtension :
    letI := presentationClassModuleAction p hg
    ProfiniteGroupExtension G
      (abelianizationProP p (freeProfiniteGroup ι) (lift g : freeProfiniteGroup ι →* G).ker) := by
  letI := presentationClassModuleAction p hg
  letI : IsClosed ((lift g : freeProfiniteGroup ι →* G).ker : Set (freeProfiniteGroup ι)) :=
    (lift g).isClosed_ker
  exact (abelianizationProPProfiniteExtension p (freeProfiniteGroup ι)
    (lift g : freeProfiniteGroup ι →* G).ker).relabelQuotient
    ((lift g).quotientKerEquivOfSurjective (lift_surjective hg))
    (fun q x ↦ by
      rw [presentationClassModuleAction_smul, ContinuousMulEquiv.symm_apply_apply])

/-- The projection of the free presentation extension sends the class of `f` to `lift g f`. -/
theorem presentationProfiniteExtension_rightHom_mk (f : freeProfiniteGroup ι) :
    letI := presentationClassModuleAction p hg
    (presentationProfiniteExtension p hg).toGroupExtension.rightHom (QuotientGroup.mk f) =
      lift g f := by
  let := presentationClassModuleAction p hg
  simp

section Comparison

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]
  (W : Subgroup H) [W.Normal] [IsClosed (W : Set H)] {a : ι → H ⧸ W}
  (ha : Dense (Subgroup.closure (Set.range a) : Set (H ⧸ W)))

/-- The free and ambient class-module extensions admit a continuous comparison over the
identity of the common quotient `H/W`. No surjectivity of the comparison is asserted. -/
theorem exists_presentationProfiniteExtension_comparison :
    letI := presentationClassModuleAction p ha
    ∃ ψ : (presentationProfiniteExtension p ha).E →ₜ*
        (abelianizationProPProfiniteExtension p H W).E,
      (abelianizationProPProfiniteExtension p H W).toGroupExtension.rightHom.comp
        ψ.toMonoidHom = (presentationProfiniteExtension p ha).toGroupExtension.rightHom := by
  let := presentationClassModuleAction p ha
  obtain ⟨ψ, hψ⟩ := exists_abelianizationProPExtension_comparison p W a
  -- The profinite-extension abbreviations retain the canonical total groups, so `ψ` has
  -- the required source and target without transporting its underlying homomorphism.
  refine ⟨ψ, MonoidHom.ext fun x ↦ ?_⟩
  induction x using QuotientGroup.induction_on with
  | H f =>
    rw [MonoidHom.comp_apply, abelianizationProPProfiniteExtension_toGroupExtension,
      presentationProfiniteExtension_rightHom_mk]
    exact hψ f

end Comparison

end TauCeti.freeProfiniteGroup

namespace TauCeti.freeProfiniteGroup

open Additive

variable (p : ℕ) [Fact p.Prime] {G ι : Type} [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G] [Fintype ι] [DecidableEq ι]
  {g : ι → G} (hgen : Subgroup.closure (Set.range g) = ⊤)

/-- Lyndon's coordinates intertwine the presented group's conjugation action with its
left group-algebra action on the relation module. -/
@[simp]
theorem abelianizationProPEquivRelationModule_presentation_smul (t : G)
    (x : Additive (abelianizationProP p (freeProfiniteGroup ι)
      (lift g : freeProfiniteGroup ι →* G).ker)) :
    letI := presentationClassModuleAction p (g := g)
      (by rw [hgen, Subgroup.coe_top]; exact dense_univ)
    abelianizationProPEquivRelationModule p hgen (t • x) =
      MonoidAlgebra.single t (1 : ℤ_[p]) • abelianizationProPEquivRelationModule p hgen x := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set G) := by
    rw [hgen, Subgroup.coe_top]
    exact dense_univ
  let := presentationClassModuleAction p hd
  obtain ⟨f, rfl⟩ := lift_surjective hd t
  rw [← ofMul_toMul x, ← ofMul_smul, presentationClassModuleAction_lift_smul,
    ofMul_smul]
  exact abelianizationProPEquivRelationModule_smul p hgen f x

end TauCeti.freeProfiniteGroup
