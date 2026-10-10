/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
public import TauCeti.Topology.Algebra.GroupExtension.Profinite
import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# The profinite extension associated with a pro-p class module

For a closed normal subgroup `V` of a profinite group `G`, kill the kernel of the canonical
map `V → Vᵃᵇ(p)` inside `G`. The resulting quotient sits in an exact sequence

`1 → Vᵃᵇ(p) → G / ker(V → Vᵃᵇ(p)) → G/V → 1`.

The inclusion identifies the kernel with the existing pro-p class module, and the extension
induces its existing conjugation action. This realizes the class-module kernel as the kernel
of a profinite extension, so coefficient maps can be used in the extension lifting theorem.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.2) and the proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Subgroup G) [hV : V.Normal]

/-- The kernel of `V → Vᵃᵇ(p)`, regarded as a subgroup of the ambient group. -/
def abelianizationProPExtensionKernel : Subgroup G :=
  (abelianizationProPMk p G V).ker.map V.subtype

omit [V.Normal] in
/-- An ambient element belongs to the extension kernel exactly when it belongs to `V` and
has trivial image in `Vᵃᵇ(p)`. -/
@[simp]
theorem mem_abelianizationProPExtensionKernel_iff (g : G) :
    g ∈ abelianizationProPExtensionKernel p G V ↔
      ∃ hg : g ∈ V, abelianizationProPMk p G V ⟨g, hg⟩ = 1 := by
  simp only [abelianizationProPExtensionKernel, Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [V.Normal] in
/-- The extension kernel is contained in `V`. -/
theorem abelianizationProPExtensionKernel_le : abelianizationProPExtensionKernel p G V ≤ V := by
  intro g hg
  exact ((mem_abelianizationProPExtensionKernel_iff p G V g).mp hg).choose

instance abelianizationProPExtensionKernel_normal :
    (abelianizationProPExtensionKernel p G V).Normal where
  conj_mem g hg s := by
    obtain ⟨hv, h⟩ := (mem_abelianizationProPExtensionKernel_iff p G V g).mp hg
    refine (mem_abelianizationProPExtensionKernel_iff p G V _).mpr
      ⟨(inferInstance : V.Normal).conj_mem g hv s, ?_⟩
    have heq : MulAut.conjNormal s ⟨g, hv⟩ =
        (⟨s * g * s⁻¹, (inferInstance : V.Normal).conj_mem g hv s⟩ : V) :=
      Subtype.ext (MulAut.conjNormal_apply s ⟨g, hv⟩)
    have hconj := abelianizationProPMk_conj p G V s ⟨g, hv⟩
    simpa only [heq, h, smul_one] using hconj.symm

/-- The total group of the extension with kernel `Vᵃᵇ(p)`. -/
abbrev abelianizationProPExtensionGroup := G ⧸ abelianizationProPExtensionKernel p G V

/-- The projection of the extension onto `G/V`. -/
def abelianizationProPExtensionRightHom : abelianizationProPExtensionGroup p G V →* G ⧸ V :=
  QuotientGroup.lift _ (QuotientGroup.mk' V) (by
    rw [QuotientGroup.ker_mk']
    exact abelianizationProPExtensionKernel_le p G V)

@[simp]
theorem abelianizationProPExtensionRightHom_mk (g : G) :
    abelianizationProPExtensionRightHom p G V (QuotientGroup.mk g) = QuotientGroup.mk g :=
  (rfl)

/-- The inclusion of the class module into the total group, induced by `V ↪ G`. -/
def abelianizationProPExtensionInl :
    abelianizationProP p G V →* abelianizationProPExtensionGroup p G V :=
  (abelianizationProPMk p G V).liftOfSurjective (abelianizationProPMk_surjective p G V)
    ⟨(QuotientGroup.mk' _).comp V.subtype, fun v hv ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩⟩

include hV in
/-- The inclusion sends the class of `v ∈ V` to its class in the ambient quotient. -/
@[simp]
theorem abelianizationProPExtensionInl_mk (v : V) :
    abelianizationProPExtensionInl p G V (abelianizationProPMk p G V v) =
      QuotientGroup.mk (v : G) := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The class-module inclusion is injective. -/
theorem abelianizationProPExtensionInl_injective :
    Function.Injective (abelianizationProPExtensionInl p G V) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨v, rfl⟩ := abelianizationProPMk_surjective p G V x
  rw [MonoidHom.mem_ker, abelianizationProPExtensionInl_mk, QuotientGroup.eq_one_iff,
    mem_abelianizationProPExtensionKernel_iff] at hx
  exact hx.choose_spec

/-- The inclusion has precisely the kernel of the projection as its range. -/
theorem range_abelianizationProPExtensionInl :
    (abelianizationProPExtensionInl p G V).range =
      (abelianizationProPExtensionRightHom p G V).ker := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      obtain ⟨v, rfl⟩ := abelianizationProPMk_surjective p G V a
      simp only [MonoidHom.mem_ker, abelianizationProPExtensionInl_mk,
        abelianizationProPExtensionRightHom_mk]
      exact (QuotientGroup.eq_one_iff (v : G)).mpr v.2
    · intro hg
      have hv : g ∈ V := by
        simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hg
      exact ⟨abelianizationProPMk p G V ⟨g, hv⟩, abelianizationProPExtensionInl_mk p G V _⟩

/-- The projection onto `G/V` is surjective. -/
theorem abelianizationProPExtensionRightHom_surjective :
    Function.Surjective (abelianizationProPExtensionRightHom p G V) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk g, abelianizationProPExtensionRightHom_mk p G V g⟩

/-- The quotient group is an extension of `G/V` by its pro-p class module. -/
def abelianizationProPExtension :
    GroupExtension (abelianizationProP p G V) (abelianizationProPExtensionGroup p G V) (G ⧸ V) :=
  GroupExtension.ofMulEquivKer (abelianizationProPExtensionRightHom_surjective p G V)
    ((MonoidHom.ofInjective (abelianizationProPExtensionInl_injective p G V)).trans
      (MulEquiv.subgroupCongr (range_abelianizationProPExtensionInl p G V)))

/-- The inclusion in the exact sequence is the canonical class-module inclusion. -/
@[simp]
theorem abelianizationProPExtension_inl :
    (abelianizationProPExtension p G V).inl = abelianizationProPExtensionInl p G V := by
  apply MonoidHom.ext
  intro a
  simp [abelianizationProPExtension, GroupExtension.ofMulEquivKer_inl,
    MonoidHom.ofInjective_apply]

/-- The projection in the exact sequence is induced by `G → G/V`. -/
@[simp]
theorem abelianizationProPExtension_rightHom :
    (abelianizationProPExtension p G V).rightHom = abelianizationProPExtensionRightHom p G V := by
  simp [abelianizationProPExtension]

/-- Conjugation in the extension induces the canonical quotient action on `Vᵃᵇ(p)`. -/
theorem abelianizationProPExtension_inducesAction :
    TauCeti.GroupExtension.InducesAction (abelianizationProPExtension p G V) := by
  let S := abelianizationProPExtension p G V
  let σ : S.Section :=
    ⟨fun q ↦ QuotientGroup.mk q.out, fun q ↦ by
      simp [S, abelianizationProPExtension]⟩
  have hσ (q : G ⧸ V) : σ q = QuotientGroup.mk q.out := (rfl)
  apply (GroupExtension.inducesAction_iff_conjActOfSection_eq σ).mpr
  apply MonoidHom.ext
  intro q
  apply MulEquiv.ext
  intro a
  rw [GroupExtension.conjActOfSection_apply]
  apply S.inl_injective
  rw [GroupExtension.inl_conjAct_comm]
  obtain ⟨v, rfl⟩ := abelianizationProPMk_surjective p G V a
  -- The action is conjugation by a representative of the quotient class.
  have hact : q • abelianizationProPMk p G V v =
      abelianizationProPMk p G V (MulAut.conjNormal q.out v) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q, abelianizationProPMk_conj]
  rw [hσ q]
  simp [S, hact, MulAut.conjNormal_apply]

variable [CompactSpace G] [T2Space G] [IsClosed (V : Set G)]

/-- The ambient extension kernel is closed. -/
instance isClosed_abelianizationProPExtensionKernel :
    IsClosed (abelianizationProPExtensionKernel p G V : Set G) := by
  have hclosed : IsClosed ((abelianizationProPMk p G V).ker : Set V) :=
    isClosed_singleton.preimage (continuous_abelianizationProPMk p G V)
  simpa only [abelianizationProPExtensionKernel, Subgroup.coe_map, Set.univ_inter,
    Subgroup.coe_subtype] using
    (isCompact_univ (X := V) |>.inter_right hclosed).image continuous_subtype_val |>.isClosed

omit [T2Space G] in
/-- The inclusion of the class module is continuous. -/
theorem continuous_abelianizationProPExtensionInl :
    Continuous (abelianizationProPExtensionInl p G V) := by
  have hq : Topology.IsQuotientMap (abelianizationProPMk p G V) :=
    Topology.IsQuotientMap.of_surjective_continuous
      (abelianizationProPMk_surjective p G V) (continuous_abelianizationProPMk p G V)
  apply hq.continuous_iff.mpr
  exact (QuotientGroup.continuous_mk.comp continuous_subtype_val).congr fun v ↦
    (abelianizationProPExtensionInl_mk p G V v).symm

omit [CompactSpace G] [T2Space G] [IsClosed (V : Set G)] in
/-- The projection of the class-module extension is continuous. -/
theorem continuous_abelianizationProPExtensionRightHom :
    Continuous (abelianizationProPExtensionRightHom p G V) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk

variable [TotallyDisconnectedSpace G]

/-- The class-module extension as a profinite group extension with the canonical action. -/
abbrev abelianizationProPProfiniteExtension :
    ProfiniteGroupExtension (G ⧸ V) (abelianizationProP p G V) where
  E := abelianizationProPExtensionGroup p G V
  toGroupExtension := abelianizationProPExtension p G V
  continuous_inl := by simpa using continuous_abelianizationProPExtensionInl p G V
  continuous_rightHom := by simpa using continuous_abelianizationProPExtensionRightHom p G V
  inducesAction := abelianizationProPExtension_inducesAction p G V

/-- Bundling the topology retains the canonical exact sequence. -/
@[simp]
theorem abelianizationProPProfiniteExtension_toGroupExtension :
    (abelianizationProPProfiniteExtension p G V).toGroupExtension =
      abelianizationProPExtension p G V :=
  (rfl)

end TauCeti
