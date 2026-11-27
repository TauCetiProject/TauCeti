/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Correspondent
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Defect groups under group isomorphisms, and the Brauer correspondent at `D = 1`

A group isomorphism `σ : G ≃* G'` induces the algebra isomorphism
`MonoidAlgebra.domCongr R R σ : R[G] ≃ₐ[R] R[G']`, which carries block idempotents to block
idempotents (`TauCeti.IsBlockIdempotent.domCongr`). It also carries defect groups to defect
groups: the Brauer projection of `σ e` at `σ(P)` vanishes exactly when that of `e` at `P` does,
because `σ` carries the centralizer of `P` onto that of `σ(P)`
(`TauCeti.brauerProjection_map_domCongr_eq_zero_iff`), and `σ` preserves `p`-subgroups and
inclusions of subgroups (`TauCeti.isDefectGroup_domCongr_map_iff`).

For `D = 1` the normalizer `N_G(1)` is all of `G` and the Brauer projection at `1` keeps every
coefficient, so the Brauer correspondent at `1` is the transport of `e` along `G ≃* N_G(1)`
(`TauCeti.brauerCorrespondent_bot`). In particular the Brauer correspondent of a block of defect
zero is a block of `R[N_G(1)]` of defect zero
(`TauCeti.IsBlockIdempotent.isBlockIdempotent_brauerCorrespondent_bot`,
`TauCeti.IsDefectGroup.isDefectGroup_brauerCorrespondent_bot`): this is the `D = 1` Check of
ModularCharactersAndBlocks §7.1.

## Main results

* `TauCeti.brauerProjection_map_domCongr_eq_zero_iff`: invariance of the vanishing of the Brauer
  projection.
* `TauCeti.isDefectGroup_domCongr_map_iff`: transport of defect groups.
* `TauCeti.brauerCorrespondent_bot`: the Brauer correspondent at `1` is the transport along
  `G ≃* N_G(1)`.
* `TauCeti.IsBlockIdempotent.isBlockIdempotent_brauerCorrespondent_bot`,
  `TauCeti.IsDefectGroup.isDefectGroup_brauerCorrespondent_bot`: blocks of defect zero go to blocks
  of defect zero.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G G' : Type*} [CommSemiring R] [Group G] [Group G']

/-- The centralizer of the image of `P` under a group isomorphism `σ` is the image of the
centralizer of `P`, read elementwise through `σ.symm`. -/
theorem mem_centralizer_map_iff (σ : G ≃* G') (P : Subgroup G) (c : G') :
    c ∈ Subgroup.centralizer ((P.map σ.toMonoidHom : Subgroup G') : Set G') ↔
      σ.symm c ∈ Subgroup.centralizer (P : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun h _ ↦ ?_
  rw [← σ.symm.injective.eq_iff, map_mul, map_mul]
  simp

/-- **The Brauer projection under a group isomorphism.** `Br_{σ(P)}(σ x) = 0` exactly when
`Br_P(x) = 0`. -/
theorem brauerProjection_map_domCongr_eq_zero_iff (σ : G ≃* G') {P : Subgroup G}
    {x : MonoidAlgebra R G} :
    brauerProjection (P.map σ.toMonoidHom) (domCongr R R σ x) = 0 ↔ brauerProjection P x = 0 := by
  simp only [brauerProjection_eq_zero_iff, coeff_domCongr]
  constructor
  · intro h c hc
    simpa using h (σ c) ((mem_centralizer_map_iff σ P (σ c)).2 (by simpa using hc))
  · intro h c hc
    exact h _ ((mem_centralizer_map_iff σ P c).1 hc)

/-- A defect group of `x` is carried by a group isomorphism `σ` to a defect group of `σ x`. -/
theorem IsDefectGroup.domCongr_map (σ : G ≃* G') {p : ℕ} {x : MonoidAlgebra R G}
    {P : Subgroup G} (h : IsDefectGroup R p x P) :
    IsDefectGroup R p (domCongr R R σ x) (P.map σ.toMonoidHom) := by
  obtain ⟨hP, hPx, hmax⟩ := isDefectGroup_iff.1 h
  refine isDefectGroup_iff.2 ⟨hP.map _, (brauerProjection_map_domCongr_eq_zero_iff σ).not.2 hPx,
    fun Q hQ hQx hPQ ↦ ?_⟩
  -- pull `Q` back to `G`
  have hQ' : (Q.comap σ.toMonoidHom).map σ.toMonoidHom = Q :=
    Subgroup.map_comap_eq_self_of_surjective σ.surjective Q
  rw [← hQ'] at hQx hPQ ⊢
  rw [hmax _ (hQ.comap_of_injective _ σ.injective)
    ((brauerProjection_map_domCongr_eq_zero_iff σ).not.1 hQx)
    ((Subgroup.map_le_map_iff_of_injective σ.injective).1 hPQ)]

/-- **Transport of defect groups.** `σ(P)` is a defect group of `σ x` exactly when `P` is a
defect group of `x`. -/
theorem isDefectGroup_domCongr_map_iff (σ : G ≃* G') {p : ℕ} {x : MonoidAlgebra R G}
    {P : Subgroup G} :
    IsDefectGroup R p (domCongr R R σ x) (P.map σ.toMonoidHom) ↔ IsDefectGroup R p x P := by
  refine ⟨fun h ↦ ?_, IsDefectGroup.domCongr_map σ⟩
  have h' := h.domCongr_map σ.symm
  have e1 : domCongr R R σ.symm (domCongr R R σ x) = x := by
    ext g
    simp
  have e2 : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G := by
    ext
    simp
  rwa [Subgroup.map_map, e2, Subgroup.map_id, e1] at h'

/-! ### The Brauer correspondent at `D = 1` -/

/-- The normalizer of the trivial subgroup is everything. -/
theorem normalizer_bot_eq_top : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
  Subgroup.normalizer_eq_top (H := ⊥)

/-- The isomorphism `G ≃* N_G(1)`. -/
noncomputable def normalizerBotEquiv : G ≃* Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
  Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr normalizer_bot_eq_top.symm)

/-- `G ≃* N_G(1)` is the identity on underlying elements. -/
theorem coe_normalizerBotEquiv (g : G) : (normalizerBotEquiv g : G) = g := by
  unfold normalizerBotEquiv
  rfl

/-- **The Brauer correspondent at `D = 1`** is the transport along `G ≃* N_G(1)`: the Brauer
projection at the trivial subgroup keeps every coefficient. -/
theorem brauerCorrespondent_bot (x : MonoidAlgebra R G) :
    brauerCorrespondent (⊥ : Subgroup G) x = domCongr R R normalizerBotEquiv x := by
  ext n
  rw [coeff_brauerCorrespondent_of_mem _ _ (Subgroup.mem_centralizer_iff.2 (by simp)),
    coeff_domCongr]
  congr 1

/-- The Brauer correspondent at `1` of a block idempotent of `R[G]` is a block idempotent of
`R[N_G(1)]`. -/
theorem IsBlockIdempotent.isBlockIdempotent_brauerCorrespondent_bot
    {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b) :
    ∃ b' : Subalgebra.center R (MonoidAlgebra R (Subgroup.normalizer ((⊥ : Subgroup G) : Set G))),
      IsBlockIdempotent b' ∧
        (b' : MonoidAlgebra R (Subgroup.normalizer ((⊥ : Subgroup G) : Set G))) =
          brauerCorrespondent ⊥ (b : MonoidAlgebra R G) := by
  have hb' := hb.domCongr normalizerBotEquiv
  refine ⟨_, hb', ?_⟩
  rw [brauerCorrespondent_bot]
  exact Subalgebra.centerCongr_apply_coe _ b

/-- **Defect zero is preserved at `D = 1`.** If `1` is a defect group of `x ∈ R[G]`, it is a defect
group of the Brauer correspondent of `x` at `1`. -/
theorem IsDefectGroup.isDefectGroup_brauerCorrespondent_bot {p : ℕ} {x : MonoidAlgebra R G}
    (h : IsDefectGroup R p x ⊥) : IsDefectGroup R p (brauerCorrespondent ⊥ x) ⊥ := by
  rw [brauerCorrespondent_bot, ← Subgroup.map_bot normalizerBotEquiv.toMonoidHom]
  exact h.domCongr_map normalizerBotEquiv

end TauCeti
