/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.PowerMap

/-!
# Homomorphism and subgroup class-fusion maps on numbered conjugacy classes

Any group homomorphism `φ : H →* G` induces a **class-fusion** map
`Fin dH.numClasses → Fin dG.numClasses` sending the index of a conjugacy class of `H` to the
index of the conjugacy class of `G` containing its image. In particular, taking `φ = S.subtype`
for a subgroup `S ≤ G` yields the subgroup class-fusion table needed for character restriction.

* `dH.fusion dG φ` tracks `ConjClasses.map φ`, composes functorially (`fusion_comp`), is
  surjective when `φ` is (`fusion_surjective_of_surjective`), divides representative orders
  (`orderOf_rep_fusion_dvd`, preserving them when `φ` is injective), and commutes with
  `invIndex`, `powIndex`, and `zpowIndex`.
* For groups whose class data is certified from explicit conjugating witnesses rather than by
  brute enumeration, `dH.fusion dG φ i = j` is paired with `fusion_eq_of_conj` (`c * rep * c⁻¹ =
  φ (dH.rep i)`) and transport lemmas across `TauCeti.ClassData.map`.

## Main definitions

* `TauCeti.ClassData.fusion`: the class-fusion map `Fin dH.numClasses → Fin dG.numClasses` along a
  group homomorphism `φ : H →* G`.

## Main results

* `TauCeti.ClassData.classOf_fusion`:
  `dG.classOf (dH.fusion dG φ i) = ConjClasses.map φ (dH.classOf i)`.
* `TauCeti.ClassData.fusion_comp`: functoriality of class fusion under homomorphism composition.
* `TauCeti.ClassData.fusion_surjective_of_surjective`: surjective homomorphisms induce surjective
  fusion maps.
* `TauCeti.ClassData.orderOf_rep_fusion_of_injective`: injective homomorphisms preserve
  representative orders under class fusion.
* `TauCeti.ClassData.fusion_zpowIndex`, `TauCeti.ClassData.fusion_invIndex`,
  `TauCeti.ClassData.fusion_powIndex`: compatibility of class fusion with inverse and power maps.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967), 446–450.
* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press (1976).
-/

public section

namespace TauCeti.ClassData

section Fusion

variable {H G K : Type*} [Group H] [Group G] [Group K]

/-- **The numbered class-fusion map** along a group homomorphism `φ : H →* G`: sends class index
`i` of `dH` to the class index in `dG` of `φ (dH.rep i)`. Only `G` needs decidable conjugacy, and
the body is exposed so subgroup-fusion tables reduce in the kernel. -/
@[expose] def fusion (dH : ClassData H) (dG : ClassData G)
    [DecidableRel (IsConj : G → G → Prop)] (φ : H →* G) (i : Fin dH.numClasses) :
    Fin dG.numClasses :=
  dG.index (φ (dH.rep i))

section TargetDecidable

variable (dH : ClassData H) (dG : ClassData G) [DecidableRel (IsConj : G → G → Prop)]

/-- The defining equation of `TauCeti.ClassData.fusion`, left off `@[simp]` so it does not rewrite
past `TauCeti.ClassData.fusion_index` or `TauCeti.ClassData.fusion_id`. -/
theorem fusion_def (φ : H →* G) (i : Fin dH.numClasses) :
    dH.fusion dG φ i = dG.index (φ (dH.rep i)) :=
  (rfl)

/-- The representative at the fused index `dH.fusion dG φ i` is conjugate in `G` to
`φ (dH.rep i)`. -/
theorem isConj_rep_fusion (φ : H →* G) (i : Fin dH.numClasses) :
    IsConj (dG.rep (dH.fusion dG φ i)) (φ (dH.rep i)) :=
  dG.isConj_rep_index (φ (dH.rep i))

/-- `dH.fusion dG φ i` equals `j` if and only if `dG.rep j` is conjugate to `φ (dH.rep i)`. -/
theorem fusion_eq_iff {φ : H →* G} {i : Fin dH.numClasses} {j : Fin dG.numClasses} :
    dH.fusion dG φ i = j ↔ IsConj (dG.rep j) (φ (dH.rep i)) :=
  dG.index_eq_iff

/-- **Certify a fusion-table entry** `dH.fusion dG φ i = j` from an explicit conjugator `c : G`. -/
theorem fusion_eq_of_conj {φ : H →* G} {i : Fin dH.numClasses} {j : Fin dG.numClasses}
    (c : G) (hc : c * dG.rep j * c⁻¹ = φ (dH.rep i)) :
    dH.fusion dG φ i = j :=
  (dH.fusion_eq_iff dG).mpr (isConj_iff.mpr ⟨c, hc⟩)

/-- **The numbered fusion map tracks `ConjClasses.map φ`.** -/
@[simp]
theorem classOf_fusion (φ : H →* G) (i : Fin dH.numClasses) :
    dG.classOf (dH.fusion dG φ i) = ConjClasses.map φ (dH.classOf i) := by
  rw [fusion, classOf_index, classOf_eq_mk, ConjClasses.map_mk]

/-- **Functoriality of class fusion**: fusing along `φ` and then along `ψ` is fusing along
`ψ.comp φ`. -/
theorem fusion_comp (dK : ClassData K) [DecidableRel (IsConj : K → K → Prop)]
    (φ : H →* G) (ψ : G →* K) (i : Fin dH.numClasses) :
    dG.fusion dK ψ (dH.fusion dG φ i) = dH.fusion dK (ψ.comp φ) i := by
  apply dK.classOf_injective
  rw [classOf_fusion, classOf_fusion, classOf_fusion, dH.classOf_eq_mk]
  simp only [ConjClasses.map_mk, MonoidHom.comp_apply]

/-- Along a surjective homomorphism, the class-fusion map is surjective. -/
theorem fusion_surjective_of_surjective {φ : H →* G} (hφ : Function.Surjective φ) :
    Function.Surjective (dH.fusion dG φ) := by
  intro j
  obtain ⟨C, hC⟩ := ConjClasses.map_surjective hφ (dG.classOf j)
  obtain ⟨i, rfl⟩ := dH.classOf_surjective C
  exact ⟨i, dG.classOf_injective ((dH.classOf_fusion dG φ i).trans hC)⟩

/-- The element order of a fused class representative in `G` divides the order of the source
representative in `H`. -/
theorem orderOf_rep_fusion_dvd (φ : H →* G) (i : Fin dH.numClasses) :
    orderOf (dG.rep (dH.fusion dG φ i)) ∣ orderOf (dH.rep i) := by
  rw [fusion, dG.orderOf_rep_index]
  exact orderOf_map_dvd φ (dH.rep i)

/-- **Injective homomorphisms (in particular subgroup embeddings `S.subtype`) preserve
representative orders under class fusion.** -/
theorem orderOf_rep_fusion_of_injective {φ : H →* G} (hφ : Function.Injective φ)
    (i : Fin dH.numClasses) :
    orderOf (dG.rep (dH.fusion dG φ i)) = orderOf (dH.rep i) := by
  rw [fusion, dG.orderOf_rep_index, orderOf_injective φ hφ]

/-- Transporting the source class data along `e : K ≃* H` reindexes `fusion` on the left. -/
@[simp]
theorem fusion_map_left (e : K ≃* H) (dK : ClassData K) (φ : H →* G)
    (i : Fin (dK.map e).numClasses) :
    (dK.map e).fusion dG φ i =
      dK.fusion dG (φ.comp (e : K →* H)) (Fin.cast (dK.numClasses_map e) i) := by
  simp [fusion]

/-- Transporting the target class data along `e : G ≃* K` reindexes `fusion` on the right. -/
@[simp]
theorem fusion_map_right [DecidableRel (IsConj : K → K → Prop)] (e : G ≃* K)
    (φ : H →* G) (i : Fin dH.numClasses) :
    dH.fusion (dG.map e) ((e : G →* K).comp φ) i =
      Fin.cast (dG.numClasses_map e).symm (dH.fusion dG φ i) := by
  simp [fusion]

end TargetDecidable

/-- Fusing along the identity homomorphism is the identity on class indices. -/
@[simp]
theorem fusion_id (dG : ClassData G) [DecidableRel (IsConj : G → G → Prop)]
    (i : Fin dG.numClasses) :
    dG.fusion dG (MonoidHom.id G) i = i := by
  rw [fusion, MonoidHom.id_apply, index_rep]

/-- Fusing `dG` into `dG.map e` along `(e : G →* H)` is the canonical `Fin.cast`. -/
@[simp]
theorem fusion_coe_map (dG : ClassData G) [DecidableRel (IsConj : H → H → Prop)]
    (e : G ≃* H) (i : Fin dG.numClasses) :
    dG.fusion (dG.map e) (e : G →* H) i = Fin.cast (dG.numClasses_map e).symm i := by
  classical
  simp [fusion]

section BothDecidable

variable (dH : ClassData H) (dG : ClassData G)
  [DecidableRel (IsConj : H → H → Prop)] [DecidableRel (IsConj : G → G → Prop)]

/-- **Class fusion tracks homomorphisms** under `TauCeti.ClassData.index`. -/
@[simp]
theorem fusion_index (φ : H →* G) (h : H) :
    dH.fusion dG φ (dH.index h) = dG.index (φ h) :=
  dG.index_eq_index_iff.mpr (φ.map_isConj (dH.isConj_rep_index h))

-- Not `@[simp]`: `dH` does not appear on the left-hand side, so `simp` cannot infer it.
/-- `TauCeti.ClassData.indexClass` intertwines `ConjClasses.map φ` with `dH.fusion dG φ`. -/
theorem indexClass_map (φ : H →* G) (C : ConjClasses H) :
    dG.indexClass (ConjClasses.map φ C) = dH.fusion dG φ (dH.indexClass C) := by
  obtain ⟨h, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.map_mk, indexClass_mk, indexClass_mk, fusion_index]

/-- Class fusion commutes with every `ℤ`-power map. -/
@[simp]
theorem fusion_zpowIndex (φ : H →* G) (z : ℤ) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.zpowIndex z i) = dG.zpowIndex z (dH.fusion dG φ i) := by
  rw [zpowIndex, fusion_index, map_zpow, ← zpowIndex_index, ← fusion]

/-- Class fusion commutes with the inverse-class map. -/
@[simp]
theorem fusion_invIndex (φ : H →* G) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.invIndex i) = dG.invIndex (dH.fusion dG φ i) := by
  rw [← zpowIndex_neg_one, fusion_zpowIndex, zpowIndex_neg_one]

/-- Class fusion commutes with every `ℕ`-power map. -/
@[simp]
theorem fusion_powIndex (φ : H →* G) (n : ℕ) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.powIndex n i) = dG.powIndex n (dH.fusion dG φ i) := by
  rw [← zpowIndex_natCast, fusion_zpowIndex, zpowIndex_natCast]

end BothDecidable

end Fusion

end TauCeti.ClassData
