/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Basic
public import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Local products for mapping tori

The projection of the mapping torus of a homeomorphism `φ : F ≃ₜ F` to the circle is
locally a product with fibre `F`. Cutting the circle at the class of `a : ℝ` chooses the
unique representative of each remaining height in `(a, a + 1)`. The corresponding open
cylinder embeds in the mapping torus and covers precisely the inverse image of the cut circle.

`MappingTorus.localProduct` identifies that inverse image with the cut circle times `F`,
commuting with the projections. Thus mapping-torus presentations supply actual local product
charts for fibering over the circle, for arbitrary topological fibres and monodromies.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the mapping-torus construction).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti.MappingTorus

variable {F : Type*} [TopologicalSpace F]

/-- The cylinder over an open interval of length one embeds openly in the mapping torus. -/
theorem isOpenEmbedding_mk_Ioo (φ : F ≃ₜ F) (a : ℝ) :
    IsOpenEmbedding (fun p : F × Ioo a (a + 1) => mk φ p.1 p.2) := by
  have hi : IsOpenEmbedding (fun p : F × Ioo a (a + 1) => (p.1, (p.2 : ℝ))) :=
    IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal
  refine .of_continuous_injective_isOpenMap
    ((continuous_mk φ).comp hi.continuous) ?_ ((isOpenMap_mk φ).comp hi.isOpenMap)
  intro p q hpq
  have ht : (p.2 : ℝ) = q.2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self p.2.property)
      (Ioo_subset_Ico_self q.2.property)).mp (by
        simpa only [proj_mk] using congrArg (proj φ) hpq)
  obtain ⟨n, hn, hnt⟩ := (mk_eq_iff φ).mp hpq
  have hn0 : n = 0 := by exact_mod_cast (show (n : ℝ) = 0 by linarith)
  subst n
  apply Prod.ext
  · simpa using hn.symm
  · exact Subtype.ext ht

private theorem range_mk_Ioo (φ : F ≃ₜ F) (a : ℝ) :
    range (fun p : F × Ioo a (a + 1) => mk φ p.1 p.2) =
      (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ)) := by
  let c := AddCircle.openPartialHomeomorphCoe (1 : ℝ) a
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, rfl⟩
    simp only [mem_compl_iff, mem_preimage, proj_mk, mem_singleton_iff]
    exact c.map_source t.property
  · intro hz
    obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
    have hθ : (t : UnitAddCircle) ∈ c.target := by
      simpa only [mem_compl_iff, mem_preimage, proj_mk, c,
        AddCircle.openPartialHomeomorphCoe_target, mem_singleton_iff] using hz
    let s := c.symm (t : UnitAddCircle)
    have hs : s ∈ Ioo a (a + 1) := c.map_target hθ
    have heq : (s : UnitAddCircle) = (t : UnitAddCircle) := c.right_inv hθ
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
    have hst : s = t + (n : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hn
      linarith
    refine ⟨⟨(φ ^ n) x, ⟨s, hs⟩⟩, ?_⟩
    dsimp only
    rw [hst, mk_vadd]

/-- The cylinder over `(a, a + 1)` is homeomorphic to the part of the mapping torus
lying over the circle cut at `a`. -/
private def cylinderHomeomorph (φ : F ≃ₜ F) (a : ℝ) :
    F × Ioo a (a + 1) ≃ₜ (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ)) :=
  (isOpenEmbedding_mk_Ioo φ a).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_mk_Ioo φ a))

/-- The cylinder chart sends a fibre point and its height to their mapping-torus class. -/
private theorem cylinderHomeomorph_apply (φ : F ≃ₜ F) (a : ℝ)
    (p : F × Ioo a (a + 1)) :
    (cylinderHomeomorph φ a p : MappingTorus φ) = mk φ p.1 p.2 := (rfl)

/-- A local product chart for the mapping-torus projection on the circle cut at `a`.
The inverse inserts the unique height representative in `(a, a + 1)`. -/
def localProduct (φ : F ≃ₜ F) (a : ℝ) :
    (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ)) ≃ₜ
      ({(a : UnitAddCircle)}ᶜ : Set UnitAddCircle) × F :=
  (cylinderHomeomorph φ a).symm.trans
    (((Homeomorph.refl F).prodCongr
      (((Homeomorph.setCongr
        (AddCircle.openPartialHomeomorphCoe_source (1 : ℝ) a).symm).trans
          (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).toHomeomorphSourceTarget).trans
        (Homeomorph.setCongr (AddCircle.openPartialHomeomorphCoe_target (1 : ℝ) a)))).trans
        (Homeomorph.prodComm _ _))

/-- The local product preserves the circle coordinate. -/
@[simp] theorem localProduct_fst (φ : F ≃ₜ F) (a : ℝ)
    (z : (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ))) :
    ((localProduct φ a z).1 : UnitAddCircle) = proj φ z := by
  obtain ⟨p, rfl⟩ := (cylinderHomeomorph φ a).surjective z
  rw [localProduct, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
    Homeomorph.trans_apply]
  simp only [Homeomorph.coe_prodComm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Homeomorph.setCongr]
  exact (proj_mk φ p.1 p.2).symm.trans
    (congrArg (proj φ) (cylinderHomeomorph_apply φ a p)).symm

/-- The inverse local product chart uses the representative in `(a, a + 1)` and leaves
the fibre coordinate unchanged. -/
@[simp] theorem localProduct_symm_apply (φ : F ≃ₜ F) (a : ℝ)
    (p : ({(a : UnitAddCircle)}ᶜ : Set UnitAddCircle) × F) :
    ((localProduct φ a).symm p : MappingTorus φ) =
      mk φ p.2 (AddCircle.equivIco (1 : ℝ) a p.1) := by
  rw [localProduct, Homeomorph.symm_trans_apply]
  simp only [Homeomorph.symm_trans_apply, Homeomorph.symm_symm, Homeomorph.prodCongr_symm,
    Homeomorph.prodComm_symm, Homeomorph.coe_prodComm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_symm, Homeomorph.refl_apply, Homeomorph.setCongr]
  rw [cylinderHomeomorph_apply]
  simp only [Prod.map_fst, Prod.fst_swap, id_eq, Prod.map_snd, Prod.snd_swap,
    Homeomorph.symm_trans_apply, Homeomorph.homeomorph_mk_coe_symm, equivOfEq_symm_apply,
    OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe,
    AddCircle.openPartialHomeomorphCoe_symm_apply]

/-- The local product chart recovers the fibre coordinate of a cylinder point whose height
lies in the chosen interval. -/
@[simp] theorem localProduct_mk (φ : F ≃ₜ F) (a : ℝ) (x : F) (t : ℝ)
    (ht : t ∈ Ioo a (a + 1)) :
    (localProduct φ a ⟨mk φ x t, by
      simpa only [mem_compl_iff, mem_preimage, proj_mk, AddCircle.openPartialHomeomorphCoe_target,
        AddCircle.openPartialHomeomorphCoe_apply, mem_singleton_iff] using
        (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).map_source (by
          simpa only [AddCircle.openPartialHomeomorphCoe_source] using ht)⟩).2 = x := by
  have hz : ∀ z : (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ)),
      (z : MappingTorus φ) = mk φ x t → z = cylinderHomeomorph φ a (x, ⟨t, ht⟩) :=
    fun z hz => Subtype.ext (hz.trans (cylinderHomeomorph_apply φ a (x, ⟨t, ht⟩)).symm)
  calc
    _ = (localProduct φ a (cylinderHomeomorph φ a (x, ⟨t, ht⟩))).2 :=
      congrArg (fun z => (localProduct φ a z).2) (hz _ rfl)
    _ = x := by
      rw [localProduct, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
        Homeomorph.trans_apply]
      rfl

/-- Over the cut circle, the mapping-torus projection is a trivial fibre bundle with fibre `F`. -/
theorem isHomeomorphicTrivialFiberBundle_proj (φ : F ≃ₜ F) (a : ℝ) :
    IsHomeomorphicTrivialFiberBundle F
      (fun z : (((proj φ) ⁻¹' {(a : UnitAddCircle)})ᶜ : Set (MappingTorus φ)) =>
        (⟨proj φ z, z.property⟩ : ({(a : UnitAddCircle)}ᶜ : Set UnitAddCircle))) :=
  ⟨localProduct φ a, fun z => Subtype.ext (localProduct_fst φ a z)⟩

/-- Every circle point has an open neighbourhood on which the mapping-torus projection is
a trivial fibre bundle with the original fibre. -/
theorem exists_isHomeomorphicTrivialFiberBundle_proj (φ : F ≃ₜ F) (θ : UnitAddCircle) :
    ∃ U : Set UnitAddCircle, IsOpen U ∧ θ ∈ U ∧
      IsHomeomorphicTrivialFiberBundle F
        (fun z : (proj φ) ⁻¹' U => (⟨proj φ z, z.property⟩ : U)) := by
  obtain ⟨b, hb⟩ := exists_ne θ
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective b
  exact ⟨{(a : UnitAddCircle)}ᶜ, isOpen_compl_singleton,
    hb.symm, isHomeomorphicTrivialFiberBundle_proj φ a⟩

end TauCeti.MappingTorus
