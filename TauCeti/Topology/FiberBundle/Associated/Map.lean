/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom
public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# Maps of associated bundles

An equivariant map `f : F →[G] F'` induces the fibrewise map `[p, v] ↦ [p, f v]`
between bundles associated to the same principal bundle. This construction is functorial,
continuous when `f` is continuous, and a homeomorphism when `f` is an equivariant homeomorphism.
It applies to nonlinear fibre maps as well as to linear and conjugate-linear representation
intertwiners. No choice of a global principal section is required. An equivariant embedding of
fibres induces an embedding of associated total spaces
(`TauCeti.AssociatedBundle.isEmbedding_totalSpaceMap`), so the bundle associated with an
invariant subspace of the fibre is a subspace of the associated bundle.

The fibre maps use the existing glued carriers. Their formula in every preferred chart is
`(b, v) ↦ (b, f v)`, so they preserve the original topologies and trivializations.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§10.7 and 10.9.
-/

public section

noncomputable section

open Bundle MulOpposite Topology

namespace TauCeti.AssociatedBundle

variable {G B : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {F F' F'' : Type*} [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]
  [TopologicalSpace F'] [MulAction G F'] [ContinuousSMul G F']
  [TopologicalSpace F''] [MulAction G F''] [ContinuousSMul G F'']

/-- The fibre map induced by an equivariant map, characterized by `map_mk`. -/
def map (f : F →[G] F') {b : B} (v : AssociatedBundle G P F b) :
    AssociatedBundle G P F' b :=
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  let e := Equiv.ofBijective (mk G p : F → AssociatedBundle G P F b) (mk_bijective p)
  mk G p (f (e.symm v))

/-- An equivariant fibre map sends `[p, v]` to `[p, f v]` in any principal frame. -/
@[simp]
theorem map_mk (f : F →[G] F') {b : B} (p : P b) (v : F) :
    map f (mk G p v) = mk G p (f v) := by
  let q := (FiberBundle.homeomorphAt G P b).symm 1
  let e := Equiv.ofBijective (mk G q : F → AssociatedBundle G P F b) (mk_bijective q)
  have hw : e.symm (mk G p v) = PrincipalBundle.division G q p • v := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (mk_eq_mk_iff.mpr rfl).symm
  dsimp only [map]
  rw [hw, f.map_smul]
  exact mk_eq_mk_iff.mpr rfl

/-- The map induced on total spaces by an equivariant fibre map. -/
def totalSpaceMap (f : F →[G] F') (v : TotalSpace F (AssociatedBundle G P F)) :
    TotalSpace F' (AssociatedBundle G P F') :=
  ⟨v.proj, map f v.2⟩

@[simp]
theorem totalSpaceMap_proj (f : F →[G] F') (v : TotalSpace F (AssociatedBundle G P F)) :
    (totalSpaceMap f v).proj = v.proj :=
  (rfl)

@[simp]
theorem totalSpaceMap_mk (f : F →[G] F') {b : B} (p : P b) (v : F) :
    totalSpaceMap f (⟨b, mk G p v⟩ : TotalSpace F (AssociatedBundle G P F)) =
      ⟨b, mk G p (f v)⟩ := by
  simp [totalSpaceMap]

/-- In each preferred chart the induced map is the original equivariant map on the fibre. -/
theorem trivializationAt_totalSpaceMap (f : F →[G] F') {b b' : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : AssociatedBundle G P F b) :
    trivializationAt F' (AssociatedBundle G P F') b' (totalSpaceMap f ⟨b, v⟩) =
      (b, f (trivializationAt F (AssociatedBundle G P F) b' ⟨b, v⟩).2) := by
  obtain ⟨p, w, rfl⟩ := exists_mk v
  simp only [totalSpaceMap_mk, trivializationAt_mk hb, f.map_smul]

@[simp]
theorem map_id {b : B} (v : AssociatedBundle G P F b) :
    map (MulActionHom.id G : F →[G] F) v = v := by
  obtain ⟨p, w, rfl⟩ := exists_mk v
  simp

@[simp]
theorem map_comp (f : F →[G] F') (g : F' →[G] F'') {b : B}
    (v : AssociatedBundle G P F b) :
    map (g.comp f) v = map g (map f v) := by
  obtain ⟨p, w, rfl⟩ := exists_mk v
  simp

@[simp]
theorem totalSpaceMap_id (v : TotalSpace F (AssociatedBundle G P F)) :
    totalSpaceMap (MulActionHom.id G : F →[G] F) v = v := by
  rcases v with ⟨b, v⟩
  simp [totalSpaceMap]

@[simp]
theorem totalSpaceMap_comp (f : F →[G] F') (g : F' →[G] F'')
    (v : TotalSpace F (AssociatedBundle G P F)) :
    totalSpaceMap (g.comp f) v = totalSpaceMap g (totalSpaceMap f v) := by
  simp [totalSpaceMap]

/-- Continuous equivariant fibre maps induce continuous maps on associated total spaces. -/
theorem continuous_totalSpaceMap (f : F →[G] F') (hf : Continuous f) :
    Continuous (totalSpaceMap (P := P) f) := by
  rw [(isOpenQuotientMap_totalSpaceMk_mk G P F).isQuotientMap.continuous_iff]
  simpa only [Function.comp_def, totalSpaceMap_mk] using
    (Continuous.totalSpaceMk_associatedBundleMk
      (f := fun x : TotalSpace G P × F ↦ x.1.proj) continuous_fst (hf.comp continuous_snd))

/-- An injective equivariant fibre map induces injective maps of the associated fibres. -/
theorem map_injective (f : F →[G] F') (hf : Function.Injective f) (b : B) :
    Function.Injective (map f : AssociatedBundle G P F b → AssociatedBundle G P F' b) := by
  intro v w h
  obtain ⟨p, v, rfl⟩ := exists_mk v
  obtain ⟨q, w, rfl⟩ := exists_mk w
  rw [map_mk, map_mk, mk_eq_mk_iff, ← map_smul] at h
  rw [mk_eq_mk_iff, hf h]

/-- An injective equivariant fibre map induces an injective map of associated total spaces. -/
theorem totalSpaceMap_injective (f : F →[G] F') (hf : Function.Injective f) :
    Function.Injective (totalSpaceMap (P := P) f) := by
  rintro ⟨b, v⟩ ⟨b', w⟩ h
  obtain rfl : b = b' := congrArg TotalSpace.proj h
  simp only [totalSpaceMap, TotalSpace.mk_inj] at h
  rw [map_injective f hf b h]

/-- An inducing equivariant fibre map induces an inducing map of associated total spaces. -/
theorem isInducing_totalSpaceMap (f : F →[G] F') (hf : IsInducing f) :
    IsInducing (totalSpaceMap (P := P) f) := by
  have hq := isOpenQuotientMap_totalSpaceMk_mk G P F
  have hq' := isOpenQuotientMap_totalSpaceMk_mk G P F'
  refine ⟨le_antisymm (continuous_totalSpaceMap f hf.continuous).le_induced fun U hU ↦ ?_⟩
  -- The preimage of `U` in `P × F` is pulled back from an open set `W'` of `P × F'`, and the
  -- image of `W'` in the associated bundle of `F'` cuts out `U`.
  obtain ⟨W', hW', hW⟩ := (IsInducing.id.prodMap hf).isOpen_iff.1 (hU.preimage hq.continuous)
  refine isOpen_induced_iff.2 ⟨_, hq'.isOpenMap _ hW', Set.ext fun y ↦ ?_⟩
  obtain ⟨⟨⟨b, p⟩, v⟩, rfl⟩ := hq.surjective y
  simp only [Set.mem_preimage, Set.mem_image, totalSpaceMap_mk]
  constructor
  · rintro ⟨w, hw, hwy⟩
    obtain ⟨g, rfl⟩ :=
      (totalSpaceMk_mk_eq_iff (x := ((⟨b, p⟩ : TotalSpace G P), f v)) (y := w)).1 hwy.symm
    have hx : ((⟨b, op g • p⟩ : TotalSpace G P), g⁻¹ • v) ∈ Prod.map id f ⁻¹' W' := by
      simpa only [Set.mem_preimage, Prod.map_apply, id_eq, map_smul] using hw
    rw [hW, Set.mem_preimage] at hx
    simpa only [mk_smul_inv_smul] using hx
  · intro hy
    have hx : ((⟨b, p⟩ : TotalSpace G P), v) ∈ Prod.map id f ⁻¹' W' := by
      rw [hW]
      exact hy
    exact ⟨_, hx, rfl⟩

/-- An equivariant embedding of fibres induces an embedding of associated total spaces. -/
theorem isEmbedding_totalSpaceMap (f : F →[G] F') (hf : IsEmbedding f) :
    IsEmbedding (totalSpaceMap (P := P) f) :=
  ⟨isInducing_totalSpaceMap f hf.isInducing, totalSpaceMap_injective f hf.injective⟩

/-- An equivariant homeomorphism induces a homeomorphism of associated total spaces. -/
def homeomorph (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v) :
    TotalSpace F (AssociatedBundle G P F) ≃ₜ TotalSpace F' (AssociatedBundle G P F') :=
  let φ : F →[G] F' := ⟨f, hf⟩
  let ψ := φ.inverse f.symm f.left_inv f.right_inv
  have hφ : ⇑φ = f := rfl
  have hψ : ⇑ψ = f.symm := rfl
  have hψφ : ψ.comp φ = MulActionHom.id G := by
    ext w
    simpa only [MulActionHom.comp_apply, MulActionHom.id_apply, hφ, hψ] using
      f.symm_apply_apply w
  have hφψ : φ.comp ψ = MulActionHom.id G := by
    ext w
    simpa only [MulActionHom.comp_apply, MulActionHom.id_apply, hφ, hψ] using
      f.apply_symm_apply w
  { toFun := totalSpaceMap φ
    invFun := totalSpaceMap ψ
    left_inv := fun v ↦ by rw [← totalSpaceMap_comp, hψφ, totalSpaceMap_id]
    right_inv := fun v ↦ by rw [← totalSpaceMap_comp, hφψ, totalSpaceMap_id]
    continuous_toFun := continuous_totalSpaceMap φ (by simpa only [hφ] using f.continuous)
    continuous_invFun := continuous_totalSpaceMap ψ (by simpa only [hψ] using f.symm.continuous) }

/-- The induced homeomorphism is the total-space map of the equivariant fibre map. -/
theorem homeomorph_apply (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v)
    (v : TotalSpace F (AssociatedBundle G P F)) :
    homeomorph (P := P) f hf v = totalSpaceMap (⟨f, hf⟩ : F →[G] F') v :=
  (rfl)

/-- The inverse homeomorphism is induced by the inverse equivariant fibre map. -/
theorem homeomorph_symm_apply (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v)
    (v : TotalSpace F' (AssociatedBundle G P F')) :
    (homeomorph (P := P) f hf).symm v =
      totalSpaceMap ((⟨f, hf⟩ : F →[G] F').inverse f.symm f.left_inv f.right_inv) v :=
  (rfl)

@[simp]
theorem homeomorph_proj (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v)
    (v : TotalSpace F (AssociatedBundle G P F)) :
    (homeomorph (P := P) f hf v).proj = v.proj := by
  rw [homeomorph_apply, totalSpaceMap_proj]

/-- The induced homeomorphism has the expected formula on classes. -/
@[simp]
theorem homeomorph_mk (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v)
    {b : B} (p : P b) (v : F) :
    homeomorph (P := P) f hf ⟨b, mk G p v⟩ = ⟨b, mk G p (f v)⟩ := by
  have hφ : ⇑(⟨f, hf⟩ : F →[G] F') = f := rfl
  rw [homeomorph_apply, totalSpaceMap_mk, hφ]

/-- The inverse induced homeomorphism applies the inverse fibre map to each class. -/
@[simp]
theorem homeomorph_symm_mk (f : F ≃ₜ F') (hf : ∀ (g : G) v, f (g • v) = g • f v)
    {b : B} (p : P b) (v : F') :
    (homeomorph (P := P) f hf).symm ⟨b, mk G p v⟩ = ⟨b, mk G p (f.symm v)⟩ := by
  apply (homeomorph (P := P) f hf).injective
  simp

end TauCeti.AssociatedBundle
