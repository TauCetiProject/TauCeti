/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ

/-!
# Composition of holomorphic functions on open domains

If `f` is holomorphic on an open set `U` and maps a subset `s ⊆ U` into an open set `V`, then
`HolomorphicFunctions.preimageOpen f V` is an open subset `U' ≤ U` containing `s` that `extend f`
maps into `V`. Right-composition by `f` on any open subset `U' ≤ U` mapped into `V` is a
continuous unital `ℂ`-algebra homomorphism
`HolomorphicFunctions.compRight f hU' hmaps : holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U'`.

The bridge theorem `holomorphicGerms.compRight_toGerm` identifies `HolomorphicFunctions.compRight`
with germ right-composition `holomorphicGerms.compRight` (defined in
`TauCeti.Analysis.Complex.Germ.Algebra`).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

variable {s : Set ℂ} {U U' U'' V V' W : Opens ℂ}

/-- The open subset of `U` where `f` takes values in `V`. -/
def preimageOpen (f : holomorphicFunctions U) (V : Opens ℂ) : Opens ℂ where
  carrier := Subtype.val '' (f.val ⁻¹' (V : Set ℂ))
  is_open' := U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)

/-- A point lies in `preimageOpen f V` iff it lies in `U` and `extend f` sends it into `V`. -/
@[simp]
theorem mem_preimageOpen {f : holomorphicFunctions U} {V : Opens ℂ} {z : ℂ} :
    z ∈ preimageOpen f V ↔ z ∈ U ∧ extend f z ∈ V := by
  constructor
  · rintro ⟨⟨z, hz⟩, hV, rfl⟩
    refine ⟨hz, ?_⟩
    rw [extend_apply f ⟨z, hz⟩]
    exact hV
  · rintro ⟨hz, hV⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    simpa only [mem_preimage, SetLike.mem_coe, extend_apply f ⟨z, hz⟩] using hV

/-- The preimage open domain is contained in the source domain of `f`. -/
theorem preimageOpen_le (f : holomorphicFunctions U) (V : Opens ℂ) : preimageOpen f V ≤ U :=
  fun _ hz => (mem_preimageOpen.mp hz).1

/-- Extending `f` by zero maps `preimageOpen f V` into `V`. -/
theorem mapsTo_extend_preimageOpen (f : holomorphicFunctions U) (V : Opens ℂ) :
    MapsTo (extend f) (preimageOpen f V) V :=
  fun _ hz => (mem_preimageOpen.mp hz).2

/-- Any subset of `U` mapped into `V` by `extend f` lies in `preimageOpen f V`. -/
theorem subset_preimageOpen {f : holomorphicFunctions U} {V : Opens ℂ}
    (hsU : s ⊆ U) (hsV : MapsTo (extend f) s V) : s ⊆ preimageOpen f V :=
  fun _ hz => mem_preimageOpen.mpr ⟨hsU hz, hsV hz⟩

private def compMap (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) : C(U', V) :=
  ⟨fun z : U' => ⟨f.val (Set.inclusion hU' z),
      SetLike.mem_coe.mp (extend_apply f (Set.inclusion hU' z) ▸ hmaps z.property)⟩,
    (f.val.continuous.comp (continuous_inclusion hU')).subtype_mk _⟩

/-- Right-composition by `f : holomorphicFunctions U` on an open subset `U' ≤ U` mapped into `V`
by `extend f` (sending `g ↦ g ∘ f`), as a unital `ℂ`-algebra homomorphism
`holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U'`. -/
def compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U' :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ (compMap f hU' hmaps)).comp
    (holomorphicFunctions V).val).codRestrict (holomorphicFunctions U') fun g =>
      mem_holomorphicFunctions_iff.mpr
        ⟨extend g ∘ extend f,
          (differentiableOn_extend g).comp ((differentiableOn_extend f).mono hU') hmaps,
          fun z => by
            have hzV : extend f z ∈ V := SetLike.mem_coe.mp (hmaps z.property)
            simp only [AlgHom.comp_apply, Subalgebra.val_apply, ContinuousMap.compRightAlgHom_apply,
              ContinuousMap.comp_apply, compMap, Function.comp_apply]
            rw [extend_apply g ⟨extend f z, hzV⟩]
            congr 1
            exact Subtype.ext (extend_apply f (Set.inclusion hU' z))⟩

/-- Pointwise evaluation of `compRight f hU' hmaps g` on `U'`. -/
@[simp]
theorem compRight_apply (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) (g : holomorphicFunctions V) (z : U') :
    (compRight f hU' hmaps g).val z = extend g (extend f z) := by
  have hzV : extend f z ∈ V := SetLike.mem_coe.mp (hmaps z.property)
  rw [extend_apply g ⟨extend f z, hzV⟩, compRight, AlgHom.coe_codRestrict,
    AlgHom.comp_apply, Subalgebra.val_apply, ContinuousMap.compRightAlgHom_apply,
    ContinuousMap.comp_apply]
  exact congrArg g.val (Subtype.ext (extend_apply f (Set.inclusion hU' z)).symm)

/-- Extending `compRight f hU' hmaps g` agrees with `extend g (extend f z)` on `U'`. -/
@[simp]
theorem extend_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) (g : holomorphicFunctions V) {z : ℂ} (hz : z ∈ U') :
    extend (compRight f hU' hmaps g) z = extend g (extend f z) := by
  rw [extend_apply _ ⟨z, hz⟩, compRight_apply]

/-- Right-composition on holomorphic functions is continuous for the compact-open topology. -/
@[continuity]
theorem continuous_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) : Continuous (compRight f hU' hmaps) := by
  unfold compRight
  exact ((ContinuousMap.compRightAlgHom_continuous ℂ ℂ (compMap f hU' hmaps)).comp
    continuous_subtype_val).subtype_mk _

/-- Right-composition of restricted ambient holomorphic functions agrees with ambient
composition. -/
@[simp]
theorem compRight_of {φ ψ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ V) (hψ : DifferentiableOn ℂ ψ U)
    (hU' : U' ≤ U) (hmaps : MapsTo (extend (of U ψ hψ)) U' V) :
    compRight (of U ψ hψ) hU' hmaps (of V φ hφ) =
      of U' (φ ∘ ψ) (hφ.comp (hψ.mono hU') fun z hz => by
        simpa only [extend_of hψ (hU' hz)] using hmaps hz) := by
  apply Subtype.ext
  ext z
  have hzV : ψ z ∈ V := by
    simpa only [← SetLike.mem_coe, extend_of hψ (hU' z.property)] using hmaps z.property
  rw [compRight_apply, of_apply, Function.comp_apply, extend_of hψ (hU' z.property),
    extend_of hφ hzV]

/-- Right-composing the coordinate function with `f` gives the restriction of `f`. -/
@[simp]
theorem compRight_id (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) :
    compRight f hU' hmaps (of V id differentiableOn_id) = restrict hU' f := by
  apply Subtype.ext
  ext z
  rw [compRight_apply, restrict_apply,
    extend_of differentiableOn_id (SetLike.mem_coe.mp (hmaps z.property)),
    id_eq, extend_apply f (Set.inclusion hU' z)]

/-- Right-composition by the coordinate function is restriction. -/
@[simp]
theorem compRight_of_id (hU' : U' ≤ U)
    (hmaps : MapsTo (extend (of U id differentiableOn_id)) U' V) :
    compRight (of U id differentiableOn_id) hU' hmaps =
      restrict (fun z hz => by
        simpa only [← SetLike.mem_coe, extend_of differentiableOn_id (hU' hz), id_eq] using
          hmaps hz) := by
  ext g z
  have hzV : (z : ℂ) ∈ V := by
    simpa only [← SetLike.mem_coe, extend_of differentiableOn_id (hU' z.property), id_eq] using
      hmaps z.property
  rw [compRight_apply, restrict_apply, extend_of differentiableOn_id (hU' z.property),
    id_eq, extend_apply g ⟨z, hzV⟩]

/-- Shrinking the target domain after right-composition shrinks the domain of right-composition. -/
@[simp]
theorem restrict_comp_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) (hU'' : U'' ≤ U') :
    (restrict hU'').comp (compRight f hU' hmaps) =
      compRight f (hU''.trans hU') (hmaps.mono_left (SetLike.coe_subset_coe.mpr hU'')) := by
  ext g z
  rw [AlgHom.comp_apply, restrict_apply, compRight_apply, compRight_apply]

/-- Applied form of `restrict_comp_compRight`. -/
@[simp]
theorem restrict_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V) (hU'' : U'' ≤ U') (g : holomorphicFunctions V) :
    restrict hU'' (compRight f hU' hmaps g) =
      compRight f (hU''.trans hU') (hmaps.mono_left (SetLike.coe_subset_coe.mpr hU'')) g :=
  DFunLike.congr_fun (restrict_comp_compRight f hU' hmaps hU'') g

/-- Right-composition after restriction widens the codomain of `f`. -/
@[simp]
theorem compRight_comp_restrict (f : holomorphicFunctions U) (hV' : V' ≤ V) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V') :
    (compRight f hU' hmaps).comp (restrict hV') =
      compRight f hU' (hmaps.mono_right (SetLike.coe_subset_coe.mpr hV')) := by
  ext g z
  rw [AlgHom.comp_apply, compRight_apply, compRight_apply,
    extend_restrict hV' g (SetLike.mem_coe.mp (hmaps z.property))]

/-- Applied form of `compRight_comp_restrict`. -/
@[simp]
theorem compRight_apply_restrict (f : holomorphicFunctions U) (hV' : V' ≤ V) (hU' : U' ≤ U)
    (hmaps : MapsTo (extend f) U' V') (g : holomorphicFunctions V) :
    compRight f hU' hmaps (restrict hV' g) =
      compRight f hU' (hmaps.mono_right (SetLike.coe_subset_coe.mpr hV')) g :=
  DFunLike.congr_fun (compRight_comp_restrict f hV' hU' hmaps) g

/-- Right-composition by a restricted inner function agrees with right-composition by the
original function on the smaller domain. -/
@[simp]
theorem compRight_restrict (f : holomorphicFunctions U) (hU₁ : U' ≤ U) (hU₂ : U'' ≤ U')
    (hmaps : MapsTo (extend (restrict hU₁ f)) U'' V) :
    compRight (restrict hU₁ f) hU₂ hmaps =
      compRight f (hU₂.trans hU₁)
        (hmaps.congr fun _ hz => extend_restrict hU₁ f (hU₂ hz)) := by
  ext g z
  rw [compRight_apply, compRight_apply, extend_restrict hU₁ f (hU₂ z.property)]

/-- Associativity of open-domain right-composition as algebra homomorphisms. -/
theorem compRight_comp_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps₁ : MapsTo (extend f) U' V') (g : holomorphicFunctions V) (hV' : V' ≤ V)
    (hmaps₂ : MapsTo (extend g) V' W) :
    (compRight f hU' hmaps₁).comp (compRight g hV' hmaps₂) =
      compRight (compRight f hU' (hmaps₁.mono_right (SetLike.coe_subset_coe.mpr hV')) g) le_rfl
        ((hmaps₂.comp hmaps₁).congr fun _ hz =>
          (extend_compRight f hU' (hmaps₁.mono_right (SetLike.coe_subset_coe.mpr hV')) g
            hz).symm) := by
  ext h z
  rw [AlgHom.comp_apply, compRight_apply, compRight_apply,
    extend_compRight g hV' hmaps₂ h (SetLike.mem_coe.mp (hmaps₁ z.property)),
    extend_compRight f hU' (hmaps₁.mono_right (SetLike.coe_subset_coe.mpr hV')) g z.property]

/-- Associativity of open-domain right-composition on elements. -/
theorem compRight_compRight (f : holomorphicFunctions U) (hU' : U' ≤ U)
    (hmaps₁ : MapsTo (extend f) U' V') (g : holomorphicFunctions V) (hV' : V' ≤ V)
    (hmaps₂ : MapsTo (extend g) V' W) (h : holomorphicFunctions W) :
    compRight f hU' hmaps₁ (compRight g hV' hmaps₂ h) =
      compRight (compRight f hU' (hmaps₁.mono_right (SetLike.coe_subset_coe.mpr hV')) g) le_rfl
        ((hmaps₂.comp hmaps₁).congr fun _ hz =>
          (extend_compRight f hU' (hmaps₁.mono_right (SetLike.coe_subset_coe.mpr hV')) g
            hz).symm) h :=
  DFunLike.congr_fun (compRight_comp_compRight f hU' hmaps₁ g hV' hmaps₂) h

end TauCeti.HolomorphicFunctions

namespace TauCeti.holomorphicGerms

variable {s t : Set ℂ}

/-- Germ right-composition agrees with open-domain right-composition on any compatible open
subset. -/
theorem compRight_toGerm {U U' V : Opens ℂ} (ht : t ⊆ V)
    (f : holomorphicFunctions U) (g : holomorphicFunctions V)
    (hU' : U' ≤ U) (hs' : s ⊆ U') (hmaps : MapsTo (HolomorphicFunctions.extend f) U' V)
    (ht_spec : spectrum ℂ (HolomorphicFunctions.toGerm (hs'.trans hU') f) ⊆ t) :
    compRight (HolomorphicFunctions.toGerm (hs'.trans hU') f) ht_spec
      (HolomorphicFunctions.toGerm ht g) =
      HolomorphicFunctions.toGerm hs' (HolomorphicFunctions.compRight f hU' hmaps g) := by
  have hf_eq : HolomorphicFunctions.toGerm (hs'.trans hU') f =
      ofFun (HolomorphicFunctions.extend f)
        (HolomorphicFunctions.analyticOnNhd_extend (hs'.trans hU') f) :=
    HolomorphicFunctions.toGerm_eq_ofFun (hs'.trans hU') f _ _ fun z =>
      (HolomorphicFunctions.extend_apply f z).symm
  have hg_eq : HolomorphicFunctions.toGerm ht g =
      ofFun (HolomorphicFunctions.extend g) (HolomorphicFunctions.analyticOnNhd_extend ht g) :=
    HolomorphicFunctions.toGerm_eq_ofFun ht g _ _ fun z =>
      (HolomorphicFunctions.extend_apply g z).symm
  have hcongr : ∀ {f₁ f₂ : holomorphicGerms s} (hf : f₁ = f₂) {g₁ g₂ : holomorphicGerms t}
      (_ : g₁ = g₂) (h₁ : spectrum ℂ f₁ ⊆ t),
      compRight f₁ h₁ g₁ = compRight f₂ (hf ▸ h₁) g₂ := by
    rintro _ _ rfl _ _ rfl _
    rfl
  rw [hcongr hf_eq hg_eq ht_spec, compRight_ofFun]
  exact (HolomorphicFunctions.toGerm_eq_ofFun hs' _ _ _ fun z =>
    HolomorphicFunctions.compRight_apply f hU' hmaps g z).symm

end TauCeti.holomorphicGerms
