/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Composition
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ

/-!
# Pullback of holomorphic functions and germ compatibility

Contravariant pullback along a holomorphic map `f : holomorphicFunctions U` taking values in `V`
defines a continuous algebra homomorphism `HolomorphicFunctions.comap f hf :
holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U`. Given any open set `V`,
`HolomorphicFunctions.preimageOpens f V` is the open subset of `U` where `f` takes values in `V`.

These open-domain pullback operations match `holomorphicGerms.comap` through `toGerm`
(`comap_toGerm`) and produce open domain-shrinking neighbourhoods via
`subset_preimageOpens_of_spectrum_subset`, linking open-domain continuity to germ pullback in the
composition theorem for the holomorphic functional calculus.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

variable {U V W : Opens ℂ}

/-- Contravariant pullback of holomorphic functions along a holomorphic map `f` from `U` into
`V`. -/
def comap (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨fun z ↦ ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
      (holomorphicFunctions V).val).codRestrict (holomorphicFunctions U) fun g ↦ by
    refine mem_holomorphicFunctions_iff_of_eqOn (g := extend g ∘ extend f) (fun z ↦ ?_) |>.mpr ?_
    · simp only [Function.comp_apply, extend_apply f z]
      exact extend_apply g ⟨f.val z, hf z⟩
    · exact (differentiableOn_extend g).comp (differentiableOn_extend f) fun z hz ↦ by
        rw [extend_apply f ⟨z, hz⟩]
        exact hf ⟨z, hz⟩

/-- Pointwise evaluation of the pullback `comap f hf g`. -/
@[simp]
theorem comap_apply (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (z : U) :
    (comap f hf g).val z = g.val ⟨f.val z, hf z⟩ := (rfl)

/-- Pullback of ambient holomorphic representatives commutes with `HolomorphicFunctions.of`. -/
@[simp]
theorem comap_of {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U)
    (hf : ∀ z : U, (of U φ hφ).val z ∈ V) (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ V) :
    comap (of U φ hφ) hf (of V ψ hψ) =
      of U (ψ ∘ φ) (hψ.comp hφ fun z hz ↦
        SetLike.mem_coe.mpr (by simpa only [of_apply] using hf ⟨z, hz⟩)) := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back the coordinate function along `f` recovers `f`. -/
@[simp]
theorem comap_of_id (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    comap f hf (of V id differentiableOn_id) = f := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back along the identity on `U` is the identity algebra homomorphism. -/
@[simp]
theorem comap_id (hf : ∀ z : U, (of U id differentiableOn_id).val z ∈ U) :
    comap (of U id differentiableOn_id) hf = AlgHom.id ℂ (holomorphicFunctions U) := by
  ext g : 1
  apply Subtype.ext
  ext z
  simp

/-- Pullback along a holomorphic map is continuous in the compact-open topology. -/
@[continuity]
theorem continuous_comap (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    Continuous (comap f hf) := by
  unfold comap
  exact ((ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    (⟨fun z ↦ ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
      continuous_subtype_val).subtype_mk _

/-- Restricting a pulled-back holomorphic function is pullback along the restricted map. -/
@[simp]
theorem restrict_comap (hWU : W ≤ U) (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions V) :
    restrict hWU (comap f hf g) =
      comap (restrict hWU f)
        (fun z ↦ by rw [restrict_apply]; exact hf (Set.inclusion hWU z)) g := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back a restricted holomorphic function is pullback along the ambient inclusion. -/
@[simp]
theorem comap_restrict (hVW : V ≤ W) (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions W) :
    comap f hf (restrict hVW g) = comap f (fun z ↦ hVW (hf z)) g := by
  apply Subtype.ext
  ext z
  simp

/-- Contravariant pullback of holomorphic functions is functorial under composition. -/
@[simp]
theorem comap_comap (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (hg : ∀ w : V, g.val w ∈ W) (h : holomorphicFunctions W) :
    comap f hf (comap g hg h) =
      comap (comap f hf g) (fun z ↦ by rw [comap_apply]; exact hg ⟨f.val z, hf z⟩) h := by
  apply Subtype.ext
  ext z
  simp

/-- The open subset of `U` on which `f : holomorphicFunctions U` takes values in `V`. -/
def preimageOpens (f : holomorphicFunctions U) (V : Opens ℂ) : Opens ℂ :=
  ⟨Subtype.val '' (f.val ⁻¹' (V : Set ℂ)),
    U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)⟩

/-- Membership in `preimageOpens f V` means lying in `U` with image in `V`. -/
@[simp]
theorem mem_preimageOpens {f : holomorphicFunctions U} {V : Opens ℂ} {z : ℂ} :
    z ∈ preimageOpens f V ↔ ∃ hz : z ∈ U, f.val ⟨z, hz⟩ ∈ V := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hfz⟩
    exact ⟨⟨z, hz⟩, hfz, rfl⟩

/-- `preimageOpens f V` is an open subset of `U`. -/
theorem preimageOpens_le (f : holomorphicFunctions U) (V : Opens ℂ) :
    preimageOpens f V ≤ U := by
  intro z hz
  exact (mem_preimageOpens.mp hz).1

/-- The restriction of `f` to `preimageOpens f V` takes values in `V`. -/
theorem restrict_preimageOpens_mem (f : holomorphicFunctions U) (V : Opens ℂ)
    (z : preimageOpens f V) : (restrict (preimageOpens_le f V) f).val z ∈ V := by
  obtain ⟨hz, hfz⟩ := mem_preimageOpens.mp z.property
  simpa only [restrict_apply] using hfz

/-- A subset `s ⊆ U` mapped by `f` into `V` is contained in `preimageOpens f V`. -/
theorem subset_preimageOpens {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U)
    (hf : ∀ (z : ℂ) (hz : z ∈ s), f.val ⟨z, hs hz⟩ ∈ V) :
    s ⊆ preimageOpens f V := fun z hz ↦
  mem_preimageOpens.mpr ⟨hs hz, hf z hz⟩

/-- A set `s` lies in `preimageOpens f V` if and only if `s ⊆ U` and `f` maps `s` into `V`. -/
theorem subset_preimageOpens_iff {s : Set ℂ} {f : holomorphicFunctions U} :
    s ⊆ preimageOpens f V ↔ ∃ hs : s ⊆ U, ∀ (z : ℂ) (hz : z ∈ s), f.val ⟨z, hs hz⟩ ∈ V :=
  ⟨fun h ↦ ⟨h.trans (preimageOpens_le f V), fun _ hz ↦ (mem_preimageOpens.mp (h hz)).2⟩,
    fun ⟨hs, hf⟩ ↦ subset_preimageOpens hs f hf⟩

end TauCeti.HolomorphicFunctions

namespace TauCeti.holomorphicGerms

open HolomorphicFunctions

variable {s t : Set ℂ}

/-- If `spectrum ℂ (toGerm hsU f) ⊆ t` and `t ⊆ V`, then `s` lies in `preimageOpens f V`. -/
theorem subset_preimageOpens_of_spectrum_subset {U V : Opens ℂ} {hsU : s ⊆ U}
    {f : holomorphicFunctions U} (hg : spectrum ℂ (toGerm hsU f) ⊆ t) (htV : t ⊆ V) :
    s ⊆ preimageOpens f V := by
  intro z hz
  refine mem_preimageOpens.mpr ⟨hsU hz, htV (hg ?_)⟩
  rw [spectrum_eq]
  exact ⟨z, hz, eval_toGerm hsU z hz f⟩

/-- Germ pullback agrees with open-domain pullback on any pair of open representatives. -/
@[simp]
theorem comap_toGerm {U V : Opens ℂ} (hsU : s ⊆ U) (htV : t ⊆ V)
    (f : holomorphicFunctions U) (hfV : ∀ z : U, f.val z ∈ V)
    (hg : spectrum ℂ (toGerm hsU f) ⊆ t) (ψ : holomorphicFunctions V) :
    comap (toGerm hsU f) hg (toGerm htV ψ) =
      toGerm hsU (HolomorphicFunctions.comap f hfV ψ) := by
  have hf : toGerm hsU f = ofFun (extend f) (analyticOnNhd_extend hsU f) :=
    toGerm_eq_ofFun hsU f (extend f) (analyticOnNhd_extend hsU f) fun z ↦ (extend_apply f z).symm
  have hψ : toGerm htV ψ = ofFun (extend ψ) (analyticOnNhd_extend htV ψ) :=
    toGerm_eq_ofFun htV ψ (extend ψ) (analyticOnNhd_extend htV ψ) fun z ↦ (extend_apply ψ z).symm
  have hg' : spectrum ℂ (ofFun (extend f) (analyticOnNhd_extend hsU f)) ⊆ t := hf ▸ hg
  rw [comap_congr_left hf (hg₂ := hg'), hψ, comap_ofFun]
  exact (toGerm_eq_ofFun hsU (HolomorphicFunctions.comap f hfV ψ) (extend ψ ∘ extend f) _ fun z ↦ by
    simp only [HolomorphicFunctions.comap_apply, Function.comp_apply, extend_apply f z]
    exact (extend_apply ψ ⟨f.val z, hfV z⟩).symm).symm

end TauCeti.holomorphicGerms
