/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth differential forms and diffeomorphisms of open subsets

This file records how `TauCeti.SmoothForm.mpullback` interacts with diffeomorphisms between open
subsets of manifolds:

* `TauCeti.SmoothForm.mpullback_subtype`: restricting a diffeomorphism `g : M ≃ₘ M'` to open
  subsets `U` and `V` that it maps onto each other intertwines restriction of smooth forms with
  pullback along `g`.
* `TauCeti.SmoothForm.mpullback_opensImage` and
  `TauCeti.SmoothForm.mpullback_opensImage_symm`: flattening a nested open subset `S : Opens W` to
  its image in `M` via `Diffeomorph.opensImage` identifies iterated restriction `S → W → M` with
  direct restriction from `M`.
* `TauCeti.SmoothForm.mpullback_symm_subtype_eq_of_apply_eq`: if a diffeomorphism `Ψ : W₀ ≃ₘ W`
  agrees with an ambient map `G : M → M'` that pulls `σ` back to `τ` at `z`, then `Ψ.symm` pulls
  `τ|_{W₀}` back to `σ|_W` at `Ψ z`.
* `TauCeti.SmoothForm.exists_diffeomorph_opens_of_le`: shrinking the target of a form-intertwining
  open-subset diffeomorphism `φ : U₁ ≃ₘ V₁` to an open subset `O ≤ V₁` restricts `φ` to an open
  subset `U ≤ U₁` while preserving the pullback identity.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Restricting a diffeomorphism `g : M ≃ₘ M'` to open subsets `U` and `V` that it maps onto each
other pulls `β|_V` back to `(g^* β)|_U`. -/
@[simp]
theorem mpullback_subtype (g : M ≃ₘ⟮I, I'⟯ M') {U : Opens M} {V : Opens M'}
    (h : ∀ z, z ∈ U ↔ g z ∈ V) (β : SmoothForm I' M' F k) :
    mpullback (g.subtype h) (g.subtype h).contMDiff
        (mpullback (Subtype.val : V → M') contMDiff_subtypeVal β) =
      mpullback (Subtype.val : U → M) contMDiff_subtypeVal (mpullback g g.contMDiff β) :=
  mpullback_mpullback_of_comp_eq (g.subtype h).contMDiff contMDiff_subtypeVal
    contMDiff_subtypeVal g.contMDiff (funext (g.subtype_apply_coe h)) β

/-- Pulling the ambient restriction of `σ` to the image of a nested open subset `S : Opens W` back
along `Diffeomorph.opensImage S` gives the iterated restriction `S → W → M`. -/
@[simp]
theorem mpullback_opensImage {W : Opens M} (S : Opens W) (σ : SmoothForm I M F k) :
    mpullback (Diffeomorph.opensImage (I := I) S) (Diffeomorph.opensImage (I := I) S).contMDiff
        (mpullback
          (Subtype.val :
            (⟨Subtype.val '' (S : Set W), W.isOpen.isOpenMap_subtypeVal _ S.isOpen⟩ : Opens M) → M)
          contMDiff_subtypeVal σ) =
      mpullback (Subtype.val : S → W) contMDiff_subtypeVal
        (mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ) :=
  mpullback_mpullback_of_comp_eq (Diffeomorph.opensImage (I := I) S).contMDiff contMDiff_subtypeVal
    contMDiff_subtypeVal contMDiff_subtypeVal
    (funext (Diffeomorph.opensImage_apply_coe (I := I) S)) σ

/-- Pulling the iterated restriction `S → W → M` of `σ` back along `(Diffeomorph.opensImage S).symm`
gives the direct restriction of `σ` from `M` to the image of `S`. -/
@[simp]
theorem mpullback_opensImage_symm {W : Opens M} (S : Opens W) (σ : SmoothForm I M F k) :
    mpullback (Diffeomorph.opensImage (I := I) S).symm
        (Diffeomorph.opensImage (I := I) S).symm.contMDiff
        (mpullback (Subtype.val : S → W) contMDiff_subtypeVal
          (mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ)) =
      mpullback
        (Subtype.val :
          (⟨Subtype.val '' (S : Set W), W.isOpen.isOpenMap_subtypeVal _ S.isOpen⟩ : Opens M) → M)
        contMDiff_subtypeVal σ :=
  mpullback_symm_eq_of_mpullback_eq (mpullback_opensImage S σ)

/-- If `∀ w, ↑(Ψ w) = G ↑w` and `G` pulls `σ` back at `z : M` to `τ`, then `Ψ.symm` pulls
`τ|_{W₀}` back at `x = Ψ z` to `σ|_W`. -/
theorem mpullback_symm_subtype_eq_of_apply_eq
    {W₀ : Opens M} {W : Opens M'} (Ψ : W₀ ≃ₘ⟮I, I'⟯ W)
    {τ : SmoothForm I M F k} {σ : SmoothForm I' M' F k}
    {z : W₀} {x : W} (hzx : Ψ z = x) {G : M → M'}
    (h : TauCeti.mpullback (F := F) I I' G σ.val (z : M) = τ.val (z : M))
    (hG : ∀ w : W₀, (Ψ w : M') = G (w : M)) :
    (mpullback Ψ.symm Ψ.symm.contMDiff
      (mpullback (Subtype.val : W₀ → M) contMDiff_subtypeVal τ)).val x =
    (mpullback (Subtype.val : W → M') contMDiff_subtypeVal σ).val x := by
  subst hzx
  have hz : TauCeti.mpullback (F := F) I I' ((Subtype.val : W → M') ∘ ⇑Ψ) σ.val z = τ.val z := by
    have hcomp : (Subtype.val : W → M') ∘ ⇑Ψ = G ∘ (Subtype.val : W₀ → M) := funext hG
    ext v
    have h1 := TauCeti.mpullback_apply (F := F) (I := I) (I' := I')
      ((Subtype.val : W → M') ∘ ⇑Ψ) σ.val z v
    have h2 := TauCeti.mpullback_apply (F := F) (I := I) (I' := I') G σ.val (z : M) v
    have h12 :
        σ.val (((Subtype.val : W → M') ∘ ⇑Ψ) z)
            (fun j ↦ mfderiv I I' ((Subtype.val : W → M') ∘ ⇑Ψ) z (v j)) =
          σ.val (G z.val) (fun j ↦ mfderiv I I' G z.val (v j)) := by
      rw [hcomp, Function.comp_apply]
      exact congrArg (σ.val (G z.val))
        (funext fun j ↦ TauCeti.Manifold.mfderiv_comp_subtype_val_apply (v j))
    exact (h1.trans (h12.trans h2.symm)).trans (DFunLike.congr_fun h v)
  have h1 := mpullback_apply_eq_smul_iff Ψ
    (mpullback Ψ.symm Ψ.symm.contMDiff
      (mpullback (Subtype.val : W₀ → M) contMDiff_subtypeVal τ))
    (mpullback (Subtype.val : W → M') contMDiff_subtypeVal σ) 1 z
  rw [one_smul, one_smul, mpullback_mpullback_symm,
    coe_mpullback_subtype_val_apply, mpullback_mpullback, coe_mpullback] at h1
  exact h1.1 hz.symm

/-- Restricting a diffeomorphism `φ : U₁ ≃ₘ V₁` (pulling `β|_{V₁}` back to `α|_{U₁}`) to an open
subset `O ≤ V₁` yields an open subset `U ≤ U₁` (consisting of the points of `U₁` mapped into `O`)
and a diffeomorphism `ψ : U ≃ₘ O` agreeing with `φ` along `Opens.inclusion hU` and pulling `β|_O`
back to `α|_U`. -/
theorem exists_diffeomorph_opens_of_le
    {U₁ : Opens M} {V₁ : Opens M'} (φ : U₁ ≃ₘ⟮I, I'⟯ V₁)
    {α : SmoothForm I M F k} {β : SmoothForm I' M' F k}
    (hform : mpullback φ φ.contMDiff
        (mpullback (Subtype.val : V₁ → M') contMDiff_subtypeVal β) =
      mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal α)
    {O : Opens M'} (hO : O ≤ V₁) :
    ∃ (U : Opens M) (hU : U ≤ U₁) (ψ : U ≃ₘ⟮I, I'⟯ O),
      (∀ z : U₁, (z : M) ∈ U ↔ (φ z : M') ∈ O) ∧
      (∀ u : U, (ψ u : M') = (φ (Opens.inclusion hU u) : M')) ∧
      mpullback ψ ψ.contMDiff
          (mpullback (Subtype.val : O → M') contMDiff_subtypeVal β) =
        mpullback (Subtype.val : U → M) contMDiff_subtypeVal α := by
  let S' : Opens U₁ := ⟨{x : U₁ | (φ x : M') ∈ O},
    O.isOpen.preimage (continuous_subtypeVal.comp φ.continuous)⟩
  let U : Opens M := ⟨Subtype.val '' (S' : Set U₁), U₁.isOpen.isOpenMap_subtypeVal _ S'.isOpen⟩
  have hU : U ≤ U₁ := Subtype.coe_image_subset (U₁ : Set M) (S' : Set U₁)
  have hφ_symm_mem (y : O) : (φ (φ.symm (Opens.inclusion hO y)) : M') ∈ O := by
    rw [congrArg (Subtype.val : V₁ → M') (φ.apply_symm_apply (Opens.inclusion hO y))]
    exact y.property
  let φO : S' ≃ₘ⟮I, I'⟯ O :=
    { toFun := fun z ↦ ⟨(φ z.val : M'), z.property⟩
      invFun := fun y ↦ ⟨φ.symm (Opens.inclusion hO y), hφ_symm_mem y⟩
      left_inv := fun z ↦ Subtype.ext (φ.left_inv z.val)
      right_inv := fun y ↦
        Subtype.ext (congrArg (Subtype.val : V₁ → M') (φ.apply_symm_apply (Opens.inclusion hO y)))
      contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff O _).1
        (ContMDiff.comp (g := (Subtype.val : V₁ → M')) contMDiff_subtypeVal
          (φ.contMDiff.comp contMDiff_subtypeVal))
      contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff S' _).1
        (φ.symm.contMDiff.comp (contMDiff_inclusion hO)) }
  let ψ : U ≃ₘ⟮I, I'⟯ O := (Diffeomorph.opensImage (I := I) S').symm.trans φO
  have hψ_apply (u : U) : (ψ u : M') = (φ (Opens.inclusion hU u) : M') :=
    congrArg (fun z : U₁ ↦ (φ z : M')) (Diffeomorph.opensImage_symm_apply_coe (I := I) S' u)
  refine ⟨U, hU, ψ, fun z ↦ ⟨fun ⟨w, hw, hwz⟩ ↦ Subtype.ext hwz ▸ hw, fun hz ↦ ⟨z, hz, rfl⟩⟩,
    hψ_apply, ?_⟩
  have hcomp : (Subtype.val : O → M') ∘ ⇑φO =
      ((Subtype.val : V₁ → M') ∘ ⇑φ) ∘ (Subtype.val : S' → U₁) := rfl
  rw [mpullback_trans, mpullback_mpullback_of_comp_eq φO.contMDiff contMDiff_subtypeVal
    contMDiff_subtypeVal (contMDiff_subtypeVal.comp φ.contMDiff) hcomp,
    ← mpullback_mpullback φ (Subtype.val : V₁ → M') φ.contMDiff contMDiff_subtypeVal,
    hform, mpullback_opensImage_symm]

end TauCeti.SmoothForm
