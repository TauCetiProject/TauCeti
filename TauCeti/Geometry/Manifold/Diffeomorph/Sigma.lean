/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma

/-!
# Diffeomorphisms of disjoint unions acting componentwise

A family of diffeomorphisms `e i : M i ≃ₘ^n⟮I, J⟯ M' i` assembles into a diffeomorphism of the
disjoint unions `Σ i, M i ≃ₘ^n⟮I, J⟯ Σ i, M' i` acting by `e i` on the copy of `M i`. This is the
smooth form of Mathlib's `Equiv.sigmaCongrRight`. For self-diffeomorphisms it is a group
homomorphism `(∀ i, M i ≃ₘ^n⟮I, I⟯ M i) →* (Σ i, M i) ≃ₘ^n⟮I, I⟯ Σ i, M i`, the smooth form of
`Equiv.Perm.sigmaCongrRightHom`. Composing with `MonoidHom.mulSingle` it produces the
diffeomorphisms of a disjoint union supported on a single component.

## Main definitions

* `Diffeomorph.sigmaCongrRight`: the diffeomorphism of disjoint unions acting componentwise.
* `Diffeomorph.sigmaCongrRightHom`: the same construction as a group homomorphism.

## Main results

* `Diffeomorph.exists_sigmaCongrRight_eq_iff`: a diffeomorphism of disjoint unions is componentwise
  exactly when it preserves the index of every point.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'}
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''}
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {M' : ι → Type*} [∀ i, TopologicalSpace (M' i)] [∀ i, ChartedSpace H' (M' i)]
  {M'' : ι → Type*} [∀ i, TopologicalSpace (M'' i)] [∀ i, ChartedSpace H'' (M'' i)]
  {n : ℕ∞ω}

/-- **Componentwise diffeomorphism of disjoint unions.** A family of diffeomorphisms
`e i : M i ≃ₘ^n⟮I, J⟯ M' i` acts on `Σ i, M i` by `e i` on the copy of `M i`. -/
def sigmaCongrRight (e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i) : (Σ i, M i) ≃ₘ^n⟮I, J⟯ Σ i, M' i where
  toEquiv := Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv
  contMDiff_toFun := ContMDiff.sigmaMap fun i ↦ (e i).contMDiff
  contMDiff_invFun := ContMDiff.sigmaMap fun i ↦ (e i).symm.contMDiff

/-- The componentwise diffeomorphism acts by `e i` on the copy of `M i`. -/
@[simp]
theorem sigmaCongrRight_apply (e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i) (x : Σ i, M i) :
    sigmaCongrRight e x = ⟨x.1, e x.1 x.2⟩ :=
  (rfl)

/-- The underlying equivalence of the componentwise diffeomorphism is the componentwise
equivalence. -/
@[simp]
theorem sigmaCongrRight_toEquiv (e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i) :
    (sigmaCongrRight e).toEquiv = Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv :=
  (rfl)

/-- The inverse of the componentwise diffeomorphism is the componentwise inverse. -/
@[simp]
theorem sigmaCongrRight_symm (e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i) :
    (sigmaCongrRight e).symm = sigmaCongrRight fun i ↦ (e i).symm :=
  (rfl)

/-- The componentwise identity is the identity. -/
@[simp]
theorem sigmaCongrRight_refl :
    sigmaCongrRight (fun i ↦ Diffeomorph.refl I (M i) n) = Diffeomorph.refl I (Σ i, M i) n :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The componentwise composite is the composite of the componentwise diffeomorphisms. -/
theorem sigmaCongrRight_trans (e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i) (e' : ∀ i, M' i ≃ₘ^n⟮J, K⟯ M'' i) :
    (sigmaCongrRight e).trans (sigmaCongrRight e') = sigmaCongrRight fun i ↦ (e i).trans (e' i) :=
  Diffeomorph.ext fun _ ↦ rfl

/-- **Index-preserving diffeomorphisms are componentwise.** A diffeomorphism of disjoint unions is
of the form `sigmaCongrRight e` exactly when it preserves the index of every point. -/
theorem exists_sigmaCongrRight_eq_iff {F : (Σ i, M i) ≃ₘ^n⟮I, J⟯ Σ i, M' i} :
    (∃ e : ∀ i, M i ≃ₘ^n⟮I, J⟯ M' i, sigmaCongrRight e = F) ↔ ∀ x, (F x).1 = x.1 := by
  refine ⟨fun ⟨e, he⟩ x ↦ by rw [← he, sigmaCongrRight_apply], fun hF ↦ ?_⟩
  have hF' (y : Σ i, M' i) : (F.symm y).1 = y.1 := (hF _).symm.trans (by rw [apply_symm_apply])
  -- The maps of components read off from `F` and its inverse.
  let f (i : ι) (x : M i) : M' i := cast (congrArg M' (hF ⟨i, x⟩)) (F ⟨i, x⟩).2
  let g (i : ι) (y : M' i) : M i := cast (congrArg M (hF' ⟨i, y⟩)) (F.symm ⟨i, y⟩).2
  have hf (i : ι) (x : M i) : (⟨i, f i x⟩ : Σ i, M' i) = F ⟨i, x⟩ :=
    Sigma.ext (hF ⟨i, x⟩).symm (cast_heq _ _)
  have hg (i : ι) (y : M' i) : (⟨i, g i y⟩ : Σ i, M i) = F.symm ⟨i, y⟩ :=
    Sigma.ext (hF' ⟨i, y⟩).symm (cast_heq _ _)
  refine ⟨fun i ↦
    { toFun := f i
      invFun := g i
      left_inv x := sigma_mk_injective <| by rw [hg, hf, symm_apply_apply]
      right_inv y := sigma_mk_injective <| by rw [hf, hg, apply_symm_apply]
      contMDiff_toFun := (TauCeti.contMDiff_sigmaMk_comp_iff (g := f i)).mp <| by
        rw [show Sigma.mk i ∘ f i = F ∘ Sigma.mk i from funext (hf i)]
        exact F.contMDiff.comp (TauCeti.contMDiff_sigmaMk i)
      contMDiff_invFun := (TauCeti.contMDiff_sigmaMk_comp_iff (g := g i)).mp <| by
        rw [show Sigma.mk i ∘ g i = F.symm ∘ Sigma.mk i from funext (hg i)]
        exact F.symm.contMDiff.comp (TauCeti.contMDiff_sigmaMk i) },
    Diffeomorph.ext fun ⟨i, x⟩ ↦ hf i x⟩

/-- **Componentwise action as a group homomorphism.** The self-diffeomorphisms of the components
act on their disjoint union, the family `e` acting by `sigmaCongrRight e`. -/
def sigmaCongrRightHom : (∀ i, M i ≃ₘ^n⟮I, I⟯ M i) →* (Σ i, M i) ≃ₘ^n⟮I, I⟯ Σ i, M i where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_refl
  map_mul' _ _ := Diffeomorph.ext fun _ ↦ rfl

/-- The homomorphism `sigmaCongrRightHom` sends a family to its componentwise diffeomorphism. -/
@[simp]
theorem sigmaCongrRightHom_apply (e : ∀ i, M i ≃ₘ^n⟮I, I⟯ M i) :
    sigmaCongrRightHom e = sigmaCongrRight e :=
  (rfl)

end Diffeomorph
