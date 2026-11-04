/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
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
* `Diffeomorph.sigmaFiber`: restriction of an index-preserving diffeomorphism to a fibre.
  Reassembling the restrictions by `sigmaCongrRight` recovers the original diffeomorphism.

## Main results

* `TauCeti.isLocalDiffeomorph_sigmaMk`: the inclusion of a component into a disjoint union is a
  local diffeomorphism.
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

/-- Restriction to a fibre of a diffeomorphism of a disjoint union which fixes the index.
No connectedness assumption on the fibres is required. -/
def sigmaFiber (e : (Σ i, M i) ≃ₘ^n⟮I, J⟯ Σ i, M' i)
    (h : ∀ x, (e x).1 = x.1) (i : ι) : M i ≃ₘ^n⟮I, J⟯ M' i where
  toEquiv := (Equiv.sigmaSubtype i).symm.trans
    ((e.toEquiv.subtypeEquiv fun x ↦ (congrArg (· = i) (h x)).symm.to_iff).trans
      (Equiv.sigmaSubtype i))
  contMDiff_toFun := by
    apply TauCeti.contMDiff_sigmaMk_iff.mp
    convert e.contMDiff.comp (TauCeti.contMDiff_sigmaMk i) using 1
    funext x
    exact (Equiv.sigmaSubtype i).symm_apply_apply ⟨e ⟨i, x⟩, h ⟨i, x⟩⟩ |> congrArg Subtype.val
  contMDiff_invFun := by
    apply TauCeti.contMDiff_sigmaMk_iff.mp
    convert e.symm.contMDiff.comp (TauCeti.contMDiff_sigmaMk i) using 1
    funext x
    exact (Equiv.sigmaSubtype i).symm_apply_apply
      ⟨e.symm ⟨i, x⟩, (h (e.symm ⟨i, x⟩)).symm.trans (congrArg Sigma.fst
        (e.apply_symm_apply ⟨i, x⟩))⟩ |> congrArg Subtype.val

/-- Including a restricted diffeomorphism into the disjoint union recovers the original map. -/
@[simp]
theorem mk_sigmaFiber_apply (e : (Σ i, M i) ≃ₘ^n⟮I, J⟯ Σ i, M' i)
    (h : ∀ x, (e x).1 = x.1) (i : ι) (x : M i) :
    (⟨i, e.sigmaFiber h i x⟩ : Σ i, M' i) = e ⟨i, x⟩ :=
  congrArg Subtype.val ((Equiv.sigmaSubtype i).symm_apply_apply ⟨e ⟨i, x⟩, h ⟨i, x⟩⟩)

/-- Reassembling all the fibre restrictions recovers the diffeomorphism of disjoint unions. -/
@[simp]
theorem sigmaCongrRight_sigmaFiber (e : (Σ i, M i) ≃ₘ^n⟮I, J⟯ Σ i, M' i)
    (h : ∀ x, (e x).1 = x.1) : sigmaCongrRight (e.sigmaFiber h) = e :=
  Diffeomorph.ext fun ⟨i, x⟩ ↦ mk_sigmaFiber_apply e h i x

/-- The inclusion of a component into a disjoint union is a `C^n` local diffeomorphism: it is a
diffeomorphism onto the open copy of the component, with inverse the second projection. -/
theorem _root_.TauCeti.isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ i, M i) := by
  intro x
  have : Nonempty (M i) := ⟨x⟩
  have hσ : Topology.IsOpenEmbedding (Sigma.mk i : M i → Σ i, M i) := .sigmaMk
  let Φ : PartialDiffeomorph I I (M i) (Σ i, M i) n :=
    { toPartialEquiv := (hσ.toOpenPartialHomeomorph _).toPartialEquiv
      open_source := (hσ.toOpenPartialHomeomorph _).open_source
      open_target := (hσ.toOpenPartialHomeomorph _).open_target
      contMDiffOn_toFun := by
        simpa using (TauCeti.contMDiff_sigmaMk (I := I) (n := n) i).contMDiffOn
      contMDiffOn_invFun := by
        rintro _ ⟨y, -, rfl⟩
        refine (TauCeti.contMDiffAt_sigma_iff.2
          (contMDiffAt_id.congr_of_eventuallyEq ?_)).contMDiffWithinAt
        exact Filter.Eventually.of_forall fun z ↦ hσ.toOpenPartialHomeomorph_left_inv }
  exact Φ.isLocalDiffeomorphAt I I n (Set.mem_univ x)

end Diffeomorph
