/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma
public import TauCeti.Logic.Equiv.Sum

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
* `Diffeomorph.sumSigmaDistrib`: a disjoint union indexed by `ι₁ ⊕ ι₂` is the binary disjoint
  union of the parts indexed by `ι₁` and by `ι₂`, the smooth form of `Equiv.sumSigmaDistrib`.
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

section SumSigmaDistrib

variable {ι₁ ι₂ : Type*} {N : ι₁ ⊕ ι₂ → Type*} [∀ i, TopologicalSpace (N i)]
  [∀ i, ChartedSpace H (N i)]

variable (I n N) in
/-- **Splitting a disjoint union indexed by a sum.** The disjoint union of a family indexed by
`ι₁ ⊕ ι₂` is diffeomorphic to the binary disjoint union of its parts indexed by `ι₁` and by `ι₂`.
This is the smooth form of `Equiv.sumSigmaDistrib`. -/
def sumSigmaDistrib : (Σ i, N i) ≃ₘ^n⟮I, I⟯ (Σ i, N (.inl i)) ⊕ (Σ i, N (.inr i)) where
  toEquiv := Equiv.sumSigmaDistrib N
  contMDiff_toFun := TauCeti.contMDiff_sigma_iff.mpr fun
    | .inl i => ContMDiff.inl.comp (TauCeti.contMDiff_sigmaMk (M := fun i ↦ N (.inl i)) i)
    | .inr i => ContMDiff.inr.comp (TauCeti.contMDiff_sigmaMk (M := fun i ↦ N (.inr i)) i)
  contMDiff_invFun := by
    convert (ContMDiff.sigmaMap (f := Sum.inl) (g := fun _ ↦ id) fun _ ↦ contMDiff_id).sumElim
      (ContMDiff.sigmaMap (f := Sum.inr) (g := fun _ ↦ id) fun _ ↦ contMDiff_id) using 1
    funext x
    rcases x with ⟨i, x⟩ | ⟨i, x⟩ <;> simp [Sigma.map]

/-- The underlying equivalence of the splitting is `Equiv.sumSigmaDistrib`. -/
@[simp]
theorem sumSigmaDistrib_toEquiv : (sumSigmaDistrib I n N).toEquiv = Equiv.sumSigmaDistrib N :=
  (rfl)

/-- Splitting sends a point of a component indexed by `ι₁` to the first summand. -/
@[simp]
theorem sumSigmaDistrib_apply_inl (i : ι₁) (x : N (.inl i)) :
    sumSigmaDistrib I n N ⟨.inl i, x⟩ = .inl ⟨i, x⟩ := by
  rw [← coe_toEquiv, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_apply]

/-- Splitting sends a point of a component indexed by `ι₂` to the second summand. -/
@[simp]
theorem sumSigmaDistrib_apply_inr (i : ι₂) (x : N (.inr i)) :
    sumSigmaDistrib I n N ⟨.inr i, x⟩ = .inr ⟨i, x⟩ := by
  rw [← coe_toEquiv, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_apply]

/-- Splitting sends the part indexed by `ι₁`, included along `Sum.inl`, to the first summand. -/
@[simp]
theorem sumSigmaDistrib_apply_sigmaMap_inl (x : Σ i, N (.inl i)) :
    sumSigmaDistrib I n N (Sigma.map Sum.inl (fun _ ↦ id) x) = .inl x := by
  rw [← coe_toEquiv, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_apply_sigmaMap_inl]

/-- Splitting sends the part indexed by `ι₂`, included along `Sum.inr`, to the second summand. -/
@[simp]
theorem sumSigmaDistrib_apply_sigmaMap_inr (x : Σ i, N (.inr i)) :
    sumSigmaDistrib I n N (Sigma.map Sum.inr (fun _ ↦ id) x) = .inr x := by
  rw [← coe_toEquiv, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_apply_sigmaMap_inr]

/-- The inverse of splitting includes the first summand along `Sum.inl`. -/
@[simp]
theorem sumSigmaDistrib_symm_apply_inl (x : Σ i, N (.inl i)) :
    (sumSigmaDistrib I n N).symm (.inl x) = Sigma.map Sum.inl (fun _ ↦ id) x := by
  rw [← toEquiv_coe_symm, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_symm_apply,
    Sum.elim_inl, Sigma.map, id]

/-- The inverse of splitting includes the second summand along `Sum.inr`. -/
@[simp]
theorem sumSigmaDistrib_symm_apply_inr (x : Σ i, N (.inr i)) :
    (sumSigmaDistrib I n N).symm (.inr x) = Sigma.map Sum.inr (fun _ ↦ id) x := by
  rw [← toEquiv_coe_symm, sumSigmaDistrib_toEquiv, Equiv.sumSigmaDistrib_symm_apply,
    Sum.elim_inr, Sigma.map, id]

end SumSigmaDistrib

end Diffeomorph
