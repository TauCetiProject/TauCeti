/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel
public import TauCeti.RingTheory.MatlisDuality.Basic

/-!
# Dual Hom cokernels and the Auslander–Reiten translate

For a map `f : P₁ →ₗ[A] P₀` between finite projective modules and a `k`-module `E`, write
`D = Hom_k(-, E)`. Then `D coker(Hom_A(P₀,N) → Hom_A(P₁,N))` is canonically
`Hom_A(N, D Tr(f))`, where `Tr(f)` is the transpose of `f`. The equivalence evaluates on elementary
maps `x ↦ φ(x) • n` and is contravariantly natural in the coefficient module `N`. For `E = k`,
`D Tr(f)` is the Auslander–Reiten translate. With `E` injective this is the lemma in Krause's proof
of Auslander's defect formula (`TauCeti/Algebra/Module/AuslanderReiten/DefectFormula.lean`).

This comparison supplies the ambient Hom space in Auslander–Reiten duality. For a
general projective presentation, its Hom cokernel need not be `Ext¹`: one must still
impose the cocycle condition, whose dual produces the quotient by maps through injectives.
The result here needs neither exactness nor minimality, and works over a commutative
ground ring without finite-dimensionality assumptions.

The construction uses `LinearMap.auslanderReitenTransposeTensorEquivCokernel` and the
universal property of `TauCeti.BalancedTensorProduct`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti

variable {k A P₀ P₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommMonoid P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {E : Type*} [AddCommGroup E] [Module k E]

private noncomputable def homCokernelDualToTranslate (f : P₁ →ₗ[A] P₀) :
    (((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E) →ₗ[k]
      (N →ₗ[A] MatlisDual k E (AuslanderReitenTranspose f)) where
  toFun u :=
    { toFun := fun n ↦ (MatlisDual.equivLinearMap k E _).symm (u.comp
        ((auslanderReitenTransposeTensorEquivCokernel f).toLinearMap.comp
          ((BalancedTensorProduct.mk k A).flip n)))
      map_add' := fun n n' ↦ by
        ext t
        simp
      map_smul' := fun a n ↦ by
        ext t
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.flip_apply,
          BalancedTensorProduct.mk_apply, MatlisDual.smul_apply, RingHom.id_apply,
          LinearEquiv.apply_symm_apply]
        rw [BalancedTensorProduct.balance] }
  map_add' := fun u v ↦ by ext n t; simp
  map_smul' := fun c u ↦ by ext n t; simp

private theorem homCokernelDualToTranslate_apply (f : P₁ →ₗ[A] P₀)
    (u : ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E)
    (n : N) (t : AuslanderReitenTranspose f) :
    MatlisDual.equivLinearMap k E _ (homCokernelDualToTranslate f u n) t = u
      (auslanderReitenTransposeTensorEquivCokernel f (BalancedTensorProduct.tmul k A t n)) := by
  simp [homCokernelDualToTranslate]

private theorem homCokernelDual_ext (f : P₁ →ₗ[A] P₀)
    {u v : ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E}
    (h : ∀ t n,
      u (auslanderReitenTransposeTensorEquivCokernel f (BalancedTensorProduct.tmul k A t n)) =
        v (auslanderReitenTransposeTensorEquivCokernel f
          (BalancedTensorProduct.tmul k A t n))) : u = v := by
  apply (LinearMap.cancel_right (auslanderReitenTransposeTensorEquivCokernel f).surjective).mp
  exact BalancedTensorProduct.hom_ext h

private noncomputable def translateToHomCokernelDual (f : P₁ →ₗ[A] P₀) :
    (N →ₗ[A] MatlisDual k E (AuslanderReitenTranspose f)) →ₗ[k]
      (((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E) where
  toFun g :=
    (BalancedTensorProduct.lift
      ((MatlisDual.equivLinearMap k E _).toLinearMap.comp (g.restrictScalars k)).flip
      (fun a t n ↦ by
        simpa only [LinearMap.flip_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.restrictScalars_apply, MatlisDual.smul_apply] using
          (LinearMap.congr_fun (congrArg (MatlisDual.equivLinearMap k E _) (g.map_smul a n))
            t).symm)).comp
      (auslanderReitenTransposeTensorEquivCokernel f).symm.toLinearMap
  map_add' := fun g h ↦ by
    apply homCokernelDual_ext f
    intro t n
    simp
  map_smul' := fun c g ↦ by
    apply homCokernelDual_ext f
    intro t n
    simp

private theorem translateToHomCokernelDual_apply (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] MatlisDual k E (AuslanderReitenTranspose f)) (t : AuslanderReitenTranspose f)
    (n : N) :
    translateToHomCokernelDual f g
      (auslanderReitenTransposeTensorEquivCokernel f (BalancedTensorProduct.tmul k A t n)) =
        MatlisDual.equivLinearMap k E _ (g n) t := by
  simp [translateToHomCokernelDual]

/-- The `E`-dual of the Hom cokernel of a map `f` between finite projectives is Hom into
`D Tr(f) = Hom_k(Tr(f), E)`, which is the Auslander–Reiten translate when `E = k`. This is an
ordinary Hom space, before the injective stable quotient occurring in AR duality. -/
noncomputable def auslanderReitenHomCokernelDualEquiv (f : P₁ →ₗ[A] P₀) :
    (((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E) ≃ₗ[k]
      (N →ₗ[A] MatlisDual k E (AuslanderReitenTranspose f)) :=
  LinearEquiv.ofLinearMap (homCokernelDualToTranslate f) (translateToHomCokernelDual f)
    (by
      ext g n t
      simp [homCokernelDualToTranslate_apply, translateToHomCokernelDual_apply])
    (by
      apply LinearMap.ext
      intro u
      apply homCokernelDual_ext f
      intro t n
      simp [translateToHomCokernelDual_apply, homCokernelDualToTranslate_apply])

/-- Evaluation at a transpose class and a vector is evaluation of the dual functional
on the class of the elementary map `x ↦ φ(x) • n`. -/
@[simp]
theorem auslanderReitenHomCokernelDualEquiv_apply_mk (f : P₁ →ₗ[A] P₀)
    (u : (((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E))
    (n : N) (φ : Module.Dual A P₁) :
    MatlisDual.equivLinearMap k E _ (auslanderReitenHomCokernelDualEquiv f u n)
        (AuslanderReitenTranspose.mk f φ) =
      u (Submodule.Quotient.mk
        (balancedDualTensorHom k A P₁ N (BalancedTensorProduct.tmul k A φ n))) := by
  simp [auslanderReitenHomCokernelDualEquiv, homCokernelDualToTranslate_apply]

/-- Inverse transport evaluates the elementary Hom-cokernel class by applying the map
into `D Tr(f)` to the vector and then to the transpose class. -/
@[simp]
theorem auslanderReitenHomCokernelDualEquiv_symm_mk (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] MatlisDual k E (AuslanderReitenTranspose f)) (φ : Module.Dual A P₁) (n : N) :
    (auslanderReitenHomCokernelDualEquiv f).symm g
      (Submodule.Quotient.mk
        (balancedDualTensorHom k A P₁ N (BalancedTensorProduct.tmul k A φ n))) =
      MatlisDual.equivLinearMap k E _ (g n) (AuslanderReitenTranspose.mk f φ) := by
  rw [← auslanderReitenTransposeTensorEquivCokernel_tmul]
  exact translateToHomCokernelDual_apply f g _ _

variable {N' : Type*} [AddCommGroup N'] [Module A N'] [Module k N']
  [IsScalarTower k A N']

/-- Dual postcomposition on the Hom cokernel corresponds to precomposition on Hom
into `D Tr(f)`. Thus the comparison is contravariantly natural in `N`. -/
@[simp]
theorem auslanderReitenHomCokernelDualEquiv_map (f : P₁ →ₗ[A] P₀) (g : N →ₗ[A] N')
    (u : (((P₁ →ₗ[A] N') ⧸ range (f.lcomp k N')) →ₗ[k] E)) :
    auslanderReitenHomCokernelDualEquiv f
      (u.comp (homCokernelMap k f g)) =
      (auslanderReitenHomCokernelDualEquiv f u).comp g := by
  ext n t
  obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective f t
  simp only [auslanderReitenHomCokernelDualEquiv_apply_mk, LinearMap.comp_apply,
    homCokernelMap_mk]
  congr 1
  congr 1
  ext x
  simp

end LinearMap
