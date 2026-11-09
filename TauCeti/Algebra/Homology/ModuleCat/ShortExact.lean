/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Connecting maps of short exact sequences of complexes of modules

For maps `φ : X ⟶ Y` and `ψ : Y ⟶ Z` of complexes of modules with `ψ` a monomorphism, the short
exact sequence `cokernel φ ⟶ cokernel (φ ≫ ψ) ⟶ cokernel ψ`
(`TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact`) has a connecting map on homology.
This file computes it on classes of elements.

## Main statements

* `TauCeti.exists_δ_kernelCokernelSequence_L₃_eq`: the connecting map sends the class of a cycle
  `x` of `cokernel ψ`, lifted to an element `s` of `Z` whose differential is the image of an element
  `t` of `Y`, to the class of the image of `t` in `cokernel φ`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe w

/-- **The connecting map of the cokernel sequence of a composite, on classes.** Let `φ : X ⟶ Y` and
`ψ : Y ⟶ Z` be maps of complexes of modules, `ψ` a monomorphism, `s` an element of `Z` in degree
`n` and `t` an element of `Y` in degree `n + 1` with `ψ t = d s`, such that the image of `s` in
`cokernel ψ` is a cycle `x`. Then the image of `t` in `cokernel φ` is a cycle, and it represents
the image of the class of `x` under the connecting map of
`cokernel φ ⟶ cokernel (φ ≫ ψ) ⟶ cokernel ψ`. -/
theorem exists_δ_kernelCokernelSequence_L₃_eq {R : Type*} [Ring R]
    {X Y Z : CochainComplex (ModuleCat.{w} R) ℤ} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [Mono ψ] (n : ℤ)
    (s : Z.X n) (t : Y.X (n + 1)) (hst : (ψ.f (n + 1)).hom t = (Z.d n (n + 1)).hom s)
    (x : (cokernel ψ).X n) (hx : ((cokernel ψ).d n (n + 1)).hom x = 0)
    (hsx : ((cokernel.π ψ).f n).hom s = x) :
    ∃ hc : ((cokernel φ).d (n + 1) (n + 1 + 1)).hom (((cokernel.π φ).f (n + 1)).hom t) = 0,
      ((kernelCokernelCompSequence_snakeInput_L₃_shortExact φ ψ).δ n (n + 1) rfl).hom
          (((cokernel ψ).homologyπ n).hom ((cokernel ψ).moduleCatCyclesMk x (n + 1) (by simp) hx)) =
        ((cokernel φ).homologyπ (n + 1)).hom ((cokernel φ).moduleCatCyclesMk
          (((cokernel.π φ).f (n + 1)).hom t) (n + 1 + 1) (by simp) hc) := by
  have hS := kernelCokernelCompSequence_snakeInput_L₃_shortExact φ ψ
  have hLg : cokernel.π (φ ≫ ψ) ≫ (kernelCokernelCompSequence.snakeInput φ ψ).L₃.g =
      cokernel.π ψ := by
    simp [kernelCokernelCompSequence.snakeInput]
  have hLf : cokernel.π φ ≫ (kernelCokernelCompSequence.snakeInput φ ψ).L₃.f =
      ψ ≫ cokernel.π (φ ≫ ψ) := by
    simp [kernelCokernelCompSequence.snakeInput]
  have hx₂ : (((kernelCokernelCompSequence.snakeInput φ ψ).L₃.g.f n).hom
      (((cokernel.π (φ ≫ ψ)).f n).hom s)) = x :=
    (congrArg (fun ξ ↦ (ξ.f n).hom s) hLg).trans hsx
  have hz₁ : (((kernelCokernelCompSequence.snakeInput φ ψ).L₃.f.f (n + 1)).hom
      (((cokernel.π φ).f (n + 1)).hom t)) =
      ((cokernel (φ ≫ ψ)).d n (n + 1)).hom (((cokernel.π (φ ≫ ψ)).f n).hom s) := by
    refine (congrArg (fun ξ ↦ (ξ.f (n + 1)).hom t) hLf).trans ?_
    -- `ψ ≫ cokernel.π` applied to `t`, written as a composite of elements.
    change ((cokernel.π (φ ≫ ψ)).f (n + 1)).hom (((ψ).f (n + 1)).hom t) = _
    rw [hst]
    exact (HomologicalComplex.Hom.comm_apply _ _ _ _).symm
  have hcyc : ((cokernel φ).d (n + 1) (n + 1 + 1)).hom (((cokernel.π φ).f (n + 1)).hom t) = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply n (n + 1) _ _ hz₁ _
  exact ⟨hcyc, hS.moduleCat_δ_homologyπ n (n + 1) rfl
    ((cokernel ψ).moduleCatCyclesMk x (n + 1) (by simp) hx)
    (((cokernel.π (φ ≫ ψ)).f n).hom s)
    (hx₂.trans (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm)
    ((cokernel φ).moduleCatCyclesMk (((cokernel.π φ).f (n + 1)).hom t) (n + 1 + 1) (by simp) hcyc)
    ((congrArg _ (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _)).trans hz₁)⟩

end TauCeti
