/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.Algebra.Module.Projective.Trans

/-!
# Composition of Weil restrictions

For a tower `A → B → C` of finite projective algebras, restricting a finitely presented
`C`-algebra first to `B` and then to `A` gives the same algebra as restricting directly
to `A`. The comparison is fixed by its effect on points: apply the two point adjunctions
and cancel `C ⊗[B] (B ⊗[A] T)` to `C ⊗[A] T`. It is natural in the algebra being restricted.

The construction uses `WeilRestriction.homEquiv` and its naturality, together with Mathlib
tensor-product cancellation. Finiteness and projectivity of `C` over `A` follow by
transitivity; the comparison allows these instances to be supplied explicitly when needed.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, §1.5.3–1.5.4, p. 27.
* J. S. Milne, *Algebraic Groups*, version 2.00 (2015), §2, 2.40–2.41, p. 51.
-/

public noncomputable section

open Algebra TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra C D]
  [Module.Finite A B] [Module.Projective A B] [Module.Finite B C] [Module.Projective B C]
  [FinitePresentation C D]

private def compHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B (WeilRestriction B C D) →ₐ[A] T) ≃ (D →ₐ[C] C ⊗[A] T) :=
  (homEquiv A B (WeilRestriction B C D) T).trans <|
    (homEquiv B C D (B ⊗[A] T)).trans <|
      AlgEquiv.arrowCongr (AlgEquiv.refl : D ≃ₐ[C] D)
        (Algebra.TensorProduct.cancelBaseChange A B C C T)

variable {A B C D} {T T' : Type*} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']

private theorem compHomEquiv_comp (g : WeilRestriction A B (WeilRestriction B C D) →ₐ[A] T)
    (h : T →ₐ[A] T') :
    compHomEquiv A B C D T' (h.comp g) =
      (Algebra.TensorProduct.lTensor C h).comp (compHomEquiv A B C D T g) := by
  simp only [compHomEquiv, Equiv.trans_apply, homEquiv_comp]
  apply AlgHom.ext
  intro d
  simp only [AlgEquiv.arrowCongr_apply, AlgHom.comp_apply]
  exact LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
    A B C (M := C) h.toLinearMap).symm _

variable (A B C D)

/-- Restriction of scalars along a tower of finite projective algebras is the composite
of the two restrictions. Its effect on points is `homEquiv_compAlgEquiv`. The default
instances on the direct extension are obtained by transitivity. -/
def compAlgEquiv
    (hfin : Module.Finite A C := Module.Finite.trans B C)
    (hproj : Module.Projective A C := Module.Projective.trans B C) :
    WeilRestriction A B (WeilRestriction B C D) ≃ₐ[A] WeilRestriction A C D :=
  let f := (compHomEquiv A B C D _).symm (universalPoint A C D)
  let g := (homEquiv A C D _).symm
    (compHomEquiv A B C D _ (AlgHom.id A _))
  AlgEquiv.ofAlgHom f g
    ((homEquiv A C D _).injective <| by
      simp only [homEquiv_comp, g, Equiv.apply_symm_apply]
      rw [← compHomEquiv_comp]
      simp [f])
    ((compHomEquiv A B C D _).injective <| by
      simp only [compHomEquiv_comp, f, Equiv.apply_symm_apply]
      rw [← homEquiv_apply]
      simp only [g, Equiv.apply_symm_apply])

variable {A B C D} [Module.Finite A C] [Module.Projective A C]

private theorem compHomEquiv_compAlgEquiv :
    compHomEquiv A B C D _ (compAlgEquiv A B C D).toAlgHom = universalPoint A C D := by
  simp only [compAlgEquiv, AlgEquiv.toAlgHom_ofAlgHom, Equiv.apply_symm_apply]

/-- The point classified by precomposing with the composition isomorphism is obtained
by applying the two point adjunctions and cancelling the intermediate scalar extension. -/
theorem homEquiv_compAlgEquiv (g : WeilRestriction A C D →ₐ[A] T) :
    (Algebra.TensorProduct.cancelBaseChange A B C C T).toAlgHom.comp
      (homEquiv B C D (B ⊗[A] T)
        (homEquiv A B (WeilRestriction B C D) T
          (g.comp (compAlgEquiv A B C D).toAlgHom))) = homEquiv A C D T g := by
  have h := compHomEquiv_comp (B := B) (C := C) (D := D)
    (compAlgEquiv A B C D).toAlgHom g
  rw [compHomEquiv_compAlgEquiv, ← homEquiv_apply] at h
  exact h

/-- The inverse composition isomorphism classifies the point obtained from the two
point adjunctions by tensor-product cancellation. -/
theorem homEquiv_compAlgEquiv_symm
    (g : WeilRestriction A B (WeilRestriction B C D) →ₐ[A] T) :
    homEquiv A C D T (g.comp (compAlgEquiv A B C D).symm.toAlgHom) =
      (Algebra.TensorProduct.cancelBaseChange A B C C T).toAlgHom.comp
        (homEquiv B C D (B ⊗[A] T)
          (homEquiv A B (WeilRestriction B C D) T g)) := by
  simpa only [AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id] using
    (homEquiv_compAlgEquiv (B := B) (g.comp (compAlgEquiv A B C D).symm.toAlgHom)).symm

variable {E : Type*} [CommRing E] [Algebra C E] [FinitePresentation C E]

omit [Module.Finite A C] [Module.Projective A C] in
private theorem compHomEquiv_comp_map (φ : D →ₐ[C] E)
    (g : WeilRestriction A B (WeilRestriction B C E) →ₐ[A] T) :
    compHomEquiv A B C D T (g.comp (map A B (map B C φ))) =
      (compHomEquiv A B C E T g).comp φ := by
  simp only [compHomEquiv, Equiv.trans_apply, homEquiv_comp_map,
    AlgEquiv.arrowCongr_apply]
  rfl

/-- The composition isomorphism is natural in the finitely presented algebra being restricted. -/
theorem compAlgEquiv_naturality (φ : D →ₐ[C] E) :
    (compAlgEquiv A B C E).toAlgHom.comp (map A B (map B C φ)) =
      (map A C φ).comp (compAlgEquiv A B C D).toAlgHom := by
  apply (compHomEquiv A B C D _).injective
  rw [compHomEquiv_comp_map, compHomEquiv_compAlgEquiv, compHomEquiv_comp,
    compHomEquiv_compAlgEquiv, ← homEquiv_apply, homEquiv_map]

end TauCeti.Algebra.WeilRestriction
