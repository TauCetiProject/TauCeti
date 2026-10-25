/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Simple comodules and the convolution action

Over a field, stability under every contraction of a coaction is equivalent to being
a subcomodule. Consequently a simple comodule is irreducible as a representation of
the multiplicative monoid of the convolution dual. Over an algebraically closed field,
Burnside's theorem then makes the convolution action surjective onto all endomorphisms
of a finite-dimensional simple comodule.

This uses the full linear dual of the coalgebra, rather than only rational points of
an affine group. It applies to arbitrary coalgebras and includes nonreduced group schemes.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* The density step uses `Representation.asAlgebraHom_surjective_of_isIrreducible`.
-/

public section

open scoped TensorProduct

namespace Submodule

open TauCeti

variable {k C M : Type*} [Field k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]

/-- A subspace stable under every contraction of the coaction is a subcomodule. -/
theorem coact_mem_range_of_forall_coactComponent_mem (W : Submodule k M)
    (hW : ∀ (f : Module.Dual k C) {m : M}, m ∈ W →
      Comodule.coactComponent (R := k) (C := C) f m ∈ W)
    {m : M} (hm : m ∈ W) :
    Comodule.coact (R := k) (C := C) m ∈
      LinearMap.range (TensorProduct.map W.subtype (LinearMap.id : C →ₗ[k] C)) := by
  rw [W.coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
  intro ψ
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro f
  rw [LinearMap.apply_matrixCoefficient, LinearMap.comp_apply, W.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero W).mpr (hW f hm), map_zero]

end Submodule

namespace TauCeti.Comodule

variable {k C M : Type*} [Field k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]

/-- A simple comodule is irreducible under the multiplicative monoid of its convolution dual. -/
theorem isIrreducible_convolutionAction [IsSimpleOrder (Subcomodule k C M)] :
    Representation.IsIrreducible
      (convolutionAction (R := k) (C := C) (M := M)).toMonoidHom := by
  have : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with h | h
    · have hbt : (⊥ : Subcomodule k C M) = ⊤ := by
        ext m
        simp [Subsingleton.elim m (0 : M)]
      exact False.elim (bot_ne_top hbt)
    · exact h
  refine ⟨fun S ↦ ?_⟩
  let W : Subcomodule k C M := Subcomodule.ofSubmodule S.toSubmodule
    (fun _ hm ↦ S.toSubmodule.coact_mem_range_of_forall_coactComponent_mem
      (fun f x hx ↦ by
        have hfx : convolutionAction (R := k) (C := C) (M := M)
            (WithConv.toConv f) x ∈ S.toSubmodule :=
          S.apply_mem_toSubmodule (WithConv.toConv f) hx
        simpa only [convolutionAction_apply, WithConv.ofConv_toConv,
          ← coactComponent_apply] using hfx) hm)
  have hW : W.toSubmodule = S.toSubmodule := rfl
  rcases eq_bot_or_eq_top W with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    simpa only [hW, Subcomodule.bot_toSubmodule, Subrepresentation.toSubmodule_bot] using
      congrArg Subcomodule.toSubmodule h
  · right
    apply Subrepresentation.toSubmodule_injective
    simpa only [hW, Subcomodule.top_toSubmodule, Subrepresentation.toSubmodule_top] using
      congrArg Subcomodule.toSubmodule h

/-- Over an algebraically closed field, the convolution dual acts as every endomorphism
on a finite-dimensional simple comodule. -/
theorem convolutionAction_surjective [IsAlgClosed k] [Module.Finite k M]
    [IsSimpleOrder (Subcomodule k C M)] :
    Function.Surjective (convolutionAction (R := k) (C := C) (M := M)) := by
  let ρ : Representation k (WithConv (Module.Dual k C)) M :=
    (convolutionAction (R := k) (C := C) (M := M)).toMonoidHom
  intro T
  obtain ⟨a, ha⟩ := ρ.asAlgebraHom_surjective_of_isIrreducible
    isIrreducible_convolutionAction T
  have hfactor : ρ.asAlgebraHom =
      (convolutionAction (R := k) (C := C) (M := M)).comp
        (MonoidAlgebra.lift k (WithConv (Module.Dual k C))
          (WithConv (Module.Dual k C)) (MonoidHom.id _)) := by
    ext f
    simp [ρ]
  rw [hfactor, AlgHom.comp_apply] at ha
  exact ⟨_, ha⟩

end TauCeti.Comodule
