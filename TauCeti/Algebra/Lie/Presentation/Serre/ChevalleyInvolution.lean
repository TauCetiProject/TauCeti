/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
public import TauCeti.Algebra.Lie.Presentation.Serre.Injective
public import TauCeti.Algebra.Lie.Presentation.Serre.Killing
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# The Chevalley involution of a Lie algebra with nondegenerate Killing form

Let `L` be a Lie algebra with nondegenerate Killing form over a field `K` of characteristic zero,
and `H` a splitting Cartan subalgebra. Serre's theorem (`TauCeti.serreLiftEquiv`) identifies `L`
with the Lie algebra presented by the Serre relations of the Cartan matrix of a base of the root
system of `H`. That presented algebra carries the Chevalley involution
`Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ` (`TauCeti.serreChevalleyInvolution`). Transported along
Serre's theorem, it is a Lie automorphism of `L` acting by `-1` on `H`, since the simple coroots
span `H`.

## Main results

* `LieSubalgebra.exists_lieEquiv_forall_mem_apply_eq_neg`: a Lie automorphism of `L` acting by
  `-1` on a splitting Cartan subalgebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §14.3 and §18.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **A Lie automorphism inverting a splitting Cartan subalgebra.** It is the Chevalley involution
`Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ` of the Serre presentation, transported along Serre's
theorem. -/
theorem _root_.LieSubalgebra.exists_lieEquiv_forall_mem_apply_eq_neg :
    ∃ ω : L ≃ₗ⁅K⁆ L, ∀ y ∈ H, ω y = -y := by
  classical
  have := finite_of_isKilling (R := K) (L := L)
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  obtain ⟨e, f, hS⟩ := TauCeti.exists_isSerreSystem_of_base b
  let E := TauCeti.serreLiftEquiv hS
  let ω : L ≃ₗ⁅K⁆ L :=
    (E.symm.trans (TauCeti.serreChevalleyInvolution K b.cartanMatrix.transpose)).trans E
  have hcoroot (i : b.support) :
      ω ((coroot ((i : H.root) : Weight K H L) : H) : L) =
        -((coroot ((i : H.root) : Weight K H L) : H) : L) := by
    simp only [ω, LieEquiv.trans_apply, E, TauCeti.serreLiftEquiv_symm_coroot,
      TauCeti.serreChevalleyInvolution_serreH, map_neg]
    rw [← TauCeti.serreLiftEquiv_symm_coroot hS i, LieEquiv.apply_symm_apply]
  refine ⟨ω, fun y hy ↦ ?_⟩
  suffices h : ∀ z : H, ω z = -(z : L) from h ⟨y, hy⟩
  intro z
  have htop : Submodule.span K ((rootSystem H).coroot '' b.support) = ⊤ :=
    b.span_coroot_support.trans RootPairing.IsRootSystem.span_coroot_eq_top
  have hmem : z ∈ Submodule.span K ((rootSystem H).coroot '' b.support) := htop ▸ trivial
  induction hmem using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    simpa [rootSystem_coroot_apply] using hcoroot ⟨i, hi⟩
  | zero => simp
  | add z w _ _ hz hw => simp [map_add, hz, hw, add_comm]
  | smul c z _ hz =>
    rw [SetLike.val_smul, map_smul, hz, smul_neg]

end TauCeti
