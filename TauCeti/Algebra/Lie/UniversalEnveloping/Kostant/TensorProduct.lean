/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Bilinear
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Comultiplication
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Orbit
public import TauCeti.Algebra.Lie.UniversalEnveloping.TensorProduct

/-!
# Tensor products of Kostant-stable lattices

If integral submodules `M` and `N` of rational Lie modules are stable under a Kostant form,
the integral span of their pure tensors is stable under the diagonal action. We use native
`Submodule.map₂` for this tensor lattice, not a second lattice structure. Stability follows
from the integral coproduct, whose coefficients are integral before acting on either factor.

Consequently the Kostant orbit of a tensor of lattice vectors lies in this tensor lattice.
When the factor lattices are finitely generated, that orbit is finitely generated too.
In particular, this bounds the integral orbit of a highest tensor in a tensor product of
admissible modules; neither the entire tensor product nor its highest cyclic summand is
asserted irreducible.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The coproduct action is `TauCeti.BialgebraModule.tensorAction`; its identification with the
diagonal Lie action is `TauCeti.UniversalEnvelopingAlgebra.tensorAction_eq_representation`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L V W : Type*} [LieRing L] [LieAlgebra ℚ L]
  [AddCommGroup V] [Module ℚ V] [LieRingModule L V] [LieModule ℚ L V]
  [AddCommGroup W] [Module ℚ W] [LieRingModule L W] [LieModule ℚ L W]
  {I J : Type*}

attribute [local instance] asModule isScalarTower_asModule

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

/-- The tensor lattice of two Kostant-stable integral submodules is stable under the diagonal
Lie representation. No finite generation, freeness or nilpotence assumption is required. -/
theorem representation_tensor_mem_map₂ (e : I → L) (h : J → L)
    (M : Submodule ℤ V) (N : Submodule ℤ W)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, representation ℚ L V u v ∈ M)
    (hN : ∀ u ∈ kostantForm e h, ∀ w ∈ N, representation ℚ L W u w ∈ N)
    {u : U} (hu : u ∈ kostantForm e h) {z : V ⊗[ℚ] W}
    (hz : z ∈ Submodule.map₂ ((TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ) M N) :
    representation ℚ L (V ⊗[ℚ] W) u z ∈
      Submodule.map₂ ((TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ) M N := by
  let P := Submodule.map₂ ((TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ) M N
  have hpure (v : V) (hv : v ∈ M) (w : W) (hw : w ∈ N)
      (t : kostantForm e h ⊗[ℤ] kostantForm e h) :
      BialgebraModule.tensorPairAction ℚ V W (kostantTensorMap e h t)
        (v ⊗ₜ[ℚ] w) ∈ P := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [kostantTensorMap_tmul, BialgebraModule.tensorPairAction_tmul,
        asModule_smul_def, asModule_smul_def]
      exact Submodule.apply_mem_map₂ _ (hM a a.property v hv) (hN b b.property w hw)
    | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply] using P.add_mem ha hb
  rw [← tensorAction_eq_representation]
  rw [Submodule.map₂_eq_span_image2] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, hv, w, hw, rfl⟩ := hz
    rw [BialgebraModule.tensorAction_apply,
      ← kostantTensorMap_kostantFormComul_apply e h ⟨u, hu⟩]
    exact hpure v hv w hw _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using P.add_mem ha hb
  | smul n z _ hz => simpa only [map_zsmul] using P.smul_mem n hz

/-- The integral orbit of a tensor of lattice vectors is contained in the tensor lattice. -/
theorem kostantOrbit_tmul_le_map₂ (e : I → L) (h : J → L)
    (M : Submodule ℤ V) (N : Submodule ℤ W)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, representation ℚ L V u v ∈ M)
    (hN : ∀ u ∈ kostantForm e h, ∀ w ∈ N, representation ℚ L W u w ∈ N)
    {v : V} (hv : v ∈ M) {w : W} (hw : w ∈ N) :
    kostantOrbit e h (v ⊗ₜ[ℚ] w) ≤
      Submodule.map₂ ((TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ) M N := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := mem_kostantOrbit_iff.mp hz
  rw [asModule_smul_def]
  exact representation_tensor_mem_map₂ e h M N hM hN hu
    (Submodule.apply_mem_map₂ _ hv hw)

/-- The orbit of a tensor of vectors in finitely generated Kostant-stable integral submodules
is finitely generated over the integers. This includes the orbit of a highest tensor. -/
theorem fg_kostantOrbit_tmul (e : I → L) (h : J → L)
    (M : Submodule ℤ V) (N : Submodule ℤ W) (hfgM : M.FG) (hfgN : N.FG)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, representation ℚ L V u v ∈ M)
    (hN : ∀ u ∈ kostantForm e h, ∀ w ∈ N, representation ℚ L W u w ∈ N)
    {v : V} (hv : v ∈ M) {w : W} (hw : w ∈ N) :
    (kostantOrbit e h (v ⊗ₜ[ℚ] w)).FG :=
  (hfgM.map₂ ((TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ) hfgN).of_le
    (kostantOrbit_tmul_le_map₂ e h M N hM hN hv hw)

end TauCeti.UniversalEnvelopingAlgebra
