/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm.Differential
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.Coalgebra.Comodule.Product
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Lie.Sl2.Decomposition

/-!
# Integrating finite-dimensional `sl₂`-modules to rational `SL₂`-representations

Every finite-dimensional `sl (Fin 2) k`-module over a characteristic-zero field `k` integrates to a
unique rational `SL₂`-representation (`comoduleOfLieModule`, `existsUnique_comodule_of_lieModule`),
functorially in Lie-module homomorphisms (`comoduleHomOfLieModuleHom`) and preserving invariant
subspaces (`exists_subcomodule_comoduleOfLieModule_iff`), without assuming algebraic closure of `k`
or restricting the module universe. Downstream, `Sl2Triple/Basic.lean` uses this to integrate `sl₂`
triples to `SL₂ ⟶ G`; `comoduleOfLieModule` is a `def` (installed locally via `letI`) rather than a
global `instance` to avoid comodule diamonds on a single `k`-vector space.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; J. S. Milne, *Algebraic Groups*, §12, §22.
-/

public section

open LieAlgebra
open scoped DirectSum TensorProduct

namespace TauCeti.SpecialLinear

universe u w w'

attribute [local instance] polynomialComodule

/-- **Existence and uniqueness of rational `SL₂`-integration.** Every finite-dimensional
`sl (Fin 2) k`-module over a characteristic-zero field carries a unique `O(SL₂)`-comodule structure
whose differential agrees with the Lie-module action across `tangentLieEquivSl 2`. -/
theorem existsUnique_comodule_of_lieModule (k : Type u) [Field k] [CharZero k] (M : Type w)
    [AddCommGroup M] [Module k M] [Module.Finite k M] [LieRingModule (SpecialLinear.sl (Fin 2) k) M]
    [LieModule k (SpecialLinear.sl (Fin 2) k) M] :
    ∃! c : Comodule k (coordinateHopfAlgebra k 2) M,
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M),
        @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ c d m =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ := by
  obtain ⟨r, N, n, hint, hequiv⟩ := Sl2Std.exists_isInternal_lieModuleEquiv k M
  let φ (i : Fin r) : N i ≃ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ Sl2Std k (n i) := (hequiv i).some
  let eSummand (i : Fin r) := (binaryFormsEquivSl2Std k (n i)).trans (φ i).symm.toLinearEquiv
  let eSum : (∀ i : Fin r, (N i).toSubmodule) ≃ₗ[k] M :=
    (DirectSum.linearEquivFunOnFintype k (Fin r) (fun i ↦ (N i).toSubmodule)).symm.trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i ↦ (N i).toSubmodule) hint)
  have heSum (g : ∀ i, (N i).toSubmodule) : eSum g = ∑ i, (g i : M) := by
    conv_lhs => rw [← Finset.univ_sum_single g]
    simp only [eSum, map_sum, LinearEquiv.trans_apply,
      DirectSum.linearEquivFunOnFintype_symm_single]
    exact Finset.sum_congr rfl fun i _ ↦ DirectSum.coeLinearMap_of (fun j ↦ (N j).toSubmodule) i _
  let E := (LinearEquiv.piCongrRight eSummand).trans eSum
  let _ : Comodule k (coordinateHopfAlgebra k 2) (∀ i : Fin r, binaryForms k (n i)) :=
    Comodule.finPi (R := k) (C := coordinateHopfAlgebra k 2) r _ fun _ ↦ inferInstance
  let cM := Comodule.Transport (R := k) (C := coordinateHopfAlgebra k 2) E
  have hcM (d) (m : M) : @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ cM d m =
      ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ := by
    rw [Comodule.differential_transport E]; conv_rhs => rw [← E.apply_symm_apply m]
    simp only [E, LinearEquiv.trans_apply, heSum, LinearEquiv.piCongrRight_apply, lie_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [eSummand, LinearEquiv.trans_apply, LieModuleEquiv.coe_toLinearEquiv]
    rw [Comodule.differential_finPi, binaryFormsEquivSl2Std_differential]
    exact congrArg Subtype.val ((φ i).symm.toLieModuleHom.map_lie _ _)
  exact ⟨cM, hcM, fun c' hc' ↦ Comodule.ext_of_differential_eq_of_geometricallyConnected
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2) fun d m ↦
      (hc' d m).trans (hcM d m).symm⟩

/-- **The canonical `O(SL₂)`-comodule integrating a finite-dimensional `sl (Fin 2) k`-module.** -/
@[implicit_reducible] noncomputable def comoduleOfLieModule (k : Type u) [Field k] [CharZero k]
    (M : Type w) [AddCommGroup M] [Module k M] [Module.Finite k M]
    [LieRingModule (SpecialLinear.sl (Fin 2) k) M] [LieModule k (SpecialLinear.sl (Fin 2) k) M] :
    Comodule k (coordinateHopfAlgebra k 2) M :=
  (existsUnique_comodule_of_lieModule k M).choose

variable {k : Type u} [Field k] [CharZero k] {M : Type w} [AddCommGroup M] [Module k M]
  [Module.Finite k M] [LieRingModule (SpecialLinear.sl (Fin 2) k) M]
  [LieModule k (SpecialLinear.sl (Fin 2) k) M] {N : Type w'} [AddCommGroup N] [Module k N]
  [Module.Finite k N] [LieRingModule (SpecialLinear.sl (Fin 2) k) N]
  [LieModule k (SpecialLinear.sl (Fin 2) k) N]

/-- The differential of `comoduleOfLieModule` agrees with `sl (Fin 2) k` via `tangentLieEquivSl`. -/
theorem differential_comoduleOfLieModule
    (d : Derivation k (coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M) :
    letI := comoduleOfLieModule k M
    Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2) d m =
      ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ :=
  (existsUnique_comodule_of_lieModule k M).choose_spec.1 d m

/-- Evaluating `Comodule.differential` for `comoduleOfLieModule` at `(tangentLieEquivSl 2).symm A`
recovers `⁅A, m⁆`. -/
theorem differential_comoduleOfLieModule_symm (A : SpecialLinear.sl (Fin 2) k) (m : M) :
    letI := comoduleOfLieModule k M
    Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2)
        ((tangentLieEquivSl (R := k) (B := k) 2).symm A) m = ⁅A, m⁆ := by
  let _ := comoduleOfLieModule k M
  rw [differential_comoduleOfLieModule, LieEquiv.apply_symm_apply]

/-- Uniqueness characterization of `comoduleOfLieModule k M` by its differential. -/
theorem eq_comoduleOfLieModule_iff (c : Comodule k (coordinateHopfAlgebra k 2) M) :
    c = comoduleOfLieModule k M ↔
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M),
        @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ c d m =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ :=
  ⟨fun h ↦ h ▸ differential_comoduleOfLieModule,
    (existsUnique_comodule_of_lieModule k M).choose_spec.2 c⟩

/-- **Functoriality of `SL₂`-integration.** Every `sl (Fin 2) k`-module homomorphism between
finite-dimensional `sl (Fin 2) k`-modules is a morphism of `O(SL₂)`-comodules. -/
noncomputable def comoduleHomOfLieModuleHom (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) :
    letI := comoduleOfLieModule k M; letI := comoduleOfLieModule k N
    Comodule.Hom k (coordinateHopfAlgebra k 2) M N :=
  letI := comoduleOfLieModule k M; letI := comoduleOfLieModule k N
  ⟨f.toLinearMap, (f.toLinearMap.map_coact_iff_map_differential_of_geometricallyConnected
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)).mpr fun d m ↦ by
      rw [differential_comoduleOfLieModule, differential_comoduleOfLieModule]; exact f.map_lie _ m⟩

@[simp] theorem comoduleHomOfLieModuleHom_toLinearMap (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) :
    letI := comoduleOfLieModule k M; letI := comoduleOfLieModule k N
    (comoduleHomOfLieModuleHom f).toLinearMap = f.toLinearMap := (rfl)

@[simp] theorem comoduleHomOfLieModuleHom_apply (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) (m : M) :
    letI := comoduleOfLieModule k M; letI := comoduleOfLieModule k N
    comoduleHomOfLieModuleHom f m = f m := (rfl)

/-- A `k`-submodule of `M` underlies an `O(SL₂)`-subcomodule for `comoduleOfLieModule k M` iff it is
`sl (Fin 2) k`-stable. -/
theorem exists_subcomodule_comoduleOfLieModule_iff (S : Submodule k M) :
    letI := comoduleOfLieModule k M
    (∃ W : Subcomodule k (coordinateHopfAlgebra k 2) M, W.toSubmodule = S) ↔
      ∀ (A : SpecialLinear.sl (Fin 2) k), ∀ m ∈ S, ⁅A, m⁆ ∈ S := by
  let _ := comoduleOfLieModule k M
  refine (S.exists_subcomodule_iff_forall_differential_mem_of_geometricallyConnected
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)).trans
    ⟨fun h A m hm ↦ ?_, fun h d m hm ↦ ?_⟩
  · rw [← differential_comoduleOfLieModule_symm A m]; exact h _ m hm
  · rw [differential_comoduleOfLieModule]; exact h _ m hm

end TauCeti.SpecialLinear
