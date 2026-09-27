/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Extension of scalars for the Lipschitz group

Extension of scalars sends each invertible Clifford generator to the corresponding pure tensor,
so it induces a homomorphism of Lipschitz groups. The twisted-conjugation action commutes with
this homomorphism: on a pure tensor, the extended element acts by extending the original action.
Consequently the resulting map to the orthogonal group agrees with scalar extension of orthogonal
automorphisms.

## Main results

* `CliffordAlgebra.lipschitzGroupBaseChange` extends a Lipschitz element's scalars.
* `CliffordAlgebra.lipschitzVectorAction_baseChange_tmul` computes the extended action on pure
  tensors.
* `CliffordAlgebra.lipschitzToOrthogonal_baseChange` gives the commuting square with extension of
  orthogonal automorphisms.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]
variable (Q : QuadraticForm R M)

private theorem ofBaseChangeAux_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ lipschitzGroup Q) :
    Units.map (ofBaseChangeAux A Q).toMonoidHom x ∈ lipschitzGroup (Q.baseChange A) := by
  induction hx using Subgroup.closure_induction with
  | mem x hgen =>
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hgen
      -- Expose the generating set of the closure in order to provide the scalar-extended vector.
      change ↑(Units.map (ofBaseChangeAux A Q).toMonoidHom x) ∈
        Set.range (ι (Q.baseChange A))
      refine ⟨1 ⊗ₜ m, ?_⟩
      change ι (Q.baseChange A) (1 ⊗ₜ m) = ofBaseChangeAux A Q (x : CliffordAlgebra Q)
      rw [← hm, ofBaseChangeAux_ι]
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

/-- The homomorphism of Lipschitz groups induced by extension of scalars. -/
def lipschitzGroupBaseChange : lipschitzGroup Q →* lipschitzGroup (Q.baseChange A) where
  toFun x := ⟨Units.map (ofBaseChangeAux A Q).toMonoidHom x.1,
    ofBaseChangeAux_mem_lipschitzGroup Q x.2⟩
  map_one' := by simp
  map_mul' x y := by simp

/-- The Clifford value of a scalar-extended Lipschitz element is obtained from the canonical
Clifford map. -/
@[simp]
theorem coe_lipschitzGroupBaseChange_apply (x : lipschitzGroup Q) :
    (((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
      (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) := by
  rw [lipschitzGroupBaseChange]
  -- Expose the underlying unit map after removing the codomain restriction.
  change ↑(Units.map (ofBaseChangeAux A Q).toMonoidHom
    (x : (CliffordAlgebra Q)ˣ)) =
      ofBaseChangeAux A Q (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  exact Units.coe_map (ofBaseChangeAux A Q).toMonoidHom (x : (CliffordAlgebra Q)ˣ)

private theorem lipschitzGroupBaseChange_inv_coe (x : lipschitzGroup Q) :
    ofBaseChangeAux A Q
        ((((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      ((((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
          (CliffordAlgebra (Q.baseChange A))ˣ)⁻¹ :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) := by
  calc
    _ = (((lipschitzGroupBaseChange (A := A) Q (x⁻¹) :
        lipschitzGroup (Q.baseChange A)) : (CliffordAlgebra (Q.baseChange A))ˣ) :
          CliffordAlgebra (Q.baseChange A)) :=
      (coe_lipschitzGroupBaseChange_apply (A := A) Q (x⁻¹)).symm
    _ = _ := by simp

/-- On a pure tensor, the scalar-extended Lipschitz action is the extension of the original
action. -/
@[simp]
theorem lipschitzVectorAction_baseChange_tmul [Invertible (2 : A)]
    (x : lipschitzGroup Q) (a : A) (m : M) :
    lipschitzVectorAction (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x) (a ⊗ₜ m) =
      a ⊗ₜ lipschitzVectorAction Q x m := by
  suffices hOne :
      lipschitzVectorAction (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x)
          (1 ⊗ₜ m) =
        1 ⊗ₜ lipschitzVectorAction Q x m by
    have ha (n : M) : a ⊗ₜ[R] n = a • (1 ⊗ₜ[R] n) := by
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' a (1 : A) n).symm
    rw [ha, map_smul, hOne, ← ha]
  apply ι_injective (Q.baseChange A)
  have hinv :
      ((((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
          (CliffordAlgebra (Q.baseChange A))ˣ)⁻¹ :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
        ofBaseChangeAux A Q
          ((((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
            CliffordAlgebra Q)) :=
    (lipschitzGroupBaseChange_inv_coe (A := A) Q x).symm
  rw [ι_lipschitzVectorAction_apply, coe_lipschitzGroupBaseChange_apply,
    ← ofBaseChangeAux_involute, hinv, ← ofBaseChangeAux_ι A Q m,
    ← map_mul, ← map_mul, ← ι_lipschitzVectorAction_apply, ofBaseChangeAux_ι]

/-- Extension of scalars commutes with the Lipschitz homomorphism to the orthogonal group. -/
@[simp]
theorem lipschitzToOrthogonal_baseChange [Invertible (2 : A)] (x : lipschitzGroup Q) :
    TauCeti.QuadraticMap.orthogonalGroupBaseChange (A := A) Q (lipschitzToOrthogonal Q x) =
      lipschitzToOrthogonal (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [TauCeti.QuadraticMap.orthogonalGroupBaseChange_apply_tmul,
        coe_lipschitzToOrthogonal_apply, coe_lipschitzToOrthogonal_apply,
        lipschitzVectorAction_baseChange_tmul]
  | add z w hz hw =>
      simp only [map_add, hz, hw]

end CliffordAlgebra
