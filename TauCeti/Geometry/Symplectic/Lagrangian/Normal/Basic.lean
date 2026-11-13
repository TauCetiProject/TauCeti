/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.LinearAlgebra.BilinearForm.QuotientDual

/-!
# The normal quotient of a Lagrangian subspace

For a Lagrangian subspace `L` of a finite-dimensional symplectic vector space,
the symplectic form identifies `V ⧸ L` with `L*` by `[n] ↦ ω(·, n)|L`.
This identification is independent of any choice of complement and commutes with
symplectic linear equivalences. It is the fibrewise normal identification used
in the Lagrangian neighborhood theorem.

For the zero section of `V × V*`, the normal class of `(v, α)` corresponds to
`α`, with a positive sign for the convention `ω = -dλ`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 8.1.
-/

public noncomputable section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {L : Submodule ℝ V}

/-- The canonical identification of the normal quotient of a Lagrangian subspace
with its dual, sending `[n]` to `ω(·, n)|L`. -/
def IsLagrangian.normalEquivDual (hL : ω.IsLagrangian L) :
    (V ⧸ L) ≃ₗ[ℝ] Module.Dual ℝ L :=
  (Submodule.quotEquivOfEq _ _ ((le_antisymm (isIsotropic_iff_le.mp hL.isIsotropic)
    (isCoisotropic_iff_le.mp hL.isCoisotropic)).trans (orthogonal_def ω L))).trans
    (ω.toBilinForm.quotientOrthogonalEquivDual ω.nondegenerate L)

/-- Evaluation of the normal duality on a representative. -/
@[simp]
theorem IsLagrangian.normalEquivDual_mk_apply (hL : ω.IsLagrangian L) (n : V) (v : L) :
    hL.normalEquivDual (Submodule.Quotient.mk n) v = ω v n := by
  rw [normalEquivDual, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact ω.toBilinForm.quotientOrthogonalEquivDual_mk_apply ω.nondegenerate L n v

/-- The inverse normal duality is characterized by symplectic pairings. -/
theorem IsLagrangian.normalEquivDual_symm_apply_eq_mk_iff (hL : ω.IsLagrangian L)
    (α : Module.Dual ℝ L) (n : V) :
    hL.normalEquivDual.symm α = Submodule.Quotient.mk n ↔ ∀ v : L, ω v n = α v := by
  rw [LinearEquiv.symm_apply_eq]
  exact LinearMap.ext_iff.trans
    (forall_congr' fun v ↦ by rw [normalEquivDual_mk_apply, eq_comm])

/-- Normal duality commutes with symplectic equivalences: the covector on the target
pulls back to the original covector on the Lagrangian subspace. -/
theorem IsLagrangian.normalEquivDual_naturality
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {ω' : SymplecticForm W} {L' : Submodule ℝ W} (hL : ω.IsLagrangian L)
    (hL' : ω'.IsLagrangian L') (e : V ≃ₗ[ℝ] W) (he : ω.IsSymplectomorphism ω' e)
    (hmap : L.map e.toLinearMap = L') (q : V ⧸ L) :
    (e.ofSubmodules L L' hmap).dualMap
        (hL'.normalEquivDual (Submodule.Quotient.equiv L L' e hmap q)) =
      hL.normalEquivDual q := by
  induction q using Submodule.Quotient.induction_on with
  | _ n =>
    ext v
    simpa only [LinearEquiv.dualMap_apply, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply, LinearEquiv.coe_coe, normalEquivDual_mk_apply,
      LinearEquiv.ofSubmodules_apply] using
      he.apply v n

/-- On the canonical cotangent zero section, the normal covector is the vertical
coordinate, with the positive sign. This is an explicit sign check; the general
normal-duality evaluation lemma already supplies the simplifier normal form. -/
theorem normalEquivDual_cotangentZeroSection_mk_apply (n : V × Module.Dual ℝ V)
    (v : cotangentZeroSection (V := V)) :
    isLagrangian_cotangentZeroSection.normalEquivDual (Submodule.Quotient.mk n) v =
      n.2 v.1.1 := by
  simp [mem_cotangentZeroSection_iff.mp v.2]

end TauCeti.SymplecticForm
