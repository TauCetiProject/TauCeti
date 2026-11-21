/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov

/-!
# Conicality of nilpotent adjoint orbits

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form.

By the Jacobson–Morozov theorem, every nonzero `ad`-nilpotent element `e ∈ 𝔤` fits into an `sl₂`
triple `(h, e, f)`. For any nonzero scalar `t : k`, `(h, t • e, t⁻¹ • f)` is another `sl₂` triple
sharing the neutral element `h`, so Malcev–Kostant conjugacy at fixed neutral element
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq`)
conjugates `e` to `t • e` under `G(k)`. Thus every nilpotent adjoint orbit is conical, and hence
contains `0` in its closure (`TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`), without
assuming `G` is connected.

## Main declarations

* `TauCeti.exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad`: every nonzero scalar
  multiple of an `ad`-nilpotent element lies in its rational adjoint orbit.
* `TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_isNilpotent_ad`: zero lies in the closure of
  every nilpotent adjoint orbit.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.2.
-/

public section

open WithConv

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Nilpotent adjoint orbits are conical.** Every nonzero scalar multiple of an `ad`-nilpotent
element lies in its rational adjoint orbit. No connectedness of `G` is assumed. -/
theorem exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad {e : 𝔤}
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) {t : k} (ht : t ≠ 0) :
    ∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g e = t • e := by
  by_cases he0 : e = 0
  · exact ⟨1, by simp [he0]⟩
  · obtain ⟨h, f, tr⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
    have tr' : IsSl2Triple h (t • e) (t⁻¹ • f) :=
      { h_ne_zero := tr.h_ne_zero
        lie_e_f := by rw [smul_lie, lie_smul, tr.lie_e_f, smul_smul, mul_inv_cancel₀ ht, one_smul]
        lie_h_e_nsmul := by rw [lie_smul, tr.lie_h_e_nsmul, smul_comm]
        lie_h_f_nsmul := by rw [lie_smul, tr.lie_h_f_nsmul, smul_neg, smul_comm] }
    obtain ⟨g, -, -, hge, -⟩ :=
      tr.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq tr'
    exact ⟨g, hge⟩

namespace Comodule.VectorOrbit

/-- **Zero lies in the closure of every nilpotent adjoint orbit.** No connectedness of `G` is
assumed. -/
theorem mk_zero_le_mk_of_isNilpotent_ad {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) :
    (mk (0 : 𝔤) : VectorOrbit k H 𝔤) ≤ mk e :=
  mk_zero_le_mk_of_forall_smul fun _ ht ↦
    exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad he ht

end Comodule.VectorOrbit

end TauCeti
