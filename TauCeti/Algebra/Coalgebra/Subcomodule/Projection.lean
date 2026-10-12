/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Projections along complementary subcomodules

Complementary subcomodules determine a projection of the ambient comodule onto either
complement. This file equips the underlying `Submodule.projection` with the proof that it
commutes with the coaction.

## Main declarations

* `TauCeti.Subcomodule.projection`: the comodule projection onto a subcomodule along a
  complementary subcomodule.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Subcomodule

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommGroup V] [Module R V] [Comodule R C V]

/-- The projection onto a subcomodule `W` along a complementary subcomodule `Q`, as a comodule
endomorphism. Its underlying linear map is `Submodule.projection`. -/
noncomputable def projection (W Q : Subcomodule R C V)
    (h : IsCompl W.toSubmodule Q.toSubmodule) : Comodule.Hom R C V V where
  toLinearMap := W.toSubmodule.projection Q.toSubmodule h
  map_coact := by
    ext v
    obtain ⟨w, hw, q, hq, rfl⟩ := Submodule.mem_sup.mp (h.sup_eq_top ▸ Submodule.mem_top :
      v ∈ W.toSubmodule ⊔ Q.toSubmodule)
    obtain ⟨x, hx⟩ := W.coact_mem hw
    obtain ⟨y, hy⟩ := Q.coact_mem hq
    have hW : W.toSubmodule.projection Q.toSubmodule h ∘ₗ W.carrier.subtype =
        LinearMap.id ∘ₗ W.carrier.subtype := by
      ext w
      exact Submodule.projection_apply_of_mem_left h w.2
    have hQ : W.toSubmodule.projection Q.toSubmodule h ∘ₗ Q.carrier.subtype =
        0 ∘ₗ Q.carrier.subtype := by
      ext q
      exact Submodule.projection_apply_of_mem_right h q.2
    simp only [LinearMap.comp_apply, map_add, ← hx, ← hy, TensorProduct.map_map, hW, hQ,
      LinearMap.id_comp, LinearMap.zero_comp, TensorProduct.map_zero_left, LinearMap.zero_apply,
      Submodule.projection_apply_of_mem_left h hw, Submodule.projection_apply_of_mem_right h hq,
      map_zero, add_zero]

/-- The underlying linear map of `TauCeti.Subcomodule.projection` is the linear projection
`Submodule.projection`. -/
@[simp]
theorem projection_toLinearMap (W Q : Subcomodule R C V)
    (h : IsCompl W.toSubmodule Q.toSubmodule) :
    (projection W Q h).toLinearMap = W.toSubmodule.projection Q.toSubmodule h :=
  (rfl)

/-- The projection onto `W` along `Q` takes values in `W`. -/
@[simp]
theorem projection_apply_mem {W Q : Subcomodule R C V}
    (h : IsCompl W.toSubmodule Q.toSubmodule) (v : V) : projection W Q h v ∈ W :=
  Submodule.projection_apply_mem h v

/-- The projection onto `W` along `Q` fixes `W` pointwise. -/
@[simp]
theorem projection_apply_of_mem_left {W Q : Subcomodule R C V}
    (h : IsCompl W.toSubmodule Q.toSubmodule) {v : V} (hv : v ∈ W) : projection W Q h v = v :=
  Submodule.projection_apply_of_mem_left h hv

/-- The projection onto `W` along `Q` vanishes on `Q`. -/
@[simp]
theorem projection_apply_of_mem_right {W Q : Subcomodule R C V}
    (h : IsCompl W.toSubmodule Q.toSubmodule) {v : V} (hv : v ∈ Q) : projection W Q h v = 0 :=
  Submodule.projection_apply_of_mem_right h hv

end Subcomodule

end TauCeti
