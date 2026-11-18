/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Complex structures induced on quotients

Let `J` be a linear complex structure on a real vector space `V`. If `J` preserves a subspace `L`,
it induces a complex structure on the quotient `V ⧸ L` for which the quotient map is complex
linear (`TauCeti.AlmostComplexStructure.quotient`). More generally, if `π : V → W` is a
surjective linear map whose kernel `J` preserves, there is exactly one complex structure `J_W` on
`W` with `π ∘ J = J_W ∘ π` (`TauCeti.AlmostComplexStructure.descend`,
`TauCeti.AlmostComplexStructure.isComplexLinearMap_iff_eq_descend`). Conversely, the kernel of a
complex-linear map is invariant
(`TauCeti.IsComplexLinearMap.apply_apply_eq_zero_of_apply_eq_zero`), so the invariance of the
kernel is exactly the condition for `π` to be complex linear for some structure on `W`.

The case of interest is the projection `E × N → E` to the first factor. Near a pseudoholomorphic
curve, coordinates `(z, W) ∈ E × N` built from a foliation of a tube by pseudoholomorphic normal
discs make every fibre `{z} × N` complex, that is, `J` preserves the vertical subspace `{0} × N`.
The structure induced on the base is then `J_E v = (J (v, 0)).1`
(`TauCeti.AlmostComplexStructure.descend_fst_apply`). It depends on the point of `E × N`, not only
on its base point, so the projection of a pseudoholomorphic map is holomorphic only for this
varying structure on the base.

## Main declarations

* `TauCeti.AlmostComplexStructure.quotient`: the structure induced on `V ⧸ L`.
* `TauCeti.AlmostComplexStructure.descend`: the structure induced on the target of a surjection
  whose kernel is `J`-invariant, characterized by `TauCeti.AlmostComplexStructure.descend_apply`.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_iff_eq_descend`: it is the only structure
  making the surjection complex linear.
-/

public section

namespace TauCeti

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The kernel of a complex-linear map is invariant under the source structure: if `F v = 0`
then `F (J v) = J' (F v) = 0`. -/
theorem IsComplexLinearMap.apply_apply_eq_zero_of_apply_eq_zero {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) {v : V}
    (hv : F v = 0) : F (J v) = 0 := by
  rw [(isComplexLinearMap_iff_apply J J' F).1 hF v, hv, J'.apply_zero]

namespace AlmostComplexStructure

/-- **The quotient complex structure.** A complex structure `J` preserving a subspace `L` induces
the complex structure `[v] ↦ [J v]` on `V ⧸ L`. -/
def quotient (J : AlmostComplexStructure V) (L : Submodule ℝ V) (hL : ∀ x ∈ L, J x ∈ L) :
    AlmostComplexStructure (V ⧸ L) where
  toLinearMap := L.mapQ L J.toLinearMap hL
  square_neg := by
    ext v
    simp

@[simp]
theorem quotient_mk (J : AlmostComplexStructure V) (L : Submodule ℝ V) (hL : ∀ x ∈ L, J x ∈ L)
    (v : V) : J.quotient L hL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J v) :=
  (rfl)

/-- The quotient map is complex linear for the quotient structure. -/
theorem isComplexLinearMap_mkQ (J : AlmostComplexStructure V) (L : Submodule ℝ V)
    (hL : ∀ x ∈ L, J x ∈ L) : IsComplexLinearMap J (J.quotient L hL) L.mkQ :=
  (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ (quotient_mk J L hL v).symm

/-- **The complex structure induced on the target of a surjection.** If `π : V → W` is surjective
and its kernel is `J`-invariant, the quotient structure on `V ⧸ ker π`, transported along
`V ⧸ ker π ≃ W`. It is characterized by `J_W (π v) = π (J v)`
(`TauCeti.AlmostComplexStructure.descend_apply`). -/
noncomputable def descend (J : AlmostComplexStructure V) (π : V →ₗ[ℝ] W)
    (hπ : Function.Surjective π) (hJ : ∀ v, π v = 0 → π (J v) = 0) :
    AlmostComplexStructure W :=
  (J.quotient (LinearMap.ker π) fun v hv ↦
    LinearMap.mem_ker.2 (hJ v (LinearMap.mem_ker.1 hv))).transport (π.quotKerEquivOfSurjective hπ)

@[simp]
theorem descend_apply (J : AlmostComplexStructure V) (π : V →ₗ[ℝ] W)
    (hπ : Function.Surjective π) (hJ : ∀ v, π v = 0 → π (J v) = 0) (v : V) :
    J.descend π hπ hJ (π v) = π (J v) := by
  have hs : (π.quotKerEquivOfSurjective hπ).symm (π v) = Submodule.Quotient.mk v := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [descend, transport_apply, hs, quotient_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The surjection is complex linear for the induced structure on its target. -/
theorem isComplexLinearMap_descend (J : AlmostComplexStructure V) (π : V →ₗ[ℝ] W)
    (hπ : Function.Surjective π) (hJ : ∀ v, π v = 0 → π (J v) = 0) :
    IsComplexLinearMap J (J.descend π hπ hJ) π :=
  (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ (descend_apply J π hπ hJ v).symm

/-- **Uniqueness of the induced structure.** A surjection `π` is complex linear from `J` to `J'`
exactly when `J'` is the structure induced by `J`. -/
theorem isComplexLinearMap_iff_eq_descend {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {π : V →ₗ[ℝ] W} (hπ : Function.Surjective π)
    (hJ : ∀ v, π v = 0 → π (J v) = 0) :
    IsComplexLinearMap J J' π ↔ J' = J.descend π hπ hJ := by
  refine ⟨fun h ↦ ext fun w ↦ ?_, fun h ↦ h ▸ isComplexLinearMap_descend J π hπ hJ⟩
  obtain ⟨v, rfl⟩ := hπ w
  rw [descend_apply, (isComplexLinearMap_iff_apply J J' π).1 h v]

/-- On a product `E × N` whose vertical subspace `{0} × N` is `J`-invariant, the structure induced
on the base `E` is the block `J_E v = (J (v, 0)).1`. -/
@[simp]
theorem descend_fst_apply {E N : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup N]
    [Module ℝ N] (J : AlmostComplexStructure (E × N))
    (hJ : ∀ v : E × N, v.1 = 0 → (J v).1 = 0) (v : E) :
    J.descend (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ v = (J (v, 0)).1 :=
  descend_apply J (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ (v, 0)

end AlmostComplexStructure

end TauCeti
