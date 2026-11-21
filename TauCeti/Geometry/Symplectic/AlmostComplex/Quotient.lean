/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Almost complex structures on quotient spaces

An invariant real subspace of an almost complex vector space has an almost complex quotient.
The quotient projection intertwines the two structures. In particular this constructs the
complex structure on the normal quotient of a pseudoholomorphic immersion, without a metric
or a choice of complement.

More generally, if `π : V → W` is a surjective linear map whose kernel `J` preserves, there is
exactly one complex structure `J_W` on `W` with `π ∘ J = J_W ∘ π`
(`TauCeti.AlmostComplexStructure.descend`,
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

* `TauCeti.AlmostComplexStructure.quotient`: the structure induced on `V ⧸ p`.
* `TauCeti.AlmostComplexStructure.descend`: the structure induced on the target of a surjection
  whose kernel is `J`-invariant, characterized by `TauCeti.AlmostComplexStructure.descend_apply`.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_iff_eq_descend`: it is the only structure
  making the surjection complex linear.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The almost complex structure induced on the quotient by an invariant real subspace. -/
def quotient (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) : AlmostComplexStructure (V ⧸ p) where
  toLinearMap := p.mapQ p J.toLinearMap hp
  square_neg := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    simp [Submodule.mapQ_apply, J.apply_apply]

/-- The underlying endomorphism is the map induced on the quotient. -/
theorem quotient_toLinearMap (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) :
    (J.quotient p hp).toLinearMap = p.mapQ p J.toLinearMap hp := (rfl)

/-- On a quotient class the induced structure applies the original structure to a lift. -/
@[simp]
theorem quotient_mk (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) (v : V) :
    J.quotient p hp (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J v) := by
  simp [quotient]

/-- The quotient projection is complex linear. -/
@[simp]
theorem isComplexLinearMap_mkQ (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) :
    IsComplexLinearMap J (J.quotient p hp) p.mkQ := by
  simp [isComplexLinearMap_iff_apply]

/-- The quotient structure is characterized by complex linearity of the quotient projection. -/
theorem quotient_eq_iff (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure (V ⧸ p)) :
    J.quotient p hp = K ↔ IsComplexLinearMap J K p.mkQ := by
  constructor
  · rintro rfl
    exact J.isComplexLinearMap_mkQ p hp
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    rw [← (isComplexLinearMap_iff_apply _ _ _).1 h w]
    simp

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Complex linearity out of a quotient can be tested after the quotient projection. -/
theorem isComplexLinearMap_comp_mkQ_iff (J : AlmostComplexStructure V)
    (p : Submodule ℝ V) (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure W)
    (f : V ⧸ p →ₗ[ℝ] W) :
    IsComplexLinearMap J K (f.comp p.mkQ) ↔ IsComplexLinearMap (J.quotient p hp) K f := by
  simp only [isComplexLinearMap_iff_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    simpa using h w
  · intro h v
    simpa using h (p.mkQ v)

/-- The quotient lift is complex-linear exactly when the original map is. -/
@[simp]
theorem isComplexLinearMap_liftQ_iff (J : AlmostComplexStructure V)
    (p : Submodule ℝ V) (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure W)
    (f : V →ₗ[ℝ] W) (hf : p ≤ LinearMap.ker f) :
    IsComplexLinearMap (J.quotient p hp) K (p.liftQ f hf) ↔ IsComplexLinearMap J K f := by
  rw [← isComplexLinearMap_comp_mkQ_iff]
  simp

/-- **The complex structure induced on the target of a surjection.** If `π : V → W` is surjective
and its kernel is `J`-invariant, the quotient structure on `V ⧸ ker π`, transported along
`V ⧸ ker π ≃ W`. It is characterized by `J_W (π v) = π (J v)`
(`TauCeti.AlmostComplexStructure.descend_apply`). -/
noncomputable def descend (J : AlmostComplexStructure V) (π : V →ₗ[ℝ] W)
    (hπ : Function.Surjective π) (hJ : ∀ v, π v = 0 → π (J v) = 0) :
    AlmostComplexStructure W :=
  (J.quotient (LinearMap.ker π) fun v hv ↦
    LinearMap.mem_ker.2 (hJ v (LinearMap.mem_ker.1 hv))).transport (π.quotKerEquivOfSurjective hπ)

/-- The induced structure is characterized by `J_W (π v) = π (J v)`. -/
@[simp]
theorem descend_apply (J : AlmostComplexStructure V) (π : V →ₗ[ℝ] W)
    (hπ : Function.Surjective π) (hJ : ∀ v, π v = 0 → π (J v) = 0) (v : V) :
    J.descend π hπ hJ (π v) = π (J v) := by
  have hs : (π.quotKerEquivOfSurjective hπ).symm (π v) = Submodule.Quotient.mk v := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [descend, transport_apply, hs, quotient_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The surjection is complex linear for the induced structure on its target. -/
@[simp]
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
    J.descend (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ v = (J (v, 0)).1 := by
  simpa using descend_apply J (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ (v, 0)

end TauCeti.AlmostComplexStructure

namespace TauCeti

variable {U V : Type*}
  [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {j : AlmostComplexStructure U} {J : AlmostComplexStructure V} {f : U →ₗ[ℝ] V}

/-- The almost complex structure on the quotient by the range of a complex-linear map. -/
def IsComplexLinearMap.quotientRange (hf : IsComplexLinearMap j J f) :
    AlmostComplexStructure (V ⧸ LinearMap.range f) :=
  J.quotient (LinearMap.range f) (fun _ hv ↦ hf.apply_mem_range hv)

/-- The range-quotient structure is induced by the target structure on the invariant range. -/
theorem IsComplexLinearMap.quotientRange_def (hf : IsComplexLinearMap j J f) :
    hf.quotientRange = J.quotient (LinearMap.range f) (fun _ hv ↦ hf.apply_mem_range hv) :=
  (rfl)

/-- On a range quotient class the induced structure applies the target structure to a lift. -/
@[simp]
theorem IsComplexLinearMap.quotientRange_mk (hf : IsComplexLinearMap j J f) (v : V) :
    hf.quotientRange (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J v) := by
  simp only [IsComplexLinearMap.quotientRange_def, AlmostComplexStructure.quotient_mk]

/-- Projection to the range quotient of a complex-linear map is complex-linear. -/
@[simp]
theorem IsComplexLinearMap.isComplexLinearMap_quotientRange_mkQ
    (hf : IsComplexLinearMap j J f) :
    IsComplexLinearMap J hf.quotientRange (LinearMap.range f).mkQ := by
  rw [hf.quotientRange_def]
  exact J.isComplexLinearMap_mkQ _ _

/-- A complex-linear map preserving invariant submodules induces a complex-linear quotient map. -/
theorem IsComplexLinearMap.mapQ {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {J : AlmostComplexStructure V} {K : AlmostComplexStructure W} {f : V →ₗ[ℝ] W}
    (h : IsComplexLinearMap J K f) (p : Submodule ℝ V) (q : Submodule ℝ W)
    (hp : ∀ v ∈ p, J v ∈ p) (hq : ∀ w ∈ q, K w ∈ q) (hf : p ≤ q.comap f) :
    IsComplexLinearMap (J.quotient p hp) (K.quotient q hq) (p.mapQ q f hf) := by
  rw [← AlmostComplexStructure.isComplexLinearMap_comp_mkQ_iff]
  rw [Submodule.mapQ_mkQ]
  exact (K.isComplexLinearMap_mkQ q hq).comp h

end TauCeti
