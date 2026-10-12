/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action

/-!
# Functoriality of Lipschitz groups

A ring homomorphism of Clifford algebras that sends vector generators to vector generators
restricts to a homomorphism of Lipschitz groups. In particular, a quadratic isometry induces such
a homomorphism, and its action on vectors is natural with respect to that isometry.

## Main results

* `CliffordAlgebra.lipschitzGroupMapOf` restricts a generator-preserving Clifford ring homomorphism
  to the Lipschitz groups.
* `QuadraticMap.Isometry.lipschitzGroupMap` is the homomorphism induced on Lipschitz groups.
* `QuadraticMap.IsometryEquiv.lipschitzGroupEquiv` is the equivalence induced on Lipschitz groups.
* `QuadraticMap.Isometry.map_lipschitzVectorAction` proves naturality of the Lipschitz action.
* `QuadraticMap.IsometryEquiv.orthogonalGroupCongr_lipschitzToOrthogonal` packages that result as
  an equality of orthogonal-group homomorphisms.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type x} [AddCommGroup N] [Module S N]
  {Q : QuadraticForm R M} {Q' : QuadraticForm S N}

/-- A Clifford ring homomorphism that sends vectors to vectors preserves the Lipschitz group. -/
theorem map_mem_lipschitzGroup_of_map_ι (F : CliffordAlgebra Q →+* CliffordAlgebra Q')
    (f : M → N) (hF : ∀ m, F (ι Q m) = ι Q' (f m))
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) :
    Units.map F.toMonoidHom x ∈ lipschitzGroup Q' := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hx
      -- Expose the generating set of the target closure before supplying the mapped vector.
      change ↑(Units.map F.toMonoidHom x) ∈ Set.range (ι Q')
      refine ⟨f m, ?_⟩
      calc
        ι Q' (f m) = F (ι Q m) := (hF m).symm
        _ = F (x : CliffordAlgebra Q) := congrArg F hm
        _ = F.toMonoidHom (x : CliffordAlgebra Q) := rfl
        _ = ↑(Units.map F.toMonoidHom x) := (Units.coe_map F.toMonoidHom x).symm
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

/-- Restrict a generator-preserving Clifford ring homomorphism to the Lipschitz groups. -/
def lipschitzGroupMapOf (F : CliffordAlgebra Q →+* CliffordAlgebra Q') (f : M → N)
    (hF : ∀ m, F (ι Q m) = ι Q' (f m)) : lipschitzGroup Q →* lipschitzGroup Q' where
  toFun x := ⟨Units.map F.toMonoidHom x.1, map_mem_lipschitzGroup_of_map_ι F f hF x.2⟩
  map_one' := by simp
  map_mul' x y := by simp

/-- The Clifford value of the restricted Lipschitz-group map is the original ring homomorphism. -/
@[simp]
theorem coe_lipschitzGroupMapOf_apply (F : CliffordAlgebra Q →+* CliffordAlgebra Q')
    (f : M → N) (hF : ∀ m, F (ι Q m) = ι Q' (f m)) (x : lipschitzGroup Q) :
    ((lipschitzGroupMapOf F f hF x : (CliffordAlgebra Q')ˣ) : CliffordAlgebra Q') =
      F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [lipschitzGroupMapOf]
  -- Remove the codomain restriction to expose the underlying map on units.
  change ↑(Units.map F.toMonoidHom (x : (CliffordAlgebra Q)ˣ)) =
    F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  exact Units.coe_map F.toMonoidHom (x : (CliffordAlgebra Q)ˣ)

/-- Mapping the inverse of a Lipschitz unit agrees with taking the inverse after restriction. -/
theorem lipschitzGroupMapOf_inv_coe (F : CliffordAlgebra Q →+* CliffordAlgebra Q')
    (f : M → N) (hF : ∀ m, F (ι Q m) = ι Q' (f m)) (x : lipschitzGroup Q) :
    F ((((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      ((((lipschitzGroupMapOf F f hF x : lipschitzGroup Q') :
          (CliffordAlgebra Q')ˣ)⁻¹ : (CliffordAlgebra Q')ˣ) : CliffordAlgebra Q') := by
  calc
    _ = (((lipschitzGroupMapOf F f hF (x⁻¹) : lipschitzGroup Q') :
        (CliffordAlgebra Q')ˣ) : CliffordAlgebra Q') :=
      (coe_lipschitzGroupMapOf_apply F f hF (x⁻¹)).symm
    _ = _ := by simp

end CliffordAlgebra

namespace QuadraticMap.Isometry

universe u v w x

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- Mapping Clifford units along a quadratic isometry preserves the Lipschitz group. -/
theorem map_mem_lipschitzGroup (f : Q₁ →qᵢ Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ lipschitzGroup Q₁) :
    Units.map (CliffordAlgebra.map f).toMonoidHom x ∈ lipschitzGroup Q₂ :=
  CliffordAlgebra.map_mem_lipschitzGroup_of_map_ι (CliffordAlgebra.map f).toRingHom f
    (CliffordAlgebra.map_apply_ι f) hx

/-- The Clifford map of a quadratic isometry restricts to a homomorphism of Lipschitz groups. -/
def lipschitzGroupMap (f : Q₁ →qᵢ Q₂) : lipschitzGroup Q₁ →* lipschitzGroup Q₂ :=
  CliffordAlgebra.lipschitzGroupMapOf (CliffordAlgebra.map f).toRingHom f
    (CliffordAlgebra.map_apply_ι f)

/-- Coercing the induced Lipschitz-group map is the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_lipschitzGroupMap_apply (f : Q₁ →qᵢ Q₂) (x : lipschitzGroup Q₁) :
    ((f.lipschitzGroupMap x : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) =
      CliffordAlgebra.map f ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  CliffordAlgebra.coe_lipschitzGroupMapOf_apply (CliffordAlgebra.map f).toRingHom f
    (CliffordAlgebra.map_apply_ι f) x

/-- Mapping the inverse of a Lipschitz unit agrees with taking the inverse after mapping. -/
@[simp]
theorem map_lipschitzGroup_inv_coe (f : Q₁ →qᵢ Q₂) (x : lipschitzGroup Q₁) :
    CliffordAlgebra.map f
        (((x : (CliffordAlgebra Q₁)ˣ)⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) =
      (((f.lipschitzGroupMap x)⁻¹ : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) :=
  CliffordAlgebra.lipschitzGroupMapOf_inv_coe (CliffordAlgebra.map f).toRingHom f
    (CliffordAlgebra.map_apply_ι f) x

-- The functoriality and equivalence API below adapts the corresponding Spin-group interface in
-- `TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map`.

/-- The identity isometry induces the identity homomorphism of a Lipschitz group. -/
@[simp]
theorem lipschitzGroupMap_id (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.Isometry.id Q₁).lipschitzGroupMap = MonoidHom.id (lipschitzGroup Q₁) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  simp only [coe_lipschitzGroupMap_apply, MonoidHom.id_apply]
  exact AlgHom.congr_fun (CliffordAlgebra.map_id Q₁) _

/-- Lipschitz-group maps respect composition of quadratic isometries. -/
@[simp]
theorem lipschitzGroupMap_comp (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    f.lipschitzGroupMap.comp g.lipschitzGroupMap = (f.comp g).lipschitzGroupMap := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  simp only [MonoidHom.comp_apply, coe_lipschitzGroupMap_apply]
  exact AlgHom.congr_fun (CliffordAlgebra.map_comp_map f g) _

/-- The Lipschitz action commutes with the map induced by a quadratic isometry. -/
@[simp]
theorem map_lipschitzVectorAction [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂)
    (x : lipschitzGroup Q₁) (m : M₁) :
    f (CliffordAlgebra.lipschitzVectorAction Q₁ x m) =
      CliffordAlgebra.lipschitzVectorAction Q₂ (f.lipschitzGroupMap x) (f m) := by
  apply CliffordAlgebra.ι_injective Q₂
  simp only [← CliffordAlgebra.map_apply_ι (f := f)
      (CliffordAlgebra.lipschitzVectorAction Q₁ x m),
    CliffordAlgebra.ι_lipschitzVectorAction_apply, map_mul,
    CliffordAlgebra.map_involute, ← f.coe_lipschitzGroupMap_apply x,
    f.map_lipschitzGroup_inv_coe, CliffordAlgebra.map_apply_ι]

end QuadraticMap.Isometry

namespace QuadraticMap.IsometryEquiv

universe u v w

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The equivalence of Lipschitz groups induced by a quadratic isometry equivalence. -/
def lipschitzGroupEquiv (e : Q₁.IsometryEquiv Q₂) : lipschitzGroup Q₁ ≃* lipschitzGroup Q₂ :=
  MonoidHom.toMulEquiv e.toIsometry.lipschitzGroupMap e.symm.toIsometry.lipschitzGroupMap
    (by
      rw [QuadraticMap.Isometry.lipschitzGroupMap_comp]
      have h : e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q₁ := by
        ext m
        exact e.symm_apply_apply m
      rw [h, QuadraticMap.Isometry.lipschitzGroupMap_id])
    (by
      rw [QuadraticMap.Isometry.lipschitzGroupMap_comp]
      have h : e.toIsometry.comp e.symm.toIsometry = QuadraticMap.Isometry.id Q₂ := by
        ext m
        exact e.apply_symm_apply m
      rw [h, QuadraticMap.Isometry.lipschitzGroupMap_id])

/-- The equivalence induced on Lipschitz groups agrees with the forward isometry map. -/
@[simp]
theorem lipschitzGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : lipschitzGroup Q₁) :
    e.lipschitzGroupEquiv x = e.toIsometry.lipschitzGroupMap x :=
  (rfl)

/-- The inverse of the induced Lipschitz equivalence is induced by the inverse quadratic
isometry. -/
@[simp]
theorem lipschitzGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.lipschitzGroupEquiv.symm = e.symm.lipschitzGroupEquiv := by
  ext x
  rfl

/-- The Lipschitz action is natural under a quadratic isometry equivalence. -/
@[simp]
theorem orthogonalGroupCongr_lipschitzToOrthogonal [Invertible (2 : R)]
    (e : Q₁.IsometryEquiv Q₂) (x : lipschitzGroup Q₁) :
    e.orthogonalGroupCongr
        (CliffordAlgebra.lipschitzToOrthogonal Q₁ x) =
      CliffordAlgebra.lipschitzToOrthogonal Q₂ (e.lipschitzGroupEquiv x) := by
  ext m
  rw [e.coe_orthogonalGroupCongr_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply, lipschitzGroupEquiv_apply]
  -- The preceding application lemmas leave both sides as bundled linear
  -- equivalence applications.  This `change` unfolds those coercions to the
  -- underlying isometry action required by the reusable naturality theorem.
  change e.toIsometry (CliffordAlgebra.lipschitzVectorAction Q₁ x (e.symm m)) = _
  simpa only [QuadraticMap.IsometryEquiv.toIsometry_apply, e.apply_symm_apply] using
    e.toIsometry.map_lipschitzVectorAction x (e.symm m)

end QuadraticMap.IsometryEquiv
