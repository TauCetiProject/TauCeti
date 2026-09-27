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

universe u v w

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

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

/-- The Lipschitz action is natural under a quadratic isometry equivalence. -/
@[simp]
theorem orthogonalGroupCongr_lipschitzToOrthogonal [Invertible (2 : R)]
    (e : Q₁.IsometryEquiv Q₂) (x : lipschitzGroup Q₁) :
    TauCeti.QuadraticMap.orthogonalGroupCongr e
        (CliffordAlgebra.lipschitzToOrthogonal Q₁ x) =
      CliffordAlgebra.lipschitzToOrthogonal Q₂ (e.toIsometry.lipschitzGroupMap x) := by
  ext m
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply]
  -- The preceding application lemmas leave both sides as bundled linear
  -- equivalence applications.  This `change` unfolds those coercions to the
  -- underlying isometry action required by the reusable naturality theorem.
  change e.toIsometry (CliffordAlgebra.lipschitzVectorAction Q₁ x (e.symm m)) = _
  simpa only [QuadraticMap.IsometryEquiv.toIsometry_apply, e.apply_symm_apply] using
    e.toIsometry.map_lipschitzVectorAction x (e.symm m)

end QuadraticMap.IsometryEquiv
