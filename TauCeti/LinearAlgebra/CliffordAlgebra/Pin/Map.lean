/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map

/-!
# Functoriality of Pin groups

A quadratic isometry `f : Q₁ →qᵢ Q₂` induces the Clifford algebra homomorphism
`CliffordAlgebra.map f`. It preserves the Lipschitz group and commutes with the Clifford star, so
it maps the Pin group of `Q₁`, the unitary part of the Lipschitz group, into the Pin group of
`Q₂`. This file packages that restriction as a group homomorphism and, for an isometry
equivalence, as a group equivalence.

These maps are compatible with the inclusion of the Spin group and with the inclusion into the
Lipschitz group, and they send the Pin element of a vector of norm `-1` to the Pin element of
its image. The twisted-conjugation action `CliffordAlgebra.pinToOrthogonal` is natural for them:
transporting the orthogonal transformation of a Pin element along an isometry equivalence `e`
with `orthogonalGroupCongr` gives the orthogonal transformation of the transported Pin element.
The Spin and Lipschitz versions of this naturality are
`QuadraticMap.IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal` and
`QuadraticMap.IsometryEquiv.orthogonalGroupCongr_lipschitzToOrthogonal`.

## Main definitions

* `QuadraticMap.Isometry.pinGroupMap` is the homomorphism of Pin groups induced by a quadratic
  isometry.
* `QuadraticMap.IsometryEquiv.pinGroupEquiv` is the group equivalence induced by a quadratic
  isometry equivalence.

## Main results

* `QuadraticMap.Isometry.pinGroupMap_ι`: a vector of norm `-1` is sent to its image.
* `QuadraticMap.Isometry.pinGroupMap_spinToPin` and
  `QuadraticMap.Isometry.pinToLipschitz_pinGroupMap`: compatibility with the Spin-group map and
  the Lipschitz-group map.
* `QuadraticMap.Isometry.pinToOrthogonal_pinGroupMap_apply`: naturality of the
  twisted-conjugation action under a quadratic isometry.
* `QuadraticMap.IsometryEquiv.orthogonalGroupCongr_pinToOrthogonal`: the same naturality as an
  equality in the orthogonal group.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace QuadraticMap.Isometry

universe u v w x

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- The Clifford map induced by a quadratic isometry sends Pin elements to Pin elements. -/
theorem map_mem_pinGroup (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁} (hx : x ∈ pinGroup Q₁) :
    CliffordAlgebra.map f x ∈ pinGroup Q₂ := by
  obtain ⟨⟨u, hu, rfl⟩, -⟩ := pinGroup.mem_iff.mp hx
  refine pinGroup.mem_iff.mpr
    ⟨⟨f.lipschitzGroupMap ⟨u, hu⟩, (f.lipschitzGroupMap ⟨u, hu⟩).property, ?_⟩, ?_⟩
  · simp only [Units.coeHom_apply, coe_lipschitzGroupMap_apply]
  · rw [Unitary.mem_iff, ← CliffordAlgebra.map_star, ← map_mul, ← map_mul,
      pinGroup.star_mul_self_of_mem hx, pinGroup.mul_star_self_of_mem hx, map_one]
    exact ⟨rfl, rfl⟩

/-- The homomorphism of Pin groups induced by a quadratic isometry. -/
def pinGroupMap (f : Q₁ →qᵢ Q₂) : pinGroup Q₁ →* pinGroup Q₂ where
  toFun x := ⟨CliffordAlgebra.map f (x : CliffordAlgebra Q₁), f.map_mem_pinGroup x.property⟩
  map_one' := Subtype.ext (map_one (CliffordAlgebra.map f))
  map_mul' x y := Subtype.ext (map_mul (CliffordAlgebra.map f)
    (x : CliffordAlgebra Q₁) (y : CliffordAlgebra Q₁))

/-- The Pin-group map is induced by the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_pinGroupMap_apply (f : Q₁ →qᵢ Q₂) (x : pinGroup Q₁) :
    (f.pinGroupMap x : CliffordAlgebra Q₂) = CliffordAlgebra.map f (x : CliffordAlgebra Q₁) :=
  (rfl)

/-- The identity isometry induces the identity homomorphism of a Pin group. -/
@[simp]
theorem pinGroupMap_id (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.Isometry.id Q₁).pinGroupMap = MonoidHom.id (pinGroup Q₁) := by
  ext x
  simp

/-- Pin-group maps respect composition of quadratic isometries. -/
@[simp]
theorem pinGroupMap_comp (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    f.pinGroupMap.comp g.pinGroupMap = (f.comp g).pinGroupMap := by
  ext x
  exact AlgHom.congr_fun (CliffordAlgebra.map_comp_map f g) (x : CliffordAlgebra Q₁)

/-- Applying two Pin-group maps in succession agrees with the Pin-group map of the composite
quadratic isometry. -/
@[simp]
theorem pinGroupMap_pinGroupMap (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) (x : pinGroup Q₁) :
    f.pinGroupMap (g.pinGroupMap x) = (f.comp g).pinGroupMap x :=
  DFunLike.congr_fun (f.pinGroupMap_comp g) x

/-- A Pin-group map is injective if its underlying Clifford-algebra map is injective. -/
theorem pinGroupMap_injective (f : Q₁ →qᵢ Q₂)
    (hf : Function.Injective (CliffordAlgebra.map f)) : Function.Injective f.pinGroupMap :=
  fun _ _ hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A quadratic isometry with an isometric left inverse induces an injective Pin-group map. -/
theorem pinGroupMap_injective_of_leftInverse (f : Q₁ →qᵢ Q₂) (g : Q₂ →qᵢ Q₁)
    (h : Function.LeftInverse g f) : Function.Injective f.pinGroupMap :=
  f.pinGroupMap_injective (CliffordAlgebra.leftInverse_map_of_leftInverse f g h).injective

/-- The Pin element of a vector of norm `-1` is sent to the Pin element of its image. -/
@[simp]
theorem pinGroupMap_ι (f : Q₁ →qᵢ Q₂) {v : M₁} (hv : Q₁ v = -1) :
    f.pinGroupMap ⟨CliffordAlgebra.ι Q₁ v, CliffordAlgebra.ι_mem_pinGroup hv⟩ =
      ⟨CliffordAlgebra.ι Q₂ (f v), CliffordAlgebra.ι_mem_pinGroup ((f.map_app v).trans hv)⟩ :=
  Subtype.ext (CliffordAlgebra.map_apply_ι f v)

/-- The Pin-group map restricts to the Spin-group map. -/
@[simp]
theorem pinGroupMap_spinToPin (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
    f.pinGroupMap (CliffordAlgebra.spinToPin Q₁ x) =
      CliffordAlgebra.spinToPin Q₂ (f.spinGroupMap x) :=
  Subtype.ext (by simp only [coe_pinGroupMap_apply, CliffordAlgebra.coe_spinToPin_apply,
    coe_spinGroupMap_apply])

/-- The square formed by the Spin and Pin-group maps and the inclusions of Spin into Pin
commutes. -/
theorem pinGroupMap_comp_spinToPin (f : Q₁ →qᵢ Q₂) :
    f.pinGroupMap.comp (CliffordAlgebra.spinToPin Q₁) =
      (CliffordAlgebra.spinToPin Q₂).comp f.spinGroupMap :=
  MonoidHom.ext (f.pinGroupMap_spinToPin)

/-- The Pin-group map is the restriction of the Lipschitz-group map. -/
@[simp]
theorem pinToLipschitz_pinGroupMap (f : Q₁ →qᵢ Q₂) (x : pinGroup Q₁) :
    CliffordAlgebra.pinToLipschitz Q₂ (f.pinGroupMap x) =
      f.lipschitzGroupMap (CliffordAlgebra.pinToLipschitz Q₁ x) :=
  Subtype.ext (Units.ext (by simp only [CliffordAlgebra.coe_pinToLipschitz_apply,
    coe_pinGroupMap_apply, coe_lipschitzGroupMap_apply]))

/-- The square formed by the Pin and Lipschitz-group maps and the inclusions of Pin into
Lipschitz commutes. -/
theorem pinToLipschitz_comp_pinGroupMap (f : Q₁ →qᵢ Q₂) :
    (CliffordAlgebra.pinToLipschitz Q₂).comp f.pinGroupMap =
      f.lipschitzGroupMap.comp (CliffordAlgebra.pinToLipschitz Q₁) :=
  MonoidHom.ext (f.pinToLipschitz_pinGroupMap)

/-- The twisted-conjugation action of Pin groups commutes with the maps induced by a quadratic
isometry. -/
@[simp]
theorem pinToOrthogonal_pinGroupMap_apply [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂)
    (x : pinGroup Q₁) (m : M₁) :
    ((CliffordAlgebra.pinToOrthogonal Q₂ (f.pinGroupMap x) :
        TauCeti.QuadraticMap.orthogonalGroup Q₂) : M₂ ≃ₗ[R] M₂) (f m) =
      f (((CliffordAlgebra.pinToOrthogonal Q₁ x : TauCeti.QuadraticMap.orthogonalGroup Q₁) :
        M₁ ≃ₗ[R] M₁) m) := by
  rw [CliffordAlgebra.coe_pinToOrthogonal_apply, CliffordAlgebra.coe_pinToOrthogonal_apply,
    pinToLipschitz_pinGroupMap]
  exact (f.map_lipschitzVectorAction (CliffordAlgebra.pinToLipschitz Q₁ x) m).symm

end QuadraticMap.Isometry

namespace QuadraticMap.IsometryEquiv

universe u v w x

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- The equivalence of Pin groups induced by a quadratic isometry equivalence. -/
def pinGroupEquiv (e : Q₁.IsometryEquiv Q₂) : pinGroup Q₁ ≃* pinGroup Q₂ :=
  MonoidHom.toMulEquiv e.toIsometry.pinGroupMap e.symm.toIsometry.pinGroupMap
    (by
      rw [Isometry.pinGroupMap_comp]
      have h : e.symm.toIsometry.comp e.toIsometry = Isometry.id Q₁ := by
        ext m
        exact e.symm_apply_apply m
      rw [h, Isometry.pinGroupMap_id])
    (by
      rw [Isometry.pinGroupMap_comp]
      have h : e.toIsometry.comp e.symm.toIsometry = Isometry.id Q₂ := by
        ext m
        exact e.apply_symm_apply m
      rw [h, Isometry.pinGroupMap_id])

/-- The equivalence induced on Pin groups agrees with the forward isometry map. -/
@[simp]
theorem pinGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : pinGroup Q₁) :
    e.pinGroupEquiv x = e.toIsometry.pinGroupMap x :=
  (rfl)

/-- The inverse of the induced Pin equivalence is induced by the inverse quadratic isometry. -/
@[simp]
theorem pinGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.pinGroupEquiv.symm = e.symm.pinGroupEquiv := by
  ext x
  rfl

/-- The identity isometry induces the identity equivalence of a Pin group. -/
@[simp]
theorem pinGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.IsometryEquiv.refl Q₁).pinGroupEquiv = MulEquiv.refl (pinGroup Q₁) :=
  MulEquiv.ext fun x ↦ DFunLike.congr_fun (Isometry.pinGroupMap_id Q₁) x

/-- Pin-group equivalences respect composition of quadratic isometry equivalences. -/
@[simp]
theorem pinGroupEquiv_trans (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).pinGroupEquiv = e₁₂.pinGroupEquiv.trans e₂₃.pinGroupEquiv :=
  MulEquiv.ext fun x ↦
    (DFunLike.congr_fun (e₂₃.toIsometry.pinGroupMap_comp e₁₂.toIsometry) x).symm

/-- The homomorphism from the Pin group to the orthogonal group is natural under isometric
equivalences of quadratic forms. -/
@[simp]
theorem orthogonalGroupCongr_pinToOrthogonal [Invertible (2 : R)]
    (e : Q₁.IsometryEquiv Q₂) (x : pinGroup Q₁) :
    e.orthogonalGroupCongr (CliffordAlgebra.pinToOrthogonal Q₁ x) =
      CliffordAlgebra.pinToOrthogonal Q₂ (e.pinGroupEquiv x) := by
  rw [CliffordAlgebra.pinToOrthogonal_eq_lipschitzToOrthogonal,
    CliffordAlgebra.pinToOrthogonal_eq_lipschitzToOrthogonal,
    e.orthogonalGroupCongr_lipschitzToOrthogonal, pinGroupEquiv_apply,
    Isometry.pinToLipschitz_pinGroupMap, lipschitzGroupEquiv_apply]

end QuadraticMap.IsometryEquiv
