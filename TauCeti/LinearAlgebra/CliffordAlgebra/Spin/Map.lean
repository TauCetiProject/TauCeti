/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Functoriality of Spin groups

A linear isometry of quadratic spaces induces an algebra homomorphism of their Clifford algebras.
This file proves that the homomorphism preserves the Spin group and packages the restriction as a
group homomorphism. Isometry equivalences induce group equivalences, and these maps commute with
the vector actions. The fixed-complement result specializes this naturality to an orthogonal
summand.

## Main results

* `QuadraticMap.Isometry.spinGroupMap` is the homomorphism of Spin groups induced by a quadratic
  isometry.
* `QuadraticMap.IsometryEquiv.spinGroupEquiv` is the group equivalence induced by a quadratic
  isometry equivalence.
* `QuadraticMap.Isometry.spinGroupMap_injective_of_leftInverse` proves injectivity when the
  isometry has an isometric left inverse.
* `QuadraticMap.Isometry.spinGroupMap_spinVectorAction` proves naturality of the Spin vector
  action.
* `QuadraticMap.IsometryEquiv.spinGroupMap_fixed_of_prod` proves that the Spin group of one
  summand fixes the other summand.
-/

public section


open QuadraticMap

namespace QuadraticMap.Isometry

universe u v w


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Mapping Clifford units along a quadratic isometry preserves the Lipschitz group. -/
theorem map_mem_lipschitzGroup (f : Q₁ →qᵢ Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ lipschitzGroup Q₁) :
    Units.map (CliffordAlgebra.map f).toMonoidHom x ∈ lipschitzGroup Q₂ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hx
      -- Express the mapped unit as a Clifford generator in the target closure.
      change ↑(Units.map (CliffordAlgebra.map f).toMonoidHom x) ∈
        Set.range (CliffordAlgebra.ι Q₂)
      refine ⟨f m, ?_⟩
      change CliffordAlgebra.ι Q₂ (f m) =
        CliffordAlgebra.map f (x : CliffordAlgebra Q₁)
      rw [← hm, CliffordAlgebra.map_apply_ι]
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

end QuadraticMap.Isometry


namespace QuadraticMap.Isometry

universe u v w x


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {N : Type x} [AddCommGroup N] [Module R N]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q : QuadraticForm R N}

/-- The Clifford map induced by a quadratic isometry sends Spin elements to Spin elements. -/
theorem map_mem_spinGroup (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
    CliffordAlgebra.map f (x : CliffordAlgebra Q₁) ∈ spinGroup Q₂ := by
  rw [spinGroup.mem_iff]
  refine ⟨?_, CliffordAlgebra.map_mem_even f x.2.2⟩
  rw [pinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · have hu :
        (↑(Units.map (CliffordAlgebra.map f).toMonoidHom (spinGroup.toUnits x)) :
            CliffordAlgebra Q₂) ∈
          (lipschitzGroup Q₂).toSubmonoid.map
            (Units.coeHom (CliffordAlgebra Q₂)) :=
      lipschitzGroup.coe_mem_iff_mem.mpr
        (f.map_mem_lipschitzGroup (spinGroup.units_mem_lipschitzGroup x.2))
    have hmap :
        (↑(Units.map (CliffordAlgebra.map f).toMonoidHom (spinGroup.toUnits x)) :
            CliffordAlgebra Q₂) = CliffordAlgebra.map f (x : CliffordAlgebra Q₁) :=
      by
        change ↑(Units.map (CliffordAlgebra.map f).toMonoidHom (spinGroup.toUnits x)) =
          (CliffordAlgebra.map f).toMonoidHom
            (↑(spinGroup.toUnits x) : CliffordAlgebra Q₁)
        exact Units.coe_map (CliffordAlgebra.map f).toMonoidHom (spinGroup.toUnits x)
    rw [← hmap]
    exact hu
  · rw [Unitary.mem_iff]
    constructor
    · rw [← CliffordAlgebra.map_star, ← map_mul, spinGroup.star_mul_self_of_mem x.2,
        map_one]
    · rw [← CliffordAlgebra.map_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
        map_one]

/-- The homomorphism of Spin groups induced by a quadratic isometry. -/
def spinGroupMap (f : Q₁ →qᵢ Q₂) : spinGroup Q₁ →* spinGroup Q₂ where
  toFun x := ⟨CliffordAlgebra.map f (x : CliffordAlgebra Q₁), f.map_mem_spinGroup x⟩
  map_one' := Subtype.ext (map_one (CliffordAlgebra.map f))
  map_mul' x y := Subtype.ext (map_mul (CliffordAlgebra.map f)
    (x : CliffordAlgebra Q₁) (y : CliffordAlgebra Q₁))

/-- The Spin-group map is induced by the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_spinGroupMap_apply (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
    (f.spinGroupMap x : CliffordAlgebra Q₂) = CliffordAlgebra.map f (x : CliffordAlgebra Q₁) :=
  (rfl)

/-- The identity isometry induces the identity homomorphism of a Spin group. -/
@[simp]
theorem spinGroupMap_id (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.Isometry.id Q₁).spinGroupMap = MonoidHom.id (spinGroup Q₁) := by
  ext x
  simp

/-- Spin-group maps respect composition of quadratic isometries. -/
@[simp]
theorem spinGroupMap_comp (f : Q₂ →qᵢ Q) (g : Q₁ →qᵢ Q₂) :
    f.spinGroupMap.comp g.spinGroupMap = (f.comp g).spinGroupMap := by
  ext x
  exact AlgHom.congr_fun (CliffordAlgebra.map_comp_map f g) (x : CliffordAlgebra Q₁)

end QuadraticMap.Isometry


namespace QuadraticMap.IsometryEquiv

universe u v w


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The equivalence of Spin groups induced by a quadratic isometry equivalence. -/
def spinGroupEquiv (e : Q₁.IsometryEquiv Q₂) : spinGroup Q₁ ≃* spinGroup Q₂ :=
  MonoidHom.toMulEquiv e.toIsometry.spinGroupMap e.symm.toIsometry.spinGroupMap
    (by
      rw [QuadraticMap.Isometry.spinGroupMap_comp]
      have h : e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q₁ := by
        ext m
        exact e.symm_apply_apply m
      rw [h, QuadraticMap.Isometry.spinGroupMap_id])
    (by
      rw [QuadraticMap.Isometry.spinGroupMap_comp]
      have h : e.toIsometry.comp e.symm.toIsometry = QuadraticMap.Isometry.id Q₂ := by
        ext m
        exact e.apply_symm_apply m
      rw [h, QuadraticMap.Isometry.spinGroupMap_id])

/-- The equivalence induced on Spin groups agrees with the forward isometry map. -/
@[simp]
theorem spinGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : spinGroup Q₁) :
    e.spinGroupEquiv x = e.toIsometry.spinGroupMap x :=
  (rfl)

/-- The inverse of the induced Spin equivalence is induced by the inverse quadratic isometry. -/
@[simp]
theorem spinGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.spinGroupEquiv.symm = e.symm.spinGroupEquiv := by
  ext x
  rfl

end QuadraticMap.IsometryEquiv


namespace QuadraticMap.Isometry

universe u v w x


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {N : Type x} [AddCommGroup N] [Module R N]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q : QuadraticForm R N}

/-- A Spin-group map is injective if its underlying Clifford-algebra map is injective. -/
theorem spinGroupMap_injective (f : Q₁ →qᵢ Q₂)
    (hf : Function.Injective (CliffordAlgebra.map f)) : Function.Injective f.spinGroupMap := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg ((↑) : spinGroup Q₂ → CliffordAlgebra Q₂) hxy

/-- A quadratic isometry with an isometric left inverse induces an injective Spin-group map. -/
theorem spinGroupMap_injective_of_leftInverse (f : Q₁ →qᵢ Q₂) (g : Q₂ →qᵢ Q₁)
    (h : Function.LeftInverse g f) : Function.Injective f.spinGroupMap :=
  f.spinGroupMap_injective (CliffordAlgebra.leftInverse_map_of_leftInverse f g h).injective

/-- Spin-group maps commute with the vector actions induced by quadratic isometries. -/
@[simp]
theorem spinGroupMap_spinVectorAction [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂)
    (x : spinGroup Q₁) (m : M₁) :
    CliffordAlgebra.spinVectorAction Q₂ (f.spinGroupMap x) (f m) =
      f (CliffordAlgebra.spinVectorAction Q₁ x m) := by
  apply CliffordAlgebra.ι_injective Q₂
  rw [CliffordAlgebra.ι_spinVectorAction_apply, ← CliffordAlgebra.map_apply_ι,
    ← CliffordAlgebra.map_apply_ι, CliffordAlgebra.ι_spinVectorAction_apply, map_mul,
    map_mul, coe_spinGroupMap_apply, CliffordAlgebra.map_star]

end QuadraticMap.Isometry


namespace QuadraticMap.IsometryEquiv

universe u v w x


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {N : Type x} [AddCommGroup N] [Module R N]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q : QuadraticForm R N}

/-- Under an orthogonal-product isometry, the image of the Spin group of the first summand fixes
every vector in the second summand. -/
theorem spinGroupMap_fixed_of_prod (e : Q.IsometryEquiv (Q₁.prod Q₂)) [Invertible (2 : R)]
    (x : spinGroup Q₁) (m₂ : M₂) :
    CliffordAlgebra.spinVectorAction Q
      ((e.symm.toIsometry.comp (QuadraticMap.Isometry.inl Q₁ Q₂)).spinGroupMap x)
      (e.symm.toIsometry.comp (QuadraticMap.Isometry.inr Q₁ Q₂) m₂) =
        e.symm.toIsometry.comp (QuadraticMap.Isometry.inr Q₁ Q₂) m₂ := by
  apply CliffordAlgebra.ι_injective Q
  rw [CliffordAlgebra.ι_spinVectorAction_apply]
  let f₁ := e.symm.toIsometry.comp (QuadraticMap.Isometry.inl Q₁ Q₂)
  let f₂ := e.symm.toIsometry.comp (QuadraticMap.Isometry.inr Q₁ Q₂)
  have hOrtho : ∀ m₁ m₂, Q.IsOrtho (f₁ m₁) (f₂ m₂) := by
    intro m₁ m₂
    rw [QuadraticMap.isOrtho_def]
    simp only [f₁, f₂, QuadraticMap.Isometry.comp_apply]
    rw [← map_add, e.symm.toIsometry.map_app, e.symm.toIsometry.map_app,
      e.symm.toIsometry.map_app]
    exact QuadraticMap.IsOrtho.inl_inr (Q₁ := Q₁) (Q₂ := Q₂) m₁ m₂
  have hcomm : Commute
      (CliffordAlgebra.map f₁ (x : CliffordAlgebra Q₁))
      (CliffordAlgebra.ι Q (f₂ m₂)) := by
    simpa only [CliffordAlgebra.map_apply_ι] using
      CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left f₁ f₂ hOrtho
        (x : CliffordAlgebra Q₁) (CliffordAlgebra.ι Q₂ m₂) x.2.2
        (CliffordAlgebra.ι_mem_evenOdd_one Q₂ m₂)
  -- Unfold the vector action to the Clifford-algebra conjugation formula.
  change CliffordAlgebra.map f₁ (x : CliffordAlgebra Q₁) * CliffordAlgebra.ι Q (f₂ m₂) *
      star (CliffordAlgebra.map f₁ (x : CliffordAlgebra Q₁)) = CliffordAlgebra.ι Q (f₂ m₂)
  rw [hcomm.eq, mul_assoc, ← CliffordAlgebra.map_star, ← map_mul,
    spinGroup.mul_star_self_of_mem x.2, map_one, mul_one]

end QuadraticMap.IsometryEquiv
