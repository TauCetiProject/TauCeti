/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.RingTheory.Flat.Basic

/-!
# Functoriality of Spin groups

A linear isometry of quadratic spaces induces an algebra homomorphism of their Clifford algebras.
This file proves that the homomorphism preserves the Spin group and packages the restriction as a
group homomorphism. It also records two facts needed for inclusions of quadratic summands: the
Clifford map from the left summand of an orthogonal product is injective over a field, and the
induced Spin map fixes the other summand under the vector action.

## Main results

* `spinGroup.map` is the homomorphism of Spin groups induced by a quadratic isometry.
* `spinGroup.map_injective_of_leftInverse` proves injectivity when the isometry has an isometric
  left inverse.
* `CliffordAlgebra.map_inl_injective` proves that the Clifford map of an orthogonal summand
  inclusion is injective over a field of characteristic different from two.
* `spinGroup.map_fixed_of_isometryEquiv_prod` proves that the Spin group of one summand fixes the
  other summand.
-/

public section


open QuadraticMap

namespace CliffordAlgebra

universe u v w x


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {N : Type x} [AddCommGroup N] [Module R N]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q : QuadraticForm R N}

/-- Clifford conjugation commutes with the algebra map induced by a quadratic isometry. -/
@[simp]
theorem map_star (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    map f (star x) = star (map f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

/-- A quadratic isometry sends the even Clifford subalgebra into the even Clifford subalgebra. -/
theorem map_mem_even (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁} (hx : x ∈ even Q₁) :
    map f x ∈ even Q₂ := by
  -- `even` is the subalgebra wrapper around degree zero of `evenOdd`; its induction principle is
  -- stated for the underlying graded submodule.
  change x ∈ evenOdd Q₁ 0 at hx
  change map f x ∈ evenOdd Q₂ 0
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      simpa using one_le_evenOdd_zero Q₂
        (Submodule.mem_one.mpr ⟨r, (map f).commutes r |>.symm⟩)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
      simpa only [map_mul, map_apply_ι, zero_add] using
        SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q₂ (f m₁) (f m₂)) hx

end CliffordAlgebra


namespace lipschitzGroup

universe u v w


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Mapping Clifford units along a quadratic isometry preserves the Lipschitz group. -/
theorem map_mem (f : Q₁ →qᵢ Q₂) {x : (CliffordAlgebra Q₁)ˣ} (hx : x ∈ lipschitzGroup Q₁) :
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

end lipschitzGroup


namespace spinGroup

universe u v w x


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {N : Type x} [AddCommGroup N] [Module R N]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q : QuadraticForm R N}

/-- The Clifford map induced by a quadratic isometry sends Spin elements to Spin elements. -/
theorem map_mem (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
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
        (lipschitzGroup.map_mem f (spinGroup.units_mem_lipschitzGroup x.2))
    simpa using hu
  · rw [Unitary.mem_iff]
    constructor
    · rw [← CliffordAlgebra.map_star, ← map_mul, spinGroup.star_mul_self_of_mem x.2,
        map_one]
    · rw [← CliffordAlgebra.map_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
        map_one]

/-- The homomorphism of Spin groups induced by a quadratic isometry. -/
def map (f : Q₁ →qᵢ Q₂) : spinGroup Q₁ →* spinGroup Q₂ where
  toFun x := ⟨CliffordAlgebra.map f (x : CliffordAlgebra Q₁), map_mem f x⟩
  map_one' := Subtype.ext (map_one (CliffordAlgebra.map f))
  map_mul' x y := Subtype.ext (map_mul (CliffordAlgebra.map f)
    (x : CliffordAlgebra Q₁) (y : CliffordAlgebra Q₁))

/-- The Spin-group map is induced by the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_map_apply (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
    (map f x : CliffordAlgebra Q₂) = CliffordAlgebra.map f (x : CliffordAlgebra Q₁) :=
  (rfl)

/-- The identity isometry induces the identity homomorphism of a Spin group. -/
@[simp]
theorem map_id (Q₁ : QuadraticForm R M₁) :
    map (QuadraticMap.Isometry.id Q₁) = MonoidHom.id (spinGroup Q₁) := by
  ext x
  simp

/-- Spin-group maps respect composition of quadratic isometries. -/
@[simp]
theorem map_comp_map (f : Q₂ →qᵢ Q) (g : Q₁ →qᵢ Q₂) :
    (map f).comp (map g) = map (f.comp g) := by
  ext x
  exact AlgHom.congr_fun (CliffordAlgebra.map_comp_map f g) (x : CliffordAlgebra Q₁)

/-- A Spin-group map is injective if its underlying Clifford-algebra map is injective. -/
theorem map_injective (f : Q₁ →qᵢ Q₂) (hf : Function.Injective (CliffordAlgebra.map f)) :
    Function.Injective (map f) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg ((↑) : spinGroup Q₂ → CliffordAlgebra Q₂) hxy

/-- A quadratic isometry with an isometric left inverse induces an injective Spin-group map. -/
theorem map_injective_of_leftInverse (f : Q₁ →qᵢ Q₂) (g : Q₂ →qᵢ Q₁)
    (h : Function.LeftInverse g f) : Function.Injective (map f) :=
  map_injective f (CliffordAlgebra.leftInverse_map_of_leftInverse f g h).injective

/-- Under an orthogonal-product isometry, the image of the Spin group of the first summand fixes
every vector in the second summand. -/
theorem map_fixed_of_isometryEquiv_prod (e : Q.IsometryEquiv (Q₁.prod Q₂)) [Invertible (2 : R)]
    (x : spinGroup Q₁) (m₂ : M₂) :
    CliffordAlgebra.spinVectorAction Q
      (map (e.symm.toIsometry.comp (QuadraticMap.Isometry.inl Q₁ Q₂)) x)
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

end spinGroup


open scoped TensorProduct

namespace CliffordAlgebra

universe u v w


variable {K : Type u} [Field K] [Invertible (2 : K)]
  {M₁ : Type v} [AddCommGroup M₁] [Module K M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module K M₂]

private theorem gradedTensorIncludeLeft_injective
    (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂) :
    Function.Injective (GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)) := by
  intro x y hxy
  apply Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (A := CliffordAlgebra Q₁) (B := CliffordAlgebra Q₂)
    (FaithfulSMul.algebraMap_injective K (CliffordAlgebra Q₂))
  have h := congrArg (GradedTensorProduct.auxEquiv K (evenOdd Q₁) (evenOdd Q₂)) hxy
  simpa using h

omit [Invertible (2 : K)] in
private theorem toProd_includeLeft (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂)
    (x : CliffordAlgebra Q₁) :
    toProd Q₁ Q₂ (GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂) x) =
      map (QuadraticMap.Isometry.inl Q₁ Q₂) x := by
  simp [toProd]

/-- The Clifford-algebra map induced by the inclusion of the left summand of an orthogonal product
is injective over a field of characteristic different from two. -/
theorem map_inl_injective (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂) :
    Function.Injective (map (QuadraticMap.Isometry.inl Q₁ Q₂)) := by
  intro x y hxy
  apply gradedTensorIncludeLeft_injective Q₁ Q₂
  apply (prodEquiv Q₁ Q₂).symm.injective
  -- Transport both elements through the product equivalence to expose `includeLeft`.
  change toProd Q₁ Q₂ (GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂) x) =
    toProd Q₁ Q₂ (GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂) y)
  rw [toProd_includeLeft, toProd_includeLeft]
  exact hxy

end CliffordAlgebra
