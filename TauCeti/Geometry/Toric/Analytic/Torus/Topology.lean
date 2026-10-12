/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Geometry.Toric.Analytic.Character.Basic

/-!
# The topology of the coordinate-free complex torus

For an additive commutative group `N`, the complex torus `ComplexTorus N` is the group of
`ℂˣ`-valued additive characters of `N →+ ℤ`.  This file equips it with the topology of pointwise
convergence: the coarsest topology for which the evaluation of every integral character is
continuous.  Any free presentation `e : (N →+ ℤ) ≃+ (ι →₀ ℤ)` identifies the torus with
`(ℂˣ)^ι` as a topological group, for an arbitrary index type `ι`.  Its ambient coordinates in
`ℂ^ι` are continuous and have range the locus where every coordinate is nonzero.  When `ι` is
finite, these ambient coordinates form an open embedding.

The torus is a Hausdorff topological group for every `N`, and every additive homomorphism of
such groups induces a continuous homomorphism of tori.  When `N` is a finitely generated free
`ℤ`-module, the torus is also second countable and locally compact.

Character evaluations are continuous by the topology of pointwise convergence.  For a chosen
presentation, the Laurent-monomial formula expresses each evaluation of the inverse coordinate
map as a finite product of powers, proving `continuous_complexTorusCoordinates_symm`.

## Main declarations

* `TauCeti.Toric.complexTorusTopology`: the topology of pointwise convergence.
* `TauCeti.Toric.continuous_complexTorus_iff`: a map into the torus is continuous exactly when
  each character evaluation of it is.
* `TauCeti.Toric.complexTorusCoordinatesContinuousMulEquiv`: a free presentation of the character
  lattice identifies the torus with `(ℂˣ)^ι` as a topological group.
* `TauCeti.Toric.complexTorusAmbient` and `TauCeti.Toric.continuous_complexTorusAmbient`:
  continuous ambient coordinates in `ℂ^ι`, with range the locus where every coordinate is nonzero.
* `TauCeti.Toric.isOpenEmbedding_complexTorusAmbient`: for finite `ι`, the ambient coordinates
  embed the torus openly into `ℂ^ι`.
* `TauCeti.Toric.continuous_complexTorusMap`: lattice maps induce continuous torus maps.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.1.
-/

public section

namespace TauCeti.Toric

open Topology

variable {N N' ι : Type*} [AddCommGroup N] [AddCommGroup N']

/-- The topology of pointwise convergence on the complex torus: the coarsest topology for which
evaluation of every integral character is continuous. -/
noncomputable instance complexTorusTopology : TopologicalSpace (ComplexTorus N) :=
  TopologicalSpace.induced (fun x : ComplexTorus N ↦ (⇑x : IntegralCharacter N → ℂˣ))
    inferInstance

/-- The torus topology is induced by the coercion to functions on the character lattice. -/
theorem isInducing_coe_complexTorus :
    IsInducing (fun x : ComplexTorus N ↦ (⇑x : IntegralCharacter N → ℂˣ)) :=
  ⟨rfl⟩

/-- The coercion of torus points to functions on the character lattice is an embedding. -/
theorem isEmbedding_coe_complexTorus :
    IsEmbedding (fun x : ComplexTorus N ↦ (⇑x : IntegralCharacter N → ℂˣ)) :=
  ⟨isInducing_coe_complexTorus, DFunLike.coe_injective⟩

/-- Evaluation at a fixed integral character is continuous on the torus. -/
@[fun_prop]
theorem continuous_complexTorus_apply (m : IntegralCharacter N) :
    Continuous fun x : ComplexTorus N ↦ x m :=
  (continuous_apply m).comp isInducing_coe_complexTorus.continuous

/-- Character evaluation is a continuous homomorphism on the torus. -/
@[fun_prop]
theorem continuous_characterEvaluation (m : IntegralCharacter N) :
    Continuous (characterEvaluation m) :=
  (continuous_complexTorus_apply m).congr fun x ↦ (characterEvaluation_apply m x).symm

/-- A map into the torus is continuous exactly when its composite with every character
evaluation is continuous. -/
theorem continuous_complexTorus_iff {X : Type*} [TopologicalSpace X] {f : X → ComplexTorus N} :
    Continuous f ↔ ∀ m : IntegralCharacter N, Continuous fun a ↦ f a m := by
  rw [isInducing_coe_complexTorus.continuous_iff, continuous_pi_iff]
  exact Iff.rfl

/-- The complex torus is a topological group for the pointwise-convergence topology. -/
instance : IsTopologicalGroup (ComplexTorus N) :=
  let f : ComplexTorus N →* (IntegralCharacter N → ℂˣ) :=
    { toFun := fun x ↦ ⇑x
      map_one' := AddChar.coe_one
      map_mul' := AddChar.coe_mul }
  Topology.IsInducing.isTopologicalGroup f ⟨rfl⟩

/-- The complex torus is Hausdorff. -/
instance : T2Space (ComplexTorus N) :=
  isEmbedding_coe_complexTorus.t2Space

/-- The map of tori induced by a lattice map is continuous. -/
@[fun_prop]
theorem continuous_complexTorusMap (f : N →+ N') : Continuous (complexTorusMap f) := by
  rw [continuous_complexTorus_iff]
  intro m
  simp only [complexTorusMap_apply, characterEvaluation_apply]
  exact continuous_complexTorus_apply _

/-! ### Coordinates supplied by a free presentation of the character lattice -/

variable (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

/-- The coordinates of a free presentation are continuous on the torus. -/
theorem continuous_complexTorusCoordinates : Continuous (complexTorusCoordinates e) :=
  continuous_pi fun i ↦ by
    simp only [complexTorusCoordinates_apply]
    exact continuous_complexTorus_apply _

/-- The inverse of the coordinates of a free presentation is continuous: every character
evaluation is a Laurent monomial in the coordinates. -/
theorem continuous_complexTorusCoordinates_symm :
    Continuous (complexTorusCoordinates e).symm := by
  rw [continuous_complexTorus_iff]
  intro m
  simp only [complexTorusCoordinates_symm_apply, Finsupp.prod]
  exact continuous_finsetProd _ fun i _ ↦ (continuous_apply i).zpow _

/-- A free presentation of the character lattice identifies the coordinate-free complex torus
with a product of copies of `ℂˣ` as a topological group. -/
noncomputable def complexTorusCoordinatesContinuousMulEquiv : ComplexTorus N ≃ₜ* (ι → ℂˣ) where
  toMulEquiv := complexTorusCoordinates e
  continuous_toFun := continuous_complexTorusCoordinates e
  continuous_invFun := continuous_complexTorusCoordinates_symm e

@[simp]
theorem coe_complexTorusCoordinatesContinuousMulEquiv :
    ⇑(complexTorusCoordinatesContinuousMulEquiv e) = complexTorusCoordinates e :=
  (rfl)

@[simp]
theorem coe_complexTorusCoordinatesContinuousMulEquiv_symm :
    ⇑(complexTorusCoordinatesContinuousMulEquiv e).symm = (complexTorusCoordinates e).symm :=
  (rfl)

/-- The ambient coordinates of the torus supplied by a free presentation `e`: the coordinates of
`e`, read as complex numbers.  For finite `ι`, they embed the torus openly into `ℂ^ι`. -/
noncomputable def complexTorusAmbient (x : ComplexTorus N) : ι → ℂ :=
  fun i ↦ (complexTorusCoordinates e x i : ℂ)

/-- The ambient coordinates are continuous for any index type. -/
@[fun_prop]
theorem continuous_complexTorusAmbient : Continuous (complexTorusAmbient e) :=
  continuous_pi fun i ↦
    Units.continuous_val.comp ((continuous_apply i).comp (continuous_complexTorusCoordinates e))

/-- An ambient coordinate is the complex value of the corresponding coordinate character. -/
@[simp]
theorem complexTorusAmbient_apply (x : ComplexTorus N) (i : ι) :
    complexTorusAmbient e x i = (x (e.symm (Finsupp.single i 1)) : ℂ) := by
  simp [complexTorusAmbient]

/-- The ambient coordinates of a torus point are nonzero. -/
@[simp↓]
theorem complexTorusAmbient_ne_zero (x : ComplexTorus N) (i : ι) :
    complexTorusAmbient e x i ≠ 0 :=
  Units.ne_zero _

/-- The ambient coordinates of a product are the pointwise product of the ambient coordinates. -/
@[simp]
theorem complexTorusAmbient_mul (x y : ComplexTorus N) :
    complexTorusAmbient e (x * y) = complexTorusAmbient e x * complexTorusAmbient e y := by
  ext i
  simp [complexTorusAmbient]

/-- The ambient coordinates of the identity are all equal to one. -/
@[simp]
theorem complexTorusAmbient_one : complexTorusAmbient e (1 : ComplexTorus N) = 1 := by
  ext i
  simp [complexTorusAmbient]

/-- The ambient coordinates of an inverse are the pointwise inverse of the ambient coordinates. -/
@[simp]
theorem complexTorusAmbient_inv (x : ComplexTorus N) :
    complexTorusAmbient e x⁻¹ = (complexTorusAmbient e x)⁻¹ := by
  ext i
  simp [complexTorusAmbient, AddChar.map_neg_eq_inv, Units.val_inv_eq_inv_val]

/-- For finite `ι`, the ambient coordinates are an open embedding of the torus into `ℂ^ι`. -/
theorem isOpenEmbedding_complexTorusAmbient [Finite ι] :
    IsOpenEmbedding (complexTorusAmbient e) :=
  (IsOpenEmbedding.piMap fun _ : ι ↦ Units.isOpenEmbedding_val).comp
    (complexTorusCoordinatesContinuousMulEquiv e).toHomeomorph.isOpenEmbedding

/-- The range of the ambient coordinates is the locus where every coordinate is nonzero. -/
theorem range_complexTorusAmbient :
    Set.range (complexTorusAmbient e) = {z : ι → ℂ | ∀ i, z i ≠ 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ i
    exact complexTorusAmbient_ne_zero e x i
  · intro hz
    refine ⟨(complexTorusCoordinates e).symm fun i ↦ Units.mk0 (z i) (hz i), ?_⟩
    ext i
    simp only [complexTorusAmbient, MulEquiv.apply_symm_apply, Units.val_mk0]

/-- The complex torus is second countable: an integral basis of `N` embeds it openly into a
finite-dimensional complex space. -/
instance [Module.Free ℤ N] [Module.Finite ℤ N] : SecondCountableTopology (ComplexTorus N) := by
  classical
  exact (isOpenEmbedding_complexTorusAmbient
    (Module.Free.chooseBasis ℤ N).integralCharacterRepr).isEmbedding.secondCountableTopology

/-- The complex torus is locally compact: an integral basis of `N` embeds it openly into a
finite-dimensional complex space. -/
instance [Module.Free ℤ N] [Module.Finite ℤ N] : LocallyCompactSpace (ComplexTorus N) := by
  classical
  exact (isOpenEmbedding_complexTorusAmbient
    (Module.Free.chooseBasis ℤ N).integralCharacterRepr).locallyCompactSpace

end TauCeti.Toric
