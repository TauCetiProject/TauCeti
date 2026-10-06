/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# The unit logarithmic lattice in the sum-zero hyperplane

The weighted logarithms of the units of a number field form a full lattice in the hyperplane
of functions on its infinite places whose coordinate sum is zero. Unlike a logarithmic embedding
which omits a distinguished place, this presentation is compatible with field automorphisms:
an automorphism permutes the logarithmic coordinates by its action on infinite places.

This is the archimedean part of the equivariant S-unit logarithmic lattice used to compute
Herbrand quotients. We transfer the lattice property from Mathlib's `NumberField.Units.unitLattice`
and use its torsion-kernel theorem, rather than proving Dirichlet's theorem again.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4, the logarithmic unit lattice.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K]

/-- The sum-zero hyperplane in the real functions on the infinite places of `K`. -/
def unitLogHyperplane : Submodule ℝ (InfinitePlace K → ℝ) :=
  LinearMap.ker (∑ w : InfinitePlace K, (LinearMap.proj w : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ))

/-- Membership in the unit logarithmic hyperplane is the product formula in logarithmic form. -/
@[simp] theorem mem_unitLogHyperplane (x : InfinitePlace K → ℝ) :
    x ∈ unitLogHyperplane K ↔ ∑ w, x w = 0 := by
  simp [unitLogHyperplane, LinearMap.sum_apply]

/-- The weighted logarithm of a unit, retaining every infinite place. -/
def unitLogEmbedding : Additive (𝓞 K)ˣ →+ unitLogHyperplane K where
  toFun u := ⟨fun w => (mult w : ℝ) * Real.log (w (u.toMul : K)),
    (mem_unitLogHyperplane K _).mpr (NumberField.Units.sum_mult_mul_log u.toMul)⟩
  map_zero' := by ext w; simp
  map_add' u v := by
    ext w
    simp [Real.log_mul, mul_add]

/-- The coordinate of the full logarithmic embedding at an infinite place. -/
@[simp] theorem unitLogEmbedding_apply (u : Additive (𝓞 K)ˣ) (w : InfinitePlace K) :
    (unitLogEmbedding K u).val w = (mult w : ℝ) * Real.log (w (u.toMul : K)) :=
  (rfl)

/-- The kernel of the full logarithmic embedding consists exactly of the roots of unity. -/
@[simp] theorem unitLogEmbedding_eq_zero_iff (u : Additive (𝓞 K)ˣ) :
    unitLogEmbedding K u = 0 ↔ u.toMul ∈ NumberField.Units.torsion K := by
  rw [NumberField.Units.mem_torsion]
  constructor
  · intro h w
    exact mult_log_place_eq_zero.mp (congrArg (fun x : unitLogHyperplane K => x.val w) h)
  · intro h
    ext w
    simp [unitLogEmbedding, h w]

/-- The kernel of the full logarithmic embedding is the additive torsion subgroup of units. -/
theorem unitLogEmbedding_ker :
    (unitLogEmbedding K).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  ext u
  simp only [AddMonoidHom.mem_ker, unitLogEmbedding_eq_zero_iff, Additive.mem_toAddSubgroup]

/-- The unit logarithmic lattice, as an integral submodule of the sum-zero hyperplane. -/
def fullUnitLattice : Submodule ℤ (unitLogHyperplane K) :=
  (unitLogEmbedding K).toIntLinearMap.range

/-- The full unit lattice is exactly the set of logarithmic images of units. -/
@[simp] theorem mem_fullUnitLattice (x : unitLogHyperplane K) :
    x ∈ fullUnitLattice K ↔ ∃ u, unitLogEmbedding K u = x :=
  (Iff.rfl)

/-! The comparison with Mathlib's coordinates is only used to transfer Dirichlet's lattice
property. The distinguished place is not part of the full logarithmic embedding. -/

open Classical in
private def unitLogCoordinates : unitLogHyperplane K ≃ₗ[ℝ] logSpace K where
  toFun x w := x.val w.val
  invFun x := ⟨fun w => if h : w = w₀ then -∑ v, x v else x ⟨w, h⟩, by
    rw [mem_unitLogHyperplane, Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    simp only [dite_true]
    have heq : (∑ v : {w : InfinitePlace K // w ≠ w₀},
        if h : v.val = w₀ then -∑ v, x v else x ⟨v.val, h⟩) = ∑ v, x v := by
      apply Finset.sum_congr rfl
      intro v _
      simp [v.property]
    rw [heq]
    exact neg_add_cancel _⟩
  left_inv x := by
    apply Subtype.ext
    funext w
    by_cases h : w = w₀
    · subst w
      have hx := (mem_unitLogHyperplane K _).mp x.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hx
      simp only [dite_true]
      linarith
    · simp [h]
  right_inv x := by
    funext w
    simp [w.property]
  map_add' x y := by rfl
  map_smul' a x := by rfl

private theorem unitLogCoordinates_apply (x : unitLogHyperplane K)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    unitLogCoordinates K x w = x.val w.val :=
  (rfl)

private theorem unitLogCoordinates_embedding (u : Additive (𝓞 K)ˣ) :
    unitLogCoordinates K (unitLogEmbedding K u) = NumberField.Units.logEmbedding K u := by
  funext w
  rw [unitLogCoordinates_apply, unitLogEmbedding_apply]
  exact (logEmbedding_component u.toMul w).symm

open Classical in
private theorem fullUnitLattice_eq_comap :
    fullUnitLattice K = ZLattice.comap ℝ (E := logSpace K) (F := unitLogHyperplane K)
      (NumberField.Units.unitLattice K)
      (unitLogCoordinates K).toContinuousLinearEquiv.toLinearMap := by
  ext x
  rw [mem_fullUnitLattice]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, trivial, unitLogCoordinates_embedding K u⟩
  · rintro ⟨u, _, hu⟩
    exact ⟨u, (unitLogCoordinates K).injective ((unitLogCoordinates_embedding K u).trans hu)⟩

/-- The unit logarithmic lattice is discrete. -/
instance discreteTopology_fullUnitLattice : DiscreteTopology (fullUnitLattice K) := by
  classical
  rw [fullUnitLattice_eq_comap]
  infer_instance

/-- **Dirichlet's unit lattice theorem, with all places retained.** The logarithmic image of
the units is a full integral lattice in the sum-zero hyperplane. -/
instance isZLattice_fullUnitLattice : IsZLattice ℝ (fullUnitLattice K) := by
  classical
  simp only [fullUnitLattice_eq_comap]
  infer_instance

/-- **Equivariance of the logarithmic embedding.** Transporting a unit along a field
isomorphism transports its coordinate at `w` to the coordinate at the pulled-back place. -/
theorem unitLogEmbedding_mapRingEquiv {L : Type*} [Field L] [NumberField L]
    (e : K ≃+* L) (u : (𝓞 K)ˣ) (w : InfinitePlace L) :
    (unitLogEmbedding L (.ofMul (Units.map (RingOfIntegers.mapRingEquiv e) u))).val w =
      (unitLogEmbedding K (.ofMul u)).val (w.comap (e : K →+* L)) := by
  have hm : mult (w.comap (e : K →+* L)) = mult w := by
    rw [mult, mult, isReal_comap_iff e]
  simp only [unitLogEmbedding_apply, toMul_ofMul, Units.coe_map,
    ← RingOfIntegers.coe_eq_algebraMap, RingEquiv.coe_toRingHom,
    comap_apply, hm]
  exact congrArg (fun x : L => (mult w : ℝ) * Real.log (w x))
    (RingOfIntegers.mapRingEquiv_apply e (u : 𝓞 K))

section GaloisAction

variable (k : Type*) [Field k] [Algebra k K]

/-- The permutation representation on the logarithmic hyperplane: an automorphism acts by
pullback along its inverse on infinite places. -/
def unitLogRepresentation : Representation ℝ Gal(K/k) (unitLogHyperplane K) where
  toFun σ :=
    { toFun x := ⟨fun w => x.val (σ⁻¹ • w), by
        rw [mem_unitLogHyperplane]
        exact (Equiv.sum_comp (MulAction.toPerm σ⁻¹) x.val).trans
          ((mem_unitLogHyperplane K _).mp x.property)⟩
      map_add' x y := by rfl
      map_smul' a x := by rfl }
  map_one' := by ext x w; simp
  map_mul' σ τ := by ext x w; simp [mul_smul]

/-- The Galois action on logarithmic vectors is the permutation of their coordinates. -/
@[simp] theorem unitLogRepresentation_apply (σ : Gal(K/k)) (x : unitLogHyperplane K)
    (w : InfinitePlace K) :
    (unitLogRepresentation K k σ x).val w = x.val (σ⁻¹ • w) :=
  (rfl)

/-- The full logarithmic embedding intertwines the action on units and the permutation
representation on infinite places. -/
@[simp] theorem unitLogRepresentation_embedding (σ : Gal(K/k)) (u : (𝓞 K)ˣ) :
    unitLogRepresentation K k σ (unitLogEmbedding K (.ofMul u)) =
      unitLogEmbedding K (.ofMul (Units.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv) u)) := by
  ext w
  rw [unitLogRepresentation_apply, unitLogEmbedding_mapRingEquiv]
  exact congrArg (fun v : InfinitePlace K => (unitLogEmbedding K (.ofMul u)).val v)
    (smul_eq_comap σ⁻¹ w)

/-- The full unit lattice is Galois-stable, so it is an integral lattice in the permutation
representation on the logarithmic hyperplane. -/
theorem unitLogRepresentation_mem_fullUnitLattice (σ : Gal(K/k))
    {x : unitLogHyperplane K} (hx : x ∈ fullUnitLattice K) :
    unitLogRepresentation K k σ x ∈ fullUnitLattice K := by
  obtain ⟨u, rfl⟩ := (mem_fullUnitLattice K x).mp hx
  exact (mem_fullUnitLattice K _).mpr
    ⟨.ofMul (Units.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv) u.toMul),
      (unitLogRepresentation_embedding K k σ u.toMul).symm⟩

/-- The integral Galois representation on the full unit logarithmic lattice, obtained by
restricting the permutation representation on the logarithmic hyperplane. -/
def fullUnitLatticeRepresentation : Representation ℤ Gal(K/k) (fullUnitLattice K) :=
  (unitLogRepresentation K k).restrictScalarsInt.subrepresentation (fullUnitLattice K)
    fun σ _ hx => by
      simpa only [Submodule.mem_comap, Representation.restrictScalarsInt_apply] using
        unitLogRepresentation_mem_fullUnitLattice K k σ hx

/-- The integral action on the full unit lattice agrees with the ambient permutation action. -/
@[simp] theorem fullUnitLatticeRepresentation_apply (σ : Gal(K/k)) (x : fullUnitLattice K) :
    (fullUnitLatticeRepresentation K k σ x).val = unitLogRepresentation K k σ x.val := by
  simp only [fullUnitLatticeRepresentation, Representation.subrepresentation_apply,
    LinearMap.restrict_apply, Representation.restrictScalarsInt_apply]

end GaloisAction

end TauCeti
