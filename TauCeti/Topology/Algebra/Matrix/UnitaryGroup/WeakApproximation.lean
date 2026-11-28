/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil
public import TauCeti.Algebra.Star.Unitary.Infinitude
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Cayley
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
public import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup.Basic
public import TauCeti.Topology.Algebra.Ring.CayleyChart
public import TauCeti.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Approximation in unitary groups by Cayley coordinates

A dense, involution-preserving homomorphism from a field of characteristic other
than two with involution
to a topological ring with continuous involution and open units gives approximation
in the Cayley cell of every nondegenerate
hermitian form. If the target is a finite product of fields and the source has
infinitely many norm-one scalars, scalar translates of this cell cover the unitary
group. Consequently the image of the source unitary group is dense in the whole group.
The target involution may permute the field factors, as it does at split places.

The Cayley-coordinate method follows [ShortProof], grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`,
`src/Lib/Adelic/Unitary/WeakApproximation.lean` (`New.Space.weak_approximation`,
`New.cayleyTransform`). The proofs here use the existing algebraic Cayley bijection
and avoid its domain complement using the finite exceptional set for the determinant
pencil `det (1 + t • g)`.
-/

public section

open Set Topology Filter TauCeti

namespace Matrix

variable {n S : Type*} [Fintype n] [DecidableEq n]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

variable {K : Type*} [Field K] [StarRing K] [StarRing S] [ContinuousStar S]
  [Nontrivial S] {f : K →+* S} {A : Matrix n n K}

/-- Matrices skew-adjoint for a nondegenerate hermitian form over a dense subfield
of characteristic different from two are dense among the matrices skew-adjoint for
its scalar extension. -/
theorem mem_closure_map_of_star_mul_add_mul_eq_zero
    (hf : DenseRange f) (hfstar : ∀ x, f (star x) = star (f x))
    (h2 : (2 : K) ≠ 0) (hA : A.IsHermitian) (hA' : IsUnit A)
    (X : Matrix n n S) (hX : star X * A.map f + A.map f * X = 0) :
    X ∈ closure ((fun Z : Matrix n n K ↦ Z.map f) ''
      {Z | star Z * A + A * Z = 0}) := by
  let B := A.map f
  have hB : B.IsHermitian := hA.map f hfstar
  have hB' : IsUnit B := hA'.map f.mapMatrix
  let Y := f (2 : K)⁻¹ • (B * X)
  let P (Z : Matrix n n S) := B⁻¹ * (Z - star Z)
  have hPY : P Y = X := by
    have hskew := (star_mul_add_mul_eq_zero_iff hB).1 hX
    have hhalfK : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
      field_simp
      norm_num
    have hhalf : f (2 : K)⁻¹ + f (2 : K)⁻¹ = 1 := by
      rw [← map_add, hhalfK, map_one]
    simp only [P, Y, star_smul, ← hfstar, star_inv₀, star_ofNat, hskew, smul_neg,
      sub_neg_eq_add, ← add_smul, hhalf, one_smul]
    exact nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).1 hB')
  have hdense : DenseRange (fun Z : Matrix n n K ↦ Z.map f) :=
    DenseRange.piMap fun _ ↦ DenseRange.piMap fun _ ↦ hf
  have hP : Continuous P := by fun_prop
  have hlim := mem_closure_image hP.continuousAt (hdense Y)
  rw [hPY] at hlim
  refine closure_mono ?_ hlim
  rintro _ ⟨_, ⟨Z, rfl⟩, rfl⟩
  refine ⟨A⁻¹ * (Z - star Z), star_inv_mul_mul_add hA (by simp [star_sub]), ?_⟩
  simp only [P, B, Matrix.map_mul, map_nonsing_inv, Matrix.map_sub f f.map_sub,
    star_eq_conjTranspose, conjTranspose_map f hfstar]

namespace unitaryGroupOf

variable [IsOpenUnits S]

/-- Every point of the Cayley cell lies in the closure of the unitary matrices over
a dense subfield of characteristic different from two, for the scalar extension of
a nondegenerate hermitian form and an involution-preserving homomorphism. -/
theorem mem_topologicalClosure_map_of_isUnit_one_add
    (hf : DenseRange f) (hfstar : ∀ x, f (star x) = star (f x))
    (h2 : (2 : K) ≠ 0) (hA : A.IsHermitian) (hA' : IsUnit A)
    (g : unitaryGroupOf (A.map f))
    (hg : IsUnit (1 + ((g : GL n S) : Matrix n n S))) :
    (g : GL n S) ∈ ((unitaryGroupOf A).map (GeneralLinearGroup.map f)).topologicalClosure := by
  have htwo : IsUnit (2 : Matrix n n S) := by
    simpa only [RingHom.comp_apply, map_ofNat] using (isUnit_iff_ne_zero.2 h2).map
      ((algebraMap S (Matrix n n S)).comp f)
  let X := cayleyCoord 1 ((g : GL n S) : Matrix n n S)
  have hX : star X * A.map f + A.map f * X = 0 :=
    star_cayleyCoord_one_mul_add_mul_cayleyCoord_one (mem_unitaryGroupOf_iff.1 g.property)
  have hXunit : IsUnit (1 + X) := isUnit_one_add_cayleyCoord_one htwo _
  have hopen : IsOpen {Z : Matrix n n S | IsUnit (1 + Z)} :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Matrix n n S)).isOpen_range.preimage
      (continuous_const.add continuous_id)
  have hclosure := hopen.closure_inter
    ⟨mem_closure_map_of_star_mul_add_mul_eq_zero hf hfstar h2 hA hA' X hX, hXunit⟩
  have hmatrix := mem_closure_image (continuousAt_cayleyCoord hXunit) hclosure
  rw [cayleyCoord_one_cayleyCoord_one htwo hg] at hmatrix
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe,
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.closure_eq_preimage_closure_image]
  refine closure_mono ?_ hmatrix
  rintro _ ⟨_, ⟨⟨Z, hZ, rfl⟩, hZunit⟩, rfl⟩
  have hZ' : IsUnit (1 + Z) := (Matrix.isUnit_map_iff f _).1 (by
    simpa only [Matrix.map_add f f.map_add, Matrix.map_one f f.map_zero f.map_one,
      Set.mem_ofPred_eq] using hZunit)
  let u := (cayleyEquiv hA' (isUnit_iff_ne_zero.2 h2)) ⟨Z, hZ, hZ'⟩
  refine ⟨GeneralLinearGroup.map f (u.val : GL n K),
    Subgroup.mem_map.2 ⟨u.val, u.val.property, rfl⟩, ?_⟩
  rw [GeneralLinearGroup.val_map_apply, coe_cayleyEquiv_apply]
  simpa only [map_one, RingHom.mapMatrix_apply] using map_cayleyCoord f.mapMatrix 1 Z

/-- Over a finite product of fields, a unitary group over a dense subfield is dense,
provided `2` is nonzero and the subfield has infinitely many norm-one scalars.
The involution on the target may permute its field factors. -/
theorem le_topologicalClosure_map [Infinite (unitary K)]
    {I : Type*} [Finite I] {L : I → Type*} [∀ i, Field (L i)] (e : S ≃+* ∀ i, L i)
    (hf : DenseRange f) (hfstar : ∀ x, f (star x) = star (f x))
    (h2 : (2 : K) ≠ 0) (hA : A.IsHermitian) (hA' : IsUnit A) :
    unitaryGroupOf (A.map f) ≤
      ((unitaryGroupOf A).map (GeneralLinearGroup.map f)).topologicalClosure := by
  intro g hg
  have hinf : (unitary K : Set K).Infinite := Set.infinite_coe_iff.1 inferInstance
  obtain ⟨a, ha, hga⟩ := exists_isUnit_one_add_smul f e hinf (g : Matrix n n S)
  let u : unitaryGroupOf A := scalarHom A ⟨a, ha⟩
  let v := GeneralLinearGroup.map f (u : GL n K)
  have hv : v ∈ unitaryGroupOf (A.map f) := map_mem_unitaryGroupOf hfstar u.property
  have hvclosure : v ∈
      ((unitaryGroupOf A).map (GeneralLinearGroup.map f)).topologicalClosure :=
    Subgroup.le_topologicalClosure _ (Subgroup.mem_map.2 ⟨u, u.property, rfl⟩)
  have hvg : IsUnit (1 + ((v * g : GL n S) : Matrix n n S)) := by
    have hval : (v : Matrix n n S) = scalar n (f a) := by
      have hu : (u : GL n K) = GeneralLinearGroup.scalar n (Unitary.toUnits ⟨a, ha⟩) :=
        Units.ext (val_scalarHom ⟨a, ha⟩)
      dsimp only [v]
      rw [hu, GeneralLinearGroup.map_scalar, GeneralLinearGroup.coe_scalar]
      rfl
    rw [Units.val_mul, hval]
    simpa only [scalar_apply, ← smul_eq_diagonal_mul] using hga
  have hvgclosure := mem_topologicalClosure_map_of_isUnit_one_add hf hfstar h2 hA hA'
    ⟨v * g, mul_mem hv hg⟩ hvg
  exact (Subgroup.mul_mem_cancel_left _ hvclosure).1 hvgclosure

/-- The closure of a unitary group over a dense subfield is precisely the unitary
group of the extended nondegenerate hermitian form over a Hausdorff finite product
of fields, when the source has characteristic different from two and infinitely
many norm-one scalars. The dense homomorphism preserves the involutions. -/
theorem topologicalClosure_map_eq [T2Space S] [Infinite (unitary K)]
    {I : Type*} [Finite I] {L : I → Type*} [∀ i, Field (L i)] (e : S ≃+* ∀ i, L i)
    (hf : DenseRange f) (hfstar : ∀ x, f (star x) = star (f x))
    (h2 : (2 : K) ≠ 0) (hA : A.IsHermitian) (hA' : IsUnit A) :
    ((unitaryGroupOf A).map (GeneralLinearGroup.map f)).topologicalClosure =
      unitaryGroupOf (A.map f) := by
  refine le_antisymm ?_ (le_topologicalClosure_map e hf hfstar h2 hA hA')
  exact Subgroup.topologicalClosure_minimal _
    (by rintro _ ⟨g, hg, rfl⟩; exact map_mem_unitaryGroupOf hfstar hg)
    (isClosed_unitaryGroupOf _)

/-- Over a Hausdorff finite product of fields, the closure of the image of the source
unitary group equals the unitary group of the extended nondegenerate hermitian form,
when the source has characteristic zero and nontrivial involution and the dense
homomorphism preserves the involutions. -/
theorem topologicalClosure_map_eq_of_exists_star_ne [T2Space S] [CharZero K]
    {I : Type*} [Finite I] {L : I → Type*} [∀ i, Field (L i)] (e : S ≃+* ∀ i, L i)
    (hf : DenseRange f) (hfstar : ∀ x, f (star x) = star (f x))
    (hstar : ∃ x : K, star x ≠ x) (hA : A.IsHermitian) (hA' : IsUnit A) :
    ((unitaryGroupOf A).map (GeneralLinearGroup.map f)).topologicalClosure =
      unitaryGroupOf (A.map f) := by
  have := infinite_unitary_of_exists_star_ne hstar
  exact topologicalClosure_map_eq e hf hfstar two_ne_zero hA hA'

end unitaryGroupOf
end Matrix
