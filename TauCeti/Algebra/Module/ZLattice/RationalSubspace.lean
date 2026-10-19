/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Localization.Integer

/-!
# The lattice of integral points of a rational subspace

For a subspace `V` of `ℚ^ι`, the integral points `V ∩ ℤ^ι` form a full lattice in the real span
of `V` inside the Euclidean space `ℝ^ι`. The lattice is the whole intersection `V ∩ ℤ^ι`, which
is saturated in `ℤ^ι`, and a `ℤ`-basis of it is a `ℚ`-basis of `V` and an `ℝ`-basis of the real
span.

## Main definitions

* `Submodule.intPoints V`: the integral points `V ∩ ℤ^ι`, as a `ℤ`-submodule of `ℤ^ι`.
* `Submodule.realSpan V`: the real span of `V` in the Euclidean space `ℝ^ι`.
* `Submodule.intLattice V`: the points of `V.realSpan` with integral coordinates, as a
  `ℤ`-submodule of `V.realSpan`.
* `Submodule.intPointsEquivIntLattice V`: the identification of the integral points of `V` with
  the points of `V.intLattice`.

## Main results

* `Submodule.toLp_mem_realSpan_iff`: the rational points of `V.realSpan` are the points of `V`.
* `Submodule.mem_intPoints_of_smul_mem`: the integral points of `V` are saturated in `ℤ^ι`.
* `Submodule.linearIndependent_intCast_basis_intPoints`,
  `Submodule.span_intCast_basis_intPoints`: a `ℤ`-basis of the integral points of `V` is a
  `ℚ`-basis of `V`.
* `Submodule.finrank_intPoints`, `Submodule.finrank_realSpan`: the integral points form a free
  `ℤ`-module of rank `dim V`, and the real span has dimension `dim V`.
* The instances `DiscreteTopology V.intLattice` and `IsZLattice ℝ V.intLattice`: the integral
  points form a full lattice in the real span.

## Implementation notes

The real span lives in `EuclideanSpace ℝ ι` because a lattice of rank smaller than `#ι` has a
covolume only in its own real span, measured by the volume of the inner product it inherits.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of
  Math. **85** (1967), 430–472, §3.

The construction is adapted from Ralf Stephan's `ArithmeticHeights/RationalLattice.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0).
-/

public section

noncomputable section

open Module Set

namespace Submodule

variable {ι : Type*}

/-- The integral points of a subspace `V` of `ℚ^ι`: the tuples `z : ι → ℤ` whose image in `ℚ^ι`
lies in `V`. -/
def intPoints (V : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  (V.restrictScalars ℤ).comap ((Algebra.linearMap ℤ ℚ).compLeft ι)

/-- An integral tuple is an integral point of `V` when its image in `ℚ^ι` lies in `V`. -/
@[simp]
theorem mem_intPoints {V : Submodule ℚ (ι → ℚ)} {z : ι → ℤ} :
    z ∈ V.intPoints ↔ (fun i ↦ (z i : ℚ)) ∈ V :=
  Iff.rfl

/-- The integral points of `V` form a saturated submodule of `ℤ^ι`: if a nonzero multiple of `z`
is an integral point of `V`, so is `z`. -/
theorem mem_intPoints_of_smul_mem {V : Submodule ℚ (ι → ℚ)} {c : ℤ} {z : ι → ℤ} (hc : c ≠ 0)
    (h : c • z ∈ V.intPoints) : z ∈ V.intPoints := by
  rw [mem_intPoints] at h ⊢
  convert V.smul_mem (c : ℚ)⁻¹ h using 1
  ext i
  simp [hc]

/-- The coordinatewise inclusion of `ℚ^ι` in the Euclidean space `ℝ^ι`. -/
private def ratCastEuclidean (ι : Type*) : (ι → ℚ) →ₗ[ℚ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℚ (ι → ℝ)).symm.toLinearMap ∘ₗ (Algebra.linearMap ℚ ℝ).compLeft ι

private theorem ratCastEuclidean_apply (v : ι → ℚ) :
    ratCastEuclidean ι v = WithLp.toLp 2 fun i ↦ (v i : ℝ) :=
  rfl

/-- The coordinatewise inclusion of `ℤ^ι` in the Euclidean space `ℝ^ι`. -/
private def intCastEuclidean (ι : Type*) : (ι → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℤ (ι → ℝ)).symm.toLinearMap ∘ₗ (Algebra.linearMap ℤ ℝ).compLeft ι

private theorem intCastEuclidean_apply (z : ι → ℤ) :
    intCastEuclidean ι z = WithLp.toLp 2 fun i ↦ (z i : ℝ) :=
  rfl

/-- The real span of a subspace `V` of `ℚ^ι`: the subspace of the Euclidean space `ℝ^ι` spanned
by the points of `V`. -/
def realSpan (V : Submodule ℚ (ι → ℚ)) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  span ℝ ((fun v : ι → ℚ ↦ WithLp.toLp 2 fun i ↦ (v i : ℝ)) '' V)

/-- The points of `V` lie in its real span. -/
theorem toLp_mem_realSpan {V : Submodule ℚ (ι → ℚ)} {v : ι → ℚ} (hv : v ∈ V) :
    (WithLp.toLp 2 fun i ↦ (v i : ℝ)) ∈ V.realSpan :=
  subset_span ⟨v, hv, rfl⟩

/-- The integral points of `V` as a lattice in the real span of `V`: the points of `V.realSpan`
whose coordinates are integers. -/
def intLattice (V : Submodule ℚ (ι → ℚ)) : Submodule ℤ V.realSpan where
  carrier := {w | ∀ i, ∃ z : ℤ, (w : EuclideanSpace ℝ ι) i = z}
  add_mem' := by
    rintro w w' hw hw' i
    obtain ⟨z, hz⟩ := hw i
    obtain ⟨z', hz'⟩ := hw' i
    exact ⟨z + z', by simp [hz, hz']⟩
  zero_mem' := fun _ ↦ ⟨0, by simp⟩
  smul_mem' := by
    rintro c w hw i
    obtain ⟨z, hz⟩ := hw i
    exact ⟨c * z, by simp [hz]⟩

/-- A point of the real span of `V` lies in `V.intLattice` when its coordinates are integers. -/
@[simp]
theorem mem_intLattice {V : Submodule ℚ (ι → ℚ)} {w : V.realSpan} :
    w ∈ V.intLattice ↔ ∀ i, ∃ z : ℤ, (w : EuclideanSpace ℝ ι) i = z :=
  Iff.rfl

variable [Finite ι]

/-- **The rational points of the real span of `V` are the points of `V`.** -/
@[simp]
theorem toLp_mem_realSpan_iff {V : Submodule ℚ (ι → ℚ)} {v : ι → ℚ} :
    (WithLp.toLp 2 fun i ↦ (v i : ℝ)) ∈ V.realSpan ↔ v ∈ V := by
  classical
  cases nonempty_fintype ι
  refine ⟨fun h ↦ ?_, toLp_mem_realSpan⟩
  by_contra hv
  -- A rational linear form vanishing on `V` but not at `v`...
  obtain ⟨f, hfv, hfV⟩ := exists_dual_map_eq_bot_of_notMem hv inferInstance
  -- ...extends to a real linear form with the same coefficients, which vanishes on the real
  -- span of `V`.
  set g : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ :=
    (EuclideanSpace.basisFun ι ℝ).toBasis.constr ℝ fun i ↦ (f (Pi.single i 1) : ℝ)
  have hg (u : ι → ℚ) : g (WithLp.toLp 2 fun i ↦ (u i : ℝ)) = f u := by
    have hu (i : ι) : Pi.single i (u i) = u i • (Pi.single i 1 : ι → ℚ) := by
      ext j
      simp [Pi.single_apply]
    conv_rhs => rw [← Finset.univ_sum_single u, map_sum]
    simp [g, Basis.constr_apply_fintype, hu]
  have hle : V.realSpan ≤ LinearMap.ker g := by
    refine span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    have hfu : f u = 0 := by
      have h := mem_map_of_mem (f := f) hu
      rwa [hfV, mem_bot] at h
    simp [hg, hfu]
  exact hfv (by exact_mod_cast (hg v).symm.trans (hle h))

/-- A point of the lattice of integral points of `V` comes from an integral point of `V`. -/
private theorem exists_mem_intPoints_of_mem_intLattice {V : Submodule ℚ (ι → ℚ)} {w : V.realSpan}
    (hw : w ∈ V.intLattice) :
    ∃ z ∈ V.intPoints, (w : EuclideanSpace ℝ ι) = intCastEuclidean ι z := by
  choose z hz using mem_intLattice.1 hw
  have hwz : (w : EuclideanSpace ℝ ι) = intCastEuclidean ι z := by
    ext i
    simp [intCastEuclidean_apply, hz]
  refine ⟨z, ?_, hwz⟩
  rw [mem_intPoints, ← toLp_mem_realSpan_iff]
  simpa [hwz, intCastEuclidean_apply] using w.2

section Basis

variable {V : Submodule ℚ (ι → ℚ)} {κ : Type*} (b : Basis κ ℤ V.intPoints)

omit [Finite ι] in
/-- The image of an integral point of `V` under a linear map is an integral combination of the
images of the members of a basis. -/
private theorem apply_mem_span_intCast_basis_intPoints {M : Type*} [AddCommGroup M] [Module ℤ M]
    (φ : (ι → ℤ) →ₗ[ℤ] M) {z : ι → ℤ} (hz : z ∈ V.intPoints) :
    φ z ∈ span ℤ (range fun i ↦ φ (b i)) := by
  have hspan : span ℤ (range fun i ↦ (b i : ι → ℤ)) = V.intPoints := by
    rw [range_comp' Subtype.val b, ← V.intPoints.coe_subtype, span_image, b.span_eq,
      map_subtype_top]
  have h := apply_mem_span_image_of_mem_span φ (hspan.symm ▸ hz : z ∈ _)
  rwa [← range_comp'] at h

/-- A basis of the integral points of `V` is linearly independent over every field of
characteristic zero. -/
theorem linearIndependent_intCast_basis_intPoints (S : Type*) [Field S] [CharZero S] :
    LinearIndependent S fun i j ↦ ((b i : ι → ℤ) j : S) := by
  have h : LinearIndependent ℤ fun i ↦ (b i : ι → ℤ) :=
    b.linearIndependent.map' V.intPoints.subtype V.intPoints.ker_subtype
  have h' := (linearIndependent_algebraMap_comp_iff (S := S) (v := fun i ↦ (b i : ι → ℤ))).2 h
  simpa [Function.comp_def] using h'

/-- A basis of the integral points of `V` spans `V` over `ℚ`. -/
theorem span_intCast_basis_intPoints : span ℚ (range fun i j ↦ ((b i : ι → ℤ) j : ℚ)) = V := by
  cases nonempty_fintype ι
  refine le_antisymm (span_le.2 ?_) fun v hv ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact (b i).2
  -- Clear the denominators of `v`.
  obtain ⟨⟨d, hd⟩, hdv⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
    Finset.univ v
  choose z hz using fun i ↦ hdv i (Finset.mem_univ i)
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  have hzv : (fun i ↦ (z i : ℚ)) = (d : ℚ) • v := by
    ext i
    simpa using hz i
  have hzV : z ∈ V.intPoints := by
    rw [mem_intPoints, hzv]
    exact V.smul_mem _ hv
  have h := span_le_restrictScalars ℤ ℚ _
    (apply_mem_span_intCast_basis_intPoints b ((Algebra.linearMap ℤ ℚ).compLeft ι) hzV)
  have hv' : v = (d : ℚ)⁻¹ • fun i ↦ (z i : ℚ) := by
    rw [hzv, inv_smul_smul₀ hd0]
  rw [hv']
  exact smul_mem _ _ h

/-- The real span of `V` is spanned by the members of a basis of its integral points. -/
private theorem realSpan_eq_span :
    V.realSpan = span ℝ (range fun i ↦ intCastEuclidean ι (b i)) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨v, hv, rfl⟩
    rw [← span_intCast_basis_intPoints b] at hv
    have h := apply_mem_span_image_of_mem_span (ratCastEuclidean ι) hv
    rw [← range_comp'] at h
    have hfun : (fun i ↦ intCastEuclidean ι (b i)) =
        ratCastEuclidean ι ∘ fun i j ↦ ((b i : ι → ℤ) j : ℚ) := by
      ext i j
      simp [ratCastEuclidean_apply, intCastEuclidean_apply]
    rw [hfun]
    exact span_le_restrictScalars ℚ ℝ _ h
  · rintro _ ⟨i, rfl⟩
    simpa [intCastEuclidean_apply] using toLp_mem_realSpan (b i).2

/-- A basis of the integral points of `V` stays linearly independent in `ℝ^ι`. -/
private theorem linearIndependent_intCastEuclidean :
    LinearIndependent ℝ fun i ↦ intCastEuclidean ι (b i) := by
  have h := (linearIndependent_intCast_basis_intPoints b ℝ).map'
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
  simpa [Function.comp_def, intCastEuclidean_apply] using h

/-- The basis of the real span of `V` given by a basis of the integral points of `V`. -/
private def realSpanBasis : Basis κ ℝ V.realSpan :=
  (Basis.span (linearIndependent_intCastEuclidean b)).map
    (LinearEquiv.ofEq _ _ (realSpan_eq_span b).symm)

private theorem coe_realSpanBasis (i : κ) :
    (realSpanBasis b i : EuclideanSpace ℝ ι) = intCastEuclidean ι (b i) := by
  simp [realSpanBasis, Basis.span_apply]

/-- The lattice of integral points of `V` is spanned by a basis of the integral points. -/
private theorem intLattice_eq_span : V.intLattice = span ℤ (range (realSpanBasis b)) := by
  refine le_antisymm (fun w hw ↦ ?_) (span_le.2 ?_)
  · obtain ⟨z, hzV, hwz⟩ := exists_mem_intPoints_of_mem_intLattice hw
    have h := apply_mem_span_intCast_basis_intPoints b (intCastEuclidean ι) hzV
    simp_rw [← coe_realSpanBasis b, ← hwz] at h
    rw [range_comp' Subtype.val, ← V.realSpan.coe_subtype, ← LinearMap.coe_restrictScalars ℤ,
      span_image] at h
    obtain ⟨u, hu, huw⟩ := mem_map.1 h
    rwa [← Subtype.ext huw]
  · rintro _ ⟨i, rfl⟩
    refine mem_intLattice.2 fun j ↦ ⟨(b i : ι → ℤ) j, ?_⟩
    simp [coe_realSpanBasis, intCastEuclidean_apply]

end Basis

/-- The integral points of `V` form a discrete subgroup of its real span. -/
instance discreteTopology_intLattice (V : Submodule ℚ (ι → ℚ)) : DiscreteTopology V.intLattice := by
  cases nonempty_fintype ι
  rw [intLattice_eq_span (Module.finBasis ℤ V.intPoints)]
  infer_instance

/-- The integral points of `V` span its real span: they form a full lattice in it. -/
instance isZLattice_intLattice [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    IsZLattice ℝ V.intLattice where
  span_top := by
    rw [intLattice_eq_span (Module.finBasis ℤ V.intPoints)]
    exact ZSpan.span_top _

/-- The integral points of `V` form a free `ℤ`-module of rank `dim V`. -/
theorem finrank_intPoints (V : Submodule ℚ (ι → ℚ)) : finrank ℤ V.intPoints = finrank ℚ V := by
  set b := Module.finBasis ℤ V.intPoints
  conv_rhs => rw [← span_intCast_basis_intPoints b]
  rw [finrank_span_eq_card (linearIndependent_intCast_basis_intPoints b ℚ), Fintype.card_fin]

/-- The real span of `V` has the dimension of `V`. -/
theorem finrank_realSpan (V : Submodule ℚ (ι → ℚ)) : finrank ℝ V.realSpan = finrank ℚ V := by
  set b := Module.finBasis ℤ V.intPoints
  rw [realSpan_eq_span b, finrank_span_eq_card (linearIndependent_intCastEuclidean b),
    Fintype.card_fin, finrank_intPoints]

/-- The map sending an integral point of `V` to the real point with the same coordinates. -/
private def intPointsToIntLattice (V : Submodule ℚ (ι → ℚ)) : V.intPoints →ₗ[ℤ] V.intLattice where
  toFun z := ⟨⟨intCastEuclidean ι z, by simpa [intCastEuclidean_apply] using toLp_mem_realSpan z.2⟩,
    fun i ↦ ⟨(z : ι → ℤ) i, by simp [intCastEuclidean_apply]⟩⟩
  map_add' z z' := by
    ext : 2
    simp
  map_smul' c z := by
    ext : 2
    exact (intCastEuclidean ι).map_smul c (z : ι → ℤ)

omit [Finite ι] in
private theorem coe_intPointsToIntLattice_apply (V : Submodule ℚ (ι → ℚ)) (z : V.intPoints) :
    ((intPointsToIntLattice V z : V.realSpan) : EuclideanSpace ℝ ι) = intCastEuclidean ι z :=
  rfl

/-- Every point of `V.intLattice` comes from exactly one integral point of `V`. -/
private theorem bijective_intPointsToIntLattice (V : Submodule ℚ (ι → ℚ)) :
    Function.Bijective (intPointsToIntLattice V) := by
  refine ⟨fun z z' h ↦ ?_, fun w ↦ ?_⟩
  · have h' := congrArg (fun w : V.intLattice ↦ ((w : V.realSpan) : EuclideanSpace ℝ ι)) h
    simp only [coe_intPointsToIntLattice_apply, intCastEuclidean_apply] at h'
    ext i
    simpa using congrArg (· i) h'
  · obtain ⟨z, hzV, hwz⟩ := exists_mem_intPoints_of_mem_intLattice w.2
    exact ⟨⟨z, hzV⟩, by ext : 2; exact hwz.symm⟩

/-- The identification of the integral points of `V` with the points of the lattice
`V.intLattice`, sending `z` to the real point with the same coordinates. It transports a
`ℤ`-basis of the lattice to a `ℤ`-basis of `V ∩ ℤ^ι`. -/
def intPointsEquivIntLattice (V : Submodule ℚ (ι → ℚ)) : V.intPoints ≃ₗ[ℤ] V.intLattice :=
  LinearEquiv.ofBijective (intPointsToIntLattice V) (bijective_intPointsToIntLattice V)

/-- The point of `V.intLattice` attached to an integral point has the same coordinates. -/
@[simp]
theorem coe_intPointsEquivIntLattice_apply (V : Submodule ℚ (ι → ℚ)) (z : V.intPoints) :
    ((V.intPointsEquivIntLattice z : V.realSpan) : EuclideanSpace ℝ ι) =
      WithLp.toLp 2 fun i ↦ ((z : ι → ℤ) i : ℝ) := by
  rw [intPointsEquivIntLattice, LinearEquiv.ofBijective_apply, coe_intPointsToIntLattice_apply,
    intCastEuclidean_apply]

/-- The integral point of `V` attached to a point of `V.intLattice` has the same coordinates. -/
@[simp]
theorem intCast_intPointsEquivIntLattice_symm_apply (V : Submodule ℚ (ι → ℚ)) (w : V.intLattice)
    (i : ι) :
    (((V.intPointsEquivIntLattice.symm w : V.intPoints) : ι → ℤ) i : ℝ) =
      ((w : V.realSpan) : EuclideanSpace ℝ ι) i := by
  conv_rhs => rw [← V.intPointsEquivIntLattice.apply_symm_apply w,
    coe_intPointsEquivIntLattice_apply]

end Submodule

end
