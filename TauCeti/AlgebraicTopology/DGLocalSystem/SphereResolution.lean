/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.CellResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Sphere
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.Basic

/-!
# The semi-free resolution of the ground ring over the chains on the loops of a sphere

Brown's twisted tensor product resolves the ground ring `R` over the chains `C_*(Ω_b B; R)` on the
Moore loops of a CW complex `B` by a semi-free module with one free generator for each cell,
attached along a cycle representing the attaching map of the cell. For a complex with one `0`-cell
`e₀` at the base point and one `(n + 1)`-cell `e₁` attached along an `n`-cycle `x` of the Moore
loops, this module is

`K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁`,  `D e₀ = 0`,  `D e₁ = x e₀`,

the free module of the cocycle `TauCeti.cycleCellCocycle R n x` of a cell attached along `x`, on
the generators `Unit ⊕ Unit` with `e₀ = Sum.inl ()` of index `0` and `e₁ = Sum.inr ()` of index
`n + 1`. That cocycle, its differential, the augmentation `ε : K → R`
(`TauCeti.loopCellAugmentation`) and the criterion below are set up in `CellResolution.lean`; the
cocycle of the circle, `TauCeti.loopCellCocycle R γ`, is its case `n = 0` and `x = [γ] - [1]`.
The augmentation vanishes on boundaries as soon as `x` has augmentation zero
(`TauCeti.loopCellAugmentation_cycleCellCocycle_differential`). It is a quasi-isomorphism as soon
as right multiplication by `x` is injective on homology and every cycle of augmentation zero is,
up to a boundary, a right multiple of `x` by a cycle
(`TauCeti.exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`): the module is
then a semi-free resolution of `R`.

For the sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell, the attaching
cycle `x` is the signed sum of the faces of the cube of Moore paths from the pole along the
characteristic map of the top cell (`TauCeti.sphereAttachingCycle`), an `(n - 1)`-cycle of the
Moore loops. Right multiplication by `x` is an isomorphism
`H_q(Ω_b Sⁿ) ≅ H_{q+n-1}(Ω_b Sⁿ)` (`TauCeti.sphereLoopHomologyMulRightEquiv`), the loops have no
homology in the degrees not divisible by `n - 1`, among them `1, …, n - 2`
(`TauCeti.isZero_homology_sphereLoop`), and they form a path
connected space, since `Sⁿ` is simply connected. So both conditions hold
(`TauCeti.exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain`,
`TauCeti.exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq`), and the module
of the sphere (`TauCeti.sphereCellCocycle`) is a semi-free resolution of the ground ring
over `C_*(Ω_b Sⁿ)`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). For `S²` the
attaching cycle has dimension `1`.

The homological conditions are stated on all of the algebra `C_*(Ω_b B; R)`, a direct sum of the
chains of every dimension, and are proved for the sphere one dimension at a time. The passage uses
the components of the differential and of right multiplication by a homogeneous chain
(`TauCeti.cubicalChainDifferential_apply`, `TauCeti.mul_cubicalChainLof_apply_add`) and of the
augmentation (`TauCeti.cubicalChainAugmentation_eq_augment`).

## Main definitions

* `TauCeti.sphereAttachingChain h k`: the attaching cycle of the top cell of the sphere, in the
  loop chain algebra.
* `TauCeti.sphereCellCocycle h k`: the cocycle of the top cell of the sphere.

## Main results

* `TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`: Brown's
  resolution of the ground ring over the chains on the loops of a sphere.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* R. Bott and H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Metric

namespace TauCeti

/-! ### The sphere -/

section Sphere

variable {ι : Type} [Fintype ι] {m : ℕ} (h : Fintype.card ι = m + 3) (k : Type) [CommRing k]

local notation "Sph" => sphere (0 : EuclideanSpace ℝ ι) 1

/-- The attaching cycle of the top cell of the sphere, as a normalized cubical chain of the Moore
loops at the pole. -/
private def sphereAttachingCycleChain :
    NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1) :=
  (((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom (sphereAttachingCycle h k)

/-- The **attaching cycle of the top cell of the sphere** `Sⁿ`, `n = m + 2`, as an element of the
loop chain algebra `C_*(Ω_b Sⁿ; k)`: the `(m + 1)`-cycle `TauCeti.sphereAttachingCycle`, the
signed sum of the faces of the cube of Moore paths from the pole along the top cell. -/
def sphereAttachingChain : loopChainAlgebra Sph (spherePolePoint h) k :=
  cubicalChainLof (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1) (sphereAttachingCycleChain h k)

/-- The attaching chain is the image of the attaching cycle `TauCeti.sphereAttachingCycle` in the
loop chain algebra; this connects it to `TauCeti.sphereLoopHomologyMulRightEquiv`. -/
theorem sphereAttachingChain_def :
    sphereAttachingChain h k = cubicalChainLof (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1)
      ((((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom
        (sphereAttachingCycle h k)) :=
  (rfl)

/-- The attaching cycle has dimension `m + 1`. -/
theorem sphereAttachingChain_mem :
    sphereAttachingChain h k ∈
      cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k (-((m + 1 : ℕ) : ℤ)) :=
  cubicalChainLof_mem _ _ _

/-- The attaching cycle is a cycle. -/
@[simp]
theorem cubicalChainDifferential_sphereAttachingChain :
    cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (sphereAttachingChain h k) = 0 :=
  cubicalChainDifferential_lof_iCycles (Y := MooreLoopSpace Sph (spherePolePoint h)) (m + 1)
    (sphereAttachingCycle h k)

/-- The attaching cycle has augmentation zero, being of positive dimension. -/
@[simp]
theorem loopChainAugmentation_sphereAttachingChain :
    loopChainAugmentation Sph (spherePolePoint h) k (sphereAttachingChain h k) = 0 :=
  loopChainAugmentation_lof_succ _ _

/-- **Brown's cocycle of the sphere** `Sⁿ`, `n = m + 2`: one `0`-cell at the pole and
one `n`-cell attached along the attaching cycle `TauCeti.sphereAttachingChain h k`. Its free
module is a semi-free resolution of `k` over `C_*(Ω_b Sⁿ; k)`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). It is
reducible to the cocycle `TauCeti.cycleCellCocycle` of a cell attached along that cycle, so the
lemmas about the latter, such as `TauCeti.cycleCellCocycle_differential_apply`, apply to it. -/
abbrev sphereCellCocycle :
    RowFiniteTwistingCocycle (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ ((m + 1 : ℕ) : ℤ) + 1)) :=
  cycleCellCocycle k (m + 1) (sphereAttachingChain h k) (sphereAttachingChain_mem h k)
    (cubicalChainDifferential_sphereAttachingChain h k)

/-- A cycle `y` of dimension `j` of the loops of the sphere whose product with the attaching
cycle is a boundary is a boundary, since right multiplication by the attaching class is injective
on homology. -/
private theorem exists_boundary_eq_of_boundary_eq_mul {j : ℕ}
    {y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k j}
    (hy : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k j y) = 0)
    {w : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (j + (m + 1) + 1)}
    (hw : NormalizedCubicalChain.boundary _ k (j + (m + 1)) w =
      NormalizedCubicalChain.mul _ k j (m + 1) y (sphereAttachingCycleChain h k)) :
    ∃ y' : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (j + 1),
      NormalizedCubicalChain.boundary _ k j y' = y := by
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero j hy
  have hdw : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (j + (m + 1)) (NormalizedCubicalChain.boundary _ k (j + (m + 1)) w)) =
        0 := by
    rw [← cubicalChainDifferential_lof_succ]
    exact (loopChain_isDGAlgebra Sph (spherePolePoint h) k).sq_zero _
  obtain ⟨wc, hwc⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ hdw
  -- `sphereLoopHomologyMulRightEquiv_homologyπ` takes these equations in the `iCycles` form.
  have hz' := hz
  have hwc' := hwc
  rw [normalizedCubicalChainComplexXEquiv_apply] at hz' hwc'
  -- The class of the product vanishes, so the class of `y` does.
  have hπz : ((normalizedCubicalChainComplex k).obj _).homologyπ j z =
      ((normalizedCubicalChainComplex k).obj _).homologyπ j 0 := by
    apply (sphereLoopHomologyMulRightEquiv h k j).injective
    rw [map_zero, map_zero, sphereLoopHomologyMulRightEquiv_homologyπ h k j z wc
      (hwc'.trans (hw.trans (congrArg (fun t ↦ NormalizedCubicalChain.mul _ k j (m + 1) t
        (sphereAttachingCycleChain h k)) hz'.symm))),
      ← map_zero (((normalizedCubicalChainComplex k).obj _).homologyπ _).hom]
    exact (normalizedCubicalChainComplex_homologyπ_eq_iff _ wc 0).2 ⟨w, by simp [hwc]⟩
  obtain ⟨y', hy'⟩ := (normalizedCubicalChainComplex_homologyπ_eq_iff j z 0).1 hπz
  exact ⟨y', by simpa [hz] using hy'⟩

/-- **Right multiplication by the attaching cycle of the sphere is injective on homology**: a
cycle `β` of the loop chain algebra of `Sⁿ` such that `β x` is a boundary is a boundary. -/
theorem exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain
    {β w : loopChainAlgebra Sph (spherePolePoint h) k}
    (hβ : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0)
    (hw : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w =
      β * sphereAttachingChain h k) :
    ∃ γ, cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k γ = β := by
  classical
  -- Each component `β j` is the boundary of some `γ j`.
  have key (j : ℕ) : ∃ y' : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k
      (j + 1), NormalizedCubicalChain.boundary _ k j y' = β j := by
    refine exists_boundary_eq_of_boundary_eq_mul h k
      (cubicalChainDifferential_lof_apply_eq_zero hβ j) (w := w (j + (m + 1) + 1)) ?_
    rw [← cubicalChainDifferential_apply, hw, sphereAttachingChain, mul_cubicalChainLof_apply_add]
  choose γ hγ using key
  refine ⟨∑ j ∈ β.support, cubicalChainLof _ k (j + 1) (γ j), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← DirectSum.sum_support_of β]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cubicalChainDifferential_lof_succ, hγ, DirectSum.lof_eq_of]

/-- A cycle of dimension `i + 1 ≤ m` of the loops of the sphere is a boundary. -/
private theorem exists_boundary_eq_of_lt {i : ℕ} (hi : i < m)
    {a : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + 1)}
    (ha : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + 1) a) = 0) :
    ∃ w : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + 2),
      NormalizedCubicalChain.boundary _ k (i + 1) w = a := by
  rw [cubicalChainDifferential_lof_succ] at ha
  exact NormalizedCubicalChain.exists_boundary_eq_of_isZero_homology
    (X := TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))
    (isZero_homology_sphereLoop h k (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    (DirectSum.of_injective (β := fun n ↦ NormalizedCubicalChain _ k n) i
      (by simpa [DirectSum.lof_eq_of] using ha))

/-- A cycle `a` of dimension `i + m + 1` of the loops of the sphere is, up to a boundary, the
product `y x` of a cycle `y` of dimension `i` with the attaching cycle, since right
multiplication by the attaching class is onto on homology. -/
private theorem exists_mul_add_boundary_eq {i : ℕ}
    {a : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + (m + 1))}
    (ha : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + (m + 1)) a) = 0) :
    ∃ (y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k i)
      (c : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + (m + 1) + 1)),
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
        (cubicalChainLof _ k i y) = 0 ∧
      NormalizedCubicalChain.mul _ k i (m + 1) y (sphereAttachingCycleChain h k) +
        NormalizedCubicalChain.boundary _ k (i + (m + 1)) c = a := by
  let X := TopCat.of (MooreLoopSpace Sph (spherePolePoint h))
  let K := (normalizedCubicalChainComplex k).obj X
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ ha
  -- A cycle `y` of dimension `i` whose product with the attaching class is the class of `a`.
  obtain ⟨z', hz'⟩ := K.moduleCat_homologyπ_surjective i
    ((sphereLoopHomologyMulRightEquiv h k i).symm (K.homologyπ (i + (m + 1)) z))
  obtain ⟨y, hy⟩ : ∃ y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k i,
      (K.iCycles i).hom z' = y := ⟨_, rfl⟩
  have hdy : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k i y) = 0 :=
    hy ▸ cubicalChainDifferential_lof_iCycles i z'
  have hdp : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + (m + 1))
        (NormalizedCubicalChain.mul _ k i (m + 1) y (sphereAttachingCycleChain h k))) = 0 := by
    rw [← cubicalChainLof_mul, ← sphereAttachingChain]
    exact IsNonUnitalDGAlgebra.map_mul_eq_zero_of_map_eq_zero
      (loopChain_isDGAlgebra Sph (spherePolePoint h) k).toIsNonUnitalDGAlgebra hdy
      (cubicalChainDifferential_sphereAttachingChain h k)
  obtain ⟨wc, hwc⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ hdp
  -- `sphereLoopHomologyMulRightEquiv_homologyπ` takes this equation in the `iCycles` form.
  have hwc' := hwc
  rw [normalizedCubicalChainComplexXEquiv_apply] at hwc'
  have hπ : K.homologyπ (i + (m + 1)) wc = K.homologyπ (i + (m + 1)) z := by
    rw [← sphereLoopHomologyMulRightEquiv_homologyπ h k i z' wc
      (hwc'.trans (congrArg (fun t ↦ NormalizedCubicalChain.mul _ k i (m + 1) t
        (sphereAttachingCycleChain h k)) hy.symm)), hz', LinearEquiv.apply_symm_apply]
  obtain ⟨c', hbc⟩ := (normalizedCubicalChainComplex_homologyπ_eq_iff _ wc z).1 hπ
  rw [hwc, hz] at hbc
  refine ⟨y, -c', hdy, ?_⟩
  rw [map_neg, hbc]
  abel

/-- **Cycles of the loops of the sphere are right multiples of the attaching cycle**: every cycle
`α` of the loop chain algebra of `Sⁿ` with augmentation zero is `β x + d w` for a cycle `β`. -/
theorem exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq
    {α : loopChainAlgebra Sph (spherePolePoint h) k}
    (hα : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k α = 0)
    (hε : loopChainAugmentation Sph (spherePolePoint h) k α = 0) :
    ∃ β w : loopChainAlgebra Sph (spherePolePoint h) k,
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0 ∧
      β * sphereAttachingChain h k +
        cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w = α := by
  classical
  -- Each homogeneous component of `α` is `β x + d w`.
  have key (j : ℕ) : ∃ β w : loopChainAlgebra Sph (spherePolePoint h) k,
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0 ∧
      β * sphereAttachingChain h k +
        cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w =
          cubicalChainLof _ k j (α j) := by
    have hj := cubicalChainDifferential_lof_apply_eq_zero hα j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : SimplyConnectedSpace Sph :=
        simplyConnectedSpace_sphere_of_lt_finrank (by simp [finrank_euclideanSpace, h]) 0
          zero_le_one
      obtain ⟨w, hw⟩ := loopZeroChain_mem_range_boundary_of_augment_eq_zero
        (by rwa [loopChainAugmentation_def, cubicalChainAugmentation_eq_augment] at hε)
      exact ⟨0, cubicalChainLof _ k 1 w, map_zero _, by
        rw [zero_mul, zero_add, cubicalChainDifferential_lof_succ, hw]⟩
    by_cases hjm : j ≤ m
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨w, hw⟩ := exists_boundary_eq_of_lt h k (by omega) hj
      exact ⟨0, cubicalChainLof _ k (i + 2) w, map_zero _, by
        rw [zero_mul, zero_add, cubicalChainDifferential_lof_succ, hw]⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + (m + 1) := ⟨j - (m + 1), by omega⟩
      obtain ⟨y, c, hy, hyc⟩ := exists_mul_add_boundary_eq h k hj
      exact ⟨cubicalChainLof _ k i y, cubicalChainLof _ k (i + (m + 1) + 1) c, hy, by
        rw [sphereAttachingChain, cubicalChainLof_mul, cubicalChainDifferential_lof_succ,
          ← map_add, hyc]⟩
  choose β w hβ hw using key
  refine ⟨∑ j ∈ α.support, β j, ∑ j ∈ α.support, w j,
    by rw [map_sum]; exact Finset.sum_eq_zero fun j _ ↦ hβ j, ?_⟩
  rw [Finset.sum_mul, map_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [← DirectSum.sum_support_of α]
  exact Finset.sum_congr rfl fun j _ ↦ (hw j).trans (DirectSum.lof_eq_of _ _ _ _ _)

/-- **Brown's resolution of the ground ring over the chains on the loops of a sphere.** For the
sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell attached along the
attaching cycle `x` of its top cell, every cycle of the free module of
`TauCeti.sphereCellCocycle h k` whose augmentation vanishes is a boundary. Since the augmentation
vanishes on boundaries and takes the value `1` on the cycle `e₀`, it is a quasi-isomorphism onto
`k`: the module `C_*(Ω_b Sⁿ; k) e₀ ⊕ C_*(Ω_b Sⁿ; k) e₁` with `D e₁ = x e₀` is a semi-free
resolution of `k` over the chains `C_*(Ω_b Sⁿ; k)` on the Moore loops. -/
theorem exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero
    {u : Unit ⊕ Unit →₀ loopChainAlgebra Sph (spherePolePoint h) k}
    (hu : rowFiniteTwistedDifferential (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (d := cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (sphereCellCocycle h k).m u = 0)
    (hε : loopCellAugmentation Sph (spherePolePoint h) k u = 0) :
    ∃ v, rowFiniteTwistedDifferential (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (d := cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (sphereCellCocycle h k).m v = u :=
  exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero _ _
    (loopChainAugmentation_sphereAttachingChain h k)
    (fun _ _ hβ hw ↦
      exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain
        h k hβ hw)
    (fun _ hα hε ↦ exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq h k hα hε)
    hu hε

end Sphere

end TauCeti
