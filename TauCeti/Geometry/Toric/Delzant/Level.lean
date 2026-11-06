/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Toric.Delzant.Torus

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Fredholm.Basic

/-!
# The level set of the Delzant construction

Let `i : N →+ V` be an integral lattice and let `(u, c)` be the facet presentation of a Delzant
polytope `Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`, with `d` facets indexed by `ι`. The
Delzant construction realizes `Δ` as the moment polytope of a symplectic toric manifold, the
symplectic reduction of `ℂ^ι` by the kernel torus `N_Δ` of `(ℝ / 2πℤ)^ι → V / 2π i(N)`, whose Lie
algebra is the kernel `𝔫` of `β_ℝ : ℝ^ι → V`, `t ↦ ∑ j, t j • i (u j)`.

This file constructs the level set of that reduction and proves its basic properties. On `ℂ^ι`,
written in real coordinates `z_j = q_j + i p_j` as `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, the
torus acts by the *reversed* rotations `z_j ↦ e^(-i t_j) z_j` (`TauCeti.weightRotation (-t)`), with
moment map

`μ(z) = (½ |z_j|² + c j)_j ∈ (ℝ^ι)*`

(`TauCeti.Toric.delzantMomentMap c`). Its Hamiltonian vector fields are the generators of the
reversed rotations (`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`), in the convention
`ι_{X_H} ω = dH`. The moment map of the subtorus `N_Δ` is the restriction of `μ` to `𝔫`, read
here in the coordinates of the basis `Module.finBasis ℝ 𝔫` (`TauCeti.Toric.delzantLevelMap i u c`),
and the **Delzant level set** is its zero set

`Z = {z | μ(z) vanishes on 𝔫}` (`TauCeti.Toric.delzantLevel i u c`),

which does not depend on the basis (`TauCeti.Toric.mem_delzantLevel_iff_forall`).

The main results:

* `μ(z)` vanishes on `𝔫 = ker β_ℝ` exactly when it factors through `β_ℝ`, so `z ∈ Z` exactly
  when there is `y ∈ V*` with `½ |z_j|² + c j = ⟨y, u j⟩` for every `j`
  (`TauCeti.Toric.mem_delzantLevel_iff`). Such a `y` lies in `Δ`, its active constraints are the
  coordinates with `z_j = 0`, and every point of `Δ` arises this way, so `Z` is nonempty exactly
  when `Δ` is (`TauCeti.Toric.nonempty_delzantLevel`). In the Delzant construction
  `y` is the value at the orbit of `z` of the moment map of the residual torus, which is why the
  reduced space has moment image `Δ`.
* `Z` is invariant under every rotation of `ℂ^ι`, closed, and compact when `Δ` is bounded
  (`TauCeti.Toric.isCompact_delzantLevel`).
* `N_Δ` acts freely on `Z` (`TauCeti.Toric.IsDelzant.weightRotation_neg_apply_eq_self_iff`): the
  stabilizer of `z` in `(ℝ / 2πℤ)^ι` is the coordinate subtorus of the coordinates with `z_j = 0`,
  which are the constraints active at the corresponding point of `Δ`, and the kernel torus meets
  it trivially (`TauCeti.Toric.IsDelzant.eq_zero_of_mem_ker_facetTorusHom`). Infinitesimally, `𝔫`
  acts locally freely on `Z`
  (`TauCeti.Toric.IsDelzant.weightGenerator_neg_apply_eq_zero_iff`).
* `0` is a regular value of the moment map of `N_Δ`
  (`TauCeti.Toric.IsDelzant.surjective_fderiv_delzantLevelMap`), so `Z` is a smooth manifold of
  dimension `2d - (d - n) = d + n`, where `n = dim V`
  (`TauCeti.Toric.IsDelzant.isManifold_delzantLevel`).

## Main definitions

* `TauCeti.Toric.delzantMomentMap c`: the moment map `z ↦ (½ |z_j|² + c j)_j` of the reversed
  standard action of `ℝ^ι` on `ℂ^ι`.
* `TauCeti.Toric.delzantLevelMap i u c`: its restriction to the Lie algebra `𝔫` of the kernel
  torus, in the coordinates of the basis `Module.finBasis ℝ 𝔫`.
* `TauCeti.Toric.delzantLevel i u c`: the level set `Z`, the zero set of `delzantLevelMap`.
* `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`: the implicit-function atlas of `Z`, modelled
  on `Fin (d + n) → ℝ`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Function Module Set Real
open scoped Manifold

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N]

/-! ### The moment map of the reversed standard action -/

section MomentMap

variable (c : ι → ℝ)

/-- The moment map `μ(z)_j = ½ |z_j|² + c j` of the reversed standard action
`z_j ↦ e^(-i t_j) z_j` of `ℝ^ι` on `ℂ^ι`, shifted by the support constants `c`. It is the weight
model moment map for the weights `-e_j`, plus the constant `c`. -/
def delzantMomentMap (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : StrongDual ℝ (ι → ℝ) :=
  weightMomentMap (fun j ↦ -ContinuousLinearMap.proj j) x + ∑ j, c j • ContinuousLinearMap.proj j

@[simp]
theorem delzantMomentMap_apply (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (t : ι → ℝ) :
    delzantMomentMap c x t = ∑ j, ((x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j) * t j := by
  simp only [delzantMomentMap, add_apply, weightMomentMap_apply, neg_apply,
    ContinuousLinearMap.proj_apply, _root_.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The moment map is invariant under every rotation of `ℂ^ι`. -/
@[simp]
theorem delzantMomentMap_weightRotation (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    delzantMomentMap c (weightRotation θ x) = delzantMomentMap c x := by
  simp only [delzantMomentMap, weightMomentMap_weightRotation]

/-- **The reversed standard action is Hamiltonian.** The Hamiltonian vector field of the component
`⟨μ, t⟩` of the moment map is the generator of the reversed rotation `z_j ↦ e^(-i t_j) z_j`. -/
theorem hamiltonianVectorField_delzantMomentMap (t : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    stdSymplecticForm.hamiltonianVectorField (fun y ↦ delzantMomentMap c y t) x =
      weightGenerator (-t) x := by
  have h : (fun y ↦ delzantMomentMap c y t) =
      fun y ↦ weightMomentMap (fun j ↦ -ContinuousLinearMap.proj j) y t + ∑ j, c j * t j := by
    funext y
    simp [delzantMomentMap]
  rw [h, SymplecticForm.hamiltonianVectorField_def, fderiv_add_const,
    ← SymplecticForm.hamiltonianVectorField_def, hamiltonianVectorField_weightMomentMap]
  congr 1

end MomentMap

/-! ### Points of the level set and points of the polytope -/

section Polytope

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ}
  {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {y : StrongDual ℝ V}

omit [Fintype ι] in
/-- If `½ |z_j|² + c j = ⟨y, u j⟩` for every `j`, then `y` lies in the facet polyhedron. -/
theorem mem_facetPolyhedron_of_forall_eq
    (h : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) : y ∈ facetPolyhedron i u c :=
  mem_facetPolyhedron.2 fun j ↦ by
    rw [← h j]
    have : 0 ≤ x.1 j ^ 2 + x.2 j ^ 2 := by positivity
    linarith

omit [Fintype ι] in
/-- If `½ |z_j|² + c j = ⟨y, u j⟩` for every `j`, then the constraints active at `y` are the
coordinates with `z_j = 0`. -/
theorem activeSet_eq_of_forall_eq
    (h : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    activeSet (facetPairing i u) c y = {j | x.1 j = 0 ∧ x.2 j = 0} := by
  ext j
  rw [mem_activeSet, facetPairing_apply, ← h j, mem_ofPred_eq]
  constructor
  · intro hj
    have h₁ : x.1 j ^ 2 + x.2 j ^ 2 = 0 := by linarith
    exact ⟨by nlinarith [sq_nonneg (x.1 j), sq_nonneg (x.2 j)],
      by nlinarith [sq_nonneg (x.1 j), sq_nonneg (x.2 j)]⟩
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]

omit [Fintype ι] in
/-- **Every point of the facet polyhedron comes from `ℂ^ι`.** A point `y ∈ V*` satisfies
`⟨y, u j⟩ = ½ |z_j|² + c j` for every `j`, for some `z`, exactly when it lies in the facet
polyhedron. -/
theorem exists_forall_eq_iff_mem_facetPolyhedron :
    (∃ x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) ↔ y ∈ facetPolyhedron i u c := by
  refine ⟨fun ⟨x, hx⟩ ↦ mem_facetPolyhedron_of_forall_eq hx, fun hy ↦ ?_⟩
  refine ⟨(WithLp.toLp 2 fun j ↦ √(2 * (y (i (u j)) - c j)), 0), fun j ↦ ?_⟩
  have hj : 0 ≤ 2 * (y (i (u j)) - c j) := by
    have := mem_facetPolyhedron.1 hy j
    linarith
  simp only [Real.sq_sqrt hj, PiLp.zero_apply]
  ring

end Polytope

/-! ### The level set -/

section Level

variable [NormedAddCommGroup V] [NormedSpace ℝ V] (i : N →+ V) (u : ι → N) (c : ι → ℝ)

/-- The moment map of the kernel torus, in coordinates: the components `⟨μ(z), b a⟩` of the
restriction of `TauCeti.Toric.delzantMomentMap c` to the Lie algebra `𝔫 = ker β_ℝ` of the kernel
torus, where `β_ℝ t = ∑ j, t j • i (u j)`, in the basis `b = Module.finBasis ℝ 𝔫`. Its zero set,
the Delzant level set, does not depend on the basis (`TauCeti.Toric.mem_delzantLevel_iff_forall`).
-/
def delzantLevelMap (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Fin (finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)))) → ℝ :=
  fun a ↦ delzantMomentMap c x (Module.finBasis ℝ (LinearMap.ker
    (Fintype.linearCombination ℝ fun j ↦ i (u j))) a)

@[simp]
theorem delzantLevelMap_apply (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (a : Fin (finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))))) :
    delzantLevelMap i u c x a = delzantMomentMap c x (Module.finBasis ℝ (LinearMap.ker
      (Fintype.linearCombination ℝ fun j ↦ i (u j))) a) :=
  (rfl)

/-- The **Delzant level set**: the points of `ℂ^ι` at which the moment map of the kernel torus
vanishes, that is, at which `μ` vanishes on `𝔫 = ker β_ℝ`
(`TauCeti.Toric.mem_delzantLevel_iff_forall`). Its quotient by the kernel torus is the symplectic
toric manifold of the Delzant construction. -/
def delzantLevel : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  {x | delzantLevelMap i u c x = 0}

variable {i u c}

/-- A point lies in the Delzant level set exactly when `μ` vanishes on the kernel of `β_ℝ`. -/
theorem mem_delzantLevel_iff_forall {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    x ∈ delzantLevel i u c ↔
      ∀ t, Fintype.linearCombination ℝ (fun j ↦ i (u j)) t = 0 → delzantMomentMap c x t = 0 := by
  simp only [delzantLevel, mem_ofPred_eq, funext_iff, delzantLevelMap_apply, Pi.zero_apply]
  refine ⟨fun h t ht ↦ ?_, fun h a ↦ h _ (Module.finBasis ℝ _ a).2⟩
  -- The restriction of `μ(z)` to `𝔫` vanishes on the basis `Module.finBasis ℝ 𝔫`.
  have h0 := (Module.finBasis ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)))).ext
    (f₁ := ((delzantMomentMap c x : (ι → ℝ) →L[ℝ] ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.ker _).subtype) (f₂ := 0) fun a ↦ by simpa using h a
  simpa using LinearMap.congr_fun h0 ⟨t, ht⟩

/-- **Points of the Delzant level set.** A point `z` lies in the level set exactly when there is
`y ∈ V*` with `½ |z_j|² + c j = ⟨y, u j⟩` for every `j`: `μ(z)` vanishes on the kernel of `β_ℝ`
exactly when it factors through `β_ℝ`. Such a `y` lies in the polytope
(`TauCeti.Toric.mem_facetPolyhedron_of_forall_eq`). -/
theorem mem_delzantLevel_iff [FiniteDimensional ℝ V]
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    x ∈ delzantLevel i u c ↔
      ∃ y : StrongDual ℝ V, ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j)) := by
  classical
  set β := Fintype.linearCombination ℝ fun j ↦ i (u j)
  rw [mem_delzantLevel_iff_forall]
  constructor
  · intro hx
    have hmem : ((delzantMomentMap c x : (ι → ℝ) →L[ℝ] ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ) ∈
        (LinearMap.ker β).dualAnnihilator :=
      (Submodule.mem_dualAnnihilator _).2 fun t ht ↦ hx t ht
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨y, hy⟩ := hmem
    refine ⟨LinearMap.toContinuousLinearMap y, fun j ↦ ?_⟩
    have hj := LinearMap.congr_fun hy (Pi.single j 1)
    simp only [LinearMap.dualMap_apply, Fintype.linearCombination_apply_single, one_smul,
      ContinuousLinearMap.coe_coe, delzantMomentMap_apply, β] at hj
    rw [LinearMap.coe_toContinuousLinearMap', hj]
    simp [Pi.single_apply]
  · rintro ⟨y, hy⟩ t ht
    rw [delzantMomentMap_apply]
    simp_rw [hy, mul_comm (y _), ← smul_eq_mul, ← map_smul, ← map_sum]
    rw [← Fintype.linearCombination_apply, ht, map_zero]

/-- The Delzant level set is nonempty exactly when the facet polyhedron is nonempty. -/
theorem nonempty_delzantLevel [FiniteDimensional ℝ V] :
    (delzantLevel i u c).Nonempty ↔ (facetPolyhedron i u c).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
    exact ⟨y, mem_facetPolyhedron_of_forall_eq hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_forall_eq_iff_mem_facetPolyhedron.2 hy
    exact ⟨x, mem_delzantLevel_iff.2 ⟨y, hx⟩⟩

/-- The Delzant level set is invariant under every rotation of `ℂ^ι`. -/
@[simp]
theorem weightRotation_mem_delzantLevel_iff (θ : ι → ℝ)
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    weightRotation θ x ∈ delzantLevel i u c ↔ x ∈ delzantLevel i u c := by
  simp only [mem_delzantLevel_iff_forall, delzantMomentMap_weightRotation]

variable (i u c) in
/-- The moment map of the kernel torus is a quadratic polynomial: its component `a` is
`∑ j, (½ |z_j|² + c j) (b a)_j`. -/
private theorem delzantLevelMap_eq_sum : delzantLevelMap i u c = fun x ↦
    ∑ j, (2⁻¹ * (x.1 j ^ 2 + x.2 j ^ 2) + c j) • fun a ↦ (Module.finBasis ℝ (LinearMap.ker
      (Fintype.linearCombination ℝ fun j ↦ i (u j))) a : ι → ℝ) j := by
  funext x a
  simp only [delzantLevelMap_apply, delzantMomentMap_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

variable (i u c) in
/-- The moment map of the kernel torus is smooth, indeed analytic. -/
theorem contDiff_delzantLevelMap {m : WithTop ℕ∞} : ContDiff ℝ m (delzantLevelMap i u c) := by
  refine contDiff_pi.2 fun a ↦ ?_
  simp only [delzantLevelMap_apply, delzantMomentMap_apply]
  fun_prop

/-- The Delzant level set is closed. -/
theorem isClosed_delzantLevel : IsClosed (delzantLevel i u c) :=
  isClosed_eq (contDiff_delzantLevelMap i u c (m := 0)).continuous continuous_const

/-- **The Delzant level set is compact** when the facet polyhedron is bounded, in particular for a
Delzant polytope: a point `z` of the level set has `|z_j|² = 2 (⟨y, u j⟩ - c j)` for a point `y`
of the polytope. -/
theorem isCompact_delzantLevel [FiniteDimensional ℝ V]
    (h : Bornology.IsBounded (facetPolyhedron i u c)) : IsCompact (delzantLevel i u c) := by
  obtain ⟨R, hR⟩ := h.exists_norm_le
  -- Each coordinate `|z_j|²` is at most `B j = 2 (R ‖i (u j)‖ - c j)`.
  set B : ι → ℝ := fun j ↦ 2 * (R * ‖i (u j)‖ - c j)
  have hB {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} (hx : x ∈ delzantLevel i u c) (j : ι) :
      x.1 j ^ 2 + x.2 j ^ 2 ≤ B j := by
    obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
    have h₁ : y (i (u j)) ≤ R * ‖i (u j)‖ :=
      (le_abs_self _).trans <| (y.le_opNorm _).trans <|
        mul_le_mul_of_nonneg_right (hR y (mem_facetPolyhedron_of_forall_eq hy)) (norm_nonneg _)
    have h₂ := hy j
    simp only [B]
    linarith
  refine Metric.isCompact_of_isClosed_isBounded isClosed_delzantLevel ?_
  refine (Metric.isBounded_closedBall (x := 0) (r := √(∑ j, B j))).subset fun x hx ↦ ?_
  have hsum {w : EuclideanSpace ℝ ι} (hw : ∀ j, w j ^ 2 ≤ B j) : ‖w‖ ≤ √(∑ j, B j) := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ ↦ by simpa using hw j)
  rw [mem_closedBall_zero_iff, norm_prod_le_iff]
  exact ⟨hsum fun j ↦ by nlinarith [hB hx j, sq_nonneg (x.2 j)],
    hsum fun j ↦ by nlinarith [hB hx j, sq_nonneg (x.1 j)]⟩

/-- The derivative of the moment map of the kernel torus: its component `a` at `z = (q, p)` is
`(δq, δp) ↦ ∑ j, (q_j δq_j + p_j δp_j) (b a)_j`. -/
theorem fderiv_delzantLevelMap_apply_apply (x v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (a : Fin (finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))))) :
    fderiv ℝ (delzantLevelMap i u c) x v a = ∑ j, (x.1 j * v.1 j + x.2 j * v.2 j) *
      (Module.finBasis ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) a :
        ι → ℝ) j := by
  set b := Module.finBasis ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)))
  have h : HasFDerivAt (delzantLevelMap i u c) (∑ j, ContinuousLinearMap.smulRight
      (x.1 j • (PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.fst ℝ _ _) +
        x.2 j • (PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _))
      fun a ↦ (b a : ι → ℝ) j) x := by
    rw [delzantLevelMap_eq_sum]
    refine HasFDerivAt.fun_sum fun j _ ↦ ?_
    have h₁ : HasFDerivAt (fun y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ y.1 j)
        ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.fst ℝ _ _)) x :=
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x.1 j).comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
    have h₂ : HasFDerivAt (fun y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ y.2 j)
        ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _)) x :=
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x.2 j).comp x (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
    refine (HasFDerivAt.smul_const (HasFDerivAt.add_const (c j) (HasFDerivAt.const_mul
      (HasFDerivAt.add (h₁.pow 2) (h₂.pow 2)) 2⁻¹)) fun a ↦ (b a : ι → ℝ) j).congr_fderiv ?_
    ext v a <;>
      simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_add,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.smulRight_apply, add_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', PiLp.proj_apply,
        PiLp.zero_apply, smul_eq_mul, mul_zero, add_zero, zero_add, Pi.smul_apply] <;>
      ring
  rw [h.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', PiLp.proj_apply, smul_eq_mul, Pi.smul_apply]

end Level

/-! ### Freeness and regularity for a Delzant polytope -/

section Delzant

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **The kernel torus acts freely on the Delzant level set.** Let `[t] ∈ (ℝ / 2πℤ)^ι` lie in the
kernel torus. Then the reversed rotation by `t` fixes a point `z` of the level set only when
`[t] = 0`: the stabilizer of `z` is the coordinate subtorus of the coordinates with `z_j = 0`, and
these are the constraints active at a point of the polytope. -/
theorem weightRotation_neg_apply_eq_self_iff (hx : x ∈ delzantLevel i u c) {t : ι → ℝ}
    (ht : (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker) :
    weightRotation (-t) x = x ↔ (fun j ↦ (t j : AddCircle (2 * π))) = 0 := by
  rw [weightRotation_apply_eq_self_iff]
  constructor
  · intro hfix
    obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
    refine hΔ.eq_zero_of_mem_ker_facetTorusHom hi (mem_facetPolyhedron_of_forall_eq hy) ht
      fun j hj ↦ ?_
    rw [activeSet_eq_of_forall_eq hy, mem_ofPred_eq, not_and_or] at hj
    obtain ⟨k, hk⟩ := hfix j hj
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨-k, by rw [neg_smul, zsmul_eq_mul, hk, Pi.neg_apply, neg_neg]⟩
  · intro h0 j _
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (2 * π)).1 (congr_fun h0 j)
    exact ⟨-k, by rw [Pi.neg_apply, ← hk, zsmul_eq_mul, Int.cast_neg, neg_mul]⟩

/-- **The Lie algebra of the kernel torus acts locally freely on the Delzant level set.** An
element `t` of `𝔫 = ker β_ℝ` generates a vector field vanishing at a point of the level set only
when `t = 0`. -/
theorem weightGenerator_neg_apply_eq_zero_iff (hx : x ∈ delzantLevel i u c) {t : ι → ℝ}
    (ht : Fintype.linearCombination ℝ (fun j ↦ i (u j)) t = 0) :
    weightGenerator (-t) x = 0 ↔ t = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, weightGenerator_apply_eq_zero_iff]⟩
  rw [weightGenerator_apply_eq_zero_iff] at h
  obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
  -- In the vector group `AddCircle 0 = ℝ`, the class of `t` is in the kernel of `β_ℝ`.
  have hker : (fun j ↦ (t j : AddCircle (0 : ℝ))) ∈ (facetTorusHom i u 0).ker := by
    rw [AddMonoidHom.mem_ker, facetTorusHom_coe, ht, QuotientAddGroup.mk_zero]
  have h0 := hΔ.eq_zero_of_mem_ker_facetTorusHom hi (mem_facetPolyhedron_of_forall_eq hy) hker
    fun j hj ↦ by
      rw [activeSet_eq_of_forall_eq hy, mem_ofPred_eq, not_and_or] at hj
      simpa using h j hj
  funext j
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (0 : ℝ)).1 (congr_fun h0 j)
  simpa using hk.symm

/-- **The level set is regular.** At every point of the Delzant level set, the derivative of the
moment map of the kernel torus, read in coordinates on `𝔫*`, is surjective, so `0` is a regular
value. -/
theorem surjective_fderiv_delzantLevelMap (hx : x ∈ delzantLevel i u c) :
    Surjective (fderiv ℝ (delzantLevelMap i u c) x) := by
  classical
  set 𝔫 := LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))
  set b := Module.finBasis ℝ 𝔫
  set S := {j | x.1 j ≠ 0 ∨ x.2 j ≠ 0}
  -- An element of `𝔫` is determined by its coordinates on the support `S` of `x`.
  let r : 𝔫 →ₗ[ℝ] S → ℝ := LinearMap.pi fun j ↦ (LinearMap.proj (j : ι)).comp 𝔫.subtype
  have hr : LinearMap.ker r = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun t ht ↦ Subtype.ext ?_
    refine (hΔ.weightGenerator_neg_apply_eq_zero_iff hi hx t.2).1 ?_
    rw [weightGenerator_apply_eq_zero_iff]
    intro j hj
    simpa [r] using congr_fun ht ⟨j, hj⟩
  obtain ⟨g, hg⟩ := r.exists_leftInverse_of_injective hr
  intro w
  -- The linear functional on `𝔫` with values `w` on the basis `b`.
  set φ : 𝔫 →ₗ[ℝ] ℝ := b.constr ℝ w
  -- Prescribe the radial derivative of `|z_j|²` on the support `S`.
  let a : ι → ℝ := fun j ↦
    if hj : j ∈ S then φ (g (Pi.single ⟨j, hj⟩ 1)) / (x.1 j ^ 2 + x.2 j ^ 2) else 0
  refine ⟨(WithLp.toLp 2 fun j ↦ a j * x.1 j, WithLp.toLp 2 fun j ↦ a j * x.2 j),
    funext fun k ↦ ?_⟩
  rw [fderiv_delzantLevelMap_apply_apply, show w k = φ (b k) by simp [φ]]
  set t := b k
  have hterm (j : ι) : (x.1 j * (a j * x.1 j) + x.2 j * (a j * x.2 j)) * (t : ι → ℝ) j =
      if hj : j ∈ S then (t : ι → ℝ) j * φ (g (Pi.single ⟨j, hj⟩ 1)) else 0 := by
    by_cases hj : j ∈ S
    · have hpos : x.1 j ^ 2 + x.2 j ^ 2 ≠ 0 := by
        rcases hj with h | h <;> positivity
      simp only [a, hj, dite_true]
      field_simp
    · obtain ⟨h₁, h₂⟩ : x.1 j = 0 ∧ x.2 j = 0 := by simpa [S, not_or] using hj
      simp [hj, h₁, h₂]
  simp only [hterm]
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ S),
    add_eq_left.2 (Finset.sum_eq_zero fun j _ ↦ by simp [j.2])]
  -- `φ t = φ (g (r t))`, and `r t` is the sum of its coordinates on `S`.
  have hφ : φ t = φ (g (r t)) := by rw [← LinearMap.comp_apply g r, hg, LinearMap.id_apply]
  rw [hφ, ← Finset.univ_sum_single (r t), map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : Pi.single j (r t j) = r t j • Pi.single j (1 : ℝ) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hj, map_smul, map_smul, smul_eq_mul]
  simp [r, j.2]

/-- The derivative of the moment map of the kernel torus has index `d + n`, where `d` is the number
of facets and `n = dim V`. -/
theorem index_fderiv_delzantLevelMap :
    (fderiv ℝ (delzantLevelMap i u c) x).index = (Fintype.card ι + finrank ℝ V : ℕ) := by
  have h₁ := (fderiv ℝ (delzantLevelMap i u c) x).index_eq_of_finiteDimensional
  have h₂ := hΔ.finrank_ker_linearCombination_real_add_finrank hi
  rw [h₁, finrank_prod, finrank_euclideanSpace, Module.finrank_fin_fun]
  push_cast
  omega

/-- The atlas of the **Delzant level set**, by the implicit-function charts of the regular level
set of the moment map of the kernel torus. It is modelled on `Fin (d + n) → ℝ`, where `d` is the
number of facets and `n = dim V`. -/
@[instance_reducible]
def delzantLevelChartedSpace :
    ChartedSpace (Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c) :=
  levelSetChartedSpace
    (fun _ _ ↦ (contDiff_delzantLevelMap i u c (m := 1)).hasStrictFDerivAt one_ne_zero)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun _ hx ↦ hΔ.surjective_fderiv_delzantLevelMap hi hx)
    (fun _ _ ↦ hΔ.index_fderiv_delzantLevelMap hi)

/-- **The Delzant level set is a smooth manifold** of dimension `d + n`, indeed a `C^m` manifold
for every `m`, including the analytic case `m = ω`, for the atlas
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
theorem isManifold_delzantLevel (m : WithTop ℕ∞) :
    letI := hΔ.delzantLevelChartedSpace hi
    IsManifold 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) m (delzantLevel i u c) :=
  isManifold_levelSet _ _ _ _ fun _ _ ↦ (contDiff_delzantLevelMap i u c).contDiffAt

/-- The inclusion of the Delzant level set into `ℂ^ι` is smooth for the atlas
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
theorem contMDiff_coe_delzantLevel {m : WithTop ℕ∞} :
    letI := hΔ.delzantLevelChartedSpace hi
    ContMDiff 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) m
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  contMDiff_coe_levelSet _ _ _ _ fun _ _ ↦ (contDiff_delzantLevelMap i u c).contDiffAt

end IsDelzant

end Delzant

end TauCeti.Toric
