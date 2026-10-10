/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Unitarily invariant seminorms on rectangular linear maps

A seminorm `N` on the linear maps `E →ₗ[𝕜] F` between two inner product spaces is *unitarily
invariant* when `N (U A V) = N A` for all unitaries `U` of `F` and `V` of `E`, acting
independently on the target and the source. Square operators are the case `E = F`. Unitaries are
represented as linear isometric equivalences `F ≃ₗᵢ[𝕜] F` and `E ≃ₗᵢ[𝕜] E`. The structure
itself assumes neither finite-dimensionality nor boundedness: it is a seminorm on all algebraic
linear maps `E →ₗ[𝕜] F`.

When `E` and `F` are finite-dimensional, the operator norm, the Frobenius norm, the Ky Fan norms
and the nuclear norm are the standard examples. The examples are not formalized here.

This file sets up the structure together with the elementary vocabulary for comparing its
values:

* the two-sided unitary orbit `U C V` of a map `C`, on which every unitarily invariant seminorm
  is constant; when `E` and `F` are finite-dimensional, the orbit of `C` consists exactly of the
  maps with the same singular values as `C`, so a unitarily invariant seminorm depends only on the
  singular values of its argument;
* the convex hull of the two-sided unitary orbit, on which every unitarily invariant seminorm is
  bounded by its value at `C`;
* finite orbit certificates, which write `X` as a combination `∑ᵢ aᵢ • Uᵢ C Vᵢ` of points of the
  orbit of `C`, and bound `N X` by the coefficient mass `∑ᵢ ‖aᵢ‖` times `N C`;
* transport of a unitarily invariant seminorm along isometric isomorphisms of the source and the
  target, and, for finite-dimensional `E` and `F`, to the adjoint maps.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm`: seminorms on `E →ₗ[𝕜] F` invariant under unitaries of
  the source and of the target.
* `LinearMap.twoSidedUnitaryOrbit`: the set of maps `U C V` with `U`, `V` unitary.
* `LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq`: two maps lie in the same orbit
  exactly when they have the same singular values.
* `TauCeti.UnitarilyInvariantSeminorm.map_eq_of_singularValues_eq`: a unitarily invariant
  seminorm is determined by the singular values of its argument.
* `LinearMap.twoSidedUnitaryOrbitHull`: the convex combinations of points of the orbit;
  `LinearMap.twoSidedUnitaryOrbitHull_eq_convexHull` identifies it with `convexHull ℝ` of the orbit
  whenever the latter makes sense.
* `TauCeti.UnitaryOrbitCertificate`: a representation `X = ∑ᵢ aᵢ • Uᵢ C Vᵢ`, with its
  coefficient mass `TauCeti.UnitaryOrbitCertificate.mass`.
* `TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`: `N X ≤ mass * N C`.
* `TauCeti.UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull`: points of
  the orbit hull have certificates of mass one, so
  `TauCeti.UnitarilyInvariantSeminorm.map_le_of_mem_twoSidedUnitaryOrbitHull`: `N X ≤ N C` on the
  hull.
* `TauCeti.UnitarilyInvariantSeminorm.arrowCongr`: transport along isometric isomorphisms of the
  source and the target.
* `TauCeti.UnitarilyInvariantSeminorm.compAdjoint`: the seminorm `B ↦ N B†` on the adjoint maps.

## Source

The structure `UnitarilyInvariantSeminorm`, the two-sided unitary orbit and the finite orbit
certificates are adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Basic.lean`).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F']
  [InnerProductSpace 𝕜 F']

namespace LinearMap

/-- The **two-sided unitary orbit** of `C : E →ₗ[𝕜] F`: the maps `U ∘ C ∘ V` for unitaries `U`
of the target and `V` of the source. -/
def twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {X | ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X}

theorem mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbit ↔
      ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X :=
  Iff.rfl

theorem linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) ∈ C.twoSidedUnitaryOrbit :=
  ⟨U, V, rfl⟩

@[simp]
theorem self_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : C ∈ C.twoSidedUnitaryOrbit :=
  ⟨.refl 𝕜 F, .refl 𝕜 E, rfl⟩

/-- Two-sided unitary orbits are equivalence classes: the orbit of any of its points is the whole
orbit. -/
theorem twoSidedUnitaryOrbit_eq_of_mem {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.twoSidedUnitaryOrbit = C.twoSidedUnitaryOrbit := by
  obtain ⟨U, V, rfl⟩ := h
  ext Y
  constructor
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.trans U', V'.trans V, by ext; simp⟩
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.symm.trans U', V'.trans V.symm, by ext; simp⟩

/-- Maps in the same two-sided unitary orbit have the same singular values. -/
theorem singularValues_eq_of_mem_twoSidedUnitaryOrbit [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.singularValues = C.singularValues := by
  obtain ⟨U, V, rfl⟩ := h
  simp

/-- **Determination of the orbit by singular values.** Two maps between finite-dimensional inner
product spaces lie in the same two-sided unitary orbit exactly when they have the same singular
values. -/
theorem mem_twoSidedUnitaryOrbit_iff_singularValues_eq [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbit ↔ X.singularValues = C.singularValues := by
  refine ⟨singularValues_eq_of_mem_twoSidedUnitaryOrbit, fun h ↦ ?_⟩
  -- Both maps are unitary multiples of the same rectangular diagonal map.
  obtain ⟨U, V, hC⟩ := C.exists_linearIsometryEquiv_eq_comp_toLin_comp
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 F)
  obtain ⟨U', V', hX⟩ := X.exists_linearIsometryEquiv_eq_comp_toLin_comp
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 F)
  rw [h] at hX
  refine ⟨U.symm.trans U', V'.trans V.symm, ?_⟩
  conv_lhs => rw [hC]
  rw [hX]
  ext x
  simp

/-! ### The convex hull of the two-sided unitary orbit -/

/-- The **convex hull of the two-sided unitary orbit** of `C`: the convex combinations
`∑ᵢ tᵢ • Xᵢ` of maps `Xᵢ` in the two-sided unitary orbit of `C`, with real weights `tᵢ ≥ 0`
summing to `1`. The weights act through `ℝ → 𝕜`: for a general `RCLike` field `𝕜` the space
`E →ₗ[𝕜] F` carries no `ℝ`-module instance to which `convexHull ℝ` could be applied. -/
def twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {X | ∃ (n : ℕ) (t : Fin n → ℝ) (Y : Fin n → E →ₗ[𝕜] F), (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
    (∀ i, Y i ∈ C.twoSidedUnitaryOrbit) ∧ ∑ i, (t i : 𝕜) • Y i = X}

theorem mem_twoSidedUnitaryOrbitHull {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbitHull ↔
      ∃ (n : ℕ) (t : Fin n → ℝ) (Y : Fin n → E →ₗ[𝕜] F), (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
        (∀ i, Y i ∈ C.twoSidedUnitaryOrbit) ∧ ∑ i, (t i : 𝕜) • Y i = X :=
  Iff.rfl

theorem twoSidedUnitaryOrbit_subset_twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) :
    C.twoSidedUnitaryOrbit ⊆ C.twoSidedUnitaryOrbitHull :=
  fun X hX ↦ mem_twoSidedUnitaryOrbitHull.mpr
    ⟨1, fun _ ↦ 1, fun _ ↦ X, fun _ ↦ zero_le_one, by simp, fun _ ↦ hX, by simp⟩

@[simp]
theorem self_mem_twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) : C ∈ C.twoSidedUnitaryOrbitHull :=
  C.twoSidedUnitaryOrbit_subset_twoSidedUnitaryOrbitHull C.self_mem_twoSidedUnitaryOrbit

/-- When `F` is also a real vector space compatibly with its `𝕜`-structure (for instance when `𝕜`
is `ℝ` or `ℂ`), the orbit hull is the convex hull `convexHull ℝ` of the two-sided unitary orbit. -/
theorem twoSidedUnitaryOrbitHull_eq_convexHull [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    (C : E →ₗ[𝕜] F) : C.twoSidedUnitaryOrbitHull = convexHull ℝ C.twoSidedUnitaryOrbit := by
  have hsmul (t : ℝ) (Y : E →ₗ[𝕜] F) : (t : 𝕜) • Y = t • Y := by
    ext x
    exact (RCLike.real_smul_eq_coe_smul t (Y x)).symm
  ext X
  rw [mem_twoSidedUnitaryOrbitHull, mem_convexHull_iff_exists_fintype]
  constructor
  · rintro ⟨n, t, Y, ht, htsum, hY, rfl⟩
    exact ⟨Fin n, inferInstance, t, Y, ht, htsum, hY, by simp only [hsmul]⟩
  · rintro ⟨ι, _, t, Y, ht, htsum, hY, rfl⟩
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, t ∘ e.symm, Y ∘ e.symm, fun i ↦ ht _, ?_, fun i ↦ hY _, ?_⟩
    · rw [← htsum]
      exact e.symm.sum_comp t
    · simp only [Function.comp_apply, hsmul]
      exact e.symm.sum_comp fun i ↦ t i • Y i

/-- The orbit hull depends only on the orbit: it is the same for every point of the orbit. -/
theorem twoSidedUnitaryOrbitHull_eq_of_mem {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.twoSidedUnitaryOrbitHull = C.twoSidedUnitaryOrbitHull := by
  ext
  simp only [mem_twoSidedUnitaryOrbitHull, twoSidedUnitaryOrbit_eq_of_mem h]

/-- The orbit hull is convex: it is closed under convex combinations of two of its points. -/
theorem smul_add_smul_mem_twoSidedUnitaryOrbitHull {C X Y : E →ₗ[𝕜] F}
    (hX : X ∈ C.twoSidedUnitaryOrbitHull) (hY : Y ∈ C.twoSidedUnitaryOrbitHull) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : 𝕜) • X + (b : 𝕜) • Y ∈ C.twoSidedUnitaryOrbitHull := by
  obtain ⟨n, t, X', ht, htsum, hX', rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp hX
  obtain ⟨m, s, Y', hs, hssum, hY', rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp hY
  refine mem_twoSidedUnitaryOrbitHull.mpr ⟨n + m, Fin.append (a • t) (b • s), Fin.append X' Y',
    fun i ↦ ?_, ?_, fun i ↦ ?_, ?_⟩
  · cases i using Fin.addCases <;> simp [mul_nonneg, *]
  · simp [Fin.sum_univ_add, ← Finset.mul_sum, htsum, hssum, hab]
  · cases i using Fin.addCases <;> simp [*]
  · simp [Fin.sum_univ_add, Finset.smul_sum, smul_smul]

/-- The orbit hull is invariant under unitaries of the source and of the target. -/
theorem linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbitHull {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbitHull) (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (U : F →ₗ[𝕜] F) ∘ₗ X ∘ₗ (V : E →ₗ[𝕜] E) ∈ C.twoSidedUnitaryOrbitHull := by
  obtain ⟨n, t, Y, ht, htsum, hY, rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp h
  refine mem_twoSidedUnitaryOrbitHull.mpr
    ⟨n, t, fun i ↦ (U : F →ₗ[𝕜] F) ∘ₗ Y i ∘ₗ (V : E →ₗ[𝕜] E), ht, htsum, fun i ↦ ?_, ?_⟩
  · rw [← twoSidedUnitaryOrbit_eq_of_mem (hY i)]
    exact (Y i).linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbit U V
  · ext x
    simp

end LinearMap

namespace TauCeti

/-- A **unitarily invariant seminorm** on the linear maps `E →ₗ[𝕜] F`: a seminorm `N` with
`N (U ∘ A ∘ V) = N A` for every unitary `U` of the target `F` and every unitary `V` of the source
`E`, acting independently. Square operators are the case `E = F`. -/
structure UnitarilyInvariantSeminorm (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] extends Seminorm 𝕜 (E →ₗ[𝕜] F) where
  /-- Invariance under unitaries of the target and of the source. -/
  map_linearIsometryEquiv_comp_comp' (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    toSeminorm ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toSeminorm A

namespace UnitarilyInvariantSeminorm

instance : FunLike (UnitarilyInvariantSeminorm 𝕜 E F) (E →ₗ[𝕜] F) ℝ where
  coe N := N.toFun
  coe_injective := by
    rintro ⟨N, _⟩ ⟨M, _⟩ h
    congr
    exact Seminorm.ext (congrFun h)

instance : SeminormClass (UnitarilyInvariantSeminorm 𝕜 E F) 𝕜 (E →ₗ[𝕜] F) where
  map_zero N := N.map_zero'
  map_add_le_add N := N.add_le'
  map_neg_eq_map N := N.neg'
  map_smul_eq_mul N := N.smul'

@[ext]
theorem ext {N M : UnitarilyInvariantSeminorm 𝕜 E F} (h : ∀ A, N A = M A) : N = M :=
  DFunLike.ext N M h

@[simp]
theorem coe_toSeminorm (N : UnitarilyInvariantSeminorm 𝕜 E F) : ⇑N.toSeminorm = N :=
  (rfl)

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/-- **Unitary invariance**: `N (U ∘ A ∘ V) = N A` for unitaries `U` of the target and `V` of the
source. -/
theorem map_linearIsometryEquiv_comp_comp (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) : N ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = N A :=
  N.map_linearIsometryEquiv_comp_comp' U V A

@[simp]
theorem map_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N ((U : F →ₗ[𝕜] F) ∘ₗ A) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp U (.refl 𝕜 E) A using 2
  ext; simp

@[simp]
theorem map_comp_linearIsometryEquiv (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    N (A ∘ₗ (V : E →ₗ[𝕜] E)) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp (.refl 𝕜 F) V A using 2
  ext; simp

/-- A unitarily invariant seminorm is constant on each two-sided unitary orbit. -/
theorem map_eq_of_mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbit) : N X = N C := by
  obtain ⟨U, V, rfl⟩ := h
  exact N.map_linearIsometryEquiv_comp_comp U V C

/-- **Determination by singular values.** On maps between finite-dimensional inner product spaces,
a unitarily invariant seminorm takes equal values at maps with the same singular values. -/
theorem map_eq_of_singularValues_eq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A B : E →ₗ[𝕜] F} (h : A.singularValues = B.singularValues) : N A = N B :=
  N.map_eq_of_mem_twoSidedUnitaryOrbit
    (LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq.mpr h)

/-! ### Transport along isometric isomorphisms -/

/-- The value of `N` on maps `E' →ₗ[𝕜] F'` read through isometric isomorphisms `E ≃ E'` and
`F ≃ F'`; `UnitarilyInvariantSeminorm.arrowCongr` packages it as an equivalence. -/
private noncomputable def transport (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) : UnitarilyInvariantSeminorm 𝕜 E' F' where
  toSeminorm := N.toSeminorm.comp
    (LinearEquiv.arrowCongr eE.toLinearEquiv eF.toLinearEquiv).symm.toLinearMap
  map_linearIsometryEquiv_comp_comp' U V A := by
    -- Conjugating `U` and `V` back to `F` and `E` turns `U ∘ A ∘ V` into a two-sided unitary
    -- multiple of the transported map.
    have h := N.map_linearIsometryEquiv_comp_comp (eF.trans (U.trans eF.symm))
      (eE.trans (V.trans eE.symm)) ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E'))
    rw [Seminorm.comp_apply, Seminorm.comp_apply, coe_toSeminorm]
    convert h using 2 <;> ext <;> simp

private theorem transport_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E' →ₗ[𝕜] F') :
    transport eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  (rfl)

/-- **Transport** of unitarily invariant seminorms along isometric isomorphisms `eE : E ≃ E'` of
the sources and `eF : F ≃ F'` of the targets: `N` corresponds to the seminorm
`A ↦ N (eF⁻¹ ∘ A ∘ eE)` on `E' →ₗ[𝕜] F'`, which is again unitarily invariant. -/
noncomputable def arrowCongr (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    UnitarilyInvariantSeminorm 𝕜 E F ≃ UnitarilyInvariantSeminorm 𝕜 E' F' where
  toFun := transport eE eF
  invFun := transport eE.symm eF.symm
  left_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp
  right_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp

@[simp]
theorem arrowCongr_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') (A : E' →ₗ[𝕜] F') :
    arrowCongr eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  transport_apply eE eF N A

@[simp]
theorem arrowCongr_symm (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    (arrowCongr (𝕜 := 𝕜) eE eF).symm = arrowCongr eE.symm eF.symm :=
  (rfl)

/-- Transport along unitaries of the source and the target leaves every unitarily invariant
seminorm unchanged. -/
@[simp]
theorem arrowCongr_eq_self (U : E ≃ₗᵢ[𝕜] E) (V : F ≃ₗᵢ[𝕜] F) : arrowCongr U V N = N := by
  ext A
  rw [arrowCongr_apply, map_linearIsometryEquiv_comp_comp]

/-! ### Transport to the adjoint maps -/

section Adjoint

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The **adjoint transport** of a unitarily invariant seminorm `N` on `E →ₗ[𝕜] F`: the seminorm
`B ↦ N B†` on `F →ₗ[𝕜] E`, again unitarily invariant. -/
noncomputable def compAdjoint : UnitarilyInvariantSeminorm 𝕜 F E where
  toSeminorm := N.toSeminorm.comp (LinearMap.adjoint (𝕜 := 𝕜) (E := F) (F := E)).toLinearMap
  map_linearIsometryEquiv_comp_comp' U V B := by
    rw [Seminorm.comp_apply, Seminorm.comp_apply]
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc] using
      N.map_linearIsometryEquiv_comp_comp V.symm U.symm (LinearMap.adjoint B)

@[simp]
theorem compAdjoint_apply (B : F →ₗ[𝕜] E) : N.compAdjoint B = N (LinearMap.adjoint B) :=
  (rfl)

@[simp]
theorem compAdjoint_compAdjoint : N.compAdjoint.compAdjoint = N := by
  ext A
  simp

end Adjoint

end UnitarilyInvariantSeminorm

/-! ### Finite orbit certificates -/

/-- A **finite unitary orbit certificate** for `X` over `C`, indexed by a finite type `ι`: a
representation `X = ∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ` of `X` as a linear combination of points of the
two-sided unitary orbit of `C`. Its coefficient mass `∑ᵢ ‖aᵢ‖` bounds every unitarily invariant
seminorm of `X` by the same seminorm of `C`
(`TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`). -/
@[ext]
structure UnitaryOrbitCertificate (ι : Type*) [Fintype ι] (C X : E →ₗ[𝕜] F) where
  /-- The coefficients `aᵢ`. -/
  coeff : ι → 𝕜
  /-- The unitaries `Uᵢ` of the target. -/
  left : ι → F ≃ₗᵢ[𝕜] F
  /-- The unitaries `Vᵢ` of the source. -/
  right : ι → E ≃ₗᵢ[𝕜] E
  /-- The representation `∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ = X`. -/
  sum_smul_comp_comp_eq :
    ∑ i, coeff i • ((left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (right i : E →ₗ[𝕜] E)) = X

namespace UnitaryOrbitCertificate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {C X : E →ₗ[𝕜] F}
  (c : UnitaryOrbitCertificate ι C X)

/-- The **coefficient mass** `∑ᵢ ‖aᵢ‖` of an orbit certificate. -/
noncomputable def mass : ℝ :=
  ∑ i, ‖c.coeff i‖

theorem mass_def : c.mass = ∑ i, ‖c.coeff i‖ :=
  (rfl)

theorem mass_nonneg : 0 ≤ c.mass :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- **Certificate bound**: if `X` has an orbit certificate over `C` of mass `m`, then
`N X ≤ m * N C` for every unitarily invariant seminorm `N`. -/
theorem apply_le_mass_mul (N : UnitarilyInvariantSeminorm 𝕜 E F) : N X ≤ c.mass * N C := by
  calc N X = N (∑ i, c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) := by
        rw [c.sum_smul_comp_comp_eq]
    _ ≤ ∑ i, N (c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
    _ = c.mass * N C := by
        simp [mass_def, Finset.sum_mul, map_smul_eq_mul, N.map_linearIsometryEquiv_comp_comp]

/-- **Reindexing** an orbit certificate along an equivalence of its finite index types. -/
def reindex (e : ι ≃ κ) : UnitaryOrbitCertificate κ C X where
  coeff := c.coeff ∘ e.symm
  left := c.left ∘ e.symm
  right := c.right ∘ e.symm
  sum_smul_comp_comp_eq := (e.symm.sum_comp fun i ↦
    c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))).trans
      c.sum_smul_comp_comp_eq

@[simp]
theorem coeff_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).coeff k = c.coeff (e.symm k) :=
  (rfl)

@[simp]
theorem left_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).left k = c.left (e.symm k) :=
  (rfl)

@[simp]
theorem right_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).right k = c.right (e.symm k) :=
  (rfl)

@[simp]
theorem mass_reindex (e : ι ≃ κ) : (c.reindex e).mass = c.mass := by
  simp only [mass_def, coeff_reindex]
  exact e.symm.sum_comp fun i ↦ ‖c.coeff i‖

end UnitaryOrbitCertificate

/-- **Certificates from convex combinations.** Every point `X = ∑ᵢ tᵢ • Uᵢ C Vᵢ` of the convex hull
of the two-sided unitary orbit of `C` has an orbit certificate over `C` of mass one. -/
theorem UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull
    {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbitHull) :
    ∃ (n : ℕ) (c : UnitaryOrbitCertificate (Fin n) C X), c.mass = 1 := by
  obtain ⟨n, t, Y, ht, htsum, hY, rfl⟩ := LinearMap.mem_twoSidedUnitaryOrbitHull.mp h
  choose U V hUV using fun i ↦ LinearMap.mem_twoSidedUnitaryOrbit.mp (hY i)
  refine ⟨n, ⟨fun i ↦ (t i : 𝕜), U, V, by simp only [hUV]⟩, ?_⟩
  simp [mass_def, abs_of_nonneg (ht _), htsum]

/-- A unitarily invariant seminorm is bounded on the convex hull of the two-sided unitary orbit of
`C` by its value at `C`. -/
theorem UnitarilyInvariantSeminorm.map_le_of_mem_twoSidedUnitaryOrbitHull
    (N : UnitarilyInvariantSeminorm 𝕜 E F) {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbitHull) : N X ≤ N C := by
  obtain ⟨n, c, hc⟩ := UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull h
  simpa [hc] using c.apply_le_mass_mul N

end TauCeti
