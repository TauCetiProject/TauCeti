/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.Algebra.Module.ZLattice.Family.DiffeomorphProd

/-!
# Changing the lattice basis of the global trivialization

Let `P : Y → (Λ →ₗ[ℤ] E)` be a family of full lattices in a finite-dimensional real normed space
`E`. A `ℤ`-basis `b` of `Λ` indexed by `ι` gives the global trivialization
`[y, v] ↦ (y, [F_y⁻¹ v])` of the family of tori `(Y × E)/Λ` over `Y`, with fibre the standard
torus `ℝ^ι/ℤ^ι` (`TauCeti.torusFamilyHomeomorphProd`, and its smooth form
`TauCeti.torusFamilyDiffeomorphProd`). This file shows that the trivialization is independent of
`b` up to the integral change-of-basis map, which does not depend on the point `y`.

For a second `ℤ`-basis `b'` of `Λ` indexed by `ι'`, the integral matrix `b'.toMatrix b` expressing
`b` in `b'` defines the real linear isomorphism `Module.Basis.realCoordChange b b' : ℝ^ι ≃ ℝ^ι'`,
`x ↦ (b'.toMatrix b) *ᵥ x`. Its inverse is the change of coordinates from `b'` back to `b`, so it
carries the standard lattice `ℤ^ι` onto `ℤ^ι'` and induces the `C^n` diffeomorphism
`Module.Basis.torusCoordChange b b' n : ℝ^ι/ℤ^ι ≃ ℝ^ι'/ℤ^ι'` of standard tori. At every `y` the
periods of `b` and `b'` are related by the same matrix (`TauCeti.periodBasis_toMatrix_periodBasis`),
so the period coordinates for `b'` are the images of those for `b` under `realCoordChange b b'`
(`TauCeti.realCoordChange_periodBasis_repr`). Consequently the trivialization for `b'` is the
trivialization for `b` followed by the constant fibre map `torusCoordChange b b' n`. The
transition maps satisfy the cocycle law (`Module.Basis.realCoordChange_trans`,
`Module.Basis.torusCoordChange_trans`).

## Main definitions

* `Module.Basis.realCoordChange`: the real linear extension `ℝ^ι ≃ ℝ^ι'` of the integral change
  of coordinates between two `ℤ`-bases.
* `Module.Basis.torusCoordChange`: the induced `C^n` diffeomorphism of standard tori.

## Main results

* `Module.Basis.map_realCoordChange_span_basisFun`: the change of coordinates carries `ℤ^ι` onto
  `ℤ^ι'`.
* `TauCeti.snd_torusFamilyHomeomorphProd_eq_mapQ`: the fibre coordinate of the topological
  trivialization for `b'` is the image of that for `b` under the change of coordinates.
* `TauCeti.snd_torusFamilyDiffeomorphProd_eq_torusCoordChange`: the same for the smooth
  trivialization, with the diffeomorphism `torusCoordChange b b' n` of standard tori.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Set Function Submodule Matrix
open scoped Manifold ContDiff

namespace Module.Basis

variable {Λ : Type*} [AddCommGroup Λ] {ι ι' ι'' : Type*}

/-- The real change-of-basis matrices of `ℤ`-bases compose like the integral ones. -/
private theorem map_toMatrix_mul_map_toMatrix [Fintype ι'] (b : Basis ι ℤ Λ)
    (b' : Basis ι' ℤ Λ) (b'' : Basis ι'' ℤ Λ) :
    (b''.toMatrix b').map ((↑) : ℤ → ℝ) * (b'.toMatrix b).map ((↑) : ℤ → ℝ) =
      (b''.toMatrix b).map ((↑) : ℤ → ℝ) := by
  simpa [toMatrix_mul_toMatrix] using
    (Matrix.map_mul (L := b''.toMatrix b') (M := b'.toMatrix b) (f := Int.castRingHom ℝ)).symm

variable [Fintype ι] [Fintype ι']

/-- Multiplication by the real change-of-basis matrices from `b` to `b'` and back is the
identity. -/
private theorem mulVecLin_map_toMatrix_comp (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ) :
    ((b.toMatrix b').map ((↑) : ℤ → ℝ)).mulVecLin ∘ₗ
      ((b'.toMatrix b).map ((↑) : ℤ → ℝ)).mulVecLin = .id := by
  classical
  rw [← mulVecLin_mul, map_toMatrix_mul_map_toMatrix, toMatrix_self,
    Matrix.map_one _ Int.cast_zero Int.cast_one, mulVecLin_one]

/-- **The real change of coordinates** between two `ℤ`-bases `b` and `b'` of `Λ`: multiplication
by the integral change-of-basis matrix `b'.toMatrix b`, whose `i`-th column holds the coordinates
of `b i` in `b'`, as a real linear isomorphism `ℝ^ι ≃ ℝ^ι'`. It sends the coordinates of an element
of `Λ` in `b` to its coordinates in `b'`, and carries the standard lattice `ℤ^ι` onto `ℤ^ι'`
(`Module.Basis.map_realCoordChange_span_basisFun`). -/
noncomputable def realCoordChange (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ) :
    (ι → ℝ) ≃L[ℝ] (ι' → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv <| LinearEquiv.ofLinearMap
    ((b'.toMatrix b).map ((↑) : ℤ → ℝ)).mulVecLin ((b.toMatrix b').map ((↑) : ℤ → ℝ)).mulVecLin
    (mulVecLin_map_toMatrix_comp b' b) (mulVecLin_map_toMatrix_comp b b')

variable (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ)

/-- The real change of coordinates from `b` to `b'` is multiplication by the matrix
`b'.toMatrix b`. -/
theorem realCoordChange_apply (x : ι → ℝ) :
    b.realCoordChange b' x = (b'.toMatrix b).map ((↑) : ℤ → ℝ) *ᵥ x := (rfl)

/-- The inverse of the change of coordinates from `b` to `b'` is the change of coordinates from
`b'` to `b`. -/
@[simp] theorem realCoordChange_symm : (b.realCoordChange b').symm = b'.realCoordChange b := (rfl)

/-- The change of coordinates from a basis to itself is the identity. -/
@[simp] theorem realCoordChange_self : b.realCoordChange b = ContinuousLinearEquiv.refl ℝ _ := by
  classical
  ext x
  simp [realCoordChange_apply]

/-- **The cocycle law.** Changing coordinates from `b` to `b'` and then from `b'` to `b''` is
changing coordinates from `b` to `b''`. -/
theorem realCoordChange_trans [Fintype ι''] (b'' : Basis ι'' ℤ Λ) :
    (b.realCoordChange b').trans (b'.realCoordChange b'') = b.realCoordChange b'' := by
  ext x
  simp only [ContinuousLinearEquiv.trans_apply, realCoordChange_apply, mulVec_mulVec,
    map_toMatrix_mul_map_toMatrix]

/-- The change of coordinates sends integer vectors to integer vectors. -/
private theorem realCoordChange_mem_span_basisFun {x : ι → ℝ}
    (hx : x ∈ span ℤ (range (Pi.basisFun ℝ ι))) :
    b.realCoordChange b' x ∈ span ℤ (range (Pi.basisFun ℝ ι')) := by
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ] at hx
  rw [(Pi.basisFun ℝ ι').mem_span_iff_repr_mem ℤ]
  intro j
  choose m hm using hx
  refine ⟨∑ i, b'.toMatrix b j i * m i, ?_⟩
  simp_all [realCoordChange_apply, Matrix.mulVec, dotProduct]

/-- The change of coordinates between two `ℤ`-bases carries the standard lattice `ℤ^ι` onto the
standard lattice `ℤ^ι'`. -/
theorem map_realCoordChange_span_basisFun :
    (span ℤ (range (Pi.basisFun ℝ ι))).map
        ((b.realCoordChange b').toLinearEquiv.restrictScalars ℤ : (ι → ℝ) →ₗ[ℤ] ι' → ℝ) =
      span ℤ (range (Pi.basisFun ℝ ι')) := by
  refine le_antisymm
    (map_le_iff_le_comap.2 fun x hx ↦ realCoordChange_mem_span_basisFun b b' hx)
    fun x hx ↦ ⟨b'.realCoordChange b x, realCoordChange_mem_span_basisFun b' b hx, ?_⟩
  exact (b.realCoordChange b').apply_symm_apply x

/-- **The change of coordinates of standard tori** between two `ℤ`-bases `b` and `b'` of `Λ`: the
`C^n` diffeomorphism `ℝ^ι/ℤ^ι ≃ ℝ^ι'/ℤ^ι'` induced by the real change of coordinates
`Module.Basis.realCoordChange b b'`, which carries `ℤ^ι` onto `ℤ^ι'`. -/
noncomputable def torusCoordChange (n : ℕ∞ω) :
    Diffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι' → ℝ)
      (AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ))
      (AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι'))) (ι' → ℝ)) n :=
  (span ℤ (range (Pi.basisFun ℝ ι))).orbitRelQuotientDiffeomorph _
    ((b.realCoordChange b').toLinearEquiv.restrictScalars ℤ)
    (b.map_realCoordChange_span_basisFun b')
    (by convert (b.realCoordChange b').contDiff using 1; ext; simp)
    (by convert (b.realCoordChange b').symm.contDiff using 1; ext; simp)

/-- The change of coordinates of standard tori sends the class of `x` to the class of its real
change of coordinates. -/
@[simp] theorem torusCoordChange_mk (n : ℕ∞ω) (x : ι → ℝ) :
    b.torusCoordChange b' n (Quotient.mk _ x) = Quotient.mk _ (b.realCoordChange b' x) := by
  simp [torusCoordChange]

/-- The inverse of the change of coordinates of standard tori from `b` to `b'` is the change of
coordinates from `b'` to `b`. -/
@[simp] theorem torusCoordChange_symm (n : ℕ∞ω) :
    (b.torusCoordChange b' n).symm = b'.torusCoordChange b n := by
  ext z
  induction z using Quotient.inductionOn
  rw [← Diffeomorph.toEquiv_coe_symm, Equiv.symm_apply_eq, Diffeomorph.coe_toEquiv,
    torusCoordChange_mk, torusCoordChange_mk, ← realCoordChange_symm,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The change of coordinates of standard tori from a basis to itself is the identity. -/
@[simp] theorem torusCoordChange_self (n : ℕ∞ω) :
    b.torusCoordChange b n = Diffeomorph.refl 𝓘(ℝ, ι → ℝ) _ n := by
  ext z
  induction z using Quotient.inductionOn
  simp

/-- **The cocycle law** for the change of coordinates of standard tori. -/
theorem torusCoordChange_trans [Fintype ι''] (b'' : Basis ι'' ℤ Λ) (n : ℕ∞ω) :
    (b.torusCoordChange b' n).trans (b'.torusCoordChange b'' n) = b.torusCoordChange b'' n := by
  ext z
  induction z using Quotient.inductionOn
  simp only [Diffeomorph.coe_trans, Function.comp_apply, torusCoordChange_mk]
  rw [← ContinuousLinearEquiv.trans_apply, realCoordChange_trans]

end Module.Basis

namespace TauCeti

section Coordinates

variable {Y : Type*} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι ι' : Type*} (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ) (hinj : ∀ y, Injective (P y))

/-- **The period change-of-basis matrix is constant.** At every `y`, the matrix expressing the
period basis for `b` in the period basis for `b'` is the integral change-of-basis matrix
`b'.toMatrix b`. -/
@[simp] theorem periodBasis_toMatrix_periodBasis (y : Y) :
    (periodBasis P b' hinj y).toMatrix (periodBasis P b hinj y) =
      (b'.toMatrix b).map ((↑) : ℤ → ℝ) := by
  ext j i
  simp [Basis.toMatrix_apply]

/-- The period coordinates for `b'` are the images of the period coordinates for `b` under the
real change of coordinates from `b` to `b'`, at every `y`. -/
@[simp] theorem realCoordChange_periodBasis_repr [Fintype ι] [Fintype ι'] (y : Y) (v : E) :
    b.realCoordChange b' ((periodBasis P b hinj y).repr v) = (periodBasis P b' hinj y).repr v := by
  rw [Basis.realCoordChange_apply, ← periodBasis_toMatrix_periodBasis P b b' hinj y]
  exact (periodBasis P b hinj y).toMatrix_mulVec_repr (periodBasis P b' hinj y) v

end Coordinates

section Topology

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ)
  (hinj : ∀ y, Injective (P y)) (hcont : ∀ l, Continuous fun y ↦ P y l)

/-- **Basis independence of the global trivialization.** The fibre coordinate of the global
trivialization for `b'` is the image of the fibre coordinate for `b` under the map
`ℝ^ι/ℤ^ι → ℝ^ι'/ℤ^ι'` induced by the real change of coordinates from `b` to `b'`, independently of
the point of the base. Both trivializations lie over `Y`
(`TauCeti.fst_torusFamilyHomeomorphProd`). -/
theorem snd_torusFamilyHomeomorphProd_eq_mapQ
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (torusFamilyHomeomorphProd P b' hinj hcont z).2 =
      (span ℤ (range (Pi.basisFun ℝ ι))).mapQ (span ℤ (range (Pi.basisFun ℝ ι')))
        ((b.realCoordChange b').toLinearEquiv.restrictScalars ℤ : (ι → ℝ) →ₗ[ℤ] ι' → ℝ)
        (map_le_iff_le_comap.1 (b.map_realCoordChange_span_basisFun b').le)
        (torusFamilyHomeomorphProd P b hinj hcont z).2 := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end Topology

section Smooth

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] (b : Basis ι ℤ Λ) (b' : Basis ι' ℤ Λ)
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω}
  [IsManifold I n Y] (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l)

/-- **Basis independence of the smooth global trivialization.** The fibre coordinate of the smooth
trivialization for `b'` is the image of the fibre coordinate for `b` under the diffeomorphism
`Module.Basis.torusCoordChange b b' n` of standard tori, which does not depend on the point of the
base. Both trivializations lie over `Y` (`TauCeti.fst_torusFamilyDiffeomorphProd`). -/
theorem snd_torusFamilyDiffeomorphProd_eq_torusCoordChange
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyDiffeomorphProd P b' hinj hP z).2 =
      b.torusCoordChange b' n (torusFamilyDiffeomorphProd P b hinj hP z).2 := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end Smooth

end TauCeti
