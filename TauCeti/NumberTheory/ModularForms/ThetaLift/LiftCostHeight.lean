/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Module.Bases.Auerbach
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic

/-!
# The local determinant and height cost of one lift

This file isolates the nonarchimedean determinant estimate and the height assembly for one theta
lift. Auerbach's lemma supplies a basis of an arbitrary coordinate subspace on which the original
coordinate functionals have norm at most one. Thus an endomorphism preserving the local coordinate
lattice has determinant in the local unit ball, with no prescribed basis of the subspace.

Orthogonal compression is cleared by an auxiliary endomorphism. Multiplicativity of determinants
then turns a lower bound for its determinant into an upper bound for the determinant of the
compression. The existing `PrimePadicIso.HeightLe` calculus assembles these local bounds with
archimedean and inverse-ratio bounds. No logarithmic weights are inserted into the finite-prime sum:
`HeightLe.of_mul_le` converts its unweighted exponential exponents to the weights in `HeightLe`.

## Main results

* `norm_det_le_one_of_preserves_localCoordinateLattice`: the ultrametric determinant bound for a
  lattice-preserving endomorphism of a subspace.
* `norm_det_le_inv_of_comp_preserves_localCoordinateLattice`: clearing a subspace endomorphism by
  an auxiliary operator of bounded-below determinant bounds the determinant of the cleared map.
* `norm_padic_det_liftCompression_le`: the denominator-cleared determinant bound for an orthogonal
  compression.
* `heightLe_determinant_ratio` and `heightLe_liftDeterminant_ratio`: the height bounds for
  determinant ratios and lift-volume ratios.

## References

The argument follows [ShortProof], `lsernau/grh-lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, `New/OneLift/LiftVolumeHeight.lean`, in the
nonarchimedean and height parts of the cost of one lift. The proofs here use the Auerbach and
height APIs on `main`. The Gram determinant factorization and archimedean eigenvalue estimate are
separate prerequisites and are not reproduced here.
-/

public noncomputable section

namespace TauCeti.ThetaLift

universe u v w

/-- The local coordinate lattice determined by a basis and a place. -/
def localCoordinateLattice {ι : Type u} {𝕜 : Type*} {E : Type v} {K : Type w}
    [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [SeminormedRing K]
    (place : 𝕜 →+* K) (b : Module.Basis ι 𝕜 E) : Set E :=
  {x | ∀ j, ‖place (b.repr x j)‖ ≤ 1}

/-- Membership in the local coordinate lattice is boundedness of every coordinate. -/
@[simp]
theorem mem_localCoordinateLattice {ι : Type u} {𝕜 : Type*} {E : Type v} {K : Type w}
    [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [SeminormedRing K] {place : 𝕜 →+* K}
    {b : Module.Basis ι 𝕜 E} {x : E} :
    x ∈ localCoordinateLattice place b ↔ ∀ j, ‖place (b.repr x j)‖ ≤ 1 :=
  Iff.rfl

/-- A matrix with entries in the closed unit ball of an ultrametric seminormed commutative ring
with `‖1‖ = 1` has determinant in that ball. -/
theorem norm_matrixDet_le_one {n K : Type*} [Fintype n] [DecidableEq n]
    [SeminormedCommRing K] [NormOneClass K] [IsUltrametricDist K]
    (M : Matrix n n K) (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ ↦ ?_
  have hsign : ‖(Equiv.Perm.sign σ : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  have hprod : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (norm_mul_le _ _).trans <| by
        simpa only [one_mul] using mul_le_mul (hM (σ a) a) ih (norm_nonneg _) zero_le_one
  calc
    ‖(Equiv.Perm.sign σ : K) * ∏ i, M (σ i) i‖
        ≤ ‖(Equiv.Perm.sign σ : K)‖ * ‖∏ i, M (σ i) i‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul hsign hprod (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- A finite family of restricted coordinate functionals has an Auerbach basis whose vectors lie
in the local coordinate lattice. -/
theorem exists_localAuerbachBasis {ι : Type u} {𝕜 : Type*} {E : Type v} {K : Type w}
    [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] [NormedField K]
    (place : 𝕜 →+* K) (b : Module.Basis ι 𝕜 E) (Z : Submodule 𝕜 E) :
    ∃ (a : Fin (Module.finrank 𝕜 Z) → ι)
      (z : Module.Basis (Fin (Module.finrank 𝕜 Z)) 𝕜 Z),
      (∀ i k, b.repr ((z k : Z) : E) (a i) = if i = k then 1 else 0) ∧
      ∀ j k, ‖place (b.repr ((z k : Z) : E) j)‖ ≤ 1 := by
  classical
  let : Finite ι := Module.Finite.finite_basis b
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  let : CompactSpace ι := inferInstance
  let ℓ : ι → Module.Dual 𝕜 Z := fun j ↦ (b.coord j).comp Z.subtype
  have hsep : ∀ v : Z, (∀ j, ℓ j v = 0) → v = 0 := by
    intro v hv
    apply Subtype.ext
    apply b.repr.injective
    ext j
    simpa [ℓ, Module.Basis.coord_apply] using hv j
  obtain ⟨a, z, hdual, hz⟩ := place.exists_auerbachBasis ℓ
    (fun _ ↦ continuous_of_discreteTopology) hsep
  exact ⟨a, z, by simpa [ℓ, Module.Basis.coord_apply] using hdual,
    by simpa [ℓ, Module.Basis.coord_apply] using hz⟩

/-- An endomorphism preserving the local coordinate lattice on a subspace has determinant norm at
most one. No basis of the subspace needs to be supplied. -/
theorem norm_det_le_one_of_preserves_localCoordinateLattice {ι : Type u} {𝕜 : Type*}
    {E : Type v} {K : Type w} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedField K] [IsUltrametricDist K]
    (place : 𝕜 →+* K) (b : Module.Basis ι 𝕜 E) (Z : Submodule 𝕜 E) (T : Module.End 𝕜 Z)
    (hT : ∀ x : Z, (x : E) ∈ localCoordinateLattice place b →
      ((T x : Z) : E) ∈ localCoordinateLattice place b) :
    ‖place (LinearMap.det T)‖ ≤ 1 := by
  classical
  obtain ⟨a, z, hdual, hz⟩ := exists_localAuerbachBasis place b Z
  have hTz (k) : ((T (z k) : Z) : E) ∈ localCoordinateLattice place b :=
    hT (z k) (fun j ↦ hz j k)
  have hcoordmap (i) : z.coord i = (b.coord (a i)).comp Z.subtype := by
    apply z.ext
    intro k
    simp [Module.Basis.coord_apply, hdual, Finsupp.single_apply, eq_comm]
  have hcoord (i k) : z.repr (T (z k)) i = b.repr ((T (z k) : Z) : E) (a i) := by
    have h := DFunLike.congr_fun (hcoordmap i) (T (z k))
    simpa only [Module.Basis.coord_apply, LinearMap.comp_apply, Submodule.coe_subtype] using h
  rw [← LinearMap.det_toMatrix z T, RingHom.map_det]
  apply norm_matrixDet_le_one
  intro i k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, hcoord]
  exact hTz k (a i)

/-- If an auxiliary operator `Λ` with determinant norm at least `c > 0` clears `T` into the
local coordinate lattice on `Z`, then `‖place (det T)‖ ≤ c⁻¹`. -/
theorem norm_det_le_inv_of_comp_preserves_localCoordinateLattice {ι : Type u} {𝕜 : Type*}
    {E : Type v} {K : Type w} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedField K] [IsUltrametricDist K]
    (place : 𝕜 →+* K) (b : Module.Basis ι 𝕜 E) (Z : Submodule 𝕜 E) (T Λ : Module.End 𝕜 Z)
    {c : ℝ} (hc : 0 < c)
    (hdet : c ≤ ‖place (LinearMap.det Λ)‖)
    (hcomp : ∀ z : Z, (z : E) ∈ localCoordinateLattice place b →
      ((Λ (T z) : Z) : E) ∈ localCoordinateLattice place b) :
    ‖place (LinearMap.det T)‖ ≤ c⁻¹ := by
  have hle : ‖place (LinearMap.det (Λ ∘ₗ T))‖ ≤ 1 :=
    norm_det_le_one_of_preserves_localCoordinateLattice place b Z (Λ ∘ₗ T) hcomp
  rw [LinearMap.det_comp, map_mul, norm_mul] at hle
  have hmul := (mul_le_mul_of_nonneg_right hdet (norm_nonneg _)).trans hle
  rwa [← le_div_iff₀' hc, one_div] at hmul

/-- Compression of an ambient operator to `Z` by orthogonal projection. -/
def liftCompression {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (Z : Submodule 𝕜 E)
    (U : Module.End 𝕜 E) : Module.End 𝕜 Z :=
  Z.orthogonalProjectionOnto.toLinearMap ∘ₗ U ∘ₗ Z.subtype

/-- A compression evaluates by projecting the ambient image. -/
@[simp]
theorem liftCompression_apply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (Z : Submodule 𝕜 E) (U : Module.End 𝕜 E)
    (z : Z) :
    liftCompression Z U z = Z.orthogonalProjectionOnto (U z) := by
  simp [liftCompression]

/-- If `U` preserves the coordinate lattice on `Z` and maps `Z` into `admissible`, while `Λ`
clears the projection of every integral admissible vector, then a lower bound
`exp (-c) ≤ ‖place (det Λ)‖` yields `‖place (det (liftCompression Z U))‖ ≤ exp c`. -/
theorem norm_padic_det_liftCompression_le {ι 𝕜 E K : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedField K] [IsUltrametricDist K] (place : 𝕜 →+* K) (b : Module.Basis ι 𝕜 E)
    (Z : Submodule 𝕜 E) (U : Module.End 𝕜 E) (Λ : Module.End 𝕜 Z)
    (c : ℝ) (admissible : Set E)
    (hdet : Real.exp (-c) ≤ ‖place (LinearMap.det Λ)‖)
    (hU_lattice : ∀ z : Z, (z : E) ∈ localCoordinateLattice place b →
      U (z : E) ∈ localCoordinateLattice place b)
    (hU_admissible : ∀ z : Z, U (z : E) ∈ admissible)
    (hΛ_projection : ∀ y : E, y ∈ admissible → y ∈ localCoordinateLattice place b →
      ((Λ (Z.orthogonalProjectionOnto y) : Z) : E) ∈ localCoordinateLattice place b) :
    ‖place (LinearMap.det (liftCompression Z U))‖ ≤ Real.exp c := by
  have hle := norm_det_le_inv_of_comp_preserves_localCoordinateLattice place b Z
    (liftCompression Z U) Λ (Real.exp_pos (-c)) hdet fun z hz ↦ by
      simpa only [liftCompression_apply] using
        hΛ_projection (U (z : E)) (hU_admissible z) (hU_lattice z hz)
  simpa [Real.exp_neg] using hle

/-- A denominator with archimedean bound `c_arch` and numerator bounds `s * β ℓ` gives a height
bound for the determinant-ratio family when finite prime sums of `β` are bounded by `β_tot` and
`0 ≤ s`. -/
theorem heightLe_determinant_ratio (det_comp : TauCeti.PrimePadicIso → ℂ) (det_base : ℂ)
    (s c_arch β_tot : ℝ) (β : ℕ → ℝ)
    (h_arch : ∀ σ : ℂ ≃+* ℂ, ‖σ det_base‖ ≤ Real.exp c_arch)
    (h_padic : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (det_comp ι)‖ ≤ Real.exp (s * β ι.prime))
    (hβ_sum : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, β ℓ ≤ β_tot)
    (hs : 0 ≤ s) :
    TauCeti.PrimePadicIso.HeightLe (fun ι ↦ det_comp ι / det_base)
      (c_arch + s * β_tot) := by
  by_cases hbase : det_base = 0
  · subst det_base
    apply (TauCeti.PrimePadicIso.heightLe_zero (c_arch + s * β_tot)).mono le_rfl
    intro ι
    simp
  refine TauCeti.PrimePadicIso.HeightLe.of_mul_le hbase h_arch
    (fun ℓ ↦ s * β ℓ) (fun ι ↦ ?_) (fun S hS ↦ ?_)
  · simpa only [mul_div_cancel₀ _ hbase] using h_padic ι
  · calc
      c_arch + ∑ ℓ ∈ S, s * β ℓ = c_arch + s * ∑ ℓ ∈ S, β ℓ := by
        rw [Finset.mul_sum]
      _ ≤ c_arch + s * β_tot :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hβ_sum S hS) hs)

/-- The lift volume ratio has height at most `d * c_γ + c_arch + s * β_tot`. -/
theorem heightLe_liftDeterminant_ratio (vol_ratio γ_ratio det_comp : TauCeti.PrimePadicIso → ℂ)
    (det_base : ℂ) (d : ℕ) (s c_γ c_arch β_tot : ℝ) (β : ℕ → ℝ)
    (hvol : ∀ ι, vol_ratio ι = (γ_ratio ι)⁻¹ ^ d * (det_comp ι / det_base))
    (hγ : TauCeti.PrimePadicIso.HeightLe (fun ι ↦ (γ_ratio ι)⁻¹) c_γ)
    (h_arch : ∀ σ : ℂ ≃+* ℂ, ‖σ det_base‖ ≤ Real.exp c_arch)
    (h_padic : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (det_comp ι)‖ ≤ Real.exp (s * β ι.prime))
    (hβ_sum : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, β ℓ ≤ β_tot)
    (hs : 0 ≤ s) :
    TauCeti.PrimePadicIso.HeightLe vol_ratio (d * c_γ + c_arch + s * β_tot) := by
  have hdet := heightLe_determinant_ratio det_comp det_base s c_arch β_tot β
    h_arch h_padic hβ_sum hs
  refine ((hγ.pow d).mul hdet).mono (by rw [add_assoc]) fun ι ↦ ?_
  simp only [hvol, Pi.mul_apply, Pi.pow_apply]
  exact le_rfl

end TauCeti.ThetaLift
