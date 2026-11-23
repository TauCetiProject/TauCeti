/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CongruenceSubgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Topology
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Congruence levels of `GL₂` over the integral finite adeles

For a Dedekind domain `R` with fraction field `K` (for instance the ring of integers of a number
field), write `Ô = ∏_v 𝒪_v` for the integral finite adeles and `NÔ` for the completion
`IsDedekindDomain.FiniteAdeleRing.completedIdeal K N` of an integral ideal `N`. This file defines
the three congruence levels of `GL₂(𝔸_f)`:

* the principal level `K(N)`, the image along `TauCeti.GeneralLinear.pointsContinuousMulEquiv`
  and the inclusion `Ô ⊆ 𝔸_f` of Tau Ceti's congruence subgroup of level `NÔ` of the `Ô`-points
  of `GL₂`, that is, `{g ∈ GL₂(Ô) : g ≡ 1 mod NÔ}`;
* `K₀(N) = {g ∈ GL₂(Ô) : c ∈ NÔ}` and `K₁(N) = {g ∈ GL₂(Ô) : c ∈ NÔ, d - 1 ∈ NÔ}`, where
  `g = [[a, b], [c, d]]`.

No generator of `N` is chosen, so nonprincipal ideals are allowed. Membership is expressed
entrywise: integral entries, integral inverse entries and the congruence conditions. The levels
satisfy `K(N) ≤ K₁(N) ≤ K₀(N)`, are monotone in `N`, and are open for `N ≠ ⊥` and compact when
the residue fields of `R` are finite.

The underlying subgroups `TauCeti.GeneralLinear.gammaZero I` and `TauCeti.GeneralLinear.gammaOne I`
of `GL₂(A)` are defined for an ideal `I` of an arbitrary commutative ring `A`.

## Main declarations

* `TauCeti.GeneralLinear.gammaZero`, `TauCeti.GeneralLinear.gammaOne`: the subgroups of `GL₂(A)`
  with `c ∈ I`, respectively `c ∈ I` and `d - 1 ∈ I`.
* `IsDedekindDomain.FiniteAdeleRing.integralGL`: the inclusion `GL_n(Ô) → GL_n(𝔸_f)`, with range
  the matrices whose entries and inverse entries are integral (`mem_range_integralGL_iff`).
* `IsDedekindDomain.FiniteAdeleRing.principalLevel`, `levelOne`, `levelZero`: the levels `K(N)`,
  `K₁(N)` and `K₀(N)`, with entrywise membership criteria `mem_principalLevel_iff`,
  `mem_levelOne_iff` and `mem_levelZero_iff`.
* `IsDedekindDomain.FiniteAdeleRing.principalLevel_le_levelOne`,
  `levelOne_le_levelZero` and the monotonicity lemmas `principalLevel_mono`, `levelOne_mono`,
  `levelZero_mono`.
* `IsDedekindDomain.FiniteAdeleRing.isOpen_principalLevel`, `isCompact_principalLevel` and their
  analogues for `K₀(N)` and `K₁(N)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §4, p. 42.
* A. Borel, *Automorphic L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.7, p. 8.
-/

public section
noncomputable section

open Topology

namespace TauCeti.GeneralLinear

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The inverse of a `2 × 2` invertible matrix, entrywise. -/
private theorem coe_inv_fin_two (g : GL (Fin 2) A) :
    (↑g⁻¹ : Matrix (Fin 2) (Fin 2) A) =
      Ring.inverse (g : Matrix (Fin 2) (Fin 2) A).det •
        !![(g : Matrix (Fin 2) (Fin 2) A) 1 1, -(g : Matrix (Fin 2) (Fin 2) A) 0 1;
          -(g : Matrix (Fin 2) (Fin 2) A) 1 0, (g : Matrix (Fin 2) (Fin 2) A) 0 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]

/-- The determinant of an invertible matrix times its ring inverse is one. -/
private theorem inverse_det_mul_det (g : GL (Fin 2) A) :
    Ring.inverse (g : Matrix (Fin 2) (Fin 2) A).det * (g : Matrix (Fin 2) (Fin 2) A).det = 1 :=
  Ring.inverse_mul_cancel _ (Matrix.isUnit_det_of_left_inverse (B := ↑g⁻¹) g.inv_mul)

/-- The subgroup `Γ₀(I)` of `GL₂(A)`: the matrices `[[a, b], [c, d]]` with `c ∈ I`. -/
def gammaZero : Subgroup (GL (Fin 2) A) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hg hh ⊢
    exact add_mem (I.mul_mem_right _ hg) (I.mul_mem_left _ hh)
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [coe_inv_fin_two]
    simpa using I.mul_mem_left (Ring.inverse (g : Matrix (Fin 2) (Fin 2) A).det)
      (I.neg_mem_iff.mpr hg)

/-- Membership in `Γ₀(I)`. -/
@[simp]
theorem mem_gammaZero {g : GL (Fin 2) A} :
    g ∈ gammaZero I ↔ (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I :=
  Iff.rfl

/-- The subgroup `Γ₁(I)` of `GL₂(A)`: the matrices `[[a, b], [c, d]]` with `c ∈ I` and
`d - 1 ∈ I`. -/
def gammaOne : Subgroup (GL (Fin 2) A) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I ∧
    (g : Matrix (Fin 2) (Fin 2) A) 1 1 - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hg hh ⊢
    refine ⟨add_mem (I.mul_mem_right _ hg.1) (I.mul_mem_left _ hh.1), ?_⟩
    simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_mul, map_one] at hg hh ⊢
    linear_combination (Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) A) 1 1)) * hh.2 +
      (Ideal.Quotient.mk I ((h : Matrix (Fin 2) (Fin 2) A) 0 1)) * hg.1 + hg.2
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    refine ⟨(gammaZero I).inv_mem (x := g) hg.1, ?_⟩
    rw [coe_inv_fin_two]
    have hdet := congrArg (Ideal.Quotient.mk I) (inverse_det_mul_det g)
    generalize Ring.inverse (g : Matrix (Fin 2) (Fin 2) A).det = u at hdet ⊢
    simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, Matrix.det_fin_two,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, smul_eq_mul] at hg hdet ⊢
    linear_combination (-(Ideal.Quotient.mk I u) *
        Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) A) 0 0)) * hg.2 +
      (Ideal.Quotient.mk I u * Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) A) 0 1)) * hg.1 +
        hdet

/-- Membership in `Γ₁(I)`. -/
@[simp]
theorem mem_gammaOne {g : GL (Fin 2) A} :
    g ∈ gammaOne I ↔
      (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I ∧ (g : Matrix (Fin 2) (Fin 2) A) 1 1 - 1 ∈ I :=
  Iff.rfl

/-- The kernel of reduction modulo `I` is contained in `Γ₁(I)`. -/
theorem ker_map_le_gammaOne :
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker ≤ gammaOne I := by
  intro g hg
  have h := fun i j ↦
    congrArg (fun M : GL (Fin 2) (A ⧸ I) ↦ (M : Matrix (Fin 2) (Fin 2) (A ⧸ I)) i j) hg
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h
  refine ⟨Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h 1 0), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  simpa using h 1 1

/-- `Γ₁(I) ≤ Γ₀(I)`. -/
theorem gammaOne_le_gammaZero : gammaOne I ≤ gammaZero I :=
  fun _ hg ↦ hg.1

/-- `Γ₀` is monotone in the ideal. -/
theorem gammaZero_mono : Monotone (gammaZero (A := A)) :=
  fun _ _ hIJ _ hg ↦ hIJ hg

/-- `Γ₁` is monotone in the ideal. -/
theorem gammaOne_mono : Monotone (gammaOne (A := A)) :=
  fun _ _ hIJ _ hg ↦ ⟨hIJ hg.1, hIJ hg.2⟩

/-- `Γ₀` of the unit ideal is everything. -/
@[simp]
theorem gammaZero_top : gammaZero (⊤ : Ideal A) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ (mem_gammaZero _).mpr Submodule.mem_top

/-- `Γ₁` of the unit ideal is everything. -/
@[simp]
theorem gammaOne_top : gammaOne (⊤ : Ideal A) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ (mem_gammaOne _).mpr ⟨Submodule.mem_top, Submodule.mem_top⟩

end TauCeti.GeneralLinear

namespace IsDedekindDomain.FiniteAdeleRing

open TauCeti TauCeti.GeneralLinear

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Integral matrices -/

/-- The integral finite adeles are a topological ring. -/
instance instIsTopologicalRingIntegralAdeles : IsTopologicalRing (integralAdeles R K) :=
  inferInstanceAs (IsTopologicalRing (integralAdeles R K).toSubring)

variable (n : ℕ)

/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` induced by `Ô ⊆ 𝔸_f`. -/
abbrev integralGL : GL (Fin n) (integralAdeles R K) →* GL (Fin n) 𝔸ᶠ[R, K] :=
  Matrix.GeneralLinearGroup.map (integralAdeles R K).val.toRingHom

variable {K n}

/-- The entries of the image of an integral matrix. -/
theorem integralGL_apply (g : GL (Fin n) (integralAdeles R K)) (i j : Fin n) :
    (integralGL K n g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j =
      (g : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j :=
  (rfl)

/-- The entries of the inverse of the image of an integral matrix. -/
theorem integralGL_inv_apply (g : GL (Fin n) (integralAdeles R K)) (i j : Fin n) :
    (↑(integralGL K n g)⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j =
      (↑g⁻¹ : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j :=
  (rfl)

variable (K n) in
/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is injective. -/
theorem integralGL_injective : Function.Injective (integralGL K n (R := R)) := by
  intro g h hgh
  refine Units.ext <| Matrix.ext fun i j ↦ Subtype.ext ?_
  exact congrArg (fun M : GL (Fin n) 𝔸ᶠ[R, K] ↦ (M : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j) hgh

/-- A matrix in `GL_n(𝔸_f)` whose entries and inverse entries are integral, as an element of
`GL_n(Ô)`. -/
def integralLift (g : GL (Fin n) 𝔸ᶠ[R, K])
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K)
    (hg' : ∀ i j, (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) :
    GL (Fin n) (integralAdeles R K) where
  val := Matrix.of fun i j ↦ ⟨_, hg i j⟩
  inv := Matrix.of fun i j ↦ ⟨_, hg' i j⟩
  val_inv := by
    refine Matrix.ext fun i j ↦ Subtype.ext ?_
    have := congrArg (fun M : GL (Fin n) 𝔸ᶠ[R, K] ↦ (M : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j)
      (mul_inv_cancel g)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply]
    push_cast at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  inv_val := by
    refine Matrix.ext fun i j ↦ Subtype.ext ?_
    have := congrArg (fun M : GL (Fin n) 𝔸ᶠ[R, K] ↦ (M : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j)
      (inv_mul_cancel g)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply]
    push_cast at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

/-- The lift of an integral matrix maps back to it. -/
@[simp]
theorem integralGL_integralLift (g : GL (Fin n) 𝔸ᶠ[R, K])
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K)
    (hg' : ∀ i j, (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) :
    integralGL K n (integralLift g hg hg') = g :=
  Units.ext (Matrix.ext fun _ _ ↦ (rfl))

/-- The entries of the lift of an integral matrix. -/
@[simp]
theorem integralLift_apply (g : GL (Fin n) 𝔸ᶠ[R, K])
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K)
    (hg' : ∀ i j, (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K)
    (i j : Fin n) :
    (integralLift g hg hg' : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j = ⟨_, hg i j⟩ :=
  (rfl)

/-- A matrix in `GL_n(𝔸_f)` lies in `GL_n(Ô)` exactly when its entries and the entries of its
inverse are integral. -/
theorem mem_range_integralGL_iff {g : GL (Fin n) 𝔸ᶠ[R, K]} :
    g ∈ (integralGL K n).range ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
        ∀ i j, (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K := by
  refine ⟨?_, fun ⟨hg, hg'⟩ ↦ ⟨_, integralGL_integralLift g hg hg'⟩⟩
  rintro ⟨g, rfl⟩
  exact ⟨fun i j ↦ ((g : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j).property,
    fun i j ↦ ((↑g⁻¹ : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j).property⟩

/-- Membership in the image of a subgroup of `GL_n(Ô)`, in terms of the lift. -/
private theorem mem_map_integralGL_iff {H : Subgroup (GL (Fin n) (integralAdeles R K))}
    {g : GL (Fin n) 𝔸ᶠ[R, K]} :
    g ∈ H.map (integralGL K n) ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K)
        (hg' : ∀ i j, (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        integralLift g hg hg' ∈ H := by
  refine ⟨?_, fun ⟨hg, hg', h⟩ ↦ ⟨_, h, integralGL_integralLift g hg hg'⟩⟩
  rintro ⟨g, hgH, rfl⟩
  have hg (i j : Fin n) := ((g : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j).property
  have hg' (i j : Fin n) := ((↑g⁻¹ : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j).property
  refine ⟨hg, hg', ?_⟩
  rwa [integralGL_injective (R := R) K n (integralGL_integralLift (integralGL K n g) hg hg')]

variable (K n) in
/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is continuous. -/
theorem continuous_integralGL : Continuous (integralGL K n (R := R)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j ↦ ?_, continuous_matrix fun i j ↦ ?_⟩
  · exact continuous_subtypeVal.comp (Units.continuous_val.matrix_elem i j)
  · exact continuous_subtypeVal.comp (Units.continuous_coe_inv.matrix_elem i j)

/-! ### The levels -/

variable (K)

/-- The **principal congruence level** `K(N) ⊆ GL₂(𝔸_f)`: the image along
`TauCeti.GeneralLinear.pointsContinuousMulEquiv` and `Ô ⊆ 𝔸_f` of the congruence subgroup of
level `NÔ` of the `Ô`-points of `GL₂`, that is, `{g ∈ GL₂(Ô) : g - 1 ∈ M₂(NÔ)}`. -/
def principalLevel (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (HopfAlgebra.congruenceSubgroup R (coordinateHopfAlgebra R 2) (completedIdeal K N)).map
    ((integralGL K 2).comp
      (pointsContinuousMulEquiv (k := R) (R := integralAdeles R K) 2 :
        WithConv (coordinateHopfAlgebra R 2 →ₐ[R] integralAdeles R K) ≃*
          GL (Fin 2) (integralAdeles R K)).toMonoidHom)

/-- The **level `K₁(N)`** of `GL₂(𝔸_f)`: the matrices `[[a, b], [c, d]] ∈ GL₂(Ô)` with
`c ∈ NÔ` and `d - 1 ∈ NÔ`. -/
def levelOne (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (gammaOne (completedIdeal K N)).map (integralGL K 2)

/-- The **level `K₀(N)`** of `GL₂(𝔸_f)`: the matrices `[[a, b], [c, d]] ∈ GL₂(Ô)` with
`c ∈ NÔ`. -/
def levelZero (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (gammaZero (completedIdeal K N)).map (integralGL K 2)

/-- `K(N)` is the image of the kernel of reduction `GL₂(Ô) → GL₂(Ô ⧸ NÔ)`. -/
theorem principalLevel_eq_map_ker (N : Ideal R) :
    principalLevel K N =
      (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (completedIdeal K N))).ker.map (integralGL K 2) := by
  rw [principalLevel, coe_pointsContinuousMulEquiv, ← Subgroup.map_map,
    ← map_congruenceSubgroup (R := R)]

/-- `K₁(N)` is the image of `Γ₁(NÔ)`. -/
theorem levelOne_def (N : Ideal R) :
    levelOne K N = (gammaOne (completedIdeal K N)).map (integralGL K 2) :=
  (rfl)

/-- `K₀(N)` is the image of `Γ₀(NÔ)`. -/
theorem levelZero_def (N : Ideal R) :
    levelZero K N = (gammaZero (completedIdeal K N)).map (integralGL K 2) :=
  (rfl)

variable {K}

/-- Entrywise membership in `K(N)`: integral entries, integral inverse entries, and every entry of
`g - 1` in `NÔ`. -/
theorem mem_principalLevel_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ principalLevel K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          ∀ i j, (⟨_, hg i j⟩ - (1 : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) i j :
            integralAdeles R K) ∈ completedIdeal K N := by
  rw [principalLevel_eq_map_ker, mem_map_integralGL_iff]
  refine exists_congr fun hg ↦ ⟨fun ⟨hg', h⟩ ↦ ⟨hg', ?_⟩, fun ⟨hg', h⟩ ↦ ⟨hg', ?_⟩⟩
  · intro i j
    have := congrArg (fun M : GL (Fin 2) (integralAdeles R K ⧸ completedIdeal K N) ↦
      (M : Matrix (Fin 2) (Fin 2) (integralAdeles R K ⧸ completedIdeal K N)) i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one, integralLift_apply] at this
    rw [← Ideal.Quotient.eq, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]
  · rw [MonoidHom.mem_ker]
    refine Units.ext (Matrix.ext fun i j ↦ ?_)
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one, integralLift_apply]
    rw [Ideal.Quotient.eq.mpr (h i j), Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]

/-- Entrywise membership in `K₁(N)`: integral entries, integral inverse entries, `c ∈ NÔ` and
`d - 1 ∈ NÔ`. -/
theorem mem_levelOne_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ levelOne K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          (⟨_, hg 1 0⟩ : integralAdeles R K) ∈ completedIdeal K N ∧
            (⟨_, hg 1 1⟩ - 1 : integralAdeles R K) ∈ completedIdeal K N := by
  rw [levelOne, mem_map_integralGL_iff]
  exact exists_congr fun hg ↦ ⟨fun ⟨hg', h⟩ ↦ ⟨hg', h⟩, fun ⟨hg', h⟩ ↦ ⟨hg', h⟩⟩

/-- Entrywise membership in `K₀(N)`: integral entries, integral inverse entries and `c ∈ NÔ`. -/
theorem mem_levelZero_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ levelZero K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          (⟨_, hg 1 0⟩ : integralAdeles R K) ∈ completedIdeal K N := by
  rw [levelZero, mem_map_integralGL_iff]
  exact exists_congr fun hg ↦ ⟨fun ⟨hg', h⟩ ↦ ⟨hg', h⟩, fun ⟨hg', h⟩ ↦ ⟨hg', h⟩⟩

variable (K)

/-- `K(N) ≤ K₁(N)`. -/
theorem principalLevel_le_levelOne (N : Ideal R) : principalLevel K N ≤ levelOne K N := by
  rw [principalLevel_eq_map_ker, levelOne]
  exact Subgroup.map_mono (ker_map_le_gammaOne _)

/-- `K₁(N) ≤ K₀(N)`. -/
theorem levelOne_le_levelZero (N : Ideal R) : levelOne K N ≤ levelZero K N :=
  Subgroup.map_mono (gammaOne_le_gammaZero _)

/-- `K(M) ≤ K(N)` whenever `M ⊆ N`. -/
theorem principalLevel_mono : Monotone (principalLevel K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (HopfAlgebra.congruenceSubgroup_mono R (coordinateHopfAlgebra R 2)
    (integralAdeles R K) (completedIdeal_mono K h))

/-- `K₁(M) ≤ K₁(N)` whenever `M ⊆ N`. -/
theorem levelOne_mono : Monotone (levelOne K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (gammaOne_mono (completedIdeal_mono K h))

/-- `K₀(M) ≤ K₀(N)` whenever `M ⊆ N`. -/
theorem levelZero_mono : Monotone (levelZero K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (gammaZero_mono (completedIdeal_mono K h))

/-- For `N = R`, `K₀(N)` is `GL₂(Ô)`. -/
@[simp]
theorem levelZero_top : levelZero K (⊤ : Ideal R) = (integralGL K 2).range := by
  rw [levelZero, completedIdeal_top, gammaZero_top, ← MonoidHom.range_eq_map]

/-- For `N = R`, `K₁(N)` is `GL₂(Ô)`. -/
@[simp]
theorem levelOne_top : levelOne K (⊤ : Ideal R) = (integralGL K 2).range := by
  rw [levelOne, completedIdeal_top, gammaOne_top, ← MonoidHom.range_eq_map]

/-- For `N = R`, `K(N)` is `GL₂(Ô)`. -/
@[simp]
theorem principalLevel_top : principalLevel K (⊤ : Ideal R) = (integralGL K 2).range := by
  rw [principalLevel_eq_map_ker]
  refine le_antisymm (Subgroup.map_le_range _ _) ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨g, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, Units.val_one,
    ← Matrix.map_one (Ideal.Quotient.mk _) (map_zero _) (map_one _), Matrix.map_apply]
  exact Ideal.Quotient.eq.mpr (by simp)

/-! ### Topology -/

/-- For `N ≠ ⊥`, `K(N)` is open in `GL₂(𝔸_f)`. -/
theorem isOpen_principalLevel {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (principalLevel K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  -- `NÔ` is open in `𝔸_f`.
  set V : Set 𝔸ᶠ[R, K] := Subtype.val '' (completedIdeal K N : Set (integralAdeles R K))
  have hV : IsOpen V :=
    (isOpen_integralAdeles R K).isOpenMap_subtypeVal _ (isOpen_completedIdeal K hN)
  have hVO : V ⊆ integralAdeles R K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  have hδ (i j : Fin 2) : (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K := by
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hset : (principalLevel K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) =
      (⋂ i, ⋂ j, {g : GL (Fin 2) 𝔸ᶠ[R, K] | (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j -
        (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ V}) ∩
      ⋂ i, ⋂ j, {g : GL (Fin 2) 𝔸ᶠ[R, K] |
        (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K} := by
    ext g
    simp only [SetLike.mem_coe, mem_principalLevel_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    refine ⟨fun ⟨hg, hg', h⟩ ↦ ⟨fun i j ↦ ⟨_, h i j, ?_⟩, hg'⟩, fun ⟨h, hg'⟩ ↦ ?_⟩
    · rw [Subalgebra.coe_sub]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · have hg (i j : Fin 2) : (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K := by
        simpa using add_mem (hVO (h i j)) (hδ i j)
      refine ⟨hg, hg', fun i j ↦ ?_⟩
      obtain ⟨x, hx, hxe⟩ := h i j
      have hx' : (⟨_, hg i j⟩ - (1 : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) i j :
          integralAdeles R K) = x := by
        refine Subtype.ext ?_
        rw [hxe, Subalgebra.coe_sub]
        congr 1
        rw [Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hx']
      exact hx
  rw [hset]
  refine .inter (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ ?_)
    (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ ?_)
  · exact hV.preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  · exact (isOpen_integralAdeles R K).preimage (Units.continuous_coe_inv.matrix_elem i j)

/-- For `N ≠ ⊥`, `K₁(N)` is open in `GL₂(𝔸_f)`. -/
theorem isOpen_levelOne {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (levelOne K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) :=
  Subgroup.isOpen_mono (principalLevel_le_levelOne K N) (isOpen_principalLevel K hN)

/-- For `N ≠ ⊥`, `K₀(N)` is open in `GL₂(𝔸_f)`. -/
theorem isOpen_levelZero {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (levelZero K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) :=
  Subgroup.isOpen_mono (levelOne_le_levelZero K N) (isOpen_levelOne K hN)

variable (n) in
/-- The entries of an integral matrix depend continuously on it. -/
private theorem continuous_entry (i j : Fin n) :
    Continuous fun g : GL (Fin n) (integralAdeles R K) ↦
      (g : Matrix (Fin n) (Fin n) (integralAdeles R K)) i j :=
  Units.continuous_val.matrix_elem i j

/-- The image in `GL_n(𝔸_f)` of a closed subgroup of `GL_n(Ô)` is compact. -/
private theorem isCompact_map_integralGL [CompactSpace (GL (Fin n) (integralAdeles R K))]
    {H : Subgroup (GL (Fin n) (integralAdeles R K))}
    (hH : IsClosed (H : Set (GL (Fin n) (integralAdeles R K)))) :
    IsCompact (H.map (integralGL K n) : Set (GL (Fin n) 𝔸ᶠ[R, K])) := by
  rw [Subgroup.coe_map]
  exact hH.isCompact.image (continuous_integralGL K n)

variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- With finite residue fields, `GL_n(Ô)` is compact. -/
instance compactSpace_gl_integralAdeles : CompactSpace (GL (Fin n) (integralAdeles R K)) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  have : CompactSpace (integralAdeles R K) := isCompact_iff_compactSpace.mp isCompact_integralAdeles
  have : CompactSpace (Matrix (Fin n) (Fin n) (integralAdeles R K)) :=
    inferInstanceAs (CompactSpace (Fin n → Fin n → integralAdeles R K))
  infer_instance

/-- With finite residue fields and `N ≠ ⊥`, `K(N)` is compact. -/
theorem isCompact_principalLevel {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (principalLevel K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  rw [principalLevel_eq_map_ker]
  refine isCompact_map_integralGL K ?_
  have hset : ((Matrix.GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (completedIdeal K N))).ker : Set (GL (Fin 2) (integralAdeles R K))) =
      ⋂ i, ⋂ j, {g : GL (Fin 2) (integralAdeles R K) |
        (g : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) i j ∈ completedIdeal K N} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq,
      ← Ideal.Quotient.eq, Units.ext_iff, Matrix.ext_iff.symm, Matrix.GeneralLinearGroup.map_apply,
      Units.val_one]
    refine forall₂_congr fun i j ↦ ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]
  rw [hset]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ (isClosed_completedIdeal K hN).preimage
    ((continuous_entry K 2 i j).sub continuous_const)

/-- With finite residue fields and `N ≠ ⊥`, `K₁(N)` is compact. -/
theorem isCompact_levelOne {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (levelOne K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  refine isCompact_map_integralGL K ?_
  have hset : (gammaOne (completedIdeal K N) : Set (GL (Fin 2) (integralAdeles R K))) =
      (fun g : GL (Fin 2) (integralAdeles R K) ↦
        (g : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) 1 0) ⁻¹' completedIdeal K N ∩
      (fun g : GL (Fin 2) (integralAdeles R K) ↦
        (g : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) 1 1 - 1) ⁻¹' completedIdeal K N :=
    (rfl)
  rw [hset]
  exact ((isClosed_completedIdeal K hN).preimage (continuous_entry K 2 1 0)).inter
    ((isClosed_completedIdeal K hN).preimage ((continuous_entry K 2 1 1).sub continuous_const))

/-- With finite residue fields and `N ≠ ⊥`, `K₀(N)` is compact. -/
theorem isCompact_levelZero {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (levelZero K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) :=
  isCompact_map_integralGL K
    ((isClosed_completedIdeal K hN).preimage (continuous_entry K 2 1 0))

end IsDedekindDomain.FiniteAdeleRing
