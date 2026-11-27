/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.NumberTheory.NumberField.Global.Adeles.FinitePoints
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Norm-one vectors in finite adelic lattices

For a CM number field `E` and a finite adelic frame `g`, the rational norm-one vectors of the
lattice `g Ô^ι` are the vectors `x : ι → E` with `star x ⬝ᵥ x = 1` and `g⁻¹ x` integral at every
finite place. This set is finite: the lattice condition puts the finite components in a compact
set, while the norm equation bounds every coordinate at every infinite place by one.

Right multiplication of the frame by an integral invertible matrix leaves this set unchanged.
A rational unitary change of frame transports it bijectively. In particular, its cardinality is
a function on rational unitary classes of lattices, as needed in mass and representation counts.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField Matrix
open scoped NumberField.AdeleRing ComplexConjugate

namespace Matrix.GeneralLinearGroup

variable {E ι : Type*} [Field E] [NumberField E] [IsCMField E]
  [Fintype ι] [DecidableEq ι]

/-- Rational vectors of hermitian norm one in the lattice `g Ô^ι` of a finite adelic frame. -/
def normOneLatticeVectors (g : GL ι 𝔸ᶠ[E]) : Set (ι → E) :=
  {x | star x ⬝ᵥ x = 1 ∧
    ∀ i, (((g⁻¹ : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
      (fun j ↦ algebraMap E 𝔸ᶠ[E] (x j))) i ∈ integralAdeles (𝓞 E) E}

/-- Membership is the norm equation together with the integrality of the inverse-frame
coordinates. -/
theorem mem_normOneLatticeVectors_iff (g : GL ι 𝔸ᶠ[E]) (x : ι → E) :
    x ∈ g.normOneLatticeVectors ↔ star x ⬝ᵥ x = 1 ∧
      ∀ i, (((g⁻¹ : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
        (fun j ↦ algebraMap E 𝔸ᶠ[E] (x j))) i ∈ integralAdeles (𝓞 E) E :=
  Iff.rfl

/-- The zero vector never has norm one. -/
@[simp]
theorem zero_notMem_normOneLatticeVectors (g : GL ι 𝔸ᶠ[E]) :
    (0 : ι → E) ∉ g.normOneLatticeVectors := by
  simp [mem_normOneLatticeVectors_iff]

/-- A norm-one lattice vector is nonzero. -/
theorem ne_zero_of_mem_normOneLatticeVectors (g : GL ι 𝔸ᶠ[E])
    {x : ι → E} (hx : x ∈ g.normOneLatticeVectors) : x ≠ 0 := by
  rintro rfl
  exact g.zero_notMem_normOneLatticeVectors hx

/-- The lattice condition can equivalently be given by integral coefficients in the frame. -/
theorem mem_normOneLatticeVectors_iff_exists (g : GL ι 𝔸ᶠ[E]) (x : ι → E) :
    x ∈ g.normOneLatticeVectors ↔ star x ⬝ᵥ x = 1 ∧
      ∃ v : ι → integralAdeles (𝓞 E) E,
        (g : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (fun i ↦ (v i : 𝔸ᶠ[E])) =
          (fun i ↦ algebraMap E 𝔸ᶠ[E] (x i)) := by
  rw [mem_normOneLatticeVectors_iff]
  constructor
  · rintro ⟨hx, hv⟩
    exact ⟨hx, fun i ↦ ⟨_, hv i⟩, mulVec_inv_mulVec g _⟩
  · rintro ⟨hx, v, hv⟩
    refine ⟨hx, fun i ↦ ?_⟩
    rw [← hv, inv_mulVec_mulVec]
    exact (v i).property

/-- Negation preserves the norm-one vectors of every lattice. -/
@[simp]
theorem neg_mem_normOneLatticeVectors_iff (g : GL ι 𝔸ᶠ[E]) (x : ι → E) :
    -x ∈ g.normOneLatticeVectors ↔ x ∈ g.normOneLatticeVectors := by
  simp only [mem_normOneLatticeVectors_iff, star_neg, neg_dotProduct, dotProduct_neg,
    neg_neg, Pi.neg_apply, map_neg, ← Pi.neg_def, mulVec_neg, neg_mem_iff]

/-- Every finite adelic lattice has finitely many rational vectors of hermitian norm one. -/
theorem finite_normOneLatticeVectors (g : GL ι 𝔸ᶠ[E]) : g.normOneLatticeVectors.Finite := by
  let C : Set (ι → 𝔸ᶠ[E]) :=
    (fun v ↦ (g : Matrix ι ι 𝔸ᶠ[E]) *ᵥ v) ''
      {v | ∀ i, v i ∈ integralAdeles (𝓞 E) E}
  have hC : IsCompact C := by
    apply (isCompact_pi_infinite (s := fun _ : ι ↦
      (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E])) fun _ ↦ isCompact_integralAdeles).image
    exact continuous_const.matrix_mulVec continuous_id
  refine (TauCeti.GlobalNumberFields.finite_setOf_infinitePlace_le_and_finiteAdele_vector_mem
    hC 1).subset fun x hx ↦ ?_
  obtain ⟨hnorm, v, hv⟩ := (g.mem_normOneLatticeVectors_iff_exists x).1 hx
  refine ⟨?_, ⟨fun i ↦ (v i : 𝔸ᶠ[E]), fun i ↦ (v i).property, hv⟩⟩
  · intro i w
    have hsum : ∑ j, ‖w.embedding (x j)‖ ^ 2 = 1 := by
      rw [IsCMField.sum_norm_sq_eq_re_star_dotProduct, hnorm, map_one, Complex.one_re]
    have hi : ‖w.embedding (x i)‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖w.embedding (x j)‖) (Finset.mem_univ i)
    rw [← InfinitePlace.norm_embedding_eq]
    nlinarith [norm_nonneg (w.embedding (x i))]

/-- Norm-one lattice vectors carry a finite type, without choosing an enumeration. -/
instance instFiniteNormOneLatticeVectors (g : GL ι 𝔸ᶠ[E]) : Finite g.normOneLatticeVectors :=
  g.finite_normOneLatticeVectors.to_subtype

/-- At the identity frame, membership means norm one and integral rational coordinates. -/
theorem mem_normOneLatticeVectors_one_iff (x : ι → E) :
    x ∈ (1 : GL ι 𝔸ᶠ[E]).normOneLatticeVectors ↔
      star x ⬝ᵥ x = 1 ∧ ∀ i, x i ∈ (algebraMap (𝓞 E) E).range := by
  simp only [mem_normOneLatticeVectors_iff, inv_one, coe_one, one_mulVec,
    algebraMap_mem_integralAdeles_iff]

/-- Every standard basis vector has norm one in the standard integral lattice. -/
@[simp]
theorem single_mem_normOneLatticeVectors_one (i : ι) :
    Pi.single i (1 : E) ∈ (1 : GL ι 𝔸ᶠ[E]).normOneLatticeVectors := by
  rw [mem_normOneLatticeVectors_one_iff]
  constructor
  · simp [dotProduct_single]
  · intro j
    by_cases h : j = i <;> simp [h]

/-- Changing the integral basis of a finite adelic lattice does not change its norm-one vectors. -/
@[simp]
theorem normOneLatticeVectors_mul_integral (g : GL ι 𝔸ᶠ[E])
    (k : GL ι (integralAdeles (𝓞 E) E)) :
    (g * map (integralAdeles (𝓞 E) E).val k).normOneLatticeVectors =
      g.normOneLatticeVectors := by
  have h (a : GL ι 𝔸ᶠ[E]) (b : GL ι (integralAdeles (𝓞 E) E))
      {x : ι → E} (hx : x ∈ a.normOneLatticeVectors) :
      x ∈ (a * map (integralAdeles (𝓞 E) E).val b).normOneLatticeVectors := by
    obtain ⟨hnorm, v, hv⟩ := (a.mem_normOneLatticeVectors_iff_exists x).1 hx
    refine ((a * map _ b).mem_normOneLatticeVectors_iff_exists x).2
      ⟨hnorm, ((b⁻¹ : GL ι (integralAdeles (𝓞 E) E)) : Matrix _ _ _) *ᵥ v, ?_⟩
    have hb : ((map (integralAdeles (𝓞 E) E).val b : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
        (fun i ↦ ((((b⁻¹ : GL ι _) : Matrix _ _ _) *ᵥ v) i : 𝔸ᶠ[E])) =
          fun i ↦ (v i : 𝔸ᶠ[E]) := by
      have h := map_mulVec ((integralAdeles (𝓞 E) E).val : _ →+* 𝔸ᶠ[E]) b
        (((b⁻¹ : GL ι _) : Matrix _ _ _) *ᵥ v)
      rwa [mulVec_inv_mulVec] at h
    rw [coe_mul, ← mulVec_mulVec, hb, hv]
  ext x
  exact ⟨fun hx ↦ by simpa using h (g * map _ k) k⁻¹ hx, h g k⟩

/-- A rational unitary change of frame carries norm-one vectors to norm-one vectors, with an
exact membership equivalence. -/
theorem mulVec_mem_normOneLatticeVectors_iff (g : GL ι 𝔸ᶠ[E]) (γ : unitaryGroup ι E)
    (x : ι → E) :
    (γ : Matrix ι ι E) *ᵥ x ∈
        (map (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) * g).normOneLatticeVectors ↔
      x ∈ g.normOneLatticeVectors := by
  have hmap : (fun i ↦ algebraMap E 𝔸ᶠ[E] (((γ : Matrix ι ι E) *ᵥ x) i)) =
      (map (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
        (fun i ↦ algebraMap E 𝔸ᶠ[E] (x i)) :=
    (map_mulVec (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) x).symm
  rw [mem_normOneLatticeVectors_iff, mem_normOneLatticeVectors_iff,
    star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup γ.property, hmap]
  simp only [_root_.mul_inv_rev, coe_mul, ← mulVec_mulVec, inv_mulVec_mulVec]

/-- The bijection of norm-one vectors induced by a rational unitary change of frame. -/
def normOneLatticeVectorsEquiv (g : GL ι 𝔸ᶠ[E]) (γ : unitaryGroup ι E) :
    g.normOneLatticeVectors ≃
      (map (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) * g).normOneLatticeVectors :=
  (toLin (Unitary.toUnits γ)).toLinearEquiv.toEquiv.subtypeEquiv fun x ↦ by
    simpa using (g.mulVec_mem_normOneLatticeVectors_iff γ x).symm

/-- The rational unitary bijection acts on the underlying vectors by matrix multiplication. -/
@[simp]
theorem normOneLatticeVectorsEquiv_apply (g : GL ι 𝔸ᶠ[E]) (γ : unitaryGroup ι E)
    (x : g.normOneLatticeVectors) :
    (g.normOneLatticeVectorsEquiv γ x).val = (γ : Matrix ι ι E) *ᵥ x.val := by
  simp only [normOneLatticeVectorsEquiv, Equiv.subtypeEquiv_apply,
    LinearEquiv.coe_toEquiv, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    toLin_apply, Matrix.mulVecLin_apply, Unitary.val_toUnits_apply]

/-- The inverse rational unitary bijection acts by the inverse matrix. -/
@[simp]
theorem normOneLatticeVectorsEquiv_symm_apply (g : GL ι 𝔸ᶠ[E]) (γ : unitaryGroup ι E)
    (y : (map (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) * g).normOneLatticeVectors) :
    ((g.normOneLatticeVectorsEquiv γ).symm y).val = ((γ⁻¹ : unitaryGroup ι E) : Matrix ι ι E) *ᵥ
      y.val := by
  have h := congrArg Subtype.val ((g.normOneLatticeVectorsEquiv γ).apply_symm_apply y)
  rw [normOneLatticeVectorsEquiv_apply] at h
  rw [← h, mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mulVec]

/-- The number of norm-one vectors is invariant under rational unitary changes and integral
changes of frame, so it descends to the corresponding double classes. -/
theorem card_normOneLatticeVectors_map_mul_mul_integral (g : GL ι 𝔸ᶠ[E]) (γ : unitaryGroup ι E)
    (k : GL ι (integralAdeles (𝓞 E) E)) :
    Nat.card ((map (algebraMap E 𝔸ᶠ[E]) (Unitary.toUnits γ) * g *
      map (integralAdeles (𝓞 E) E).val k).normOneLatticeVectors) =
        Nat.card g.normOneLatticeVectors := by
  rw [normOneLatticeVectors_mul_integral]
  exact (Nat.card_congr (g.normOneLatticeVectorsEquiv γ)).symm

end Matrix.GeneralLinearGroup
