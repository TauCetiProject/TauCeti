/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Lie.CartanExists
public import TauCeti.Algebra.Lie.CompactRealForm.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre.ChevalleyInvolution
public import TauCeti.Algebra.Lie.Weights.Chevalley.Twist
public import TauCeti.Algebra.Lie.Weights.Positivity.RootVector
public import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Weights.Killing

/-!
# Existence of a compact real form

Every finite-dimensional complex Lie algebra `L` with nondegenerate Killing form has a compact real
form (Knapp, Theorem 6.11; Helgason, Chapter III, Theorem 6.3).

Choose a splitting Cartan subalgebra `H`, a base `b` of its root system, and a Chevalley system:
a Lie automorphism `ω` acting by `-1` on `H` together with root vectors `x α`, normalised by
`⁅x α, x (-α)⁆ = α∨`, with `ω (x α) = -x (-α)`. The automorphism `ω` is the Chevalley involution
of the Serre presentation of `L`, transported along Serre's theorem
(`LieSubalgebra.exists_lieEquiv_forall_mem_apply_eq_neg`); over an algebraically closed field the
root vectors can then be rescaled into a Chevalley system for it
(`TauCeti.exists_isChevalleySystem_of_isAlgClosed`).

The root vectors and the simple coroots form a basis of `L` whose structure constants are integers.
The conjugation `σ` of the coordinates in this basis (`Module.Basis.coordConj`) therefore preserves
brackets (`Module.Basis.isLieConjugation_coordConj`), and it commutes with `ω`, which preserves the
integral span of the basis. Their composite `τ = σ ∘ ω`
(`TauCeti.IsChevalleySystem.compactConjugation`) is a conjugation with `τ (x α) = -x (-α)` and
`τ α∨ = -α∨`.

Its Hermitian Killing form `H_τ(v, v) = -B(v, τ v)` is positive definite
(`TauCeti.IsChevalleySystem.isCompactConjugation_compactConjugation`). Writing
`v = ∑ a_α x α + ∑ a_i αᵢ∨`, the root spaces of `α` and `-β` are Killing-orthogonal unless
`α = β`, and orthogonal to `H`, so

```text
H_τ(v, v) = ∑_α |a_α|² B(x α, x (-α)) + ∑_γ |γ(h)|²,    h = ∑ a_i αᵢ∨,
```

the second sum running over the roots and coming from `B(h, h') = ∑_γ γ(h) γ(h')` on `H` and the
integrality of `γ(αᵢ∨)`. Each `B(x α, x (-α)) = 2 / ⟨α, α⟩` is a positive rational, and the roots
separate the points of `H`.

## Main definitions

* `TauCeti.IsChevalleySystem.compactConjugation`: the compact conjugation of a Chevalley system.

## Main results

* `TauCeti.IsChevalleySystem.killingHermitianForm_compactConjugation_self`: the formula for
  `H_τ(v, v)` above.
* `TauCeti.IsChevalleySystem.isCompactConjugation_compactConjugation`: the compact conjugation
  of a Chevalley system is compact.
* `TauCeti.exists_isCompactConjugation`: every finite-dimensional complex Lie algebra with
  nondegenerate Killing form has a compact real form.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Section VI.1.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, Section 6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling

open scoped ComplexOrder

namespace TauCeti

/-! ### The compact conjugation of a Chevalley system -/

namespace IsChevalleySystem

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra] [IsTriangularizable ℂ H L] {ω : L ≃ₗ⁅ℂ⁆ L}
  {x : Weight ℂ H L → L}
  (hx : IsChevalleySystem ω x) (b : (rootSystem H).Base)

/-- The conjugation fixing the root vectors and simple coroots fixes the Chevalley Lie lattice. -/
theorem coordConj_eq_self_of_mem_chevalleyLieLattice {z : L} (hz : z ∈ hx.chevalleyLieLattice) :
    (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj z = z := by
  lift z to hx.chevalleyLieLattice using hz with w
  have h : (w : L) = ∑ k, (hx.rootSimpleCorootBasis b).repr w k •
      hx.toIsSl2System.rootSimpleCorootFieldBasis b k := by
    conv_lhs => rw [← (hx.rootSimpleCorootBasis b).sum_repr w]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [SetLike.val_smul, coe_rootSimpleCorootBasis]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_zsmul, Module.Basis.coordConj_self]

/-- The basis of root vectors and simple coroots lies in the Chevalley Lie lattice. -/
theorem rootSimpleCorootFieldBasis_mem_chevalleyLieLattice (k : H.root ⊕ b.support) :
    hx.toIsSl2System.rootSimpleCorootFieldBasis b k ∈ hx.chevalleyLieLattice := by
  rw [← coe_rootSimpleCorootBasis]
  exact (hx.rootSimpleCorootBasis b k).property

/-- The Chevalley involution sends the basis of root vectors and simple coroots into the Chevalley
Lie lattice. -/
theorem apply_rootSimpleCorootFieldBasis_mem_chevalleyLieLattice (k : H.root ⊕ b.support) :
    ω (hx.toIsSl2System.rootSimpleCorootFieldBasis b k) ∈ hx.chevalleyLieLattice := by
  rcases k with α | i
  · rw [IsSl2System.rootSimpleCorootFieldBasis_inl, hx.map_root]
    exact neg_mem (hx.rootVector_mem_chevalleyLieLattice _)
  · rw [IsSl2System.rootSimpleCorootFieldBasis_inr, hx.map_coroot]
    exact neg_mem (hx.coroot_mem_chevalleyLieLattice _)

/-- The conjugation fixing the root vectors and simple coroots commutes with the Chevalley
involution. -/
theorem coordConj_apply_comm (z : L) :
    (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj (ω z) =
      ω ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj z) := by
  have h : (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj.toLinearMap.comp
      ω.toLieHom.toLinearMap =
      ω.toLieHom.toLinearMap.comp
        (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj.toLinearMap :=
    (hx.toIsSl2System.rootSimpleCorootFieldBasis b).ext fun k ↦ by
      simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom,
        LinearEquiv.coe_coe, Module.Basis.coordConj_self]
      exact hx.coordConj_eq_self_of_mem_chevalleyLieLattice b
        (hx.apply_rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b k)
  exact DFunLike.congr_fun h z

/-- The **compact conjugation** of a Chevalley system: the Chevalley involution `ω`, followed by
the conjugation of the coordinates in the basis of root vectors and simple coroots of `b`. It sends
`x α` to `-x (-α)` and `α∨` to `-α∨`. -/
noncomputable def compactConjugation : L →ₛₗ[starRingEnd ℂ] L :=
  (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj.toLinearMap.comp ω.toLieHom.toLinearMap

/-- The compact conjugation is `ω` followed by the conjugation of coordinates. -/
theorem compactConjugation_apply (z : L) :
    hx.compactConjugation b z = (hx.toIsSl2System.rootSimpleCorootFieldBasis b).coordConj (ω z) :=
  (rfl)

/-- The compact conjugation sends `x α` to `-x (-α)`. -/
@[simp]
theorem compactConjugation_rootVector (α : Weight ℂ H L) :
    hx.compactConjugation b (x α) = -x (-α) := by
  rw [compactConjugation_apply, hx.map_root, map_neg,
    hx.coordConj_eq_self_of_mem_chevalleyLieLattice b (hx.rootVector_mem_chevalleyLieLattice _)]

/-- The compact conjugation sends `α∨` to `-α∨`. -/
@[simp]
theorem compactConjugation_coroot (α : Weight ℂ H L) :
    hx.compactConjugation b (coroot α) = -(coroot α : L) := by
  rw [compactConjugation_apply, hx.map_coroot, map_neg,
    hx.coordConj_eq_self_of_mem_chevalleyLieLattice b (hx.coroot_mem_chevalleyLieLattice _)]

/-- **The compact conjugation is a conjugation.** -/
theorem isLieConjugation_compactConjugation : IsLieConjugation (hx.compactConjugation b) where
  map_lie y z := by
    have hσ := (hx.toIsSl2System.rootSimpleCorootFieldBasis b).isLieConjugation_coordConj
      fun i j ↦ hx.coordConj_eq_self_of_mem_chevalleyLieLattice b <|
        hx.chevalleyLieLattice.lie_mem (hx.rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b i)
          (hx.rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b j)
    rw [compactConjugation_apply, compactConjugation_apply, compactConjugation_apply,
      LieEquiv.map_lie]
    simpa only [LinearEquiv.coe_coe] using hσ.map_lie (ω y) (ω z)
  involutive z := by
    rw [compactConjugation_apply, compactConjugation_apply, ← hx.coordConj_apply_comm b,
      Module.Basis.coordConj_coordConj, hx.involutive z]

/-! ### Positivity of the Hermitian Killing form -/

/-- The Hermitian Killing form of the compact conjugation, in the coordinates of the basis of root
vectors and simple coroots. -/
theorem killingHermitianForm_compactConjugation_eq_sum (v : L) :
    (hx.compactConjugation b).killingHermitianForm v v =
      ∑ k, ∑ l, (hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v k *
        star ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v l) *
          -killingForm ℂ L (hx.toIsSl2System.rootSimpleCorootFieldBasis b k)
            (ω (hx.toIsSl2System.rootSimpleCorootFieldBasis b l)) := by
  set c := hx.toIsSl2System.rootSimpleCorootFieldBasis b
  rw [← (hx.compactConjugation b).killingHermitianForm.sum_repr_mul_repr_mulₛₗ c c v v,
    Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [LinearMap.killingHermitianForm_def, compactConjugation_apply,
    hx.coordConj_eq_self_of_mem_chevalleyLieLattice b
      (hx.apply_rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b l),
    RingHom.id_apply, starRingEnd_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- **The Hermitian Killing form of the compact conjugation.** For `v = ∑ a_α x α + ∑ aᵢ αᵢ∨`,
`H_τ(v, v) = ∑_α |a_α|² B(x α, x (-α)) + ∑_γ |γ(h)|²` with `h = ∑ aᵢ αᵢ∨`. -/
theorem killingHermitianForm_compactConjugation_self (v : L) :
    (hx.compactConjugation b).killingHermitianForm v v =
      ∑ α : H.root, (Complex.normSq
          ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v (Sum.inl α)) : ℂ) *
            killingForm ℂ L (x α) (x (-α)) +
        ∑ γ ∈ H.root, (Complex.normSq (γ (∑ i,
          ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v (Sum.inr i)) •
            coroot (i : Weight ℂ H L))) : ℂ) := by
  have hcart (α : H.root) (j : b.support) :
      killingForm ℂ L (x α) (coroot (j : Weight ℂ H L)) = 0 :=
    hx.toIsSl2System.killingForm_rootVector_cartan_eq_zero (H.isNonZero_coe_root α) _
  have hcart' (i : b.support) (β : H.root) :
      killingForm ℂ L (coroot (i : Weight ℂ H L)) (x (-(β : Weight ℂ H L))) = 0 := by
    rw [LieModule.traceForm_comm]
    exact hx.toIsSl2System.killingForm_rootVector_cartan_eq_zero
      (Weight.IsNonZero.neg (H.isNonZero_coe_root β)) _
  rw [hx.killingHermitianForm_compactConjugation_eq_sum b, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, IsSl2System.rootSimpleCorootFieldBasis_inl,
    IsSl2System.rootSimpleCorootFieldBasis_inr, hx.map_root, hx.map_coroot, map_neg, neg_neg,
    hcart, hcart', mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [sum_sum_mul_star_killingForm_coroot]
  congr 1
  · refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [Finset.sum_eq_single α (fun β _ hβ ↦ by
        rw [hx.toIsSl2System.killingForm_rootVector_neg_eq_zero_of_ne
          fun h ↦ hβ (Subtype.ext h).symm, mul_zero])
      (by simp), ← Complex.mul_conj, starRingEnd_apply]
  · exact Finset.sum_congr rfl fun γ _ ↦ Complex.mul_conj _

/-- **The compact conjugation of a Chevalley system is compact**: its Hermitian Killing form
`-B(v, τ v)` is positive definite. -/
theorem isCompactConjugation_compactConjugation :
    IsCompactConjugation (hx.compactConjugation b) where
  toIsLieConjugation := hx.isLieConjugation_compactConjugation b
  pos v hv := by
    set c := hx.toIsSl2System.rootSimpleCorootFieldBasis b
    choose q hq hqB using fun α : H.root ↦
      hx.toIsSl2System.exists_pos_rat_killingForm_rootVector_neg (H.isNonZero_coe_root α)
    set r : H.root → ℝ := fun α ↦ q α
    have hr (α : H.root) : 0 < r α := Rat.cast_pos.mpr (hq α)
    have hrB (α : H.root) : killingForm ℂ L (x α) (x (-α)) = r α := by
      rw [hqB]
      simp [r]
    set h : H := ∑ i, c.repr v (Sum.inr i) • coroot (i : Weight ℂ H L) with hh
    have key : (hx.compactConjugation b).killingHermitianForm v v =
        ((∑ α : H.root, Complex.normSq (c.repr v (Sum.inl α)) * r α +
          ∑ γ ∈ H.root, Complex.normSq (γ h) : ℝ) : ℂ) := by
      rw [hx.killingHermitianForm_compactConjugation_self b]
      push_cast
      simp only [hrB, hh, c]
    rw [key, Complex.zero_lt_real]
    have h1 : 0 ≤ ∑ α : H.root, Complex.normSq (c.repr v (Sum.inl α)) * r α :=
      Finset.sum_nonneg fun α _ ↦ mul_nonneg (Complex.normSq_nonneg _) (hr α).le
    have h2 : 0 ≤ ∑ γ ∈ H.root, Complex.normSq (γ h) :=
      Finset.sum_nonneg fun γ _ ↦ Complex.normSq_nonneg _
    by_contra hle
    have e1 : ∑ α : H.root, Complex.normSq (c.repr v (Sum.inl α)) * r α = 0 := by linarith
    have e2 : ∑ γ ∈ H.root, Complex.normSq (γ h) = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun α _ ↦
      mul_nonneg (Complex.normSq_nonneg _) (hr α).le] at e1
    rw [Finset.sum_eq_zero_iff_of_nonneg fun γ _ ↦ Complex.normSq_nonneg _] at e2
    have hinl (α : H.root) : c.repr v (Sum.inl α) = 0 :=
      Complex.normSq_eq_zero.mp
        ((mul_eq_zero.mp (e1 α (Finset.mem_univ _))).resolve_right (hr α).ne')
    have h0 : h = 0 :=
      eq_zero_of_forall_root_apply_eq_zero fun γ hγ ↦ Complex.normSq_eq_zero.mp (e2 γ hγ)
    apply hv
    rw [← c.sum_repr v, Fintype.sum_sum_type]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add, c,
      IsSl2System.rootSimpleCorootFieldBasis_inr]
    simpa [hh] using congrArg Subtype.val h0

end IsChevalleySystem

/-- **Existence of a compact real form.** Every finite-dimensional complex Lie algebra with
nondegenerate Killing form has a compact conjugation, whose fixed points are a real form of it with
negative definite Killing form (`TauCeti.IsCompactConjugation.killingForm_realForm_self_neg`). -/
theorem exists_isCompactConjugation (L : Type*) [LieRing L] [LieAlgebra ℂ L] [IsKilling ℂ L] :
    ∃ τ : L →ₛₗ[starRingEnd ℂ] L, IsCompactConjugation τ := by
  have := finite_of_isKilling (R := ℂ) (L := L)
  obtain ⟨H, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base ℂ L
  obtain ⟨ω, hω⟩ := H.exists_lieEquiv_forall_mem_apply_eq_neg
  obtain ⟨x, hx⟩ := exists_isChevalleySystem_of_isAlgClosed hω
  exact ⟨_, hx.isCompactConjugation_compactConjugation b⟩

end TauCeti
