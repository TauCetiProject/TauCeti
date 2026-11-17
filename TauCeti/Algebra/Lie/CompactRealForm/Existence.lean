/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Lie.CartanExists
public import TauCeti.Algebra.Lie.CompactRealForm.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
public import TauCeti.Algebra.Lie.Presentation.Serre.Injective
public import TauCeti.Algebra.Lie.Presentation.Serre.Killing
public import TauCeti.Algebra.Lie.Weights.Chevalley.Twist
public import TauCeti.Algebra.Lie.Weights.Positivity
public import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# Existence of a compact real form

Every finite-dimensional complex Lie algebra `L` with nondegenerate Killing form has a compact real
form (Knapp, Theorem 6.11; Helgason, Chapter III, Theorem 6.3).

Choose a splitting Cartan subalgebra `H`, a base `b` of its root system, and a Chevalley system:
a Lie automorphism `ω` acting by `-1` on `H` together with root vectors `x α`, normalised by
`⁅x α, x (-α)⁆ = α∨`, with `ω (x α) = -x (-α)`. The automorphism `ω` is the Chevalley involution
of the Serre presentation of `L`, transported along Serre's theorem
(`TauCeti.exists_lieEquiv_forall_mem_apply_eq_neg`); over an algebraically closed field the root
vectors can then be rescaled into a Chevalley system for it
(`TauCeti.exists_isChevalleySystem_of_isAlgClosed`).

The root vectors and the simple coroots form a basis of `L` whose structure constants are integers.
The conjugation `σ` of the coordinates in this basis (`TauCeti.basisConj`) therefore preserves
brackets, and it commutes with `ω`, which preserves the integral span of the basis. Their
composite `τ = σ ∘ ω` (`TauCeti.IsChevalleySystem.compactConjugation`) is a conjugation with
`τ (x α) = -x (-α)` and `τ α∨ = -α∨`.

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

* `TauCeti.basisConj`: the conjugation of a complex vector space fixing a basis.
* `TauCeti.IsChevalleySystem.compactConjugation`: the compact conjugation of a Chevalley system.

## Main results

* `TauCeti.isLieConjugation_basisConj`: the conjugation fixing a basis with real structure
  constants is a conjugation of Lie algebras.
* `TauCeti.exists_lieEquiv_forall_mem_apply_eq_neg`: a Lie automorphism acting by `-1` on a
  splitting Cartan subalgebra.
* `TauCeti.exists_isChevalleySystem_of_isAlgClosed`: over an algebraically closed field, every
  such automorphism carries a Chevalley system.
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

@[expose] public section

open LieAlgebra LieModule LieAlgebra.IsKilling

open scoped ComplexOrder

namespace TauCeti

/-! ### The conjugation fixing a basis -/

section BasisConj

variable {L : Type*} [AddCommGroup L] [Module ℂ L] {ι : Type*} [Fintype ι]
  (c : Module.Basis ι ℂ L)

/-- The **conjugation fixing a basis** of a complex vector space: it conjugates the coordinates. -/
noncomputable def basisConj : L →ₛₗ[starRingEnd ℂ] L where
  toFun x := c.equivFun.symm fun i ↦ star (c.equivFun x i)
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext i
    simp [star_add]
  map_smul' a x := by
    rw [← LinearEquiv.map_smul]
    congr 1
    ext i
    simp

/-- `TauCeti.basisConj` conjugates the coordinates. -/
@[simp]
theorem repr_basisConj (x : L) (i : ι) : c.repr (basisConj c x) i = star (c.repr x i) := by
  rw [← c.equivFun_apply, ← c.equivFun_apply, basisConj, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply]

/-- `TauCeti.basisConj` fixes the basis. -/
@[simp]
theorem basisConj_self (i : ι) : basisConj c (c i) = c i :=
  c.ext_elem fun j ↦ by
    classical
    rw [repr_basisConj, c.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

/-- `TauCeti.basisConj` is an involution. -/
@[simp]
theorem basisConj_basisConj (x : L) : basisConj c (basisConj c x) = x :=
  c.ext_elem fun j ↦ by simp

end BasisConj

section LieBasisConj

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {ι : Type*} [Fintype ι]
  (c : Module.Basis ι ℂ L)

/-- **The conjugation fixing a basis with real structure constants preserves brackets.** -/
theorem isLieConjugation_basisConj
    (h : ∀ i j, basisConj c ⁅c i, c j⁆ = ⁅c i, c j⁆) : IsLieConjugation (basisConj c) where
  map_lie x y := by
    conv_lhs => rw [← c.sum_repr x, ← c.sum_repr y]
    conv_rhs => rw [← c.sum_repr x, ← c.sum_repr y]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, LinearMap.map_smulₛₗ, h,
      basisConj_self]
  involutive := basisConj_basisConj c

end LieBasisConj

/-! ### Chevalley systems over an algebraically closed field -/

section Chevalley

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [FiniteDimensional K L] in
variable (H) in
/-- **A Lie automorphism inverting a splitting Cartan subalgebra.** It is the Chevalley involution
`Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ` of the Serre presentation, transported along Serre's
theorem. -/
theorem exists_lieEquiv_forall_mem_apply_eq_neg : ∃ ω : L ≃ₗ⁅K⁆ L, ∀ y ∈ H, ω y = -y := by
  classical
  have := finite_of_isKilling (R := K) (L := L)
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  obtain ⟨e, f, hS, hspan⟩ := exists_isSerreSystem_of_base b
  let E := serreLiftEquiv hS hspan
  let ω : L ≃ₗ⁅K⁆ L := (E.symm.trans (serreChevalleyInvolution K b.cartanMatrix.transpose)).trans E
  have hcoroot (i : b.support) :
      ω ((coroot ((i : H.root) : Weight K H L) : H) : L) =
        -((coroot ((i : H.root) : Weight K H L) : H) : L) := by
    simp only [ω, LieEquiv.trans_apply, E, serreLiftEquiv_symm_coroot,
      serreChevalleyInvolution_serreH, map_neg]
    rw [← serreLiftEquiv_symm_coroot hS hspan i, LieEquiv.apply_symm_apply]
  refine ⟨ω, fun y hy ↦ ?_⟩
  suffices h : ∀ z : H, ω z = -(z : L) from h ⟨y, hy⟩
  intro z
  have htop : Submodule.span K ((rootSystem H).coroot '' b.support) = ⊤ :=
    b.span_coroot_support.trans RootPairing.IsRootSystem.span_coroot_eq_top
  have hmem : z ∈ Submodule.span K ((rootSystem H).coroot '' b.support) := htop ▸ trivial
  induction hmem using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    simpa [rootSystem_coroot_apply] using hcoroot ⟨i, hi⟩
  | zero => simp
  | add z w _ _ hz hw => simp [map_add, hz, hw, add_comm]
  | smul c z _ hz =>
    change ω (c • (z : L)) = -(c • (z : L))
    rw [map_smul, hz, smul_neg]

/-- **Chevalley systems over an algebraically closed field.** A Lie automorphism acting by `-1`
on a splitting Cartan subalgebra carries a Chevalley system: the scalars `c α` with
`ω (x α) = c α • x (-α)` of any normalised family have square roots of `-c α`, by which the family
rescales. -/
theorem exists_isChevalleySystem_of_isAlgClosed [IsAlgClosed K] {ω : L ≃ₗ⁅K⁆ L}
    (hω : ∀ y ∈ H, ω y = -y) : ∃ x : Weight K H L → L, IsChevalleySystem ω x := by
  obtain ⟨x, hx⟩ := exists_isSl2System K H (L := L)
  refine hx.exists_isChevalleySystem_of_forall_exists_sq ω hω fun α hα ↦ ?_
  have hσ := LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg ω hω
  obtain ⟨c, -, hc⟩ := hx.exists_map_eq_smul ω hσ hα
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (-c) two_pos
  exact ⟨t, by rw [hc, weightPerm_eq_neg ω hω, ht, neg_neg]⟩

end Chevalley

/-! ### The compact conjugation of a Chevalley system -/

namespace IsChevalleySystem

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra] [IsTriangularizable ℂ H L] {ω : L ≃ₗ⁅ℂ⁆ L}
  {x : Weight ℂ H L → L}
  (hx : IsChevalleySystem ω x) (b : (rootSystem H).Base)

/-- The conjugation fixing the root vectors and simple coroots fixes the Chevalley Lie lattice. -/
theorem basisConj_eq_self_of_mem_chevalleyLieLattice {z : L} (hz : z ∈ hx.chevalleyLieLattice) :
    basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b) z = z := by
  let w : hx.chevalleyLieLattice := ⟨z, hz⟩
  have h : z = ∑ k, (hx.rootSimpleCorootBasis b).repr w k •
      hx.toIsSl2System.rootSimpleCorootFieldBasis b k := by
    conv_lhs => rw [show z = (w : L) from rfl, ← (hx.rootSimpleCorootBasis b).sum_repr w]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [SetLike.val_smul, coe_rootSimpleCorootBasis]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_zsmul, basisConj_self]

/-- The basis of root vectors and simple coroots lies in the Chevalley Lie lattice. -/
theorem rootSimpleCorootFieldBasis_mem_chevalleyLieLattice (k : H.root ⊕ b.support) :
    hx.toIsSl2System.rootSimpleCorootFieldBasis b k ∈ hx.chevalleyLieLattice := by
  rw [← coe_rootSimpleCorootBasis]
  exact (hx.rootSimpleCorootBasis b k).2

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
theorem basisConj_apply_comm (z : L) :
    basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b) (ω z) =
      ω (basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b) z) := by
  have h : (basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b)).comp
      ω.toLieHom.toLinearMap =
      ω.toLieHom.toLinearMap.comp (basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b)) :=
    (hx.toIsSl2System.rootSimpleCorootFieldBasis b).ext fun k ↦ by
      simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom,
        basisConj_self]
      exact hx.basisConj_eq_self_of_mem_chevalleyLieLattice b
        (hx.apply_rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b k)
  exact DFunLike.congr_fun h z

/-- The **compact conjugation** of a Chevalley system: the Chevalley involution `ω`, followed by
the conjugation of the coordinates in the basis of root vectors and simple coroots of `b`. It sends
`x α` to `-x (-α)` and `α∨` to `-α∨`. -/
noncomputable def compactConjugation : L →ₛₗ[starRingEnd ℂ] L :=
  (basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b)).comp ω.toLieHom.toLinearMap

/-- The compact conjugation is `ω` followed by the conjugation of coordinates. -/
theorem compactConjugation_apply (z : L) :
    hx.compactConjugation b z = basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b) (ω z) :=
  rfl

/-- The compact conjugation sends `x α` to `-x (-α)`. -/
@[simp]
theorem compactConjugation_rootVector (α : Weight ℂ H L) :
    hx.compactConjugation b (x α) = -x (-α) := by
  rw [compactConjugation_apply, hx.map_root, map_neg,
    hx.basisConj_eq_self_of_mem_chevalleyLieLattice b (hx.rootVector_mem_chevalleyLieLattice _)]

/-- The compact conjugation sends `α∨` to `-α∨`. -/
@[simp]
theorem compactConjugation_coroot (α : Weight ℂ H L) :
    hx.compactConjugation b (coroot α) = -(coroot α : L) := by
  rw [compactConjugation_apply, hx.map_coroot, map_neg,
    hx.basisConj_eq_self_of_mem_chevalleyLieLattice b (hx.coroot_mem_chevalleyLieLattice _)]

/-- **The compact conjugation is a conjugation.** -/
theorem isLieConjugation_compactConjugation : IsLieConjugation (hx.compactConjugation b) where
  map_lie y z := by
    have hσ := isLieConjugation_basisConj (hx.toIsSl2System.rootSimpleCorootFieldBasis b)
      fun i j ↦ hx.basisConj_eq_self_of_mem_chevalleyLieLattice b <|
        hx.chevalleyLieLattice.lie_mem (hx.rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b i)
          (hx.rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b j)
    rw [compactConjugation_apply, compactConjugation_apply, compactConjugation_apply,
      LieEquiv.map_lie, hσ.map_lie]
  involutive z := by
    rw [compactConjugation_apply, compactConjugation_apply, ← hx.basisConj_apply_comm b,
      basisConj_basisConj, hx.involutive z]

/-! ### Positivity of the Hermitian Killing form -/

/-- A point of `H` on which every root vanishes is zero. -/
private theorem eq_zero_of_forall_root_apply_eq_zero {h : H}
    (hh : ∀ γ ∈ H.root, γ h = 0) : h = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ h).mp fun f ↦ ?_
  have hf : f ∈ Submodule.span ℂ
      ({α : Weight ℂ H L | α.IsNonZero}.image (Weight.toLinear ℂ H L)) := by
    rw [span_weight_isNonZero_eq_top]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨γ, hγ, rfl⟩ := hg
    exact hh γ (by simpa [LieSubalgebra.root] using hγ)
  | zero => rfl
  | add f g _ _ hf hg => simp [hf, hg]
  | smul c f _ hf => simp [hf]

include hx in
/-- `B(x α, x (-α))` is a positive real number: it is `2 / ⟨α, α⟩`. -/
theorem exists_pos_killingForm_rootVector_neg {α : Weight ℂ H L} (hα : α.IsNonZero) :
    ∃ r : ℝ, 0 < r ∧ killingForm ℂ L (x α) (x (-α)) = r := by
  obtain ⟨q, hq, hqα⟩ := exists_pos_rat_invForm_root_self hα
  rw [invForm_apply_apply] at hqα
  refine ⟨2 * (q : ℝ)⁻¹, by positivity, ?_⟩
  rw [hx.toIsSl2System.killingForm_root_neg_eq α hα]
  have h : α ((cartanEquivDual H).symm α) = (q : ℂ) := by simpa using hqα
  rw [h]
  push_cast
  ring

include hx in
/-- Root vectors at `α` and `-β` are Killing-orthogonal unless `α = β`. -/
theorem killingForm_rootVector_neg_eq_zero {α β : Weight ℂ H L} (hαβ : α ≠ β) :
    killingForm ℂ L (x α) (x (-β)) = 0 :=
  killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero ℂ L H
    (hx.toIsSl2System.mem_rootSpace α) (hx.toIsSl2System.mem_rootSpace (-β)) fun h ↦ hαβ <|
      Weight.ext fun y ↦ by
        have := congr_fun h y
        simp only [Pi.add_apply, Weight.coe_neg, Pi.neg_apply, Pi.zero_apply] at this
        exact add_neg_eq_zero.mp this

include hx in
/-- A root vector is Killing-orthogonal to `H`. -/
theorem killingForm_rootVector_cartan {α : Weight ℂ H L} (hα : α.IsNonZero) (h : H) :
    killingForm ℂ L (x α) h = 0 :=
  killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero ℂ L H (β := 0)
    (hx.toIsSl2System.mem_rootSpace α) (by rw [rootSpace_zero_eq]; exact h.2)
    fun h' ↦ hα (by rwa [add_zero] at h')

/-- On `H` the Killing form is `B(h, h') = ∑_γ γ(h) γ(h')`, the sum over the roots. -/
private theorem killingForm_cartan_eq_sum (h h' : H) :
    killingForm ℂ L h h' = ∑ γ ∈ H.root, γ h * γ h' := by
  have := LinearMap.congr_fun₂ (restrict_killingForm_eq_sum (K := ℂ) (L := L) (H := H)) h h'
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul] at this
  exact this.trans (Finset.sum_congr rfl fun _ _ ↦ rfl)

/-- The compact conjugation in the coordinates of the basis of root vectors and simple coroots. -/
theorem compactConjugation_eq_sum (v : L) :
    hx.compactConjugation b v =
      ∑ k, star ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v k) •
        ω (hx.toIsSl2System.rootSimpleCorootFieldBasis b k) := by
  conv_lhs => rw [← (hx.toIsSl2System.rootSimpleCorootFieldBasis b).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [LinearMap.map_smulₛₗ, compactConjugation_apply,
    hx.basisConj_eq_self_of_mem_chevalleyLieLattice b
      (hx.apply_rootSimpleCorootFieldBasis_mem_chevalleyLieLattice b k), starRingEnd_apply]

/-- The Hermitian Killing form of the compact conjugation, in the coordinates of the basis of root
vectors and simple coroots. -/
theorem killingHermitianForm_compactConjugation_eq_sum (v : L) :
    killingHermitianForm (hx.compactConjugation b) v v =
      ∑ k, ∑ l, (hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v k *
        star ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v l) *
          -killingForm ℂ L (hx.toIsSl2System.rootSimpleCorootFieldBasis b k)
            (ω (hx.toIsSl2System.rootSimpleCorootFieldBasis b l)) := by
  set c := hx.toIsSl2System.rootSimpleCorootFieldBasis b
  rw [killingHermitianForm, hx.compactConjugation_eq_sum b]
  nth_rw 1 [← c.sum_repr v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    ← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- The Gram part of the Hermitian Killing form on `H`: for `h = ∑ aᵢ αᵢ∨`,
`∑ aᵢ conj aⱼ B(αᵢ∨, αⱼ∨) = ∑_γ |γ(h)|²`. -/
private theorem sum_sum_killingForm_coroot (a : b.support → ℂ) :
    ∑ i, ∑ j, a i * star (a j) *
        killingForm ℂ L (coroot (i : Weight ℂ H L)) (coroot (j : Weight ℂ H L)) =
      ∑ γ ∈ H.root, (Complex.normSq (γ (∑ i, a i • coroot (i : Weight ℂ H L))) : ℂ) := by
  have hreal (γ : Weight ℂ H L) (i : b.support) :
      star (γ (coroot (i : Weight ℂ H L))) = γ (coroot (i : Weight ℂ H L)) := by
    rw [apply_coroot_eq_cast]
    exact star_intCast _
  calc _ = ∑ i, ∑ j, ∑ γ ∈ H.root, a i * γ (coroot (i : Weight ℂ H L)) *
        star (a j * γ (coroot (j : Weight ℂ H L))) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [killingForm_cartan_eq_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ ↦ ?_
          rw [star_mul', hreal]
          ring
    _ = ∑ γ ∈ H.root, ∑ i, ∑ j, a i * γ (coroot (i : Weight ℂ H L)) *
        star (a j * γ (coroot (j : Weight ℂ H L))) := by
          refine (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans ?_
          exact Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun γ _ ↦ ?_
          rw [← Complex.mul_conj, map_sum, map_sum, Finset.sum_mul_sum]
          simp only [map_smul, smul_eq_mul, starRingEnd_apply]

/-- **The Hermitian Killing form of the compact conjugation.** For `v = ∑ a_α x α + ∑ aᵢ αᵢ∨`,
`H_τ(v, v) = ∑_α |a_α|² B(x α, x (-α)) + ∑_γ |γ(h)|²` with `h = ∑ aᵢ αᵢ∨`. -/
theorem killingHermitianForm_compactConjugation_self (v : L) :
    killingHermitianForm (hx.compactConjugation b) v v =
      ∑ α : H.root, (Complex.normSq
          ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v (Sum.inl α)) : ℂ) *
            killingForm ℂ L (x α) (x (-α)) +
        ∑ γ ∈ H.root, (Complex.normSq (γ (∑ i,
          ((hx.toIsSl2System.rootSimpleCorootFieldBasis b).repr v (Sum.inr i)) •
            coroot (i : Weight ℂ H L))) : ℂ) := by
  have hcart (α : H.root) (j : b.support) :
      killingForm ℂ L (x α) (coroot (j : Weight ℂ H L)) = 0 :=
    hx.killingForm_rootVector_cartan (H.isNonZero_coe_root α) _
  have hcart' (i : b.support) (β : H.root) :
      killingForm ℂ L (coroot (i : Weight ℂ H L)) (x (-(β : Weight ℂ H L))) = 0 := by
    rw [LieModule.traceForm_comm]
    exact hx.killingForm_rootVector_cartan (Weight.IsNonZero.neg (H.isNonZero_coe_root β)) _
  rw [hx.killingHermitianForm_compactConjugation_eq_sum b, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, IsSl2System.rootSimpleCorootFieldBasis_inl,
    IsSl2System.rootSimpleCorootFieldBasis_inr, hx.map_root, hx.map_coroot, map_neg, neg_neg,
    hcart, hcart', mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  rw [sum_sum_killingForm_coroot]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Finset.sum_eq_single α (fun β _ hβ ↦ by
      rw [hx.killingForm_rootVector_neg_eq_zero fun h ↦ hβ (Subtype.ext h).symm, mul_zero])
    (by simp), ← Complex.mul_conj, starRingEnd_apply]

/-- **The compact conjugation of a Chevalley system is compact**: its Hermitian Killing form
`-B(v, τ v)` is positive definite. -/
theorem isCompactConjugation_compactConjugation :
    IsCompactConjugation (hx.compactConjugation b) where
  toIsLieConjugation := hx.isLieConjugation_compactConjugation b
  pos v hv := by
    set c := hx.toIsSl2System.rootSimpleCorootFieldBasis b
    choose r hr hrB using fun α : H.root ↦
      hx.exists_pos_killingForm_rootVector_neg (H.isNonZero_coe_root α)
    set h : H := ∑ i, c.repr v (Sum.inr i) • coroot (i : Weight ℂ H L) with hh
    have key : killingHermitianForm (hx.compactConjugation b) v v =
        ((∑ α : H.root, Complex.normSq (c.repr v (Sum.inl α)) * r α +
          ∑ γ ∈ H.root, Complex.normSq (γ h) : ℝ) : ℂ) := by
      rw [hx.killingHermitianForm_compactConjugation_self b]
      push_cast
      simp only [hrB]
      rfl
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
negative definite Killing form (`TauCeti.IsCompactConjugation.killingForm_realForm_neg`). -/
theorem exists_isCompactConjugation (L : Type*) [LieRing L] [LieAlgebra ℂ L] [IsKilling ℂ L] :
    ∃ τ : L →ₛₗ[starRingEnd ℂ] L, IsCompactConjugation τ := by
  have := finite_of_isKilling (R := ℂ) (L := L)
  obtain ⟨H, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base ℂ L
  obtain ⟨ω, hω⟩ := exists_lieEquiv_forall_mem_apply_eq_neg H
  obtain ⟨x, hx⟩ := exists_isChevalleySystem_of_isAlgClosed hω
  exact ⟨_, hx.isCompactConjugation_compactConjugation b⟩

end TauCeti
