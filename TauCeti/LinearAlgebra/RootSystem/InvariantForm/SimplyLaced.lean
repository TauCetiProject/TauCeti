/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Invariant forms on simply laced root systems

In a simply laced root pairing, the Cartan matrix of a base is symmetric, every root and its coroot
expand with the same integer coefficients in the simple roots and simple coroots, and the Cartan
pairing is symmetric on all roots. When the roots span, sending each simple root `αᵢ` to its coroot
functional `αᵢ^∨` defines a canonical Weyl- and automorphism-invariant symmetric bilinear form
`RootPairing.Base.simplyLacedForm` in which every root has squared length `2` and pairing with any
root `αᵣ` equals evaluation against `αᵣ^∨`; over a linearly ordered field this form is positive
definite.

In a simply laced irreducible root system all roots have the same length for every invariant form,
and two roots whose sum is again a root have Cartan integer `-1`.

## Main definitions

* `RootPairing.Base.simplyLacedForm`: the invariant symmetric bilinear form on a simply laced root
  system giving every root squared length `2`.

## Main results

* `RootPairing.InvariantForm.apply_root_root_eq_of_isSimplyLaced`: in a simply laced irreducible
  root system all roots have the same length.
* `RootPairing.Base.pairingIn_eq_neg_one_of_isSimplyLaced`: two roots whose sum is a root have
  Cartan integer `-1`.
* `RootPairing.Base.cartanMatrix_isSymm_of_isSimplyLaced`: a simply laced Cartan matrix of a base
  is symmetric.
* `RootPairing.Base.exists_root_and_coroot_eq_sum_int_of_isSimplyLaced`: in a simply laced root
  pairing, each root and its coroot share the same integer coordinates in the base.
* `RootPairing.Base.pairingIn_symm_of_isSimplyLaced` and
  `RootPairing.Base.pairing_symm_of_isSimplyLaced`: the Cartan pairing of a simply laced root
  pairing is symmetric on all roots.
* `RootPairing.Base.simplyLacedForm_apply_root`,
  `RootPairing.Base.simplyLacedForm_apply_root_left`, and
  `RootPairing.Base.simplyLacedForm_apply_root_self`: evaluation of `simplyLacedForm` on roots.
* `RootPairing.Base.simplyLacedForm_weightMap`: every root-pairing automorphism preserves
  `simplyLacedForm`.
* `RootPairing.Base.posDef_simplyLacedForm`: over a linearly ordered field, `simplyLacedForm` is
  positive definite.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 4.
-/

public section

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **In a simply laced irreducible root system all roots have the same length** for every invariant
form. Irreducibility is needed: a system of type `A₁ × A₁` has invariant forms giving its two
components different lengths. -/
theorem InvariantForm.apply_root_root_eq_of_isSimplyLaced [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  have hsimple (l m : b.support) : B.form (P.root l) (P.root l) = B.form (P.root m) (P.root m) := by
    refine b.induction_on_cartanMatrix
      (fun k : b.support ↦ B.form (P.root l) (P.root l) = B.form (P.root k) (P.root k)) rfl ?_
    intro u v (huv : B.form (P.root l) (P.root l) = _) hne
    rcases eq_or_ne u v with rfl | hne'
    · exact huv
    have hvu : b.cartanMatrix v u = -1 := (hsl hne'.symm).resolve_left hne
    have huv' : b.cartanMatrix u v = -1 :=
      (hsl hne').resolve_left (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp hne)
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have := B.pairing_mul_eq_pairing_mul_swap (u : ι) v
    rw [hp v u hvu, hp u v huv'] at this
    rw [huv]
    linear_combination -this
  have : Nonempty ι := ⟨i⟩
  obtain ⟨l⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hall (x : ι) : B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l) := by
    refine b.induction_simple_reflect x
      (p := fun x ↦ B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l))
      (fun k hk ↦ hsimple ⟨k, hk⟩ l) fun k r hk _ ↦ ?_
    rw [← hk, root_reflectionPerm, B.apply_reflection_reflection]
  rw [hall i, hall j]

namespace Base

section Symmetry

variable [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- **A simply laced Cartan matrix of a root-pairing base is symmetric**, since off-diagonal entries
lie in `{0, -1}` and `0` entries occur symmetrically. -/
theorem cartanMatrix_isSymm_of_isSimplyLaced (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) :
    b.cartanMatrix.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply]
  rcases eq_or_ne j i with rfl | hne
  · rfl
  rcases hsl hne with h0 | h1
  · exact h0.trans (b.cartanMatrix_apply_eq_zero_iff_symm.mp h0).symm
  · have hnz : b.cartanMatrix i j ≠ 0 := fun h0 ↦ by
      rw [b.cartanMatrix_apply_eq_zero_iff_symm.mpr h0] at h1
      omega
    exact h1.trans ((hsl hne.symm).resolve_left hnz).symm

variable [Finite ι] [P.IsReduced] (b : P.Base)

/-- **In a simply laced root pairing, each root and its coroot expand with the same integer
coefficients in the simple roots and simple coroots.** -/
theorem exists_root_and_coroot_eq_sum_int_of_isSimplyLaced
    (hsl : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    ∃ f : ι → ℤ, P.root i = ∑ k ∈ b.support, f k • P.root k ∧
      P.coroot i = ∑ k ∈ b.support, f k • P.coroot k := by
  classical
  have hsym := b.cartanMatrix_isSymm_of_isSimplyLaced hsl
  have hcsym {u v : ι} (hu : u ∈ b.support) (hv : v ∈ b.support) :
      P.pairingIn ℤ u v = P.pairingIn ℤ v u := by
    simpa [cartanMatrix, cartanMatrixIn_def] using congr_fun₂ hsym.eq ⟨v, hv⟩ ⟨u, hu⟩
  refine b.induction_reflect i
      (p := fun i ↦ ∃ f : ι → ℤ, P.root i = ∑ k ∈ b.support, f k • P.root k ∧
        P.coroot i = ∑ k ∈ b.support, f k • P.coroot k) ?_ ?_ ?_
  · rintro r ⟨f, hrf, hcf⟩
    refine ⟨fun k ↦ -f k, ?_, ?_⟩
    · rw [root_reflectionPerm, reflection_apply_self, hrf]
      simp [neg_smul, Finset.sum_neg_distrib]
    · rw [coroot_reflectionPerm, coreflection_apply_self, hcf]
      simp [neg_smul, Finset.sum_neg_distrib]
  · intro r hr
    refine ⟨fun k ↦ if k = r then 1 else 0, ?_, ?_⟩ <;> simp [hr]
  · rintro r j ⟨f, hrf, hcf⟩ hj
    have hflip (x y : ι) : P.flip.pairingIn ℤ x y = P.pairingIn ℤ y x :=
      FaithfulSMul.algebraMap_injective ℤ R <| by
        rw [algebraMap_pairingIn, algebraMap_pairingIn]; rfl
    have hp : P.pairingIn ℤ j r = P.pairingIn ℤ r j := by
      rw [← hflip r j, pairingIn_eq_sum_of_root_eq_sum (P := P.flip) hcf j,
        pairingIn_eq_sum_of_root_eq_sum hrf j]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hflip, hcsym hj hk]
    refine ⟨fun k ↦ f k - if k = j then P.pairingIn ℤ r j else 0, ?_, ?_⟩
    · simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', hj,
        ite_true, ← hrf, root_reflectionPerm, P.reflection_apply_root' ℤ]
    · rw [coroot_reflectionPerm]
      change P.flip.reflection j (P.flip.root r) = _
      rw [P.flip.reflection_apply_root' ℤ, hflip, hp]
      simp only [flip_root, hcf]
      simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', hj,
        ite_true]

/-- **The integer Cartan pairing of a simply laced root pairing is symmetric on all roots.** -/
theorem pairingIn_symm_of_isSimplyLaced (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
  have hflip (x y : ι) : P.flip.pairingIn ℤ x y = P.pairingIn ℤ y x :=
    FaithfulSMul.algebraMap_injective ℤ R <| by
      rw [algebraMap_pairingIn, algebraMap_pairingIn]; rfl
  have hexp (r s : ι) {u v : ι → ℤ} (hu : P.root r = ∑ k ∈ b.support, u k • P.root k)
      (hv : P.coroot s = ∑ l ∈ b.support, v l • P.coroot l) :
      P.pairingIn ℤ r s =
        ∑ k ∈ b.support, ∑ l ∈ b.support, u k * v l * P.pairingIn ℤ k l := by
    rw [pairingIn_eq_sum_of_root_eq_sum hu s]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← hflip s k, pairingIn_eq_sum_of_root_eq_sum (P := P.flip) hv k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [hflip]; ring
  obtain ⟨f, hrf, hcf⟩ := b.exists_root_and_coroot_eq_sum_int_of_isSimplyLaced hsl i
  obtain ⟨g, hrg, hcg⟩ := b.exists_root_and_coroot_eq_sum_int_of_isSimplyLaced hsl j
  have hsym := b.cartanMatrix_isSymm_of_isSimplyLaced hsl
  rw [hexp i j hrf hcg, hexp j i hrg hcf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun k hk ↦ ?_
  have hkl : P.pairingIn ℤ k l = P.pairingIn ℤ l k := by
    simpa [cartanMatrix, cartanMatrixIn_def] using congr_fun₂ hsym.eq ⟨l, hl⟩ ⟨k, hk⟩
  rw [hkl]
  ring

/-- **The Cartan pairing of a simply laced root pairing is symmetric on all roots.** -/
theorem pairing_symm_of_isSimplyLaced (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    P.pairing i j = P.pairing j i := by
  rw [← P.algebraMap_pairingIn ℤ, ← P.algebraMap_pairingIn ℤ j i,
    b.pairingIn_symm_of_isSimplyLaced hsl]

/-- **In a simply laced irreducible root system, two roots whose sum is a root have Cartan integer
`-1`.** -/
theorem pairingIn_eq_neg_one_of_isSimplyLaced [P.IsIrreducible]
    (hsl : b.cartanMatrix.IsSimplyLaced) {i k m : ι}
    (hm : P.root m = P.root i + P.root k) : P.pairingIn ℤ i k = -1 := by
  have := Fintype.ofFinite ι
  let B := P.toInvariantForm
  have hlen (x y : ι) := B.apply_root_root_eq_of_isSimplyLaced b hsl x y
  have hexp := B.form_root_add_root_self k i
  rw [add_comm (P.root k), ← hm, hlen m k, hlen i k] at hexp
  have hz : (P.pairing i k + 1) * B.form (P.root k) (P.root k) = 0 := by
    linear_combination -hexp
  have hp : P.pairing i k = -1 := by
    have := (mul_eq_zero.mp hz).resolve_right (B.ne_zero k)
    linear_combination this
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, hp, map_neg, map_one]

end Symmetry

section SimplyLacedForm

variable [CharZero R] [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] (b : P.Base)

private theorem constr_coroot'_apply_root (hsl : b.cartanMatrix.IsSimplyLaced) (r : ι) (y : M) :
    (b.toWeightBasis.constr R fun k : b.support ↦ P.coroot' k) (P.root r) y = P.coroot' r y := by
  obtain ⟨f, hrf, hcf⟩ := b.exists_root_and_coroot_eq_sum_int_of_isSimplyLaced hsl r
  have hc : P.coroot' r y = ∑ k ∈ b.support, f k • P.coroot' k y := by
    change P.toLinearMap y (P.coroot r) = ∑ k ∈ b.support, f k • P.toLinearMap y (P.coroot k)
    rw [hcf, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ map_zsmul _ _ _
  rw [hrf, hc, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hbk : P.root k = b.toWeightBasis ⟨k, hk⟩ := (b.toWeightBasis_apply ⟨k, hk⟩).symm
  rw [map_zsmul, LinearMap.smul_apply, hbk, Module.Basis.constr_basis]

/-- **The norm-two invariant form of a simply laced root system.** Sending each simple root `αᵢ` of
`b` to its coroot functional `αᵢ^∨` defines a symmetric reflection-invariant bilinear form on `M`
in which every root `αᵣ` satisfies `B(x, αᵣ) = ⟨x, αᵣ^∨⟩` and `B(αᵣ, αᵣ) = 2`. -/
noncomputable def simplyLacedForm (hsl : b.cartanMatrix.IsSimplyLaced) : P.InvariantForm :=
  let form : LinearMap.BilinForm R M := b.toWeightBasis.constr R fun k : b.support ↦ P.coroot' k
  have hleft (r : ι) (y : M) : form (P.root r) y = P.coroot' r y :=
    b.constr_coroot'_apply_root hsl r y
  have hflip : form = form.flip :=
    b.toWeightBasis.ext fun i ↦ b.toWeightBasis.ext fun j ↦ by
      change form (b.toWeightBasis i) (b.toWeightBasis j) =
        form (b.toWeightBasis j) (b.toWeightBasis i)
      simp only [Base.toWeightBasis_apply, hleft, root_coroot'_eq_pairing]
      exact b.pairing_symm_of_isSimplyLaced hsl j i
  have hsymm : LinearMap.IsSymm form := ⟨fun x y ↦ LinearMap.congr_fun₂ hflip x y⟩
  have hright (x : M) (r : ι) : form x (P.root r) = P.coroot' r x :=
    (hsymm.eq x (P.root r)).trans (hleft r x)
  { form := form
    symm := hsymm
    ne_zero r := by
      rw [hleft, root_coroot'_eq_pairing, pairing_same]
      exact two_ne_zero
    isOrthogonal_reflection r x y := by
      simp only [reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hleft, hright, root_coroot'_eq_pairing, pairing_same]
      ring }

@[simp]
theorem simplyLacedForm_apply_root_left (hsl : b.cartanMatrix.IsSimplyLaced) (r : ι) (y : M) :
    (b.simplyLacedForm hsl).form (P.root r) y = P.coroot' r y :=
  b.constr_coroot'_apply_root hsl r y

@[simp]
theorem simplyLacedForm_apply_root (hsl : b.cartanMatrix.IsSimplyLaced) (x : M) (r : ι) :
    (b.simplyLacedForm hsl).form x (P.root r) = P.coroot' r x :=
  ((b.simplyLacedForm hsl).symm.eq x (P.root r)).trans (b.simplyLacedForm_apply_root_left hsl r x)

theorem simplyLacedForm_apply_root_self (hsl : b.cartanMatrix.IsSimplyLaced) (r : ι) :
    (b.simplyLacedForm hsl).form (P.root r) (P.root r) = 2 := by
  rw [simplyLacedForm_apply_root, root_coroot'_eq_pairing, pairing_same]

/-- Every automorphism of the root pairing preserves `simplyLacedForm`, even without assuming it
stabilizes the base `b`. -/
@[simp]
theorem simplyLacedForm_weightMap (hsl : b.cartanMatrix.IsSimplyLaced) (g : P.Aut) (x y : M) :
    (b.simplyLacedForm hsl).form (g.weightMap x) (g.weightMap y) =
      (b.simplyLacedForm hsl).form x y := by
  have heq : ((b.simplyLacedForm hsl).form (g.weightMap x)).comp g.weightMap =
      (b.simplyLacedForm hsl).form x :=
    b.toWeightBasis.ext fun r ↦ by
      rw [LinearMap.comp_apply, b.toWeightBasis_apply, Hom.root_weightMap_apply P P r g.toHom,
        simplyLacedForm_apply_root, simplyLacedForm_apply_root]
      exact (P.coroot'_smul g (g.indexEquiv r) x).trans (by simp)
  exact LinearMap.congr_fun heq y

end SimplyLacedForm

end Base

end CommRing

namespace Base

section Ordered

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]

/-- **Over a linearly ordered field, `simplyLacedForm` is positive definite.** On each irreducible
component it is a positive multiple (`2 / P.RootForm (α, α) > 0`) of the positive-definite canonical
root form. -/
theorem posDef_simplyLacedForm (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) :
    (b.simplyLacedForm hsl).form.toQuadraticMap.PosDef := by
  have := Fintype.ofFinite ι
  let B₀ := P.toInvariantForm
  set B := b.simplyLacedForm hsl
  rw [← InvariantForm.ofComponent_restrictComponent B, InvariantForm.posDef_ofComponent_iff]
  intro C x hx
  have hx0 : (x : M) ≠ 0 := by simpa using hx
  obtain ⟨i, rfl⟩ : ∃ i, P.componentOf i = C := C.exists_rep
  have hscale : 0 < InvariantForm.componentScale B₀ B (P.componentOf i) := by
    rw [InvariantForm.componentScale_eq_div, b.simplyLacedForm_apply_root_self hsl]
    exact div_pos two_pos (P.rootForm_posDef _ (P.ne_zero i))
  rw [LinearMap.BilinMap.toQuadraticMap_apply, InvariantForm.restrictComponent_form_apply,
    InvariantForm.form_apply_eq_componentScale_mul B₀ B x.2 x.2]
  exact mul_pos hscale (P.rootForm_posDef _ hx0)

end Ordered

end Base

end RootPairing
