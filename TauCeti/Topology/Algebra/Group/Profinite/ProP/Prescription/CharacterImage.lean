/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.CrossedHomLinearization
public import TauCeti.Topology.Algebra.Group.Profinite.Free.PadicUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Presentation
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Quotient.PiSpanSingleton
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# The image of a prescribed character of a one-relator pro-`p` group

For a one-relator presentation `G = ⟨X ∣ r⟩` with finite `X`, `r` in the Frattini subgroup and
nondegenerate degree-one form, a character with Labute's prescription property takes values in
`1 + p^kℤ_p` exactly when `p^k` divides every exponent sum of `r`.

## Main result

* `TauCeti.HasPrescriptionProperty.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum`:
  for finite `X`, character image containment is equivalent to divisibility of every exponent sum.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  §2, Theorem 4.
-/

public section

namespace TauCeti

open freeProP Matrix

universe u

attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]

section Presented

variable {X : Type u} {r : freeProP p X}

/-- A character of a presented pro-`p` group lands in `1 + p^kℤ_p` exactly when its values on the
generators do. -/
private theorem range_le_unitsPrincipal_iff_forall_of (χ : presentedProP p X {r} →ₜ* ℤ_[p]ˣ)
    (k : ℕ) :
    χ.toMonoidHom.range ≤ unitsPrincipal p k ↔
      ∀ x, (p : ℤ_[p]) ^ k ∣ ((χ.comp (presentedProP.mk p {r}) (of x) : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
  rw [MonoidHom.range_le_iff_of_topologicalClosure_closure_eq_top
    presentedProP.topologicalClosure_closure_range_of_eq_top χ.continuous
    (isClosed_unitsPrincipal p k)]
  simp only [Set.forall_mem_range, ContinuousMonoidHom.coe_toMonoidHom,
    MonoidHom.coe_ofClass, mem_unitsPrincipal_iff, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, presentedProP.mk_of]

/-- The exponent sum at `x` is a crossed homomorphism for the trivial character. -/
private theorem isCrossedHom_one_exponentSum (x : X) :
    IsCrossedHom (1 : freeProP p X →ₜ* ℤ_[p]ˣ) fun g ↦ (exponentSum p X g).toAdd x :=
  isCrossedHom_iff.2 fun g h ↦ by
    simp [add_comm]

private theorem continuous_exponentSum_apply (x : X) :
    Continuous fun g : freeProP p X ↦ (exponentSum p X g).toAdd x :=
  (continuous_apply x).comp (continuous_toAdd.comp (exponentSum p X).continuous)

/-- **The inductive step.** Let `χ` be a continuous character of `F` for which every continuous
crossed homomorphism vanishes at `r`, congruent to `1` modulo `p^k` on the generators. If `p^(k+1)`
divides every exponent sum of `r` and the degree-one form of `r` is nondegenerate, then `χ` is
congruent to `1` modulo `p^(k+1)` on the generators. -/
private theorem pow_succ_dvd_sub_one_of_forall_pow_succ_dvd_exponentSum [Finite X]
    (hr : r ∈ proPFrattini p (freeProP p X))
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate)
    {χ : freeProP p X →ₜ* ℤ_[p]ˣ}
    (hkill : ∀ F : freeProP p X → ℤ_[p], Continuous F → IsCrossedHom χ F → F r = 0) {k : ℕ}
    (hk : ∀ x, (p : ℤ_[p]) ^ k ∣ (χ (of x) : ℤ_[p]) - 1)
    (he : ∀ x, (p : ℤ_[p]) ^ (k + 1) ∣ (exponentSum p X r).toAdd x) (x : X) :
    (p : ℤ_[p]) ^ (k + 1) ∣ (χ (of x) : ℤ_[p]) - 1 := by
  classical
  have := Fintype.ofFinite X
  set n : pLowerCentralSeries p (freeProP p X) 1 :=
    ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩ with hn
  set B : Matrix X X (ZMod p) :=
    LinearMap.BilinForm.toMatrix (dualBasis p X) (degreeOneForm (gradedMk p (freeProP p X) 1 n))
    with hB
  have hBdet : B.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (dualBasis p X)).1 hnd
  -- `χ ≡ 1 mod p^k` on the generators, read against the trivial character.
  have hk₁ : ∀ x, (p : ℤ_[p]) ^ k ∣ (χ (of x) : ℤ_[p]) - (1 : freeProP p X →ₜ* ℤ_[p]ˣ) (of x) :=
    fun x ↦ by simpa [ContinuousMonoidHom.coe_one] using hk x
  choose s hs using hk
  -- The values on the generators of the exponent sum at `j`.
  set c : X → X → ℤ_[p] := fun j x ↦ (exponentSum p X (of x)).toAdd j
  -- The first-order expansion at `r`, comparing the exponent sum at `j` with the crossed
  -- homomorphism for `χ` taking the same values on the generators, which vanishes at `r`.
  have hsum : ∀ j, (p : ℤ_[p]) ∣ ∑ i, s i * (ZMod.cast (B i j) : ℤ_[p]) := fun j ↦ by
    have h := IsCrossedHom.pow_succ_dvd_sub_sub_sum_degreeOneForm (χ := 1) (χ' := χ) hk₁
      (isCrossedHom_one_exponentSum j) (isCrossedHom_crossedHom χ (c j))
      (continuous_exponentSum_apply j) (continuous_crossedHom χ (c j))
      (fun x ↦ (crossedHom_of χ (c j) x).symm) n
    rw [hkill _ (continuous_crossedHom χ (c j)) (isCrossedHom_crossedHom χ (c j))] at h
    have h' : (p : ℤ_[p]) ^ k * p ∣ (p : ℤ_[p]) ^ k * ∑ i, s i * (ZMod.cast (B i j) : ℤ_[p]) := by
      rw [← pow_succ]
      convert dvd_neg.2 (dvd_add h (he j)) using 1
      simp [hn, hs, hB, LinearMap.BilinForm.toMatrix_apply, Pi.single_apply, Finset.mul_sum,
        mul_assoc]
    exact (mul_dvd_mul_iff_left (pow_ne_zero k (Nat.cast_ne_zero.2
      (Fact.out : p.Prime).ne_zero))).1 h'
  -- Modulo `p`, the reduced vector `s` is in the left kernel of the matrix of the form.
  have hs0 : (fun i ↦ PadicInt.toZMod (s i)) = 0 := by
    refine eq_zero_of_vecMul_eq_zero hBdet (funext fun j ↦ ?_)
    have := (PadicInt.toZMod_eq_zero_iff_dvd _).2 (hsum j)
    simpa [vecMul, dotProduct, ZMod.ringHom_map_cast] using this
  rw [hs x, pow_succ]
  exact mul_dvd_mul_left _ ((PadicInt.toZMod_eq_zero_iff_dvd _).1 (congrFun hs0 x))

/-- **The level of the character with the prescription property is the content of the exponent
vector of the relator.** Let `G = ⟨X ∣ r⟩` be a one-relator pro-`p` group with finite `X` and
`r ∈ Φ(F)` whose
class in `gr_1(F)` has nondegenerate degree-one form, and let `χ : G → ℤ_pˣ` be a continuous
character with the prescription property. Then `χ` takes values in `1 + p^kℤ_p` exactly when `p^k`
divides the exponent sum of `r` at every generator. -/
theorem HasPrescriptionProperty.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum [Finite X]
    (hr : r ∈ proPFrattini p (freeProP p X))
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate)
    {χ : presentedProP p X {r} →ₜ* ℤ_[p]ˣ} (hχ : HasPrescriptionProperty χ) (k : ℕ) :
    χ.toMonoidHom.range ≤ unitsPrincipal p k ↔
      ∀ x, (p : ℤ_[p]) ^ k ∣ (exponentSum p X r).toAdd x := by
  classical
  have := Fintype.ofFinite X
  -- Every continuous crossed homomorphism for the pulled-back character vanishes at `r`.
  have hkill : ∀ F : freeProP p X → ℤ_[p], Continuous F →
      IsCrossedHom (χ.comp (presentedProP.mk p {r})) F → F r = 0 := fun F hFc hF ↦
    (presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero
      (Set.singleton_subset_iff.2 hr) χ).1 hχ F hFc hF r rfl
  -- The values on the generators of the exponent sum at `j`.
  set c : X → X → ℤ_[p] := fun j x ↦ (exponentSum p X (of x)).toAdd j
  rw [range_le_unitsPrincipal_iff_forall_of]
  refine ⟨fun h j ↦ ?_, fun he ↦ ?_⟩
  · -- The exponent sum at `j` and the crossed homomorphism for `χ` with the same values on the
    -- generators are congruent modulo `p^k`, and the latter vanishes at `r`.
    have := IsCrossedHom.pow_dvd_sub_of_forall_of_eq (χ := 1)
      (χ' := χ.comp (presentedProP.mk p {r})) (k := k)
      (fun x ↦ by simpa [ContinuousMonoidHom.coe_one] using h x) (isCrossedHom_one_exponentSum j)
      (isCrossedHom_crossedHom _ (c j)) (continuous_exponentSum_apply j)
      (continuous_crossedHom _ (c j)) (fun x ↦ (crossedHom_of _ (c j) x).symm) r
    rwa [hkill _ (continuous_crossedHom _ (c j)) (isCrossedHom_crossedHom _ (c j)), zero_sub,
      dvd_neg] at this
  · induction k with
    | zero => simp
    | succ k ih =>
      exact pow_succ_dvd_sub_one_of_forall_pow_succ_dvd_exponentSum hr hnd hkill
        (ih fun x ↦ (pow_dvd_pow _ k.le_succ).trans (he x)) he

end Presented

end TauCeti
