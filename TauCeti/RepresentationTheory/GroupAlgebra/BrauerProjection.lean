/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.GroupTheory.PGroup.FixedPointSum
public import TauCeti.RepresentationTheory.GroupAlgebra.RelativeTrace

/-!
# The Brauer homomorphism

For a subgroup `P` of `G`, the **Brauer projection** `Br_P : R[G] → R[C_G(P)]` keeps the
coefficients of an element of `R[G]` on the centralizer `C_G(P)` and discards the others
(`TauCeti.brauerProjection`). It is `R`-linear on all of `R[G]` and is not multiplicative there:
in `S₃` with `P = ⟨(12)⟩` and `r` a `3`-cycle, `Br_P(r · r²) = 1` while `Br_P(r) = Br_P(r²) = 0`.

When `P` is a `p`-group and `R` has characteristic `p`, `Br_P` is multiplicative on the fixed
points `R[G]^P` of conjugation by `P` (`TauCeti.brauerProjection_mul`), and so restricts to an
algebra homomorphism `R[G]^P → R[C_G(P)]`, the **Brauer homomorphism** (`TauCeti.brauerHom`). The
proof counts the `P`-orbits on the elements `g` of `G`, acting by conjugation, in the coefficient
`∑_g x_g y_{g⁻¹ c}` of `x y` at `c ∈ C_G(P)`: an orbit of size `p^n` with `n ≥ 1` contributes `0`,
and the fixed points are `C_G(P)`. Both hypotheses are needed: over `ℚ`, `x = r + r²` gives
`Br_P(x²) = 2` but `Br_P(x)² = 0`; and over `𝔽₂` with `P = C₃` and `x` the sum of the
transpositions, `Br_P(x²) = 1 + r + r²` but `Br_P(x)² = 0`.

For `Q ≤ P`, `C_G(P) ≤ C_G(Q)` and `Br_P` factors through `Br_Q`
(`TauCeti.brauerProjection_eq_comapDomain`).

This is the Brauer homomorphism of the ModularCharactersAndBlocks roadmap, §6.1, from which the
defect groups of §6.2 are defined.

## Main definitions

* `TauCeti.brauerProjection P`: the coefficient projection `R[G] → R[C_G(P)]`.
* `TauCeti.brauerHom hP`: the Brauer homomorphism `R[G]^P →ₐ[R] R[C_G(P)]` for a `p`-group `P`
  in characteristic `p`.

## Main results

* `TauCeti.brauerProjection_mul`: `Br_P(x y) = Br_P(x) Br_P(y)` for `x, y ∈ R[G]^P`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243, and
  Corollary 12.5.4, p. 246.
* A. Martínez, *Modular representation theory of finite groups*, Theorem 4.1, p. 23.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G]

/-- The **Brauer projection** `Br_P : R[G] → R[C_G(P)]`, which keeps the coefficients on the
centralizer of `P` and discards the others. It is linear on all of `R[G]`, and multiplicative on
`R[G]^P` when `P` is a `p`-group in characteristic `p` (`TauCeti.brauerProjection_mul`). -/
noncomputable def brauerProjection (P : Subgroup G) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R (Subgroup.centralizer (P : Set G)) where
  toFun := comapDomain Subtype.val Subtype.val_injective
  map_add' := comapDomain_add _ _
  map_smul' c x := by
    ext
    simp

/-- The coefficient of `Br_P(x)` at `c ∈ C_G(P)` is the coefficient of `x` at `c`. -/
@[simp]
theorem coeff_brauerProjection (P : Subgroup G) (x : MonoidAlgebra R G)
    (c : Subgroup.centralizer (P : Set G)) :
    (brauerProjection P x).coeff c = x.coeff c := by
  simp [brauerProjection]

/-- `Br_P(1) = 1`, since `1 ∈ C_G(P)`. -/
@[simp]
theorem brauerProjection_one (P : Subgroup G) :
    brauerProjection P (1 : MonoidAlgebra R G) = 1 := by
  ext c
  rw [coeff_brauerProjection, one_def, one_def, coeff_single, coeff_single]
  by_cases h : c = 1
  · subst h
    rw [Finsupp.single_eq_same, OneMemClass.coe_one, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne (show (c : G) ≠ 1 from fun e => h (Subtype.ext e))]

/-- **The Brauer projection factors through smaller subgroups.** For `Q ≤ P`, `Br_P` is `Br_Q`
followed by restriction of coefficients from `C_G(Q)` to `C_G(P) ≤ C_G(Q)`. -/
theorem brauerProjection_eq_comapDomain {Q P : Subgroup G} (hQP : Q ≤ P) (x : MonoidAlgebra R G) :
    brauerProjection P x =
      comapDomain (Subgroup.inclusion (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQP)))
        (Subgroup.inclusion_injective _) (brauerProjection Q x) := by
  ext c
  simp

/-- **The Brauer map is multiplicative.** For a `p`-subgroup `P` of a finite group `G` and `R` of
characteristic `p`, the Brauer projection is multiplicative on the elements of `R[G]` fixed by
conjugation by `P` (Webb, §12.5, p. 243, and Corollary 12.5.4, p. 246). -/
theorem brauerProjection_mul [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) {x y : MonoidAlgebra R G} (hx : x ∈ conjInvariants R P)
    (hy : y ∈ conjInvariants R P) :
    brauerProjection P (x * y) = brauerProjection P x * brauerProjection P y := by
  classical
  have := Fintype.ofFinite G
  let : MulAction P G := MulAction.compHom G (MulAut.conj.comp P.subtype)
  have hsmul (g : P) (a : G) : g • a = g * a * (g : G)⁻¹ := rfl
  ext c
  have hc := Subgroup.mem_centralizer_iff.1 c.property
  rw [coeff_brauerProjection, coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp),
    coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  simp only [coeff_brauerProjection]
  rw [IsPGroup.sum_eq_sum_fixedPoints hP (fun a : G => x.coeff a * y.coeff (a⁻¹ * c)) ?_]
  · refine Finset.sum_subtype _ (fun a => ?_) (fun a : G => x.coeff a * y.coeff (a⁻¹ * c)) |>.trans
      (Fintype.sum_congr _ _ fun a => by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedPoints, hsmul,
      Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    refine ⟨fun h m hm => ?_, fun h m => ?_⟩
    · simpa [mul_inv_eq_iff_eq_mul] using h ⟨m, hm⟩
    · rw [h m m.property, mul_inv_cancel_right]
  · intro g a
    have hgc : (g : G)⁻¹ * c = c * (g : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g g.property, mul_inv_cancel_right]
    rw [hsmul, (mem_conjInvariants_iff_coeff.1 hx) g g.property a]
    congr 1
    rw [← (mem_conjInvariants_iff_coeff.1 hy) g g.property (a⁻¹ * c)]
    congr 1
    simp only [mul_inv_rev, inv_inv, mul_assoc, hgc]

/-- The **Brauer homomorphism** `R[G]^P → R[C_G(P)]` of a `p`-subgroup `P` of a finite group `G`
in characteristic `p`: the restriction of the Brauer projection to the fixed points of
conjugation by `P`, multiplicative by `TauCeti.brauerProjection_mul`. -/
noncomputable def brauerHom [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) :
    conjInvariants R P →ₐ[R] MonoidAlgebra R (Subgroup.centralizer (P : Set G)) :=
  AlgHom.ofLinearMap (brauerProjection P ∘ₗ (conjInvariants R P).val.toLinearMap)
    (by simp) fun x y => by simpa using brauerProjection_mul hP x.property y.property

/-- The Brauer homomorphism is the Brauer projection on `R[G]^P`. -/
@[simp]
theorem brauerHom_apply [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) (x : conjInvariants R P) :
    brauerHom hP x = brauerProjection P (x : MonoidAlgebra R G) := by
  rw [brauerHom, AlgHom.ofLinearMap_apply]
  rfl

end TauCeti
