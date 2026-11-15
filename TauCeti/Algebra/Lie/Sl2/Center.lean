/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear
public import TauCeti.Algebra.Lie.Sl2.DiagonalCartan
public import TauCeti.Algebra.Lie.Sl2.Killing
import Mathlib.Algebra.CharZero.Infinite
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Injective
public import TauCeti.Algebra.Polynomial.EvenComp

/-!
# The centre of `U(sl₂)` and linkage

The worked rank-one case of the Harish-Chandra theorem. In `U(sl (Fin 2) K)`, with standard basis
`e = E₀₁`, `f = E₁₀`, `h = E₀₀ - E₁₁`, the element

`Ω = h² + 2h + 4fe`

is eight times the Casimir element of the Killing form, so it is central. In the coordinate
`t = λ(h)` on weights, for the base `{α}` selecting `e` as positive (so `ρ(h) = 1`), the
Harish-Chandra projection sends `Ω` to `t² + 2t`, which is invariant under the dot action
`t ↦ -t - 2`, and the linear Harish-Chandra projection sends it to `t² - 1`, invariant under the
Weyl group `t ↦ -t`. Consequently:

* two central characters agree exactly when their weights are equal or exchanged by the dot action
  (linkage), and the value on the weight `n` is `n (n + 2)`;
* `Ω` generates the centre: evaluation at `Ω` is an algebra isomorphism `K[X] ≃ Z(U(sl₂))`.

The surjectivity of that isomorphism is the invariant theory of one variable: the Harish-Chandra
projection of a central element is a polynomial `q(t)` with `q(-t - 2) = q(t)`, hence a polynomial
in `(t + 1)²`, hence in `t² + 2t`; and a central element is determined by its Harish-Chandra
projection (`TauCeti.hcProjection_injective`).

## Main definitions

* `TauCeti.slTwoOmega`: the element `Ω` of `U(sl₂)`, and `TauCeti.slTwoOmegaCenter` the same element
  in the centre.
* `TauCeti.slTwoCenterEquiv`: the isomorphism `K[X] ≃ₐ[K] Z(U(sl₂))` sending `X` to `Ω`.

## Main results

* `TauCeti.slTwoOmega_eq_smul_casimirElement`: `Ω = 8 • casimirElement`.
* `TauCeti.hcProjection_slTwoOmegaCenter` and `TauCeti.hcProjectionLinear_slTwoOmegaCenter`: the two
  Harish-Chandra projections of `Ω`.
* `TauCeti.vermaCentralCharacter_slTwoOmegaCenter`: `χ_λ(Ω) = t² + 2t`, and
  `TauCeti.vermaCentralCharacter_slTwoWeight_natCast`: `χ_n(Ω) = n (n + 2)`.
* `TauCeti.vermaCentralCharacter_eq_iff_slTwoCartanGenerator`: linkage for `sl₂`.
* `TauCeti.range_hcProjection_slTwoPositiveBase` and
  `TauCeti.range_hcProjectionLinear_slTwoPositiveBase`: the images `K[t² + 2t]` and `K[t²]`.

## Implementation notes

The isomorphism and the images take `K : Type`, the universe in which
`TauCeti.hcProjection_injective` is available; the other results hold in an arbitrary universe.
Only a field of characteristic zero is needed, not an algebraically closed one, because the
diagonal Cartan of `sl₂` is split over every field.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.1 and §23.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type*} [CommRing R]

variable (R) in
/-- **The element `Ω = h² + 2h + 4fe` of `U(sl₂)`**, where `e = E₀₁`, `f = E₁₀` and `h = E₀₀ - E₁₁`
are the standard basis. Over a field of characteristic zero it is `8 •` the Casimir element
(`TauCeti.slTwoOmega_eq_smul_casimirElement`) and generates the centre
(`TauCeti.slTwoCenterEquiv`). -/
noncomputable def slTwoOmega : _root_.UniversalEnvelopingAlgebra R (SpecialLinear.sl (Fin 2) R) :=
  _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) *
      _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) +
    (2 : R) • _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) +
    (4 : R) • (_root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 1) *
      _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 0))

/-- The defining equation `Ω = h² + 2h + 4fe`. -/
theorem slTwoOmega_def :
    slTwoOmega R =
      _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) *
          _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) +
        (2 : R) • _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 2) +
        (4 : R) • (_root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 1) *
          _root_.UniversalEnvelopingAlgebra.ι R (slFinTwoBasis R 0)) := (rfl)

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

local notation "U" => _root_.UniversalEnvelopingAlgebra K
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι K

omit [CharZero K] in
/-- The relation `e f = f e + h` in `U(sl₂)`. -/
private theorem ι_mul_ι_slFinTwoBasis :
    ι (slFinTwoBasis K 0) * ι (slFinTwoBasis K 1) =
      ι (slFinTwoBasis K 1) * ι (slFinTwoBasis K 0) + ι (slFinTwoBasis K 2) := by
  have := (ι : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ U _).map_lie
    (slFinTwoBasis K 0) (slFinTwoBasis K 1)
  rw [lie_slFinTwoBasis_zero_one, LieRing.of_associative_ring_bracket] at this
  rw [this]
  abel

/-- **`Ω` is eight times the Casimir element** of the Killing form. -/
theorem slTwoOmega_eq_smul_casimirElement :
    slTwoOmega K = (8 : K) • casimirElement K (SpecialLinear.sl (Fin 2) K) := by
  rw [casimirElement_eq_sum (slFinTwoBasis K), killingDualBasis_slFinTwoBasis, Fin.sum_univ_three,
    slTwoOmega]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_smul, mul_smul_comm,
    ι_mul_ι_slFinTwoBasis]
  module

/-- `Ω` is central. -/
theorem slTwoOmega_mem_center :
    slTwoOmega K ∈ Subalgebra.center K (U (SpecialLinear.sl (Fin 2) K)) := by
  rw [slTwoOmega_eq_smul_casimirElement]
  exact Subalgebra.smul_mem _ (casimirElement_mem_center K _) _

variable (K) in
/-- `Ω` as an element of the centre of `U(sl₂)`. -/
noncomputable def slTwoOmegaCenter : Subalgebra.center K (U (SpecialLinear.sl (Fin 2) K)) :=
  ⟨slTwoOmega K, slTwoOmega_mem_center⟩

/-- The element of the centre `slTwoOmegaCenter` is `Ω`. -/
@[simp]
theorem coe_slTwoOmegaCenter :
    (slTwoOmegaCenter K : U (SpecialLinear.sl (Fin 2) K)) = slTwoOmega K := (rfl)

/-- `f = E₁₀` lies in the negative nilradical of the positive base. -/
private theorem slFinTwoBasis_one_mem_negativeNilradical :
    slFinTwoBasis K 1 ∈ negativeNilradical (slTwoDiagonalCartan K) (slTwoPositiveBase K) := by
  let i : (LieSubalgebra.root : Finset (Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K))) :=
    ⟨-slTwoRoot K, by simpa [LieSubalgebra.root] using slTwoRoot_isNonZero⟩
  refine mem_negativeNilradical_of_mem_rootSpace (slTwoDiagonalCartan K) (slTwoPositiveBase K)
    (α := i) ?_ ?_
  · rw [eq_reflectionPerm_slTwoRootIndex (i := i) rfl,
      reflectionPerm_self_mem_negRoots_iff_mem_posRoots]
    exact (mem_posRoots _ _ _).mpr
      (RootPairing.Base.isPos_of_mem_support slTwoRootIndex_mem_support)
  · rw [slFinTwoBasis_one]
    exact single_one_zero_mem_rootSpace_neg_slTwoRoot 1

/-- **The Cartan projection of `Ω`** is `h² + 2h`. -/
theorem cartanProjection_slTwoOmega :
    cartanProjection (slTwoPositiveBase K) (slTwoOmega K) =
      ι (slTwoCartanGenerator K) * ι (slTwoCartanGenerator K) +
        (2 : K) • ι (slTwoCartanGenerator K) := by
  have hι : ι (slFinTwoBasis K 2) = ι ((slTwoCartanGenerator K : slTwoDiagonalCartan K) :
      SpecialLinear.sl (Fin 2) K) := by
    rw [slFinTwoBasis_two, coe_slTwoCartanGenerator]
  rw [slTwoOmega, map_add, map_add, map_smul, map_smul,
    cartanProjection_ι_mul_of_mem_negativeNilradical _ slFinTwoBasis_one_mem_negativeNilradical,
    hι, cartanProjection_ι_coe_mul, cartanProjection_ι_coe, smul_zero, add_zero]

/-- **The Harish-Chandra projection of `Ω`** is `h² + 2h`. -/
@[simp]
theorem hcProjection_slTwoOmegaCenter :
    hcProjection (slTwoPositiveBase K) (slTwoOmegaCenter K) =
      SymmetricAlgebra.ι K _ (slTwoCartanGenerator K) ^ 2 +
        (2 : K) • SymmetricAlgebra.ι K _ (slTwoCartanGenerator K) := by
  rw [hcProjection_apply, coe_slTwoOmegaCenter, cartanProjection_slTwoOmega, map_add, map_mul,
    map_smul, UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_ι, sq]

/-- **The central character of `Ω`**: in the coordinate `t = λ(h)` it is `t² + 2t`. -/
@[simp]
theorem vermaCentralCharacter_slTwoOmegaCenter
    (lam : Module.Dual K (slTwoDiagonalCartan K)) :
    vermaCentralCharacter (slTwoPositiveBase K) lam (slTwoOmegaCenter K) =
      lam (slTwoCartanGenerator K) ^ 2 + 2 * lam (slTwoCartanGenerator K) := by
  rw [← lift_hcProjection, hcProjection_slTwoOmegaCenter]
  simp

/-- The value of a linear form at `h` is its pairing with the coroot of the simple root. -/
theorem coroot'_slTwoRootIndex (lam : Module.Dual K (slTwoDiagonalCartan K)) :
    (IsKilling.rootSystem (slTwoDiagonalCartan K)).coroot' (slTwoRootIndex K) lam =
      lam (slTwoCartanGenerator K) := by
  rw [rootSystem_coroot'_apply, IsKilling.rootSystem_coroot_apply, coe_slTwoRootIndex,
    coroot_slTwoRoot]

/-- The value of the Weyl vector at `h` is `1`. -/
@[simp]
theorem weylVector_slTwoCartanGenerator :
    weylVector (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K)
      (slTwoCartanGenerator K) = 1 := by
  rw [← coroot'_slTwoRootIndex, coroot'_weylVector _ _ slTwoRootIndex_mem_support]

/-- `χ_n(Ω) = n (n + 2)`, the central character at the highest weight `n`. -/
theorem vermaCentralCharacter_slTwoWeight_natCast (n : ℕ) :
    vermaCentralCharacter (slTwoPositiveBase K) (slTwoWeight (n : K)) (slTwoOmegaCenter K) =
      n * (n + 2) := by
  rw [vermaCentralCharacter_slTwoOmegaCenter, slTwoWeight_slTwoCartanGenerator]
  ring

/-- The linear Harish-Chandra projection of `Ω` is `h² - 1`. -/
@[simp]
theorem hcProjectionLinear_slTwoOmegaCenter :
    hcProjectionLinear (slTwoPositiveBase K) (slTwoOmegaCenter K) =
      SymmetricAlgebra.ι K _ (slTwoCartanGenerator K) ^ 2 - 1 := by
  rw [hcProjectionLinear_apply, hcProjection_slTwoOmegaCenter]
  simp only [two_smul, map_add, map_pow, SymmetricAlgebra.translation_ι, LinearMap.neg_apply,
    weylVector_slTwoCartanGenerator, map_neg, map_one]
  ring

/-- The non-trivial dot action on weights of `sl₂`: `t ↦ -t - 2`. -/
theorem dotAction_ofIdx_slTwoCartanGenerator (lam : Module.Dual K (slTwoDiagonalCartan K)) :
    dotAction (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K)
      (RootPairing.weylGroup.ofIdx _ (slTwoRootIndex K)) lam (slTwoCartanGenerator K) =
        -lam (slTwoCartanGenerator K) - 2 := by
  rw [← coroot'_slTwoRootIndex, ← coroot'_slTwoRootIndex,
    coroot'_dotAction_ofIdx _ _ slTwoRootIndex_mem_support]

/-- **Linkage for `sl₂`**: two central characters agree exactly when the values at `h` are equal or
exchanged by `t ↦ -t - 2`. -/
theorem vermaCentralCharacter_eq_iff_slTwoCartanGenerator
    (lam mu : Module.Dual K (slTwoDiagonalCartan K)) :
    vermaCentralCharacter (slTwoPositiveBase K) lam =
        vermaCentralCharacter (slTwoPositiveBase K) mu ↔
      mu (slTwoCartanGenerator K) = lam (slTwoCartanGenerator K) ∨
        mu (slTwoCartanGenerator K) = -lam (slTwoCartanGenerator K) - 2 := by
  constructor
  · intro h
    have := congrArg (· (slTwoOmegaCenter K)) h
    simp only [vermaCentralCharacter_slTwoOmegaCenter] at this
    have hprod : (mu (slTwoCartanGenerator K) - lam (slTwoCartanGenerator K)) *
        (mu (slTwoCartanGenerator K) + lam (slTwoCartanGenerator K) + 2) = 0 := by
      linear_combination -this
    obtain h | h := mul_eq_zero.mp hprod
    · exact .inl (by linear_combination h)
    · exact .inr (by linear_combination h)
  · rintro (h | h)
    · rw [dual_ext_slTwoCartanGenerator h]
    · rw [← vermaCentralCharacter_dotAction (slTwoPositiveBase K)
        (RootPairing.weylGroup.ofIdx _ (slTwoRootIndex K)) lam,
        dual_ext_slTwoCartanGenerator ((dotAction_ofIdx_slTwoCartanGenerator lam).trans h.symm)]

end Field

section Center

variable {K : Type} [Field K] [CharZero K]

local notation "U" => _root_.UniversalEnvelopingAlgebra K
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι K

open Polynomial

/-- `p(Ω) = 0` forces `p = 0`, since `Ω` takes infinitely many values under central characters. -/
private theorem aeval_slTwoOmegaCenter_injective :
    Function.Injective (aeval (R := K) (slTwoOmegaCenter K)) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp ↦ ?_
  have hroot (t : K) : p.eval (t ^ 2 + 2 * t) = 0 := by
    have := congrArg (vermaCentralCharacter (slTwoPositiveBase K) (slTwoWeight t)) hp
    rw [← aeval_algHom_apply, vermaCentralCharacter_slTwoOmegaCenter,
      slTwoWeight_slTwoCartanGenerator, map_zero, coe_aeval_eq_eval] at this
    exact this
  have hmono : StrictMono (fun n : ℕ ↦ n ^ 2 + 2 * n) := fun a b h ↦ by
    simp only
    nlinarith
  refine p.eq_zero_of_infinite_isRoot (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ (n : K) ^ 2 + 2 * (n : K)) (fun m n hmn ↦ hmono.injective ?_)
    fun n ↦ hroot n)
  simp only at hmn ⊢
  exact_mod_cast hmn

omit [CharZero K] in
/-- Every element of `S(H)` is a polynomial in the generator `h`. -/
private theorem exists_aeval_eq_symmetricAlgebra
    (p : SymmetricAlgebra K (slTwoDiagonalCartan K)) :
    ∃ q : K[X], aeval (SymmetricAlgebra.ι K _ (slTwoCartanGenerator K)) q = p := by
  have htop : Algebra.adjoin K {(SymmetricAlgebra.ι K (slTwoDiagonalCartan K)
      (slTwoCartanGenerator K))} = ⊤ := by
    rw [eq_top_iff, ← SymmetricAlgebra.adjoin_range_ι, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [eq_smul_slTwoCartanGenerator x, map_smul]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin rfl) _
  have hp : p ∈ Algebra.adjoin K {(SymmetricAlgebra.ι K (slTwoDiagonalCartan K)
      (slTwoCartanGenerator K))} := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hp
  exact hp

/-- The Harish-Chandra projection of a central element is a polynomial in `t² + 2t`. -/
private theorem exists_hcProjection_eq_aeval
    (z : Subalgebra.center K (U (SpecialLinear.sl (Fin 2) K))) :
    ∃ r : K[X], hcProjection (slTwoPositiveBase K) z =
      aeval (hcProjection (slTwoPositiveBase K) (slTwoOmegaCenter K)) r := by
  obtain ⟨q, hq⟩ := exists_aeval_eq_symmetricAlgebra (hcProjection (slTwoPositiveBase K) z)
  have heval (lam : Module.Dual K (slTwoDiagonalCartan K)) :
      SymmetricAlgebra.lift lam (hcProjection (slTwoPositiveBase K) z) =
        q.eval (lam (slTwoCartanGenerator K)) := by
    rw [← hq, ← aeval_algHom_apply, SymmetricAlgebra.lift_ι_apply, coe_aeval_eq_eval]
  have hinv : q.comp (-X - 2) = q := Polynomial.funext fun t ↦ by
    have := mem_dotInvariants_iff.mp (hcProjection_mem_dotInvariants (b := slTwoPositiveBase K) z)
      (RootPairing.weylGroup.ofIdx _ (slTwoRootIndex K)) (slTwoWeight t)
    rw [heval, heval, dotAction_ofIdx_slTwoCartanGenerator,
      slTwoWeight_slTwoCartanGenerator] at this
    simpa [eval_comp] using this
  obtain ⟨r, rfl⟩ := exists_eq_comp_X_sq_add_two_mul_X_of_comp_neg_X_sub_two_eq hinv
  refine ⟨r, ?_⟩
  rw [← hq, aeval_comp, hcProjection_slTwoOmegaCenter]
  simp [two_smul, sq, two_mul]

/-- Evaluation at `Ω` is a bijection from polynomials to the centre of `U(sl₂)`. -/
theorem aeval_slTwoOmegaCenter_bijective :
    Function.Bijective (aeval (R := K) (slTwoOmegaCenter K)) :=
  ⟨aeval_slTwoOmegaCenter_injective, fun z ↦ by
    obtain ⟨r, hr⟩ := exists_hcProjection_eq_aeval z
    exact ⟨r, hcProjection_injective (slTwoPositiveBase K) <| by
      rw [← aeval_algHom_apply, hr]⟩⟩

/-- **The centre of `U(sl₂)` is the polynomial algebra on `Ω`.** -/
noncomputable def slTwoCenterEquiv :
    K[X] ≃ₐ[K] Subalgebra.center K (U (SpecialLinear.sl (Fin 2) K)) :=
  AlgEquiv.ofBijective _ aeval_slTwoOmegaCenter_bijective

/-- `slTwoCenterEquiv` is evaluation at `Ω`. -/
@[simp]
theorem slTwoCenterEquiv_apply (p : K[X]) :
    slTwoCenterEquiv p = aeval (slTwoOmegaCenter K) p := (rfl)

/-- `slTwoCenterEquiv` sends `X` to `Ω`. -/
theorem slTwoCenterEquiv_X : slTwoCenterEquiv (K := K) X = slTwoOmegaCenter K := by
  simp

/-- An algebra map out of the centre of `U(sl₂)` has image the subalgebra generated by the image
of `Ω`. -/
private theorem range_eq_adjoin_of_center {A : Type*} [CommRing A] [Algebra K A]
    (φ : Subalgebra.center K (U (SpecialLinear.sl (Fin 2) K)) →ₐ[K] A) :
    φ.range = Algebra.adjoin K {φ (slTwoOmegaCenter K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  ext x
  simp only [AlgHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨r, rfl⟩ := aeval_slTwoOmegaCenter_bijective.2 z
    exact ⟨r, aeval_algHom_apply φ _ r⟩
  · rintro ⟨r, rfl⟩
    exact ⟨aeval (slTwoOmegaCenter K) r, (aeval_algHom_apply φ _ r).symm⟩

/-- **The image of the Harish-Chandra projection** of `sl₂` is `K[t² + 2t]`. -/
theorem range_hcProjection_slTwoPositiveBase :
    (hcProjection (slTwoPositiveBase K)).range =
      Algebra.adjoin K {(SymmetricAlgebra.ι K _ (slTwoCartanGenerator K) ^ 2 +
        (2 : K) • SymmetricAlgebra.ι K _ (slTwoCartanGenerator K))} := by
  rw [range_eq_adjoin_of_center, hcProjection_slTwoOmegaCenter]

/-- **The image of the linear Harish-Chandra projection** of `sl₂` is `K[t²]`. -/
theorem range_hcProjectionLinear_slTwoPositiveBase :
    (hcProjectionLinear (slTwoPositiveBase K)).range =
      Algebra.adjoin K {(SymmetricAlgebra.ι K _ (slTwoCartanGenerator K) ^ 2)} := by
  rw [range_eq_adjoin_of_center, hcProjectionLinear_slTwoOmegaCenter]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ rfl
    exact sub_mem (Algebra.subset_adjoin rfl) (one_mem _)
  · rintro _ rfl
    have := add_mem (Algebra.subset_adjoin (Set.mem_singleton _)) (one_mem (Algebra.adjoin K
      {(SymmetricAlgebra.ι K (slTwoDiagonalCartan K) (slTwoCartanGenerator K) ^ 2 - 1)}))
    rwa [sub_add_cancel] at this

end Center

end TauCeti
