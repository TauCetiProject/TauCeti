/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Octonion.Derivation
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Chevalley generators of type `G₂` in the derivations of the split octonions

`TauCeti/Algebra/Octonion/Derivation.lean` identifies the derivation algebra of the split
octonions, as a module, with `𝔰𝔩₃ × R³ × R³`, through the special linear derivations
`TauCeti.Octonion.slDerivation` and the two vector families `TauCeti.Octonion.upperDerivation`
and `TauCeti.Octonion.lowerDerivation`. This file exhibits Chevalley generators of type `G₂` in it:
three families `H`, `E`, `F` indexed by the two simple roots that satisfy Serre's relations for
Mathlib's Cartan matrix `CartanMatrix.G₂`. The universal property of the Serre presentation then
gives a homomorphism of Lie algebras

`TauCeti.Octonion.g₂ToDerivationLieAlgebra : LieAlgebra.g₂ →ₗ⁅R⁆ Der 𝕆`

from the split Lie algebra of type `G₂` presented by generators and relations. When `2` and `3`
are invertible, the generators `E` and `F` generate `Der 𝕆`, so this homomorphism is surjective.

The trace-zero diagonal matrices act diagonally on all three families: a diagonal matrix
`diag(d₀, d₁, d₂)` acts on the upper vector derivation of the `i`-th basis vector by `dᵢ`, on the
lower one by `-dᵢ`, and on the special linear derivation of the matrix unit `Eᵢⱼ` by `dᵢ - dⱼ`. The
weights `±εᵢ` of the vector families are the six short roots of `G₂`, and the weights `εᵢ - εⱼ` of
`𝔰𝔩₃` are the six long roots. The simple roots are the short root `α₁ = ε₁` and the long root
`α₂ = ε₀ - ε₁` (indexing basis vectors from `0`), in Bourbaki's numbering, with
`⟨α₂, α₁∨⟩ = -3` and `⟨α₁, α₂∨⟩ = -1`, the off-diagonal entries of `CartanMatrix.G₂`.
Accordingly:

* `E₁` is the upper vector derivation of `e₁`, and `F₁` is minus the lower one, so that
  `⁅E₁, F₁⁆ = H₁` is the special linear derivation of `diag(-1, 2, -1)`;
* `E₂` and `F₂` are the special linear derivations of the matrix units `E₀₁` and `E₁₀`, and `H₂` is
  the special linear derivation of `diag(1, -1, 0)`.

Every relation is checked from the bracket formulas of the three families, over an arbitrary
commutative ring. For generation, brackets of these root vectors give the upper and lower vector
derivations of `e₀`, those of `e₂` up to the factor `2` coming from the cross product, and then
every matrix unit of `𝔰𝔩₃` up to the factor `-3` from the bracket of an upper with a lower vector
derivation; this is where `2` and `3` must be invertible.

Since `Der 𝕆` has rank `14`, the surjection shows that `LieAlgebra.g₂` has rank at least `14`
(`TauCeti.Octonion.fourteen_le_rank_g₂`). Its injectivity, which would identify `Der 𝕆` with
`LieAlgebra.g₂`, is not proved here.

## Main definitions

* `TauCeti.Octonion.cartanDerivation`, `TauCeti.Octonion.raisingDerivation` and
  `TauCeti.Octonion.loweringDerivation`: the Chevalley generators `Hᵢ`, `Eᵢ`, `Fᵢ` in `Der 𝕆`.
* `TauCeti.Octonion.g₂ToDerivationLieAlgebra`: the homomorphism `LieAlgebra.g₂ →ₗ⁅R⁆ Der 𝕆`
  they determine.

## Main results

* `TauCeti.Octonion.isSerreSystem`: the generators satisfy Serre's relations for
  `CartanMatrix.G₂`.
* `TauCeti.Octonion.lieSpan_range_raisingDerivation_union_range_loweringDerivation`: if `2` and
  `3` are invertible, the raising and lowering generators generate `Der 𝕆`.
* `TauCeti.Octonion.g₂ToDerivationLieAlgebra_surjective`: hence `Der 𝕆` is a quotient of
  `LieAlgebra.g₂`.
* `TauCeti.Octonion.fourteen_le_rank_g₂`: hence `LieAlgebra.g₂` has rank at least `14`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 22, where `𝔤₂` is
  built as `𝔰𝔩₃ ⊕ W ⊕ W*` and compared with the derivations of the octonions.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX, for the numbering of the
  simple roots of `G₂`.
-/

public section

namespace TauCeti

namespace Octonion

open LieAlgebra.SpecialLinear Matrix

variable {R : Type*} [CommRing R]

/-! ### The generators -/

/-- **The Cartan generators of type `G₂` in `Der 𝕆`**: the special linear derivations of
`diag(-1, 2, -1)`, the coroot of the short simple root, and of `diag(1, -1, 0)`, the coroot of the
long simple root. -/
def cartanDerivation : Fin 2 → derivationLieAlgebra R (Octonion R) :=
  ![slDerivation (singleSubSingle 1 0 1 + singleSubSingle 1 2 1),
    slDerivation (singleSubSingle 0 1 1)]

/-- **The raising generators of type `G₂` in `Der 𝕆`**: the upper vector derivation of the basis
vector `e₁`, a root vector for the short simple root, and the special linear derivation of the
matrix unit `E₀₁`, a root vector for the long simple root. -/
def raisingDerivation : Fin 2 → derivationLieAlgebra R (Octonion R) :=
  ![upperDerivation (Pi.single 1 1), slDerivation (single 0 1 (by decide) 1)]

/-- **The lowering generators of type `G₂` in `Der 𝕆`**: minus the lower vector derivation of the
basis vector `e₁`, and the special linear derivation of the matrix unit `E₁₀`. -/
def loweringDerivation : Fin 2 → derivationLieAlgebra R (Octonion R) :=
  ![-lowerDerivation (Pi.single 1 1), slDerivation (single 1 0 (by decide) 1)]

@[simp] theorem cartanDerivation_zero :
    cartanDerivation (R := R) 0 = slDerivation (singleSubSingle 1 0 1 + singleSubSingle 1 2 1) :=
  (rfl)

@[simp] theorem cartanDerivation_one :
    cartanDerivation (R := R) 1 = slDerivation (singleSubSingle 0 1 1) := (rfl)

@[simp] theorem raisingDerivation_zero :
    raisingDerivation (R := R) 0 = upperDerivation (Pi.single 1 1) := (rfl)

@[simp] theorem raisingDerivation_one :
    raisingDerivation (R := R) 1 = slDerivation (single 0 1 (by decide) 1) := (rfl)

@[simp] theorem loweringDerivation_zero :
    loweringDerivation (R := R) 0 = -lowerDerivation (Pi.single 1 1) := (rfl)

@[simp] theorem loweringDerivation_one :
    loweringDerivation (R := R) 1 = slDerivation (single 1 0 (by decide) 1) := (rfl)

/-! ### Serre's relations -/

/-- The higher Serre relation `(ad E₁)⁴ E₂ = 0`: the iterated brackets run through the upper
vector derivation of `e₀`, the lower one of `e₂` and the special linear derivation of `E₁₂`, and
`E₁₂` kills `e₁`. -/
private theorem ad_pow_raisingDerivation_zero :
    (LieAlgebra.ad R (derivationLieAlgebra R (Octonion R)) (raisingDerivation 0) ^ 3)
      ⁅raisingDerivation (R := R) 0, raisingDerivation 1⁆ = 0 := by
  simp only [raisingDerivation_zero, raisingDerivation_one, pow_succ, pow_zero,
    Module.End.one_apply, Module.End.mul_apply, LieAlgebra.ad_apply,
    ← lie_skew (upperDerivation (R := R) _) (slDerivation _), lie_slDerivation_upperDerivation,
    lie_upperDerivation_upperDerivation, lie_upperDerivation_lowerDerivation, map_neg,
    neg_eq_zero]
  convert map_zero (upperDerivation (R := R)) using 2
  ext i
  fin_cases i <;> simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The higher Serre relation `(ad E₂)² E₁ = 0`: `E₀₁` sends `e₁` to `e₀` and kills `e₀`. -/
private theorem lie_raisingDerivation_one_lie_raisingDerivation_one_raisingDerivation_zero :
    ⁅raisingDerivation (R := R) 1, ⁅raisingDerivation (R := R) 1, raisingDerivation (R := R) 0⁆⁆ =
      0 := by
  simp only [raisingDerivation_zero, raisingDerivation_one, lie_slDerivation_upperDerivation]
  convert map_zero (upperDerivation (R := R)) using 2
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The higher Serre relation `(ad F₁)⁴ F₂ = 0`, the mirror image of
`ad_pow_raisingDerivation_zero`. -/
private theorem ad_pow_loweringDerivation_zero :
    (LieAlgebra.ad R (derivationLieAlgebra R (Octonion R)) (loweringDerivation 0) ^ 3)
      ⁅loweringDerivation (R := R) 0, loweringDerivation 1⁆ = 0 := by
  simp only [loweringDerivation_zero, loweringDerivation_one, pow_succ, pow_zero,
    Module.End.one_apply, Module.End.mul_apply, LieAlgebra.ad_apply, neg_lie, neg_neg,
    ← lie_skew (lowerDerivation (R := R) _) (slDerivation _), lie_slDerivation_lowerDerivation,
    lie_lowerDerivation_lowerDerivation,
    ← lie_skew (lowerDerivation (R := R) _) (upperDerivation _),
    lie_upperDerivation_lowerDerivation, map_neg, LinearMap.neg_apply, neg_eq_zero]
  convert map_zero (lowerDerivation (R := R)) using 2
  simp only [coe_slOfVectors, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_vecMulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_three]

/-- The higher Serre relation `(ad F₂)² F₁ = 0`, the mirror image of
`lie_raisingDerivation_one_lie_raisingDerivation_one_raisingDerivation_zero`. -/
private theorem lie_loweringDerivation_one_lie_loweringDerivation_one_loweringDerivation_zero :
    ⁅loweringDerivation (R := R) 1,
      ⁅loweringDerivation (R := R) 1, loweringDerivation (R := R) 0⁆⁆ = 0 := by
  simp only [loweringDerivation_zero, loweringDerivation_one, lie_neg,
    lie_slDerivation_lowerDerivation, map_neg, neg_eq_zero]
  convert map_zero (lowerDerivation (R := R)) using 2
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **The Chevalley generators of `Der 𝕆` satisfy Serre's relations of type `G₂`**, for Mathlib's
Cartan matrix `CartanMatrix.G₂`, over every commutative ring. -/
theorem isSerreSystem :
    IsSerreSystem R CartanMatrix.G₂ (cartanDerivation (R := R)) raisingDerivation
      loweringDerivation where
  lie_H_H := by
    simp only [Fin.forall_fin_two, cartanDerivation_zero, cartanDerivation_one,
      ← LieHom.map_lie]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← map_zero (slDerivation (R := R))] <;> congr 1 <;>
      apply Subtype.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Ring.lie_def, Matrix.mul_apply, Matrix.single_apply]
  lie_E_F_self := by
    simp only [Fin.forall_fin_two, cartanDerivation_zero, cartanDerivation_one,
      raisingDerivation_zero, raisingDerivation_one, loweringDerivation_zero,
      loweringDerivation_one, ← LieHom.map_lie, lie_upperDerivation_lowerDerivation, ← map_neg]
    constructor <;> congr 1 <;> apply Subtype.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Ring.lie_def, Matrix.vecMulVec_apply]
  lie_E_F_of_ne := by
    simp only [Fin.forall_fin_two, raisingDerivation_zero, raisingDerivation_one,
      loweringDerivation_zero, loweringDerivation_one, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, zero_ne_one, one_ne_zero, not_false_eq_true, forall_const, true_and,
      and_true, lie_neg, ← lie_skew (upperDerivation _), lie_slDerivation_upperDerivation,
      lie_slDerivation_lowerDerivation, neg_eq_zero]
    constructor
    · convert map_zero (upperDerivation (R := R)) using 2
      ext i
      fin_cases i <;> simp
    · convert map_zero (lowerDerivation (R := R)) using 2
      ext i
      fin_cases i <;> simp [Matrix.transpose_single]
  lie_H_E := by
    simp only [Fin.forall_fin_two, cartanDerivation_zero, cartanDerivation_one,
      raisingDerivation_zero, raisingDerivation_one, ← LieHom.map_lie,
      lie_slDerivation_upperDerivation, ← map_zsmul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> congr 1
    · ext i
      fin_cases i <;> norm_num [CartanMatrix.G₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [CartanMatrix.G₂, Ring.lie_def, Matrix.mul_apply, Matrix.single_apply]
    · ext i
      fin_cases i <;> simp [CartanMatrix.G₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [CartanMatrix.G₂, Ring.lie_def, Matrix.mul_apply, Matrix.single_apply]
  lie_H_F := by
    simp only [Fin.forall_fin_two, cartanDerivation_zero, cartanDerivation_one,
      loweringDerivation_zero, loweringDerivation_one, ← LieHom.map_lie,
      lie_slDerivation_lowerDerivation, ← map_neg, ← map_zsmul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> congr 1
    · ext i
      fin_cases i <;> norm_num [CartanMatrix.G₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [CartanMatrix.G₂, Ring.lie_def, Matrix.mul_apply, Matrix.single_apply]
    · ext i
      fin_cases i <;> simp [CartanMatrix.G₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [CartanMatrix.G₂, Ring.lie_def, Matrix.mul_apply, Matrix.single_apply]
  ad_pow_lie_E_E := by
    -- The exponents `-CMᵢⱼ` of the higher Serre relations are `0`, `3`, `1` and `0`.
    have hCM : (-CartanMatrix.G₂ 0 0).toNat = 0 ∧ (-CartanMatrix.G₂ 0 1).toNat = 3 ∧
        (-CartanMatrix.G₂ 1 0).toNat = 1 ∧ (-CartanMatrix.G₂ 1 1).toNat = 0 := by
      decide
    simp only [Fin.forall_fin_two, hCM, pow_zero, Module.End.one_apply, lie_self,
      pow_one, LieAlgebra.ad_apply, ad_pow_raisingDerivation_zero,
      lie_raisingDerivation_one_lie_raisingDerivation_one_raisingDerivation_zero, and_self]
  ad_pow_lie_F_F := by
    -- The exponents `-CMᵢⱼ` of the higher Serre relations are `0`, `3`, `1` and `0`.
    have hCM : (-CartanMatrix.G₂ 0 0).toNat = 0 ∧ (-CartanMatrix.G₂ 0 1).toNat = 3 ∧
        (-CartanMatrix.G₂ 1 0).toNat = 1 ∧ (-CartanMatrix.G₂ 1 1).toNat = 0 := by
      decide
    simp only [Fin.forall_fin_two, hCM, pow_zero, Module.End.one_apply, lie_self,
      pow_one, LieAlgebra.ad_apply, ad_pow_loweringDerivation_zero,
      lie_loweringDerivation_one_lie_loweringDerivation_one_loweringDerivation_zero, and_self]

/-! ### The homomorphism from the Serre algebra -/

/-- **The homomorphism from the split Lie algebra of type `G₂` to `Der 𝕆`**, determined by the
Chevalley generators of `TauCeti.Octonion.isSerreSystem` through the universal property of the
Serre presentation. -/
noncomputable def g₂ToDerivationLieAlgebra :
    LieAlgebra.g₂ (R := R) →ₗ⁅R⁆ derivationLieAlgebra R (Octonion R) :=
  serreLift isSerreSystem

@[simp] theorem g₂ToDerivationLieAlgebra_serreH (i : Fin 2) :
    g₂ToDerivationLieAlgebra (serreH R CartanMatrix.G₂ i) = cartanDerivation i :=
  serreLift_serreH isSerreSystem i

@[simp] theorem g₂ToDerivationLieAlgebra_serreE (i : Fin 2) :
    g₂ToDerivationLieAlgebra (serreE R CartanMatrix.G₂ i) = raisingDerivation i :=
  serreLift_serreE isSerreSystem i

@[simp] theorem g₂ToDerivationLieAlgebra_serreF (i : Fin 2) :
    g₂ToDerivationLieAlgebra (serreF R CartanMatrix.G₂ i) = loweringDerivation i :=
  serreLift_serreF isSerreSystem i

/-! ### Generation -/

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie subalgebra of `Der 𝕆` containing the special linear derivations of the off-diagonal
matrix units contains every special linear derivation: brackets of opposite matrix units give the
diagonal elements `Eᵢᵢ - Eⱼⱼ`, and these together span `𝔰𝔩₃`. -/
private theorem slDerivation_mem {S : LieSubalgebra R (derivationLieAlgebra R (Octonion R))}
    (hsingle : ∀ i j (h : i ≠ j), slDerivation (single i j h (1 : R)) ∈ S)
    (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) : slDerivation M ∈ S := by
  have hsingle' : ∀ i j (h : i ≠ j) (c : R), slDerivation (single i j h c) ∈ S := fun i j h c => by
    simpa [← map_smul] using S.smul_mem c (hsingle i j h)
  -- The pullback of `S` to `gl₃`, as a submodule of trace-zero matrices.
  let N : Submodule R (Matrix (Fin 3) (Fin 3) R) :=
    (S.toSubmodule.comap slDerivation.toLinearMap).map (sl (Fin 3) R).incl.toLinearMap
  have hN : ∀ M : LieAlgebra.SpecialLinear.sl (Fin 3) R, slDerivation M ∈ S → M.1 ∈ N :=
    fun M hM => ⟨M, hM, rfl⟩
  obtain ⟨M', hM', hMM'⟩ : M.1 ∈ N := by
    refine mem_of_trace_eq_zero_of_single_mem (fun {p q} hpq c => ?_) (fun p q c => ?_)
      (LinearMap.mem_ker.mp M.2)
    · simpa using hN _ (hsingle' p q hpq c)
    · rcases eq_or_ne p q with rfl | hpq
      · simp
      · refine (val_singleSubSingle p q c).symm ▸ hN _ ?_
        rw [← lie_single_single_eq_singleSubSingle hpq, LieHom.map_lie]
        exact S.lie_mem (hsingle' _ _ _ _) (hsingle _ _ _)
  rwa [← Subtype.ext hMM']

/-- When `3` is invertible, a Lie subalgebra of `Der 𝕆` containing the upper and lower vector
derivations of the three basis vectors is everything: the bracket of the upper vector derivation
of `eᵢ` with the lower one of `eⱼ`, for `i ≠ j`, is `-3` times the special linear derivation of the
matrix unit `Eᵢⱼ`, and every derivation is a sum of the three families
(`TauCeti.Octonion.derivationOfTriple_surjective`). -/
private theorem eq_top_of_upperDerivation_mem_of_lowerDerivation_mem [Invertible (3 : R)]
    {S : LieSubalgebra R (derivationLieAlgebra R (Octonion R))}
    (hu : ∀ i, upperDerivation (Pi.single i (1 : R)) ∈ S)
    (hl : ∀ i, lowerDerivation (Pi.single i (1 : R)) ∈ S) : S = ⊤ := by
  have hsingle : ∀ i j (h : i ≠ j), slDerivation (single i j h (1 : R)) ∈ S := by
    intro i j h
    have hm := S.smul_mem (-⅟(3 : R)) (S.lie_mem (hu i) (hl j))
    rw [lie_upperDerivation_lowerDerivation, ← map_smul] at hm
    convert hm using 2
    apply Subtype.ext
    ext a b
    have h3 : ⅟(3 : R) * 3 = 1 := invOf_mul_self 3
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [Matrix.single_apply, Matrix.vecMulVec_apply, h, ha, hb] <;> grind
  have hsingle_smul : ∀ (i : Fin 3) (r : R), Pi.single i r = r • Pi.single i (1 : R) := by
    intro i r
    simp [← Pi.single_smul]
  have hup : ∀ u, upperDerivation u ∈ S := fun u => by
    rw [← Finset.univ_sum_single u, map_sum]
    refine sum_mem fun i _ => ?_
    rw [hsingle_smul, map_smul]
    exact S.smul_mem _ (hu i)
  have hlow : ∀ t, lowerDerivation t ∈ S := fun t => by
    rw [← Finset.univ_sum_single t, map_sum]
    refine sum_mem fun i _ => ?_
    rw [hsingle_smul, map_smul]
    exact S.smul_mem _ (hl i)
  refine eq_top_iff.2 fun D _ => ?_
  obtain ⟨⟨M, u, t⟩, rfl⟩ := derivationOfTriple_surjective D
  rw [derivationOfTriple_apply]
  exact add_mem (slDerivation_mem hsingle M) (add_mem (hup u) (hlow t))

/-- **The raising and lowering generators generate `Der 𝕆`** when `2` and `3` are invertible.

Brackets of the generators give the upper and lower vector derivations of `e₀`, and the bracket of
two upper (lower) vector derivations gives twice the lower (upper) vector derivation of `e₂`. The
vector derivations of all three basis vectors generate `Der 𝕆` once `3` is invertible. -/
theorem lieSpan_range_raisingDerivation_union_range_loweringDerivation [Invertible (2 : R)]
    [Invertible (3 : R)] :
    LieSubalgebra.lieSpan R (derivationLieAlgebra R (Octonion R))
      (Set.range raisingDerivation ∪ Set.range loweringDerivation) = ⊤ := by
  set S := LieSubalgebra.lieSpan R (derivationLieAlgebra R (Octonion R))
      (Set.range raisingDerivation ∪ Set.range loweringDerivation)
  have hE : ∀ i, raisingDerivation i ∈ S := fun i =>
    LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩)
  have hF : ∀ i, loweringDerivation i ∈ S := fun i =>
    LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩)
  have hu1 : upperDerivation (Pi.single 1 1) ∈ S := hE 0
  have hl1 : lowerDerivation (Pi.single 1 1) ∈ S := by
    simpa using neg_mem (hF 0)
  have hu0 : upperDerivation (Pi.single 0 1) ∈ S := by
    have h := S.lie_mem (hE 1) hu1
    rw [raisingDerivation_one, lie_slDerivation_upperDerivation] at h
    convert h using 2
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hl0 : lowerDerivation (Pi.single 0 1) ∈ S := by
    have h := neg_mem (S.lie_mem (hF 1) hl1)
    rw [loweringDerivation_one, lie_slDerivation_lowerDerivation, ← map_neg, neg_neg] at h
    convert h using 2
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hl2 : lowerDerivation (Pi.single 2 1) ∈ S := by
    have h := S.smul_mem ⅟(2 : R) (S.lie_mem hu0 hu1)
    rw [lie_upperDerivation_upperDerivation, ← map_smul] at h
    convert h using 2
    ext i
    fin_cases i <;> simp [cross_apply]
  have hu2 : upperDerivation (Pi.single 2 1) ∈ S := by
    have h := S.smul_mem ⅟(2 : R) (S.lie_mem hl0 hl1)
    rw [lie_lowerDerivation_lowerDerivation, ← map_smul] at h
    convert h using 2
    ext i
    fin_cases i <;> simp [cross_apply]
  refine eq_top_of_upperDerivation_mem_of_lowerDerivation_mem (fun i => ?_) fun i => ?_
  · fin_cases i
    exacts [hu0, hu1, hu2]
  · fin_cases i
    exacts [hl0, hl1, hl2]

/-- **`Der 𝕆` is a quotient of the split Lie algebra of type `G₂`**: when `2` and `3` are
invertible, `TauCeti.Octonion.g₂ToDerivationLieAlgebra` is surjective. -/
theorem g₂ToDerivationLieAlgebra_surjective [Invertible (2 : R)] [Invertible (3 : R)] :
    Function.Surjective (g₂ToDerivationLieAlgebra (R := R)) :=
  serreLift_surjective isSerreSystem
    lieSpan_range_raisingDerivation_union_range_loweringDerivation

/-- **The split Lie algebra of type `G₂` has rank at least `14`** over a commutative ring with the
strong rank condition in which `2` and `3` are invertible, since it surjects onto the
`14`-dimensional `Der 𝕆`. -/
theorem fourteen_le_rank_g₂ (R : Type*) [CommRing R] [StrongRankCondition R]
    [Invertible (2 : R)] [Invertible (3 : R)] :
    14 ≤ Module.rank R (LieAlgebra.g₂ (R := R)) := by
  have h := LinearMap.rank_le_of_surjective (g₂ToDerivationLieAlgebra (R := R)).toLinearMap
    g₂ToDerivationLieAlgebra_surjective
  rw [← Module.finrank_eq_rank, finrank_derivationLieAlgebra] at h
  exact_mod_cast h

end Octonion

end TauCeti
