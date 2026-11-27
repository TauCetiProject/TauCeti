/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.ConnectedSum.Basic
public import TauCeti.LowDimTopology.Heegaard.StableInvariant
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hat homology and relative gradings of connected sums with `S¹ × S²`

The connected sum `Y # (S¹ × S²)` of a pointed Heegaard diagram with the genus-one diagram of
`S¹ × S²`, taken in a region `r₀` containing a basepoint
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphere`), has the hat complex of `Y` tensored with
the two-dimensional space `W` on the two new intersection points `p` and `q`, with zero
differential. This file passes to homology and adds the relative gradings:

* `\widetilde{HF}(Y # (S¹ × S²)) ≅ \widetilde{HF}(Y) ⊗ W`
  (`TauCeti.HeegaardRegionSystem.hatHomologySumCircleTimesSphereEquiv`), so the dimension doubles
  while the number of basepoints stays the same, and the stable hat invariant doubles
  (`TauCeti.HeegaardRegionSystem.hatStableClass_sumCircleTimesSphere`), unlike adding a basepoint,
  which leaves it unchanged.
* The new periodic domain `B₁ - B₂` has Maslov index zero, so the periodic Maslov indices do not
  change (`TauCeti.HeegaardRegionSystem.periodicMaslovIndices_sumCircleTimesSphere`), and the
  generators `(x, i)` and `(y, j)` have relative grading `gr(x, y) + j - i`
  (`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_sumCircleTimesSphere`): the
  factor `W` is graded like `H_*(S¹)`, with `p` one above `q`.

Iterating the move in the old region `r₀` gives the `k`-fold connected sum
`Y # (S¹ × S²) # ⋯ # (S¹ × S²)` (`TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphere`). Its
generators are the pairs of a generator `x` of the original diagram and a choice `ε : Fin k → Fin 2`
of a new point on each new `α`-curve
(`TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphereGeneratorEquiv`). Its hat homology has
dimension `2 ^ k` times that of the original diagram, and the generators `(x, ε)` and `(y, δ)` have
relative grading `gr(x, y) + ∑ᵢ (δ i - ε i)`. Starting from the genus-one diagram of `S³`, the lens
space diagram with `p = 1`, this is the diagram of `#ᵏ (S¹ × S²)`: its hat complex has zero
differential and `2 ^ k` generators `ε`, the generator `0` is the top one, and `ε` lies as many
degrees below it as there are `i` with `ε i = 1`
(`TauCeti.HeegaardRegionSystem.relativeGrading_iterateSumCircleTimesSphere_lensSpace`). These are
the degrees of the exterior algebra `Λ^* H¹(#ᵏ (S¹ × S²))` on `k` generators of degree one, which
`HF̂(#ᵏ (S¹ × S²))` is as a relatively graded group.

## Main definitions

* `TauCeti.HeegaardRegionSystem.hatHomologySumCircleTimesSphereEquiv`: the identification of the
  hat homology of the connected sum with `\widetilde{HF}(Y) ⊗ W`.
* `TauCeti.HeegaardRegionSystem.SumFinTwo`: the type `X ⊕ Fin 2 ⊕ ⋯ ⊕ Fin 2`, the intersection
  points and the regions of an iterated connected sum.
* `TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphere`: the `k`-fold connected sum with
  `S¹ × S²`, with its region Euler characteristics
  `TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphereEuler` and its generators
  `TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphereGenerator`.

## Main results

* `TauCeti.HeegaardRegionSystem.finrank_hatHomology_sumCircleTimesSphere` and
  `TauCeti.HeegaardRegionSystem.hatStableClass_sumCircleTimesSphere`: the hat homology and the
  stable hat invariant double.
* `TauCeti.HeegaardRegionSystem.periodicMaslovIndices_sumCircleTimesSphere`,
  `maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_sumCircleTimesSphere`
  and `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_sumCircleTimesSphere`: the
  relative grading of the connected sum.
* `TauCeti.HeegaardRegionSystem.finrank_hatHomology_iterateSumCircleTimesSphere`,
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeGrading_iterateSumCircleTimesSphere`
  and `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_iterateSumCircleTimesSphere`:
  the hat homology and the relative grading of the `k`-fold connected sum.
* `TauCeti.HeegaardRegionSystem.finrank_hatHomology_iterateSumCircleTimesSphere_lensSpace` and
  `TauCeti.HeegaardRegionSystem.relativeGrading_iterateSumCircleTimesSphere_lensSpace`: the hat
  homology of `#ᵏ (S¹ × S²)` has dimension `2 ^ k`, with the gradings of an exterior algebra.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §6 (the connected sum formula
  `HF̂(Y₁ # Y₂) ≅ HF̂(Y₁) ⊗ HF̂(Y₂)`) and §3.1 (`HF̂(#ᵏ (S¹ × S²))` as an exterior algebra).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Module
open scoped TensorProduct

/-- A domain `D` from `x` to `y` extends to a domain of the connected sum from `(x, i)` to
`(y, j)`: put the multiplicity `D(r₀) + j - i` on the bigon `B₁` and `D(r₀)` on the bigon
`B₂`. -/
theorem IsDomainBetween.sumCircleTimesSphere {H : HeegaardRegionSystem n Point Region Basepoint}
    {r₀ : Region} {x y : H.Generator} {D : Region → ℤ}
    (hD : H.IsDomainBetween x y D) (i j : Fin 2) :
    (H.sumCircleTimesSphere r₀).IsDomainBetween (H.addBasepointGenerator r₀ x i)
      (H.addBasepointGenerator r₀ y j) (Sum.elim D ![D r₀ + (j - i), D r₀]) :=
  (H.isDomainBetween_sumCircleTimesSphere_iff r₀).mpr ⟨by simpa using hD, by simp; ring⟩

section RelativeGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) (χ : Region → ℤ)

/-- A periodic domain of the connected sum has, at every generator `(x, i)`, the Maslov index of
its restriction to the old regions at `x`: the multiplicities of the two bigons add up to twice
that of `r₀`, which cancels them in the index formula. In particular `B₁ - B₂` has Maslov index
zero. -/
theorem maslovIndex_sumCircleTimesSphere_of_mem_periodicDomains (x : H.Generator) (i : Fin 2)
    {P : Region ⊕ Fin 2 → ℤ} (hP : P ∈ (H.sumCircleTimesSphere r₀).periodicDomains) :
    (H.sumCircleTimesSphere r₀).maslovIndex (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ x i) P =
      H.maslovIndex χ x x (P ∘ Sum.inl) := by
  have hs : (P (Sum.inr 0) : ℚ) + P (Sum.inr 1) = 2 * P (Sum.inl r₀) := by
    exact_mod_cast ((H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mp hP).2
  rw [maslovIndex_sumCircleTimesSphere]
  linarith

/-- The connected sum with `S¹ × S²` does not change the periodic Maslov indices at a
generator. -/
@[simp]
theorem periodicMaslovIndices_sumCircleTimesSphere (x : H.Generator) (i : Fin 2) :
    (H.sumCircleTimesSphere r₀).periodicMaslovIndices (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) = H.periodicMaslovIndices χ x := by
  ext q
  simp only [mem_periodicMaslovIndices_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P ∘ Sum.inl, ((H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mp hP).1,
      (H.maslovIndex_sumCircleTimesSphere_of_mem_periodicDomains r₀ χ x i hP).symm⟩
  · rintro ⟨Q, hQ, rfl⟩
    -- Extend `Q` by its multiplicity on `r₀` over both bigons.
    have hP : Sum.elim Q (fun _ => Q r₀) ∈ (H.sumCircleTimesSphere r₀).periodicDomains :=
      (H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mpr
        ⟨by simpa using hQ, by simp [two_mul]⟩
    exact ⟨_, hP, by
      rw [H.maslovIndex_sumCircleTimesSphere_of_mem_periodicDomains r₀ χ x i hP, Sum.elim_comp_inl]⟩

/-- **The grading normalization survives the connected sum with `S¹ × S²`.** Suppose every domain
`E` from a generator of the original diagram to itself has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` among the
periodic Maslov indices, the normalization under which its relative grading is well defined. Then
so does every such domain of the connected sum. -/
theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_sumCircleTimesSphere
    [Fintype Basepoint]
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    ∀ (x : (H.sumCircleTimesSphere r₀).Generator) (E : Region ⊕ Fin 2 → ℤ),
      (H.sumCircleTimesSphere r₀).IsDomainBetween x x E →
        (H.sumCircleTimesSphere r₀).maslovIndex (sumCircleTimesSphereEuler χ r₀) x x E -
            2 * ∑ z, (E ((H.sumCircleTimesSphere r₀).basepoint z) : ℚ) ∈
          (H.sumCircleTimesSphere r₀).periodicMaslovIndices (sumCircleTimesSphereEuler χ r₀) x := by
  intro x' E hE
  obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective x'
  rw [addBasepointGeneratorEquiv_apply] at hE ⊢
  obtain ⟨hE, hs⟩ := (H.isDomainBetween_sumCircleTimesSphere_iff r₀).mp hE
  have hs' : (E (Sum.inr 0) : ℚ) + E (Sum.inr 1) - 2 * E (Sum.inl r₀) = 0 := by
    exact_mod_cast hs.trans (sub_self _)
  rw [periodicMaslovIndices_sumCircleTimesSphere, maslovIndex_sumCircleTimesSphere]
  -- The bigons and `r₀` cancel in the Maslov index, and the basepoints are the old ones.
  convert hself x _ hE using 1
  simp only [Function.comp_apply]
  linarith

variable {H r₀} [Fintype Basepoint] {χ}
variable (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
  H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)

include hself

/-- **The relative grading of the connected sum with `S¹ × S²`**, modulo the periodic Maslov
indices: when the original diagram satisfies the relative-grading normalization `hself` and a
domain joins `x` to `y`, the generators `(x, i)` and `(y, j)` of the connected sum have relative
grading `gr(x, y) + j - i`. -/
theorem IsDomainBetween.coe_relativeGrading_sumCircleTimesSphere {x y : H.Generator}
    {D : Region → ℤ} (hD : H.IsDomainBetween x y D) (i j : Fin 2) :
    ((H.sumCircleTimesSphere r₀).relativeGrading (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y j) :
          ℚ ⧸ H.periodicMaslovIndices χ x) =
      ((H.relativeGrading χ x y + (j - i : ℚ) : ℚ) : ℚ ⧸ H.periodicMaslovIndices χ x) := by
  have h' := (hD.sumCircleTimesSphere (r₀ := r₀) i j).coe_relativeGrading_eq
    (H.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_sumCircleTimesSphere r₀ χ hself)
  rw [periodicMaslovIndices_sumCircleTimesSphere] at h'
  rw [h', QuotientAddGroup.mk_add, hD.coe_relativeGrading_eq hself, ← QuotientAddGroup.mk_add]
  congr 1
  rw [maslovIndex_sumCircleTimesSphere]
  simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Sum.elim_comp_inl, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- **The relative grading of the connected sum with `S¹ × S²`**: when the original diagram
satisfies the relative-grading normalization `hself`, its periodic domains have Maslov index zero
at `x` and a domain joins `x` to `y`, the generators `(x, i)` and `(y, j)` of the connected sum
have relative grading `gr(x, y) + j - i`. -/
theorem IsDomainBetween.relativeGrading_sumCircleTimesSphere {x y : H.Generator} {D : Region → ℤ}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (i j : Fin 2) :
    (H.sumCircleTimesSphere r₀).relativeGrading (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y j) =
      H.relativeGrading χ x y + (j - i : ℚ) := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp
    (hD.coe_relativeGrading_sumCircleTimesSphere (r₀ := r₀) hself i j)
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- The two generators `(x, i)` and `(x, j)` of the connected sum with `S¹ × S²` have relative
grading `j - i` when the original diagram satisfies the relative-grading normalization `hself` and
its periodic domains have Maslov index zero at `x`. -/
theorem relativeGrading_sumCircleTimesSphere_self {x : H.Generator}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (i j : Fin 2) :
    (H.sumCircleTimesSphere r₀).relativeGrading (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ x j) = (j - i : ℚ) := by
  rw [(isDomainBetween_zero x).relativeGrading_sumCircleTimesSphere hself hP,
    relativeGrading_self hself hP, zero_add]

end RelativeGrading

section HatHomology

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {r₀ : Region} {χ : Region → ℤ}
  {H}

/-- The hat differential of the connected sum with `S¹ × S²` in a region containing a basepoint
squares to zero when that of the original diagram does. -/
theorem hatDifferential_sumCircleTimesSphere_comp_self_eq_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    (H.sumCircleTimesSphere r₀).hatDifferential (sumCircleTimesSphereEuler χ r₀) ∘ₗ
      (H.sumCircleTimesSphere r₀).hatDifferential (sumCircleTimesSphereEuler χ r₀) = 0 := by
  rw [H.hatDifferential_sumCircleTimesSphere_eq_hatDifferential_addBasepoint r₀ hr₀]
  exact H.hatDifferential_addBasepoint_comp_self_eq_zero hr₀ hd

/-- **The hat homology of `Y # (S¹ × S²)` is `\widetilde{HF}(Y) ⊗ W`**, for the connected sum
taken in a region containing a basepoint, with `W = 𝔽₂ × 𝔽₂` spanned by the two new
intersection points. -/
noncomputable def hatHomologySumCircleTimesSphereEquiv (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    (H.sumCircleTimesSphere r₀).hatHomology (sumCircleTimesSphereEuler χ r₀)
        (hatDifferential_sumCircleTimesSphere_comp_self_eq_zero hr₀ hd) ≃ₗ[ZMod 2]
      H.hatHomology χ hd ⊗[ZMod 2] (ZMod 2 × ZMod 2) :=
  -- The two hat complexes are equal, so transport the hat homology of the added basepoint.
  ((LinearEquiv.refl (ZMod 2) _).homologyEquiv
      (hatDifferential_sumCircleTimesSphere_comp_self_eq_zero hr₀ hd)
      (H.hatDifferential_addBasepoint_comp_self_eq_zero hr₀ hd)
      (by
        rw [H.hatDifferential_sumCircleTimesSphere_eq_hatDifferential_addBasepoint r₀ hr₀,
          LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id])).trans
    (H.hatHomologyAddBasepointEquiv hr₀ hd)

/-- The inverse of `TauCeti.HeegaardRegionSystem.hatHomologySumCircleTimesSphereEquiv` sends the
class of a cycle `z` tensored with `w` to the class of the cycle
`(TauCeti.HeegaardRegionSystem.addBasepointProdEquiv r₀).symm (z ⊗ w)`, as for the added basepoint
(`TauCeti.HeegaardRegionSystem.hatHomologyAddBasepointEquiv_symm_mk_tmul`). -/
@[simp]
theorem hatHomologySumCircleTimesSphereEquiv_symm_mk_tmul (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) (z : LinearMap.ker (H.hatDifferential χ))
    (w : ZMod 2 × ZMod 2) :
    (hatHomologySumCircleTimesSphereEquiv hr₀ hd).symm (Submodule.Quotient.mk z ⊗ₜ w) =
      Submodule.Quotient.mk ⟨(H.addBasepointProdEquiv r₀).symm ((z : H.Generator →₀ ZMod 2) ⊗ₜ w),
        by
          rw [H.hatDifferential_sumCircleTimesSphere_eq_hatDifferential_addBasepoint r₀ hr₀]
          exact LinearMap.map_mem_ker_of_comp_eq (H.addBasepointProdEquiv r₀).symm.toLinearMap
            (H.hatDifferential_comp_addBasepointProdEquiv_symm hr₀).symm
            (LinearMap.tmul_mem_ker_rTensor z.property w)⟩ := by
  rw [hatHomologySumCircleTimesSphereEquiv, LinearEquiv.symm_trans_apply,
    hatHomologyAddBasepointEquiv_symm_mk_tmul, LinearEquiv.symm_apply_eq,
    LinearEquiv.homologyEquiv_mk]
  simp only [LinearEquiv.refl_apply]

/-- The hat homology doubles in dimension under the connected sum with `S¹ × S²` in a region
containing a basepoint. -/
theorem finrank_hatHomology_sumCircleTimesSphere (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    finrank (ZMod 2) ((H.sumCircleTimesSphere r₀).hatHomology (sumCircleTimesSphereEuler χ r₀)
        (hatDifferential_sumCircleTimesSphere_comp_self_eq_zero hr₀ hd)) =
      2 * finrank (ZMod 2) (H.hatHomology χ hd) :=
  (hatHomologySumCircleTimesSphereEquiv hr₀ hd).finrank_eq.trans
    ((H.hatHomologyAddBasepointEquiv hr₀ hd).finrank_eq.symm.trans
      (H.finrank_hatHomology_addBasepoint hr₀ hd))

/-- **The stable hat invariant doubles under the connected sum with `S¹ × S²`**: the hat homology
is tensored with `W` while the number of basepoints stays the same, so
`HF̂_st(Y # (S¹ × S²)) = HF̂_st(Y) ⊗ HF̂(S¹ × S²)`. -/
theorem hatStableClass_sumCircleTimesSphere [Fintype Basepoint]
    (hr₀ : r₀ ∈ Set.range H.basepoint) (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    (H.sumCircleTimesSphere r₀).hatStableClass (sumCircleTimesSphereEuler χ r₀)
        (hatDifferential_sumCircleTimesSphere_comp_self_eq_zero hr₀ hd) =
      2 * H.hatStableClass χ hd := by
  rw [hatStableClass_def, hatStableClass_def,
    stableClass_eq_mul_of_finrank_eq_mul (finrank_hatHomology_sumCircleTimesSphere hr₀ hd),
    Nat.cast_ofNat]

end HatHomology

/-! ### The `k`-fold connected sum -/

section Iterate

/-- The type `X ⊕ Fin 2 ⊕ ⋯ ⊕ Fin 2` with `k` summands `Fin 2`, nested to the left: the
intersection points and the regions of the `k`-fold connected sum with `S¹ × S²`
(`TauCeti.HeegaardRegionSystem.iterateSumCircleTimesSphere`).

Its body is exposed so that `SumFinTwo X (k + 1)` unfolds to `SumFinTwo X k ⊕ Fin 2`, as the
types of the iterated connected sums require. -/
@[expose] def SumFinTwo (X : Type u) : ℕ → Type u
  | 0 => X
  | k + 1 => SumFinTwo X k ⊕ Fin 2

instance instFintypeSumFinTwo {X : Type u} [Fintype X] : ∀ k, Fintype (SumFinTwo X k)
  | 0 => inferInstanceAs (Fintype X)
  | k + 1 => @instFintypeSum _ _ (instFintypeSumFinTwo k) _

instance instDecidableEqSumFinTwo {X : Type u} [DecidableEq X] :
    ∀ k, DecidableEq (SumFinTwo X k)
  | 0 => inferInstanceAs (DecidableEq X)
  | k + 1 => @instDecidableEqSum _ _ (instDecidableEqSumFinTwo k) _

/-- The region `r₀` of the `k`-fold connected sum: the old region `r₀`, joined to the lenses of
all the sums, in which the next sum is taken. -/
def iterateSumCircleTimesSphereRegion (r₀ : Region) : ∀ k, SumFinTwo Region k
  | 0 => r₀
  | k + 1 => Sum.inl (iterateSumCircleTimesSphereRegion r₀ k)

@[simp]
theorem iterateSumCircleTimesSphereRegion_zero (r₀ : Region) :
    iterateSumCircleTimesSphereRegion r₀ 0 = r₀ :=
  (rfl)

@[simp]
theorem iterateSumCircleTimesSphereRegion_succ (r₀ : Region) (k : ℕ) :
    iterateSumCircleTimesSphereRegion r₀ (k + 1) =
      Sum.inl (iterateSumCircleTimesSphereRegion r₀ k) :=
  (rfl)

/-- The `k`-fold connected sum `Y # (S¹ × S²) # ⋯ # (S¹ × S²)` of the diagram with the
genus-one diagram of `S¹ × S²`, each sum taken in the old region `r₀`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphere`).

Its body is exposed so that the generators of the `(k + 1)`-fold sum are visibly those of the
connected sum of the `k`-fold one, as `iterateSumCircleTimesSphereGenerator` requires. -/
@[expose] def iterateSumCircleTimesSphere (r₀ : Region) :
    ∀ k, HeegaardRegionSystem (n + k) (SumFinTwo Point k) (SumFinTwo Region k) Basepoint
  | 0 => H
  | k + 1 => (iterateSumCircleTimesSphere r₀ k).sumCircleTimesSphere
      (iterateSumCircleTimesSphereRegion r₀ k)

/-- The `0`-fold connected sum is the original diagram. -/
@[simp]
theorem iterateSumCircleTimesSphere_zero (r₀ : Region) : H.iterateSumCircleTimesSphere r₀ 0 = H :=
  (rfl)

/-- The `(k + 1)`-fold connected sum is the connected sum of the `k`-fold one with `S¹ × S²`. -/
theorem iterateSumCircleTimesSphere_succ (r₀ : Region) (k : ℕ) :
    H.iterateSumCircleTimesSphere r₀ (k + 1) =
      (H.iterateSumCircleTimesSphere r₀ k).sumCircleTimesSphere
        (iterateSumCircleTimesSphereRegion r₀ k) :=
  (rfl)

/-- When the region `r₀` contains a basepoint of the original diagram, the region `r₀` of every
iterated connected sum contains a basepoint, so that each further sum is taken in a region
containing a basepoint. -/
theorem iterateSumCircleTimesSphereRegion_mem_range_basepoint {r₀ : Region}
    (hr₀ : r₀ ∈ Set.range H.basepoint) :
    ∀ k, iterateSumCircleTimesSphereRegion r₀ k ∈
      Set.range (H.iterateSumCircleTimesSphere r₀ k).basepoint
  | 0 => hr₀
  | k + 1 => by
    obtain ⟨z, hz⟩ := iterateSumCircleTimesSphereRegion_mem_range_basepoint hr₀ k
    exact ⟨z, congrArg Sum.inl hz⟩

variable (r₀ : Region)

/-- The generator `(x, ε)` of the `k`-fold connected sum: the generator `x` of the original
diagram, together with the new point `ε i` on the `α`-curve of the `i`-th sum. -/
noncomputable def iterateSumCircleTimesSphereGenerator (x : H.Generator) :
    ∀ k, (Fin k → Fin 2) → (H.iterateSumCircleTimesSphere r₀ k).Generator
  | 0, _ => x
  | k + 1, ε => (H.iterateSumCircleTimesSphere r₀ k).addBasepointGenerator
      (iterateSumCircleTimesSphereRegion r₀ k)
      (iterateSumCircleTimesSphereGenerator x k (Fin.init ε)) (ε (Fin.last k))

/-- The generator `(x, ε)` of the `0`-fold connected sum is `x`. -/
@[simp]
theorem iterateSumCircleTimesSphereGenerator_zero (x : H.Generator) (ε : Fin 0 → Fin 2) :
    H.iterateSumCircleTimesSphereGenerator r₀ x 0 ε = x :=
  (rfl)

/-- The generator `(x, ε)` of the `(k + 1)`-fold connected sum is the generator
`((x, Fin.init ε), ε (Fin.last k))` of the connected sum of the `k`-fold one with `S¹ × S²`. -/
theorem iterateSumCircleTimesSphereGenerator_succ (x : H.Generator) (k : ℕ)
    (ε : Fin (k + 1) → Fin 2) :
    H.iterateSumCircleTimesSphereGenerator r₀ x (k + 1) ε =
      (H.iterateSumCircleTimesSphere r₀ k).addBasepointGenerator
        (iterateSumCircleTimesSphereRegion r₀ k)
        (H.iterateSumCircleTimesSphereGenerator r₀ x k (Fin.init ε)) (ε (Fin.last k)) :=
  (rfl)

/-- The generators of the `k`-fold connected sum are the pairs `(x, ε)` of a generator `x` of the
original diagram and a choice `ε : Fin k → Fin 2` of a new point on each new `α`-curve: split off
the last entry of `ε` (`Fin.snocEquiv`) and use the generators of a single connected sum
(`TauCeti.HeegaardRegionSystem.addBasepointGeneratorEquiv`). -/
noncomputable def iterateSumCircleTimesSphereGeneratorEquiv :
    ∀ k, H.Generator × (Fin k → Fin 2) ≃ (H.iterateSumCircleTimesSphere r₀ k).Generator
  | 0 => Equiv.prodUnique _ _
  | k + 1 => ((Equiv.prodCongr (Equiv.refl _)
      ((Fin.snocEquiv fun _ => Fin 2).symm.trans (Equiv.prodComm _ _))).trans
    ((Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (iterateSumCircleTimesSphereGeneratorEquiv k) (Equiv.refl _)))).trans
    ((H.iterateSumCircleTimesSphere r₀ k).addBasepointGeneratorEquiv
      (iterateSumCircleTimesSphereRegion r₀ k))

/-- The equivalence sends `(x, ε)` to the generator `(x, ε)`. -/
@[simp]
theorem iterateSumCircleTimesSphereGeneratorEquiv_apply :
    ∀ k (c : H.Generator × (Fin k → Fin 2)),
      H.iterateSumCircleTimesSphereGeneratorEquiv r₀ k c =
        H.iterateSumCircleTimesSphereGenerator r₀ c.1 k c.2
  | 0, _ => rfl
  | k + 1, (x, ε) => by
    have hε : (Fin.snocEquiv fun _ => Fin 2).symm ε = (ε (Fin.last k), Fin.init ε) := by
      rw [Equiv.symm_apply_eq, Fin.snocEquiv_apply, Fin.snoc_init_self]
    -- The last factor lands in the generators of the single connected sum, which are those of
    -- the `(k + 1)`-fold sum only up to unfolding `iterateSumCircleTimesSphere`, so the steps
    -- `Equiv.trans_apply` and `addBasepointGeneratorEquiv_apply` touching that factor are
    -- applied by unification rather than by rewriting.
    rw [iterateSumCircleTimesSphereGeneratorEquiv]
    refine (Equiv.trans_apply _ _ (x, ε)).trans ?_
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hε,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply,
      iterateSumCircleTimesSphereGeneratorEquiv_apply k, iterateSumCircleTimesSphereGenerator_succ]
    exact addBasepointGeneratorEquiv_apply _ _ _

/-- The inverse equivalence reads off the old generator `x` and the choice `ε`. -/
@[simp]
theorem iterateSumCircleTimesSphereGeneratorEquiv_symm_apply (k : ℕ) (x : H.Generator)
    (ε : Fin k → Fin 2) :
    (H.iterateSumCircleTimesSphereGeneratorEquiv r₀ k).symm
      (H.iterateSumCircleTimesSphereGenerator r₀ x k ε) = (x, ε) :=
  (H.iterateSumCircleTimesSphereGeneratorEquiv r₀ k).symm_apply_eq.mpr
    (H.iterateSumCircleTimesSphereGeneratorEquiv_apply r₀ k (x, ε)).symm

/-- Distinct pairs `(x, ε)` give distinct generators of the `k`-fold connected sum. -/
theorem iterateSumCircleTimesSphereGenerator_injective (k : ℕ) :
    Function.Injective fun c : H.Generator × (Fin k → Fin 2) =>
      H.iterateSumCircleTimesSphereGenerator r₀ c.1 k c.2 :=
  fun _ _ h => (H.iterateSumCircleTimesSphereGeneratorEquiv r₀ k).injective (by simpa using h)

variable [DecidableEq Region]

/-- The region Euler characteristics of the `k`-fold connected sum: each sum lowers that of `r₀`
by two and adds two bigons, which are discs. -/
def iterateSumCircleTimesSphereEuler (χ : Region → ℤ) (r₀ : Region) :
    ∀ k, SumFinTwo Region k → ℤ
  | 0 => χ
  | k + 1 => sumCircleTimesSphereEuler (iterateSumCircleTimesSphereEuler χ r₀ k)
      (iterateSumCircleTimesSphereRegion r₀ k)

/-- The region Euler characteristics of the `0`-fold connected sum are the original ones. -/
@[simp]
theorem iterateSumCircleTimesSphereEuler_zero (χ : Region → ℤ) (r₀ : Region) :
    iterateSumCircleTimesSphereEuler χ r₀ 0 = χ :=
  (rfl)

/-- The region Euler characteristics of the `(k + 1)`-fold connected sum are those of the
connected sum of the `k`-fold one with `S¹ × S²`. -/
theorem iterateSumCircleTimesSphereEuler_succ (χ : Region → ℤ) (r₀ : Region) (k : ℕ) :
    iterateSumCircleTimesSphereEuler χ r₀ (k + 1) =
      sumCircleTimesSphereEuler (iterateSumCircleTimesSphereEuler χ r₀ k)
        (iterateSumCircleTimesSphereRegion r₀ k) :=
  (rfl)

variable {H r₀} [Fintype Point] [Fintype Region]

/-- The hat differential of the `k`-fold connected sum with `S¹ × S²` in a region containing a
basepoint squares to zero when that of the original diagram does. -/
theorem hatDifferential_iterateSumCircleTimesSphere_comp_self_eq_zero {χ : Region → ℤ}
    (hr₀ : r₀ ∈ Set.range H.basepoint) (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    ∀ k, (H.iterateSumCircleTimesSphere r₀ k).hatDifferential
        (iterateSumCircleTimesSphereEuler χ r₀ k) ∘ₗ
      (H.iterateSumCircleTimesSphere r₀ k).hatDifferential
        (iterateSumCircleTimesSphereEuler χ r₀ k) = 0
  | 0 => hd
  | k + 1 => hatDifferential_sumCircleTimesSphere_comp_self_eq_zero
      (H.iterateSumCircleTimesSphereRegion_mem_range_basepoint hr₀ k)
      (hatDifferential_iterateSumCircleTimesSphere_comp_self_eq_zero hr₀ hd k)

/-- **The hat homology of the `k`-fold connected sum with `S¹ × S²`** in a region containing a
basepoint has `2 ^ k` times the dimension of that of the original diagram. -/
theorem finrank_hatHomology_iterateSumCircleTimesSphere {χ : Region → ℤ}
    (hr₀ : r₀ ∈ Set.range H.basepoint) (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    ∀ k, finrank (ZMod 2) ((H.iterateSumCircleTimesSphere r₀ k).hatHomology
        (iterateSumCircleTimesSphereEuler χ r₀ k)
        (hatDifferential_iterateSumCircleTimesSphere_comp_self_eq_zero hr₀ hd k)) =
      2 ^ k * finrank (ZMod 2) (H.hatHomology χ hd)
  | 0 => (one_mul _).symm
  | k + 1 => by
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc,
      ← finrank_hatHomology_iterateSumCircleTimesSphere hr₀ hd k]
    exact finrank_hatHomology_sumCircleTimesSphere
      (H.iterateSumCircleTimesSphereRegion_mem_range_basepoint hr₀ k) _

/-- The stable hat invariant of the `k`-fold connected sum with `S¹ × S²` in a region containing a
basepoint is `2 ^ k` times that of the original diagram. -/
theorem hatStableClass_iterateSumCircleTimesSphere [Fintype Basepoint] {χ : Region → ℤ}
    (hr₀ : r₀ ∈ Set.range H.basepoint) (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0)
    (k : ℕ) :
    (H.iterateSumCircleTimesSphere r₀ k).hatStableClass (iterateSumCircleTimesSphereEuler χ r₀ k)
        (hatDifferential_iterateSumCircleTimesSphere_comp_self_eq_zero hr₀ hd k) =
      2 ^ k * H.hatStableClass χ hd := by
  rw [hatStableClass_def, hatStableClass_def,
    stableClass_eq_mul_of_finrank_eq_mul (finrank_hatHomology_iterateSumCircleTimesSphere hr₀ hd k),
    Nat.cast_pow, Nat.cast_ofNat]

variable (r₀) (χ : Region → ℤ)

/-- The `k`-fold connected sum with `S¹ × S²` does not change the periodic Maslov indices: those
at `(x, ε)` are those at `x`. -/
@[simp]
theorem periodicMaslovIndices_iterateSumCircleTimesSphere (x : H.Generator) :
    ∀ k (ε : Fin k → Fin 2),
      (H.iterateSumCircleTimesSphere r₀ k).periodicMaslovIndices
          (iterateSumCircleTimesSphereEuler χ r₀ k)
          (H.iterateSumCircleTimesSphereGenerator r₀ x k ε) =
        H.periodicMaslovIndices χ x
  | 0, _ => rfl
  | k + 1, ε => by
    rw [iterateSumCircleTimesSphereGenerator_succ,
      ← periodicMaslovIndices_iterateSumCircleTimesSphere x k (Fin.init ε)]
    exact periodicMaslovIndices_sumCircleTimesSphere _ _ _ _ _

/-- The grading normalization of the original diagram passes to its `k`-fold connected sum with
`S¹ × S²`
(`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_sumCircleTimesSphere`). -/
theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_iterateSumCircleTimesSphere
    [Fintype Basepoint]
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    ∀ k (x : (H.iterateSumCircleTimesSphere r₀ k).Generator) (E : SumFinTwo Region k → ℤ),
      (H.iterateSumCircleTimesSphere r₀ k).IsDomainBetween x x E →
        (H.iterateSumCircleTimesSphere r₀ k).maslovIndex (iterateSumCircleTimesSphereEuler χ r₀ k)
            x x E - 2 * ∑ z, (E ((H.iterateSumCircleTimesSphere r₀ k).basepoint z) : ℚ) ∈
          (H.iterateSumCircleTimesSphere r₀ k).periodicMaslovIndices
            (iterateSumCircleTimesSphereEuler χ r₀ k) x
  | 0 => hself
  | k + 1 => maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_sumCircleTimesSphere
      (H.iterateSumCircleTimesSphere r₀ k) _ _
      (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_iterateSumCircleTimesSphere hself k)

variable {r₀ χ}

omit [DecidableEq Region] [Fintype Point] [Fintype Region] in
/-- A domain from `x` to `y` gives a domain of the `k`-fold connected sum with `S¹ × S²` from
`(x, ε)` to `(y, δ)`, for all `ε` and `δ`. -/
theorem IsDomainBetween.exists_isDomainBetween_iterateSumCircleTimesSphere {x y : H.Generator}
    {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    ∀ k (ε δ : Fin k → Fin 2), ∃ E, (H.iterateSumCircleTimesSphere r₀ k).IsDomainBetween
      (H.iterateSumCircleTimesSphereGenerator r₀ x k ε)
      (H.iterateSumCircleTimesSphereGenerator r₀ y k δ) E
  | 0, _, _ => ⟨D, hD⟩
  | k + 1, ε, δ => by
    obtain ⟨E, hE⟩ := hD.exists_isDomainBetween_iterateSumCircleTimesSphere k (Fin.init ε)
      (Fin.init δ)
    exact ⟨_, hE.sumCircleTimesSphere _ _⟩

variable [Fintype Basepoint]
variable (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
  H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)

include hself

/-- **The relative grading of the `k`-fold connected sum with `S¹ × S²`**, modulo the periodic
Maslov indices: when the original diagram satisfies the relative-grading normalization `hself` and
a domain joins `x` to `y`, the generators `(x, ε)` and `(y, δ)` have relative grading
`gr(x, y) + ∑ᵢ (δ i - ε i)`. -/
theorem IsDomainBetween.coe_relativeGrading_iterateSumCircleTimesSphere {x y : H.Generator}
    {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    ∀ k (ε δ : Fin k → Fin 2),
      ((H.iterateSumCircleTimesSphere r₀ k).relativeGrading
          (iterateSumCircleTimesSphereEuler χ r₀ k)
          (H.iterateSumCircleTimesSphereGenerator r₀ x k ε)
          (H.iterateSumCircleTimesSphereGenerator r₀ y k δ) : ℚ ⧸ H.periodicMaslovIndices χ x) =
        ((H.relativeGrading χ x y + ∑ i, ((δ i : ℚ) - ε i) : ℚ) : ℚ ⧸ H.periodicMaslovIndices χ x)
  | 0, _, _ => by rw [Fin.sum_univ_zero]; exact congrArg _ (add_zero _).symm
  | k + 1, ε, δ => by
    obtain ⟨E, hE⟩ := hD.exists_isDomainBetween_iterateSumCircleTimesSphere (r₀ := r₀) k
      (Fin.init ε) (Fin.init δ)
    have h := hE.coe_relativeGrading_sumCircleTimesSphere
      (r₀ := iterateSumCircleTimesSphereRegion r₀ k)
      (H.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_iterateSumCircleTimesSphere r₀ χ
        hself k) (ε (Fin.last k)) (δ (Fin.last k))
    rw [periodicMaslovIndices_iterateSumCircleTimesSphere] at h
    refine h.trans ?_
    rw [QuotientAddGroup.mk_add, hD.coe_relativeGrading_iterateSumCircleTimesSphere k,
      ← QuotientAddGroup.mk_add, Fin.sum_univ_castSucc, add_assoc]
    simp only [Fin.init_def]

/-- **The relative grading of the `k`-fold connected sum with `S¹ × S²`**: when the original
diagram satisfies the relative-grading normalization `hself`, its periodic domains have Maslov
index zero at `x` and a domain joins `x` to `y`, the generators `(x, ε)` and `(y, δ)` have relative
grading `gr(x, y) + ∑ᵢ (δ i - ε i)`. -/
theorem IsDomainBetween.relativeGrading_iterateSumCircleTimesSphere {x y : H.Generator}
    {D : Region → ℤ} (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0)
    (hD : H.IsDomainBetween x y D) (k : ℕ) (ε δ : Fin k → Fin 2) :
    (H.iterateSumCircleTimesSphere r₀ k).relativeGrading (iterateSumCircleTimesSphereEuler χ r₀ k)
        (H.iterateSumCircleTimesSphereGenerator r₀ x k ε)
        (H.iterateSumCircleTimesSphereGenerator r₀ y k δ) =
      H.relativeGrading χ x y + ∑ i, ((δ i : ℚ) - ε i) := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp
    (hD.coe_relativeGrading_iterateSumCircleTimesSphere (r₀ := r₀) hself k ε δ)
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- The generators `(x, ε)` and `(x, δ)` of the `k`-fold connected sum with `S¹ × S²` have relative
grading `∑ᵢ (δ i - ε i)` when the original diagram satisfies the relative-grading normalization
`hself` and its periodic domains have Maslov index zero at `x`. -/
theorem relativeGrading_iterateSumCircleTimesSphere_self {x : H.Generator}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (k : ℕ) (ε δ : Fin k → Fin 2) :
    (H.iterateSumCircleTimesSphere r₀ k).relativeGrading (iterateSumCircleTimesSphereEuler χ r₀ k)
        (H.iterateSumCircleTimesSphereGenerator r₀ x k ε)
        (H.iterateSumCircleTimesSphereGenerator r₀ x k δ) = ∑ i, ((δ i : ℚ) - ε i) := by
  rw [(isDomainBetween_zero x).relativeGrading_iterateSumCircleTimesSphere hself hP,
    relativeGrading_self hself hP, zero_add]

end Iterate

/-! ### The diagrams of `#ᵏ (S¹ × S²)` -/

section LensSpace

/-- The hat homology of the `k`-fold connected sum of the genus-one diagram of `S³`, the lens space
diagram with `p = 1`, with `S¹ × S²`, a diagram of `#ᵏ (S¹ × S²)`, has dimension `2 ^ k`, as
`HF̂(#ᵏ (S¹ × S²)) ≅ Λ^* 𝔽₂ᵏ` predicts. -/
theorem finrank_hatHomology_iterateSumCircleTimesSphere_lensSpace (k : ℕ) :
    finrank (ZMod 2) (((lensSpace 1 1 0).iterateSumCircleTimesSphere 0 k).hatHomology
        (iterateSumCircleTimesSphereEuler 1 0 k)
        (hatDifferential_iterateSumCircleTimesSphere_comp_self_eq_zero (r₀ := 0)
          ⟨(), lensSpace_basepoint ()⟩
          (hatDifferential_lensSpace_comp_self_eq_zero 1 1 0) k)) = 2 ^ k := by
  rw [finrank_hatHomology_iterateSumCircleTimesSphere (r₀ := 0) ⟨(), lensSpace_basepoint ()⟩
      (hatDifferential_lensSpace_comp_self_eq_zero 1 1 0),
    finrank_hatHomology_lensSpace, mul_one]

/-- **The relative grading of `#ᵏ (S¹ × S²)`.** In the `k`-fold connected sum of the genus-one
diagram of `S³` with `S¹ × S²`, the generators `ε` and `δ`, choices of a new point on each new
`α`-curve, have relative grading `∑ᵢ (δ i - ε i)`. So `0` is the top generator, and `ε` lies as
many degrees below it as there are `i` with `ε i = 1`: these are the degrees of the exterior
algebra on `k` generators of degree one. -/
theorem relativeGrading_iterateSumCircleTimesSphere_lensSpace (k : ℕ) (ε δ : Fin k → Fin 2) :
    ((lensSpace 1 1 0).iterateSumCircleTimesSphere 0 k).relativeGrading
        (iterateSumCircleTimesSphereEuler 1 0 k)
        ((lensSpace 1 1 0).iterateSumCircleTimesSphereGenerator 0
          (lensSpaceGenerator 1 1 0 0) k ε)
        ((lensSpace 1 1 0).iterateSumCircleTimesSphereGenerator 0
          (lensSpaceGenerator 1 1 0 0) k δ) =
      ∑ i, ((δ i : ℚ) - ε i) := by
  refine relativeGrading_iterateSumCircleTimesSphere_self
    (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton () (by simp)) ?_ k ε δ
  intro P hP
  rw [periodicDomains_lensSpace, AddSubgroup.mem_bot] at hP
  rw [hP, map_zero]

end LensSpace

end HeegaardRegionSystem

end TauCeti
