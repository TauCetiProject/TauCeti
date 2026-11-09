/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Diamond
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.AtkinLehner

/-!
# The Hecke operators on modular symbols commute

Any two Hecke operators of level `Γ₁(N)` on `𝕄_w(Γ₁(N); R)`, attached to double cosets in
`Δ₀(N)`, commute. In particular the operators `T_m` and `T_n` commute for all indices `m` and
`n`, whatever their prime factors and their relation to the level, and every `T_n` commutes with
every diamond operator. The coefficient ring is any commutative ring, so these relations hold on
the integral symbol module, before passing to complex periods.

The composite of two Hecke operators is the sum `∑_D m(D₁, D₂; D) • T_D` over the double cosets
met by the products of right-coset representatives
(`TauCeti.ModularSymbols.heckeSymbol_comp_heckeSymbol_eq_sum_nsmul`), with coefficients the
multiplicities `m(δ₂⁻¹, δ₁⁻¹; d⁻¹)`. These are symmetric in `δ₁` and `δ₂`
(`HeckeRing.GL2.multiplicity_inv_comm_Gamma1`) because the Atkin–Lehner anti-involution fixes
every double coset of `Γ₁(N)` in `Δ₀(N)`. This is Shimura's Proposition 3.8, transported to the
action on symbols. A double coset met in one order but not the other has multiplicity zero, so
the two sums agree term by term.

For a double coset in an arbitrary monoid `Δ`, a diamond still commutes with its operator when
the double coset is fixed by conjugation by a lift of the diamond label
(`TauCeti.ModularSymbols.commute_heckeSymbol_diamondSymbol`), by normalizer covariance of Hecke
sums on representations.

## Main results

* `TauCeti.ModularSymbols.commute_heckeSymbol_heckeSymbol`: the Hecke operators of any two
  double cosets of `Γ₁(N)` in `Δ₀(N)` commute.
* `TauCeti.ModularSymbols.commute_heckeTSymbol`: `T_m` and `T_n` commute.
* `TauCeti.ModularSymbols.commute_heckeTSymbol_diamondSymbol`: `T_n` commutes with every
  diamond operator.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, and Proposition 3.8.
* W. Stein, *Modular Forms: A Computational Approach*, §8.3.
-/

public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix Matrix.SpecialLinearGroup
  CongruenceSubgroup MvPolynomial Representation TensorProduct
open scoped MatrixGroups

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w N : ℕ} [NeZero N]

/-- A diamond commutes with the operator of a double coset fixed by conjugation by a lift of
its label. The statement is integral and imposes no condition on the weight. -/
theorem commute_heckeSymbol_diamondSymbol {Δ : Submonoid (GL (Fin 2) ℚ)}
    {D : HeckeCoset Δ ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))}
    (hD : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2)
    [Finite (DecompQuotient ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹)]
    (g : ↥(Gamma0 N))
    (hconj : (mapGL ℚ (g : SL(2, ℤ)))⁻¹ * D.out * mapGL ℚ (g : SL(2, ℤ)) ∈
      doubleCoset (D.out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) :
    Commute (heckeSymbol (R := R) (w := w) (Gamma1 N) (Gamma1 N) D hD)
      (diamondSymbol R w N ((Gamma0Map N).toHomUnits g)) := by
  have hnorm := mapGL_mem_normalizer_Gamma1_map ℚ g
  have hu : diamondSymbol R w N ((Gamma0Map N).toHomUnits g) ∘ₗ Coinvariants.mk _ =
      (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R (Gamma1 N) w) ∘ₗ
        symbolIntRep R w ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_intEntries 2 g⟩ :=
    LinearMap.ext (diamondSymbol_mk g rfl)
  have h := HeckeCoset.heckeSum_comp_of_mem_normalizer D (symbolIntRep R w) hD
    (map_mapGL_le_intEntries 2 (Gamma1 N)) (map_mapGL_le_intEntries 2 (Gamma1 N))
    (fun _ hγ ↦ mk_comp_symbolIntRep_of_mem (Gamma1 N) hγ)
    (mapGL_mem_intEntries 2 g) hnorm hnorm hconj _ hu
  rw [commute_iff_eq]
  refine Coinvariants.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.comp_apply, mul_apply_eq_comp]
  rw [diamondSymbol_mk g rfl, heckeSymbol_mk_eq_heckeSum, heckeSymbol_mk_eq_heckeSum]
  exact LinearMap.congr_fun h x

attribute [local instance] Fintype.ofFinite in
/-- **Any two Hecke operators of level `Γ₁(N)` commute on modular symbols.** For double cosets
`D₁`, `D₂` of `Γ₁(N)` in `Δ₀(N)`, both composites are `∑_D m • T_D` with the same coefficients,
by the symmetry of the multiplicity under the Atkin–Lehner anti-involution. -/
theorem commute_heckeSymbol_heckeSymbol
    (D₁ D₂ : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) :
    Commute (heckeSymbol (R := R) (w := w) (Gamma1 N) (Gamma1 N) D₁
        (Delta0_le_intEntries N D₁.out.2))
      (heckeSymbol (Gamma1 N) (Gamma1 N) D₂ (Delta0_le_intEntries N D₂.out.2)) := by
  classical
  -- the term of the double coset `D` in the composite `T_{E₁} ∘ T_{E₂}`
  let f (E₁ E₂ D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ))) : Module.End R (ModularSymbols R (Gamma1 N) w) :=
    multiplicity ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) (E₂.out : GL (Fin 2) ℚ)⁻¹ (E₁.out : GL (Fin 2) ℚ)⁻¹
        (D.out : GL (Fin 2) ℚ)⁻¹ •
      heckeSymbol (Gamma1 N) (Gamma1 N) D (Delta0_le_intEntries N D.out.2)
  -- a composite is the sum of its terms over any finset containing the double cosets it meets
  have hcomp (E₁ E₂ : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ))) (hE₁ : (E₁.out : GL (Fin 2) ℚ) ∈ intEntries 2)
      (hE₂ : (E₂.out : GL (Fin 2) ℚ) ∈ intEntries 2) (S : Finset _)
      (hS : Finset.univ.image (pairCoset E₁ E₂) ⊆ S) :
      heckeSymbol (R := R) (w := w) (Gamma1 N) (Gamma1 N) E₁ hE₁ *
        heckeSymbol (Gamma1 N) (Gamma1 N) E₂ hE₂ = ∑ D ∈ S, f E₁ E₂ D := by
    rw [Module.End.mul_eq_comp, heckeSymbol_comp_heckeSymbol_eq_sum_nsmul]
    refine (Finset.sum_attach _ (f E₁ E₂)).trans (Finset.sum_subset hS fun D _ hD ↦ ?_)
    -- a double coset met by no pair of representatives has multiplicity zero
    have : IsEmpty (PairCosetFiber E₁ E₂ D (D.out : GL (Fin 2) ℚ)) :=
      ⟨fun i ↦ hD (Finset.mem_image.mpr ⟨i.1.1, Finset.mem_univ _, i.1.2⟩)⟩
    simp only [f]
    rw [← card_pairs_pairCoset_rightCoset_eq_multiplicity (mem_doubleCoset_self _ _ _),
      Nat.card_of_isEmpty, zero_smul]
  rw [commute_iff_eq,
    hcomp D₁ D₂ _ _ _ (Finset.subset_union_left (s₂ := Finset.univ.image (pairCoset D₂ D₁))),
    hcomp D₂ D₁ _ _ _ Finset.subset_union_right]
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  simp only [f]
  rw [multiplicity_inv_comm_Gamma1 N D₁.out.2 D₂.out.2 D.out.2]

/-- **The Hecke operators `T_m` and `T_n` on modular symbols commute**, for all positive indices
`m` and `n`, with no condition relating them to each other or to the level. -/
theorem commute_heckeTSymbol (m n : ℕ) [NeZero m] [NeZero n] :
    Commute (heckeTSymbol R w N m) (heckeTSymbol R w N n) := by
  rw [heckeTSymbol_def, heckeTSymbol_def]
  exact commute_heckeSymbol_heckeSymbol _ _

/-- **Every Hecke operator `T_n` commutes with every diamond on modular symbols**, at every index
`n`, whether or not it is prime to the level. In particular this relation holds over `ℤ`. -/
theorem commute_heckeTSymbol_diamondSymbol (n : ℕ) [NeZero n] (d : (ZMod N)ˣ) :
    Commute (heckeTSymbol R w N n) (diamondSymbol R w N d) := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective d
  rw [heckeTSymbol_def, diamondSymbol_eq_heckeSymbol g hg]
  exact commute_heckeSymbol_heckeSymbol _ _

end TauCeti.ModularSymbols
