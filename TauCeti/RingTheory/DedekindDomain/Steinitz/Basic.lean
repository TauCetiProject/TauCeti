/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Ideal
public import TauCeti.RingTheory.DedekindDomain.ModuleDecomposition
import TauCeti.LinearAlgebra.Dimension.Pi
import TauCeti.RingTheory.FractionalIdeal.Projective

/-!
# Steinitz's theorem for finite projective modules over a Dedekind domain

Let `R` be a Dedekind domain and `M` a finitely generated projective `R`-module of rank `r + 1`;
over a Dedekind domain these are exactly the finite flat, or finite torsion-free, modules. Then

```text
M ≃ Rʳ × ⋀ʳ⁺¹ M,
```

so `M` is determined up to isomorphism by its rank and its determinant, the top exterior power
`⋀ʳ⁺¹ M`, an invertible module. In particular two finite projective modules of the same positive
rank are isomorphic exactly when their determinants are.

The proof combines three facts.

* A pseudo-basis writes `M` as a product of `r + 1` nonzero ideals
  (`Module.exists_linearEquiv_pi_ideal`).
* The product identity `I × J ≃ R × IJ` for nonzero ideals collapses such a product to
  `Rʳ × I` with `I` the product of the ideals (`Ideal.nonempty_pi_linearEquiv_pi_prod_prod`).
  This is the classical form of Steinitz's theorem, `Module.exists_linearEquiv_pi_prod_ideal`.
* The top exterior power of `Rʳ × I` is `I` (`Ideal.exteriorPowerPiProdEquiv`), so the ideal
  in the classical form is the determinant of `M`.

The rank used is `Module.finrank R M`, which for a finite flat module over a domain is its
dimension after extension of scalars to the fraction field.

## Main results

* `Ideal.nonempty_prod_linearEquiv_prod_mul`: `I × J ≃ R × IJ` for nonzero ideals.
* `Module.exists_linearEquiv_pi_prod_ideal`: a finite flat module of rank `r + 1` is `Rʳ × I` for
  a nonzero ideal `I`.
* `Module.nonempty_linearEquiv_pi_prod_exteriorPower`: such a module is `Rʳ × ⋀ʳ⁺¹ M`.
* `Module.nonempty_linearEquiv_iff_nonempty_linearEquiv_exteriorPower`: two such modules of the
  same rank are isomorphic exactly when their top exterior powers are.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §3, Proposition 3.4 and Corollary 3.5.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §1,
  Theorem 1.6 and Lemma 1.5.
-/

public section

open Module exteriorPower
open scoped nonZeroDivisors TensorProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

namespace Ideal

/-- A finite product of nonzero ideals of a domain is nonzero. -/
private theorem prod_ne_bot {ι : Type*} {s : Finset ι} {J : ι → Ideal R}
    (h : ∀ i ∈ s, J i ≠ ⊥) : ∏ i ∈ s, J i ≠ ⊥ := by
  simpa only [← Submodule.zero_eq_bot] using Finset.prod_ne_zero_iff.mpr h

/-- **The product identity for integral ideals.** For nonzero ideals `I` and `J` of a Dedekind
domain, `I × J ≃ R × IJ`. -/
theorem nonempty_prod_linearEquiv_prod_mul {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Nonempty ((I × J) ≃ₗ[R] R × (I * J : Ideal R)) := by
  let K := FractionRing R
  have hI' : (I : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  obtain ⟨e⟩ := FractionalIdeal.nonempty_prod_linearEquiv_prod_mul hI'.isUnit hJ'
  have hIJ : (((I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K) : FractionalIdeal R⁰ K) :
      Submodule R K) = (((I * J : Ideal R) : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [FractionalIdeal.coeIdeal_mul]
  exact ⟨((FractionalIdeal.coeIdealEquiv I).symm.prodCongr
    (FractionalIdeal.coeIdealEquiv J).symm) ≪≫ₗ e ≪≫ₗ (LinearEquiv.refl R R).prodCongr
      (LinearEquiv.ofEq _ _ hIJ ≪≫ₗ FractionalIdeal.coeIdealEquiv (I * J))⟩

/-- A product of `r + 1` nonzero ideals of a Dedekind domain is isomorphic to `Rʳ × ∏ᵢ Jᵢ`. -/
theorem nonempty_pi_linearEquiv_pi_prod_prod :
    ∀ {r : ℕ} (J : Fin (r + 1) → Ideal R), (∀ i, J i ≠ ⊥) →
      Nonempty (((i : Fin (r + 1)) → J i) ≃ₗ[R] (Fin r → R) × (∏ i, J i : Ideal R))
  | 0, J, _ => by
    have h : J 0 = ∏ i, J i := by rw [Fin.prod_univ_one]
    exact ⟨(Fin.consLinearEquiv R fun i ↦ J i).symm ≪≫ₗ
      LinearEquiv.prodComm R _ _ ≪≫ₗ LinearEquiv.prodCongr (LinearEquiv.ofSubsingleton _ _)
        (LinearEquiv.ofEq _ _ h)⟩
  | r + 1, J, hJ => by
    obtain ⟨e⟩ := nonempty_pi_linearEquiv_pi_prod_prod (fun i : Fin (r + 1) ↦ J i.succ)
      fun i ↦ hJ i.succ
    have hK : (∏ i : Fin (r + 1), J i.succ : Ideal R) ≠ ⊥ := prod_ne_bot fun i _ ↦ hJ i.succ
    obtain ⟨f⟩ := nonempty_prod_linearEquiv_prod_mul (hJ 0) hK
    have h : J 0 * ∏ i : Fin (r + 1), J i.succ = ∏ i, J i := (Fin.prod_univ_succ J).symm
    -- `J₀ × (Rʳ × K) ≃ Rʳ × (J₀ × K) ≃ Rʳ × (R × J₀ K) ≃ Rʳ⁺¹ × J₀ K`.
    exact ⟨(Fin.consLinearEquiv R fun i ↦ J i).symm ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr e ≪≫ₗ (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R _).prodCongr f ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      ((LinearEquiv.prodComm R _ _).trans (Fin.consLinearEquiv R fun _ ↦ R)).prodCongr
        (LinearEquiv.ofEq _ _ h)⟩

end Ideal

namespace Module

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

/-- **Steinitz's theorem.** A finite flat module of rank `r + 1` over a Dedekind domain, that is
a finitely generated projective module, is isomorphic to `Rʳ × I` for a nonzero ideal `I`. -/
theorem exists_linearEquiv_pi_prod_ideal {r : ℕ} (hr : finrank R M = r + 1) :
    ∃ I : Ideal R, I ≠ ⊥ ∧ Nonempty (M ≃ₗ[R] (Fin r → R) × I) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := exists_linearEquiv_pi_ideal R (FractionRing R) M
  -- The number of ideal factors is the rank of `M`.
  have hrank := (finrank_eq_card_of_linearEquiv_pi hJ e).symm.trans hr
  generalize finrank (FractionRing R) (FractionRing R ⊗[R] M) = n at J hJ e hrank
  obtain rfl : n = r + 1 := by rwa [Fintype.card_fin] at hrank
  obtain ⟨f⟩ := Ideal.nonempty_pi_linearEquiv_pi_prod_prod J hJ
  exact ⟨∏ i, J i, Ideal.prod_ne_bot fun i _ ↦ hJ i, ⟨e ≪≫ₗ f⟩⟩

/-- **Steinitz decomposition by the determinant.** A finite flat module `M` of rank `r + 1` over a
Dedekind domain, that is a finitely generated projective module, is isomorphic to
`Rʳ × ⋀ʳ⁺¹ M`, the free module of rank `r` plus its top exterior power. -/
theorem nonempty_linearEquiv_pi_prod_exteriorPower {r : ℕ} (hr : finrank R M = r + 1) :
    Nonempty (M ≃ₗ[R] (Fin r → R) × ⋀[R]^(r + 1) M) := by
  obtain ⟨I, -, ⟨e⟩⟩ := exists_linearEquiv_pi_prod_ideal M hr
  exact ⟨e ≪≫ₗ (LinearEquiv.refl R _).prodCongr
    ((I.exteriorPowerPiProdEquiv r).symm ≪≫ₗ (e.exteriorPower (r + 1)).symm)⟩

/-- **Rank and determinant classify finite projective modules over a Dedekind domain.** Two finite
flat modules of the same rank `r + 1` are isomorphic exactly when their top exterior powers
`⋀ʳ⁺¹` are. -/
theorem nonempty_linearEquiv_iff_nonempty_linearEquiv_exteriorPower (N : Type*) [AddCommGroup N]
    [Module R N] [Module.Finite R N] [Module.Flat R N] {r : ℕ} (hM : finrank R M = r + 1)
    (hN : finrank R N = r + 1) :
    Nonempty (M ≃ₗ[R] N) ↔ Nonempty (⋀[R]^(r + 1) M ≃ₗ[R] ⋀[R]^(r + 1) N) := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.exteriorPower (r + 1)⟩, fun ⟨e⟩ ↦ ?_⟩
  obtain ⟨eM⟩ := nonempty_linearEquiv_pi_prod_exteriorPower M hM
  obtain ⟨eN⟩ := nonempty_linearEquiv_pi_prod_exteriorPower N hN
  exact ⟨eM ≪≫ₗ (LinearEquiv.refl R _).prodCongr e ≪≫ₗ eN.symm⟩

end Module
