/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Diamond
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Gamma0Conjugation

/-!
# Hecke operators commute with diamonds on modular symbols

The prime Hecke operator `T_p` commutes with every diamond operator on
`𝕄_w(Γ₁(N); R)`, including when `p` divides `N`. The coefficient ring is any commutative ring,
so the relation holds on the integral symbol module, before passing to complex periods.

More generally, a diamond commutes with the operator of any integral double coset fixed by
conjugation by a lift of its label. The relation follows from normalizer covariance of Hecke
sums on representations. For the prime operators the requisite double-coset stability is
`HeckeRing.GL2.conj_natDiagGL_mem_doubleCoset_of_prime`.

These are the mixed generator relations between the Hecke and diamond actions on symbols;
commutation between two Hecke operators is a separate assertion.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
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
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [diamondSymbol_mk g rfl, heckeSymbol_mk_eq_heckeSum, heckeSymbol_mk_eq_heckeSum]
  exact LinearMap.congr_fun h x

/-- Every prime Hecke operator commutes with every diamond on modular symbols, at good and
bad primes alike. In particular this relation holds over `ℤ`. -/
theorem commute_heckeTSymbol_diamondSymbol {p : ℕ} [NeZero p] (hp : p.Prime)
    (d : (ZMod N)ˣ) :
    Commute (heckeTSymbol R w N p) (diamondSymbol R w N d) := by
  obtain ⟨g, rfl⟩ := Gamma0Map_toHomUnits_surjective d
  rw [heckeTSymbol_def]
  apply commute_heckeSymbol_diamondSymbol
  have hnorm := mapGL_mem_normalizer_Gamma1_map ℚ g
  have hconj := conj_natDiagGL_mem_doubleCoset_of_prime hp (inv_mem g.2)
  simp only [map_inv] at hconj
  have hdc := doubleCoset_eq_of_mem hconj
  rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL, ← hdc]
  exact (conj_mem_doubleCoset_conj_iff_of_mem_normalizer hnorm hnorm _ _).mpr (by
    rw [← doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset_self _ _ _)

end TauCeti.ModularSymbols
