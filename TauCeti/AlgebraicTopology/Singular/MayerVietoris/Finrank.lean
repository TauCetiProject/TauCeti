/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.LinearAlgebra.Exact

/-!
# Dimensions of homology along the Mayer–Vietoris sequence

Let `U` and `V` be open subsets covering a space `X`, and let `k` be a division ring. When the
singular homologies over `k` of `U ∩ V`, `U`, `V` and `X` are finite-dimensional and that of
`U ∩ V` vanishes in all large degrees, the Mayer–Vietoris long exact sequence
`⋯ ⟶ Hₙ(U ∩ V) ⟶ Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X) ⟶ Hₙ₋₁(U ∩ V) ⟶ ⋯ ⟶ H₀(X) ⟶ 0`
forces the alternating sum of `dim Hₙ(U ∩ V) - (dim Hₙ(U) + dim Hₙ(V)) + dim Hₙ(X)` to vanish
(`TauCeti.finsum_finrank_singularHomology_mayerVietoris`). This is the dimension count behind the
additivity of the Euler characteristic along open covers.

The exact sequence (`TopCat.mayerVietoris_exact₁`, `TopCat.mayerVietoris_exact₂`,
`TopCat.mayerVietoris_exact₃` and `TopCat.epi_mayerVietorisFromBiprod_zero`) is fed to
`TauCeti.finsum_neg_one_pow_finrank_eq_zero_of_exact`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits Module AlgebraicTopology Set

universe w

namespace TauCeti

/-- Singular homology is by definition the homology of the singular simplicial set, the form in
which the Mayer--Vietoris sequence is stated. -/
private lemma singularHomologyFunctor_obj_obj_eq (k : Type w) [Ring k] (n : ℕ) (Y : TopCat.{w}) :
    ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (ModuleCat.of k k)).obj Y =
      (TopCat.toSSet.obj Y).homology (ModuleCat.of k k) n :=
  rfl

/-- **The Mayer--Vietoris relation between dimensions of homology.**  If `X` is covered by two
open subsets `U` and `V`, the singular homologies of `U ∩ V`, `U`, `V` and `X` over a division
ring are finite-dimensional and that of `U ∩ V` vanishes in all large degrees, then the
alternating sum of `dim Hₙ(U ∩ V) - (dim Hₙ(U) + dim Hₙ(V)) + dim Hₙ(X)` vanishes. -/
theorem finsum_finrank_singularHomology_mayerVietoris {X : TopCat.{w}} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (k : Type w) [DivisionRing k]
    [hI : ∀ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of ↥(U ∩ V)))]
    [∀ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of U))]
    [∀ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of V))]
    [hX : ∀ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj X)]
    (hfin : (Function.support fun n ↦ finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of ↥(U ∩ V)))).Finite) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
          (ModuleCat.of k k)).obj (TopCat.of ↥(U ∩ V))) : ℤ) -
        (finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
            (ModuleCat.of k k)).obj (TopCat.of U)) +
          finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
            (ModuleCat.of k k)).obj (TopCat.of V)) : ℕ) +
        finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
          (ModuleCat.of k k)).obj X)) = 0 := by
  let R := ModuleCat.of k k
  have hfg (n : ℕ) := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₂ R hU hV hUV n)
  have hgδ (n : ℕ) := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₃ R hU hV hUV (n + 1) n)
  have hδf (n : ℕ) := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₁ R hU hV hUV (n + 1) n)
  have hg := (ModuleCat.epi_iff_surjective _).1
    (TopCat.epi_mayerVietorisFromBiprod_zero R hU hV hUV)
  -- The exact sequence is phrased through simplicial homology of singular simplicial sets, so the
  -- hypotheses are transported along `singularHomologyFunctor_obj_obj_eq`.
  have (n : ℕ) : Module.Finite k
      ((TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).homology R n : ModuleCat.{w} k) := by
    rw [← singularHomologyFunctor_obj_obj_eq]
    exact hI n
  have (n : ℕ) : Module.Finite k ((TopCat.toSSet.obj X).homology R n : ModuleCat.{w} k) := by
    rw [← singularHomologyFunctor_obj_obj_eq]
    exact hX n
  have hB (n : ℕ) : finrank k ↑((TopCat.toSSet.obj (TopCat.of U)).homology R n ⊞
      (TopCat.toSSet.obj (TopCat.of V)).homology R n) =
      finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj (TopCat.of U)) +
        finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj (TopCat.of V)) := by
    rw [← singularHomologyFunctor_obj_obj_eq, ← singularHomologyFunctor_obj_obj_eq]
    exact ModuleCat.finrank_biprod _ _
  have hA (Y : TopCat.{w}) (n : ℕ) : finrank k ↑((TopCat.toSSet.obj Y).homology R n) =
      finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj Y) := by
    rw [singularHomologyFunctor_obj_obj_eq]
  have := finsum_neg_one_pow_finrank_eq_zero_of_exact hfg hgδ hδf hg hfin
  simp only [hB, hA] at this
  exact this

end TauCeti
