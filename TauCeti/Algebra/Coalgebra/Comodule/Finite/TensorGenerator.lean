/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.MatrixCoefficient
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.RightRigid
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import TauCeti.CategoryTheory.Monoidal.Rigid.TensorGenerator

/-!
# Finite generation and tensor generators

Let `H` be a Hopf algebra over a field `K`. This file proves that `H` is finitely generated as a
`K`-algebra exactly when one finite-dimensional comodule `X` tensor-generates
`FGComoduleCat K H` with its dual: every finite comodule is a quotient of a subobject of a finite
direct sum of tensor words `X^{⊗ a} ⊗ (Xᘁ)^{⊗ b}` (`TauCeti.IsTensorGenerator`). For a
commutative `H` this is the finite-type criterion for the affine group scheme `Spec H` in terms of
its category of representations.

Both directions go through matrix coefficients, using the dictionary of
`TauCeti.Algebra.Coalgebra.Comodule.Finite.MatrixCoefficient`: a finite comodule is a
subquotient of a finite sum of members of a family exactly when its coefficients lie among
theirs, and the coefficients of a tensor product are the products of the coefficients.

* If `H` is finitely generated, a finite regular subcomodule `X` containing a set of generators
  has coefficients generating `H`. Every element of `H` is then a sum of products of
  coefficients of `X`, that is a coefficient of a sum of tensor powers of `X`. The coefficients
  of a given finite comodule span a finite-dimensional space, so finitely many tensor powers
  suffice. The dual is not needed in this direction.
* If `X` tensor-generates, every finite comodule has its coefficients in the algebra generated
  by the coefficients of `X` and `Xᘁ`, which are finite-dimensional. By the fundamental theorem
  of coalgebras every element of `H` is a coefficient of a finite regular subcomodule, so this
  algebra is all of `H`.

## Main declarations

* `TauCeti.FGComoduleCat.exists_isTensorGenerator`: a finitely generated Hopf algebra has a
  finite comodule tensor-generating its comodules.
* `TauCeti.FGComoduleCat.finiteType_of_isTensorGenerator`: a tensor generator makes the Hopf
  algebra finitely generated.
* `TauCeti.FGComoduleCat.finiteType_iff_exists_isTensorGenerator`: the criterion.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Proposition 2.20(b) and its proof.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.5.
-/

public section

open CategoryTheory MonoidalCategory Limits

namespace TauCeti.FGComoduleCat

universe u

variable {K : Type u} [Field K] {H : Type u} [Ring H] [HopfAlgebra K H]

/-- **A finitely generated Hopf algebra has a tensor generator.** If `H` is finitely generated
over the field `K`, some finite-dimensional comodule tensor-generates `FGComoduleCat K H`;
tensor words without dual factors already suffice. -/
theorem exists_isTensorGenerator [Algebra.FiniteType K H] :
    ∃ X : FGComoduleCat.{u, u, u} K H, IsTensorGenerator X := by
  obtain ⟨M, hM, htop⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := K) (C := H)
  -- `hM` is stated for the underlying submodule, whose carrier is that of `M`.
  have : Module.Finite K M := hM
  let X : FGComoduleCat.{u, u, u} K H := of (R := K) (C := H) M
  refine ⟨X, (isTensorGenerator_iff X).2 fun Y ↦ ?_⟩
  -- The coefficients of all tensor powers of `X` span a subalgebra containing those of `X`.
  let T : Submodule K H :=
    ⨆ r : ℕ, Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := ↥(tensorPow X r))
  have hone : (1 : H) ∈ T := Submodule.mem_iSup_of_mem 0 <| by
    rw [tensorPow_zero, matrixCoefficientSubmodule_tensorUnit]
    exact Submodule.mem_span_singleton_self 1
  have hmul (x y : H) (hx : x ∈ T) (hy : y ∈ T) : x * y ∈ T := by
    refine (?_ : T * T ≤ T) (Submodule.mul_mem_mul hx hy)
    rw [Submodule.iSup_mul]
    refine iSup_le fun r ↦ ?_
    rw [Submodule.mul_iSup]
    refine iSup_le fun q ↦ ?_
    rw [mul_matrixCoefficientSubmodule_tensorPow]
    exact le_iSup (fun r ↦
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := ↥(tensorPow X r))) (q + r)
  have hT : Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := Y) ≤ T := by
    have hadjoin : Algebra.adjoin K (Comodule.matrixCoefficientSet (R := K) (C := H) (M := M)) ≤
        T.toSubalgebra hone hmul := by
      refine Algebra.adjoin_le fun c hc ↦ Submodule.mem_iSup_of_mem 1 ?_
      rw [matrixCoefficientSubmodule_eq_of_iso (ρ_ X)]
      exact Submodule.subset_span hc
    intro c _
    have hc : c ∈ Comodule.matrixCoefficientSubalgebra (R := K) (C := H) (M := M) := by
      rw [htop]
      trivial
    exact hadjoin hc
  obtain ⟨ι, _, g, Z, i, p, hip⟩ := exists_mono_epi_of_matrixCoefficientSubmodule_le_iSup
    (M := Y) (F := fun r ↦ tensorPow X r ⊗ tensorPow Xᘁ 0) <|
    hT.trans <| iSup_mono fun r ↦ (matrixCoefficientSubmodule_eq_of_iso (ρ_ (tensorPow X r))).ge
  exact ⟨ι, inferInstance, g, fun _ ↦ 0, Z, i, p, hip⟩

/-- **A tensor generator makes the Hopf algebra finitely generated.** If a finite-dimensional
comodule `X` tensor-generates `FGComoduleCat K H` with its dual, then `H` is generated as a
`K`-algebra by the finitely many coefficients of `X` and `Xᘁ`. -/
theorem finiteType_of_isTensorGenerator {X : FGComoduleCat.{u, u, u} K H}
    (hX : IsTensorGenerator X) : Algebra.FiniteType K H := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 (inferInstance : Module.Finite K
    ↥(Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ⊔
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := ↥Xᘁ)))
  let A := Algebra.adjoin K (s : Set H)
  have hA : Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ⊔
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := ↥Xᘁ) ≤
        Subalgebra.toSubmodule A := by
    rw [← hs]
    exact Submodule.span_le.2 Algebra.subset_adjoin
  have hmul : Subalgebra.toSubmodule A * Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule A :=
    Submodule.mul_le.2 fun _ hx _ hy ↦ A.mul_mem hx hy
  -- Coefficients of tensor powers stay in `A`.
  have hpow (Y : FGComoduleCat.{u, u, u} K H)
      (hY : Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := Y) ≤
        Subalgebra.toSubmodule A) (n : ℕ) :
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := ↥(tensorPow Y n)) ≤
        Subalgebra.toSubmodule A := by
    induction n with
    | zero =>
      rw [tensorPow_zero, matrixCoefficientSubmodule_tensorUnit, Submodule.span_le,
        Set.singleton_subset_iff]
      exact A.one_mem
    | succ n ih =>
      rw [tensorPow_succ, matrixCoefficientSubmodule_tensorObj]
      exact (mul_le_mul' hY ih).trans hmul
  refine ⟨⟨s, eq_top_iff.2 fun h _ ↦ ?_⟩⟩
  -- Every element of `H` is a coefficient of a finite regular subcomodule.
  obtain ⟨D, hD, hhD⟩ := Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem (k := K) h
  have : Module.Finite K D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let Y : FGComoduleCat.{u, u, u} K H := of (R := K) (C := H) D.toRegularSubcomodule
  have hhY : h ∈ Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := Y) :=
    D.toRegularSubcomodule.toSubmodule_le_matrixCoefficientSubmodule <| by
      rwa [Subcoalgebra.toRegularSubcomodule_toSubmodule]
  obtain ⟨ι, _, a, b, Z, i, p, hip⟩ := (isTensorGenerator_iff X).1 hX Y
  have hY := (matrixCoefficientSubmodule_le_iSup_iff_exists_mono_epi (κ := ι) (M := Y)
    (F := fun j ↦ tensorPow X (a j) ⊗ tensorPow Xᘁ (b j))).2 ⟨ι, inferInstance, id, Z, i, p, hip⟩
  rw [← Subalgebra.mem_toSubmodule]
  refine (hY.trans (iSup_le fun j ↦ ?_)) hhY
  rw [matrixCoefficientSubmodule_tensorObj]
  exact (mul_le_mul' (hpow X (le_sup_left.trans hA) _)
    (hpow Xᘁ (le_sup_right.trans hA) _)).trans hmul

/-- **Finite generation is tensor generation.** A Hopf algebra over a field is finitely generated
exactly when some finite-dimensional comodule tensor-generates its category of finite
comodules with its dual (Deligne–Milne, Proposition 2.20(b)). -/
theorem finiteType_iff_exists_isTensorGenerator :
    Algebra.FiniteType K H ↔ ∃ X : FGComoduleCat.{u, u, u} K H, IsTensorGenerator X :=
  ⟨fun _ ↦ exists_isTensorGenerator, fun ⟨_, hX⟩ ↦ finiteType_of_isTensorGenerator hX⟩

end TauCeti.FGComoduleCat
