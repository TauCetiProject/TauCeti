/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.FringePresentation.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finitely presented modules over a dagger algebra descend to a fringe stage

Let `A` be a `K`-algebra with a fringe presentation, so that `A` is the colimit of the stages
`A_ρ = T_n(ρ) ⧸ (f₁, …, f_r)` as `ρ → 1⁺`. Each stage map `A_ρ → A` makes `A` an
`A_ρ`-algebra. This file shows that every finitely presented `A`-module `M` is defined over
every stage close enough to `1`: for all such `ρ` there is a finitely presented `A_ρ`-module
`M_ρ = A_ρⁿ ⧸ N`, with `N` finitely generated, such that

```text
A ⊗[A_ρ] M_ρ ≃ₗ[A] M.
```

The algebra `A ≅ W_n ⧸ (f₁, …, f_r)` is a dagger algebra, and over a complete field dagger
algebras are noetherian (`TauCeti.Dagger.IsDaggerAlgebra.isNoetherianRing`), so there the result
applies to every finite `A`-module (`Module.finitePresentation_of_finite`). It lets finite modules
over a dagger algebra, such as the modules of sections of coherent sheaves on affinoid dagger
spaces, be studied through finite modules over the stages `A_ρ`, which are affinoid algebras when
`ρ` lies in the divisible hull of the value group.

The proof spreads out a presentation. Write `M` as the cokernel of a matrix `C` with entries in
`A`. Its finitely many entries lie in the fringe algebra of every radius close enough to `1`, so
`C` is the image of a matrix `C_ρ` over `A_ρ`. Base change along `A_ρ → A` is right exact and
identifies `A ⊗[A_ρ] A_ρᵐ` with `Aᵐ`, so it carries the cokernel of `C_ρ` to the cokernel of
`C`.

## Main results

* `TauCeti.Dagger.FringePresentation.eventually_exists_linearEquiv_tensorProduct`: a finitely
  presented `A`-module is the base change of a finitely presented module over every stage of
  radius close enough to `1`, and `exists_linearEquiv_tensorProduct` gives one such stage.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §2, Lemma 2.15 (1).
-/

public section

namespace TauCeti.Dagger.FringePresentation

open Filter TensorProduct

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Type*} [CommRing A] [Algebra K A]
  (P : FringePresentation K A)

/-- **Finitely presented modules descend to a fringe stage.** A finitely presented `A`-module `M`
is, for every radius `ρ` close enough to `1`, the base change `A ⊗[A_ρ] (A_ρⁿ ⧸ N)` of a
finitely presented module over the stage `A_ρ`. -/
theorem eventually_exists_linearEquiv_tensorProduct (M : Type*) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] :
    ∀ᶠ ρ in atBot, ∃ (n : ℕ) (N : Submodule (P.stage ρ) (Fin n → P.stage ρ)),
      N.FG ∧ Nonempty (A ⊗[P.stage ρ] ((Fin n → P.stage ρ) ⧸ N) ≃ₗ[A] M) := by
  -- A presentation `Aᵐ → Aⁿ → M → 0`; the entries of its matrix come from the stage `A_ρ`.
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' A M
  filter_upwards [eventually_all.mpr fun i : Fin n ↦ eventually_all.mpr fun j : Fin m ↦
    P.eventually_mem_fringeAlgebra (LinearMap.toMatrix' g i j)] with ρ hρ
  choose c hc using fun i j ↦ P.mem_fringeAlgebra.mp (hρ i j)
  let gρ : (Fin m → P.stage ρ) →ₗ[P.stage ρ] (Fin n → P.stage ρ) := Matrix.toLin' (Matrix.of c)
  refine ⟨n, LinearMap.range gρ, Submodule.fg_range _, ⟨?_⟩⟩
  -- Under `A ⊗[A_ρ] A_ρᵏ ≃ Aᵏ`, the base change of `gρ` is `g`.
  let e := piScalarRight (P.stage ρ) A A (Fin n)
  let e' := piScalarRight (P.stage ρ) A A (Fin m)
  have hcomm : g ∘ₗ e'.toLinearMap = e.toLinearMap ∘ₗ gρ.baseChange A := by
    ext j i
    simp [gρ, e, e', Algebra.smul_def, hc, LinearMap.toMatrix'_apply,
      Pi.apply_single (fun _ ↦ P.ofStage ρ) fun _ ↦ map_zero _]
  have hrange : LinearMap.range g = (LinearMap.range (gρ.baseChange A)).map e.toLinearMap := by
    rw [← LinearMap.range_comp, ← hcomm, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr e'.surjective)]
  -- Base change is right exact, so both `A ⊗[A_ρ] (A_ρⁿ ⧸ range gρ)` and `M` are `Aⁿ ⧸ range g`.
  have hexact : Function.Exact (gρ.baseChange A) ((LinearMap.range gρ).mkQ.baseChange A) :=
    lTensor_exact A (LinearMap.exact_map_mkQ_range gρ) (Submodule.mkQ_surjective _)
  exact ((hexact.linearEquivOfSurjective
    (LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _))).symm.trans
    (Submodule.Quotient.equiv _ _ e hrange.symm)).trans (hfg.linearEquivOfSurjective hf)

/-- A finitely presented `A`-module is the base change `A ⊗[A_ρ] (A_ρⁿ ⧸ N)` of a finitely
presented module over some stage `A_ρ`. -/
theorem exists_linearEquiv_tensorProduct (M : Type*) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] :
    ∃ (ρ : Set.Ioc (1 : ℝ) P.radius) (n : ℕ) (N : Submodule (P.stage ρ) (Fin n → P.stage ρ)),
      N.FG ∧ Nonempty (A ⊗[P.stage ρ] ((Fin n → P.stage ρ) ⧸ N) ≃ₗ[A] M) :=
  (P.eventually_exists_linearEquiv_tensorProduct M).exists

end TauCeti.Dagger.FringePresentation
