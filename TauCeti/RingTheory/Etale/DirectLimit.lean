/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Etale.Finite
public import TauCeti.Algebra.Colimit.Ring
public import TauCeti.RingTheory.Etale.NoetherianDescent

/-!
# Finite étale algebras over directed colimits of rings

Let `R = Ring.DirectLimit G f` be the colimit of a directed system of commutative rings `G i`,
indexed by a nonempty directed preorder. No finiteness or noetherian hypothesis is imposed on the
`G i`. This file shows that every finite étale `R`-algebra `S` comes from a finite stage: there
are an index `i` and a finite étale `G i`-algebra `Sᵢ` with `S ≃ₐ[R] R ⊗[G i] Sᵢ`.

By `Algebra.Etale.exists_subalgebra_fg_of_finite`, `S` is the base change of a finite étale
algebra `S₀` over a subring `R₀` of `R` of finite type over `ℤ`. Such a subring is finitely
presented over `ℤ`, so its inclusion into `R` factors through some `G i`
(`Ring.DirectLimit.exists_of_comp_eq_of_finitePresentation`), and `Sᵢ = G i ⊗[R₀] S₀` works.

The index set must be nonempty: the colimit of the empty system is `ℤ`, and the finite étale
`ℤ`-algebra `ℤ × ℤ` comes from no stage.

## Main results

* `Ring.DirectLimit.exists_etale_finite_algEquiv_tensorProduct`: a finite étale algebra over the
  colimit is the base change of a finite étale algebra over some stage.
* `Ring.DirectLimit.finiteEtale_essSurj`: the same statement in the category
  `CommAlgCat.FiniteEtale`, for the base change functors from the stages.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
* [Stacks Project, Lemma 10.143.3 (8)](https://stacks.math.columbia.edu/tag/00U2) for the
  noetherian models of étale algebras.
-/

public section

universe v u

open TensorProduct CommAlgCat

namespace Ring.DirectLimit

variable {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type u}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]

/-- A finite étale algebra over a directed colimit of rings is the base change of a finite étale
algebra over some stage. -/
theorem exists_etale_finite_algEquiv_tensorProduct (S : Type*) [CommRing S]
    [Algebra (DirectLimit G (f · · ·)) S] [Algebra.Etale (DirectLimit G (f · · ·)) S]
    [Module.Finite (DirectLimit G (f · · ·)) S] :
    ∃ i, ∃ (Sᵢ : Type u) (_ : CommRing Sᵢ) (_ : Algebra (G i) Sᵢ),
      Algebra.Etale (G i) Sᵢ ∧ Module.Finite (G i) Sᵢ ∧
      letI := (of G (f · · ·) i).toAlgebra
      Nonempty (S ≃ₐ[DirectLimit G (f · · ·)] DirectLimit G (f · · ·) ⊗[G i] Sᵢ) := by
  obtain ⟨R₀, S₀, _, _, hR₀, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg_of_finite ℤ (DirectLimit G (f · · ·)) S
  have : Algebra.FinitePresentation ℤ R₀ :=
    Algebra.FinitePresentation.of_finiteType.1 (Subalgebra.fg_iff_finiteType R₀ |>.1 hR₀)
  obtain ⟨i, φ, hφ⟩ :=
    exists_of_comp_eq_of_finitePresentation (algebraMap R₀ (DirectLimit G (f · · ·)))
  let := (of G (f · · ·) i).toAlgebra
  let : Algebra R₀ (G i) := φ.toAlgebra
  have : IsScalarTower R₀ (G i) (DirectLimit G (f · · ·)) :=
    .of_algebraMap_eq fun x ↦ congr($hφ x).symm
  -- The stage model `G i ⊗[R₀] S₀` is finite over `G i`, hence small over `G i`.
  have : Small.{u} (G i ⊗[R₀] S₀) := Module.Finite.small (G i) _
  let e' := Shrink.algEquiv (G i) (G i ⊗[R₀] S₀)
  exact ⟨i, Shrink.{u} (G i ⊗[R₀] S₀), inferInstance, inferInstance, .of_equiv e'.symm,
    .equiv e'.symm.toLinearEquiv,
    ⟨e.trans <| (Algebra.TensorProduct.cancelBaseChange R₀ (G i) _ _ S₀).symm.trans <|
      Algebra.TensorProduct.congr .refl e'.symm⟩⟩

/-- Every finite étale algebra over a directed colimit of rings is, up to isomorphism, the base
change of a finite étale algebra over some stage. -/
theorem finiteEtale_essSurj (S : FiniteEtale.{max v u} (DirectLimit G (f · · ·))) :
    ∃ i, ∃ Sᵢ : FiniteEtale.{u} (G i),
      letI := (of G (f · · ·) i).toAlgebra
      Nonempty ((FiniteEtale.baseChange (G i) (DirectLimit G (f · · ·))).obj Sᵢ ≅ S) := by
  obtain ⟨i, Sᵢ, _, _, _, _, ⟨e⟩⟩ := exists_etale_finite_algEquiv_tensorProduct (f := f) S.obj
  let := (of G (f · · ·) i).toAlgebra
  exact ⟨i, .of (G i) Sᵢ, ⟨FiniteEtale.isoMk e.symm⟩⟩

end Ring.DirectLimit
