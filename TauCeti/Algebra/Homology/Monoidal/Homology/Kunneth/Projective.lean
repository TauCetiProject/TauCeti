/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Homology.Monoidal.Homology.Braiding

/-!
# The Künneth theorem for a factor with projective homology

Let `K` be a chain complex of projective modules over a commutative ring `R`, indexed by `ℕ`,
whose homology modules are projective, and let `L` be any chain complex of `R`-modules indexed by
`ℕ`.  Then the Künneth map

`⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)`

is an isomorphism (`HomologicalComplex.isIso_homologyKunneth_of_projective`).  No condition is
imposed on `L` or on `R`.

The cycles of `K` split off its terms and its homology splits off its cycles
(`ChainComplex.isSplitMono_iCycles_of_projective_homology`), so `K` is homotopy equivalent to a
complex with zero differentials whose terms are its homology modules
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).  These are projective, hence flat, so the
Künneth theorem for a flat factor with zero differentials
(`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`) applies, and the Künneth map is
invariant under homotopy equivalences
(`HomologicalComplex.isIso_homologyKunneth_iff_of_homotopyEquiv`).

When moreover the homology of `K` is a single copy of `R`, in one degree `r` and with basis `o`,
only one summand of the Künneth map survives, so the cross product `x ↦ o × x` is a bijection
`H_q(L) ≅ H_{r+q}(K ⊗ L)` (`HomologicalComplex.bijective_homologyCross_tmul`). For the relative
chains of `(ℝʳ, ℝʳ ∖ 0)` this is the suspension isomorphism by a local orientation.

By the symmetry of the Künneth map (`ChainComplex.isIso_homologyKunneth_comm`), the same
holds with the factors interchanged, the projective factor second
(`HomologicalComplex.isIso_homologyKunneth_of_projective_right`).

A typical `K` is the relative chain complex of a topological pair with free relative homology, such
as a cube modulo its boundary; the theorem then computes the relative homology of the product of
the pair with an arbitrary space, on either side.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory

namespace HomologicalComplex

universe u

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ p, Module.Projective R (K.X p)] [∀ p, Module.Projective R (K.homology p)]

/-- **The Künneth theorem when one factor is projective with projective homology.**  If `K` is a
complex of projective modules indexed by `ℕ` whose homology modules are projective, then for every
complex `L` the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an isomorphism. -/
theorem isIso_homologyKunneth_of_projective (n : ℕ) : IsIso (homologyKunneth K L n) := by
  have (p : ℕ) : Projective (K.homology p) := ModuleCat.projective_of_categoryTheory_projective _
  have (p : ℕ) : Projective (K.X p) := ModuleCat.projective_of_categoryTheory_projective _
  have := K.isSplitMono_iCycles_of_projective_homology
  -- `K` is homotopy equivalent to a complex with zero differentials, whose terms are the
  -- homology modules of `K` and so are flat
  obtain ⟨K', hK', ⟨e⟩⟩ := K.exists_homotopyEquiv_d_eq_zero
  have (p : ℕ) : Module.Flat R (K'.X p) :=
    have : Module.Projective R (K'.X p) := .of_equiv ((e.toHomologyIso p).trans
      (K'.XIsoHomologyOfDEqZero p (hK' _ _) (hK' _ _)).symm).toLinearEquiv
    inferInstance
  rw [isIso_homologyKunneth_iff_of_homotopyEquiv n e (HomotopyEquiv.refl L)]
  exact isIso_homologyKunneth_of_d_eq_zero_of_flat K' L hK' n

/-- **The Künneth theorem when the second factor is projective with projective homology.**  If `K`
is a complex of projective modules indexed by `ℕ` whose homology modules are projective, then for
every complex `L` the Künneth map `⨁_{p + q = n} Hₚ(L) ⊗ H_q(K) ⟶ Hₙ(L ⊗ K)` is an isomorphism.
This is `HomologicalComplex.isIso_homologyKunneth_of_projective` with the factors interchanged. -/
theorem isIso_homologyKunneth_of_projective_right (n : ℕ) : IsIso (homologyKunneth L K n) :=
  (ChainComplex.isIso_homologyKunneth_comm L K n).2
    (isIso_homologyKunneth_of_projective K L n)

open Limits in
omit [∀ p, Module.Projective R (K.homology p)] in
/-- **The cross product with a basis of homology concentrated in one degree is bijective.** Let `K`
be a complex of projective modules indexed by `ℕ` whose homology vanishes outside degree `r` and
is free of rank one in degree `r`, with basis `o`. Then for every complex `L` the cross product
`x ↦ o × x` is a bijection `H_q(L) → H_n(K ⊗ L)` for `r + q = n`. -/
theorem bijective_homologyCross_tmul {r : ℕ} (hK : ∀ p ≠ r, IsZero (K.homology p))
    {o : K.homology r} (ho : Function.Bijective (LinearMap.toSpanSingleton R _ o)) (q n : ℕ)
    (h : r + q = n) :
    Function.Bijective fun x : L.homology q ↦ homologyCross K L r q n h (o ⊗ₜ x) := by
  let e : R ≃ₗ[R] K.homology r := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ o) ho
  have (p : ℕ) : Module.Projective R (K.homology p) := by
    by_cases hp : p = r
    · subst hp
      exact .of_equiv e
    · have := ModuleCat.subsingleton_of_isZero (hK p hp)
      infer_instance
  -- Only the summand `H_r(K) ⊗ H_q(L)` of the Künneth sum in degree `n` is nonzero.
  have := GradedObject.Monoidal.isIso_ιTensorObj_of_isZero_left (fun p ↦ K.homology p)
    (fun q ↦ L.homology q) hK q n h
  have := isIso_homologyKunneth_of_projective K L n
  have hc : IsIso (homologyCross K L r q n h) := by
    rw [← ι_homologyKunneth]
    infer_instance
  refine ((ConcreteCategory.isIso_iff_bijective _).1 hc).comp ?_
  -- `x ↦ o ⊗ x` is `x ↦ 1 ⊗ x ↦ e 1 ⊗ x`, a composite of linear equivalences.
  convert ((TensorProduct.lid R (L.homology q)).symm.trans
    (TensorProduct.congr e (LinearEquiv.refl R _))).bijective using 1
  ext x
  -- `e 1 = 1 • o` by definition of `e`.
  exact congrArg (· ⊗ₜ[R] x) (one_smul R o).symm

end HomologicalComplex
