/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Defs
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic

/-!
# Maps out of a row-finite twisted free module

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A`, and let `(ℳ, dM)` be a differential graded left
module over the same differential graded algebra. A left-linear map `K_m → M` of degree zero is
determined by the images `c x ∈ ℳ (-ind x)` of the generators; it is
`Finsupp.linearCombination A c`. On the generators, its compatibility with the differentials is
the **generator equation**

`dM (c x) = ∑_y m x y • c y`

for every generator `x`: the differential of the image of `x` is the image of the differential
of `x`. A `RowFiniteTwistingCocycle.GeneratorMap` records such images. The DG
Leibniz rules of `K_m` and of `ℳ` extend the generator equation to the chain-map identity on all
of `K_m` (`RowFiniteTwistingCocycle.GeneratorMap.linearCombination_differential`).

This is the form in which a semi-free model built from cells is compared with a geometric chain
module: the comparison is specified on generators, and its compatibility with the differentials is
checked one generator at a time. Continuation maps between row-finite twisted modules are the
special case in which the target is another row-finite twisted module.

## Main definitions and results

* `RowFiniteTwistingCocycle.GeneratorMap`: generator images satisfying the generator equation.
* `RowFiniteTwistingCocycle.GeneratorMap.linearCombination_mem`: the induced map preserves degrees.
* `RowFiniteTwistingCocycle.GeneratorMap.linearCombination_differential`: the induced map
  commutes with the differentials.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. 69 (1959), 223–246.
* B. Keller, *Deriving DG categories*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}
  [AddCommGroup M] [Module R M] [Module A M]

namespace RowFiniteTwistingCocycle

/-- Images of the generators of the free module `K_m` in a graded module `ℳ` with an endomorphism
`dM`, of the degrees of the generators and satisfying the generator equation: the differential of
the image of a generator is the image of its differential row. They determine the left-linear
map `Finsupp.linearCombination A image : K_m → M`, which commutes with the differentials when
`(ℳ, dM)` is a differential graded left module. -/
structure GeneratorMap (m : RowFiniteTwistingCocycle 𝒜 d P ind) (ℳ : ℤ → Submodule R M)
    (dM : M →ₗ[R] M) where
  /-- The image of each generator. -/
  image : P → M
  /-- The image of a generator of index `ind x` has cohomological degree `-ind x`. -/
  mem_graded : ∀ x, image x ∈ ℳ (-ind x)
  /-- The generator equation: the differential of an image is the image of the differential. -/
  differential_image : ∀ x, dM (image x) = Finsupp.linearCombination A image (m.m x)

namespace GeneratorMap

variable {m : RowFiniteTwistingCocycle 𝒜 d P ind} {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}

omit [GradedAlgebra 𝒜] in
@[ext]
theorem ext {f g : m.GeneratorMap ℳ dM} (h : ∀ x, f.image x = g.image x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

variable (f : m.GeneratorMap ℳ dM)

omit [GradedAlgebra 𝒜] in
/-- The induced map sends a vector of total degree `n` to an element of degree `n`. -/
theorem linearCombination_mem [SetLike.GradedSMul 𝒜 ℳ] {n : ℤ} {v : P →₀ A}
    (hv : v ∈ rowFiniteTotalGrading 𝒜 ind n) :
    Finsupp.linearCombination A f.image v ∈ ℳ n := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hv
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have := SetLike.GradedSMul.smul_mem (hv x) (f.mem_graded x)
  simpa only [vadd_eq_add, add_neg_cancel_right] using this

/-- **The generator equation extends to the whole free module.** The left-linear map determined
by the generator images commutes with the differentials, by the DG Leibniz rules of `K_m` and of
`ℳ`. -/
theorem linearCombination_differential [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] {hA : IsDGAlgebra 𝒜 d} (hM : IsDGLeftModule hA ℳ dM) (v : P →₀ A) :
    dM (Finsupp.linearCombination A f.image v) =
      Finsupp.linearCombination A f.image
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [Finsupp.linearCombination_single, hM.leibniz a.2,
        rowFiniteTwistedDifferential_single m.m x a.2, map_add,
        Finsupp.linearCombination_single, f.differential_image x]
      simp only [map_smul, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

end GeneratorMap

end RowFiniteTwistingCocycle

end TauCeti
