/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Basic

import TauCeti.Algebra.MvPolynomial.AevalConstX
import TauCeti.LinearAlgebra.End.ScalarExtension

/-!
# Homogeneous polynomial laws

A polynomial law `f : M →ₚₗ[R] N` is *homogeneous of degree `n`* if
`f (s • x) = s ^ n • f x` for every commutative `R`-algebra `S`, every `s : S` and every
`x : S ⊗[R] M`. The condition is imposed after every scalar extension, not only on `M` itself:
over a finite field `𝔽_q` the identity law satisfies `s • m = s ^ q • m` for all `s ∈ 𝔽_q` and
`m ∈ M`, yet it is not homogeneous of degree `q`, as `T • x ≠ T ^ q • x` over `𝔽_q[T]` for
nonzero `x`.

Homogeneous laws of degree `d` are the objects represented by the degree-`d` divided powers
`Γ^d_R(M)` (Roby), and the degree-one laws are exactly the base changes of linear maps.

## Main declarations

* `PolynomialLaw.IsHomogeneousOfDegree n f`: the law `f` is homogeneous of degree `n`.
* `PolynomialLaw.IsHomogeneousOfDegree.toFun_smul`: homogeneity holds after scalar extension to
  algebras in every universe.
* `PolynomialLaw.homogeneousSubmodule R M N n`: the submodule of laws homogeneous of degree `n`;
  in particular the zero law is homogeneous of every degree.
* `PolynomialLaw.IsHomogeneousOfDegree.comp`: composing laws of degrees `p` and `q` gives a law
  of degree `p * q`.
* `PolynomialLaw.IsHomogeneousOfDegree.toFun'_add`, `PolynomialLaw.IsHomogeneousOfDegree.toFun_add`:
  a law homogeneous of degree one is additive after every scalar extension.
* `PolynomialLaw.IsHomogeneousOfDegree.toLinearMap`: the ground map of a law homogeneous of degree
  one, as a linear map, whose polynomial law is the original law.
* `LinearMap.toLinearMap_isHomogeneousOfDegree_toPolynomialLaw`: conversely, the linear map
  recovered from `u.toPolynomialLaw` is `u`.
* `PolynomialLaw.isHomogeneousOfDegree_one_iff`: a law is homogeneous of degree one if and only
  if it is the polynomial law `u.toPolynomialLaw` of a linear map `u`.
* `PolynomialLaw.range_toPolynomialLawₗ`, `PolynomialLaw.homogeneousSubmoduleOneEquiv`: the
  laws homogeneous of degree one are the image of `LinearMap.toPolynomialLawₗ`, which identifies
  `M →ₗ[R] N` with `homogeneousSubmodule R M N 1`.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*, Ann. Sci. École Norm.
  Sup. (3) 80 (1963), 213-348
* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.1](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

open scoped Polynomial

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- A polynomial law `f : M →ₚₗ[R] N` is homogeneous of degree `n` if
`f (s • x) = s ^ n • f x` for every commutative `R`-algebra `S`, every `s : S` and every
`x : S ⊗[R] M`. See `IsHomogeneousOfDegree.toFun_smul` for algebras in other universes. -/
def IsHomogeneousOfDegree (n : ℕ) (f : M →ₚₗ[R] N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S) (x : S ⊗[R] M),
    f.toFun' S (s • x) = s ^ n • f.toFun' S x

theorem isHomogeneousOfDegree_iff {n : ℕ} {f : M →ₚₗ[R] N} :
    f.IsHomogeneousOfDegree n ↔ ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S)
      (x : S ⊗[R] M), f.toFun' S (s • x) = s ^ n • f.toFun' S x :=
  Iff.rfl

namespace IsHomogeneousOfDegree

variable {n : ℕ} {f : M →ₚₗ[R] N}

theorem toFun'_smul (hf : f.IsHomogeneousOfDegree n) {S : Type u} [CommSemiring S]
    [Algebra R S] (s : S) (x : S ⊗[R] M) : f.toFun' S (s • x) = s ^ n • f.toFun' S x :=
  hf S s x

/-- Homogeneity of a polynomial law holds after scalar extension to a commutative `R`-algebra in
an arbitrary universe. -/
theorem toFun_smul (hf : f.IsHomogeneousOfDegree n) {S : Type*} [CommSemiring S] [Algebra R S]
    (s : S) (x : S ⊗[R] M) : f.toFun S (s • x) = s ^ n • f.toFun S x := by
  obtain ⟨k, ψ, p, q, rfl, rfl⟩ := exists_lift' x s
  rw [← AlgHom.rTensor_toLinearMap_apply_smul, ← isCompat_apply, ← toFun'_eq_toFun, hf.toFun'_smul,
    AlgHom.rTensor_toLinearMap_apply_smul, map_pow, toFun'_eq_toFun, isCompat_apply]

/-- The ground map of a law homogeneous of degree `n` is homogeneous of degree `n`. -/
theorem ground_smul (hf : f.IsHomogeneousOfDegree n) (r : R) (m : M) :
    f.ground (r • m) = r ^ n • f.ground m := by
  rw [ground_apply, ground_apply, tmul_smul, hf.toFun'_smul, map_smul]

theorem add {g : M →ₚₗ[R] N} (hf : f.IsHomogeneousOfDegree n) (hg : g.IsHomogeneousOfDegree n) :
    (f + g).IsHomogeneousOfDegree n := fun S _ _ s x ↦ by
  simp only [add_def, Pi.add_apply, hf.toFun'_smul, hg.toFun'_smul, smul_add]

theorem smul (hf : f.IsHomogeneousOfDegree n) (r : R) : (r • f).IsHomogeneousOfDegree n :=
  fun S _ _ s x ↦ by simp only [smul_def, Pi.smul_apply, hf.toFun'_smul, smul_comm r]

/-- Composing a law homogeneous of degree `q` with one homogeneous of degree `p` gives a law
homogeneous of degree `p * q`. -/
theorem comp {g : N →ₚₗ[R] P} {p q : ℕ} (hg : g.IsHomogeneousOfDegree q)
    (hf : f.IsHomogeneousOfDegree p) : (g.comp f).IsHomogeneousOfDegree (p * q) :=
  fun S _ _ s x ↦ by
    simp only [comp_toFun', Function.comp_apply, hf.toFun'_smul, hg.toFun'_smul, pow_mul]

end IsHomogeneousOfDegree

/-- The zero law is homogeneous of every degree. -/
theorem isHomogeneousOfDegree_zero (n : ℕ) : (0 : M →ₚₗ[R] N).IsHomogeneousOfDegree n :=
  fun S _ _ s x ↦ by simp only [zero_def, Pi.zero_apply, smul_zero]

theorem isHomogeneousOfDegree_id : (id : M →ₚₗ[R] M).IsHomogeneousOfDegree 1 :=
  fun S _ _ s x ↦ by simp only [id_apply', id_eq, pow_one]

variable (R M N) in
/-- The submodule of polynomial laws `M →ₚₗ[R] N` which are homogeneous of degree `n`. -/
def homogeneousSubmodule (n : ℕ) : Submodule R (M →ₚₗ[R] N) where
  carrier := {f | f.IsHomogeneousOfDegree n}
  add_mem' := IsHomogeneousOfDegree.add
  zero_mem' := isHomogeneousOfDegree_zero n
  smul_mem' r _ hf := hf.smul r

@[simp]
theorem mem_homogeneousSubmodule {n : ℕ} {f : M →ₚₗ[R] N} :
    f ∈ homogeneousSubmodule R M N n ↔ f.IsHomogeneousOfDegree n :=
  Iff.rfl

end PolynomialLaw

/-- The polynomial law of a linear map is homogeneous of degree one. -/
theorem LinearMap.isHomogeneousOfDegree_toPolynomialLaw {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (u : M →ₗ[R] N) : u.toPolynomialLaw.IsHomogeneousOfDegree 1 := fun S _ _ s x ↦ by
  simp only [toPolynomialLaw_toFun', map_smul, pow_one]

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

namespace IsHomogeneousOfDegree

variable {f : M →ₚₗ[R] N}

/-- A polynomial law homogeneous of degree one is additive after every scalar extension. -/
theorem toFun'_add (hf : f.IsHomogeneousOfDegree 1) (S : Type u) [CommSemiring S] [Algebra R S]
    (x y : S ⊗[R] M) : f.toFun' S (x + y) = f.toFun' S x + f.toFun' S y := by
  -- Over `S[T₀, T₁]` put `w = f (T₀ • x + T₁ • y)`. For `a : Fin 2 → S`, substituting
  -- `Tᵢ ↦ aᵢ X` and taking the coefficient of `X` sends `w` to `f (a₀ • x + a₁ • y)`, by
  -- homogeneity in `X`. That coefficient is additive in `a`; compare `a = (1, 1)` with
  -- `(1, 0)` and `(0, 1)`.
  let ι : S →ₐ[R] MvPolynomial (Fin 2) S := IsScalarTower.toAlgHom R S _
  let j : S →ₐ[R] S[X] := IsScalarTower.toAlgHom R S _
  let z : MvPolynomial (Fin 2) S ⊗[R] M :=
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) S) • ι.toLinearMap.rTensor M x +
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) S) • ι.toLinearMap.rTensor M y
  let ψ (a : Fin 2 → S) : MvPolynomial (Fin 2) S →ₐ[R] S[X] :=
    (MvPolynomial.aeval fun i ↦ Polynomial.C (a i) * Polynomial.X).restrictScalars R
  let c : S[X] →ₗ[R] S := (Polynomial.lcoeff S 1).restrictScalars R
  have hψι (a : Fin 2 → S) : (ψ a).comp ι = j := AlgHom.ext fun s ↦ by
    simp [ψ, ι, j, Polynomial.C_eq_algebraMap]
  -- substituting `Tᵢ ↦ aᵢ X` and taking the coefficient of `X` recovers `f (a₀ • x + a₁ • y)`
  have key (a : Fin 2 → S) :
      (c ∘ₗ (ψ a).toLinearMap).rTensor N (f.toFun' _ z) = f.toFun' S (a 0 • x + a 1 • y) := by
    have hz : (ψ a).toLinearMap.rTensor M z =
        (Polynomial.X : S[X]) • j.toLinearMap.rTensor M (a 0 • x + a 1 • y) := by
      simp only [z, map_add, AlgHom.rTensor_toLinearMap_apply_smul, ← LinearMap.rTensor_comp_apply,
        ← AlgHom.comp_toLinearMap, hψι, smul_add, smul_smul]
      simp [ψ, j, Polynomial.C_eq_algebraMap, mul_comm]
    rw [LinearMap.rTensor_comp_apply, isCompat_apply', hz, hf.toFun'_smul, pow_one,
      ← isCompat_apply', TauCeti.rTensor_lcoeff_one_X_smul]
  -- the coefficient of `X` is additive in the substituted values
  have hsum : c ∘ₗ (ψ ![1, 1]).toLinearMap =
      c ∘ₗ (ψ ![1, 0]).toLinearMap + c ∘ₗ (ψ ![0, 1]).toLinearMap := by
    refine LinearMap.ext fun p ↦ ?_
    induction p using MvPolynomial.induction_on with
    | C s => simp [ψ, c]
    | add p q hp hq => simp_all only [LinearMap.add_apply, map_add]
    | mul_X p i _ =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, ψ, c,
        AlgHom.coe_restrictScalars', LinearMap.coe_restrictScalars, Polynomial.lcoeff_apply,
        MvPolynomial.coeff_one_aeval_C_mul_X_mul_X]
      fin_cases i <;> simp
  have h := key ![1, 1]
  rw [hsum, LinearMap.rTensor_add, LinearMap.add_apply, key, key] at h
  simpa using h.symm

/-- A polynomial law homogeneous of degree one sends `s ⊗ₜ m` to `s ⊗ₜ f.ground m`. -/
theorem toFun'_tmul (hf : f.IsHomogeneousOfDegree 1) {S : Type u} [CommSemiring S]
    [Algebra R S] (s : S) (m : M) : f.toFun' S (s ⊗ₜ[R] m) = s ⊗ₜ[R] f.ground m := by
  have h := hf.toFun'_smul s ((1 : S) ⊗ₜ[R] m)
  rwa [smul_tmul', smul_eq_mul, mul_one, pow_one, ← one_tmul_ground_apply', smul_tmul',
    smul_eq_mul, mul_one] at h

/-- The ground map of a polynomial law homogeneous of degree one, as a linear map. -/
def toLinearMap (hf : f.IsHomogeneousOfDegree 1) : M →ₗ[R] N where
  toFun := f.ground
  map_add' m m' := by
    rw [ground_apply, ground_apply, ground_apply, tmul_add, hf.toFun'_add, map_add]
  map_smul' r m := by simpa using hf.ground_smul r m

@[simp]
theorem coe_toLinearMap (hf : f.IsHomogeneousOfDegree 1) : ⇑hf.toLinearMap = f.ground :=
  (rfl)

/-- A polynomial law homogeneous of degree one is the polynomial law of its ground map. -/
@[simp]
theorem toPolynomialLaw_toLinearMap (hf : f.IsHomogeneousOfDegree 1) :
    hf.toLinearMap.toPolynomialLaw = f := by
  ext S _ _ x
  rw [LinearMap.toPolynomialLaw_toFun']
  induction x using TensorProduct.inductionOn with
  | tmul s m => rw [LinearMap.baseChange_tmul, hf.toFun'_tmul, coe_toLinearMap]
  | add x y hx hy => rw [map_add, hx, hy, hf.toFun'_add]

/-- A polynomial law homogeneous of degree one is additive after scalar extension to a
commutative `R`-algebra in an arbitrary universe. -/
theorem toFun_add (hf : f.IsHomogeneousOfDegree 1) (S : Type*) [CommSemiring S] [Algebra R S]
    (x y : S ⊗[R] M) : f.toFun S (x + y) = f.toFun S x + f.toFun S y := by
  rw [← hf.toPolynomialLaw_toLinearMap, LinearMap.toPolynomialLaw_toFun, map_add]

end IsHomogeneousOfDegree

/-- A polynomial law is homogeneous of degree one if and only if it is the polynomial law of a
linear map, namely of its ground map `IsHomogeneousOfDegree.toLinearMap`. -/
theorem isHomogeneousOfDegree_one_iff {f : M →ₚₗ[R] N} :
    f.IsHomogeneousOfDegree 1 ↔ ∃ u : M →ₗ[R] N, u.toPolynomialLaw = f :=
  ⟨fun hf ↦ ⟨hf.toLinearMap, hf.toPolynomialLaw_toLinearMap⟩,
    fun ⟨u, hu⟩ ↦ hu ▸ u.isHomogeneousOfDegree_toPolynomialLaw⟩

end PolynomialLaw

/-- The linear map recovered from the polynomial law of a linear map `u` is `u`. -/
@[simp]
theorem LinearMap.toLinearMap_isHomogeneousOfDegree_toPolynomialLaw {R : Type u}
    [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (u : M →ₗ[R] N) : u.isHomogeneousOfDegree_toPolynomialLaw.toLinearMap = u := by
  ext m
  simp

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable (R M N) in
/-- The polynomial laws homogeneous of degree one are exactly those of linear maps. -/
theorem range_toPolynomialLawₗ :
    LinearMap.range (LinearMap.toPolynomialLawₗ R M N) = homogeneousSubmodule R M N 1 := by
  ext f
  simp [isHomogeneousOfDegree_one_iff]

variable (R M N) in
/-- Linear maps `M →ₗ[R] N` are identified with polynomial laws homogeneous of degree one, by
`LinearMap.toPolynomialLaw` with inverse `IsHomogeneousOfDegree.toLinearMap`. -/
def homogeneousSubmoduleOneEquiv : (M →ₗ[R] N) ≃ₗ[R] homogeneousSubmodule R M N 1 where
  toFun u := ⟨u.toPolynomialLaw, u.isHomogeneousOfDegree_toPolynomialLaw⟩
  invFun f := (mem_homogeneousSubmodule.mp f.2).toLinearMap
  map_add' u v := Subtype.ext (LinearMap.toPolynomialLaw_add u v)
  map_smul' r u := Subtype.ext (LinearMap.toPolynomialLaw_smul r u)
  left_inv := LinearMap.toLinearMap_isHomogeneousOfDegree_toPolynomialLaw
  right_inv f := Subtype.ext (mem_homogeneousSubmodule.mp f.2).toPolynomialLaw_toLinearMap

@[simp]
theorem coe_homogeneousSubmoduleOneEquiv_apply (u : M →ₗ[R] N) :
    (homogeneousSubmoduleOneEquiv R M N u : M →ₚₗ[R] N) = u.toPolynomialLaw :=
  (rfl)

@[simp]
theorem homogeneousSubmoduleOneEquiv_symm_apply (f : homogeneousSubmodule R M N 1) :
    (homogeneousSubmoduleOneEquiv R M N).symm f = (mem_homogeneousSubmodule.mp f.2).toLinearMap :=
  (rfl)

end PolynomialLaw
