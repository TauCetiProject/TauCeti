/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.LinearAlgebra.Determinant.Projective
public import TauCeti.LinearAlgebra.End.Aeval
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import TauCeti.LinearAlgebra.Trace.Projective
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.BaseChange
-- `baseChangeTowerAlgEquiv` and its comparison with `rTensor` are used only in the proof of
-- `AlgHom.projectiveCharpolyRev_lmul_rTensor`.
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# The reversed characteristic polynomial on a finite projective module

For an endomorphism `f` of a finite projective module `M` over a commutative ring `R`, this file
defines the reversed characteristic polynomial

  `LinearMap.projectiveCharpolyRev f = det (1 - X f) ∈ R[X]`,

the determinant `LinearMap.projectiveDet` of `1 - X f` on `R[X] ⊗[R] M`. On a free module of
finite rank it is the reverse of `LinearMap.charpoly f`. Its constant coefficient is `1`, while
its degree is only bounded by the ranks of `M` at the points of `Spec R`, which need not be
constant. For the same reason `det (X - f)` need not be monic, and the reversed form is the one
used here.

If `π : R ^ n → M` and `σ : M → R ^ n` split `M` off a free module, then
`projectiveCharpolyRev f` is the reversed characteristic polynomial of the matrix of `σ ∘ f ∘ π`
(`LinearMap.projectiveCharpolyRev_eq_charpolyRev_toMatrix`). Through this description:

* its value at `t` is the determinant of `1 - t f` (`LinearMap.eval_projectiveCharpolyRev`), so
  its value at `0` is `1` (`LinearMap.eval_zero_projectiveCharpolyRev`), and
  its coefficient in degree one is minus the trace `LinearMap.projectiveTrace` of `f`
  (`LinearMap.coeff_projectiveCharpolyRev_one`);
* it commutes with base change (`LinearMap.projectiveCharpolyRev_baseChange`);
* its degree is at most any bound for the ranks of `M` at the points of `Spec R`
  (`LinearMap.natDegree_projectiveCharpolyRev_le`); on a free module its coefficient in degree
  `finrank R M` is `(-1) ^ finrank R M * det f`, so the degree is the rank exactly when
  `det f ≠ 0`, in particular when `f` is invertible
  (`LinearMap.natDegree_projectiveCharpolyRev_eq_finrank_iff`);
* it is transported along semilinear isomorphisms
  (`LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq`);
* **Cayley–Hamilton**: for some `n` bounding its degree, the reflection `X ^ n · Q(1/X)` of
  `Q = projectiveCharpolyRev f` is a monic polynomial killing `f`
  (`LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero`,
  `LinearMap.monic_reflect_projectiveCharpolyRev`); when the rank of `M` on `Spec R` is bounded by
  `d`, the reflection at `d` itself kills `f`
  (`LinearMap.aeval_reflect_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le`,
  `LinearMap.aeval_reverse_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le`).

The last statement turns a norm into an integral equation: an element of a finite projective
`R`-algebra is a root of a monic polynomial whose coefficients are those of the reversed
characteristic polynomial of multiplication by it. This is how integrality over rings of
invariants is proved for finite locally free group actions and equivalence relations.

For multiplication in a finite projective algebra, the reversed characteristic polynomial is
invariant under algebra isomorphisms (`AlgEquiv.projectiveCharpolyRev_lmul`) and commutes with
maps of the scalar algebra of a scalar extension (`AlgHom.projectiveCharpolyRev_lmul_rTensor`).
If its coefficients for `t f` are equalized by `algebraMap A B` and an injective `t : A →+* B`,
then `f` is integral over that equalizer
(`RingHom.isIntegral_of_coeff_projectiveCharpolyRev_mem_eqLocus`).

## Main definitions

* `LinearMap.projectiveCharpolyRev`: the reversed characteristic polynomial `det (1 - X f)`.

## References

* O. Goldman, *Determinants in projective modules*, Nagoya Math. J. **18** (1961), 27–36.
* The Stacks Project, Tag 03BK.
-/

public section

open Polynomial Module

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]

/-- The **reversed characteristic polynomial** `det (1 - X f)` of an endomorphism `f` of a finite
projective module: the determinant `LinearMap.projectiveDet` of `1 - X f` on `R[X] ⊗[R] M`. On a
free module of finite rank it is the reverse of `LinearMap.charpoly f`
(`projectiveCharpolyRev_eq_reverse_charpoly`). -/
noncomputable def projectiveCharpolyRev (f : Module.End R M) : R[X] :=
  projectiveDet (1 - (X : R[X]) • f.baseChange R[X])

/-- The reversed characteristic polynomial is the determinant `LinearMap.projectiveDet` of
`1 - X f` on `R[X] ⊗[R] M`. -/
theorem projectiveCharpolyRev_def (f : Module.End R M) :
    projectiveCharpolyRev f = projectiveDet (1 - (X : R[X]) • f.baseChange R[X]) :=
  (rfl)

/-- If `π : F → M` and `σ : M → F` split `M` off a free module `F` with basis `b`, the reversed
characteristic polynomial of `f` is that of the matrix of `σ ∘ f ∘ π` in `b`. -/
theorem projectiveCharpolyRev_eq_charpolyRev_toMatrix {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup F] [Module R F] (b : Basis ι R F) (π : F →ₗ[R] M) (σ : M →ₗ[R] F)
    (h : π ∘ₗ σ = id) (f : Module.End R M) :
    projectiveCharpolyRev f = (toMatrix b b (σ ∘ₗ f ∘ₗ π)).charpolyRev := by
  have : Module.Free R F := .of_basis b
  have : Module.Finite R F := .of_basis b
  have hX : π.baseChange R[X] ∘ₗ σ.baseChange R[X] = id := by
    rw [← baseChange_comp, h, baseChange_id]
  rw [projectiveCharpolyRev, projectiveDet_eq_det_of_comp_eq_id _ _ hX,
    ← splitEnd_apply _ _ hX, splitEnd_one_sub, smul_comp, comp_smul,
    ← baseChange_comp, ← baseChange_comp, ← det_toMatrix (Algebra.TensorProduct.basis R[X] b),
    Matrix.charpolyRev]
  congr 1
  let b' := Algebra.TensorProduct.basis R[X] b
  rw [Module.End.one_eq_id,
    map_sub (toMatrix b' b') id ((X : R[X]) • (σ ∘ₗ f ∘ₗ π).baseChange R[X]), map_smul,
    toMatrix_baseChange, toMatrix_id, Polynomial.algebraMap_eq]

/-- If `M` has a finite basis `b`, the reversed characteristic polynomial of `f` is that of its
matrix in `b`. -/
theorem projectiveCharpolyRev_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (f : Module.End R M) :
    projectiveCharpolyRev f = (toMatrix b b f).charpolyRev := by
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix b id id (id_comp _), id_comp, comp_id]

/-- On a free module of finite rank, the reversed characteristic polynomial is the reverse of the
characteristic polynomial. -/
theorem projectiveCharpolyRev_eq_reverse_charpoly [Module.Free R M] (f : Module.End R M) :
    projectiveCharpolyRev f = f.charpoly.reverse := by
  rw [projectiveCharpolyRev_eq_charpolyRev (Module.Free.chooseBasis R M), ← Matrix.reverse_charpoly,
    charpoly_toMatrix]

/-- The constant coefficient of the reversed characteristic polynomial is `1`. -/
@[simp]
theorem coeff_projectiveCharpolyRev_zero (f : Module.End R M) :
    (projectiveCharpolyRev f).coeff 0 = 1 := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-- The value at `t` of the reversed characteristic polynomial `det (1 - X f)` is the
determinant of `1 - t f`. -/
theorem eval_projectiveCharpolyRev (f : Module.End R M) (t : R) :
    (projectiveCharpolyRev f).eval t = projectiveDet (1 - t • f) := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hσ : σ ∘ₗ (1 - t • f) ∘ₗ π + (1 - σ ∘ₗ π) = 1 - t • σ ∘ₗ f ∘ₗ π := by
    ext x
    simp
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    Matrix.eval_charpolyRev_eq_det_one_sub_smul, projectiveDet_eq_det_of_comp_eq_id π σ h, hσ,
    ← det_toMatrix (Pi.basisFun R (Fin n)), map_sub, map_smul, toMatrix_one]

/-- The value at `0` of the reversed characteristic polynomial is `1`. -/
@[simp]
theorem eval_zero_projectiveCharpolyRev (f : Module.End R M) :
    (projectiveCharpolyRev f).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_projectiveCharpolyRev_zero]

/-- The value at `1` of the reversed characteristic polynomial `det (1 - X f)` is the determinant
of `1 - f`. -/
@[simp]
theorem eval_one_projectiveCharpolyRev (f : Module.End R M) :
    (projectiveCharpolyRev f).eval 1 = projectiveDet (1 - f) := by
  rw [eval_projectiveCharpolyRev, one_smul]

/-- The coefficient of `det (1 - X f)` in degree one is minus the trace of `f`. -/
@[simp]
theorem coeff_projectiveCharpolyRev_one (f : Module.End R M) :
    (projectiveCharpolyRev f).coeff 1 = -projectiveTrace R M f := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    Matrix.coeff_charpolyRev_eq_neg_trace, ← trace_eq_matrix_trace, ← projectiveTrace_eq_trace,
    ← comp_assoc, projectiveTrace_cyclic, ← comp_assoc, h, id_comp]

/-- The reversed characteristic polynomial commutes with base change. -/
@[simp]
theorem projectiveCharpolyRev_baseChange (A : Type*) [CommRing A] [Algebra R A]
    (f : Module.End R M) :
    projectiveCharpolyRev (f.baseChange A) = (projectiveCharpolyRev f).map (algebraMap R A) := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hA : π.baseChange A ∘ₗ σ.baseChange A = id := by
    rw [← baseChange_comp, h, baseChange_id]
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix
      (Algebra.TensorProduct.basis A (Pi.basisFun R (Fin n))) _ _ hA,
    projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    ← Matrix.charpolyRev_map, ← toMatrix_baseChange, baseChange_comp, baseChange_comp]

open scoped TensorProduct in
/-- The degree of the reversed characteristic polynomial is at most any bound for the ranks of
`M` at the points of `Spec R`. -/
theorem natDegree_projectiveCharpolyRev_le {n : ℕ} (hn : ∀ p, rankAtStalk (R := R) M p ≤ n)
    (f : Module.End R M) : (projectiveCharpolyRev f).natDegree ≤ n := by
  -- a coefficient of degree above `n` vanishes at every localisation `A` at a maximal ideal,
  -- where `A ⊗[R] M` is free of rank at most `n`
  refine natDegree_le_iff_coeff_eq_zero.2 fun k hk ↦ eq_zero_of_localization _ fun J hJ ↦ ?_
  let A := Localization.AtPrime J
  have : Module.Free A (A ⊗[R] M) := free_of_flat_of_isLocalRing
  have hdeg : (projectiveCharpolyRev (f.baseChange A)).natDegree ≤ finrank A (A ⊗[R] M) := by
    rw [projectiveCharpolyRev_eq_reverse_charpoly]
    exact (reverse_natDegree_le _).trans (charpoly_natDegree _).le
  have hr := hn ⟨J, hJ.isPrime⟩
  rw [rankAtStalk_eq_finrank_tensorProduct] at hr
  rw [projectiveCharpolyRev_baseChange] at hdeg
  rw [← coeff_map]
  exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (hr.trans_lt hk))

/-- On a free module, the coefficient of `det (1 - X f)` in degree `finrank R M` is
`(-1) ^ finrank R M` times the determinant of `f`. -/
theorem coeff_projectiveCharpolyRev_finrank [Module.Free R M] (f : Module.End R M) :
    (projectiveCharpolyRev f).coeff (finrank R M) = (-1) ^ finrank R M * LinearMap.det f := by
  nontriviality R
  rw [projectiveCharpolyRev_eq_charpolyRev (Module.Free.chooseBasis R M),
    Module.finrank_eq_card_chooseBasisIndex, Matrix.coeff_charpolyRev_card, det_toMatrix]

/-- On a free module, the degree of `det (1 - X f)` is at most the rank. -/
theorem natDegree_projectiveCharpolyRev_le_finrank [Module.Free R M] (f : Module.End R M) :
    (projectiveCharpolyRev f).natDegree ≤ finrank R M := by
  nontriviality R
  rw [projectiveCharpolyRev_eq_charpolyRev (Module.Free.chooseBasis R M),
    Module.finrank_eq_card_chooseBasisIndex]
  exact Matrix.natDegree_charpolyRev_le _

/-- On a free module over a nontrivial ring, the degree of `det (1 - X f)` equals the rank
exactly when the determinant of `f` is nonzero. -/
theorem natDegree_projectiveCharpolyRev_eq_finrank_iff [Nontrivial R] [Module.Free R M]
    (f : Module.End R M) :
    (projectiveCharpolyRev f).natDegree = finrank R M ↔ LinearMap.det f ≠ 0 := by
  have hc := coeff_projectiveCharpolyRev_finrank f
  have hunit : IsUnit ((-1 : R) ^ finrank R M) := isUnit_neg_one.pow _
  refine ⟨fun h hdet ↦ ?_, fun hdet ↦ (natDegree_projectiveCharpolyRev_le_finrank f).antisymm
    (le_natDegree_of_ne_zero ?_)⟩
  · -- a vanishing leading coefficient would make the polynomial zero, but its constant term is `1`
    have hlead : (projectiveCharpolyRev f).leadingCoeff = 0 := by
      rw [leadingCoeff, h, hc, hdet, mul_zero]
    simpa [leadingCoeff_eq_zero.1 hlead] using coeff_projectiveCharpolyRev_zero f
  · rwa [hc, Ne, hunit.mul_right_eq_zero]

/-- On a free module over a nontrivial ring, the degree of `det (1 - X f)` is the rank when `f`
is invertible. -/
theorem natDegree_projectiveCharpolyRev_eq_finrank_of_isUnit [Nontrivial R] [Module.Free R M]
    {f : Module.End R M} (hf : IsUnit f) :
    (projectiveCharpolyRev f).natDegree = finrank R M :=
  (natDegree_projectiveCharpolyRev_eq_finrank_iff f).2 ((isUnit_iff_isUnit_det f).1 hf).ne_zero

/-- **Transport along a semilinear isomorphism.** If a `θ`-semilinear isomorphism `e : M ≃ M'`
over a ring isomorphism `θ : R ≃ R'` carries `f` to `g`, that is `g ∘ e = e ∘ f`, then the
reversed characteristic polynomial of `g` is that of `f` with `θ` applied to its coefficients. -/
theorem projectiveCharpolyRev_eq_map_of_comp_eq {R' M' : Type*} [CommRing R'] [AddCommGroup M']
    [Module R' M'] [Module.Finite R' M'] [Module.Projective R' M'] {θ : R →+* R'} {θ' : R' →+* R}
    [RingHomInvPair θ θ'] [RingHomInvPair θ' θ] (e : M ≃ₛₗ[θ] M') {f : Module.End R M}
    {g : Module.End R' M'} (hfg : ∀ x, g (e x) = e (f x)) :
    projectiveCharpolyRev g = (projectiveCharpolyRev f).map θ := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hx (x : M) : π (σ x) = x := congr($h x)
  -- the coordinatewise transport of the splitting `(π, σ)` of `M` to a splitting of `M'`
  let π' : (Fin n → R') →ₗ[R'] M' :=
    { toFun v := e (π fun i ↦ θ' (v i))
      map_add' v w := by simp [← map_add, Pi.add_def]
      map_smul' c v := by
        rw [RingHom.id_apply, ← RingHomInvPair.comp_apply_eq₂ (σ := θ) (σ' := θ') (x := c),
          ← e.map_smulₛₗ, ← π.map_smul]
        congr 2
        ext i
        simp }
  let σ' : M' →ₗ[R'] Fin n → R' :=
    { toFun x i := θ (σ (e.symm x) i)
      map_add' x y := by ext i; simp
      map_smul' c x := by
        ext i
        simp [e.symm.map_smulₛₗ] }
  have h' : π' ∘ₗ σ' = id := by
    ext x
    simp [π', σ', hx]
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R' (Fin n)) π' σ' h',
    projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    ← Matrix.charpolyRev_map]
  congr 1
  ext i j
  have hsingle : (fun k ↦ θ' ((Pi.single j 1 : Fin n → R') k)) = (Pi.single j 1 : Fin n → R) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  simp [toMatrix_eq_toMatrix', toMatrix'_apply, π', σ', hsingle, hfg]

/-- **Cayley–Hamilton on a finite projective module.** For some `n` bounding the degree of the
reversed characteristic polynomial `Q` of `f`, the reflection `X ^ n · Q(1/X)` of `Q` kills `f`;
it is monic (`monic_reflect_projectiveCharpolyRev`). -/
theorem exists_aeval_reflect_projectiveCharpolyRev_eq_zero (f : Module.End R M) :
    ∃ n, (projectiveCharpolyRev f).natDegree ≤ n ∧
      aeval f ((projectiveCharpolyRev f).reflect n) = 0 := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton M := Module.subsingleton R M
    refine ⟨n, ?_, Subsingleton.elim _ _⟩
    rw [Subsingleton.elim (projectiveCharpolyRev f) 0, natDegree_zero]
    exact n.zero_le
  have hx (x : M) : π (σ x) = x := congr($h x)
  let g := σ ∘ₗ f ∘ₗ π
  have hg : g ∘ₗ σ = σ ∘ₗ f := by
    ext x
    simp [g, hx]
  rw [projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun R (Fin n)) π σ h,
    ← Matrix.reverse_charpoly, charpoly_toMatrix]
  have hdeg : g.charpoly.natDegree = n := by
    rw [charpoly_natDegree, Module.finrank_fin_fun]
  refine ⟨n, (reverse_natDegree_le _).trans hdeg.le, ?_⟩
  -- the reflection of the reverse of the characteristic polynomial of `g` is that polynomial
  rw [reverse, hdeg, reflect_reflect]
  have hgσ := congr(π ∘ₗ $(Module.End.aeval_comp_of_comp_eq hg g.charpoly))
  rw [aeval_self_charpoly, zero_comp, comp_zero, ← comp_assoc, h, id_comp] at hgσ
  exact hgσ.symm

/-- The reflection `X ^ n · Q(1/X)` of the reversed characteristic polynomial `Q` of `f` is monic
whenever `n` bounds the degree of `Q`. -/
theorem monic_reflect_projectiveCharpolyRev (f : Module.End R M) {n : ℕ}
    (hn : (projectiveCharpolyRev f).natDegree ≤ n) :
    ((projectiveCharpolyRev f).reflect n).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one n (natDegree_reflect_le.trans (max_le le_rfl hn)) ?_
  rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_projectiveCharpolyRev_zero]

open scoped TensorProduct in
/-- **Cayley–Hamilton on a finite projective module of bounded rank.** If `M` has rank at most `d`
at every point of `Spec R`, the reflection `X ^ d · Q(1/X)` at `d` of
`Q = projectiveCharpolyRev f` kills `f`. -/
theorem aeval_reflect_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le {d : ℕ}
    (hd : ∀ p, rankAtStalk (R := R) M p ≤ d) (f : Module.End R M) :
    aeval f ((projectiveCharpolyRev f).reflect d) = 0 := by
  ext x
  refine Module.eq_zero_of_localization_maximal (fun P _ ↦ Localization.AtPrime P ⊗[R] M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) M 1) _ fun P hP ↦ ?_
  let A := Localization.AtPrime P
  have : Module.Free A (A ⊗[R] M) := free_of_flat_of_isLocalRing
  have hfin : finrank A (A ⊗[R] M) ≤ d := by
    rw [← rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨P, hP.isPrime⟩]
    exact hd ⟨P, hP.isPrime⟩
  -- Over the local ring `A`, `A ⊗[R] M` is free of rank `r ≤ d`, so reflecting `Q_A` at `d` gives
  -- `X ^ (d - r)` times the ordinary characteristic polynomial of `f.baseChange A`.
  have hpoly : ((projectiveCharpolyRev f).reflect d).map (algebraMap R A) =
      X ^ (d - finrank A (A ⊗[R] M)) * (f.baseChange A).charpoly := by
    rw [← reflect_map, ← projectiveCharpolyRev_baseChange,
      projectiveCharpolyRev_eq_reverse_charpoly]
    have hdeg : (f.baseChange A).charpoly.reverse.natDegree ≤ finrank A (A ⊗[R] M) :=
      (reverse_natDegree_le _).trans (charpoly_natDegree _).le
    calc (f.baseChange A).charpoly.reverse.reflect d
        = ((1 : A[X]) * (f.baseChange A).charpoly.reverse).reflect
            ((d - finrank A (A ⊗[R] M)) + finrank A (A ⊗[R] M)) := by
          rw [one_mul, Nat.sub_add_cancel hfin]
      _ = (1 : A[X]).reflect (d - finrank A (A ⊗[R] M)) *
            (f.baseChange A).charpoly.reverse.reflect (finrank A (A ⊗[R] M)) :=
          reflect_mul 1 _ (by simp) hdeg
      _ = X ^ (d - finrank A (A ⊗[R] M)) * (f.baseChange A).charpoly := by
          rw [← C_1, reflect_C, C_1, one_mul, reverse, charpoly_natDegree, reflect_reflect]
  have hbase : (aeval f ((projectiveCharpolyRev f).reflect d)).baseChange A = 0 := by
    have hmap : (aeval f ((projectiveCharpolyRev f).reflect d)).baseChange A =
        aeval (f.baseChange A) ((projectiveCharpolyRev f).reflect d) :=
      (aeval_algHom_apply (Module.End.baseChangeHom R A M) f _).symm
    rw [hmap,
      aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R A (Module.End A (A ⊗[R] M))).symm,
      hpoly, map_mul, aeval_self_charpoly, mul_zero]
  rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, hbase, LinearMap.zero_apply]

/-- If `M` has rank at most `(projectiveCharpolyRev f).natDegree` at every point of `Spec R`, the
reversal `(projectiveCharpolyRev f).reverse` kills `f`. -/
theorem aeval_reverse_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le {f : Module.End R M}
    (hd : ∀ p, rankAtStalk (R := R) M p ≤ (projectiveCharpolyRev f).natDegree) :
    aeval f (projectiveCharpolyRev f).reverse = 0 :=
  aeval_reflect_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le hd f

end LinearMap

open scoped TensorProduct

namespace AlgEquiv

variable {R S T : Type*} [CommRing R] [Ring S] [Ring T] [Algebra R S] [Algebra R T]
  [Module.Finite R S] [Module.Projective R S] [Module.Finite R T] [Module.Projective R T]

/-- The reversed characteristic polynomial of multiplication is invariant under an algebra
isomorphism of finite projective algebras. -/
theorem projectiveCharpolyRev_lmul (e : S ≃ₐ[R] T) (x : S) :
    LinearMap.projectiveCharpolyRev (Algebra.lmul R T (e x)) =
      LinearMap.projectiveCharpolyRev (Algebra.lmul R S x) := by
  simpa using LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq e.toLinearEquiv
    (f := Algebra.lmul R S x) (g := Algebra.lmul R T (e x)) (fun y ↦ by simp)

end AlgEquiv

namespace AlgHom

variable {R S A A' : Type*} [CommRing R] [Ring S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S] [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A']

/-- The reversed characteristic polynomial of multiplication on a scalar extension commutes
with an arbitrary map of the scalar algebra. The norm analogue is
`Algebra.projectiveNorm_rTensor`. It is stated with `LinearMap.mul`, the simp normal form of
`Algebra.lmul`. -/
@[simp]
theorem projectiveCharpolyRev_lmul_rTensor (φ : A →ₐ[R] A') (x : A ⊗[R] S) :
    LinearMap.projectiveCharpolyRev
        (LinearMap.mul A' (A' ⊗[R] S) (Algebra.TensorProduct.rTensor S φ x)) =
      (LinearMap.projectiveCharpolyRev (LinearMap.mul A (A ⊗[R] S) x)).map φ := by
  rw [← Algebra.coe_lmul_eq_mul, ← Algebra.coe_lmul_eq_mul]
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R A A' := .of_algHom φ
  have hφ : IsScalarTower.toAlgHom R A A' = φ := AlgHom.ext fun a ↦ by
    rw [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
  -- `A' ⊗[R] S` is the base change of `A ⊗[R] S` along `φ`
  rw [← AlgEquiv.projectiveCharpolyRev_lmul
      (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R A S A').symm,
    ← hφ, Algebra.TensorProduct.baseChangeTowerAlgEquiv_symm_rTensor,
    ← Algebra.baseChange_lmul, LinearMap.projectiveCharpolyRev_baseChange,
    IsScalarTower.coe_toAlgHom]

end AlgHom

namespace RingHom

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B]

/-- **Integrality from invariant characteristic coefficients.** Let `B` be a finite projective
`A`-algebra and `t : A →+* B` an injective ring homomorphism. If the coefficients of the reversed
characteristic polynomial of multiplication by `t f` on `B` lie in the equalizer
`{a : algebraMap A B a = t a}`, then `f` is integral over that equalizer: by Cayley–Hamilton, a
monic reflection of this polynomial has invariant coefficients and kills `f`. -/
theorem isIntegral_of_coeff_projectiveCharpolyRev_mem_eqLocus (t : A →+* B)
    (ht : Function.Injective t) (f : A)
    (hf : ∀ i, (LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t f))).coeff i ∈
      (algebraMap A B).eqLocus t) :
    _root_.IsIntegral ((algebraMap A B).eqLocus t) f := by
  set Q := LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t f))
  -- by Cayley–Hamilton, a monic reflection `p = Q.reflect n` of `Q` kills `t f`
  obtain ⟨n, hn, hQn⟩ :=
    LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero (Algebra.lmul A B (t f))
  have h1 : aeval (t f) (Q.reflect n) = 0 := by
    have h1 := congr($hQn 1)
    rw [Polynomial.aeval_algHom_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]
      at h1
    exact h1
  -- the coefficients of `p` are invariants
  have hS : ((Q.reflect n).coeffs : Set A) ⊆ (algebraMap A B).eqLocus t := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.mp hc
    rw [coeff_reflect]
    exact hf _
  -- so `t (p f) = p (t f) = 0`, and `p f = 0` since `t` is injective
  have hp : (Q.reflect n).map t = (Q.reflect n).map (algebraMap A B) := by
    ext i
    rw [coeff_map, coeff_map, coeff_reflect]
    exact (mem_eqLocus.mp (hf _)).symm
  have h2 : eval f (Q.reflect n) = 0 := by
    apply ht
    rw [map_zero, ← h1, aeval_def, ← eval_map, ← hp, eval_map, eval₂_at_apply]
  refine ⟨(Q.reflect n).toSubring _ hS,
    (monic_toSubring _ _ _).mpr (LinearMap.monic_reflect_projectiveCharpolyRev _ hn), ?_⟩
  rw [← eval_map]
  convert h2
  exact map_toSubring _ _ _

end RingHom
