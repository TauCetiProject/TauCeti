/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.Polynomial.AlgebraMap
public import TauCeti.LinearAlgebra.Determinant.Projective
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

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

* it commutes with base change (`LinearMap.projectiveCharpolyRev_baseChange`);
* it is transported along semilinear isomorphisms
  (`LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq`);
* **Cayley–Hamilton**: for some `n` bounding its degree, the reflection `X ^ n · Q(1/X)` of
  `Q = projectiveCharpolyRev f` is a monic polynomial killing `f`
  (`LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero`,
  `LinearMap.monic_reflect_projectiveCharpolyRev`).

The last statement turns a norm into an integral equation: an element of a finite projective
`R`-algebra is a root of a monic polynomial whose coefficients are those of the reversed
characteristic polynomial of multiplication by it. This is how integrality over rings of
invariants is proved for finite locally free group actions and equivalence relations.

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
  have hgσ := congr(π ∘ₗ $(aeval_comp_eq_comp_aeval hg g.charpoly))
  rw [aeval_self_charpoly, zero_comp, comp_zero, ← comp_assoc, h, id_comp] at hgσ
  exact hgσ.symm

/-- The reflection `X ^ n · Q(1/X)` of the reversed characteristic polynomial `Q` of `f` is monic
whenever `n` bounds the degree of `Q`. -/
theorem monic_reflect_projectiveCharpolyRev (f : Module.End R M) {n : ℕ}
    (hn : (projectiveCharpolyRev f).natDegree ≤ n) :
    ((projectiveCharpolyRev f).reflect n).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one n (natDegree_reflect_le.trans (max_le le_rfl hn)) ?_
  rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_projectiveCharpolyRev_zero]

end LinearMap
