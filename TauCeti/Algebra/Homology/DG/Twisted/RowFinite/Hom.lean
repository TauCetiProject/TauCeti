/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic

/-!
# Graded maps out of a row-finite twisted free module

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A`, and let `N` be a differential graded left module.
A graded `A`-linear map `Ψ : K_m → N` of degree `j` satisfies the Koszul rule
`Ψ (a • f) = (-1)^(j |a|) a • Ψ f`, so it is determined by the images `u x ∈ N` of the generators,
of degree `j - ind x`, which may be chosen freely. The map with these values is
`TauCeti.rowFiniteSignedCombination j u`, which sends `single x a` to `(-1)^(j |a|) a • u x`.
For `j = 0` it is the linear combination `Finsupp.linearCombination A u`
(`TauCeti.rowFiniteSignedCombination_zero_left`), and for `j = 1` with free target it is the
signed row substitution `TauCeti.rowFiniteSignedMap` (`TauCeti.rowFiniteSignedCombination_one`).

The complex of graded maps `K_m → N` has differential `δ Ψ = d_N ∘ Ψ - (-1)^j Ψ ∘ D`. Read on
generators, it sends a family `u` of degree `j` to the family
`δ_j u = x ↦ d_N (u x) - (-1)^j Ψ_u (m x)` (`TauCeti.rowFiniteHomDifferential`), because the
differential of the generator `x` is its row `m x`. The Leibniz identity
`Ψ_{δ_j u} = d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D` holds on the whole free module
(`TauCeti.rowFiniteSignedCombination_rowFiniteHomDifferential`), so `δ_j` is the differential of
the complex of graded maps out of `K_m`, written on generator values, and it squares to zero
(`TauCeti.RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential`).
Its zero-cycles are the families giving morphisms of differential graded modules
(`TauCeti.forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero`), and for free targets
its degree `0` and `-1`
equations are those of row-finite continuation and parametrized cocycles.

The value of `δ_j u` at `x` only reads `u` on `x` and on the support of the row `m x`
(`TauCeti.rowFiniteSignedCombination_congr`). This locality is what lets maps out of `K_m` be
built one generator at a time when the rows lower a bounded-below index, as in
`TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting`.

## Main definitions

* `TauCeti.rowFiniteSignedCombination j u`: the graded map of degree `j` with generator values `u`.
* `TauCeti.rowFiniteHomDifferential m dN j u`: the differential of the complex of graded maps out
  of `K_m`, on generator values.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uN uN' uP uQ

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-! ### The graded map with given generator values -/

section SignedCombination

variable (𝒜) in
/-- The graded `A`-linear map of degree `j` out of the free module `P →₀ A` with generator values
`u`: it sends `single x a` to `(-1)^(j |a|) a • u x` for homogeneous `a`. -/
def rowFiniteSignedCombination (j : ℤ) (u : P → N) : (P →₀ A) →ₗ[R] N :=
  Finsupp.lsum R fun x ↦
    ((LinearMap.toSpanSingleton A N (u x)).restrictScalars R).comp
      ((InternalGrading.ofDecomposition 𝒜).koszulTwist j)

/-- The graded map with generator values `u` is a finite sum over the support of its input. -/
theorem rowFiniteSignedCombination_apply (j : ℤ) (u : P → N) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j u f =
      f.sum (fun x a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist j a • u x) := by
  classical
  simp [rowFiniteSignedCombination, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply,
    Function.comp_def]

/-- The graded map with generator values `u` on a single, not necessarily homogeneous,
coefficient. -/
theorem rowFiniteSignedCombination_single_koszulTwist (j : ℤ) (u : P → N) (x : P) (a : A) :
    rowFiniteSignedCombination 𝒜 j u (Finsupp.single x a) =
      (InternalGrading.ofDecomposition 𝒜).koszulTwist j a • u x := by
  simp [rowFiniteSignedCombination, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The graded map with generator values `u` on a single homogeneous coefficient of degree `q`. -/
theorem rowFiniteSignedCombination_single (j : ℤ) (u : P → N) (x : P) {q : ℤ} {a : A}
    (ha : a ∈ 𝒜 q) :
    rowFiniteSignedCombination 𝒜 j u (Finsupp.single x a) = (j * q).negOnePow • (a • u x) := by
  rw [rowFiniteSignedCombination_single_koszulTwist, koszulTwist_eq_negOnePow_smul j ha,
    smul_assoc]

/-- A generator is sent to its value. -/
@[simp]
theorem rowFiniteSignedCombination_single_one (j : ℤ) (u : P → N) (x : P) :
    rowFiniteSignedCombination 𝒜 j u (Finsupp.single x 1) = u x := by
  rw [rowFiniteSignedCombination_single j u x (SetLike.one_mem_graded 𝒜)]
  simp

/-- **The graded map of degree `j` satisfies the Koszul rule**:
`Ψ (a • f) = (-1)^(j |a|) a • Ψ f`, written with the Koszul twist so that `a` need not be
homogeneous. -/
theorem rowFiniteSignedCombination_smul (j : ℤ) (u : P → N) (a : A) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j u (a • f) =
      (InternalGrading.ofDecomposition 𝒜).koszulTwist j a • rowFiniteSignedCombination 𝒜 j u f := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | @homogeneous q a =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [smul_add, map_add, hf, hg]
    | single x b =>
      rw [Finsupp.smul_single, smul_eq_mul, rowFiniteSignedCombination_single_koszulTwist,
        rowFiniteSignedCombination_single_koszulTwist, koszulTwist_eq_negOnePow_smul j a.2]
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add b c hb hc => simp only [mul_add, map_add, add_smul, smul_add, hb, hc]
      | @homogeneous p b =>
        rw [koszulTwist_eq_negOnePow_smul j (SetLike.GradedMul.mul_mem a.2 b.2),
          koszulTwist_eq_negOnePow_smul j b.2, mul_add, Int.negOnePow_add]
        simp only [Units.smul_def, smul_assoc, mul_smul]
        rw [smul_comm (a : A) ((j * p).negOnePow : ℤ)]

/-- With degree zero, the graded map with generator values `u` is their linear combination. -/
theorem rowFiniteSignedCombination_zero_left (u : P → N) :
    rowFiniteSignedCombination 𝒜 0 u = (Finsupp.linearCombination A u).restrictScalars R := by
  refine Finsupp.lhom_ext fun x a ↦ ?_
  rw [rowFiniteSignedCombination_single_koszulTwist, LinearMap.restrictScalars_apply,
    Finsupp.linearCombination_single]
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_smul, ha, hb]
  | @homogeneous q a => rw [koszulTwist_eq_negOnePow_smul 0 a.2, zero_mul, Int.negOnePow_zero,
      one_smul]

/-- With degree one and free target, the graded map with generator values `h` is the signed row
substitution. -/
theorem rowFiniteSignedCombination_one {Q : Type uQ} (h : P → Q →₀ A) :
    rowFiniteSignedCombination 𝒜 1 h = rowFiniteSignedMap (𝒜 := 𝒜) h :=
  LinearMap.ext fun f ↦ by rw [rowFiniteSignedCombination_apply, rowFiniteSignedMap_apply]

/-- The graded maps of degrees `-1` and `1` with the same generator values agree: the Koszul sign
only depends on the parity of the degree. -/
theorem rowFiniteSignedCombination_neg_one (u : P → N) :
    rowFiniteSignedCombination 𝒜 (-1) u = rowFiniteSignedCombination 𝒜 1 u := by
  refine Finsupp.lhom_ext fun x a ↦ ?_
  rw [rowFiniteSignedCombination_single_koszulTwist, rowFiniteSignedCombination_single_koszulTwist]
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_smul, ha, hb]
  | @homogeneous q a =>
    rw [koszulTwist_eq_negOnePow_smul (-1) a.2, koszulTwist_eq_negOnePow_smul 1 a.2, neg_mul,
      Int.negOnePow_neg]

/-- The graded map only depends on the generator values on the support of its input. -/
theorem rowFiniteSignedCombination_congr (j : ℤ) {u u' : P → N} {f : P →₀ A}
    (h : ∀ x ∈ f.support, u x = u' x) :
    rowFiniteSignedCombination 𝒜 j u f = rowFiniteSignedCombination 𝒜 j u' f := by
  rw [rowFiniteSignedCombination_apply, rowFiniteSignedCombination_apply]
  exact Finset.sum_congr rfl fun x hx ↦ by dsimp only; rw [h x hx]

/-- The graded map with zero generator values is zero. -/
@[simp]
theorem rowFiniteSignedCombination_zero_right (j : ℤ) :
    rowFiniteSignedCombination 𝒜 j (0 : P → N) = 0 :=
  LinearMap.ext fun f ↦ by simp [rowFiniteSignedCombination_apply]

/-- The graded map is additive in its generator values. -/
theorem rowFiniteSignedCombination_add (j : ℤ) (u u' : P → N) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j (u + u') f =
      rowFiniteSignedCombination 𝒜 j u f + rowFiniteSignedCombination 𝒜 j u' f := by
  simp only [rowFiniteSignedCombination_apply, Pi.add_apply, smul_add, Finsupp.sum_add]

/-- The graded map is subtractive in its generator values. -/
theorem rowFiniteSignedCombination_sub (j : ℤ) (u u' : P → N) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j (u - u') f =
      rowFiniteSignedCombination 𝒜 j u f - rowFiniteSignedCombination 𝒜 j u' f := by
  simp only [rowFiniteSignedCombination_apply, Pi.sub_apply, smul_sub, Finsupp.sum_sub]

/-- The graded map is negated with its generator values. -/
theorem rowFiniteSignedCombination_neg (j : ℤ) (u : P → N) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j (-u) f = -rowFiniteSignedCombination 𝒜 j u f := by
  simp only [rowFiniteSignedCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg]

/-- Postcomposition with an `A`-linear map acts on the generator values. -/
theorem map_rowFiniteSignedCombination (g : N →ₗ[A] N') (j : ℤ) (u : P → N) (f : P →₀ A) :
    g (rowFiniteSignedCombination 𝒜 j u f) = rowFiniteSignedCombination 𝒜 j (g ∘ u) f := by
  simp only [rowFiniteSignedCombination_apply, Finsupp.sum, map_sum, map_smul,
    Function.comp_apply]

/-- **Precomposition with a substitution of rows**: the graded map with generator values `u`,
applied to the linear combination of rows `ν`, is the graded map with generator values
`Ψ_u ∘ ν`. -/
theorem rowFiniteSignedCombination_linearCombination {Q : Type uQ} (j : ℤ) (u : Q → N)
    (ν : P → Q →₀ A) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 j u (Finsupp.linearCombination A ν f) =
      rowFiniteSignedCombination 𝒜 j (fun x ↦ rowFiniteSignedCombination 𝒜 j u (ν x)) f := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, rowFiniteSignedCombination_apply,
    Finsupp.sum]
  exact Finset.sum_congr rfl fun x _ ↦ rowFiniteSignedCombination_smul j u _ _

variable {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩]

/-- Generator values of degree `j - ind x` give a graded map of degree `j`. -/
theorem rowFiniteSignedCombination_mem {j : ℤ} {u : P → N} {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hu : ∀ x ∈ f.support, u x ∈ 𝒩 (j - ind x)) :
    rowFiniteSignedCombination 𝒜 j u f ∈ 𝒩 (n + j) := by
  rw [mem_rowFiniteTotalGrading_iff] at hf
  rw [rowFiniteSignedCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  rw [koszulTwist_eq_negOnePow_smul j (hf x), smul_assoc]
  refine Submodule.smul_of_tower_mem _ _ ?_
  convert SetLike.GradedSMul.smul_mem (hf x) (hu x hx) using 2
  simp only [vadd_eq_add]
  ring

omit [GradedAlgebra 𝒜] in
/-- The row of a generator `x` has total degree `1 - ind x`, one more than the generator. -/
theorem RowFiniteTwistingCocycle.m_mem_rowFiniteTotalGrading
    (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    m.m x ∈ rowFiniteTotalGrading 𝒜 ind (1 - ind x) :=
  (mem_rowFiniteTotalGrading_iff _ _).mpr fun y ↦ by
    convert m.mem_graded x y using 2
    ring

end SignedCombination

/-! ### The differential of the complex of graded maps -/

section HomDifferential

variable (𝒜) in
/-- **The differential of the complex of graded maps out of `K_m`, on generator values.** A family
`u` of degree `j`, with `u x` of degree `j - ind x`, is sent to the family
`x ↦ d_N (u x) - (-1)^j Ψ_u (m x)` of degree `j + 1`, where `Ψ_u` is the graded map with
generator values `u`. These are the generator values of `d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D`
(`TauCeti.rowFiniteSignedCombination_rowFiniteHomDifferential`). -/
def rowFiniteHomDifferential (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N) : P → N :=
  fun x ↦ dN (u x) - j.negOnePow • rowFiniteSignedCombination 𝒜 j u (m x)

theorem rowFiniteHomDifferential_apply (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N)
    (x : P) :
    rowFiniteHomDifferential 𝒜 m dN j u x =
      dN (u x) - j.negOnePow • rowFiniteSignedCombination 𝒜 j u (m x) :=
  (rfl)

/-- The differential of graded maps is additive. -/
theorem rowFiniteHomDifferential_add (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u u' : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (u + u') =
      rowFiniteHomDifferential 𝒜 m dN j u + rowFiniteHomDifferential 𝒜 m dN j u' := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.add_apply, map_add,
    rowFiniteSignedCombination_add, smul_add]
  abel

/-- The differential of graded maps is subtractive. -/
theorem rowFiniteHomDifferential_sub (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u u' : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (u - u') =
      rowFiniteHomDifferential 𝒜 m dN j u - rowFiniteHomDifferential 𝒜 m dN j u' := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.sub_apply, map_sub,
    rowFiniteSignedCombination_sub, smul_sub]
  abel

/-- The differential of graded maps commutes with negation. -/
theorem rowFiniteHomDifferential_neg (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (-u) = -rowFiniteHomDifferential 𝒜 m dN j u := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.neg_apply, map_neg,
    rowFiniteSignedCombination_neg, smul_neg]
  abel

/-- The value of the differential at `x` only depends on the generator values at `x` and on the
support of the row of `x`. -/
theorem rowFiniteHomDifferential_congr (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) {u u' : P → N}
    {x : P} (hx : u x = u' x) (h : ∀ y ∈ (m x).support, u y = u' y) :
    rowFiniteHomDifferential 𝒜 m dN j u x = rowFiniteHomDifferential 𝒜 m dN j u' x := by
  rw [rowFiniteHomDifferential_apply, rowFiniteHomDifferential_apply, hx,
    rowFiniteSignedCombination_congr j h]

/-- Postcomposition with an `A`-linear map commuting with the differentials commutes with the
differential of graded maps. -/
theorem map_rowFiniteHomDifferential (m : P → P →₀ A) {dN : N →ₗ[R] N} {dN' : N' →ₗ[R] N'}
    (g : N →ₗ[A] N') (hg : ∀ z, g (dN z) = dN' (g z)) (j : ℤ) (u : P → N) :
    g ∘ rowFiniteHomDifferential 𝒜 m dN j u = rowFiniteHomDifferential 𝒜 m dN' j (g ∘ u) := by
  funext x
  simp only [Function.comp_apply, rowFiniteHomDifferential_apply, map_sub, hg,
    map_rowFiniteSignedCombination, Units.smul_def, map_zsmul]

variable {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N} {hA : IsDGAlgebra 𝒜 d}

/-- The differential of graded maps raises the degree of generator values by one. -/
theorem rowFiniteHomDifferential_mem (hN : IsDGLeftModule hA 𝒩 dN)
    (m : RowFiniteTwistingCocycle 𝒜 d P ind) {j : ℤ} {u : P → N}
    (hu : ∀ x, u x ∈ 𝒩 (j - ind x)) (x : P) :
    rowFiniteHomDifferential 𝒜 m.m dN j u x ∈ 𝒩 (j + 1 - ind x) := by
  refine Submodule.sub_mem _ ?_ (Submodule.smul_of_tower_mem _ _ ?_)
  · convert hN.isHomogeneous.map_mem (hu x) using 2
    ring
  · convert rowFiniteSignedCombination_mem (m.m_mem_rowFiniteTotalGrading x) fun y _ ↦ hu y
      using 2
    ring

/-- **The Leibniz identity of graded maps.** The graded map with generator values `δ_j u` is
`d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D` on the whole free module. -/
theorem rowFiniteSignedCombination_rowFiniteHomDifferential (hN : IsDGLeftModule hA 𝒩 dN)
    (m : P → P →₀ A) (j : ℤ) (u : P → N) (f : P →₀ A) :
    rowFiniteSignedCombination 𝒜 (j + 1) (rowFiniteHomDifferential 𝒜 m dN j u) f =
      dN (rowFiniteSignedCombination 𝒜 j u f) -
        j.negOnePow • rowFiniteSignedCombination 𝒜 j u
          (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, smul_add]
    abel
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a b ha hb =>
      simp only [Finsupp.single_add, map_add, ha, hb, smul_add]
      abel
    | @homogeneous q a =>
      -- The two terms involving `d a` cancel; what remains is `a` times the generator value.
      have hΨ : rowFiniteSignedCombination 𝒜 j u (q.negOnePow • ((a : A) • m x)) =
          (j * q + q).negOnePow • ((a : A) • rowFiniteSignedCombination 𝒜 j u (m x)) := by
        rw [LinearMap.map_smul_of_tower, rowFiniteSignedCombination_smul,
          koszulTwist_eq_negOnePow_smul j a.2, smul_assoc, smul_smul, ← Int.negOnePow_add,
          add_comm q]
      have hd : dN (rowFiniteSignedCombination 𝒜 j u (Finsupp.single x a)) =
          (j * q).negOnePow • (d a • u x) + (j * q + q).negOnePow • ((a : A) • dN (u x)) := by
        rw [rowFiniteSignedCombination_single j u x a.2, LinearMap.map_smul_of_tower,
          hN.leibniz a.2, smul_add, smul_smul, ← Int.negOnePow_add]
      have hj : j.negOnePow * (j * (q + 1)).negOnePow = (j * q).negOnePow := by
        rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
        exact ⟨j, by ring⟩
      rw [rowFiniteSignedCombination_single _ _ x a.2, rowFiniteTwistedDifferential_single m x a.2,
        map_add, rowFiniteSignedCombination_single j u x (hA.map_mem a.2), hΨ, hd,
        rowFiniteHomDifferential_apply, smul_add, smul_smul, hj, smul_sub, smul_sub, smul_smul,
        ← Int.negOnePow_add, smul_comm (a : A) j.negOnePow, smul_smul, ← Int.negOnePow_add,
        show (j + 1) * q = j * q + q by ring, show j + (j * q + q) = j * q + q + j by ring]
      abel

/-- The differential of graded maps vanishes on generator values of a vanishing row: the identity
`δ_(j+1) (δ_j u) = 0` at a single generator. -/
theorem RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential_apply
    (hN : IsDGLeftModule hA 𝒩 dN) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (j : ℤ) (u : P → N)
    (x : P) :
    rowFiniteHomDifferential 𝒜 m.m dN (j + 1) (rowFiniteHomDifferential 𝒜 m.m dN j u) x = 0 := by
  rw [rowFiniteHomDifferential_apply, rowFiniteSignedCombination_rowFiniteHomDifferential hN,
    m.differential_row, map_zero, smul_zero, sub_zero, rowFiniteHomDifferential_apply, map_sub,
    hN.sq_zero, LinearMap.map_smul_of_tower, Int.negOnePow_succ, Units.neg_smul]
  abel

/-- **The differential of graded maps squares to zero.** -/
theorem RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential
    (hN : IsDGLeftModule hA 𝒩 dN) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (j : ℤ) (u : P → N) :
    rowFiniteHomDifferential 𝒜 m.m dN (j + 1) (rowFiniteHomDifferential 𝒜 m.m dN j u) = 0 :=
  funext (m.rowFiniteHomDifferential_rowFiniteHomDifferential_apply hN j u)

omit [DirectSum.Decomposition 𝒩] in
/-- **The zero-cycles are the morphisms of differential graded modules**: the linear combination
of generator values `u` commutes with the differentials exactly when `u` has vanishing
differential in degree `0`. -/
theorem forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (m : P → P →₀ A)
    (u : P → N) :
    (∀ x, Finsupp.linearCombination A u (m x) = dN (u x)) ↔
      rowFiniteHomDifferential 𝒜 m dN 0 u = 0 := by
  simp only [funext_iff, rowFiniteHomDifferential_apply, Int.negOnePow_zero, one_smul,
    rowFiniteSignedCombination_zero_left, LinearMap.restrictScalars_apply, Pi.zero_apply,
    sub_eq_zero]
  exact forall_congr' fun _ ↦ eq_comm

omit [DirectSum.Decomposition 𝒩] in
/-- In degree `-1`, the differential of graded maps adds the signed row substitution: this is the
left-hand side of the equation of a parametrized cocycle. -/
theorem rowFiniteHomDifferential_neg_one_apply (m : P → P →₀ A) (u : P → N) (x : P) :
    rowFiniteHomDifferential 𝒜 m dN (-1) u x =
      dN (u x) + rowFiniteSignedCombination 𝒜 1 u (m x) := by
  rw [rowFiniteHomDifferential_apply, rowFiniteSignedCombination_neg_one, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, one_smul, sub_neg_eq_add]

end HomDifferential

end TauCeti
