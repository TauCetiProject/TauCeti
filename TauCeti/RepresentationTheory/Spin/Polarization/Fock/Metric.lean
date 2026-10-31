/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Basic
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# The Hermitian metric of the normalized Fock module

Let `Q` be a nondegenerate quadratic form on a finite-dimensional real vector space `V` and `J` an
almost complex structure preserving `Q`. In the geometric convention `Q (v) = -g (v, v)`, the
metric `g` induces on the `i`-eigenspace `W` of the complexified complex structure the Hermitian
form

  `h (x, y) = g_ℂ (conj x, y) = -(1/2) polar Q_ℂ (conj x, y)`,

conjugate-linear in `x`, where `conj x = TauCeti.tmulConj V x` lies in the `-i`-eigenspace `W'`.
For a basis `b` of `W` that is orthonormal for `h`, in the sense that
`polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`, let `H` be the Hermitian form on the spinor module `⋀ W` for
which the increasing wedge basis of `b` is orthonormal. It is the exterior Gram metric of `h`: it
is positive definite, and it does not depend on the orthonormal basis.

This file proves that **the normalized Fock action is a `*`-representation for `H`**:
`H (c(a) s) t = H s (c(a^*) t)` for every element `a` of the complexified Clifford algebra, where
`a^*` is the conjugate-linear Clifford involution `CliffordAlgebra.conjStar`. In particular
Clifford multiplication `c(v)` by a real vector is skew-Hermitian. The underlying statement is the
adjointness of creation and annihilation: exterior multiplication by `x ∈ W` is adjoint to the
contraction `ι(conj x)` against `g_ℂ`, that is to `-(1/2)` times the contraction
`TauCeti.SpinPolarizationData.contract` against the polar form. Since the normalized Fock action
is `c(x) = √2 ε(x)` on `W` and `c(y) = (1/√2)` times contraction on `W'`, both halves of
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` carry the same factor, and the wedge basis is orthonormal.

The native action `TauCeti.spinAction`, which is `ε(v^(1,0)) - 2 ι(v^(0,1))`, is instead a
`*`-representation for the pullback `H (T s) (T t)` of `H` along the degree scaling `T` by `√2`
that intertwines the two actions. On `⋀^p W` this native metric is `2 ^ p` times `H`, so the wedge
basis is orthogonal for it with squared norms `2 ^ p`.

For a Euclidean space with `Q (v) = -‖v‖²` and an orthogonal complex structure, such a basis
exists: it is `√2 u₁^(1,0), …, √2 u_ℓ^(1,0)` for an adapted orthonormal basis
`(u₁, J u₁, …, u_ℓ, J u_ℓ)` of `V`.

## Main results

* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_apply_eq_polar`: an orthonormal basis of `W`
  is orthonormal for the intrinsic form `h (x, y) = -(1/2) polar Q_ℂ (conj x, y)`.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_wedge_left` and
  `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_contract_left`: creation and annihilation are
  adjoint.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_fockAction_left`: the normalized Fock action is
  a `*`-representation for `CliffordAlgebra.conjStar`, and
  `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_realFockAction_left`: its restriction to the real
  Clifford algebra is one for Clifford conjugation.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_fockAction_ι_one_tmul_left`: Clifford
  multiplication by a real vector is skew-Hermitian.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_degreeScaling_of_mem_exteriorPower`: the native
  metric is `2 ^ p` times the normalized one on `⋀^p W`, and
  `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_degreeScaling_spinAction_left`: the native action
  is a `*`-representation for it.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_exteriorAlgebra_eq`: the metric does not depend
  on the orthonormal basis.
* `TauCeti.AlmostComplexStructure.exists_basis_polar_tmulConj`: orthonormal bases exist for
  `Q (v) = -‖v‖²`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra Matrix Module QuadraticMap
open TauCeti.ExteriorAlgebra
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

section Metric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate) {ι : Type*} [Fintype ι] [LinearOrder ι]
  (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)

variable (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
  if i = j then -2 else 0)
include hb

/-- **An orthonormal basis of `W` is orthonormal for the intrinsic Hermitian form**: if
`polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`, then the form making `b` orthonormal is
`h (x, y) = -(1/2) polar Q_ℂ (conj x, y)`. In the geometric convention `Q (v) = -g (v, v)` this is
`h (x, y) = g_ℂ (conj x, y)`. -/
theorem toLinearMapₛₗ₂_apply_eq_polar (x y : (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b b (1 : Matrix ι ι ℂ) x y =
      -(2 : ℂ)⁻¹ * polar (Q.baseChange ℂ) (tmulConj V x) y := by
  let W := (J.spinPolarizationData hQJ hQ).W
  let B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
    ((((Q.baseChange ℂ).polarBilin.comp (tmulConj V)).comp W.subtype).compl₂ W.subtype)
  have hB : toLinearMapₛₗ₂ (starRingEnd ℂ) b b (1 : Matrix ι ι ℂ) = (-(2 : ℂ)⁻¹) • B := by
    refine LinearMap.ext_basis b b fun i j ↦ ?_
    simp only [toLinearMapₛₗ₂_apply_basis, one_apply, LinearMap.smul_apply, B,
      LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, polarBilin_apply_apply,
      hb, smul_eq_mul]
    split_ifs <;> norm_num
  simp only [hB, LinearMap.smul_apply, B, LinearMap.compl₂_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, polarBilin_apply_apply, smul_eq_mul]

/-- The polar pairing of the conjugate of `x` is `-2` times the Hermitian form `h (x, ·)`. -/
private theorem pairingEquiv_tmulConj (x : (J.spinPolarizationData hQJ hQ).W) :
    (J.spinPolarizationData hQJ hQ).pairingEquiv
        ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ =
      (-2 : ℂ) • toLinearMapₛₗ₂ (starRingEnd ℂ) b b (1 : Matrix ι ι ℂ) x := by
  refine LinearMap.ext fun y ↦ ?_
  rw [SpinPolarizationData.pairingEquiv_apply, polar_comm, LinearMap.smul_apply,
    J.toLinearMapₛₗ₂_apply_eq_polar hQJ hQ b hb, smul_eq_mul, ← mul_assoc]
  norm_num

/-- **Creation is adjoint to annihilation**: for an orthonormal basis `b` of `W` and the metric `H`
making its wedge basis orthonormal, exterior multiplication by `x ∈ W` is adjoint to `-(1/2)`
times the contraction against the polar pairing with the conjugate `conj x ∈ W'`. In the geometric
convention `Q (v) = -g (v, v)` this is the contraction `ι(conj x)` against `g_ℂ`. -/
theorem toLinearMapₛₗ₂_wedge_left (x : (J.spinPolarizationData hQJ hQ).W)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) ((J.spinPolarizationData hQJ hQ).wedge x s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s
        ((-(2 : ℂ)⁻¹) • (J.spinPolarizationData hQJ hQ).contract
          ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ t) := by
  rw [SpinPolarizationData.wedge_apply, ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_left,
    SpinPolarizationData.contract_apply, J.pairingEquiv_tmulConj hQJ hQ b hb]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  norm_num

/-- **Annihilation is adjoint to creation**: for an orthonormal basis `b` of `W` and the metric `H`
making its wedge basis orthonormal, the contraction against the polar pairing with `y ∈ W'` is
adjoint to `-2` times exterior multiplication by the conjugate `conj y ∈ W`. -/
theorem toLinearMapₛₗ₂_contract_left (y : (J.spinPolarizationData hQJ hQ).W')
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) ((J.spinPolarizationData hQJ hQ).contract y s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s
        ((-2 : ℂ) • (J.spinPolarizationData hQJ hQ).wedge
          ⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩ t) := by
  obtain ⟨x, rfl⟩ : ∃ x : (J.spinPolarizationData hQJ hQ).W,
      ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ = y :=
    ⟨⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩,
      Subtype.ext (tmulConj_tmulConj V y)⟩
  have hx : (⟨tmulConj V (tmulConj V (x : ℂ ⊗[ℝ] V)),
      J.tmulConj_mem_spinPolarizationData_W hQJ hQ
        (J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2)⟩ :
      (J.spinPolarizationData hQJ hQ).W) = x :=
    Subtype.ext (tmulConj_tmulConj V x)
  rw [hx, SpinPolarizationData.contract_apply, J.pairingEquiv_tmulConj hQJ hQ b hb,
    SpinPolarizationData.wedge_apply]
  simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_right, smul_eq_mul, map_neg, map_ofNat]

/-- The `*`-representation property for a vector of `W`. -/
private theorem toLinearMapₛₗ₂_fockAction_ι_coe_W_left (x : (J.spinPolarizationData hQJ hQ).W)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ)
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) (x : ℂ ⊗[ℝ] V)) s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s
        (J.fockAction hQJ hQ
          (conjStar Q (CliffordAlgebra.ι (Q.baseChange ℂ) (x : ℂ ⊗[ℝ] V))) t) := by
  -- The conjugate of `x` is the vector of `W'` with the same underlying tensor.
  have hx : tmulConj V (x : ℂ ⊗[ℝ] V) =
      ((⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ :
        (J.spinPolarizationData hQJ hQ).W') : ℂ ⊗[ℝ] V) := (rfl)
  rw [conjStar_ι, map_neg, hx, fockAction_ι_coe_W', fockAction_ι_coe_W]
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.map_smulₛₗ, map_smul, map_neg,
    J.toLinearMapₛₗ₂_wedge_left hQJ hQ b hb, Complex.conj_ofReal, smul_eq_mul,
    ← Complex.ofReal_inv, ← Real.sqrt_div_self, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The `*`-representation property for a vector of `W'`. -/
private theorem toLinearMapₛₗ₂_fockAction_ι_coe_W'_left (y : (J.spinPolarizationData hQJ hQ).W')
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ)
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) (y : ℂ ⊗[ℝ] V)) s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s
        (J.fockAction hQJ hQ
          (conjStar Q (CliffordAlgebra.ι (Q.baseChange ℂ) (y : ℂ ⊗[ℝ] V))) t) := by
  -- The conjugate of `y` is the vector of `W` with the same underlying tensor.
  have hy : tmulConj V (y : ℂ ⊗[ℝ] V) =
      ((⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩ :
        (J.spinPolarizationData hQJ hQ).W) : ℂ ⊗[ℝ] V) := (rfl)
  rw [conjStar_ι, map_neg, hy, fockAction_ι_coe_W', fockAction_ι_coe_W]
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.map_smulₛₗ, map_smul, map_neg,
    J.toLinearMapₛₗ₂_contract_left hQJ hQ b hb, ← Complex.ofReal_inv, ← Real.sqrt_div_self,
    Complex.ofReal_div, Complex.ofReal_ofNat, map_div₀, Complex.conj_ofReal, map_ofNat, smul_eq_mul]
  ring

/-- **The normalized Fock action is a `*`-representation**: for an orthonormal basis `b` of `W`
and the metric `H` making its wedge basis orthonormal, `H (c(a) s) t = H s (c(a^*) t)` for every
element `a` of the complexified Clifford algebra, where `a^*` is the conjugate-linear Clifford
involution `CliffordAlgebra.conjStar`. -/
theorem toLinearMapₛₗ₂_fockAction_left (a : CliffordAlgebra (Q.baseChange ℂ))
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) (J.fockAction hQJ hQ a s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s (J.fockAction hQJ hQ (conjStar Q a) t) := by
  induction a using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    simp only [conjStar_algebraMap, AlgHom.commutes, Module.algebraMap_end_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  | ι w =>
    -- Split `w` along the polarization; the orthogonal remainder vanishes.
    obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := (J.spinPolarizationData hQJ hQ).decompositionEquiv.surjective w
    have hz : (z : ℂ ⊗[ℝ] V) = 0 := by
      have := z.2
      simpa only [spinPolarizationData_line, Submodule.mem_bot] using this
    rw [SpinPolarizationData.decompositionEquiv_apply]
    dsimp only
    rw [hz, add_zero]
    simp only [map_add, LinearMap.add_apply, J.toLinearMapₛₗ₂_fockAction_ι_coe_W_left hQJ hQ b hb,
      J.toLinearMapₛₗ₂_fockAction_ι_coe_W'_left hQJ hQ b hb]
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | mul a a' ha ha' =>
    simp only [conjStar_mul, map_mul, Module.End.mul_apply]
    rw [ha, ha']

/-- **Clifford multiplication by a real vector is skew-Hermitian**: for an orthonormal basis `b`
of `W` and the metric `H` making its wedge basis orthonormal, `H (c(v) s) t = -H s (c(v) t)`. -/
theorem toLinearMapₛₗ₂_fockAction_ι_one_tmul_left (v : V)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ)
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) s) t =
      -toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) t) := by
  rw [J.toLinearMapₛₗ₂_fockAction_left hQJ hQ b hb, conjStar_ι_tmul, map_one (starRingEnd ℂ),
    map_neg, LinearMap.neg_apply, map_neg]

/-- **The real Fock action is a `*`-representation for Clifford conjugation**: for an orthonormal
basis `b` of `W` and the metric `H` making its wedge basis orthonormal,
`H (c(a) s) t = H s (c(star a) t)` for every element `a` of the real Clifford algebra, where
`star = reverse ∘ involute`. -/
theorem toLinearMapₛₗ₂_realFockAction_left (a : CliffordAlgebra Q)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) (J.realFockAction hQJ hQ a s) t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s (J.realFockAction hQJ hQ (star a) t) := by
  rw [realFockAction_apply, realFockAction_apply, J.toLinearMapₛₗ₂_fockAction_left hQJ hQ b hb,
    conjStar_ofBaseChangeAux]

/-- **The Fock metric does not depend on the orthonormal basis**: two bases of `W` orthonormal for
`h (x, y) = -(1/2) polar Q_ℂ (conj x, y)` give the same metric on `⋀ W`. -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_eq {ι' : Type*} [Fintype ι'] [LinearOrder ι']
    (b' : Basis ι' ℂ (J.spinPolarizationData hQJ hQ).W)
    (hb' : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b' i : ℂ ⊗[ℝ] V)) (b' j) =
      if i = j then -2 else 0) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b'.ExteriorAlgebra b'.ExteriorAlgebra
        (1 : Matrix (Finset ι') (Finset ι') ℂ) :=
  ExteriorAlgebra.toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq b b' <|
    LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by
      rw [J.toLinearMapₛₗ₂_apply_eq_polar hQJ hQ b hb,
        J.toLinearMapₛₗ₂_apply_eq_polar hQJ hQ b' hb']

end Metric

section NativeMetric

/-! ### The metric of the native action

The degree scaling `T` by `√2` intertwines the native action `TauCeti.spinAction` with the
normalized Fock action, so the native action is a `*`-representation for the pullback
`H (T s) (T t)` of the normalized Fock metric. On `⋀^p W` that pullback is `2 ^ p` times `H`. -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate) {ι : Type*} [Fintype ι] [LinearOrder ι]
  (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W) {r : ℂˣ} (hr : (r : ℂ) = Real.sqrt 2)
include hr

/-- **The native Fock metric has degree-`p` factor `2 ^ p`**: for the metric `H` making the wedge
basis of `b` orthonormal and the degree scaling `T` by `√2`, the pullback `H (T s) (T t)` is
`2 ^ p` times `H s t` for `s` in `⋀^p W`. -/
theorem toLinearMapₛₗ₂_degreeScaling_of_mem_exteriorPower {p : ℕ}
    {s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQ).W)
    (t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) (degreeScaling r s) (degreeScaling r t) =
      2 ^ p * toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) s t := by
  have h2 : star (r : ℂ) * r = 2 := by
    rw [hr, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  rw [ExteriorAlgebra.toLinearMapₛₗ₂_degreeScaling_degreeScaling_of_mem_exteriorPower b r hs, h2]

/-- **The native action is a `*`-representation for the native Fock metric**: for an orthonormal
basis `b` of `W`, the metric `H` making its wedge basis orthonormal and the degree scaling `T` by
`√2`, the native action `TauCeti.spinAction` satisfies
`H (T (a • s)) (T t) = H (T s) (T (a^* • t))`, where `a^*` is `CliffordAlgebra.conjStar`. -/
theorem toLinearMapₛₗ₂_degreeScaling_spinAction_left
    (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
      if i = j then -2 else 0)
    (a : CliffordAlgebra (Q.baseChange ℂ))
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ)
        (degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) a s)) (degreeScaling r t) =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) (degreeScaling r s)
        (degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) (conjStar Q a) t)) := by
  have hT (a : CliffordAlgebra (Q.baseChange ℂ))
      (x : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
      degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) a x) =
        J.fockAction hQJ hQ a (degreeScaling r x) :=
    LinearMap.congr_fun (J.degreeScaling_comp_spinAction_eq_fockAction_comp hQJ hQ hr a) x
  rw [hT, hT, J.toLinearMapₛₗ₂_fockAction_left hQJ hQ b hb]

end NativeMetric

section Existence

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V} (hQJ : ∀ v, Q (J v) = Q v)
  (hQnd : Q.Nondegenerate)

/-- **Orthonormal bases of `W` exist** for the geometric form `Q (v) = -‖v‖²` of a Euclidean space
of dimension `2ℓ`: there is a basis `b` of `W` with `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`, namely
`bₖ = √2 uₖ^(1,0)` for an orthonormal basis `(u₁, J u₁, …, u_ℓ, J u_ℓ)` of `V` adapted to `J`. -/
theorem exists_basis_polar_tmulConj (hQ : ∀ v, Q v = -‖v‖ ^ 2) (ℓ : ℕ)
    (hdim : finrank ℝ V = 2 * ℓ) :
    ∃ b : Basis (Fin ℓ) ℂ (J.spinPolarizationData hQJ hQnd).W,
      ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
        if i = j then -2 else 0 := by
  have hJ (v : V) : ‖J v‖ = ‖v‖ := by
    have h := hQJ v
    rw [hQ, hQ, neg_inj] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hpolar (a c : V) : polar Q a c = -(2 * ⟪a, c⟫) := by
    rw [polar, hQ, hQ, hQ, norm_add_sq_real]
    ring
  obtain ⟨u, hu⟩ := J.exists_adapted_orthonormalBasis hJ ℓ hdim
  have hinner (a c : Fin (2 * ℓ)) : ⟪u a, u c⟫ = if a = c then 1 else 0 :=
    orthonormal_iff_ite.mp u.orthonormal a c
  let w : Fin ℓ → (J.spinPolarizationData hQJ hQnd).W := fun k ↦
    (Real.sqrt 2 : ℂ) • ⟨J.holomorphicPart (u ⟨2 * k, by omega⟩),
      J.holomorphicPart_mem_spinPolarizationData_W hQJ hQnd _⟩
  have hw (i j : Fin ℓ) : polar (Q.baseChange ℂ) (tmulConj V (w i : ℂ ⊗[ℝ] V)) (w j) =
      if i = j then -2 else 0 := by
    have hsqrt : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
    simp only [w, Submodule.coe_smul, map_smulₛₗ, Complex.conj_ofReal, tmulConj_holomorphicPart,
      polar_smul_left, polar_smul_right, smul_eq_mul]
    rw [polar_comm, J.polar_holomorphicPart_antiholomorphicPart hQJ, ← hu i, hpolar, hpolar,
      hinner, hinner]
    -- The basis vectors `u (2 j)` and `u (2 i + 1)` are distinct, and `u (2 j) = u (2 i)` only
    -- for `i = j`.
    have h₁ : (⟨2 * j, by omega⟩ : Fin (2 * ℓ)) = ⟨2 * i + 1, by omega⟩ ↔ False := by
      simp only [Fin.mk.injEq, iff_false]
      omega
    have h₂ : (⟨2 * j, by omega⟩ : Fin (2 * ℓ)) = ⟨2 * i, by omega⟩ ↔ i = j := by
      simp only [Fin.ext_iff]
      omega
    simp only [h₁, h₂, ite_false]
    split_ifs
    · push_cast
      linear_combination (-1 : ℂ) * hsqrt
    · push_cast
      ring
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h := congrArg (((Q.baseChange ℂ).polarBilin (tmulConj V (w i : ℂ ⊗[ℝ] V))).comp
      (J.spinPolarizationData hQJ hQnd).W.subtype) hg
    simp only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
      polarBilin_apply_apply, hw, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, hi,
      ite_true, map_zero] at h
    simpa using h
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' w hli ?_, fun i j ↦ ?_⟩
  · rw [Fintype.card_fin, finrank_spinPolarizationData_W, hdim]
    omega
  · simp only [basisOfLinearIndependentOfCardEqFinrank', Basis.coe_mk, hw]

end Existence

end TauCeti.AlmostComplexStructure
