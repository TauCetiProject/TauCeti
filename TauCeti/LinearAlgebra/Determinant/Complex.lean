/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray
public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.LinearAlgebra.Determinant.Line
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Complex orientations of real determinant lines

A finite-dimensional complex vector space `E` carries a canonical real orientation
(`TauCeti.complexOrientation`). On its real determinant line `⋀ⁿ E`, `n = finrank ℝ E`, this is
the ray `TauCeti.complexDetLineRay E` of `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯`, which is the same for
every complex basis `b` (`Module.Basis.complexDetLineRay_eq`), because the real determinant
between two such real bases is the squared modulus of the complex one. Likewise the real
determinant line `det (ker f) ⊗ (det (coker f))^*` of a complex-linear map `f` with
finite-dimensional kernel and cokernel carries the complex orientation
`LinearMap.complexDetLineRay f`, the ray of `(b₀ ∧ I • b₀ ∧ ⋯) ⊗ (c₀ ∧ I • c₀ ∧ ⋯)^*` for complex
bases `b` of the kernel and `c` of the cokernel (`LinearMap.complexDetLineRay_eq`). These are the
complex orientations of the determinant lines of complex-linear Fredholm operators, such as
complex Dirac and Cauchy–Riemann operators.

Real-linear isomorphisms commuting with `I` preserve these orientations
(`LinearEquiv.map_complexDetLineRay`, `LinearMap.map_detLineCongr_complexDetLineRay`).
Isomorphisms anticommuting with `I`, that is, conjugate-linear ones, change them by a sign. On a
space of complex dimension `n` the sign is `(-1) ^ n`, since each pair `bᵢ, I • bᵢ` goes to
`g bᵢ, -(I • g bᵢ)` (`LinearEquiv.map_complexDetLineRay_eq_neg_one_pow_smul`). On the
determinant line of a map, transport along a commuting square of conjugate-linear isomorphisms
multiplies the complex orientation by `(-1) ^ (k + c)`, where `k` and `c` are the complex
dimensions of the kernel and the cokernel; this is `(-1)` to the complex index `k - c`
(`LinearMap.map_detLineCongr_complexDetLineRay_eq_neg_one_pow_smul`).

In Seiberg–Witten theory this is the complex factor of the determinant sign of charge
conjugation: the quaternionic structure of the spinors is a conjugate-linear intertwiner of the
Dirac operators of a `Spinᶜ` structure and of its conjugate, so it contributes `(-1)` to the
complex index of the Dirac operator. Charge conjugation negates both the domain and the target of
the real deformation operator on imaginary forms; that contributes `(-1)` to the sum of the
dimensions of its kernel and cokernel (`LinearMap.detLineCongr_neg_apply`).

## Main definitions

* `Module.Basis.complexToRealFin`: the real basis `(b₀, I • b₀, b₁, I • b₁, …)` underlying a
  complex basis, indexed by `Fin (finrank ℝ E)`.
* `TauCeti.complexDetLineRay`: the complex orientation of the determinant line of a complex vector
  space.
* `LinearMap.cokerRestrictScalarsEquiv`: the cokernel of a complex-linear map is that of the
  underlying real-linear map.
* `LinearMap.complexDetLineGen`: the generator of the determinant line of a complex-linear map
  given by complex bases of its kernel and cokernel.
* `LinearMap.complexDetLineRay`: the complex orientation of the determinant line of a
  complex-linear map.

## Main results

* `Module.Basis.complexDetLineRay_eq`, `LinearMap.complexDetLineRay_eq`: every choice of complex
  bases computes the complex orientation.
* `TauCeti.det_complexToRealFin_comp_pos`,
  `TauCeti.neg_one_pow_mul_det_complexToRealFin_comp_pos`: the sign of the real determinant of a
  complex-linear, respectively conjugate-linear, isomorphism in real bases underlying complex
  bases.
* `LinearEquiv.map_complexDetLineRay`, `LinearMap.map_detLineCongr_complexDetLineRay`:
  complex-linear transport preserves the complex orientation.
* `LinearEquiv.map_complexDetLineRay_eq_neg_one_pow_smul`,
  `LinearMap.map_detLineCongr_complexDetLineRay_eq_neg_one_pow_smul`: conjugate-linear transport
  multiplies it by `(-1) ^ n`, respectively `(-1) ^ (k + c)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Module exteriorPower

namespace TauCeti

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- The index equivalence `Fin (finrank ℂ E) × Fin 2 ≃ Fin (finrank ℝ E)` sending `(i, k)` to
`2 * i + k`, which orders the real basis underlying a complex basis `b` as
`(b₀, I • b₀, b₁, I • b₁, …)`. -/
def complexRealFinEquiv : Fin (finrank ℂ E) × Fin 2 ≃ Fin (finrank ℝ E) :=
  (complexRealIndexEquiv _).trans (finCongr finrank_real_eq_two_mul_finrank_complex.symm)

@[simp]
theorem complexRealFinEquiv_apply_val (i : Fin (finrank ℂ E)) (k : Fin 2) :
    (complexRealFinEquiv E (i, k) : ℕ) = 2 * i + k := by
  simp [complexRealFinEquiv]

end TauCeti

namespace Module.Basis

open TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- The real basis `(b₀, I • b₀, b₁, I • b₁, …)` underlying a complex basis `b`, indexed by
`Fin (finrank ℝ E)` so that its exterior product lies in the determinant line `⋀ⁿ E`. -/
def complexToRealFin (b : Basis (Fin (finrank ℂ E)) ℂ E) : Basis (Fin (finrank ℝ E)) ℝ E :=
  b.complexToReal.reindex (complexRealFinEquiv E)

@[simp]
theorem complexToRealFin_apply (b : Basis (Fin (finrank ℂ E)) ℂ E) (i : Fin (finrank ℂ E))
    (k : Fin 2) :
    b.complexToRealFin (complexRealFinEquiv E (i, k)) = Complex.basisOneI k • b i := by
  simp [complexToRealFin]

/-- The real determinant between the real bases underlying two complex bases is the squared
modulus of their complex determinant. -/
theorem det_complexToRealFin (b c : Basis (Fin (finrank ℂ E)) ℂ E) :
    b.complexToRealFin.det c.complexToRealFin = Complex.normSq (b.det c) := by
  rw [complexToRealFin, complexToRealFin, det_reindex, ← det_complexToReal]
  congr 1
  ext j
  simp

end Module.Basis

namespace TauCeti

open Complex

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-- If `(-1) ^ n * d` is positive, then `d • x` lies on the ray of `(-1) ^ n • x`. -/
private theorem sameRay_smul_neg_one_pow_smul {L : Type*} [AddCommGroup L] [Module ℝ L] {d : ℝ}
    {n : ℕ} (hd : 0 < (-1) ^ n * d) (x : L) :
    SameRay ℝ (d • x) (((-1 : ℝˣ) ^ n) • x) := by
  have h : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  have hx : d • x = ((-1) ^ n * d) • (((-1 : ℝˣ) ^ n) • x) := by
    rw [Units.smul_def, smul_smul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    congr 1
    linear_combination (-d) * h
  rw [hx]
  exact SameRay.sameRay_pos_smul_left _ hd

/-- The real determinant, against the real basis underlying a complex basis `c` of `F`, of the
image under a complex-linear `g` of the real basis underlying a complex basis `b` of `E` is
positive. -/
theorem det_complexToRealFin_comp_pos (g : E ≃ₗ[ℝ] F) (hg : ∀ x, g (I • x) = I • g x)
    (b : Basis (Fin (finrank ℂ E)) ℂ E) (c : Basis (Fin (finrank ℂ F)) ℂ F) :
    0 < c.complexToRealFin.det (g ∘ b.complexToRealFin ∘ Fin.cast g.finrank_eq.symm) := by
  set gC : E ≃ₗ[ℂ] F :=
    .ofBijective (g.toLinearMap.complexOfMapISmul hg) (by simpa using g.bijective)
  have hgC (x : E) : gC x = g x := by simp [gC]
  set b' := (b.map gC).reindex (finCongr gC.finrank_eq)
  have hb : g ∘ b.complexToRealFin ∘ Fin.cast g.finrank_eq.symm = b'.complexToRealFin := by
    funext j
    obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealFinEquiv F).surjective j
    have hj : Fin.cast g.finrank_eq.symm (complexRealFinEquiv F (i, k)) =
        complexRealFinEquiv E (Fin.cast gC.finrank_eq.symm i, k) := Fin.ext (by simp)
    simp only [Function.comp_apply, hj, Basis.complexToRealFin_apply, b', Basis.reindex_apply,
      Basis.map_apply, ← hgC, map_smul, finCongr_symm, finCongr_apply]
  rw [hb, Basis.det_complexToRealFin]
  exact Complex.normSq_pos.mpr (c.isUnit_det b').ne_zero

/-- For a conjugate-linear `g`, the real determinant of the preceding lemma has the sign
`(-1) ^ n`, `n = finrank ℂ E`: the vectors `I • bᵢ` go to `-(I • g bᵢ)`. -/
theorem neg_one_pow_mul_det_complexToRealFin_comp_pos [FiniteDimensional ℂ F] (g : E ≃ₗ[ℝ] F)
    (hg : ∀ x, g (I • x) = -(I • g x))
    (b : Basis (Fin (finrank ℂ E)) ℂ E) (c : Basis (Fin (finrank ℂ F)) ℂ F) :
    0 < (-1) ^ finrank ℂ E *
      c.complexToRealFin.det (g ∘ b.complexToRealFin ∘ Fin.cast g.finrank_eq.symm) := by
  have hn : finrank ℂ E = finrank ℂ F := g.finrank_complex_eq
  have hconj := g.toLinearMap.map_smul_eq_conj_smul_of_map_I_smul hg
  -- The images `g bᵢ` form a complex basis `b'` of `F`, since `g` is conjugate-linear.
  have hli : LinearIndependent ℂ (g ∘ b ∘ Fin.cast hn.symm) :=
    (b.linearIndependent.comp _ (Fin.cast_injective hn.symm)).map_of_injective_injectiveₛ
      (starRingEnd ℂ) g.toAddEquiv.toAddMonoidHom (RingHom.injective _) g.injective
      fun r m ↦ by simpa using hconj (starRingEnd ℂ r) m
  set b' : Basis (Fin (finrank ℂ F)) ℂ F :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _)
  -- The image of the real basis of `b` is the real basis of `b'` with its `I`-vectors negated.
  set s : Fin (finrank ℝ F) → ℝˣ :=
    fun j ↦ if ((complexRealFinEquiv F).symm j).2 = 0 then 1 else -1
  have hb : g ∘ b.complexToRealFin ∘ Fin.cast g.finrank_eq.symm =
      b'.complexToRealFin.unitsSMul s := by
    funext j
    obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealFinEquiv F).surjective j
    have hj : Fin.cast g.finrank_eq.symm (complexRealFinEquiv F (i, k)) =
        complexRealFinEquiv E (Fin.cast hn.symm i, k) := Fin.ext (by simp)
    have hb'i : b' i = g (b (Fin.cast hn.symm i)) := by simp [b']
    simp only [Function.comp_apply, hj, Basis.complexToRealFin_apply, Basis.unitsSMul_apply,
      Equiv.symm_apply_apply, s, hb'i]
    fin_cases k <;> simp [hg, Units.smul_def]
  have hs : ∏ j, (s j : ℝ) = (-1) ^ finrank ℂ F := by
    rw [← (complexRealFinEquiv F).prod_comp, Fintype.prod_prod_type]
    simp [s, Fin.prod_univ_two]
  have hdet : c.complexToRealFin.det (b'.complexToRealFin.unitsSMul s) =
      (-1) ^ finrank ℂ F * c.complexToRealFin.det b'.complexToRealFin := by
    have : ⇑(b'.complexToRealFin.unitsSMul s) = fun j ↦ (s j : ℝ) • b'.complexToRealFin j :=
      funext fun j ↦ by simp [Basis.unitsSMul_apply, Units.smul_def]
    rw [this, AlternatingMap.map_smul_univ, hs, smul_eq_mul]
  rw [hb, hdet, Basis.det_complexToRealFin, ← mul_assoc, hn, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  exact Complex.normSq_pos.mpr (c.isUnit_det b').ne_zero

/-! ### The complex orientation of a determinant line -/

variable (E) in
/-- The **complex orientation** of the real determinant line `⋀ⁿ E`, `n = finrank ℝ E`, of a
finite-dimensional complex vector space: the ray of `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯` for any
complex basis `b` (`Module.Basis.complexDetLineRay_eq`). -/
def complexDetLineRay [FiniteDimensional ℂ E] : Module.Ray ℝ (detLine ℝ E) :=
  rayOfNeZero ℝ (ιMulti ℝ _ (finBasis ℂ E).complexToRealFin)
    ((ιMulti_ne_zero_iff _).2 (finBasis ℂ E).complexToRealFin.linearIndependent)

end TauCeti

namespace Module.Basis

open TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]

/-- The complex orientation of the determinant line is the ray of `b₀ ∧ I • b₀ ∧ b₁ ∧ ⋯` for every
complex basis `b`. -/
theorem complexDetLineRay_eq (b : Basis (Fin (finrank ℂ E)) ℂ E) :
    complexDetLineRay E = rayOfNeZero ℝ (ιMulti ℝ _ b.complexToRealFin)
      ((ιMulti_ne_zero_iff _).2 b.complexToRealFin.linearIndependent) := by
  rw [complexDetLineRay, ray_eq_iff, b.complexToRealFin.exteriorPower_ιMulti_eq_det_smul,
    det_complexToRealFin]
  exact SameRay.sameRay_pos_smul_left _
    (Complex.normSq_pos.mpr (b.isUnit_det _).ne_zero)

end Module.Basis

namespace LinearEquiv

open TauCeti Complex

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]

/-- A complex-linear isomorphism carries the complex orientation of the determinant line to the
complex orientation. -/
theorem map_complexDetLineRay (g : E ≃ₗ[ℝ] F) (hg : ∀ x, g (I • x) = I • g x) :
    Module.Ray.map g.detLineCongr (complexDetLineRay E) = complexDetLineRay F := by
  rw [complexDetLineRay, complexDetLineRay, Module.Ray.map_apply, ray_eq_iff, detLineCongr_ιMulti,
    (finBasis ℂ F).complexToRealFin.exteriorPower_ιMulti_eq_det_smul]
  exact SameRay.sameRay_pos_smul_left _ (det_complexToRealFin_comp_pos g hg _ _)

/-- A conjugate-linear isomorphism carries the complex orientation of the determinant line to
`(-1) ^ n` times the complex orientation, `n = finrank ℂ E`. -/
theorem map_complexDetLineRay_eq_neg_one_pow_smul (g : E ≃ₗ[ℝ] F)
    (hg : ∀ x, g (I • x) = -(I • g x)) :
    Module.Ray.map g.detLineCongr (complexDetLineRay E) =
      (-1 : ℝˣ) ^ finrank ℂ E • complexDetLineRay F := by
  rw [complexDetLineRay, complexDetLineRay, Module.Ray.map_apply, smul_rayOfNeZero, ray_eq_iff,
    detLineCongr_ιMulti, (finBasis ℂ F).complexToRealFin.exteriorPower_ιMulti_eq_det_smul]
  exact sameRay_smul_neg_one_pow_smul (neg_one_pow_mul_det_complexToRealFin_comp_pos g hg _ _) _

end LinearEquiv

namespace LinearMap

open TauCeti Complex TensorProduct

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (f : M →ₗ[ℂ] N)

/-- `Submodule.restrictScalarsEquiv` for the kernel, with its target written as the kernel of the
underlying real-linear map, the form in which `LinearMap.detLine` uses it. -/
private def kerRestrictScalarsEquiv : ker f ≃ₗ[ℝ] ker (f.restrictScalars ℝ) :=
  ((ker f).restrictScalarsEquiv ℝ).symm.restrictScalars ℝ

/-- The cokernel of a complex-linear map, with its real structure, is the cokernel of the
underlying real-linear map. -/
def cokerRestrictScalarsEquiv : (N ⧸ range (f.restrictScalars ℝ)) ≃ₗ[ℝ] N ⧸ range f :=
  (Submodule.quotEquivOfEq _ _ (range_restrictScalars f)).trans
    (Submodule.Quotient.restrictScalarsEquiv ℝ (range f))

@[simp]
theorem cokerRestrictScalarsEquiv_mk (y : N) :
    f.cokerRestrictScalarsEquiv (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

@[simp]
theorem cokerRestrictScalarsEquiv_symm_mk (y : N) :
    f.cokerRestrictScalarsEquiv.symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

/-! ### The complex orientation of the determinant line of a complex-linear map -/

section Ray

/-- The element `(b₀ ∧ I • b₀ ∧ b₁ ∧ ⋯) ⊗ (c₀ ∧ I • c₀ ∧ c₁ ∧ ⋯)^*` of the real determinant line
`det (ker f) ⊗ (det (coker f))^*` of a complex-linear map `f`, for complex bases `b` of the kernel
and `c` of the cokernel. Its second factor is the functional taking the value `1` on
`c₀ ∧ I • c₀ ∧ c₁ ∧ ⋯`. -/
def complexDetLineGen (b : Basis (Fin (finrank ℂ (ker f))) ℂ (ker f))
    (c : Basis (Fin (finrank ℂ (N ⧸ range f))) ℂ (N ⧸ range f)) :
    (f.restrictScalars ℝ).detLine :=
  f.kerRestrictScalarsEquiv.detLineCongr (ιMulti ℝ _ b.complexToRealFin) ⊗ₜ
    (alternatingMapLinearEquiv c.complexToRealFin.det ∘ₗ
      f.cokerRestrictScalarsEquiv.detLineCongr.toLinearMap)

/-- The generator is nonzero: it pairs to `1` against the product of the determinant functional
of `b` and evaluation at `c₀ ∧ I • c₀ ∧ c₁ ∧ ⋯`. -/
theorem complexDetLineGen_ne_zero (b : Basis (Fin (finrank ℂ (ker f))) ℂ (ker f))
    (c : Basis (Fin (finrank ℂ (N ⧸ range f))) ℂ (N ⧸ range f)) :
    f.complexDetLineGen b c ≠ 0 := by
  set ψ := alternatingMapLinearEquiv b.complexToRealFin.det ∘ₗ
    f.kerRestrictScalarsEquiv.detLineCongr.symm.toLinearMap
  set y := f.cokerRestrictScalarsEquiv.detLineCongr.symm (ιMulti ℝ _ c.complexToRealFin)
  intro h
  have := congrArg (TensorProduct.lift ((LinearMap.mul ℝ ℝ).compl₁₂ ψ (LinearMap.applyₗ y))) h
  simp only [complexDetLineGen, map_zero, lift.tmul, compl₁₂_apply, mul_apply',
    applyₗ_apply_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply, alternatingMapLinearEquiv_apply_ιMulti, Basis.det_self, ψ, y,
    mul_one, one_ne_zero] at this

/-- Changing the complex bases multiplies the generator by a positive real number. -/
theorem sameRay_complexDetLineGen (b b' : Basis (Fin (finrank ℂ (ker f))) ℂ (ker f))
    (c c' : Basis (Fin (finrank ℂ (N ⧸ range f))) ℂ (N ⧸ range f)) :
    SameRay ℝ (f.complexDetLineGen b' c') (f.complexDetLineGen b c) := by
  have hc : alternatingMapLinearEquiv c'.complexToRealFin.det =
      c'.complexToRealFin.det c.complexToRealFin • alternatingMapLinearEquiv
        c.complexToRealFin.det := by
    rw [← map_smul, ← c'.complexToRealFin.det.eq_smul_basis_det c.complexToRealFin]
  rw [complexDetLineGen, complexDetLineGen, b.complexToRealFin.exteriorPower_ιMulti_eq_det_smul,
    hc, map_smul, LinearMap.smul_comp, smul_tmul_smul, Basis.det_complexToRealFin,
    Basis.det_complexToRealFin]
  exact SameRay.sameRay_pos_smul_left _ (mul_pos
    (Complex.normSq_pos.mpr (b.isUnit_det _).ne_zero)
    (Complex.normSq_pos.mpr (c'.isUnit_det _).ne_zero))

variable [FiniteDimensional ℂ (ker f)] [FiniteDimensional ℂ (N ⧸ range f)]

/-- The **complex orientation** of the real determinant line of a complex-linear map `f` with
finite-dimensional kernel and cokernel: the ray of
`(b₀ ∧ I • b₀ ∧ ⋯) ⊗ (c₀ ∧ I • c₀ ∧ ⋯)^*` for any complex bases `b` of the kernel and `c` of the
cokernel (`LinearMap.complexDetLineRay_eq`). -/
def complexDetLineRay : Module.Ray ℝ (f.restrictScalars ℝ).detLine :=
  rayOfNeZero ℝ _ (f.complexDetLineGen_ne_zero (finBasis ℂ _) (finBasis ℂ _))

/-- The complex orientation of the determinant line of `f` is the ray of the generator
`LinearMap.complexDetLineGen` of any complex bases of the kernel and the cokernel. -/
theorem complexDetLineRay_eq (b : Basis (Fin (finrank ℂ (ker f))) ℂ (ker f))
    (c : Basis (Fin (finrank ℂ (N ⧸ range f))) ℂ (N ⧸ range f)) :
    f.complexDetLineRay = rayOfNeZero ℝ _ (f.complexDetLineGen_ne_zero b c) :=
  (ray_eq_iff _ _).2 (f.sameRay_complexDetLineGen _ _ _ _)

end Ray

/-! ### Transport along commuting squares -/

section Transport

variable {M' N' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N'] {f' : M' →ₗ[ℂ] N'}
  (e₁ : M ≃ₗ[ℝ] M') (e₂ : N ≃ₗ[ℝ] N')
  (h : f'.restrictScalars ℝ ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars ℝ)

/-- The isomorphism of complex kernels induced by a commuting square of real isomorphisms. -/
private def kerCongrOfComp : ker f ≃ₗ[ℝ] ker f' :=
  f.kerRestrictScalarsEquiv.trans ((e₁.ofSubmodules _ _
    ((f.restrictScalars ℝ).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
      f'.kerRestrictScalarsEquiv.symm)

private theorem coe_kerCongrOfComp_apply (x : ker f) :
    (kerCongrOfComp f e₁ e₂ h x : M') = e₁ x :=
  rfl

private theorem kerCongrOfComp_I_smul {s : ℂ} (he₁ : ∀ x, e₁ (I • x) = s • e₁ x) (x : ker f) :
    kerCongrOfComp f e₁ e₂ h (I • x) = s • kerCongrOfComp f e₁ e₂ h x :=
  Subtype.ext (by simp [coe_kerCongrOfComp_apply, he₁])

/-- The isomorphism of complex cokernels induced by a commuting square of real isomorphisms. -/
private def cokerCongrOfComp : (N ⧸ range f) ≃ₗ[ℝ] N' ⧸ range f' :=
  f.cokerRestrictScalarsEquiv.symm.trans ((Submodule.Quotient.equiv _ _ e₂
    ((f.restrictScalars ℝ).map_range_eq_range_of_comp_eq e₁.surjective h)).trans
      f'.cokerRestrictScalarsEquiv)

private theorem cokerCongrOfComp_mk (y : N) :
    cokerCongrOfComp f e₁ e₂ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e₂ y) :=
  rfl

private theorem cokerCongrOfComp_symm_I_smul {s : ℂ} (hs : s = I ∨ s = -I)
    (he₂ : ∀ y, e₂ (I • y) = s • e₂ y) (z : N' ⧸ range f') :
    (cokerCongrOfComp f e₁ e₂ h).symm (I • z) = s • (cokerCongrOfComp f e₁ e₂ h).symm z := by
  have hg (y : N ⧸ range f) : cokerCongrOfComp f e₁ e₂ h (I • y) =
      s • cokerCongrOfComp f e₁ e₂ h y := by
    induction y using Submodule.Quotient.induction_on with
    | H y => rw [← Submodule.Quotient.mk_smul, cokerCongrOfComp_mk, cokerCongrOfComp_mk, he₂,
        Submodule.Quotient.mk_smul]
  rw [LinearEquiv.symm_apply_eq]
  rcases hs with rfl | rfl
  · rw [hg, LinearEquiv.apply_symm_apply]
  · rw [neg_smul, map_neg, hg, LinearEquiv.apply_symm_apply, neg_smul, neg_neg]

/-- The transport of the generator along a commuting square is a multiple of the generator, by
the product of a kernel determinant and a cokernel determinant. -/
private theorem detLineCongr_complexDetLineGen
    (b : Basis (Fin (finrank ℂ (ker f))) ℂ (ker f))
    (c : Basis (Fin (finrank ℂ (N ⧸ range f))) ℂ (N ⧸ range f))
    (b' : Basis (Fin (finrank ℂ (ker f'))) ℂ (ker f'))
    (c' : Basis (Fin (finrank ℂ (N' ⧸ range f'))) ℂ (N' ⧸ range f')) :
    (f.restrictScalars ℝ).detLineCongr e₁ e₂ h (f.complexDetLineGen b c) =
      (b'.complexToRealFin.det (kerCongrOfComp f e₁ e₂ h ∘ b.complexToRealFin ∘
          Fin.cast (kerCongrOfComp f e₁ e₂ h).finrank_eq.symm) *
        c.complexToRealFin.det ((cokerCongrOfComp f e₁ e₂ h).symm ∘ c'.complexToRealFin ∘
          Fin.cast (cokerCongrOfComp f e₁ e₂ h).symm.finrank_eq.symm)) •
      f'.complexDetLineGen b' c' := by
  set g₁ := kerCongrOfComp f e₁ e₂ h
  set g₂ := cokerCongrOfComp f e₁ e₂ h
  have hk : f.kerRestrictScalarsEquiv.trans (e₁.ofSubmodules _ _
      ((f.restrictScalars ℝ).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)) =
      g₁.trans f'.kerRestrictScalarsEquiv :=
    LinearEquiv.ext fun _ ↦ rfl
  have hq : (Submodule.Quotient.equiv _ _ e₂
      ((f.restrictScalars ℝ).map_range_eq_range_of_comp_eq e₁.surjective h)).symm.trans
        f.cokerRestrictScalarsEquiv = f'.cokerRestrictScalarsEquiv.trans g₂.symm := by
    refine LinearEquiv.ext fun y ↦ ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.eq_symm_apply]
      obtain ⟨z, rfl⟩ := e₂.surjective y
      rw [Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply,
        Submodule.mapQ_apply, cokerRestrictScalarsEquiv_mk, cokerRestrictScalarsEquiv_mk,
        cokerCongrOfComp_mk]
      simp
  -- The cokernel functional, pulled back along `g₂⁻¹`, is a multiple of that of `c'`.
  have hφ : alternatingMapLinearEquiv c.complexToRealFin.det ∘ₗ
      g₂.symm.detLineCongr.toLinearMap =
      c.complexToRealFin.det (g₂.symm ∘ c'.complexToRealFin ∘ Fin.cast g₂.symm.finrank_eq.symm) •
        alternatingMapLinearEquiv c'.complexToRealFin.det := by
    refine exteriorPower.linearMap_ext ?_
    rw [((alternatingMapLinearEquiv c.complexToRealFin.det ∘ₗ
      g₂.symm.detLineCongr.toLinearMap).compAlternatingMap (ιMulti ℝ _)).eq_smul_basis_det
        c'.complexToRealFin]
    ext v
    simp
  rw [complexDetLineGen, detLineCongr_tmul, ← LinearEquiv.trans_apply,
    ← LinearEquiv.detLineCongr_trans, hk, LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    LinearEquiv.detLineCongr_ιMulti, b'.complexToRealFin.exteriorPower_ιMulti_eq_det_smul,
    map_smul, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.detLineCongr_symm,
    ← LinearEquiv.detLineCongr_trans, hq, LinearEquiv.detLineCongr_trans, LinearEquiv.coe_trans,
    ← LinearMap.comp_assoc, hφ, LinearMap.smul_comp, smul_tmul_smul, complexDetLineGen]

variable [FiniteDimensional ℂ (ker f)] [FiniteDimensional ℂ (N ⧸ range f)]
  [FiniteDimensional ℂ (ker f')] [FiniteDimensional ℂ (N' ⧸ range f')]

/-- Transport along a commuting square of complex-linear isomorphisms carries the complex
orientation of the determinant line of `f` to that of `f'`. -/
theorem map_detLineCongr_complexDetLineRay (he₁ : ∀ x, e₁ (I • x) = I • e₁ x)
    (he₂ : ∀ y, e₂ (I • y) = I • e₂ y) :
    Module.Ray.map ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h) f.complexDetLineRay =
      f'.complexDetLineRay := by
  rw [complexDetLineRay, Module.Ray.map_apply, f'.complexDetLineRay_eq (finBasis ℂ _)
    (finBasis ℂ _), ray_eq_iff, detLineCongr_complexDetLineGen _ _ _ _ _ _ (finBasis ℂ _)
    (finBasis ℂ _)]
  exact SameRay.sameRay_pos_smul_left _ (mul_pos
    (det_complexToRealFin_comp_pos _ (kerCongrOfComp_I_smul f e₁ e₂ h he₁) _ _)
    (det_complexToRealFin_comp_pos _
      (cokerCongrOfComp_symm_I_smul f e₁ e₂ h (.inl rfl) he₂) _ _))

/-- **The determinant sign of a conjugate-linear transport.** Transport along a commuting square
of conjugate-linear isomorphisms carries the complex orientation of the determinant line of `f`
to `(-1) ^ (k + c)` times that of `f'`, where `k` and `c` are the complex dimensions of the kernel
and the cokernel of `f`. The sign is `(-1)` to the complex index `k - c`. -/
theorem map_detLineCongr_complexDetLineRay_eq_neg_one_pow_smul
    (he₁ : ∀ x, e₁ (I • x) = -(I • e₁ x)) (he₂ : ∀ y, e₂ (I • y) = -(I • e₂ y)) :
    Module.Ray.map ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h) f.complexDetLineRay =
      (-1 : ℝˣ) ^ (finrank ℂ (ker f) + finrank ℂ (N ⧸ range f)) • f'.complexDetLineRay := by
  have he₁' (x : M) : e₁ (I • x) = (-I) • e₁ x := by rw [he₁, neg_smul]
  have he₂' (y : N) : e₂ (I • y) = (-I) • e₂ y := by rw [he₂, neg_smul]
  have hk := neg_one_pow_mul_det_complexToRealFin_comp_pos _
    (fun x ↦ by rw [kerCongrOfComp_I_smul f e₁ e₂ h he₁' x, neg_smul]) (finBasis ℂ _)
    (finBasis ℂ (ker f'))
  have hc := neg_one_pow_mul_det_complexToRealFin_comp_pos _
    (fun x ↦ by rw [cokerCongrOfComp_symm_I_smul f e₁ e₂ h (.inr rfl) he₂' x, neg_smul])
    (finBasis ℂ _) (finBasis ℂ (N ⧸ range f))
  rw [(cokerCongrOfComp f e₁ e₂ h).symm.finrank_complex_eq] at hc
  rw [complexDetLineRay, Module.Ray.map_apply, f'.complexDetLineRay_eq (finBasis ℂ _)
    (finBasis ℂ _), smul_rayOfNeZero, ray_eq_iff, detLineCongr_complexDetLineGen _ _ _ _ _ _
    (finBasis ℂ _) (finBasis ℂ _)]
  have hpos := mul_pos hk hc
  rw [mul_mul_mul_comm, ← pow_add] at hpos
  exact sameRay_smul_neg_one_pow_smul hpos (f'.complexDetLineGen (finBasis ℂ _) (finBasis ℂ _))

end Transport

end LinearMap
