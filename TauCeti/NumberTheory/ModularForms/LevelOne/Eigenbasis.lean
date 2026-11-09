/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
public import TauCeti.LinearAlgebra.Trace.Submodule
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
public import TauCeti.NumberTheory.ModularForms.LevelOne.Hecke
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner
import TauCeti.NumberTheory.ModularForms.FiniteDimensional
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientCriterion

/-!
# The Hecke eigenbasis and Eisenstein eigenform at level one

At level one, the congruence subgroup `(Gamma1 1).map (mapGL ℝ)` equals the full modular group `𝒮ℒ`
(`Gamma1_one_map_eq_SL`), there are no oldforms (`cuspFormsNew_one`), and `(ZMod 1)ˣ` is trivial,
so every form has trivial nebentypus. Transporting the Atkin–Lehner–Miyake–Li newform basis
`HeckeRing.GL2.Newform.basis 1 k` along this group equality equips `CuspForm 𝒮ℒ k` with a canonical
basis `levelOneNewformBasis k` indexed by `Newform 1 k`.

Because the level-one Hecke operators `heckeTLevelOne` and `heckeTCuspLevelOne` share the positive
Fourier-coefficient divisor-sum formula with the composite Hecke-ring elements
`heckeTCompositeGamma0 1 n` acting at trivial character, the two actions agree across
`modularFormGamma1OneEquiv` (for `k ≠ 0`) and `cuspFormGamma1OneEquiv` (at every weight). From this
comparison we obtain:

* commutativity of the level-one Hecke operators `heckeTCuspLevelOne` and `heckeTLevelOne`;
* simultaneous diagonalization of `heckeTCuspLevelOne k n` on `levelOneNewformBasis k`, with
  eigenvalue the `n`-th Fourier coefficient `(qExpansion 1 f.toCuspForm).coeff n`, and the trace
  formula `Tr(Tₙ | S_k) = ∑_{f ∈ Newform 1 k} aₙ(f)`;
* separation of coordinates in any subspace of `CuspForm 𝒮ℒ k` stable under `Tₚ` for every prime
  `p` (`levelOneNewformBasis_mem_of_forall_prime`), combining multiplicity one at level one with
  `Module.Basis.self_mem_of_repr_ne_zero_of_forall`, and the resulting prime-Hecke injectivity
  criterion `injective_of_heckeTCuspLevelOne_mem_ker`;
* the Hecke eigenform equation `Tₙ(E_k) = σ_{k-1}(n) E_k` for the normalized Eisenstein series
  `ModularForm.E hk` at even weight `k ≥ 4` (`heckeTLevelOne_E`), deduced from the multiplicativity
  and prime-power recurrence of `σ_{k-1}` via `forall_heckeTCompositeGamma0_eq_coeff_smul_iff`,
  together with the direct-sum decomposition `M_k(SL(2, ℤ)) = S_k(SL(2, ℤ)) ⊕ ℂ · E_k` and the
  resulting trace identity `Tr(Tₙ | M_k) = Tr(Tₙ | S_k) + σ_{k-1}(n)`.

## Main definitions

* `TauCeti.modularFormGamma1OneEquiv`, `TauCeti.cuspFormGamma1OneEquiv`: the `ℂ`-linear
  equivalences `M_k(Γ₁(1)) ≃ₗ[ℂ] M_k(SL(2, ℤ))` and `S_k(Γ₁(1)) ≃ₗ[ℂ] S_k(SL(2, ℤ))` preserving
  underlying functions on `ℍ`.
* `TauCeti.levelOneNewformBasis`: the basis of `CuspForm 𝒮ℒ k` indexed by `Newform 1 k`.

## Main results

* `TauCeti.heckeTCuspLevelOne_cuspFormGamma1OneEquiv`,
  `TauCeti.heckeTLevelOne_modularFormGamma1OneEquiv`: compatibility of `heckeTCuspLevelOne` and
  `heckeTLevelOne` with `heckeTCompositeGamma0 1 n`.
* `TauCeti.commute_heckeTCuspLevelOne`, `TauCeti.commute_heckeTLevelOne`: level-one Hecke operators
  commute.
* `HeckeRing.GL2.Newform.twelve_le_weight`, `TauCeti.heckeTCuspLevelOne_levelOneNewformBasis`,
  `TauCeti.trace_heckeTCuspLevelOne`, `TauCeti.levelOneNewformBasis_mem_of_forall_prime`,
  `TauCeti.injective_of_heckeTCuspLevelOne_mem_ker`: the weight bound `12 ≤ k` on level-one
  newforms, eigenbasis action, trace, prime-Hecke invariant-subspace coordinate extraction, and
  injectivity criterion on `CuspForm 𝒮ℒ k`.
* `TauCeti.heckeTLevelOne_E`, `TauCeti.isCompl_cuspFormSubmodule_span_E`,
  `TauCeti.trace_heckeTLevelOne`: the Eisenstein Hecke eigenvalue, the cusp/Eisenstein complement,
  and the trace of `Tₙ` on `ModularForm 𝒮ℒ k`.

## References

* [J.-P. Serre, *A course in arithmetic*][serre1973], Chapter VII, §§4–5.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.2.3, 5.3.1, and 5.8.5, and Theorem 5.8.2.
-/

public noncomputable section

open CongruenceSubgroup EisensteinSeries HeckeRing.GL2 Matrix.SpecialLinearGroup ModularForm
  UpperHalfPlane
open scoped ArithmeticFunction.sigma MatrixGroups ModularForm

namespace TauCeti

/-! ### Re-reading `Γ₁(1)` forms as `SL(2, ℤ)` forms -/

/-- **Modular forms for `Γ₁(1)` and for `SL(2, ℤ)` are canonically linearly isomorphic**, via the
subgroup equality `Gamma1_one_map_eq_SL`, without changing the underlying function on `ℍ`. -/
def modularFormGamma1OneEquiv (k : ℤ) :
    ModularForm ((Gamma1 1).map (mapGL ℝ)) k ≃ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun f := f.copy f rfl Gamma1_one_map_eq_SL.symm
  map_add' _ _ := ModularForm.ext fun _ ↦ rfl
  map_smul' _ _ := ModularForm.ext fun _ ↦ rfl
  invFun f := f.copy f rfl Gamma1_one_map_eq_SL
  left_inv _ := ModularForm.ext fun _ ↦ rfl
  right_inv _ := ModularForm.ext fun _ ↦ rfl

/-- `modularFormGamma1OneEquiv` preserves the underlying function on `ℍ`. -/
@[simp]
theorem _root_.ModularForm.coe_modularFormGamma1OneEquiv_apply {k : ℤ}
    (f : ModularForm ((Gamma1 1).map (mapGL ℝ)) k) :
    ⇑(modularFormGamma1OneEquiv k f) = ⇑f := (rfl)

/-- The inverse of `modularFormGamma1OneEquiv` preserves the underlying function on `ℍ`. -/
@[simp]
theorem _root_.ModularForm.coe_modularFormGamma1OneEquiv_symm_apply {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ⇑((modularFormGamma1OneEquiv k).symm f) = ⇑f := (rfl)

/-- **Cusp forms for `Γ₁(1)` and for `SL(2, ℤ)` are canonically linearly isomorphic**, via the
subgroup equality `Gamma1_one_map_eq_SL`, without changing the underlying function on `ℍ`. -/
def cuspFormGamma1OneEquiv (k : ℤ) :
    CuspForm ((Gamma1 1).map (mapGL ℝ)) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun f := f.copy f rfl Gamma1_one_map_eq_SL.symm
  map_add' _ _ := CuspForm.ext fun _ ↦ rfl
  map_smul' _ _ := CuspForm.ext fun _ ↦ rfl
  invFun f := f.copy f rfl Gamma1_one_map_eq_SL
  left_inv _ := CuspForm.ext fun _ ↦ rfl
  right_inv _ := CuspForm.ext fun _ ↦ rfl

/-- `cuspFormGamma1OneEquiv` preserves the underlying function on `ℍ`. -/
@[simp]
theorem _root_.CuspForm.coe_cuspFormGamma1OneEquiv_apply {k : ℤ}
    (f : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) :
    ⇑(cuspFormGamma1OneEquiv k f) = ⇑f := (rfl)

/-- The inverse of `cuspFormGamma1OneEquiv` preserves the underlying function on `ℍ`. -/
@[simp]
theorem _root_.CuspForm.coe_cuspFormGamma1OneEquiv_symm_apply {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    ⇑((cuspFormGamma1OneEquiv k).symm f) = ⇑f := (rfl)

/-- Every `Γ₁(1)` modular form lies in the trivial-character subspace `M_k(Γ₁(1), 1)`. -/
theorem _root_.ModularForm.mem_modFormCharSpace_one_level_one {k : ℤ}
    (F : ModularForm ((Gamma1 1).map (mapGL ℝ)) k) :
    F ∈ modFormCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) :=
  (mem_modFormCharSpace_one_iff_diamondOp F).mpr fun d ↦ by simp [Subsingleton.elim d 1]

/-- Every `Γ₁(1)` cusp form lies in the trivial-character subspace `S_k(Γ₁(1), 1)`. -/
theorem _root_.CuspForm.mem_cuspFormCharSpace_one_level_one {k : ℤ}
    (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) :
    F ∈ cuspFormCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) :=
  (mem_cuspFormCharSpace_one_iff_diamondOpCusp F).mpr fun d ↦ by simp [Subsingleton.elim d 1]

/-- At level one every modular form has trivial nebentypus. -/
@[simp]
theorem modFormCharSpace_one_level_one (k : ℤ) :
    modFormCharSpace (N := 1) k (1 : (ZMod 1)ˣ →* ℂˣ) = ⊤ :=
  eq_top_iff.mpr fun F _ ↦ F.mem_modFormCharSpace_one_level_one

/-- At level one every cusp form has trivial nebentypus. -/
@[simp]
theorem cuspFormCharSpace_one_level_one (k : ℤ) :
    cuspFormCharSpace (N := 1) k (1 : (ZMod 1)ˣ →* ℂˣ) = ⊤ :=
  eq_top_iff.mpr fun F _ ↦ F.mem_cuspFormCharSpace_one_level_one

/-! ### Compatibility of `heckeTLevelOne` and `heckeTCuspLevelOne` with `heckeTCompositeGamma0 1` -/

/-- **Compatibility of `heckeTCuspLevelOne` with the composite `Γ₀(1)` Hecke action.** Across
`cuspFormGamma1OneEquiv`, `heckeTCuspLevelOne k n` agrees with `heckeTCompositeGamma0 1 n` acting on
`S_k(Γ₁(1), 1)`: both have the same Fourier-coefficient divisor-sum formula at every index. -/
theorem heckeTCuspLevelOne_cuspFormGamma1OneEquiv (k : ℤ) (n : ℕ) [NeZero n]
    (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) :
    heckeTCuspLevelOne k n (cuspFormGamma1OneEquiv k F) =
      cuspFormGamma1OneEquiv k
        (heckeRingHomCuspCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) (heckeTCompositeGamma0 1 n)
          ⟨F, F.mem_cuspFormCharSpace_one_level_one⟩) := by
  apply CuspForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  ext m
  dsimp only
  rw [qExpansion_coeff_heckeTCuspLevelOne, CuspForm.coe_cuspFormGamma1OneEquiv_apply,
    CuspForm.coe_cuspFormGamma1OneEquiv_apply,
    qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 (NeZero.ne n)]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [DirichletCharacter.level_one (MulChar.ofUnitHom 1),
    MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- **Compatibility of `heckeTLevelOne` with the composite `Γ₀(1)` Hecke action** at nonzero weight:
both operators have the same positive Fourier coefficients, which determine a modular form when
`k ≠ 0`. -/
theorem heckeTLevelOne_modularFormGamma1OneEquiv {k : ℤ} (hk : k ≠ 0) (n : ℕ) [NeZero n]
    (F : ModularForm ((Gamma1 1).map (mapGL ℝ)) k) :
    heckeTLevelOne k n (modularFormGamma1OneEquiv k F) =
      modularFormGamma1OneEquiv k
        (heckeRingHomCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) (heckeTCompositeGamma0 1 n)
          ⟨F, F.mem_modFormCharSpace_one_level_one⟩) := by
  apply TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos one_mem_strictPeriods_SL hk
  intro m hm
  rw [qExpansion_coeff_heckeTLevelOne, _root_.ModularForm.coe_modularFormGamma1OneEquiv_apply,
    _root_.ModularForm.coe_modularFormGamma1OneEquiv_apply,
    qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero (NeZero.ne n) _ hm.ne']
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [DirichletCharacter.level_one (MulChar.ofUnitHom 1),
    MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

private theorem heckeTCompositeGamma0_level_one_comm (m n : ℕ) :
    heckeTCompositeGamma0 1 m * heckeTCompositeGamma0 1 n =
      heckeTCompositeGamma0 1 n * heckeTCompositeGamma0 1 m :=
  HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution 1)
    (atkinLehnerAntiInvolution_onHeckeCoset_eq_self 1) _ _

/-- **Level-one Hecke operators on cusp forms commute.** -/
theorem commute_heckeTCuspLevelOne (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    Commute (heckeTCuspLevelOne k m) (heckeTCuspLevelOne k n) := by
  rw [commute_iff_eq]
  ext f z
  obtain ⟨F, rfl⟩ := (cuspFormGamma1OneEquiv k).surjective f
  have hcomm := congrArg
    (fun T ↦ ((heckeRingHomCuspCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) T
      ⟨F, F.mem_cuspFormCharSpace_one_level_one⟩ : cuspFormCharSpace k _) :
        CuspForm ((Gamma1 1).map (mapGL ℝ)) k))
    (heckeTCompositeGamma0_level_one_comm m n)
  simp only [map_mul, mul_apply_eq_comp] at hcomm
  rw [mul_apply_eq_comp, mul_apply_eq_comp, heckeTCuspLevelOne_cuspFormGamma1OneEquiv,
    heckeTCuspLevelOne_cuspFormGamma1OneEquiv, heckeTCuspLevelOne_cuspFormGamma1OneEquiv,
    heckeTCuspLevelOne_cuspFormGamma1OneEquiv]
  exact congrArg (fun G ↦ cuspFormGamma1OneEquiv k G z) hcomm

/-- **Level-one Hecke operators on modular forms commute.** -/
theorem commute_heckeTLevelOne (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    Commute (heckeTLevelOne k m) (heckeTLevelOne k n) := by
  rw [commute_iff_eq]
  rcases eq_or_ne k 0 with rfl | hk
  · -- At weight `0` every level-one modular form is constant, so its positive `q`-coefficients
    -- vanish and `Tₙ` acts by multiplying the constant term by `∑_{d ∣ n} d⁻¹`.
    apply LinearMap.ext fun f ↦ _root_.ModularForm.qExpansion_injective one_pos
      one_mem_strictPeriods_SL ?_
    ext j
    rcases eq_or_ne j 0 with rfl | hj
    · simp only [mul_apply_eq_comp, qExpansion_coeff_zero_heckeTLevelOne]
      ring
    · have hzero (g : ModularForm 𝒮ℒ 0) : (qExpansion 1 g).coeff j = 0 := by
        by_contra hne
        exact TauCeti.ModularForm.weight_ne_zero_of_pos_qExpansion_coeff_ne_zero one_pos
          one_mem_strictPeriods_SL (Nat.pos_of_ne_zero hj) hne rfl
      rw [hzero, hzero]
  · ext f z
    obtain ⟨F, rfl⟩ := (modularFormGamma1OneEquiv k).surjective f
    have hcomm := congrArg
       (fun T ↦ ((heckeRingHomCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) T
        ⟨F, F.mem_modFormCharSpace_one_level_one⟩ : modFormCharSpace k _) :
          ModularForm ((Gamma1 1).map (mapGL ℝ)) k))
      (heckeTCompositeGamma0_level_one_comm m n)
    simp only [map_mul, mul_apply_eq_comp] at hcomm
    rw [mul_apply_eq_comp, mul_apply_eq_comp, heckeTLevelOne_modularFormGamma1OneEquiv hk,
      heckeTLevelOne_modularFormGamma1OneEquiv hk, heckeTLevelOne_modularFormGamma1OneEquiv hk,
      heckeTLevelOne_modularFormGamma1OneEquiv hk]
    exact congrArg (fun G ↦ modularFormGamma1OneEquiv k G z) hcomm

/-! ### The newform eigenbasis of `CuspForm 𝒮ℒ k` -/

/-- **The canonical basis of `S_k(SL(2, ℤ))` consisting of normalized Hecke eigenforms**, obtained
by transporting `HeckeRing.GL2.Newform.basis 1 k` along `cuspFormsNew_one` and
`cuspFormGamma1OneEquiv`. -/
def levelOneNewformBasis (k : ℤ) : Module.Basis (Newform 1 k) ℂ (CuspForm 𝒮ℒ k) :=
  (Newform.basis 1 k).map
    ((LinearEquiv.ofTop _ (cuspFormsNew_one k)).trans (cuspFormGamma1OneEquiv k))

/-- At a newform `f`, the basis vector `levelOneNewformBasis k f` has the same underlying function
on `ℍ` as `f.toCuspForm`. -/
@[simp]
theorem coe_levelOneNewformBasis_apply (k : ℤ) (f : Newform 1 k) :
    ⇑(levelOneNewformBasis k f) = ⇑f.toCuspForm := by
  simp [levelOneNewformBasis]

/-- `cuspFormGamma1OneEquiv` carries `f.toCuspForm` to `levelOneNewformBasis k f`. -/
@[simp]
theorem cuspFormGamma1OneEquiv_toCuspForm (k : ℤ) (f : Newform 1 k) :
    cuspFormGamma1OneEquiv k f.toCuspForm = levelOneNewformBasis k f := by
  ext z
  simp

/-- Every level-one newform has weight `k ≥ 12`, since `S_k(SL(2, ℤ)) = 0` for `k < 12`. -/
theorem _root_.HeckeRing.GL2.Newform.twelve_le_weight {k : ℤ} (f : Newform 1 k) : 12 ≤ k := by
  by_contra! hk
  have hne : levelOneNewformBasis k f ≠ 0 := (levelOneNewformBasis k).ne_zero f
  have hzero : Module.rank ℂ (CuspForm 𝒮ℒ k) = 0 := CuspForm.rank_eq_zero_of_weight_lt_twelve hk
  exact hne (rank_zero_iff_forall_zero.mp hzero _)

/-- **Each basis vector of `levelOneNewformBasis k` is an eigenform of every `heckeTCuspLevelOne`**,
with eigenvalue equal to its `n`-th Fourier coefficient. -/
theorem heckeTCuspLevelOne_levelOneNewformBasis (k : ℤ) (n : ℕ) [NeZero n] (f : Newform 1 k) :
    heckeTCuspLevelOne k n (levelOneNewformBasis k f) =
      (qExpansion 1 f.toCuspForm).coeff n • levelOneNewformBasis k f := by
  rw [← cuspFormGamma1OneEquiv_toCuspForm, heckeTCuspLevelOne_cuspFormGamma1OneEquiv]
  have key : ∀ (χ : (ZMod 1)ˣ →* ℂˣ) (hF : f.toCuspForm ∈ cuspFormCharSpace k χ),
      ((heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 1 n) ⟨f.toCuspForm, hF⟩ :
        cuspFormCharSpace k χ) : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) =
        (qExpansion 1 f.toCuspForm).coeff n • f.toCuspForm := by
    intro χ hF
    obtain rfl : χ = f.χ := Subsingleton.elim _ _
    have hval := f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm
      ⟨n, Nat.pos_of_neZero n⟩ (Nat.coprime_one_right n)
    simp only [PNat.mk_coe] at hval
    rw [hval]
    exact congrArg Subtype.val (f.isEigen ⟨n, Nat.pos_of_neZero n⟩ (Nat.coprime_one_right n))
  rw [key _ _, map_smul]

/-- **The trace of `Tₙ` on `S_k(SL(2, ℤ))` is the sum of the `n`-th Fourier coefficients of the
level-one newforms.** -/
theorem trace_heckeTCuspLevelOne (k : ℤ) (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ (CuspForm 𝒮ℒ k) (heckeTCuspLevelOne k n) =
      ∑ᶠ f : Newform 1 k, (qExpansion 1 f.toCuspForm).coeff n := by
  classical
  let : Fintype (Newform 1 k) := Fintype.ofFinite (Newform 1 k)
  rw [finsum_eq_sum_of_fintype, LinearMap.trace_eq_matrix_trace ℂ (levelOneNewformBasis k)]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  simp [LinearMap.toMatrix_apply, heckeTCuspLevelOne_levelOneNewformBasis]

/-- **Prime-Hecke invariant subspaces of `S_k(SL(2, ℤ))` contain every newform occurring in their
elements.** Two distinct level-one newforms differ in their eigenvalue at some prime (strong
multiplicity one, `Newform.eq_of_forall_prime_eigenvalue_eq`), so the joint prime-Hecke weights on
`levelOneNewformBasis k` are injective and `Module.Basis.self_mem_of_repr_ne_zero_of_forall`
clears extra coordinates. -/
theorem levelOneNewformBasis_mem_of_forall_prime {k : ℤ} {W : Submodule ℂ (CuspForm 𝒮ℒ k)}
    (hW : ∀ p : Nat.Primes, ∀ g ∈ W, heckeTCuspLevelOne k p.1 g ∈ W) {g : CuspForm 𝒮ℒ k}
    (hg : g ∈ W) {f : Newform 1 k} (hf : (levelOneNewformBasis k).repr g f ≠ 0) :
    levelOneNewformBasis k f ∈ W := by
  let a (f₀ : Newform 1 k) (p : Nat.Primes) : ℂ := (qExpansion 1 f₀.toCuspForm).coeff p.1
  have hdiag (f₀ : Newform 1 k) (p : Nat.Primes) :
      heckeTCuspLevelOne k p.1 (levelOneNewformBasis k f₀) =
        a f₀ p • levelOneNewformBasis k f₀ :=
    heckeTCuspLevelOne_levelOneNewformBasis k p.1 f₀
  have hinj : Function.Injective a := fun f₁ f₂ h ↦
    Newform.eq_of_forall_prime_eigenvalue_eq (Subsingleton.elim f₁.χ f₂.χ) fun p hp hp1 ↦ by
      rw [← f₁.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f₁.isNorm ⟨p, hp.pos⟩ hp1,
        ← f₂.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f₂.isNorm ⟨p, hp.pos⟩ hp1]
      exact congr_fun h ⟨p, hp⟩
  exact (levelOneNewformBasis k).self_mem_of_repr_ne_zero_of_forall hdiag hinj hW hg hf

/-- **Injectivity criterion on `S_k(SL(2, ℤ))` via prime Hecke operators.** A semilinear map out of
`CuspForm 𝒮ℒ k` whose kernel is stable under `heckeTCuspLevelOne k p` for every prime `p` and that
vanishes on no basis vector of `levelOneNewformBasis k` is injective. -/
theorem injective_of_heckeTCuspLevelOne_mem_ker {k : ℤ} {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] {φ : ℂ →+* R} {L : CuspForm 𝒮ℒ k →ₛₗ[φ] M}
    (hker : ∀ p : Nat.Primes, ∀ g ∈ LinearMap.ker L, heckeTCuspLevelOne k p.1 g ∈ LinearMap.ker L)
    (hbasis : ∀ f : Newform 1 k, L (levelOneNewformBasis k f) ≠ 0) :
    Function.Injective L := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  by_contra hne
  obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp
    ((map_ne_zero_iff _ (levelOneNewformBasis k).repr.injective).mpr hne)
  exact hbasis f (LinearMap.mem_ker.mp
    (levelOneNewformBasis_mem_of_forall_prime hker (LinearMap.mem_ker.mpr hg) hf))

/-! ### The normalized Eisenstein series as a Hecke eigenform -/

/-- The first Fourier coefficient of `ModularForm.E hk` at even weight `k ≥ 4` is nonzero:
all positive coefficients are multiples of it (`E_qExpansion_coeff`), and a nonzero modular form of
nonzero weight cannot have all positive Fourier coefficients equal to zero. -/
theorem qExpansion_coeff_one_E_ne_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (qExpansion 1 (ModularForm.E hk)).coeff 1 ≠ 0 := by
  intro h1
  rw [E_qExpansion_coeff hk hk2 1, ite_eq_right one_ne_zero, ArithmeticFunction.sigma_one,
    Nat.cast_one, mul_one] at h1
  refine E_ne_zero hk hk2 (TauCeti.ModularForm.eq_zero_of_forall_pos_qExpansion_coeff_eq_zero
    one_pos one_mem_strictPeriods_SL (by omega) fun m hm ↦ ?_)
  rw [E_qExpansion_coeff hk hk2 m, ite_eq_right hm.ne', h1, zero_mul]

/-- A level-one form `F` whose Fourier coefficients are `σ_{k-1}(m)` for `m ≥ 1` is an eigenvector
of the Hecke operator `Tₙ` on the trivial-character space, with eigenvalue `σ_{k-1}(n)`: the
coefficients are multiplicative and satisfy the prime-power recurrence. -/
private lemma heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul_of_coeff {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) [NeZero n] (F : modFormCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ))
    (hpos : ∀ {m : ℕ}, m ≠ 0 → (qExpansion 1 F.val).coeff m = (σ (k - 1) m : ℂ)) :
    heckeRingHomCharSpace (k : ℤ) (1 : (ZMod 1)ˣ →* ℂˣ)
      (heckeTCompositeGamma0 1 n) F = (σ (k - 1) n : ℂ) • F := by
  have h1 : (qExpansion 1 F.val).coeff 1 = 1 := by
    simpa [ArithmeticFunction.sigma_one] using hpos one_ne_zero
  rw [← hpos (NeZero.ne n)]
  refine (forall_heckeTCompositeGamma0_eq_coeff_smul_iff F h1).mpr ⟨?_, ?_⟩ n (NeZero.ne n)
  · intro u v huv
    rcases eq_or_ne u 0 with rfl | hu
    · obtain rfl := (Nat.coprime_zero_left v).mp huv
      rw [zero_mul, h1, mul_one]
    rcases eq_or_ne v 0 with rfl | hv
    · obtain rfl := (Nat.coprime_zero_right u).mp huv
      rw [mul_zero, h1, one_mul]
    rw [hpos (mul_ne_zero hu hv), hpos hu, hpos hv,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime huv, Nat.cast_mul]
  · intro p hp r
    have hk1 : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    have hs (m : ℕ) :
        (σ (k - 1) (p ^ (m + 1)) : ℂ) = (p : ℂ) ^ (k - 1) * σ (k - 1) (p ^ m) + 1 := by
      exact_mod_cast ArithmeticFunction.sigma_prime_pow_succ hp m
    have hp1 : (σ (k - 1) p : ℂ) = (p : ℂ) ^ (k - 1) + 1 := by
      simpa [ArithmeticFunction.sigma_one] using hs 0
    rw [hpos (pow_ne_zero _ hp.ne_zero), hpos hp.ne_zero, hpos (pow_ne_zero _ hp.ne_zero),
      hpos (pow_ne_zero _ hp.ne_zero), DirichletCharacter.level_one (MulChar.ofUnitHom 1),
      MulChar.one_apply (isUnit_of_subsingleton _), one_mul, hk1, zpow_natCast,
      hs (r + 1), hs r, hp1]
    ring

/-- **The normalized Eisenstein series `E_k` is a Hecke eigenform** with eigenvalue `σ_{k-1}(n)` at
every `n ≥ 1` (Serre, *A Course in Arithmetic*, VII.5.3; Diamond–Shurman, Proposition 5.2.3). -/
theorem heckeTLevelOne_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) [NeZero n] :
    heckeTLevelOne k n (ModularForm.E hk) =
      (σ (k - 1) n : ℂ) • ModularForm.E hk := by
  set c := (qExpansion 1 (ModularForm.E hk)).coeff 1
  have hc0 : c ≠ 0 := qExpansion_coeff_one_E_ne_zero hk hk2
  have hc_eq : c = -(2 * (k : ℂ) / bernoulli k) := by
    simpa [c, ArithmeticFunction.sigma_one] using E_qExpansion_coeff hk hk2 1
  -- Rescale `E_k` on `Γ₁(1)` so that its first Fourier coefficient is `1`; its `m`-th coefficient
  -- for `m ≥ 1` is then `σ_{k-1}(m)`.
  let G : ModularForm ((Gamma1 1).map (mapGL ℝ)) k :=
    c⁻¹ • (modularFormGamma1OneEquiv k).symm (ModularForm.E hk)
  let F : modFormCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) := ⟨G, G.mem_modFormCharSpace_one_level_one⟩
  have hpos {m : ℕ} (hm : m ≠ 0) : (qExpansion 1 F.val).coeff m = (σ (k - 1) m : ℂ) := by
    dsimp only [F]
    rw [FunLike.coe_smul,
      _root_.ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map 1),
      PowerSeries.coeff_smul, _root_.ModularForm.coe_modularFormGamma1OneEquiv_symm_apply,
      E_qExpansion_coeff hk hk2 m, ite_eq_right hm, ← hc_eq, smul_eq_mul, inv_mul_cancel_left₀ hc0]
  have heig := heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul_of_coeff (by omega) n F hpos
  have hG : modularFormGamma1OneEquiv k G = c⁻¹ • ModularForm.E hk := by
    simp [G]
  have hTG := heckeTLevelOne_modularFormGamma1OneEquiv (k := (k : ℤ)) (by omega) n G
  dsimp only [F] at heig
  rw [hG, map_smul, heig, Submodule.coe_smul, map_smul, hG] at hTG
  exact smul_right_injective _ (inv_ne_zero hc0) (hTG.trans (smul_comm _ _ _))

/-! ### The cusp/Eisenstein decomposition and trace of `Tₙ` on `ModularForm 𝒮ℒ k` -/

/-- **At even weight `k ≥ 4`, `M_k(SL(2, ℤ))` is the internal direct sum of `S_k(SL(2, ℤ))` and
`ℂ · E_k`.** -/
theorem isCompl_cuspFormSubmodule_span_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    IsCompl (ModularForm.cuspFormSubmodule 𝒮ℒ k) (ℂ ∙ ModularForm.E hk) := by
  refine ⟨Submodule.disjoint_def.mpr fun f hf hE ↦ ?_,
    codisjoint_iff.mpr (eq_top_iff.mpr fun f _ ↦ ?_)⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hE
    rw [ModularForm.mem_cuspFormSubmodule_iff, ModularForm.isCuspForm_iff_coeffZero_eq_zero,
      FunLike.coe_smul, _root_.ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_smul, E_qExpansion_coeff_zero hk hk2, smul_eq_mul, mul_one] at hf
    simp [hf]
  · exact Submodule.mem_sup.mpr
      ⟨f - (qExpansion 1 f).coeff 0 • ModularForm.E hk,
        ModularForm.sub_smul_isCuspForm f (ModularForm.E hk) (E_qExpansion_coeff_zero hk hk2),
        (qExpansion 1 f).coeff 0 • ModularForm.E hk,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩

/-- **The trace of `Tₙ` on `M_k(SL(2, ℤ))` at even weight `k ≥ 4`** is the cusp-form trace plus
`σ_{k-1}(n)`. -/
theorem trace_heckeTLevelOne {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ (ModularForm 𝒮ℒ k) (heckeTLevelOne k n) =
      LinearMap.trace ℂ (CuspForm 𝒮ℒ k) (heckeTCuspLevelOne k n) + (σ (k - 1) n : ℂ) := by
  have hA : ∀ f ∈ ModularForm.cuspFormSubmodule 𝒮ℒ (k : ℤ),
      heckeTLevelOne k n f ∈ ModularForm.cuspFormSubmodule 𝒮ℒ (k : ℤ) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨heckeTCuspLevelOne k n g, (heckeTLevelOne_coe_cuspForm k n g).symm⟩
  have hB : ∀ f ∈ (ℂ ∙ ModularForm.E hk),
      heckeTLevelOne k n f ∈ (ℂ ∙ ModularForm.E hk) := by
    intro f hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [map_smul, heckeTLevelOne_E hk hk2 n]
    exact (ℂ ∙ ModularForm.E hk).smul_mem a
      ((ℂ ∙ ModularForm.E hk).smul_mem _ (Submodule.mem_span_singleton_self _))
  rw [LinearMap.trace_eq_trace_restrict_add_trace_restrict
    (isCompl_cuspFormSubmodule_span_E hk hk2) (heckeTLevelOne k n) hA hB,
    LinearMap.trace_restrict_span_singleton (E_ne_zero hk hk2) (heckeTLevelOne_E hk hk2 n) hB]
  congr 1
  let e := ModularForm.CuspForm.equivCuspFormSubmodule 𝒮ℒ (k : ℤ)
  have hconj : (heckeTLevelOne k n).restrict hA = e.conj (heckeTCuspLevelOne k n) := by
    ext f z
    obtain ⟨g, rfl⟩ := e.surjective f
    rw [LinearMap.restrict_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, e.symm_apply_apply]
    exact DFunLike.congr_fun (heckeTLevelOne_coe_cuspForm k n g) z
  rw [hconj, LinearMap.trace_conj']

end TauCeti
