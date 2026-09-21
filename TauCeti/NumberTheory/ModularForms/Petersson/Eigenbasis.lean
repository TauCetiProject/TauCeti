/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.EigenFromPrimes
public import TauCeti.NumberTheory.ModularForms.Petersson.Normal
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# A simultaneous eigenbasis for the good Hecke operators

On a fixed nebentypus space `S_k(N, χ)`, the good prime Hecke operators commute and are
normal for the Petersson product.  This file applies the finite-dimensional spectral theorem to
obtain a Petersson-orthonormal basis whose vectors are good Hecke eigenforms.

The Petersson product is not installed globally as the inner product on cusp forms, because that
would replace their existing function-space norm.  Accordingly, the public result exposes an
ordinary algebraic basis together with its explicit Petersson orthonormality equation.  Internally
we install the Petersson inner-product core only while applying Mathlib's joint-eigenspace API.

## Main result

* `HeckeRing.GL2.exists_peterssonOrthonormalBasis_eigenformAwayFromLevel`: every fixed
  nebentypus cusp space has a finite Petersson-orthonormal basis whose vectors underlie bundled
  good Hecke eigenforms with that nebentypus.

## Provenance

The rescaling of a good Hecke operator to a symmetric operator follows the proof of
`exists_simultaneous_eigenform_basis` in the AINTLIB `LeanModularForms` project at commit
`112d12d95` (`HeckeRIngs/GL2/AdjointTheoryPetersson.lean`, Apache-2.0).  The basis construction
here instead uses Mathlib's joint-eigenspace and collected-orthonormal-basis APIs, and the public
statement records spanning and unit norm explicitly.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.5.4.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.4.
-/

public section

noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped Function HeckeCosetModule MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-! ### The commuting symmetric family -/

/-- A prime index away from the level. -/
private abbrev GoodPrimeIndex (N : ℕ) := {p : ℕ // p.Prime ∧ p.Coprime N}

/-- The canonical Hecke-ring action of the good prime indexed by `i`. -/
private noncomputable def goodPrimeHeckeFamily :
    GoodPrimeIndex N → Module.End ℂ (cuspFormCharSpace k χ) :=
  fun i ↦ heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N i.1)

/-- The family at the index `i` is the Hecke-ring action of `T_p` for the prime `p = i`. -/
private theorem goodPrimeHeckeFamily_apply (i : GoodPrimeIndex N) :
    goodPrimeHeckeFamily k χ i =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N i.1) :=
  rfl

private theorem goodPrimeHeckeFamily_pairwise_commute :
    Pairwise (Commute on goodPrimeHeckeFamily k χ) := by
  intro i j _
  rw [Function.onFun_apply, goodPrimeHeckeFamily_apply, goodPrimeHeckeFamily_apply]
  exact Commute.map
    (HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
      (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) _ _)
    (heckeRingHomCuspCharSpace k χ)

/-- The Petersson core, installed locally for the spectral argument. -/
noncomputable local instance peterssonInnerCosetsCoreInstance :
    InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  CuspForm.peterssonInnerCosetsCore

/-- The Petersson normed additive structure, installed only for the spectral argument. -/
noncomputable local instance peterssonNormedAddCommGroup :
    NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The Petersson inner-product structure, installed only for the spectral argument. -/
noncomputable local instance peterssonInnerProductSpace :
    InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  InnerProductSpace.ofCore _

private theorem inner_charSpace_apply (f g : cuspFormCharSpace k χ) :
    inner ℂ f g = CuspForm.peterssonInnerCosets
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) g := by
  rw [Submodule.coe_inner]
  exact CuspForm.peterssonInnerCosetsCore_inner _ _

/-- A good prime Hecke operator becomes symmetric after multiplication by a nonzero scalar. -/
private theorem exists_symmetric_smul_goodPrimeHeckeFamily (i : GoodPrimeIndex N) :
    ∃ c : ℂ, c ≠ 0 ∧ (c • goodPrimeHeckeFamily k χ i).IsSymmetric := by
  -- The Petersson adjoint of `T_p` on the `χ`-space is `χ(p)⁻¹ T_p`, so rescale by a square
  -- root `c` of `χ(p)⁻¹`.
  obtain ⟨c, hc_sq⟩ := IsAlgClosed.exists_pow_nat_eq
    ((χ (ZMod.unitOfCoprime i.1 i.2.2) : ℂ)⁻¹) (show 0 < 2 by omega)
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc, zero_pow (by omega)] at hc_sq
    exact inv_ne_zero (mod_cast Units.ne_zero (χ (ZMod.unitOfCoprime i.1 i.2.2))) hc_sq.symm
  -- A character value has finite order, hence norm one, so `c` is a unit complex number.
  have hconj_mul : starRingEnd ℂ c * c = 1 := by
    have hnorm_sq : ‖c‖ ^ 2 = 1 := by
      rw [← norm_pow, hc_sq]
      simpa only [map_inv, Units.coeHom_apply] using ((Units.coeHom ℂ).isOfFinOrder
        (MonoidHom.isOfFinOrder χ
          (isOfFinOrder_of_finite (ZMod.unitOfCoprime i.1 i.2.2))).inv).norm_eq_one
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm_sq,
      Complex.ofReal_one]
  refine ⟨c, hc_ne, fun f g ↦ ?_⟩
  -- The adjoint pair, read in the second argument: `⟪f, T_p g⟫ = conj (χ(p)⁻¹) ⟪T_p f, g⟫`.
  have hadj := isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (χ := χ) k i.2.1 i.2.2 g f
  simp only [LinearMap.flip_apply,
    TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply, Pi.smul_apply,
    Submodule.coe_smul, CuspForm.peterssonInnerCosets_smul_left] at hadj
  rw [inner_charSpace_apply k χ, inner_charSpace_apply k χ]
  simp only [goodPrimeHeckeFamily_apply, LinearMap.smul_apply, Submodule.coe_smul,
    CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right]
  -- Scalar algebra: `c * conj c ^ 2 = conj c` because `conj c * c = 1`.
  have hcc : c * starRingEnd ℂ c ^ 2 = starRingEnd ℂ c := by
    rw [pow_two, ← mul_assoc, mul_comm c (starRingEnd ℂ c), hconj_mul, one_mul]
  rw [hadj, ← hc_sq, map_pow, ← mul_assoc, hcc]

/-- A chosen nonzero scalar making each good prime Hecke operator symmetric. -/
private noncomputable def goodPrimeHeckeScale (i : GoodPrimeIndex N) : ℂ :=
  (exists_symmetric_smul_goodPrimeHeckeFamily k χ i).choose

private theorem goodPrimeHeckeScale_ne_zero (i : GoodPrimeIndex N) :
    goodPrimeHeckeScale k χ i ≠ 0 :=
  (exists_symmetric_smul_goodPrimeHeckeFamily k χ i).choose_spec.1

/-- The commuting symmetric family obtained by rescaling the good prime Hecke operators. -/
private noncomputable def symmetricGoodPrimeHeckeFamily :
    GoodPrimeIndex N → Module.End ℂ (cuspFormCharSpace k χ) :=
  fun i ↦ goodPrimeHeckeScale k χ i • goodPrimeHeckeFamily k χ i

private theorem symmetricGoodPrimeHeckeFamily_isSymmetric (i : GoodPrimeIndex N) :
    (symmetricGoodPrimeHeckeFamily k χ i).IsSymmetric :=
  (exists_symmetric_smul_goodPrimeHeckeFamily k χ i).choose_spec.2

private theorem symmetricGoodPrimeHeckeFamily_pairwise_commute :
    Pairwise (Commute on symmetricGoodPrimeHeckeFamily k χ) := by
  intro i j hij
  exact ((goodPrimeHeckeFamily_pairwise_commute k χ hij).smul_left _).smul_right _

/-! ### The simultaneous eigenbasis -/

/-- **The good Hecke operators admit a simultaneous Petersson-orthonormal eigenbasis.**

More precisely, the fixed-nebentypus cusp space has a finite algebraic basis `b` satisfying
`<b_i, b_j>_Pet = δ_ij`, and every `b_i` is the underlying form of a bundled
`EigenformAwayFromLevel` with nebentypus `χ`.  The explicit Petersson equation avoids changing
the globally installed function-space norm on cusp forms. -/
theorem exists_peterssonOrthonormalBasis_eigenformAwayFromLevel :
    ∃ (I : Type) (b : Module.Basis I ℂ (cuspFormCharSpace k χ)),
      Finite I ∧
      (∀ i, CuspForm.peterssonInnerCosets
        (b i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (b i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 1) ∧
      (∀ i j, i ≠ j → CuspForm.peterssonInnerCosets
        (b i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (b j : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0) ∧
      ∀ i, ∃ f : EigenformAwayFromLevel N k,
        f.χ = χ ∧ f.toCuspForm = (b i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  classical
  let W : (GoodPrimeIndex N → ℂ) → Submodule ℂ (cuspFormCharSpace k χ) :=
    fun a ↦ ⨅ i, Module.End.eigenspace (symmetricGoodPrimeHeckeFamily k χ i) (a i)
  have hInternal : DirectSum.IsInternal W :=
    LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
      (symmetricGoodPrimeHeckeFamily_isSymmetric k χ)
      (symmetricGoodPrimeHeckeFamily_pairwise_commute k χ)
  have hOrthogonal : OrthogonalFamily ℂ
      (fun a : GoodPrimeIndex N → ℂ ↦ W a) (fun a ↦ (W a).subtypeₗᵢ) :=
    by
      simpa only [W] using
        LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces
          (symmetricGoodPrimeHeckeFamily_isSymmetric k χ)
  let J : (GoodPrimeIndex N → ℂ) → Type := fun a ↦ Fin (Module.finrank ℂ (W a))
  let basisAt : ∀ a, Module.Basis (J a) ℂ (W a) :=
    fun a ↦ (stdOrthonormalBasis ℂ (W a)).toBasis
  let b : Module.Basis (Σ a, J a) ℂ (cuspFormCharSpace k χ) :=
    hInternal.collectedBasis basisAt
  have hb_orthonormal : Orthonormal ℂ b :=
    hInternal.collectedBasis_orthonormal hOrthogonal fun a ↦ by
      simpa only [basisAt, OrthonormalBasis.coe_toBasis] using
        (stdOrthonormalBasis ℂ (W a)).orthonormal
  refine ⟨Σ a, J a, b, Module.Finite.finite_basis b, ?_, ?_, ?_⟩
  · intro i
    rw [← inner_charSpace_apply k χ]
    simpa using orthonormal_iff_ite.mp hb_orthonormal i i
  · intro i j hij
    rw [← inner_charSpace_apply k χ]
    exact hb_orthonormal.inner_eq_zero hij
  · intro i
    have hiW : b i ∈ W i.1 := hInternal.collectedBasis_mem basisAt i
    have hprime : ∀ p : ℕ, p.Prime → p.Coprime N → ∃ c : ℂ,
        heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) (b i) = c • b i := by
      intro p hp hpN
      let q : GoodPrimeIndex N := ⟨p, hp, hpN⟩
      have heig := Module.End.mem_eigenspace_iff.mp
        ((Submodule.mem_iInf _).mp hiW q)
      have hscaled : goodPrimeHeckeScale k χ q •
          goodPrimeHeckeFamily k χ q (b i) = i.1 q • b i := by
        simpa only [symmetricGoodPrimeHeckeFamily, LinearMap.smul_apply] using heig
      refine ⟨(goodPrimeHeckeScale k χ q)⁻¹ * i.1 q, ?_⟩
      have := congrArg (fun x ↦ (goodPrimeHeckeScale k χ q)⁻¹ • x) hscaled
      simpa only [goodPrimeHeckeFamily, q, smul_smul,
        inv_mul_cancel₀ (goodPrimeHeckeScale_ne_zero k χ q), one_smul] using this
    have hbi_ne : (b i : cuspFormCharSpace k χ) ≠ 0 := hb_orthonormal.ne_zero i
    let f := EigenformAwayFromLevel.ofForallPrime (b i).2
      (fun h ↦ hbi_ne (Subtype.ext h)) hprime
    exact ⟨f, EigenformAwayFromLevel.ofForallPrime_χ _ _ _,
      EigenformAwayFromLevel.ofForallPrime_toCuspForm _ _ _⟩

end HeckeRing.GL2

end
