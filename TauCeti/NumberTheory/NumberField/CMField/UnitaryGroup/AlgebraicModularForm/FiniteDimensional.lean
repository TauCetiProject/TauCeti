/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AlgebraicModularForm
public import TauCeti.RepresentationTheory.Coinduced.FiniteLevel

/-!
# Finite dimension of algebraic modular forms at a character level

For a framed hermitian space `V`, algebraic modular forms with coefficients in `W` are smooth
functions on the finite adelic unitary group satisfying covariance under the rational points.
At level `(K, χ)`, their values on representatives of the double cosets
`Γ_{V,f} \ G_f / K` determine them. Thus a finite class set and finite-dimensional coefficients
give a finite-dimensional space, of dimension at most the number of classes times `dim W`.

Only finiteness of the class set is assumed here. The result therefore applies whenever
reduction theory supplies this finiteness; it does not require definiteness, compactness or
openness of `K`, finite stabilizers, or local constancy of `χ` as additional hypotheses.
Indeed the ambient character level of all coinduced functions is already finite-dimensional.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§4–6.
* [ShortProof]: grh-lean, https://github.com/lsernau/grh-lean, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`,
  `grh/src/Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean`
  (`New.finite_levelSpace_smoothFormRep`, `New.Space.finite_formTranslation_levelSpace`).
  These are the finiteness statements modeled here; the proof uses the existing coinduced
  carrier and evaluation on the double coset class set.
-/

public section

open Matrix NumberField Representation

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ} (V : FramedHermitianSpace E s)
  {A W : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W]
  (ρ : Representation A (infiniteAdelicUnitaryGroup E s) W)
  {K : Subgroup (finiteAdelicUnitaryGroup E ι)} {χ : K →* A}

/-- Algebraic modular forms at the same character level are determined by their values at any
family of representatives of the finite rational double cosets. The class set need not be
finite for this extensionality statement. -/
theorem algebraicModularFormsOfLevel_ext
    (c : DoubleCoset.Quotient (V.finiteRationalPoints :
      Set (finiteAdelicUnitaryGroup E ι)) (K : Set _) → finiteAdelicUnitaryGroup E ι)
    (hc : ∀ q : DoubleCoset.Quotient (V.finiteRationalPoints :
      Set (finiteAdelicUnitaryGroup E ι)) (K : Set _),
      DoubleCoset.mk V.finiteRationalPoints K (c q) = q)
    {f g : V.algebraicModularFormsOfLevel ρ K χ}
    (hfg : ∀ q, f.val.val (c q) = g.val.val (c q)) : f = g := by
  -- Rewrite the class set before introducing its dependent family of representatives.
  revert c
  rw [finiteRationalPoints_def]
  intro c hc hfg
  have hf := (V.mem_algebraicModularFormsOfLevel_iff ρ).mp f.property
  have hg := (V.mem_algebraicModularFormsOfLevel_iff ρ).mp g.property
  have h := weightSpace_coind_ext (V.coefficientRep ρ) V.finiteRationalEmbedding χ c hc
    (f := ⟨f.val, mem_weightSpace_coind_comp_subtype_iff.mpr hf.2⟩)
    (g := ⟨g.val, mem_weightSpace_coind_comp_subtype_iff.mpr hg.2⟩) hfg
  exact Subtype.ext (congrArg
    (fun u : weightSpace ((coind V.finiteRationalEmbedding (V.coefficientRep ρ)).comp
      K.subtype) χ ↦ u.val) h)

end TauCeti.FramedHermitianSpace

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ} (V : FramedHermitianSpace E s)
  {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
  (ρ : Representation k (infiniteAdelicUnitaryGroup E s) W)
  (K : Subgroup (finiteAdelicUnitaryGroup E ι)) (χ : K →* k)
  [Finite (DoubleCoset.Quotient (V.finiteRationalPoints :
    Set (finiteAdelicUnitaryGroup E ι)) (K : Set _))] [FiniteDimensional k W]

/-- Algebraic modular forms of character level with a finite double coset class set and
finite-dimensional coefficients form a finite-dimensional space. -/
instance finiteDimensional_algebraicModularFormsOfLevel :
    FiniteDimensional k (V.algebraicModularFormsOfLevel ρ K χ) := by
  have : Finite (DoubleCoset.Quotient (V.finiteRationalEmbedding.range :
      Set (finiteAdelicUnitaryGroup E ι)) (K : Set _)) := by
    simpa only [finiteRationalPoints_def] using
      (inferInstance : Finite (DoubleCoset.Quotient
        (V.finiteRationalPoints : Set (finiteAdelicUnitaryGroup E ι)) (K : Set _)))
  rw [algebraicModularFormsOfLevel_def]
  infer_instance

/-- The dimension at a character level is at most the number of finite rational double cosets
times the coefficient dimension. -/
theorem finrank_algebraicModularFormsOfLevel_le :
    Module.finrank k (V.algebraicModularFormsOfLevel ρ K χ) ≤
      Nat.card (DoubleCoset.Quotient (V.finiteRationalPoints :
        Set (finiteAdelicUnitaryGroup E ι)) (K : Set _)) * Module.finrank k W := by
  have : Finite (DoubleCoset.Quotient (V.finiteRationalEmbedding.range :
      Set (finiteAdelicUnitaryGroup E ι)) (K : Set _)) := by
    simpa only [finiteRationalPoints_def] using
      (inferInstance : Finite (DoubleCoset.Quotient
        (V.finiteRationalPoints : Set (finiteAdelicUnitaryGroup E ι)) (K : Set _)))
  rw [finiteRationalPoints_def]
  have hle : V.algebraicModularFormsOfLevel ρ K χ ≤
      weightSpace ((coind V.finiteRationalEmbedding (V.coefficientRep ρ)).comp K.subtype) χ := by
    rw [algebraicModularFormsOfLevel_def]
    exact inf_le_right
  exact (Submodule.finrank_mono hle).trans
    (finrank_weightSpace_coind_le (V.coefficientRep ρ) V.finiteRationalEmbedding K χ)

end TauCeti.FramedHermitianSpace
