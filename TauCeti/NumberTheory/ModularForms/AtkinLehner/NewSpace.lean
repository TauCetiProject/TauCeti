/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.OldSpace
public import TauCeti.NumberTheory.ModularForms.Petersson.AtkinLehner
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The Atkin–Lehner operators preserve the full new subspace

For an exact divisor `Q ∥ N` and a chosen Atkin–Lehner matrix `W`, the normalized operator
`𝒲_Q` on `S_k(Γ₁(N))` preserves the full new subspace. This is the carrier statement needed
before restricting the operator to a nebentypus space: `𝒲_Q` generally changes that character,
but it does not change newness.

The proof combines two facts. The operator preserves the oldspace
(`TauCeti.normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld`) and is Petersson-unitary
(`TauCeti.peterssonInnerCosets_normalizedAtkinLehnerOperatorGamma1Cusp`). Its restriction to the
finite-dimensional oldspace is injective, hence surjective. Thus every old form is the image of
an old form, and unitarity transports orthogonality to the oldspace.

## Main result

* `TauCeti.normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew`: every chosen normalized
  Atkin–Lehner operator preserves `S_k(Γ₁(N))ⁿᵉʷ`.
* `TauCeti.normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew_inf_cuspFormCharSpace`:
  on newforms, the same operator transports the nebentypus by `χ ↦ χ ∘ ι_Q`.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243, §1.
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.8.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

open _root_.CuspForm TauCeti.CuspForm

variable {N Q : ℕ} [NeZero N] {k : ℤ} {W : Matrix (Fin 2) (Fin 2) ℤ}

/-- **Every chosen normalized Atkin–Lehner operator preserves the full newspace at level
`Γ₁(N)`.** No nebentypus hypothesis is imposed: on character spaces this operator transports
the character, while this theorem says that it preserves newness on the ambient carrier. -/
theorem normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew (h : Q ∥ N)
    (hW : IsAtkinLehnerMatrix N Q W) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsNew N k) :
    normalizedAtkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f ∈ cuspFormsNew N k := by
  rw [cuspFormsNew_def] at hf ⊢
  rw [mem_peterssonOrthogonal_iff] at hf ⊢
  intro g hg
  let T := normalizedAtkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k
  let T_old : Module.End ℂ (cuspFormsOld N k) :=
    (T.domRestrict (cuspFormsOld N k)).codRestrict (cuspFormsOld N k) fun x ↦
      normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld h hW x.property
  have hT_old_injective : Function.Injective T_old := by
    intro x y hxy
    apply Subtype.ext
    apply normalizedAtkinLehnerOperatorGamma1Cusp_injective h.pos h.dvd hW k
    exact congrArg Subtype.val hxy
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hT_old_injective ⟨g, hg⟩
  have hxval : T x = g := congrArg Subtype.val hx
  rw [← hxval, peterssonInnerCosets_normalizedAtkinLehnerOperatorGamma1Cusp]
  exact hf x x.property

/-- **The normalized Atkin–Lehner operator transports new nebentypus spaces.** It carries
`S_k(N, χ)ⁿᵉʷ` into `S_k(N, χ ∘ ι_Q)ⁿᵉʷ`, where `ι_Q` inverts the residue modulo `Q` and fixes
the residue modulo `N / Q`. -/
theorem normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew_inf_cuspFormCharSpace
    (h : Q ∥ N) (hW : IsAtkinLehnerMatrix N Q W) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :
    normalizedAtkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f ∈
      cuspFormsNew N k ⊓ cuspFormCharSpace k
        (χ.comp ((hW.isExactDivisor h.ne_zero h.dvd).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) := by
  refine ⟨normalizedAtkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew h hW hf.1, ?_⟩
  rw [normalizedAtkinLehnerOperatorGamma1Cusp_def, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace h.pos h.dvd hW hf.2)

end TauCeti
