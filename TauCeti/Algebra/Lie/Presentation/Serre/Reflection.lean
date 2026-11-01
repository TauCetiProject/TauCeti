/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import TauCeti.Algebra.Lie.Derivation.LocallyNilpotent
public import TauCeti.Algebra.Lie.Presentation.Serre.Integrable
import Mathlib.Tactic.Module

/-!
# The simple reflections of a Serre system permute its weight spaces

Let `(H, E, F)` be a Serre system for a matrix of integers `CM` in a Lie algebra `L` over a
`ℚ`-algebra `R` (`TauCeti.IsSerreSystem`), and suppose that the raising and lowering families
generate `L`. The motivating example is the Lie algebra `Matrix.ToLieAlgebra R CM` presented by
Serre's relations, with its own generators.

The adjoint actions of `Eᵢ` and `Fᵢ` are locally nilpotent (`TauCeti.IsSerreSystem.engel_E_eq_top`),
so their exponentials are automorphisms of `L` even though `L` need not be finite dimensional
(`LieDerivation.locallyNilpotentExp`). The **Weyl automorphism** of the index `i` is the composite

`TauCeti.IsSerreSystem.weylAut h hspan i = exp (ad Eᵢ) ∘ exp (ad (-Fᵢ)) ∘ exp (ad Eᵢ)`,

the automorphism Kac writes `rᵢ` and Humphreys `τᵢ`. When `CMᵢᵢ = 2`, it satisfies the reflection
formula: an element `y` with `⁅y, Eᵢ⁆ = c • Eᵢ` and `⁅y, Fᵢ⁆ = -(c • Fᵢ)` is sent to `y - c • Hᵢ`.
On the Cartan generators this reads `Hⱼ ↦ Hⱼ - CMⱼᵢ • Hᵢ`, the simple coreflection. Consequently
the Weyl automorphism carries the simultaneous eigenspace `L_χ` of the `ad Hⱼ` onto the eigenspace
of the reflected weight `sᵢ χ = χ - χᵢ • CM.col i`, where `CM.col i` is the weight of `Eᵢ`.

This is the step of Serre's theorem identifying `Matrix.ToLieAlgebra K CM`, for a Cartan matrix `CM`
over a field `K` of characteristic zero, with the finite-dimensional split semisimple Lie algebra of
that Cartan matrix, in which the Weyl group enters: since every root is a Weyl translate of a simple
root, and the weight spaces of the simple roots and their multiples are already known
(`TauCeti.IsSerreSystem.iInf_eigenspace_ad_col_eq_span_singleton`,
`TauCeti.IsSerreSystem.iInf_eigenspace_ad_nsmul_col_eq_bot`), the weight spaces of all roots and
their multiples follow.

For an `sl₂` triple whose raising and lowering elements act nilpotently on all of `L`, the same
composite is `TauCeti.weylAut`. That construction does not apply here: in the presented algebra the
adjoint actions are only known to be locally nilpotent.

## Main definitions

* `TauCeti.IsSerreSystem.weylAut`: the automorphism `exp (ad Eᵢ) ∘ exp (ad (-Fᵢ)) ∘ exp (ad Eᵢ)`.

## Main results

* `TauCeti.IsSerreSystem.weylAut_apply_of_lie_eq_smul`: the reflection formula `y ↦ y - c • Hᵢ`.
* `TauCeti.IsSerreSystem.weylAut_apply_H`: the Weyl automorphism acts on the Cartan generators by
  the simple coreflection `Hⱼ ↦ Hⱼ - CMⱼᵢ • Hᵢ`.
* `TauCeti.IsSerreSystem.weylAut_apply_H_self`, `TauCeti.IsSerreSystem.weylAut_apply_E_self` and
  `TauCeti.IsSerreSystem.weylAut_apply_F_self`: it negates and swaps the triple
  `Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ`.
* `TauCeti.IsSerreSystem.weylAut_mem_iInf_eigenspace_ad` and
  `TauCeti.IsSerreSystem.map_weylAut_iInf_eigenspace_ad`: the Weyl automorphism carries the weight
  space of `χ` onto the weight space of `χ - χᵢ • CM.col i`.
* `TauCeti.map_weylAut_iInf_eigenspace_ad_serreH`: the same statement for the Lie algebra presented
  by Serre's relations.

## References

* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI, appendix
* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  §18.3
* V. G. Kac, *Infinite Dimensional Lie Algebras*, third edition, Cambridge University Press (1990),
  §3.8.
-/

public section

open LieAlgebra

namespace TauCeti

variable {B R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  {CM : Matrix B B ℤ} {H E F : B → L}

namespace IsSerreSystem

omit [Algebra ℚ R] in
/-- The inner derivation `ad x` acts by the bracket with `x`. -/
private theorem ad_toLinearMap_apply (x y : L) :
    (LieDerivation.ad R L x).toLinearMap y = ⁅x, y⁆ := by
  rw [LieDerivation.coe_ad_apply_eq_ad_apply, LieAlgebra.ad_apply]

omit [Algebra ℚ R] in
/-- If every element is killed by a power of `ad x`, the inner derivation `ad x` is locally
nilpotent in the form `LieDerivation.locallyNilpotentExp` asks for. -/
private theorem exists_ad_pow_apply_eq_zero {x : L} (hx : LieSubalgebra.engel R x = ⊤) (y : L) :
    ∃ n, ((LieDerivation.ad R L x).toLinearMap ^ n) y = 0 := by
  rw [LieDerivation.coe_ad_apply_eq_ad_apply]
  exact (LieSubalgebra.mem_engel_iff R x y).1 (hx ▸ LieSubalgebra.mem_top y)

variable (h : IsSerreSystem R CM H E F)
  (hspan : LieSubalgebra.lieSpan R L (Set.range E ∪ Set.range F) = ⊤)

/-- The exponential `exp (ad Eᵢ)`, an automorphism because `ad Eᵢ` is locally nilpotent. -/
private noncomputable def expAdE (i : B) : L ≃ₗ⁅R⁆ L :=
  (LieDerivation.ad R L (E i)).locallyNilpotentExp
    (exists_ad_pow_apply_eq_zero (h.engel_E_eq_top hspan i))

/-- The exponential `exp (ad (-Fᵢ))`, an automorphism because `ad Fᵢ` is locally nilpotent. -/
private noncomputable def expAdNegF (i : B) : L ≃ₗ⁅R⁆ L :=
  (LieDerivation.ad R L (-F i)).locallyNilpotentExp
    (exists_ad_pow_apply_eq_zero (by rw [LieSubalgebra.engel_neg]; exact h.engel_F_eq_top hspan i))

/-- The **Weyl automorphism** `exp (ad Eᵢ) ∘ exp (ad (-Fᵢ)) ∘ exp (ad Eᵢ)` of a Lie algebra
generated by the raising and lowering families of a Serre system. The exponentials are those of the
locally nilpotent derivations `ad Eᵢ` and `ad (-Fᵢ)`. When `CMᵢᵢ = 2` it realises the simple
reflection `sᵢ` on the weight spaces (`TauCeti.IsSerreSystem.map_weylAut_iInf_eigenspace_ad`). -/
noncomputable def weylAut (i : B) : L ≃ₗ⁅R⁆ L :=
  (h.expAdE hspan i).trans ((h.expAdNegF hspan i).trans (h.expAdE hspan i))

private theorem weylAut_apply' (i : B) (y : L) :
    h.weylAut hspan i y = h.expAdE hspan i (h.expAdNegF hspan i (h.expAdE hspan i y)) :=
  (rfl)

/-- `exp (ad Eᵢ) y = y + ⁅Eᵢ, y⁆` when `⁅Eᵢ, ⁅Eᵢ, y⁆⁆ = 0`. -/
private theorem expAdE_apply_of_lie_lie_eq_zero (i : B) {y : L} (hy : ⁅E i, ⁅E i, y⁆⁆ = 0) :
    h.expAdE hspan i y = y + ⁅E i, y⁆ := by
  rw [expAdE, LieDerivation.locallyNilpotentExp_apply,
    Module.End.locallyNilpotentExp_apply_of_apply_apply_eq_zero _ _
      (by rwa [ad_toLinearMap_apply, ad_toLinearMap_apply]), ad_toLinearMap_apply]

/-- `exp (ad (-Fᵢ)) y = y + ⁅-Fᵢ, y⁆` when `⁅-Fᵢ, ⁅-Fᵢ, y⁆⁆ = 0`. -/
private theorem expAdNegF_apply_of_lie_lie_eq_zero (i : B) {y : L}
    (hy : ⁅-F i, ⁅-F i, y⁆⁆ = 0) : h.expAdNegF hspan i y = y + ⁅-F i, y⁆ := by
  rw [expAdNegF, LieDerivation.locallyNilpotentExp_apply,
    Module.End.locallyNilpotentExp_apply_of_apply_apply_eq_zero _ _
      (by rwa [ad_toLinearMap_apply, ad_toLinearMap_apply]), ad_toLinearMap_apply]

/-- `exp (ad Eᵢ)` fixes `Eᵢ`. -/
private theorem expAdE_apply_E_self (i : B) : h.expAdE hspan i (E i) = E i := by
  rw [expAdE, LieDerivation.locallyNilpotentExp_apply,
    Module.End.locallyNilpotentExp_apply_of_apply_eq_zero _ _
      (by rw [ad_toLinearMap_apply, lie_self])]

/-- `exp (ad Eᵢ)` sends `Hᵢ` to `Hᵢ - 2 • Eᵢ`. -/
private theorem expAdE_apply_H_self {i : B} (hii : CM i i = 2) :
    h.expAdE hspan i (H i) = H i - (2 : R) • E i := by
  have hEH : ⁅E i, H i⁆ = -((2 : R) • E i) := by
    rw [← lie_skew, h.lie_H_E, hii, ← Int.cast_smul_eq_zsmul R, Int.cast_ofNat]
  rw [h.expAdE_apply_of_lie_lie_eq_zero hspan i (by rw [hEH]; simp), hEH, sub_eq_add_neg]

/-- `exp (ad (-Fᵢ))` sends `Eᵢ` to `Eᵢ + Hᵢ - Fᵢ`. -/
private theorem expAdNegF_apply_E_self {i : B} (hii : CM i i = 2) :
    h.expAdNegF hspan i (E i) = E i + H i - F i := by
  have hFE : ⁅-F i, E i⁆ = H i := by rw [neg_lie, lie_skew, h.lie_E_F_self]
  have hFH : ⁅-F i, H i⁆ = 2 • (-F i) := by
    rw [neg_lie, ← lie_skew, neg_neg, h.lie_H_F, hii, smul_neg, ← natCast_zsmul]
    rfl
  rw [expAdNegF, LieDerivation.locallyNilpotentExp_apply,
    Module.End.locallyNilpotentExp_apply_of_apply_apply_eq_two_nsmul _ _
      (by rw [ad_toLinearMap_apply, ad_toLinearMap_apply, hFE, hFH])
      (by rw [ad_toLinearMap_apply, lie_self]), ad_toLinearMap_apply, hFE, sub_eq_add_neg]

/-- **The reflection formula.** If `CMᵢᵢ = 2` and `y` acts on `Eᵢ` and `Fᵢ` by the opposite scalars
`c` and `-c`, the Weyl automorphism sends `y` to `y - c • Hᵢ`. -/
theorem weylAut_apply_of_lie_eq_smul {i : B} (hii : CM i i = 2) {y : L} {c : R}
    (hyE : ⁅y, E i⁆ = c • E i) (hyF : ⁅y, F i⁆ = -(c • F i)) :
    h.weylAut hspan i y = y - c • H i := by
  have hEy : ⁅E i, y⁆ = -(c • E i) := by rw [← lie_skew, hyE]
  have hFy : ⁅-F i, y⁆ = -(c • F i) := by rw [neg_lie, lie_skew, hyF]
  have s₁ : h.expAdE hspan i y = y - c • E i := by
    rw [h.expAdE_apply_of_lie_lie_eq_zero hspan i (by rw [hEy]; simp), hEy, sub_eq_add_neg]
  have hyF' : h.expAdNegF hspan i y = y - c • F i := by
    rw [h.expAdNegF_apply_of_lie_lie_eq_zero hspan i (by rw [hFy]; simp), hFy, sub_eq_add_neg]
  have s₂ : h.expAdNegF hspan i (y - c • E i) = y - c • E i - c • H i := by
    rw [map_sub, map_smul, hyF', h.expAdNegF_apply_E_self hspan hii]
    module
  have hEE := h.expAdE_apply_E_self hspan i
  rw [h.weylAut_apply' hspan i, s₁, s₂, map_sub, map_sub, map_smul, map_smul, s₁, hEE,
    h.expAdE_apply_H_self hspan hii]
  module

/-- **The Weyl automorphism on the Cartan generators** is the simple coreflection
`Hⱼ ↦ Hⱼ - CMⱼᵢ • Hᵢ`. -/
theorem weylAut_apply_H {i : B} (hii : CM i i = 2) (j : B) :
    h.weylAut hspan i (H j) = H j - CM j i • H i := by
  rw [h.weylAut_apply_of_lie_eq_smul hspan hii (c := (CM j i : R))
      (by rw [h.lie_H_E, Int.cast_smul_eq_zsmul]) (by rw [h.lie_H_F, Int.cast_smul_eq_zsmul]),
    Int.cast_smul_eq_zsmul]

/-- The Weyl automorphism negates `Hᵢ`. -/
theorem weylAut_apply_H_self {i : B} (hii : CM i i = 2) : h.weylAut hspan i (H i) = -H i := by
  rw [h.weylAut_apply_H hspan hii, hii]
  module

/-- `exp (ad Eᵢ)` sends `Fᵢ` to `Fᵢ + Hᵢ - Eᵢ`. -/
private theorem expAdE_apply_F_self {i : B} (hii : CM i i = 2) :
    h.expAdE hspan i (F i) = F i + H i - E i := by
  have hEH : ⁅E i, H i⁆ = 2 • (-E i) := by
    rw [← lie_skew, h.lie_H_E, hii, smul_neg, ← natCast_zsmul]
    rfl
  rw [expAdE, LieDerivation.locallyNilpotentExp_apply,
    Module.End.locallyNilpotentExp_apply_of_apply_apply_eq_two_nsmul _ _
      (by rw [ad_toLinearMap_apply, ad_toLinearMap_apply, h.lie_E_F_self, hEH])
      (by rw [ad_toLinearMap_apply, lie_neg, lie_self, neg_zero]), ad_toLinearMap_apply,
    h.lie_E_F_self, sub_eq_add_neg]

/-- `exp (ad (-Fᵢ))` sends `Hᵢ` to `Hᵢ - 2 • Fᵢ`. -/
private theorem expAdNegF_apply_H_self {i : B} (hii : CM i i = 2) :
    h.expAdNegF hspan i (H i) = H i - (2 : R) • F i := by
  have hFH : ⁅-F i, H i⁆ = -((2 : R) • F i) := by
    rw [neg_lie, ← lie_skew, neg_neg, h.lie_H_F, hii, ← Int.cast_smul_eq_zsmul R, Int.cast_ofNat]
  rw [h.expAdNegF_apply_of_lie_lie_eq_zero hspan i (by rw [hFH]; simp), hFH, sub_eq_add_neg]

/-- The Weyl automorphism sends `Eᵢ` to `-Fᵢ`. -/
theorem weylAut_apply_E_self {i : B} (hii : CM i i = 2) : h.weylAut hspan i (E i) = -F i := by
  have hEE := h.expAdE_apply_E_self hspan i
  rw [h.weylAut_apply' hspan i, hEE, h.expAdNegF_apply_E_self hspan hii, map_sub, map_add, hEE,
    h.expAdE_apply_H_self hspan hii, h.expAdE_apply_F_self hspan hii]
  module

/-- The Weyl automorphism sends `Fᵢ` to `-Eᵢ`. -/
theorem weylAut_apply_F_self {i : B} (hii : CM i i = 2) : h.weylAut hspan i (F i) = -E i := by
  have hFF : h.expAdNegF hspan i (F i) = F i := by
    rw [expAdNegF, LieDerivation.locallyNilpotentExp_apply,
      Module.End.locallyNilpotentExp_apply_of_apply_eq_zero _ _
        (by rw [ad_toLinearMap_apply, neg_lie, lie_self, neg_zero])]
  have hEE := h.expAdE_apply_E_self hspan i
  rw [h.weylAut_apply' hspan i, h.expAdE_apply_F_self hspan hii, map_sub, map_add, hFF,
    h.expAdNegF_apply_H_self hspan hii, h.expAdNegF_apply_E_self hspan hii]
  have : F i + (H i - (2 : R) • F i) - (E i + H i - F i) = -E i := by module
  rw [this, map_neg, hEE]

/-- The Weyl automorphism fixes `Hⱼ` after the simple coreflection: it squares to the identity on
the span of the Cartan generators. -/
private theorem weylAut_apply_H_sub {i : B} (hii : CM i i = 2) (j : B) :
    h.weylAut hspan i (H j - CM j i • H i) = H j := by
  rw [h.weylAut_apply_of_lie_eq_smul hspan hii (c := -(CM j i : R))
    (by rw [sub_lie, smul_lie, h.lie_H_E, h.lie_H_E, hii, ← Int.cast_smul_eq_zsmul R (CM j i),
      ← Int.cast_smul_eq_zsmul R (CM j i), ← Int.cast_smul_eq_zsmul R 2]; module)
    (by rw [sub_lie, smul_lie, h.lie_H_F, h.lie_H_F, hii, ← Int.cast_smul_eq_zsmul R (CM j i),
      ← Int.cast_smul_eq_zsmul R (CM j i), ← Int.cast_smul_eq_zsmul R 2]; module)]
  rw [← Int.cast_smul_eq_zsmul R (CM j i)]
  module

omit [Algebra ℚ R] in
/-- An automorphism carrying each `Hⱼ - CMⱼᵢ • Hᵢ` to `Hⱼ` carries a simultaneous eigenvector of the
`ad Hⱼ` of weight `χ` to one of weight `χ - χᵢ • CM.col i`. -/
private theorem map_mem_iInf_eigenspace_ad (φ : L ≃ₗ⁅R⁆ L) {i : B}
    (hφ : ∀ j, φ (H j - CM j i • H i) = H j) {χ : B → ℤ} {z : L}
    (hz : z ∈ ⨅ j, (ad R L (H j)).eigenspace (χ j : R)) :
    φ z ∈ ⨅ j, (ad R L (H j)).eigenspace ((χ - χ i • CM.col i) j : R) := by
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, ad_apply] at hz ⊢
  intro j
  rw [← hφ j, ← LieEquiv.map_lie, sub_lie, ← Int.cast_smul_eq_zsmul R (CM j i), smul_lie, hz j,
    hz i, map_sub, map_smul, map_smul, map_smul, Pi.sub_apply, Pi.smul_apply, Matrix.col_apply,
    smul_eq_mul, Int.cast_sub, Int.cast_mul]
  module

/-- **The Weyl automorphism maps weight spaces to reflected weight spaces.** If `CMᵢᵢ = 2`, it
carries a simultaneous eigenvector of the `ad Hⱼ` of weight `χ` to one of weight
`χ - χᵢ • CM.col i`, where `CM.col i` is the weight of `Eᵢ`. -/
theorem weylAut_mem_iInf_eigenspace_ad {i : B} (hii : CM i i = 2) {χ : B → ℤ} {z : L}
    (hz : z ∈ ⨅ j, (ad R L (H j)).eigenspace (χ j : R)) :
    h.weylAut hspan i z ∈ ⨅ j, (ad R L (H j)).eigenspace ((χ - χ i • CM.col i) j : R) :=
  map_mem_iInf_eigenspace_ad _ (h.weylAut_apply_H_sub hspan hii) hz

/-- **The Weyl automorphism permutes the weight spaces.** If `CMᵢᵢ = 2`, it carries the
simultaneous eigenspace of the `ad Hⱼ` of weight `χ` onto that of weight `χ - χᵢ • CM.col i`, the
image of `χ` under the simple reflection `sᵢ`. -/
theorem map_weylAut_iInf_eigenspace_ad {i : B} (hii : CM i i = 2) (χ : B → ℤ) :
    (⨅ j, (ad R L (H j)).eigenspace (χ j : R)).map (h.weylAut hspan i).toLinearEquiv.toLinearMap =
      ⨅ j, (ad R L (H j)).eigenspace ((χ - χ i • CM.col i) j : R) := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun z hz =>
    h.weylAut_mem_iInf_eigenspace_ad hspan hii hz) fun z hz => ?_
  -- the inverse automorphism undoes the coreflection, so it maps back, since `sᵢ² = 1`
  have hsymm : ∀ j, (h.weylAut hspan i).symm (H j - CM j i • H i) = H j := fun j => by
    rw [LieEquiv.symm_apply_eq, h.weylAut_apply_H hspan hii]
  have hχ : (χ - χ i • CM.col i) - (χ - χ i • CM.col i) i • CM.col i = χ := by
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul, hii]
    ring
  refine ⟨(h.weylAut hspan i).symm z, ?_, (h.weylAut hspan i).apply_symm_apply z⟩
  have := map_mem_iInf_eigenspace_ad _ hsymm hz
  rwa [hχ] at this

end IsSerreSystem

/-- In the Lie algebra presented by Serre's relations for a matrix `CM` with `CMᵢᵢ = 2`, over a
`ℚ`-algebra, the Weyl automorphism of the index `i` carries the weight space of `χ` onto that of
`χ - χᵢ • CM.col i`. -/
theorem map_weylAut_iInf_eigenspace_ad_serreH [DecidableEq B] (R : Type*) [CommRing R]
    [Algebra ℚ R] {i : B} (hii : CM i i = 2) (χ : B → ℤ) :
    (⨅ j, (ad R (Matrix.ToLieAlgebra R CM) (serreH R CM j)).eigenspace (χ j : R)).map
        ((isSerreSystem_serre R CM).weylAut (lieSpan_serreE_union_serreF_eq_top R CM)
          i).toLinearEquiv.toLinearMap =
      ⨅ j, (ad R (Matrix.ToLieAlgebra R CM) (serreH R CM j)).eigenspace
        ((χ - χ i • CM.col i) j : R) :=
  (isSerreSystem_serre R CM).map_weylAut_iInf_eigenspace_ad _ hii χ

end TauCeti
