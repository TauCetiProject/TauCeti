/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
public import TauCeti.NumberTheory.ModularForms.SlashAdjugate
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The Petersson product under a slash and as an integral over translated domains

Slashing by `α ∈ GL(2, ℝ)` of positive determinant moves the Petersson integrand along the
Möbius action, and the invariant measure of `ℍ` does not see that motion. Writing
`D = det α > 0`, Mathlib's `UpperHalfPlane.petersson_slash` reads

```text
petersson k (f ∣[k] α) (h ∣[k] α) τ = D ^ (k - 2) * petersson k f h (α • τ),
```

so integrating over a domain `S` and changing variables gives

```text
⟪f ∣[k] α, h ∣[k] α⟫_S = D ^ (k - 2) * ⟪f, h⟫_{α • S}.
```

Feeding `h ∣[k] α⁻¹` into that identity moves a slash across the pairing, one argument at a
time — the **adjoint formula for a single slash**:

```text
⟪f ∣[k] α, h⟫_S = D ^ (k - 2) * ⟪f, h ∣[k] α⁻¹⟫_{α • S}.
```

This is the change-of-variables step behind the adjoint theory of the Hecke operators
(Diamond–Shurman §5.5, Miyake §4.5), in the shape the change of variables produces. The
classical form uses the main involution `α^ι = (det α) · α⁻¹` in place of `α⁻¹`; the two differ
by the scalar matrix `D · I`, which slashes as multiplication by `D ^ (k - 2)`, so the two
statements carry the same content and the determinant factor above is exactly the scalar the
involution absorbs. Either way it is the analytic input to the Petersson adjoint
`Tₙ* = ⟨n⟩⁻¹Tₙ` of the Hecke operators at indices prime to the level.

When the slashed right arguments all coincide — `h ∣[k] αᵢ^ι = h'` for every `i` — those
translated pairings reassemble into *one* pairing over the union `⋃ᵢ αᵢ • S`. The translates
are only almost-everywhere disjoint, which is why the reassembly runs through
`TauCeti.MeasureTheory.integral_biUnion_finset₀` rather than Mathlib's
`MeasureTheory.integral_biUnion_finset`. Whether that union is itself a fundamental domain is a
separate question about the family, not settled here; once it is, `peterssonInner` moves to any
other fundamental domain by `UpperHalfPlane.peterssonInner_eq_of_isFundamentalDomain`.

The same change of variables identifies the coset sum defining the Petersson product on
`S_k(Γ)` with a *single* integral. Each summand
`⟪f ∣[k] q⁻¹, g ∣[k] q⁻¹⟫_𝒟` is the integral of the unslashed Petersson integrand over the
translate `q⁻¹ • 𝒟`; passing to the open domain `𝒟ᵒ`, which differs from `𝒟` by a null set,
those translates — one for each coset of `Γ·{±I}` — become pairwise *disjoint*. So `⟪f, g⟫` is
the integral of `petersson k f g` over `⋃_q q⁻¹ • 𝒟ᵒ`. This file does not formalize that this
union is itself a fundamental domain for `Γ`.

## Main results

* `UpperHalfPlane.peterssonInner_slash_slash_of_det_pos`: a simultaneous slash by a
  positive-determinant `α` rescales the pairing by `(det α) ^ (k - 2)` and translates the
  domain.
* `UpperHalfPlane.peterssonInner_slash_left_of_det_pos` and
  `UpperHalfPlane.peterssonInner_slash_right_of_det_pos`: the adjoint formula, moving a slash
  from one argument of the pairing to the other.
* `UpperHalfPlane.peterssonInner_slash_left_adjugateGL` and
  `UpperHalfPlane.peterssonInner_slash_right_adjugateGL`: the same adjoint formulas written with
  the main involution `α^ι` in place of `α⁻¹`, where no determinant factor remains.
* `UpperHalfPlane.peterssonInner_sum_slash_left_adjugateGL` and
  `UpperHalfPlane.peterssonInner_sum_slash_right_adjugateGL`: the same, for a *finite family* of
  slashes at once — the shape a Hecke operator presents, being a slash sum over coset
  representatives.
* `UpperHalfPlane.peterssonInner_sum_slash_left_adjugateGL_biUnion` and
  `UpperHalfPlane.peterssonInner_sum_slash_right_adjugateGL_biUnion`: when the slashed arguments
  all coincide, that finite sum is a *single* pairing over the union of the translated domains.
* `UpperHalfPlane.peterssonInner_slash_slash_SL`: the determinant-one case, where the scalar
  disappears and only the domain moves.
* `CuspForm.peterssonInnerCosets_eq_sum_smul_fd`: the coset pairing is a sum of integrals over
  translates of `𝒟`.
* `CuspForm.peterssonInnerCosets_eq_peterssonInner`: that sum is the single integral of
  `petersson k f g` over the union of the corresponding translates of `𝒟ᵒ` — a union which
  `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter` shows is a fundamental
  domain for the image of `Γ` in `PSL(2, ℤ)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 5.4 and 5.5.
* Miyake, *Modular forms*, Section 4.5.
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>, commit
  `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, Apache-2.0 — `AdjointTheory.lean` for the
  single-slash involution form, `AdjointTheory/SummandAdjoint.lean` for the finite-family form
  (`peterssonInner_sum_slash_adjoint`) and for the reassembly over the union
  (`peterssonInner_sum_slash_adjoint_constantRHS`).
-/

public section

noncomputable section

open MeasureTheory UpperHalfPlane ModularGroup

open scoped Function MatrixGroups ModularForm Pointwise

namespace UpperHalfPlane

variable {k : ℤ} {g : GL (Fin 2) ℝ}

/-! ### Slashing by an element of positive determinant -/

/-- **A simultaneous slash rescales the Petersson pairing and translates its domain**:
`⟪f ∣[k] α, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f, h⟫_{α • S}`.

No integrability hypothesis is needed: both sides are the same set integral after the change of
variables, and `MeasureTheory.integral` is defined (as `0`) even where it fails to converge. -/
theorem peterssonInner_slash_slash_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) * peterssonInner k (g • S) f h := by
  rw [peterssonInner_def, peterssonInner_def, ← Set.image_smul,
    (measurePreserving_smul g volume).setIntegral_image_emb
      (measurableEmbedding_const_smul g)]
  simp_rw [petersson_slash]
  simp only [σ_eq_refl_of_det_pos hg, ContinuousAlgEquiv.refl_apply,
    Matrix.GeneralLinearGroup.val_det_apply, abs_of_pos hg]
  exact MeasureTheory.integral_const_mul _ _

/-- **The adjoint of a slash, on the left argument**:
`⟪f ∣[k] α, h⟫_S = (det α) ^ (k - 2) · ⟪f, h ∣[k] α⁻¹⟫_{α • S}` for `α` of positive determinant.

The classical statement uses the main involution `α^ι = (det α) · α⁻¹` in place of `α⁻¹`;
slashing by the scalar matrix `(det α) · I` is multiplication by `(det α) ^ (k - 2)`, which is
precisely the factor carried here. -/
theorem peterssonInner_slash_left_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) h =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) f (h ∣[k] g⁻¹) := by
  have hslash := peterssonInner_slash_slash_of_det_pos k hg S f (h ∣[k] g⁻¹)
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-- **The adjoint of a slash, in involution form**:
`⟪f ∣[k] α, h⟫_S = ⟪f, h ∣[k] α^ι⟫_{α • S}`, with no determinant factor.

This is the shape the classical adjoint theory uses (Diamond–Shurman §5.5, Miyake §4.5), and
the shape the Hecke adjoint `Tₙ* = ⟨n⟩⁻¹Tₙ` is assembled in: the main involution `α^ι` preserves
the integral matrices, so it acts on the Hecke cosets, where `α⁻¹` does not. The determinant
factor of `peterssonInner_slash_left_of_det_pos` has not gone away — `ModularForm.slash_adjugateGL`
says it is exactly what the involution contributes over the inverse.

Ported from AINTLIB (github.com/CBirkbeck/AINTLIB @ `6d87d596a537`, Apache-2.0),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`:
`peterssonInner_slash_adjoint` (:412), stated over its `peterssonAdj` (:322) — which is
`TauCeti.adjugateGL` specialised to `GL (Fin 2) ℝ`. -/
theorem peterssonInner_slash_left_adjugateGL (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) h = peterssonInner k (g • S) f (h ∣[k] TauCeti.adjugateGL g) := by
  rw [ModularForm.slash_adjugateGL, peterssonInner_smul_right,
    peterssonInner_slash_left_of_det_pos k hg]

/-- **The adjoint of a slash, on the right argument**:
`⟪f, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f ∣[k] α⁻¹, h⟫_{α • S}`. The mirror of
`peterssonInner_slash_left_of_det_pos`, with the same proof. -/
theorem peterssonInner_slash_right_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S f (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) (f ∣[k] g⁻¹) h := by
  have hslash := peterssonInner_slash_slash_of_det_pos k hg S (f ∣[k] g⁻¹) h
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-- **The adjoint of a slash on the right, in involution form**:
`⟪f, h ∣[k] α⟫_S = ⟪f ∣[k] α^ι, h⟫_{α • S}`. The mirror of
`peterssonInner_slash_left_adjugateGL`, and like it free of the determinant factor. -/
theorem peterssonInner_slash_right_adjugateGL (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S f (h ∣[k] g) =
      peterssonInner k (g • S) (f ∣[k] TauCeti.adjugateGL g) h := by
  rw [ModularForm.slash_adjugateGL, peterssonInner_smul_left, map_zpow₀, Complex.conj_ofReal,
    peterssonInner_slash_right_of_det_pos k hg]

/-! ### A finite family of slashes -/

/-- **The summand-level adjoint, on the left argument**: for a finite family `αᵢ` of
positive-determinant matrices,

```text
⟪∑ᵢ f ∣[k] αᵢ, h⟫_S = ∑ᵢ ⟪f, h ∣[k] αᵢ^ι⟫_{αᵢ • S}.
```

This is the shape in which the adjoint meets a Hecke operator, which is not a single slash but a
*sum* of them: `HeckeRing.GL2.heckeSlashSum`, which underlies the Hecke operator
`HeckeRing.GL2.heckeTCuspNat`, is `∑ᵥ f ∣[k] aᵥ` over representatives of the right cosets in a
double coset. The domains `αᵢ • S` are left where the change of variables puts
them — reassembling them into one domain is a separate step, and the reason the integrability
hypothesis is stated per summand rather than for the sum.

`hint` has to be supplied where the family is fixed. The integrability lemmas already here —
`UpperHalfPlane.integrableOn_petersson_slash_left` and its relatives — do **not** cover it: they
are stated over `𝒟`, for a slash by `SL(2, ℤ)`, and with *both* arguments slashed, where `hint`
allows an arbitrary `S`, a positive-determinant `GL(2, ℝ)` matrix, and only the left argument
slashed.

Adapted from AINTLIB (github.com/CBirkbeck/AINTLIB @ `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`,
Apache-2.0), `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/AdjointTheory/
SummandAdjoint.lean`: `peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable` (:620).
**The split is deliberate.** That statement bundles this identity with null-measurability of each
translate, pairwise a.e.-disjointness across the family, and integrability over the union — none
of which the identity needs. Here the domains are left where the change of variables puts them
and reassembling them is a separate step, so the only side condition is integrability of each
summand. The same citation covers `peterssonInner_sum_slash_right_adjugateGL` below. -/
theorem peterssonInner_sum_slash_left_adjugateGL (k : ℤ) {ι : Type*} (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ)
    (hα : ∀ i ∈ s, 0 < ((α i : Matrix (Fin 2) (Fin 2) ℝ)).det) (S : Set ℍ) (f h : ℍ → ℂ)
    (hint : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k (f ∣[k] α i) h τ) S (volume : Measure ℍ)) :
    peterssonInner k S (∑ i ∈ s, f ∣[k] α i) h =
      ∑ i ∈ s, peterssonInner k (α i • S) f (h ∣[k] TauCeti.adjugateGL (α i)) := by
  rw [peterssonInner_sum_left k S s (fun i ↦ f ∣[k] α i) h hint]
  exact Finset.sum_congr rfl fun i hi ↦
    peterssonInner_slash_left_adjugateGL k (hα i hi) S f h

/-- **The summand-level adjoint, on the right argument**: the mirror of
`peterssonInner_sum_slash_left_adjugateGL`,

```text
⟪f, ∑ᵢ h ∣[k] αᵢ⟫_S = ∑ᵢ ⟪f ∣[k] αᵢ^ι, h⟫_{αᵢ • S}.
```
-/
theorem peterssonInner_sum_slash_right_adjugateGL (k : ℤ) {ι : Type*} (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ)
    (hα : ∀ i ∈ s, 0 < ((α i : Matrix (Fin 2) (Fin 2) ℝ)).det) (S : Set ℍ) (f h : ℍ → ℂ)
    (hint : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k f (h ∣[k] α i) τ) S (volume : Measure ℍ)) :
    peterssonInner k S f (∑ i ∈ s, h ∣[k] α i) =
      ∑ i ∈ s, peterssonInner k (α i • S) (f ∣[k] TauCeti.adjugateGL (α i)) h := by
  rw [peterssonInner_sum_right k S s f (fun i ↦ h ∣[k] α i) hint]
  exact Finset.sum_congr rfl fun i hi ↦
    peterssonInner_slash_right_adjugateGL k (hα i hi) S f h

/-! ### Reassembling the translated domains -/

/-- **The aggregate adjoint identity, on the left argument.** When all the translated right
arguments coincide — `h ∣[k] αᵢ^ι = h'` for every `i` — the sum produced by
`peterssonInner_sum_slash_left_adjugateGL` is a *single* pairing, over the union of the
translated domains:

```text
⟪∑ᵢ f ∣[k] αᵢ, h⟫_S = ⟪f, h'⟫_{⋃ᵢ αᵢ • S}.
```

The constancy hypothesis `hadj` is what makes the reassembly possible at all: with a different
integrand on each piece there is nothing to reassemble. It is not a restriction in the Hecke
setting. There the `αᵢ` are right-coset representatives of a double coset, and their involutions
`αᵢ^ι` differ from one another by *left* multiplication by elements of the group `h` is modular
for, which slashing kills. For `Tₚ` on `Γ₁(N)` the representatives are `![![1, b], ![0, p]]`,
whose involution is `![![1, -b], ![0, 1]] * ![![p, 0], ![0, 1]]` with the first factor in
`Γ₁(N)`, so every `h ∣[k] αᵢ^ι` is `h ∣[k] ![![p, 0], ![0, 1]]`.

The union is not asserted to be a fundamental domain — that is a separate statement about the
family, and once it is available `peterssonInner_eq_of_isFundamentalDomain` moves the pairing to
any other fundamental domain. -/
theorem peterssonInner_sum_slash_left_adjugateGL_biUnion (k : ℤ) {ι : Type*} (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ)
    (hα : ∀ i ∈ s, 0 < ((α i : Matrix (Fin 2) (Fin 2) ℝ)).det) (S : Set ℍ) (f h h' : ℍ → ℂ)
    (hadj : ∀ i ∈ s, h ∣[k] TauCeti.adjugateGL (α i) = h')
    (hint : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k (f ∣[k] α i) h τ) S (volume : Measure ℍ))
    (hd : Set.Pairwise (↑s) (AEDisjoint (volume : Measure ℍ) on fun i ↦ α i • S))
    (hm : ∀ i ∈ s, NullMeasurableSet (α i • S) (volume : Measure ℍ))
    (hfi : IntegrableOn (fun τ ↦ petersson k f h' τ) (⋃ i ∈ s, α i • S) (volume : Measure ℍ)) :
    peterssonInner k S (∑ i ∈ s, f ∣[k] α i) h =
      peterssonInner k (⋃ i ∈ s, α i • S) f h' := by
  rw [peterssonInner_sum_slash_left_adjugateGL k s α hα S f h hint, peterssonInner_def,
    TauCeti.MeasureTheory.integral_biUnion_finset₀ s hd hm hfi]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [peterssonInner_def, hadj i hi]

/-- **The aggregate adjoint identity, on the right argument**: the mirror of
`peterssonInner_sum_slash_left_adjugateGL_biUnion`,

```text
⟪f, ∑ᵢ h ∣[k] αᵢ⟫_S = ⟪f', h⟫_{⋃ᵢ αᵢ • S}    whenever f ∣[k] αᵢ^ι = f' for every i.
```
-/
theorem peterssonInner_sum_slash_right_adjugateGL_biUnion (k : ℤ) {ι : Type*} (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ)
    (hα : ∀ i ∈ s, 0 < ((α i : Matrix (Fin 2) (Fin 2) ℝ)).det) (S : Set ℍ) (f f' h : ℍ → ℂ)
    (hadj : ∀ i ∈ s, f ∣[k] TauCeti.adjugateGL (α i) = f')
    (hint : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k f (h ∣[k] α i) τ) S (volume : Measure ℍ))
    (hd : Set.Pairwise (↑s) (AEDisjoint (volume : Measure ℍ) on fun i ↦ α i • S))
    (hm : ∀ i ∈ s, NullMeasurableSet (α i • S) (volume : Measure ℍ))
    (hfi : IntegrableOn (fun τ ↦ petersson k f' h τ) (⋃ i ∈ s, α i • S) (volume : Measure ℍ)) :
    peterssonInner k S f (∑ i ∈ s, h ∣[k] α i) =
      peterssonInner k (⋃ i ∈ s, α i • S) f' h := by
  rw [peterssonInner_sum_slash_right_adjugateGL k s α hα S f h hint, peterssonInner_def,
    TauCeti.MeasureTheory.integral_biUnion_finset₀ s hd hm hfi]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [peterssonInner_def, hadj i hi]

/-! ### Slashing by an element of `SL(2, ℤ)` -/

/-- **A simultaneous slash by `SL(2, ℤ)` only translates the domain of the Petersson pairing**:
the determinant is `1`, so the scalar of `peterssonInner_slash_slash_of_det_pos` disappears. -/
theorem peterssonInner_slash_slash_SL (k : ℤ) (γ : SL(2, ℤ)) (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] γ) (h ∣[k] γ) = peterssonInner k (γ • S) f h := by
  have hdet_eq : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val (Matrix.SpecialLinearGroup.det_mapGL γ)
  have hdet : 0 < (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) :=
    det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  simpa only [ModularForm.SL_slash, hdet_eq, Complex.ofReal_one, one_zpow, one_mul,
    sl_smul_set] using peterssonInner_slash_slash_of_det_pos
      (g := (γ : GL (Fin 2) ℝ)) k hdet S f h

end UpperHalfPlane

/-! ### The Petersson product as an integral over a union of translated domains -/

namespace CuspForm

open Matrix.SpecialLinearGroup

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-- **The Petersson product of `S_k(Γ)` is a sum of integrals over translates of `𝒟`.** Each
coset summand of `CuspForm.peterssonInnerCosets` slashes both arguments by the same element of
`SL(2, ℤ)`, so `UpperHalfPlane.peterssonInner_slash_slash_SL` strips the slashes at the cost of
moving the domain. -/
theorem peterssonInnerCosets_eq_sum_smul_fd (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g =
      ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
        UpperHalfPlane.peterssonInner k ((q.out)⁻¹ • fd) ⇑f ⇑g := by
  rw [peterssonInnerCosets_def]
  exact Finset.sum_congr rfl fun q _ ↦ UpperHalfPlane.peterssonInner_slash_slash_SL _ _ _ _ _

/-- **The Petersson product of `S_k(Γ)` is a single integral over a union of translates.** The
sets `q⁻¹ • 𝒟ᵒ`, one for each coset of `Γ·{±I}` in `SL(2, ℤ)`, are open and pairwise disjoint,
and carry an integrable Petersson integrand, so the sum of integrals over them is the integral
over their union.

That union **is** a fundamental domain for the image of `Γ` in `PSL(2, ℤ)`:
`ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter`. -/
theorem peterssonInnerCosets_eq_peterssonInner (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g =
      UpperHalfPlane.peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out)⁻¹ • fdo)) ⇑f ⇑g := by
  rw [UpperHalfPlane.peterssonInner_def, integral_iUnion_fintype
      (fun q ↦ (isOpen_smul_fdo _).measurableSet)
      (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter Γ)
      (fun q ↦ (UpperHalfPlane.integrableOn_petersson_sl_smul_fd_left
        k (Γ.map (mapGL ℝ)) f g _).mono_set (Set.smul_set_mono fdo_subset_fd)),
    peterssonInnerCosets_eq_sum_smul_fd]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hae : ((((q.out)⁻¹ : SL(2, ℤ)) • fd : Set ℍ)) =ᵐ[volume]
      (((q.out)⁻¹ : SL(2, ℤ)) • fdo) := by
    rw [ModularGroup.sl_smul_set, ModularGroup.sl_smul_set]
    exact (MeasureTheory.smul_set_ae_eq _).mpr fd_ae_eq_fdo
  rw [UpperHalfPlane.peterssonInner_congr_set hae, UpperHalfPlane.peterssonInner_def]

end CuspForm
