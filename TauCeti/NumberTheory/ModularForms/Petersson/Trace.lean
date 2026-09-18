/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.NumberTheory.ModularForms.Petersson.Unitary

/-!
# The Petersson adjoint of the trace and of the double coset operators

For a subgroup `Γ' ≤ Γ` of finite index in `SL₂(ℤ)`, Mathlib's `CuspForm.trace` sends a cusp form
`h` for `Γ'` to the cusp form `∑ᵢ h ∣[k] γᵢ` for `Γ`, the sum running over representatives `γᵢ`
of the right cosets `Γ' \ Γ`. For the un-normalised Petersson products
`CuspForm.peterssonInnerCosets` of the two levels, the trace is **adjoint to restriction**:

```text
⟪tr h, g⟫_Γ = ⟪h, g⟫_Γ'        (g a cusp form for Γ).
```

Unfolded, `⟪h, g⟫_Γ'` is an integral over a fundamental domain for `Γ'`, which the translates
`γᵢ • D` of a fundamental domain `D` for `Γ` tile; moving each piece back to `D` turns `h` into
`h ∣[k] γᵢ` and leaves `g` unchanged. Here the argument is run on the defining coset sums, where
it becomes a reindexing: the cosets of `Γ'·{±I}` in `SL₂(ℤ)` are in bijection with pairs of a
coset of `Γ·{±I}` and a coset of `Γ'` in `Γ`. That bijection needs the hypothesis
`-I ∈ Γ → -I ∈ Γ'`, and the identity needs it too: if `-I` lies in `Γ` but not in `Γ'`, then the
trace counts every translate twice, and in even weight the left side is twice the right.

Combined with the conjugation law `TauCeti.CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq`,
this gives the adjoint of the **double coset operator**. For `α ∈ GL₂(ℝ)` of positive determinant,
`f ↦ tr (f ∣[k] α)` — the trace, from `α⁻¹ Γ₁ α ∩ Γ₂` to `Γ₂`, of the translate of `f` by `α` — is
the operator `f ↦ f[Γ₁ α Γ₂]_k` of Diamond–Shurman §5.1, from `S_k(Γ₁)` to `S_k(Γ₂)`, and its
Petersson adjoint is the double coset operator of the main involution `α^ι = (det α) · α⁻¹`:

```text
⟪f[Γ₁ α Γ₂]_k, g⟫_Γ₂ = ⟪f, g[Γ₂ α^ι Γ₁]_k⟫_Γ₁.
```

The Hecke operators `Tₙ` are double coset operators of this kind, so this is the analytic core
of the adjoint formula `Tₙ* = ⟨n⟩⁻¹ Tₙ` at indices prime to the level.

The Petersson products here are not normalised by the volume of the fundamental domain. When
`Γ₁ = Γ₂` that makes no difference to the identity, and it is Diamond–Shurman's Proposition
5.5.2(b). When `Γ₁ ≠ Γ₂` it is the un-normalised products that match with no volume factor.

## Main results

* `CuspForm.peterssonInnerCosets_sum_slash_left`: the adjunction for the trace written with an
  arbitrary family of coset representatives.
* `CuspForm.peterssonInnerCosets_trace_left`: the same for Mathlib's `CuspForm.trace`.
* `CuspForm.peterssonInnerCosets_trace_translate`: the Petersson adjoint of the double coset
  operator `f ↦ tr (f ∣[k] α)` is `g ↦ tr (g ∣[k] α^ι)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 5.1 and 5.5.
-/

public section

open UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

namespace CuspForm

variable {k : ℤ}

/-! ### The trace is adjoint to restriction -/

/-- **The trace is adjoint to restriction, for a chosen family of coset representatives.** Let
`Γ' ≤ Γ` be of finite index in `SL₂(ℤ)` with `-I ∈ Γ → -I ∈ Γ'`, and let `γ` enumerate `Γ / Γ'`,
so that the `(γ i)⁻¹` represent the right cosets `Γ' \ Γ`. If `F` is the trace
`∑ᵢ h ∣[k] (γ i)⁻¹` of a cusp form `h` for `Γ'`, then for every cusp form `g` for `Γ`

```text
⟪F, g⟫_Γ = ⟪h, g⟫_Γ'.
```

The trace is taken as data `F` with its defining equation, so that a caller holding its own coset
representatives — the Hecke operators come with theirs — need not pass through the quotient. For
Mathlib's `CuspForm.trace` see `peterssonInnerCosets_trace_left`. -/
theorem peterssonInnerCosets_sum_slash_left {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    {ι : Type*} [Fintype ι] (γ : ι → Γ)
    (hγ : Function.Bijective fun i ↦ (QuotientGroup.mk (γ i) : Γ ⧸ Γ'.subgroupOf Γ))
    (h : CuspForm (Γ'.map (mapGL ℝ)) k) (g F : CuspForm (Γ.map (mapGL ℝ)) k)
    (hF : ⇑F = ∑ i, ⇑h ∣[k] ((γ i : SL(2, ℤ)))⁻¹) :
    peterssonInnerCosets F g =
      peterssonInnerCosets h (CuspForm.ofLe (Subgroup.map_mono hle) g) := by
  -- the cosets of `Γ'·{±I}` are the pairs of a coset `p` of `Γ·{±I}` and an index `i`, via
  -- `(p, i) ↦ p.out * γ i`: Mathlib's coset tower `G/H ≃ G/K × K/H`, with the second factor
  -- `Γ·{±I} / Γ'·{±I}` enumerated by the `γ i`
  set Φ : (SL(2, ℤ) ⧸ Γ.withCenter) × ι → SL(2, ℤ) ⧸ Γ'.withCenter :=
    fun x ↦ QuotientGroup.mk (x.1.out * (γ x.2 : SL(2, ℤ))) with hΦ_def
  have hwc : Γ'.withCenter ≤ Γ.withCenter :=
    Subgroup.withCenter_le_iff.mpr ⟨hle.trans Γ.le_withCenter, Γ.center_le_withCenter⟩
  set j : ι → Γ.withCenter ⧸ Γ'.withCenter.subgroupOf Γ.withCenter :=
    fun i ↦ QuotientGroup.mk ⟨γ i, Γ.le_withCenter (γ i).2⟩
  have hj : Function.Bijective j := by
    refine ⟨fun i i' hii' ↦ hγ.1 (QuotientGroup.eq.mpr ?_), fun q ↦ ?_⟩
    · have hx : (γ i : SL(2, ℤ))⁻¹ * γ i' ∈ Γ ⊓ Γ'.withCenter :=
        ⟨Γ.mul_mem (Γ.inv_mem (γ i).2) (γ i').2,
          Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq (s := Γ'.withCenter.subgroupOf _)).mp hii')⟩
      rwa [Subgroup.inf_withCenter_eq_of_le hle hneg] at hx
    · obtain ⟨x, hx, hsign⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp q.out.2
      obtain ⟨i, hi⟩ := hγ.2 (QuotientGroup.mk ⟨x, hx⟩)
      have hix : (γ i : SL(2, ℤ))⁻¹ * x ∈ Γ' := by
        have := (QuotientGroup.eq (s := Γ'.subgroupOf Γ)).mp hi
        rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this
      refine ⟨i, ?_⟩
      rw [← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.mpr (Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr
        ⟨_, hix, ?_⟩)
      rw [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rcases hsign with hsign | hsign <;> rw [hsign]
      · exact Or.inl rfl
      · exact Or.inr (mul_neg _ _)
  have hΦ : Function.Bijective Φ :=
    (Subgroup.quotientEquivProdOfLE' hwc Quotient.out Quotient.out_eq').symm.bijective.comp
      (Function.bijective_id.prodMap hj)
  rw [peterssonInnerCosets_def, peterssonInnerCosets_def,
    ← (Equiv.ofBijective Φ hΦ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- the summand at `(p, i)` pairs `h ∣ (γ i)⁻¹` against `g`, both moved by `p.out⁻¹`, since
  -- `g ∣ (γ i)⁻¹ = g`
  have hsummand : ∀ i, (⇑g ∣[k] (p.out)⁻¹) = (⇑g ∣[k] ((γ i : SL(2, ℤ))⁻¹ * (p.out)⁻¹)) :=
    fun i ↦ by
      rw [SlashAction.slash_mul, SlashInvariantFormClass.SL_slash_eq g _ (Γ.inv_mem (γ i).2)]
  rw [hF, SlashAction.sum_slash, UpperHalfPlane.peterssonInner_sum_left k fd Finset.univ _ _
    fun i _ ↦ by
      rw [hsummand i, ← SlashAction.slash_mul]
      simpa only [CuspForm.coe_ofLe] using
        integrableOn_petersson_slash_left k _ h (CuspForm.ofLe (Subgroup.map_mono hle) g) _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Equiv.ofBijective_apply, hΦ_def, peterssonInner_slash_inv_out, mul_inv_rev, hsummand i,
    CuspForm.coe_ofLe, SlashAction.slash_mul, SlashAction.slash_mul]

/-- **The trace is adjoint to restriction.** Let `𝒢 ≤ GL₂(ℝ)` meet the image of a finite-index
`Γ ≤ SL₂(ℤ)` in the image of `Γ' ≤ Γ`, with `-I ∈ Γ → -I ∈ Γ'`. For a cusp form `h` for `𝒢` and
a cusp form `g` for `Γ`, the Petersson product of Mathlib's trace `CuspForm.trace` of `h` down to
`Γ` against `g` is the product at level `Γ'` of `h` and `g`, both read as forms for `Γ'`:

```text
⟪tr h, g⟫_Γ = ⟪h, g⟫_Γ'.
```

The group `𝒢` is general because that is how the trace arises: for the double coset operators
`h` is a translate `f ∣[k] α`, modular for the conjugate `α⁻¹ Γ₁ α`, which is not contained in
`Γ`. The hypothesis on `-I` is needed: when `-I ∈ Γ` but `-I ∉ Γ'`, the trace counts each coset
of `Γ'·{±I}` twice. -/
theorem peterssonInnerCosets_trace_left {𝒢 : Subgroup (GL (Fin 2) ℝ)} {Γ Γ' : Subgroup SL(2, ℤ)}
    [Γ.FiniteIndex] [Γ'.FiniteIndex] [𝒢.IsFiniteRelIndex (Γ.map (mapGL ℝ))]
    (hΓ' : Γ'.map (mapGL ℝ) = 𝒢 ⊓ Γ.map (mapGL ℝ))
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    (h : CuspForm 𝒢 k) (g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets (CuspForm.trace (Γ.map (mapGL ℝ)) h) g =
      peterssonInnerCosets (CuspForm.ofLe (hΓ'.trans_le inf_le_left) h)
        (CuspForm.ofLe (hΓ'.trans_le inf_le_right) g) := by
  have hinj : Function.Injective (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) := mapGL_injective
  have hle : Γ' ≤ Γ := (Subgroup.map_le_map_iff_of_injective hinj).mp (hΓ'.trans_le inf_le_right)
  set e := Subgroup.equivMapOfInjective Γ (mapGL ℝ) hinj
  -- membership in `Γ'` is membership of the image in `𝒢`
  have key : ∀ y : Γ.map (mapGL ℝ), ((e.symm y : Γ) : SL(2, ℤ)) ∈ Γ' ↔ (y : GL (Fin 2) ℝ) ∈ 𝒢 := by
    intro y
    have hy : mapGL ℝ ((e.symm y : Γ) : SL(2, ℤ)) = y := by
      rw [← Subgroup.coe_equivMapOfInjective_apply Γ (mapGL ℝ) hinj, MulEquiv.apply_symm_apply]
    rw [← Subgroup.mem_map_iff_mem hinj, hΓ', Subgroup.mem_inf, hy]
    exact and_iff_left y.2
  -- the instance `CuspForm.trace` sums with
  let : Fintype (Γ.map (mapGL ℝ) ⧸ 𝒢.subgroupOf (Γ.map (mapGL ℝ))) := Fintype.ofFinite _
  -- the coset spaces of the trace and of `Γ / Γ'` correspond along `e`
  let E : Γ.map (mapGL ℝ) ⧸ 𝒢.subgroupOf (Γ.map (mapGL ℝ)) ≃ Γ ⧸ Γ'.subgroupOf Γ :=
    Quotient.congr e.symm.toEquiv fun a b ↦ by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_inv,
        ← map_mul, key]
  have hE : (fun q ↦ (QuotientGroup.mk (e.symm q.out) : Γ ⧸ Γ'.subgroupOf Γ)) = E := by
    funext q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  refine peterssonInnerCosets_sum_slash_left hle hneg
    (fun q : Γ.map (mapGL ℝ) ⧸ 𝒢.subgroupOf (Γ.map (mapGL ℝ)) ↦ e.symm q.out)
    (hE ▸ E.bijective) _ g _ ?_
  rw [CuspForm.coe_trace]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- the `SL(2, ℤ)` slash action goes through the coercion to `GL (Fin 2) ℝ`, which is `mapGL ℝ`
  have hq : (((e.symm q.out : Γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) = (q.out : GL (Fin 2) ℝ) :=
    (Subgroup.coe_equivMapOfInjective_apply Γ (mapGL ℝ) hinj _).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply _))
  conv_lhs => rw [← Quotient.out_eq q]
  rw [SlashInvariantForm.quotientFunc_mk, CuspForm.coe_ofLe, ModularForm.SL_slash,
    map_inv, map_inv, hq]

/-! ### The adjoint of a double coset operator -/

/-- **The Petersson adjoint of a double coset operator.** Let `Γ₁`, `Γ₂` be of finite index in
`SL₂(ℤ)`, with `-I ∈ Γ₁ ↔ -I ∈ Γ₂`, and let `α ∈ GL₂(ℝ)` have positive determinant, with
`α⁻¹ Γ₁ α ∩ Γ₂` of finite index in `Γ₂` and `α Γ₂ α⁻¹ ∩ Γ₁` of finite index in `Γ₁`. The operator
`f ↦ tr (f ∣[k] α)` from `S_k(Γ₁)` to `S_k(Γ₂)` — Mathlib's `CuspForm.trace` of the translate
`CuspForm.translate f α`, which is the double coset operator `f[Γ₁ α Γ₂]_k` — has Petersson
adjoint `g ↦ tr (g ∣[k] α^ι)`, the double coset operator of the main involution
`α^ι = TauCeti.adjugateGL α`:

```text
⟪f[Γ₁ α Γ₂]_k, g⟫_Γ₂ = ⟪f, g[Γ₂ α^ι Γ₁]_k⟫_Γ₁.
```

Both sides are computed at the intermediate level: the trace on either side is adjoint to
restriction (`peterssonInnerCosets_trace_left`), and `α` conjugates `α⁻¹ Γ₁ α ∩ Γ₂` onto
`Γ₁ ∩ α Γ₂ α⁻¹`, carrying one intermediate product to the other
(`TauCeti.CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq`). The main involution rather than
`α⁻¹` appears because `α^ι α = (det α) · 1`, whose slash is multiplication by `(det α) ^ (k - 2)`:
exactly the factor the conjugation produces.

The two finite-index hypotheses are instance arguments because `CuspForm.trace` requires them.
For `α` with rational entries both hold, since `Γ₁` and `Γ₂` are commensurable with all their
rational conjugates; that is not proved here. -/
theorem peterssonInnerCosets_trace_translate {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} [Γ₁.FiniteIndex]
    [Γ₂.FiniteIndex] {α : GL (Fin 2) ℝ} (hα : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ).det)
    [(ConjAct.toConjAct α⁻¹ • Γ₁.map (mapGL ℝ)).IsFiniteRelIndex (Γ₂.map (mapGL ℝ))]
    [(ConjAct.toConjAct (TauCeti.adjugateGL α)⁻¹ • Γ₂.map (mapGL ℝ)).IsFiniteRelIndex
      (Γ₁.map (mapGL ℝ))]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ₁ ↔ (-1 : SL(2, ℤ)) ∈ Γ₂)
    (f : CuspForm (Γ₁.map (mapGL ℝ)) k) (g : CuspForm (Γ₂.map (mapGL ℝ)) k) :
    peterssonInnerCosets (CuspForm.trace (Γ₂.map (mapGL ℝ)) (CuspForm.translate f α)) g =
      peterssonInnerCosets f
        (CuspForm.trace (Γ₁.map (mapGL ℝ)) (CuspForm.translate g (TauCeti.adjugateGL α))) := by
  set 𝒢₁ := ConjAct.toConjAct α⁻¹ • Γ₁.map (mapGL ℝ)
  set 𝒢₂ := ConjAct.toConjAct (TauCeti.adjugateGL α)⁻¹ • Γ₂.map (mapGL ℝ)
  -- the two intermediate levels `α⁻¹ Γ₁ α ∩ Γ₂` and `Γ₁ ∩ α Γ₂ α⁻¹`, inside `SL(2, ℤ)`
  have h₃ : (Γ₂ ⊓ 𝒢₁.comap (mapGL ℝ)).map (mapGL ℝ) = 𝒢₁ ⊓ Γ₂.map (mapGL ℝ) := by
    rw [Subgroup.map_inf_comap, inf_comm]
  have h₃' : (Γ₁ ⊓ 𝒢₂.comap (mapGL ℝ)).map (mapGL ℝ) = 𝒢₂ ⊓ Γ₁.map (mapGL ℝ) := by
    rw [Subgroup.map_inf_comap, inf_comm]
  have := Subgroup.finiteIndex_inf_comap Γ₂ 𝒢₁ (mapGL ℝ)
  have := Subgroup.finiteIndex_inf_comap Γ₁ 𝒢₂ (mapGL ℝ)
  have hc₁ : (-1 : GL (Fin 2) ℝ) ∈ Subgroup.center (GL (Fin 2) ℝ) :=
    Subgroup.mem_center_iff.mpr fun g ↦ by rw [mul_neg_one, neg_one_mul]
  have hneg₁ : (-1 : SL(2, ℤ)) ∈ Γ₂ → (-1 : SL(2, ℤ)) ∈ Γ₂ ⊓ 𝒢₁.comap (mapGL ℝ) := by
    intro h
    have h1 : (-1 : GL (Fin 2) ℝ) ∈ Γ₁.map (mapGL ℝ) := ⟨-1, hneg.mpr h, mapGL_neg_one⟩
    refine Subgroup.mem_inf.mpr ⟨h, ?_⟩
    rw [Subgroup.mem_comap, mapGL_neg_one]
    exact Subgroup.mem_conjAct_smul_of_mem_center hc₁ _ h1
  have hneg₂ : (-1 : SL(2, ℤ)) ∈ Γ₁ → (-1 : SL(2, ℤ)) ∈ Γ₁ ⊓ 𝒢₂.comap (mapGL ℝ) := by
    intro h
    have h2 : (-1 : GL (Fin 2) ℝ) ∈ Γ₂.map (mapGL ℝ) := ⟨-1, hneg.mp h, mapGL_neg_one⟩
    refine Subgroup.mem_inf.mpr ⟨h, ?_⟩
    rw [Subgroup.mem_comap, mapGL_neg_one]
    exact Subgroup.mem_conjAct_smul_of_mem_center hc₁ _ h2
  -- `α` conjugates `α⁻¹ Γ₁ α ∩ Γ₂` onto `Γ₁ ∩ α Γ₂ α⁻¹`, because `α⁻¹ (α^ι)⁻¹` is a scalar
  have hconj : ConjAct.toConjAct α⁻¹ • (Γ₁ ⊓ 𝒢₂.comap (mapGL ℝ)).map (mapGL ℝ) =
      (Γ₂ ⊓ 𝒢₁.comap (mapGL ℝ)).map (mapGL ℝ) := by
    have hmul : α⁻¹ * (TauCeti.adjugateGL α)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det α)⁻¹ := by
      rw [Matrix.GeneralLinearGroup.adjugateGL_eq_scalar_mul_inv, mul_inv_rev, inv_inv,
        inv_mul_cancel_left, map_inv]
    have hc : Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det α)⁻¹ ∈
        Subgroup.center (GL (Fin 2) ℝ) :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨_, rfl⟩
    rw [h₃, h₃', Subgroup.smul_inf, ← mul_smul, ← map_mul, hmul,
      Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.center_le_normalizer _ hc), inf_comm]
  have hscal : TauCeti.adjugateGL α * α =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det α) := by
    rw [Matrix.GeneralLinearGroup.adjugateGL_eq_scalar_mul_inv, inv_mul_cancel_right]
  -- the conjugation step, with the scalar `(det α) ^ (k - 2)` from `α^ι α = (det α) · 1`
  set d : ℂ := ((α : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2)
  have hd : d ≠ 0 := zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hα.ne')
  have hC := TauCeti.CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq hα hconj
    (f := CuspForm.ofLe (h₃'.trans_le inf_le_right) f)
    (g := CuspForm.ofLe (h₃'.trans_le inf_le_left) (CuspForm.translate g (TauCeti.adjugateGL α)))
    (F := CuspForm.ofLe (h₃.trans_le inf_le_left) (CuspForm.translate f α))
    (G := d • CuspForm.ofLe (h₃.trans_le inf_le_right) g)
    (by rw [CuspForm.coe_ofLe, CuspForm.coe_translate_gl, CuspForm.coe_ofLe])
    (by rw [CuspForm.coe_ofLe, CuspForm.coe_translate_gl, ← SlashAction.slash_mul, hscal,
      ModularForm.slash_scalar, FunLike.coe_smul, CuspForm.coe_ofLe,
      Matrix.GeneralLinearGroup.val_det_apply])
  rw [peterssonInnerCosets_smul_right] at hC
  rw [peterssonInnerCosets_trace_left h₃ hneg₁, mul_left_cancel₀ hd hC,
    ← peterssonInnerCosets_conj_symm, ← peterssonInnerCosets_trace_left h₃' hneg₂,
    peterssonInnerCosets_conj_symm]

end CuspForm
