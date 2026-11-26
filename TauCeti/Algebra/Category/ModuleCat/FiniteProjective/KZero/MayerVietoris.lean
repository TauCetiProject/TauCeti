/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Map
public import TauCeti.Data.Matrix.Pullback
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Elementary

/-!
# The Mayer–Vietoris sequence of `K₀` at `K₀(A₁) × K₀(A₂)`

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms between arbitrary (possibly
noncommutative) rings, and let `D = A₁ ×_Q A₂` be their fibre product, Mathlib's
`RingHom.pullback π₁ π₂`, with projections `p₁ : D →+* A₁` and `p₂ : D →+* A₂`. When at least one
of `π₁` and `π₂` is surjective, the projective `K₀`-groups (`TauCeti.KZero`) satisfy the last
exactness statement of the Mayer–Vietoris sequence of the Milnor square:

```text
K₀(D) ──(K₀(p₁), K₀(p₂))──▶ K₀(A₁) × K₀(A₂) ──(x, y) ↦ K₀(π₁) x - K₀(π₂) y──▶ K₀(Q)
```

is exact at `K₀(A₁) × K₀(A₂)`. The composite is zero for every commutative square
(`TauCeti.KZero.map_pullback_comm_sq`), without any surjectivity hypothesis.

The proof works with idempotent matrices (`TauCeti.IdempotentMonoid.kZeroEquiv`). Write the two
classes as `[e₁] - m₁[A₁]` and `[e₂] - m₂[A₂]`. Their images in `K₀(Q)` agree exactly when, after
adding identity blocks, the idempotent matrices `π₁(e₁)` and `π₂(e₂)` become equivalent. Equivalent
idempotents are conjugate by an elementary matrix after padding with zero blocks
(`Matrix.IdempotentEquivalent.exists_mem_elementarySubgroup_conj_fromBlocks_zero`), and elementary
matrices lift along a surjective leg. So `e₁` (if `π₁` is onto, say) can be replaced by an
equivalent idempotent whose image over `Q` *equals* the padded `π₂(e₂)`
(`Matrix.IdempotentEquivalent.exists_idempotentEquivalent_map_eq`). The two matrices then glue
entrywise to an idempotent matrix over `D` (`RingHom.pullbackMatrixEquiv`), whose class maps to the
given pair. Surjectivity of one leg is used only to lift that elementary conjugator. Neither
injectivity of `K₀(D) → K₀(A₁) × K₀(A₂)` nor surjectivity of `K₀(A₁) × K₀(A₂) → K₀(Q)` is claimed;
both fail in general.

## Main results

* `TauCeti.KZero.map_pullback_comm_sq`: the square of `K₀`-groups induced by the fibre product
  square of rings commutes.
* `TauCeti.KZero.mayerVietoris_exact`: exactness of
  `K₀(A₁ ×_Q A₂) → K₀(A₁) × K₀(A₂) → K₀(Q)` at the middle term, when `π₁` or `π₂` is surjective.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  Theorem 3.3 (the exact sequence `K₀(D) → K₀(A₁) ⊕ K₀(A₂) → K₀(Q)` of a fibre product square
  with a surjective leg).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter II, §2 (idempotent matrices and `K₀`), and Chapter III,
  Theorem 2.6 (the Mayer–Vietoris sequence of a Milnor square).
-/

public section

noncomputable section

open Matrix _root_.Algebra

namespace TauCeti.KZero

open IdempotentMonoid

universe u

variable {A₁ A₂ Q : Type u} [Ring A₁] [Ring A₂] [Ring Q] (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)

/-- The square of `K₀`-groups induced by the fibre product square of rings commutes:
`K₀(π₁) ∘ K₀(p₁) = K₀(π₂) ∘ K₀(p₂)` on `K₀(A₁ ×_Q A₂)`. -/
theorem map_pullback_comm_sq :
    (map π₁).comp (map (π₁.pullbackFst π₂)) = (map π₂).comp (map (π₁.pullbackSnd π₂)) := by
  rw [← map_comp, ← map_comp, RingHom.pullback_comm_sq]

/-- **Gluing idempotents.** If idempotent matrices `e₁` over `A₁` and `e₂` over `A₂` are
equivalent to idempotent matrices `f₁` and `f₂` of a common size with `π₁(f₁) = π₂(f₂)`, then the
pair of classes `([e₁], [e₂])` comes from `K₀(A₁ ×_Q A₂)`: it is the image of the class of the
idempotent matrix over the fibre product glued from `f₁` and `f₂`. -/
private theorem mk_prod_mk_mem_range_of_map_eq {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    [Fintype μ] {e₁ : Matrix ι ι A₁} {e₂ : Matrix κ κ A₂} {f₁ : Matrix μ μ A₁}
    {f₂ : Matrix μ μ A₂} (h₁ : IdempotentEquivalent e₁ f₁) (h₂ : IdempotentEquivalent e₂ f₂)
    (hf : f₁.map π₁ = f₂.map π₂) :
    (kZeroEquiv A₁ (GrothendieckAddGroup.of (mk e₁ h₁.isIdempotentElem_left)),
        kZeroEquiv A₂ (GrothendieckAddGroup.of (mk e₂ h₂.isIdempotentElem_left))) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  classical
  let f : Matrix μ μ (π₁.pullback π₂) := (π₁.pullbackMatrixEquiv π₂).symm ⟨(f₁, f₂), hf⟩
  have hf' : IsIdempotentElem f := IsIdempotentElem.map
    (Subtype.ext (Prod.ext h₁.isIdempotentElem_right.eq h₂.isIdempotentElem_right.eq))
    (π₁.pullbackMatrixEquiv π₂).symm
  have hf₁ : f.map (π₁.pullbackFst π₂) = f₁ := by ext i j; simp [f]
  have hf₂ : f.map (π₁.pullbackSnd π₂) = f₂ := by ext i j; simp [f]
  refine ⟨kZeroEquiv _ (GrothendieckAddGroup.of (mk f hf')), ?_⟩
  rw [AddMonoidHom.prod_apply, map_kZeroEquiv_of_mk, map_kZeroEquiv_of_mk,
    mk_congr_matrix _ h₁.isIdempotentElem_right hf₁,
    mk_congr_matrix _ h₂.isIdempotentElem_right hf₂, mk_eq_mk h₁, mk_eq_mk h₂]

/-- **Aligning idempotents along a surjective leg.** If the images over `Q` of idempotent matrices
`e₁` over `A₁` and `e₂` over `A₂` are equivalent idempotents, and one of `π₁` and `π₂` is
surjective, then the pair of classes `([e₁], [e₂])` comes from `K₀(A₁ ×_Q A₂)`. Padded by zero
blocks, the idempotent over the surjective leg is equivalent to one whose image over `Q` is exactly
the padded image of the other. -/
private theorem mk_prod_mk_mem_range_of_idempotentEquivalent
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) {ι κ : Type*} [Fintype ι]
    [Fintype κ] {e₁ : Matrix ι ι A₁} {e₂ : Matrix κ κ A₂}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (he : IdempotentEquivalent (e₁.map π₁) (e₂.map π₂)) :
    (kZeroEquiv A₁ (GrothendieckAddGroup.of (mk e₁ he₁)),
        kZeroEquiv A₂ (GrothendieckAddGroup.of (mk e₂ he₂))) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  classical
  rcases h with hπ₁ | hπ₂
  · obtain ⟨f₁, h₁, hf₁⟩ := he.exists_idempotentEquivalent_map_eq hπ₁ he₁
    -- `e₂` is equivalent to its padding `(0 ⊕ e₂) ⊕ 0`, whose image is the image of `f₁`.
    exact mk_prod_mk_mem_range_of_map_eq π₁ π₂ h₁
      (he₂.idempotentEquivalent_fromBlocks_fromBlocks_zero ι (ι ⊕ κ)).symm
      (by simp [hf₁, fromBlocks_map])
  · obtain ⟨f₂, h₂, hf₂⟩ := he.symm.exists_idempotentEquivalent_map_eq hπ₂ he₂
    -- `e₁` is equivalent to its padding `(0 ⊕ e₁) ⊕ 0`, whose image is the image of `f₂`.
    exact mk_prod_mk_mem_range_of_map_eq π₁ π₂
      (he₁.idempotentEquivalent_fromBlocks_fromBlocks_zero κ (κ ⊕ ι)).symm h₂
      (by simp [hf₂, fromBlocks_map])

/-- The pair `([A₁], [A₂])` of classes of the free modules of rank one is the image of `[D]`. -/
private theorem regular_prod_regular_mem_range :
    (SplitK0.of.{u} (finiteProjectiveModulesRegular A₁ᵐᵒᵖ),
        SplitK0.of.{u} (finiteProjectiveModulesRegular A₂ᵐᵒᵖ)) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range :=
  ⟨SplitK0.of.{u} (finiteProjectiveModulesRegular (π₁.pullback π₂)ᵐᵒᵖ), by
    rw [AddMonoidHom.prod_apply, map_of_finiteProjectiveModulesRegular,
      map_of_finiteProjectiveModulesRegular]⟩

/-- **Removing identity blocks.** If the pair of classes of `e₁ ⊕ 1ₘ` and `e₂ ⊕ 1ₙ` comes from
`K₀(A₁ ×_Q A₂)`, then so does every pair `(x, y)` with `x + c[A₁] = [e₁] + m[A₁]` and
`y + c[A₂] = [e₂] + n[A₂]`: the two pairs differ by `c` copies of `([A₁], [A₂])`, which is the
image of `c[D]`. -/
private theorem mem_range_of_mk_fromBlocks_one_mem_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e₁ : Matrix ι ι A₁} {e₂ : Matrix κ κ A₂} (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) {m n : ℕ} (c : ℕ) {x : KZero A₁} {y : KZero A₂}
    (hx : x + c • SplitK0.of.{u} (finiteProjectiveModulesRegular A₁ᵐᵒᵖ) =
      kZeroEquiv A₁ (GrothendieckAddGroup.of (mk e₁ he₁)) +
        m • SplitK0.of.{u} (finiteProjectiveModulesRegular A₁ᵐᵒᵖ))
    (hy : y + c • SplitK0.of.{u} (finiteProjectiveModulesRegular A₂ᵐᵒᵖ) =
      kZeroEquiv A₂ (GrothendieckAddGroup.of (mk e₂ he₂)) +
        n • SplitK0.of.{u} (finiteProjectiveModulesRegular A₂ᵐᵒᵖ))
    (hmem : (kZeroEquiv A₁ (GrothendieckAddGroup.of
          (mk (fromBlocks e₁ 0 0 (1 : Matrix (Fin m) (Fin m) A₁))
            (he₁.fromBlocks_zero₁₂_zero₂₁ .one))),
        kZeroEquiv A₂ (GrothendieckAddGroup.of
          (mk (fromBlocks e₂ 0 0 (1 : Matrix (Fin n) (Fin n) A₂))
            (he₂.fromBlocks_zero₁₂_zero₂₁ .one)))) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range) :
    (x, y) ∈ ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  rw [kZeroEquiv_of_mk_fromBlocks_one he₁, kZeroEquiv_of_mk_fromBlocks_one he₂, ← hx, ← hy,
    ← Prod.mk_add_mk, ← Prod.smul_mk] at hmem
  exact (add_mem_cancel_right (nsmul_mem (regular_prod_regular_mem_range π₁ π₂) c)).1 hmem

/-- If idempotent matrices `e₁` over `A₁` and `e₂` over `A₂` have images with the same class in
`K₀(Q)`, and one of `π₁` and `π₂` is surjective, then `([e₁], [e₂])` comes from `K₀(A₁ ×_Q A₂)`.
After adding a common identity block the images become equivalent idempotents, and the identity
blocks themselves come from the free module over the fibre product. -/
private theorem mk_prod_mk_mem_range (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {ι κ : Type*} [Fintype ι] [Fintype κ] {e₁ : Matrix ι ι A₁}
    {e₂ : Matrix κ κ A₂} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (he : kZeroEquiv Q (GrothendieckAddGroup.of (mk (e₁.map π₁) (he₁.matrix_map π₁))) =
      kZeroEquiv Q (GrothendieckAddGroup.of (mk (e₂.map π₂) (he₂.matrix_map π₂)))) :
    (kZeroEquiv A₁ (GrothendieckAddGroup.of (mk e₁ he₁)),
        kZeroEquiv A₂ (GrothendieckAddGroup.of (mk e₂ he₂))) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  rw [kZeroEquiv_of, kZeroEquiv_of, toKZero_mk_eq_toKZero_mk_iff] at he
  obtain ⟨k, hk⟩ := he
  exact mem_range_of_mk_fromBlocks_one_mem_range π₁ π₂ he₁ he₂ k rfl rfl
    (mk_prod_mk_mem_range_of_idempotentEquivalent π₁ π₂ h _ _
      (by simpa [fromBlocks_map, Matrix.map_one] using hk))

/-- **Exactness of the Mayer–Vietoris sequence of `K₀` at `K₀(A₁) × K₀(A₂)`.** For ring
homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`, at least one of which is surjective, a pair of
classes `(x, y)` with `K₀(π₁) x = K₀(π₂) y` in `K₀(Q)` is `(K₀(p₁) z, K₀(p₂) z)` for some class `z`
of the fibre product `A₁ ×_Q A₂`, where `p₁` and `p₂` are its two projections; and conversely.
That is, the sequence
`K₀(A₁ ×_Q A₂) → K₀(A₁) × K₀(A₂) → K₀(Q)`, `z ↦ (K₀(p₁) z, K₀(p₂) z)`,
`(x, y) ↦ K₀(π₁) x - K₀(π₂) y`, is exact at the middle term. -/
theorem mayerVietoris_exact (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    Function.Exact ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂)))
      ((map π₁).comp (AddMonoidHom.fst (KZero A₁) (KZero A₂)) -
        (map π₂).comp (AddMonoidHom.snd (KZero A₁) (KZero A₂))) := by
  rintro ⟨x, y⟩
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd, sub_eq_zero, ← AddMonoidHom.coe_range, SetLike.mem_coe]
  refine ⟨fun hxy ↦ ?_, ?_⟩
  · -- Write `x = [e₁] - m₁[A₁]` and `y = [e₂] - m₂[A₂]`.
    obtain ⟨n₁, e₁, he₁, m₁, rfl⟩ := exists_kZeroEquiv_sub_nsmul_eq x
    obtain ⟨n₂, e₂, he₂, m₂, rfl⟩ := exists_kZeroEquiv_sub_nsmul_eq y
    rw [map_sub, map_sub, map_nsmul, map_nsmul, map_kZeroEquiv_of_mk, map_kZeroEquiv_of_mk,
      map_of_finiteProjectiveModulesRegular, map_of_finiteProjectiveModulesRegular,
      sub_eq_sub_iff_add_eq_add, ← kZeroEquiv_of_mk_fromBlocks_one,
      ← kZeroEquiv_of_mk_fromBlocks_one] at hxy
    -- So `[π₁(e₁ ⊕ 1_{m₂})] = [π₂(e₂ ⊕ 1_{m₁})]` in `K₀(Q)`, and `(e₁ ⊕ 1_{m₂}, e₂ ⊕ 1_{m₁})`
    -- glue; subtract the class of the free module `D^{m₁ + m₂}`.
    exact mem_range_of_mk_fromBlocks_one_mem_range π₁ π₂ he₁ he₂ (m := m₂) (n := m₁) (m₁ + m₂)
      (by rw [add_nsmul]; abel) (by rw [add_nsmul]; abel)
      (mk_prod_mk_mem_range π₁ π₂ h _ _ (by simpa [fromBlocks_map, Matrix.map_one] using hxy))
  · rintro ⟨z, hz⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hz
    exact DFunLike.congr_fun (map_pullback_comm_sq π₁ π₂) z

end TauCeti.KZero
