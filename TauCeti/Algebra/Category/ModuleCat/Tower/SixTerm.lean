/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.LinearAlgebra.Exact

/-!
# The six-term sequence of `lim` and `lim¹`

Let `0 → A → B → C → 0` be a sequence of towers of modules over a ring `R`, given by morphisms
of towers `f : A ⟶ B` and `g : B ⟶ C` which form a short exact sequence `0 → Aₙ → Bₙ → Cₙ → 0`
at every level `n`. This file constructs the connecting map `lim C → lim¹ A` and proves that

```text
0 → lim A → lim B → lim C → lim¹ A → lim¹ B → lim¹ C → 0
```

is exact. The connecting map sends a compatible family `c ∈ lim C` to the class of the family
`a ∈ ∏ₙ Aₙ` with `f(a) = δ(b)`, where `b ∈ ∏ₙ Bₙ` is any family lifting `c` and `δ` is the shift
map of `B`; it is natural in morphisms of such sequences. As a consequence, `lim B → lim C` is
surjective whenever `lim¹ A` vanishes.

This is the snake lemma applied to the shift maps of the short exact sequence of products
`0 → ∏ₙ Aₙ → ∏ₙ Bₙ → ∏ₙ Cₙ → 0`. The ring `R` is only assumed associative and unital, so the
argument is carried out directly rather than through Mathlib's `SnakeLemma.δ`, which is stated
over commutative rings.

## Main declarations

* `TauCeti.ModuleTower.connectingMap`: the connecting map `lim C → lim¹ A`.
* `TauCeti.ModuleTower.connectingMap_eq_mk`: its value on a family `c` is the class of any `a`
  with `f(a) = δ(b)` and `g(b) = c`.
* `TauCeti.ModuleTower.limMap_injective`, `TauCeti.ModuleTower.exact_limMap`,
  `TauCeti.ModuleTower.exact_limMap_connectingMap`,
  `TauCeti.ModuleTower.exact_connectingMap_limOneMap`, `TauCeti.ModuleTower.exact_limOneMap`,
  `TauCeti.ModuleTower.limOneMap_surjective`: exactness of the six-term sequence.
* `TauCeti.ModuleTower.connectingMap_natural`: naturality of the connecting map.
* `TauCeti.ModuleTower.limMap_surjective_of_subsingleton_limOne`: if `lim¹ A = 0`, then
  `lim B → lim C` is surjective.

## References

* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks: Algebra, Lemma 10.86.4, Tag 0598](https://stacks.math.columbia.edu/tag/0598)
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti

namespace ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R] {A B C : ModuleTower.{v} R} {f : A ⟶ B} {g : B ⟶ C}

section Product

/-- A levelwise injective morphism of towers is injective on products. -/
theorem productMap_injective (hf : ∀ n, Function.Injective (f.app (op n)).hom) :
    Function.Injective (productMap f) := by
  rw [coe_productMap]
  exact Function.Injective.piMap hf

/-- A levelwise surjective morphism of towers is surjective on products. -/
theorem productMap_surjective (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Surjective (productMap g) := by
  rw [coe_productMap]
  exact Function.Surjective.piMap hg

/-- A levelwise exact pair of morphisms of towers is exact on products. -/
theorem exact_productMap (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom) :
    Function.Exact (productMap f) (productMap g) := by
  rw [coe_productMap, coe_productMap]
  exact Function.Exact.piMap hfg

end Product

section Exact

variable (hf : ∀ n, Function.Injective (f.app (op n)).hom)
  (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
  (hg : ∀ n, Function.Surjective (g.app (op n)).hom)

include hf in
/-- `lim A → lim B` is injective for a levelwise injective morphism of towers. -/
theorem limMap_injective : Function.Injective (limMap f) := fun x y hxy ↦
  Subtype.ext <| productMap_injective hf <| by
    rw [← coe_limMap_apply, ← coe_limMap_apply, hxy]

include hf hfg in
/-- Exactness of `lim A → lim B → lim C` for a levelwise exact sequence `0 → A → B → C`. -/
theorem exact_limMap : Function.Exact (limMap f) (limMap g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (exact_productMap hfg (x : B.Product)).1 <| by
      rw [← coe_limMap_apply, hx, Submodule.coe_zero]
    -- `a` is compatible because `f(δ(a)) = δ(f(a)) = δ(x) = 0` and `f` is injective.
    have hmem : a ∈ A.lim := by
      rw [mem_lim_iff_shift_eq_zero]
      apply productMap_injective hf
      rw [← shift_productMap_apply, ha, map_zero]
      exact B.mem_lim_iff_shift_eq_zero.1 x.2
    exact ⟨⟨a, hmem⟩, Subtype.ext ((coe_limMap_apply f _).trans ha)⟩
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    rw [coe_limMap_apply, coe_limMap_apply, Submodule.coe_zero]
    exact (exact_productMap hfg).apply_apply_eq_zero _

include hfg in
/-- If `b` lifts a compatible family of `C`, then the shift `δ(b)` comes from `∏ₙ Aₙ`. -/
theorem exists_productMap_eq_shift {b : B.Product} (hb : productMap g b ∈ C.lim) :
    ∃ a, productMap f a = B.shift b := by
  refine (exact_productMap hfg _).1 ?_
  rw [← shift_productMap_apply]
  exact C.mem_lim_iff_shift_eq_zero.1 hb

/-- The families in `∏ₙ Bₙ` lifting a compatible family of `C`, the domain of the relation
defining the connecting map. -/
private abbrev liftDomain (g : B ⟶ C) : Submodule R B.Product :=
  C.lim.comap (productMap g)

/-- The map sending a lift `b` of a compatible family of `C` to that family. -/
private def liftProj (g : B ⟶ C) : liftDomain g →ₗ[R] C.lim :=
  (productMap g).restrict fun _ hb ↦ hb

include hg in
private theorem liftProj_surjective : Function.Surjective (liftProj g) := by
  intro c
  obtain ⟨b, hb⟩ := productMap_surjective hg (c : C.Product)
  exact ⟨⟨b, by rw [Submodule.mem_comap, hb]; exact c.2⟩, Subtype.ext hb⟩

/-- The map sending a lift `b` of a compatible family of `C` to the class in `lim¹ A` of the
preimage of `δ(b)` under the injective map `∏ₙ Aₙ → ∏ₙ Bₙ`. -/
private def liftClass : liftDomain g →ₗ[R] A.limOne :=
  (LinearMap.range A.shift).mkQ ∘ₗ
    (LinearEquiv.ofInjective (productMap f) (productMap_injective hf)).symm.toLinearMap ∘ₗ
    (B.shift ∘ₗ (liftDomain g).subtype).codRestrict (LinearMap.range (productMap f))
      fun b ↦ by
        obtain ⟨a, ha⟩ := exists_productMap_eq_shift hfg b.2
        exact ⟨a, ha⟩

private theorem liftClass_apply (b : liftDomain g) {a : A.Product}
    (ha : productMap f a = B.shift b) :
    liftClass hf hfg b = Submodule.Quotient.mk a := by
  simp only [liftClass, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Submodule.mkQ_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext ha.symm

private theorem ker_liftProj_le :
    LinearMap.ker (liftProj g) ≤ LinearMap.ker (liftClass hf hfg) := by
  intro b hb
  rw [LinearMap.mem_ker] at hb ⊢
  -- A lift of the zero family is `f(a')`, and then `δ(f(a')) = f(δ(a'))` has class zero.
  obtain ⟨a', ha'⟩ := (exact_productMap hfg (b : B.Product)).1 (congrArg Subtype.val hb)
  rw [liftClass_apply hf hfg b (a := A.shift a'), Submodule.Quotient.mk_eq_zero]
  · exact LinearMap.mem_range_self _ _
  · rw [← ha', shift_productMap_apply]

/-- The connecting map `lim C → lim¹ A` of a levelwise short exact sequence `0 → A → B → C → 0`
of towers. It sends `c ∈ lim C` to the class of the family `a ∈ ∏ₙ Aₙ` with `f(a) = δ(b)`, for
any family `b ∈ ∏ₙ Bₙ` with `g(b) = c` (see `connectingMap_eq_mk`). -/
def connectingMap : C.lim →ₗ[R] A.limOne :=
  (LinearMap.ker (liftProj g)).liftQ (liftClass hf hfg) (ker_liftProj_le hf hfg) ∘ₗ
    ((liftProj g).quotKerEquivOfSurjective (liftProj_surjective hg)).symm.toLinearMap

/-- The connecting map sends `c ∈ lim C` to the class of `a`, whenever `g(b) = c` and
`f(a) = δ(b)`. -/
theorem connectingMap_eq_mk (c : C.lim) {b : B.Product} (hb : productMap g b = c)
    {a : A.Product} (ha : productMap f a = B.shift b) :
    connectingMap hf hfg hg c = Submodule.Quotient.mk a := by
  have hmem : b ∈ liftDomain g := by rw [Submodule.mem_comap, hb]; exact c.2
  have hc : c = liftProj g ⟨b, hmem⟩ := Subtype.ext hb.symm
  rw [connectingMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hc,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  exact liftClass_apply hf hfg _ ha

/-- Exactness of `lim B → lim C → lim¹ A`. -/
theorem exact_limMap_connectingMap :
    Function.Exact (limMap g) (connectingMap hf hfg hg) := by
  intro c
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := productMap_surjective hg (c : C.Product)
    obtain ⟨a, ha⟩ := exists_productMap_eq_shift hfg (b := b) (by rw [hb]; exact c.2)
    rw [connectingMap_eq_mk hf hfg hg c hb ha, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨a', rfl⟩ := hc
    -- Correcting `b` by `f(a')` gives a compatible family of `B` still lifting `c`.
    have hmem : b - productMap f a' ∈ B.lim := by
      rw [mem_lim_iff_shift_eq_zero, map_sub, shift_productMap_apply, ha, sub_self]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [coe_limMap_apply, Submodule.coe_mk, map_sub, hb,
      (exact_productMap hfg).apply_apply_eq_zero, sub_zero]
  · rintro ⟨x, rfl⟩
    have hx : B.shift x = 0 := B.mem_lim_iff_shift_eq_zero.1 x.2
    rw [connectingMap_eq_mk hf hfg hg _ (coe_limMap_apply g x).symm (a := 0)
      (by rw [map_zero, hx]), Submodule.Quotient.mk_zero]

/-- Exactness of `lim C → lim¹ A → lim¹ B`. -/
theorem exact_connectingMap_limOneMap :
    Function.Exact (connectingMap hf hfg hg) (limOneMap f) := by
  intro y
  induction y using Submodule.Quotient.induction_on with | H a => ?_
  rw [limOneMap_mk, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    have hmem : productMap g b ∈ C.lim := by
      rw [mem_lim_iff_shift_eq_zero, shift_productMap_apply, hb,
        (exact_productMap hfg).apply_apply_eq_zero]
    exact ⟨⟨_, hmem⟩, connectingMap_eq_mk hf hfg hg _ rfl hb.symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := productMap_surjective hg (c : C.Product)
    obtain ⟨a', ha'⟩ := exists_productMap_eq_shift hfg (b := b) (by rw [hb]; exact c.2)
    rw [connectingMap_eq_mk hf hfg hg c hb ha', Submodule.Quotient.eq] at hc
    -- `a' - a = δ(a'')`, so `f(a) = δ(b) - δ(f(a'')) = δ(b - f(a''))`.
    obtain ⟨a'', ha''⟩ := hc
    refine ⟨b - productMap f a'', ?_⟩
    rw [map_sub, ← ha', shift_productMap_apply, ← map_sub, ha'', sub_sub_cancel]

end Exact

/-- Exactness of `lim¹ A → lim¹ B → lim¹ C` for a levelwise exact sequence `A → B → C → 0`. -/
theorem exact_limOneMap (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Exact (limOneMap f) (limOneMap g) := by
  intro y
  constructor
  · induction y using Submodule.Quotient.induction_on with | H b => ?_
    rw [limOneMap_mk, Submodule.Quotient.mk_eq_zero]
    rintro ⟨c, hc⟩
    -- Lift `c` to `b'`; then `b - δ(b')` maps to zero, so it is `f(a)`.
    obtain ⟨b', rfl⟩ := productMap_surjective hg c
    obtain ⟨a, ha⟩ := (exact_productMap hfg (b - B.shift b')).1 <| by
      rw [map_sub, ← hc, ← shift_productMap_apply, sub_self]
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    rw [limOneMap_mk, ha, Submodule.Quotient.eq, sub_sub_cancel_left, neg_mem_iff]
    exact LinearMap.mem_range_self _ _
  · rintro ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    rw [limOneMap_mk, limOneMap_mk, (exact_productMap hfg).apply_apply_eq_zero,
      Submodule.Quotient.mk_zero]

/-- `lim¹ B → lim¹ C` is surjective for a levelwise surjective morphism of towers. -/
theorem limOneMap_surjective (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Surjective (limOneMap g) := by
  intro y
  induction y using Submodule.Quotient.induction_on with | H c => ?_
  obtain ⟨b, rfl⟩ := productMap_surjective hg c
  exact ⟨Submodule.Quotient.mk b, limOneMap_mk g b⟩

/-- If `lim¹ A = 0`, then `lim B → lim C` is surjective for a levelwise short exact sequence
`0 → A → B → C → 0` of towers. -/
theorem limMap_surjective_of_subsingleton_limOne
    (hf : ∀ n, Function.Injective (f.app (op n)).hom)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom) [Subsingleton A.limOne] :
    Function.Surjective (limMap g) := fun c ↦
  (exact_limMap_connectingMap hf hfg hg c).1 (Subsingleton.elim _ _)

/-- **Naturality of the connecting map.** A morphism `(α, β, γ)` of levelwise short exact sequences
of towers, from `0 → A → B → C → 0` to `0 → A' → B' → C' → 0`, commutes with the connecting
maps: `δ' ∘ lim γ = lim¹ α ∘ δ`. -/
theorem connectingMap_natural {A' B' C' : ModuleTower.{v} R} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    (hf : ∀ n, Function.Injective (f.app (op n)).hom)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom)
    (hf' : ∀ n, Function.Injective (f'.app (op n)).hom)
    (hfg' : ∀ n, Function.Exact (f'.app (op n)).hom (g'.app (op n)).hom)
    (hg' : ∀ n, Function.Surjective (g'.app (op n)).hom)
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C') (hαβ : f ≫ β = α ≫ f') (hβγ : g ≫ γ = β ≫ g') :
    connectingMap hf' hfg' hg' ∘ₗ limMap γ = limOneMap α ∘ₗ connectingMap hf hfg hg := by
  ext c
  obtain ⟨b, hb⟩ := productMap_surjective hg (c : C.Product)
  obtain ⟨a, ha⟩ := exists_productMap_eq_shift hfg (b := b) (by rw [hb]; exact c.2)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, connectingMap_eq_mk hf hfg hg c hb ha,
    limOneMap_mk]
  refine connectingMap_eq_mk hf' hfg' hg' _ (b := productMap β b) ?_ ?_
  · rw [coe_limMap_apply, ← hb, ← LinearMap.comp_apply (productMap g'), ← productMap_comp,
      ← hβγ, productMap_comp, LinearMap.comp_apply]
  · rw [← LinearMap.comp_apply (productMap f'), ← productMap_comp, ← hαβ, productMap_comp,
      LinearMap.comp_apply, ha, shift_productMap_apply]

end ModuleTower

end TauCeti
