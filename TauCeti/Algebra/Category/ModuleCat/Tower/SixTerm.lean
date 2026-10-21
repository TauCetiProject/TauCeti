/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
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
`0 → ∏ₙ Aₙ → ∏ₙ Bₙ → ∏ₙ Cₙ → 0`, whose kernels and cokernels are the rows of `lim` and `lim¹`.
It is Mathlib's categorical snake lemma `CategoryTheory.ShortComplex.SnakeInput` in the abelian
category `ModuleCat R`, so the ring `R` need only be associative and unital. The exactness
statements not involving the connecting map are proved directly, so that each assumes only the
levelwise hypotheses it uses.

## Main declarations

* `TauCeti.ModuleTower.snakeInput`: the snake input formed by the shift maps of the products.
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

open CategoryTheory Limits Opposite

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

/-- `lim A` is a kernel of the shift map in `ModuleCat R`. -/
private def isLimitLim (F : ModuleTower.{v} R) :
    IsLimit (KernelFork.ofι (f := ModuleCat.ofHom F.shift) (ModuleCat.ofHom F.lim.subtype)
      (ModuleCat.hom_ext <| LinearMap.ext fun x ↦ (mem_lim_iff_shift_eq_zero _).1 x.2)) :=
  ModuleCat.isLimitKernelFork _ _
    (LinearMap.exact_iff.2 (by
      rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, Submodule.range_subtype, lim_eq_ker]))
    Subtype.val_injective

/-- `lim¹ A` is a cokernel of the shift map in `ModuleCat R`. -/
private def isColimitLimOne (F : ModuleTower.{v} R) :
    IsColimit (CokernelCofork.ofπ (f := ModuleCat.ofHom F.shift)
      (ModuleCat.ofHom (LinearMap.range F.shift).mkQ)
      (ModuleCat.hom_ext <| LinearMap.range_mkQ_comp _)) :=
  ModuleCat.isColimitCokernelCofork _ _ (LinearMap.exact_iff.2 (Submodule.ker_mkQ _))
    (Submodule.mkQ_surjective _)

include hfg in
/-- The composite of a levelwise exact pair of morphisms of towers vanishes. -/
private theorem comp_eq_zero : f ≫ g = 0 := by
  ext n x
  exact (hfg n.unop).apply_apply_eq_zero x

/-- The short complex `∏ₙ Aₙ → ∏ₙ Bₙ → ∏ₙ Cₙ` of product maps. -/
private abbrev productComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom (productMap f)) (ModuleCat.ofHom (productMap g)) <| by
    rw [← ModuleCat.ofHom_comp, ← productMap_comp, comp_eq_zero hfg, productMap_zero]
    rfl

/-- The snake input of a levelwise short exact sequence `0 → A → B → C → 0` of towers: the shift
maps of the short exact sequence of products `0 → ∏ₙ Aₙ → ∏ₙ Bₙ → ∏ₙ Cₙ → 0`, whose kernels
and cokernels are the rows `lim A → lim B → lim C` and `lim¹ A → lim¹ B → lim¹ C`. -/
def snakeInput : ShortComplex.SnakeInput (ModuleCat.{v} R) where
  L₀ := ShortComplex.mk (ModuleCat.ofHom (limMap f)) (ModuleCat.ofHom (limMap g)) <| by
    rw [← ModuleCat.ofHom_comp, ← limMap_comp, comp_eq_zero hfg, limMap_zero]
    rfl
  L₁ := productComplex hfg
  L₂ := productComplex hfg
  L₃ := ShortComplex.mk (ModuleCat.ofHom (limOneMap f)) (ModuleCat.ofHom (limOneMap g)) <| by
    rw [← ModuleCat.ofHom_comp, ← limOneMap_comp, comp_eq_zero hfg, limOneMap_zero]
    rfl
  v₀₁ :=
    { τ₁ := ModuleCat.ofHom A.lim.subtype
      τ₂ := ModuleCat.ofHom B.lim.subtype
      τ₃ := ModuleCat.ofHom C.lim.subtype }
  v₁₂ :=
    { τ₁ := ModuleCat.ofHom A.shift
      τ₂ := ModuleCat.ofHom B.shift
      τ₃ := ModuleCat.ofHom C.shift
      comm₁₂ := ModuleCat.hom_ext (shift_natural f).symm
      comm₂₃ := ModuleCat.hom_ext (shift_natural g).symm }
  v₂₃ :=
    { τ₁ := ModuleCat.ofHom (LinearMap.range A.shift).mkQ
      τ₂ := ModuleCat.ofHom (LinearMap.range B.shift).mkQ
      τ₃ := ModuleCat.ofHom (LinearMap.range C.shift).mkQ }
  w₀₂ := by
    ext x : 3 <;> exact (mem_lim_iff_shift_eq_zero _).1 x.2
  w₁₃ := by
    ext x : 3 <;> exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ x)
  h₀ := ShortComplex.isLimitOfIsLimitπ _
    ((KernelFork.isLimitMapConeEquiv _ _).symm A.isLimitLim)
    ((KernelFork.isLimitMapConeEquiv _ _).symm B.isLimitLim)
    ((KernelFork.isLimitMapConeEquiv _ _).symm C.isLimitLim)
  h₃ := ShortComplex.isColimitOfIsColimitπ _
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm A.isColimitLimOne)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm B.isColimitLimOne)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm C.isColimitLimOne)
  L₁_exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 (exact_productMap hfg)
  epi_L₁_g := (ModuleCat.epi_iff_surjective _).2 (productMap_surjective hg)
  L₂_exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 (exact_productMap hfg)
  mono_L₂_f := (ModuleCat.mono_iff_injective _).2 (productMap_injective hf)

/-- The connecting map `lim C → lim¹ A` of a levelwise short exact sequence `0 → A → B → C → 0`
of towers, the connecting map of `snakeInput`. It sends `c ∈ lim C` to the class of the family
`a ∈ ∏ₙ Aₙ` with `f(a) = δ(b)`, for any family `b ∈ ∏ₙ Bₙ` with `g(b) = c` (see
`connectingMap_eq_mk`). -/
def connectingMap : C.lim →ₗ[R] A.limOne :=
  (snakeInput hf hfg hg).δ.hom

/-- The connecting map sends `c ∈ lim C` to the class of `a`, whenever `g(b) = c` and
`f(a) = δ(b)`. -/
theorem connectingMap_eq_mk (c : C.lim) {b : B.Product} (hb : productMap g b = c)
    {a : A.Product} (ha : productMap f a = B.shift b) :
    connectingMap hf hfg hg c = Submodule.Quotient.mk a :=
  (snakeInput hf hfg hg).δ_apply c b a hb ha

/-- Exactness of `lim B → lim C → lim¹ A`. -/
theorem exact_limMap_connectingMap :
    Function.Exact (limMap g) (connectingMap hf hfg hg) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (snakeInput hf hfg hg).L₁'_exact

/-- Exactness of `lim C → lim¹ A → lim¹ B`. -/
theorem exact_connectingMap_limOneMap :
    Function.Exact (connectingMap hf hfg hg) (limOneMap f) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (snakeInput hf hfg hg).L₂'_exact

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
  -- The morphisms of towers induce a morphism of snake inputs, levelwise on `lim`, the products
  -- and `lim¹`.
  let ψ : productComplex hfg ⟶ productComplex hfg' :=
    { τ₁ := ModuleCat.ofHom (productMap α)
      τ₂ := ModuleCat.ofHom (productMap β)
      τ₃ := ModuleCat.ofHom (productMap γ)
      comm₁₂ := by simp only [← ModuleCat.ofHom_comp, ← productMap_comp, hαβ]
      comm₂₃ := by simp only [← ModuleCat.ofHom_comp, ← productMap_comp, hβγ] }
  let φ : snakeInput hf hfg hg ⟶ snakeInput hf' hfg' hg' :=
    { f₀ :=
        { τ₁ := ModuleCat.ofHom (limMap α)
          τ₂ := ModuleCat.ofHom (limMap β)
          τ₃ := ModuleCat.ofHom (limMap γ)
          comm₁₂ := by simp only [snakeInput, ← ModuleCat.ofHom_comp, ← limMap_comp, hαβ]
          comm₂₃ := by simp only [snakeInput, ← ModuleCat.ofHom_comp, ← limMap_comp, hβγ] }
      f₁ := ψ
      f₂ := ψ
      f₃ :=
        { τ₁ := ModuleCat.ofHom (limOneMap α)
          τ₂ := ModuleCat.ofHom (limOneMap β)
          τ₃ := ModuleCat.ofHom (limOneMap γ)
          comm₁₂ := by simp only [snakeInput, ← ModuleCat.ofHom_comp, ← limOneMap_comp, hαβ]
          comm₂₃ := by simp only [snakeInput, ← ModuleCat.ofHom_comp, ← limOneMap_comp, hβγ] }
      comm₀₁ := by ext x : 3 <;> exact coe_limMap_apply _ x
      comm₁₂ := by ext x : 3 <;> exact shift_productMap_apply _ x
      comm₂₃ := by ext x : 3 <;> exact (limOneMap_mk _ x).symm }
  exact congrArg ModuleCat.Hom.hom (ShortComplex.SnakeInput.naturality_δ φ).symm

end ModuleTower

end TauCeti
