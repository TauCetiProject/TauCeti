/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SnakeLemma
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.Algebra.Exact.Pi

/-!
# The six-term sequence of `lim` and `lim¹`

Let `0 → A → B → C → 0` be a sequence of towers of `R`-modules, given by morphisms of towers
`f : A ⟶ B` and `g : B ⟶ C` which are exact at every level, with `fₙ` injective and `gₙ`
surjective. Then the products of the terms form a short exact sequence commuting with the shift
maps, and the snake lemma gives an exact sequence

```text
0 → lim A → lim B → lim C → lim¹ A → lim¹ B → lim¹ C → 0.
```

This file constructs the connecting map `ModuleTower.connecting : lim C → lim¹ A`, characterizes
it by `ModuleTower.connecting_apply` (lift a compatible family `c` to a family `b` of `B`; its
shift comes from a family `a` of `A`, and the connecting map sends `c` to the class of `a`),
proves exactness at each of the six terms and the naturality of the connecting map in morphisms
of short exact sequences of towers. Each exactness statement only assumes the levelwise
injectivity, exactness and surjectivity it uses. As a consequence, `lim B → lim C` is surjective
whenever `lim¹ A` vanishes, for instance when the transitions of `A` are surjective
(`ModuleTower.subsingleton_limOne_of_surjective`).

This six-term sequence is the input to Milnor sequences for towers of complexes and to the long
exact sequences of derived limits of towers.

## Main declarations

* `TauCeti.ModuleTower.connecting`: the connecting map `lim C → lim¹ A`.
* `TauCeti.ModuleTower.exact_limMap`, `TauCeti.ModuleTower.exact_limMap_connecting`,
  `TauCeti.ModuleTower.exact_connecting_limOneMap`, `TauCeti.ModuleTower.exact_limOneMap`:
  exactness of the six-term sequence; exactness at the two ends is
  `TauCeti.ModuleTower.limMap_injective` and `TauCeti.ModuleTower.limOneMap_surjective`.
* `TauCeti.ModuleTower.connecting_naturality`: naturality of the connecting map.
* `TauCeti.ModuleTower.limMap_surjective_of_subsingleton_limOne`: `lim B → lim C` is surjective
  when `lim¹ A = 0`.

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

variable {R : Type u} [Ring R] {F G H : ModuleTower.{v} R} {f : F ⟶ G} {g : G ⟶ H}

section Product

/-- A levelwise exact pair of morphisms of towers is exact on products. -/
theorem exact_productMap (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom) :
    Function.Exact (productMap f) (productMap g) := by
  rw [coe_productMap, coe_productMap]
  exact Function.Exact.piMap hfg

/-- A levelwise exact pair of morphisms of towers composes to zero. -/
theorem comp_eq_zero_of_exact (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom) :
    f ≫ g = 0 := by
  ext n : 2
  exact ModuleCat.hom_ext (hfg (unop n)).linearMap_comp_eq_zero

/-- Every compatible family `c` of `C` lifts to a family `b` of `B` whose shift comes from `A`. -/
private theorem exists_lift (f : F ⟶ G) (g : G ⟶ H)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom) (c : H.lim) :
    ∃ b : G.Product, productMap g b = c ∧ ∃ a : F.Product, productMap f a = G.shift b := by
  obtain ⟨b, hb⟩ := productMap_surjective hg (c : H.Product)
  refine ⟨b, hb, (exact_productMap hfg (G.shift b)).1 ?_⟩
  rw [← shift_natural_apply, hb]
  exact LinearMap.mem_ker.1 (H.lim_eq_ker ▸ c.2)

end Product

section Lim

/-- Exactness of `lim A → lim B → lim C` for a levelwise exact sequence `0 → A → B → C`. -/
theorem exact_limMap (hf : ∀ n, Function.Injective (f.app (op n)).hom)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom) :
    Function.Exact (limMap f) (limMap g) := by
  refine Function.Exact.of_comp_of_mem_range ?_ fun y hy ↦ ?_
  · rw [← LinearMap.coe_comp, LinearMap.coe_zero_iff, ← limMap_comp, comp_eq_zero_of_exact hfg,
      limMap_zero]
  obtain ⟨x, hx⟩ := (exact_productMap hfg (y : G.Product)).1
    (by rw [← coe_limMap_apply, hy, Submodule.coe_zero])
  -- `x` is compatible because `f` is injective on products and commutes with the shifts.
  have hxlim : x ∈ F.lim := by
    rw [lim_eq_ker, LinearMap.mem_ker]
    refine productMap_injective hf ?_
    rw [← shift_natural_apply, hx, map_zero]
    exact LinearMap.mem_ker.1 (G.lim_eq_ker ▸ y.2)
  exact ⟨⟨x, hxlim⟩, Subtype.ext <| (coe_limMap_apply f _).trans hx⟩

/-- If `lim¹ A` vanishes, then for a levelwise exact sequence `A → B → C → 0` the map
`lim B → lim C` is surjective. -/
theorem limMap_surjective_of_subsingleton_limOne
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom) [Subsingleton F.limOne] :
    Function.Surjective (limMap g) := by
  intro z
  -- Lift `z` to a family `y`; the shift of `y` comes from a family `x` of `A`, which is itself a
  -- shift `F.shift w` since `lim¹ A = 0`. Then `y - f w` is compatible and maps to `z`.
  obtain ⟨y, hy, x, hx⟩ := exists_lift f g hfg hg z
  obtain ⟨w, hw⟩ := F.subsingleton_limOne_iff.1 ‹_› x
  have hlim : y - productMap f w ∈ G.lim := by
    rw [lim_eq_ker, LinearMap.mem_ker, map_sub, shift_natural_apply, hw, hx, sub_self]
  refine ⟨⟨_, hlim⟩, Subtype.ext ?_⟩
  rw [coe_limMap_apply, map_sub, hy, (exact_productMap hfg).apply_apply_eq_zero, sub_zero]

end Lim

section LimOne

/-- Exactness of `lim¹ A → lim¹ B → lim¹ C` for a levelwise exact sequence `A → B → C → 0`. -/
theorem exact_limOneMap (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Exact (limOneMap f) (limOneMap g) := by
  have hmapQ {P Q : ModuleTower.{v} R} (e : P ⟶ Q) : limOneMap e =
      (LinearMap.range P.shift).mapQ (LinearMap.range Q.shift) (productMap e)
        (range_shift_le_comap e) :=
    Submodule.linearMap_qext _ <| LinearMap.ext fun x ↦ limOneMap_mk e x
  rw [hmapQ, hmapQ, (exact_productMap hfg).exact_mapQ_iff]
  -- A shift `H.shift (g w)` is the image of the shift `G.shift w`.
  rintro _ ⟨-, z, rfl⟩
  obtain ⟨w, rfl⟩ := productMap_surjective hg z
  exact ⟨G.shift w, LinearMap.mem_range_self _ w, (shift_natural_apply g w).symm⟩

end LimOne

section Connecting

/-- `lim A ↪ ∏ₙ Aₙ → ∏ₙ Aₙ` is exact: `lim A` is the kernel of the shift. -/
private theorem exact_lim_subtype_shift (F : ModuleTower.{v} R) :
    Function.Exact F.lim.subtype F.shift := by
  rw [lim_eq_ker]
  exact LinearMap.exact_subtype_ker_map F.shift

/-- The shift naturality square of a morphism of towers, over `ℤ` as the snake lemma uses it. -/
private theorem shift_natural_int (f : F ⟶ G) :
    ((productMap f).restrictScalars ℤ).comp (F.shift.restrictScalars ℤ) =
      (G.shift.restrictScalars ℤ).comp ((productMap f).restrictScalars ℤ) :=
  LinearMap.ext fun x ↦ (LinearMap.congr_fun (shift_natural f) x).symm

variable (f g)
variable (hf : ∀ n, Function.Injective (f.app (op n)).hom)
  (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
  (hg : ∀ n, Function.Surjective (g.app (op n)).hom)

/-- The connecting map `lim C → lim¹ A` as a `ℤ`-linear map: the snake lemma for the shift maps
on the short exact sequence of products `0 → ∏ₙ Aₙ → ∏ₙ Bₙ → ∏ₙ Cₙ → 0`, applied over `ℤ`.
The `R`-linear version is `connecting`. -/
private def connectingAux : H.lim →ₗ[ℤ] F.limOne :=
  SnakeLemma.δ' (F.shift.restrictScalars ℤ) (G.shift.restrictScalars ℤ)
    (H.shift.restrictScalars ℤ) ((productMap f).restrictScalars ℤ)
    ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    ((productMap f).restrictScalars ℤ) ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    (shift_natural_int f) (shift_natural_int g) (H.lim.subtype.restrictScalars ℤ)
    (exact_lim_subtype_shift H) ((LinearMap.range F.shift).mkQ.restrictScalars ℤ)
    (LinearMap.exact_map_mkQ_range F.shift) (productMap_surjective hg) (productMap_injective hf)

/-- The snake-lemma characterization of `connectingAux`. -/
private theorem connectingAux_apply (c : H.lim) (b : G.Product) (hb : productMap g b = c)
    (a : F.Product) (ha : productMap f a = G.shift b) :
    connectingAux f g hf hfg hg c = Submodule.Quotient.mk a :=
  SnakeLemma.δ'_eq (x := c) (y := b) (hy := hb) (z := a) (hz := ha) ..

/-- The connecting map `lim C → lim¹ A` of the six-term sequence of a levelwise short exact
sequence of towers `0 → A → B → C → 0`. It sends a compatible family `c` to the class of any
family `a` of `A` with `f(a) = δ(b)` for some lift `b` of `c`; see `connecting_apply`. -/
def connecting : H.lim →ₗ[R] F.limOne where
  toFun := connectingAux f g hf hfg hg
  map_add' := map_add _
  map_smul' r c := by
    obtain ⟨b, hb, a, ha⟩ := exists_lift f g hfg hg c
    rw [connectingAux_apply f g hf hfg hg c b hb a ha,
      connectingAux_apply f g hf hfg hg (r • c) (r • b) (by rw [map_smul, hb, Submodule.coe_smul])
        (r • a) (by rw [map_smul, map_smul, ha]),
      RingHom.id_apply, Submodule.Quotient.mk_smul]

/-- **The connecting map of the six-term sequence.** If `b` lifts the compatible family `c` of
`C` and `f(a) = δ(b)`, then `c` is sent to the class of `a` in `lim¹ A`. -/
theorem connecting_apply (c : H.lim) (b : G.Product) (hb : productMap g b = c) (a : F.Product)
    (ha : productMap f a = G.shift b) :
    connecting f g hf hfg hg c = Submodule.Quotient.mk a :=
  connectingAux_apply f g hf hfg hg c b hb a ha

/-- The underlying function of `connecting` is that of the snake-lemma map `connectingAux`. -/
private theorem coe_connecting : ⇑(connecting f g hf hfg hg) = connectingAux f g hf hfg hg :=
  (rfl)

/-- Exactness of `lim B → lim C → lim¹ A`. -/
theorem exact_limMap_connecting : Function.Exact (limMap g) (connecting f g hf hfg hg) := by
  rw [coe_connecting]
  exact SnakeLemma.exact_δ'_right (F.shift.restrictScalars ℤ) (G.shift.restrictScalars ℤ)
    (H.shift.restrictScalars ℤ) ((productMap f).restrictScalars ℤ)
    ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    ((productMap f).restrictScalars ℤ) ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    (shift_natural_int f) (shift_natural_int g) (G.lim.subtype.restrictScalars ℤ)
    (exact_lim_subtype_shift G) (H.lim.subtype.restrictScalars ℤ) (exact_lim_subtype_shift H)
    ((LinearMap.range F.shift).mkQ.restrictScalars ℤ) (LinearMap.exact_map_mkQ_range F.shift)
    (productMap_surjective hg) (productMap_injective hf) ((limMap g).restrictScalars ℤ)
    (LinearMap.ext fun x ↦ (coe_limMap_apply g x).symm) Subtype.val_injective

/-- Exactness of `lim C → lim¹ A → lim¹ B`. -/
theorem exact_connecting_limOneMap : Function.Exact (connecting f g hf hfg hg) (limOneMap f) := by
  rw [coe_connecting]
  have hcomm : ((limOneMap f).restrictScalars ℤ).comp
      ((LinearMap.range F.shift).mkQ.restrictScalars ℤ) =
      ((LinearMap.range G.shift).mkQ.restrictScalars ℤ).comp ((productMap f).restrictScalars ℤ) :=
    LinearMap.ext fun x ↦ limOneMap_mk f x
  exact SnakeLemma.exact_δ'_left (F.shift.restrictScalars ℤ) (G.shift.restrictScalars ℤ)
    (H.shift.restrictScalars ℤ) ((productMap f).restrictScalars ℤ)
    ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    ((productMap f).restrictScalars ℤ) ((productMap g).restrictScalars ℤ) (exact_productMap hfg)
    (shift_natural_int f) (shift_natural_int g) (H.lim.subtype.restrictScalars ℤ)
    (exact_lim_subtype_shift H) ((LinearMap.range F.shift).mkQ.restrictScalars ℤ)
    (LinearMap.exact_map_mkQ_range F.shift) ((LinearMap.range G.shift).mkQ.restrictScalars ℤ)
    (LinearMap.exact_map_mkQ_range G.shift) (productMap_surjective hg) (productMap_injective hf)
    ((limOneMap f).restrictScalars ℤ) hcomm (Submodule.Quotient.mk_surjective _)

/-- **Naturality of the connecting map.** A morphism `(α, β, γ)` from the short exact sequence of
towers `0 → A → B → C → 0` to `0 → A' → B' → C' → 0` gives a commutative square relating the two
connecting maps `lim C → lim¹ A` and `lim C' → lim¹ A'`. -/
theorem connecting_naturality {F' G' H' : ModuleTower.{v} R} {f' : F' ⟶ G'} {g' : G' ⟶ H'}
    (hf' : ∀ n, Function.Injective (f'.app (op n)).hom)
    (hfg' : ∀ n, Function.Exact (f'.app (op n)).hom (g'.app (op n)).hom)
    (hg' : ∀ n, Function.Surjective (g'.app (op n)).hom)
    (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H') (h₁ : f ≫ β = α ≫ f') (h₂ : g ≫ γ = β ≫ g') :
    limOneMap α ∘ₗ connecting f g hf hfg hg = connecting f' g' hf' hfg' hg' ∘ₗ limMap γ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨b, hb, a, ha⟩ := exists_lift f g hfg hg c
  rw [LinearMap.comp_apply, LinearMap.comp_apply, connecting_apply f g hf hfg hg c b hb a ha,
    limOneMap_mk]
  -- The images `β(b)` and `α(a)` are the lifts computing the connecting map of `γ(c)`.
  refine (connecting_apply f' g' hf' hfg' hg' _ (productMap β b) ?_ (productMap α a) ?_).symm
  · rw [coe_limMap_apply, ← productMap_comp_apply, ← h₂, productMap_comp_apply, hb]
  · rw [← productMap_comp_apply, ← h₁, productMap_comp_apply, ha, shift_natural_apply]

end Connecting

end ModuleTower

end TauCeti
