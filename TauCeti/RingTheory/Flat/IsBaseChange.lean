/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.FiveLemma
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Injectivity of base-change maps along flat ring maps

Let `S` be a flat `R`-algebra. Mathlib's `IsBaseChange.of_left_exact` says that kernels commute
with base change from `R` to `S`: in a commutative diagram with left exact rows

```text
0 → M₁ --f--> M₂ --g--> M₃
    |h₁       |h₂       |h₃
    v         v         v
0 → N₁ --f'-> N₂ --g'-> N₃
```

of `R`-modules `Mᵢ` and `S`-modules `Nᵢ`, if `h₂` and `h₃` are base changes, so is `h₁`. This file
records the weaker hypotheses that suffice, in the form used to compare sections of sheaves over
covers whose overlaps are only partially controlled:

* if `f` is injective and `h₂` is a base change, the induced map `S ⊗[R] M₁ → N₁` is injective;
* if `h₂` is a base change and the induced map `S ⊗[R] M₃ → N₃` is only injective, then `h₁` is
  still a base change.

Flatness of `S` can also be traded for flatness of `M₃`: if the top row is a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` with `M₃` flat, then it stays exact after tensoring with any `S`, so `h₁`
is a base change for every `R`-algebra `S`. This is the form in which the kernel of a surjective
Čech differential onto flat modules commutes with arbitrary base change.

For compatible pairs `ker (f.coprod (-g))`, projection to the second factor also has an
injective scalar-extension comparison if the comparisons for `f` and for multiplication on
`ker g` are injective. This is the linear-algebra step in formal gluing
([Stacks, Proposition 15.91.16](https://stacks.math.columbia.edu/tag/05ER)).

## Main results

* `LinearMap.liftBaseChange_injective_of_isBaseChange`: injectivity of `S ⊗[R] M₁ → N₁`.
* `LinearMap.injective_liftBaseChange_snd_ker_coprod`: injectivity of the comparison from
  compatible pairs to the second factor.
* `IsBaseChange.of_left_exact_of_lTensor`: the five-lemma criterion for an arbitrary `R`-algebra
  `S`, assuming that tensoring the top row with `S` keeps it left exact.
* `IsBaseChange.of_left_exact_of_injective`: the variant of `IsBaseChange.of_left_exact` with an
  injective right base-change map.
* `IsBaseChange.of_left_exact_of_surjective`: the variant for an arbitrary `R`-algebra `S`, when
  the top row is short exact with flat right term.
-/

public section

open TensorProduct

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

section LeftExact

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  {h₁ : M₁ →ₗ[R] N₁} {h₂ : M₂ →ₗ[R] N₂} {h₃ : M₃ →ₗ[R] N₃}
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

/-- Let `S` be flat over `R` and let `f : M₁ → M₂` be injective. If `h₂ : M₂ → N₂` is a base change
and `h₂ ∘ f = f' ∘ h₁`, then the map `S ⊗[R] M₁ → N₁` induced by `h₁` is injective. -/
theorem LinearMap.liftBaseChange_injective_of_isBaseChange [Module.Flat R S]
    (comm : h₂.comp f = (f'.restrictScalars R).comp h₁) (isb₂ : IsBaseChange S h₂)
    (inj : Function.Injective f) : Function.Injective (h₁.liftBaseChange S) := by
  refine Function.Injective.of_comp (f := f') ?_
  rw [← LinearMap.coe_comp, ← LinearMap.liftBaseChange_comp_baseChange S comm,
    LinearMap.coe_comp, LinearMap.baseChange_eq_lTensor]
  exact isb₂.liftBaseChange_injective.comp (Module.Flat.lTensor_preserves_injective_linearMap f inj)

/-- **Kernels commute with base change when tensoring keeps the top row left exact.** Let `S` be
any `R`-algebra, and consider a commutative diagram with rows `M₁ → M₂ → M₃` of `R`-modules and a
left exact row `0 → N₁ → N₂ → N₃` of `S`-modules. If the tensored row
`0 → S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃` is left exact, `h₂ : M₂ → N₂` is a base change and the map
`S ⊗[R] M₃ → N₃` induced by `h₃` is injective, then `h₁ : M₁ → N₁` is a base change. The variants
`IsBaseChange.of_left_exact_of_injective` and `IsBaseChange.of_left_exact_of_surjective` supply
the exactness of the tensored row from flatness of `S` or of `M₃`. -/
theorem IsBaseChange.of_left_exact_of_lTensor
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂)
    (isb₂ : IsBaseChange S h₂) (inj₃ : Function.Injective (h₃.liftBaseChange S))
    (exactS : Function.Exact (f.lTensor S) (g.lTensor S))
    (injS : Function.Injective (f.lTensor S))
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ := by
  have hb : Function.Bijective (h₁.liftBaseChange S) := by
    refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
      ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
      (f'.restrictScalars R) (g'.restrictScalars R) ((h₁.liftBaseChange S).restrictScalars R)
      ((h₂.liftBaseChange S).restrictScalars R) ((h₃.liftBaseChange S).restrictScalars R)
      ?_ ?_ exactS exact₂ ?_ inj₃ injS inj₂
    · exact congrArg (LinearMap.restrictScalars R)
        (LinearMap.liftBaseChange_comp_baseChange S comm₁).symm
    · exact congrArg (LinearMap.restrictScalars R)
        (LinearMap.liftBaseChange_comp_baseChange S comm₂).symm
    · exact isb₂.liftBaseChange_bijective
  exact IsBaseChange.iff_liftBaseChange_bijective.2 hb

/-- **Kernels commute with flat base change**, with an injective comparison on the right. Let `S`
be flat over `R`, and consider a commutative diagram with left exact rows
`0 → M₁ → M₂ → M₃` of `R`-modules and `0 → N₁ → N₂ → N₃` of `S`-modules. If `h₂ : M₂ → N₂` is a
base change and the map `S ⊗[R] M₃ → N₃` induced by `h₃` is injective, then `h₁ : M₁ → N₁` is a
base change. Compare `IsBaseChange.of_left_exact`, which assumes that `h₃` is a base change. -/
theorem IsBaseChange.of_left_exact_of_injective [Module.Flat R S]
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂)
    (isb₂ : IsBaseChange S h₂) (inj₃ : Function.Injective (h₃.liftBaseChange S))
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ :=
  IsBaseChange.of_left_exact_of_lTensor S comm₁ comm₂ isb₂ inj₃
    (Module.Flat.lTensor_exact S exact₁)
    (Module.Flat.lTensor_preserves_injective_linearMap f inj₁) exact₂ inj₂

/-- **Kernels of surjections onto flat modules commute with base change.** Let `S` be any
`R`-algebra, and consider a commutative diagram whose top row `0 → M₁ → M₂ → M₃ → 0` is a short
exact sequence of `R`-modules with `M₃` flat, and whose bottom row `0 → N₁ → N₂ → N₃` is a left
exact sequence of `S`-modules. If `h₂ : M₂ → N₂` is a base change and the map `S ⊗[R] M₃ → N₃`
induced by `h₃` is injective, then `h₁ : M₁ → N₁` is a base change. Compare
`IsBaseChange.of_left_exact_of_injective`, which assumes `S` flat instead. -/
theorem IsBaseChange.of_left_exact_of_surjective [Module.Flat R M₃]
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂)
    (isb₂ : IsBaseChange S h₂) (inj₃ : Function.Injective (h₃.liftBaseChange S))
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f) (surj₁ : Function.Surjective g)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ :=
  -- Tensoring with `S` keeps `f` injective because the cokernel `M₃` of `f` is flat.
  IsBaseChange.of_left_exact_of_lTensor S comm₁ comm₂ isb₂ inj₃ (lTensor_exact S exact₁ surj₁)
    (LinearMap.lTensor_injective_of_exact_of_flat g surj₁ f inj₁ exact₁ S) exact₂ inj₂

end LeftExact

namespace LinearMap

open Function

variable {S} {M N P : Type*} [Module.Flat R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- Scalar extension of the projection from compatible pairs to the second factor is
injective if the comparison for the first map and multiplication on the kernel of the
second map are injective. No finiteness or faithful flatness is required. -/
theorem injective_liftBaseChange_snd_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[S] P)
    (hf : Injective (f.liftBaseChange S))
    (hg : Injective (((LinearMap.id : g.ker →ₗ[S] g.ker).restrictScalars R).liftBaseChange S)) :
    Injective (((LinearMap.snd R M N).domRestrict
      (f.coprod (-g.restrictScalars R)).ker).liftBaseChange S) := by
  let K := (f.coprod (-g.restrictScalars R)).ker
  let a : g.ker →ₗ[R] K :=
    ((LinearMap.inr R M N).comp (g.ker.subtype.restrictScalars R)).codRestrict K
      (fun n ↦ by simp [K, LinearMap.mem_ker])
  let b : K →ₗ[R] M := (LinearMap.fst R M N).domRestrict K
  let c : K →ₗ[R] N := (LinearMap.snd R M N).domRestrict K
  have hK (k : K) : f k.val.1 = g k.val.2 := by
    simpa only [K, LinearMap.mem_ker, LinearMap.coprod_apply,
      LinearMap.neg_apply, LinearMap.coe_restrictScalars, sub_eq_zero, ← sub_eq_add_neg]
      using k.property
  have ha : Injective a := by
    intro n n' h
    exact Subtype.ext (congrArg (fun k : K ↦ k.val.2) h)
  have hab : Exact a b := by
    intro k
    constructor
    · intro hk
      refine ⟨⟨k.val.2, ?_⟩, ?_⟩
      · have hk0 : k.val.1 = 0 := by simpa [b] using hk
        simpa [hk0] using (hK k).symm
      · apply Subtype.ext
        exact Prod.ext hk.symm rfl
    · rintro ⟨n, rfl⟩
      simp [a, b, LinearMap.codRestrict]
  have hfc : (f.liftBaseChange S).restrictScalars R ∘ₗ b.lTensor S =
      (g.restrictScalars R) ∘ₗ (c.liftBaseChange S).restrictScalars R := by
    ext s k
    simp [b, c, hK k]
  let μ := ((LinearMap.id : g.ker →ₗ[S] g.ker).restrictScalars R).liftBaseChange S
  have hca : (c.liftBaseChange S).restrictScalars R ∘ₗ a.lTensor S =
      (g.ker.subtype.restrictScalars R) ∘ₗ μ.restrictScalars R := by
    ext s n
    simp [a, c, μ, LinearMap.codRestrict]
  -- Apply the four lemma to the exact rows starting in zero, with vertical maps
  -- multiplication, the compatible-pairs comparison, and the comparison for `f`.
  exact LinearMap.injective_of_surjective_of_injective_of_injective
    (0 : Unit →ₗ[R] S ⊗[R] g.ker) (a.lTensor S) (b.lTensor S)
    (0 : Unit →ₗ[R] g.ker) (g.ker.subtype.restrictScalars R) (g.restrictScalars R)
    (0 : Unit →ₗ[R] Unit) (μ.restrictScalars R) ((c.liftBaseChange S).restrictScalars R)
    ((f.liftBaseChange S).restrictScalars R) (by simp) hca.symm hfc.symm
    ((LinearMap.exact_zero_iff_injective Unit _).mpr
      (Module.Flat.lTensor_preserves_injective_linearMap a ha))
    (Module.Flat.lTensor_exact S hab)
    ((LinearMap.exact_zero_iff_injective Unit _).mpr g.ker.subtype_injective)
    (fun _ ↦ ⟨(), rfl⟩) hg hf

end LinearMap
