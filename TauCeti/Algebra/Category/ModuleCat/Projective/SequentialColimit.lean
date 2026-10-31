/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# The telescope of a sequence of modules and its projective dimension

Let `F₀ → F₁ → F₂ → ⋯` be a sequence of `R`-modules, a functor `F : ℕ ⥤ ModuleCat R`, with
transition maps `φₙ : Fₙ → Fₙ₊₁`. Its colimit `M` sits in the *telescope* short exact sequence

```text
0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → M → 0,
```

whose first map sends `x ∈ Fₙ` to `x - φₙ(x) ∈ Fₙ ⊕ Fₙ₊₁` and whose second map is induced by the
legs `Fₙ → M` of the colimit cocone. Dimension shifting along it shows that if every `Fₙ` has
projective dimension at most `d`, then `M` has projective dimension at most `d + 1`: the direct sum
`⨁ₙ Fₙ` has projective dimension at most `d`, as coproducts of modules are exact.

The bound is sharp: `ℚ` is the colimit of `ℤ →2 ℤ →3 ℤ →4 ⋯` (multiplication by `n + 2` at the
`n`-th step) of free `ℤ`-modules but is not projective. This is how a bound on the projective
dimension of modules over the stages of a sequential colimit of rings, such as the perfection of
a ring of characteristic `p`, leads to a bound over the colimit.

## Main declarations

* `ModuleCat.telescopeDiff`: the map `⨁ₙ Fₙ → ⨁ₙ Fₙ`, `x ↦ x - φₙ(x)`, which is injective
  (`ModuleCat.telescopeDiff_injective`).
* `ModuleCat.telescopeShortComplex`: the telescope sequence of a cocone over `F`, short exact when
  the cocone is a colimit (`ModuleCat.shortExact_telescopeShortComplex`).
* `ModuleCat.hasProjectiveDimensionLT_succ_of_isColimit`: the colimit of a sequence of modules of
  projective dimension `< n` has projective dimension `< n + 1`.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341 (the telescope
  sequence).
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), proof of Proposition 11.31.
-/

public section

open CategoryTheory Limits DirectSum

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)

/-- The difference map of the telescope of a sequence `F₀ → F₁ → ⋯` of modules: the endomorphism
of `⨁ₙ Fₙ` sending `x` in the summand `Fₙ` to `x - φₙ(x)`, where `φₙ(x)` lies in the summand
`Fₙ₊₁`. -/
noncomputable def telescopeDiff : (⨁ n, F.obj n) →ₗ[R] ⨁ n, F.obj n :=
  toModule R ℕ _ fun n ↦ lof R ℕ (fun n ↦ F.obj n) n -
    lof R ℕ (fun n ↦ F.obj n) (n + 1) ∘ₗ (F.map (homOfLE (n.le_add_right 1))).hom

@[simp]
theorem telescopeDiff_lof (n : ℕ) (x : F.obj n) :
    telescopeDiff F (lof R ℕ (fun n ↦ F.obj n) n x) =
      lof R ℕ (fun n ↦ F.obj n) n x -
        lof R ℕ (fun n ↦ F.obj n) (n + 1) (F.map (homOfLE (n.le_add_right 1)) x) := by
  simp [telescopeDiff]

theorem telescopeDiff_apply_zero (a : ⨁ n, F.obj n) : telescopeDiff F a 0 = a 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n x =>
    rw [← lof_eq_of R, telescopeDiff_lof, DFinsupp.sub_apply]
    rcases n with _ | n <;> simp [lof_eq_of, of_eq_of_ne]
  | add a b ha hb => simp [ha, hb]

theorem telescopeDiff_apply_succ (a : ⨁ n, F.obj n) (n : ℕ) :
    telescopeDiff F a (n + 1) = a (n + 1) - F.map (homOfLE (n.le_add_right 1)) (a n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    rw [← lof_eq_of R, telescopeDiff_lof, DFinsupp.sub_apply]
    rcases eq_or_ne m n with rfl | hmn
    · simp [lof_eq_of, of_eq_of_ne]
    · rcases eq_or_ne m (n + 1) with rfl | -
      · simp [lof_eq_of, of_eq_of_ne]
      · simp [lof_eq_of, of_eq_of_ne, Ne.symm hmn]
  | add a b ha hb => simp [ha, hb, sub_add_sub_comm]

/-- The difference map of the telescope is injective: the component of `a` in degree `n` is
recovered from the components of `telescopeDiff F a` in degrees `≤ n`. -/
theorem telescopeDiff_injective : Function.Injective (telescopeDiff F) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ DFinsupp.ext fun n ↦ ?_
  induction n with
  | zero => simpa [telescopeDiff_apply_zero] using congr($ha 0)
  | succ n ih => simpa [telescopeDiff_apply_succ, ih] using congr($ha (n + 1))

/-- The telescope sequence `⨁ₙ Fₙ → ⨁ₙ Fₙ → c.pt` of a cocone `c` over a sequence of modules
`F`: the first map is `telescopeDiff F`, the second is induced by the legs of `c`. It is short
exact when `c` is a colimit cocone (`ModuleCat.shortExact_telescopeShortComplex`). -/
@[expose, simps] noncomputable def telescopeShortComplex (c : Cocone F) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ofHom (telescopeDiff F))
    (ConcreteCategory.ofHom (C := ModuleCat R) (X := of R (⨁ n, F.obj n)) (Y := c.pt)
      (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom)) <| by
    ext : 1
    refine DirectSum.linearMap_ext _ fun n ↦ LinearMap.ext fun x ↦ ?_
    simp

/-- The cocone over `F` with point the cokernel of `telescopeDiff F`, whose legs are the
summand inclusions followed by the quotient map. -/
private noncomputable def telescopeCokernelCocone : Cocone F where
  pt := of R ((⨁ n, F.obj n) ⧸ LinearMap.range (telescopeDiff F))
  ι := NatTrans.ofSequence (fun n ↦ ConcreteCategory.ofHom (C := ModuleCat R) (X := F.obj n)
      (Y := of R ((⨁ n, F.obj n) ⧸ LinearMap.range (telescopeDiff F)))
      ((LinearMap.range (telescopeDiff F)).mkQ ∘ₗ lof R ℕ (fun n ↦ F.obj n) n)) fun n ↦ by
    ext x
    simpa [Submodule.Quotient.eq] using (LinearMap.range (telescopeDiff F)).neg_mem
      (LinearMap.mem_range_self (telescopeDiff F) (lof R ℕ (fun n ↦ F.obj n) n x))

/-- The telescope sequence of a colimit cocone over a sequence of modules is short exact. -/
theorem shortExact_telescopeShortComplex {c : Cocone F} (hc : IsColimit c) :
    (telescopeShortComplex F c).ShortExact := by
  -- The map from the colimit to the cokernel of `telescopeDiff F` restricts to the quotient map,
  -- so every element of `⨁ₙ Fₙ` sent to zero in the colimit lies in the image of the difference.
  have key (a : ⨁ n, F.obj n) : (hc.desc (telescopeCokernelCocone F)).hom
      (toModule R ℕ c.pt (fun n ↦ (c.ι.app n).hom) a) =
        (LinearMap.range (telescopeDiff F)).mkQ a := by
    induction a using DirectSum.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | of n x =>
      rw [← lof_eq_of R, toModule_lof]
      exact congr(Hom.hom $(hc.fac (telescopeCokernelCocone F) n) x)
    | add a b ha hb =>
      -- The two sides carry the module structures of `of R Q` and `Q`, equal by unfolding.
      simp only [map_add, ha, hb]
      rfl
  have hsurj : Function.Surjective (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom) := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit hc]
    refine iSup_le fun n ↦ ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨lof R ℕ (fun n ↦ F.obj n) n x, by simp⟩
  refine { exact := (ShortComplex.moduleCat_exact_iff _).2 fun a ha ↦ ?_
           mono_f := (mono_iff_injective _).2 (telescopeDiff_injective F)
           epi_g := (epi_iff_surjective _).2 hsurj }
  exact LinearMap.mem_range.1 <| (Submodule.Quotient.mk_eq_zero _).1 <|
    (key a).symm.trans ((congrArg _ ha).trans (map_zero _))

/-- The colimit of a sequence of modules of projective dimension `< n` has projective dimension
`< n + 1`. In terms of `HasProjectiveDimensionLE`, a sequential colimit of modules of projective
dimension at most `d` has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLT_succ_of_isColimit [Small.{v} R] {c : Cocone F} (hc : IsColimit c)
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (F.obj i) n) :
    HasProjectiveDimensionLT c.pt (n + 1) := by
  have : AB4OfSize.{0} (ModuleCat.{v} R) := AB4OfSize_shrink.{0, v} _
  have hsum (m : ℕ) (hm : n ≤ m) : HasProjectiveDimensionLT (of R (⨁ i, F.obj i)) m :=
    hasProjectiveDimensionLT_of_isColimit_cofan (coproductCoconeIsColimit fun i ↦ F.obj i) m
      fun i ↦ hasProjectiveDimensionLT_of_ge _ n m hm
  exact (shortExact_telescopeShortComplex F hc).hasProjectiveDimensionLT_X₃ n (hsum n le_rfl)
    (hsum (n + 1) n.le_succ)

end ModuleCat
