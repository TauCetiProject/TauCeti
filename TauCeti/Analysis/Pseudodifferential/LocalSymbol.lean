/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Symbols on an open set of positions

For an open set `U ⊆ ℝⁿ`, a symbol of order `m` on `U × ℝⁿ` is a map `a(x, ξ)`, smooth on
`U × ℝⁿ`, such that on every compact set `K ⊆ U` of positions every mixed derivative satisfies

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{K,α,β} ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`.

These are the symbols that arise in a chart of a manifold, whose domain is an open subset of `ℝⁿ`.
We define their class `TauCeti.LocalSymbol U V W m` and show that it is a complex vector space. As
for homogeneous symbols at `ξ = 0`, values outside the domain are fixed by a convention: the
coefficient is `0` at every position outside `U`. So a local symbol is determined by its values on
`U × ℝⁿ` (`TauCeti.LocalSymbol.ext_of_mem`), and its mixed derivatives at positions of `U` are the
usual ones, since they only depend on the values nearby (`TauCeti.mixedDeriv_congr_of_eventually`).

The local classes are compared with the class `TauCeti.Symbol n V W m` of symbols on `ℝⁿ × ℝⁿ`:

* `TauCeti.Symbol.restrict`: a symbol on `ℝⁿ × ℝⁿ` restricts to a symbol on `U × ℝⁿ` with the same
  estimates on the compact subsets of `U`;
* `TauCeti.LocalSymbol.restrict`: a symbol on `U × ℝⁿ` restricts to every smaller open set, and
  restrictions compose (`TauCeti.LocalSymbol.restrict_restrict`,
  `TauCeti.Symbol.restrict_restrict`);
* `TauCeti.Symbol.restrictTopEquiv`: for `U = ℝⁿ` restriction is a linear equivalence
  (`TauCeti.Symbol.restrict_top`), so the local class over all of `ℝⁿ` is exactly
  `TauCeti.Symbol`.

A smooth coefficient on `U × ℝⁿ` need not extend smoothly to `ℝⁿ × ℝⁿ` (for instance `1 / x₁` on
the half-space `x₁ > 0`), so for `U ≠ ℝⁿ` a local symbol is in general not the restriction of a
global one.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set

namespace TauCeti

variable {n : ℕ}

/-- The class `S^m_{1,0}` of symbols of order `m` on `U × ℝⁿ`, for an open set `U ⊆ ℝⁿ` of
positions, with values in `V →L[ℂ] W`: maps `a`, smooth on `U × ℝⁿ`, such that on every compact
set `K ⊆ U` of positions and for all words `α`, `β` of coordinate indices,
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for some `C`, all `x ∈ K` and all frequencies `ξ`. By
convention the coefficient vanishes at positions outside `U`. -/
@[ext]
structure LocalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a(x, ξ)` of the symbol at the position `x` and the frequency `ξ`, set to
  `0` at positions outside `U`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient ((U : Set (CoordinateSpace n)) ×ˢ univ)
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  exists_bound : ∀ K : Set (CoordinateSpace n), K ⊆ U → IsCompact K → ∀ α β : List (Fin n),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

namespace LocalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : LocalSymbol U V W m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => LocalSymbol.ext h

/-- A local symbol is determined by its values at the positions of its domain. -/
theorem ext_of_mem {a b : LocalSymbol U V W m}
    (h : ∀ x ∈ U, ∀ ξ, a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext ⟨x, ξ⟩
  by_cases hx : x ∈ U
  · exact h x hx ξ
  · rw [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]

/-- At a position `x ∈ U`, the coefficient of a local symbol agrees nearby with a smooth function on
all of `ℝⁿ × ℝⁿ`. -/
private theorem exists_contDiff_eventually_eq_coefficient (a : LocalSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∈ U) :
    ∃ g : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W, ContDiff ℝ ∞ g ∧
      ∀ᶠ y in 𝓝 x, ∀ η, g (y, η) = a.coefficient (y, η) :=
  let ⟨g, hg, hga⟩ := a.contDiffOn_coefficient.exists_contDiff_eventually_eq_prod_univ
    isCompact_singleton U.isOpen (singleton_subset_iff.2 hx)
  ⟨g, hg, hga x rfl⟩

section Module

instance : Zero (LocalSymbol U V W m) where
  zero :=
    { coefficient := 0
      contDiffOn_coefficient := contDiffOn_const
      coefficient_of_notMem := fun _ _ _ => rfl
      exists_bound := fun _ _ _ α β => ⟨0, le_rfl, fun x _ ξ => by simp [mixedDeriv_zero]⟩ }

instance : Add (LocalSymbol U V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient.add b.contDiffOn_coefficient
      coefficient_of_notMem := fun x hx ξ => by
        simp [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]
      exists_bound := fun K hKU hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hKU hK α β
        obtain ⟨D, hD, hb⟩ := b.exists_bound K hKU hK α β
        refine ⟨C + D, add_nonneg hC hD, fun x hx ξ => ?_⟩
        obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventually_eq_coefficient (hKU hx)
        obtain ⟨g, hg, hgb⟩ := b.exists_contDiff_eventually_eq_coefficient (hKU hx)
        have hfg : ∀ᶠ y in 𝓝 x, ∀ η, (a.coefficient + b.coefficient) (y, η) = (f + g) (y, η) := by
          filter_upwards [hfa, hgb] with y hya hyb η
          rw [Pi.add_apply, Pi.add_apply, hya, hyb]
        rw [mixedDeriv_congr_of_eventually hfg]
        refine norm_mixedDeriv_add_le hf hg ?_ ?_
        · rw [mixedDeriv_congr_of_eventually hfa]
          exact ha x hx ξ
        · rw [mixedDeriv_congr_of_eventually hgb]
          exact hb x hx ξ }

instance : SMul ℂ (LocalSymbol U V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul c
      coefficient_of_notMem := fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ]
      exists_bound := fun K hKU hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hKU hK α β
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x hx ξ => ?_⟩
        obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventually_eq_coefficient (hKU hx)
        have hcf : ∀ᶠ y in 𝓝 x, ∀ η, (c • a.coefficient) (y, η) = (c • f) (y, η) := by
          filter_upwards [hfa] with y hy η
          rw [Pi.smul_apply, Pi.smul_apply, hy]
        rw [mixedDeriv_congr_of_eventually hcf]
        refine norm_mixedDeriv_smul_le hf c ?_
        rw [mixedDeriv_congr_of_eventually hfa]
        exact ha x hx ξ }

instance : Neg (LocalSymbol U V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (LocalSymbol U V W m) where
  sub a b := a + -b

instance : SMul ℕ (LocalSymbol U V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (LocalSymbol U V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : LocalSymbol U V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : LocalSymbol U V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : LocalSymbol U V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : LocalSymbol U V W m) : (-a).coefficient = -a.coefficient :=
  neg_one_smul ℂ a.coefficient

@[simp]
theorem coefficient_sub (a b : LocalSymbol U V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient := by
  rw [sub_eq_add_neg a.coefficient]
  exact congrArg (a.coefficient + ·) (coefficient_neg b)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : LocalSymbol U V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : LocalSymbol U V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (LocalSymbol U V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (LocalSymbol U V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

end Module

section Restrict

/-- The restriction of a local symbol on `U` to a smaller open set `U'`, extended by zero at
positions outside `U'`. It satisfies the same estimates on the compact subsets of `U'`. -/
def restrict (h : U' ≤ U) : LocalSymbol U V W m →ₗ[ℂ] LocalSymbol U' V W m where
  toFun a :=
    { coefficient := ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient
      contDiffOn_coefficient := (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr
        fun _ hp => indicator_of_mem hp _
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      exists_bound := fun K hKU' hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K (hKU'.trans h) hK α β
        refine ⟨C, hC, fun x hx ξ => ?_⟩
        rw [mixedDeriv_indicator_prod_univ_of_mem U'.isOpen (hKU' hx)]
        exact ha x hx ξ }
  map_add' a b := by
    ext1
    exact indicator_add' _ _ _
  map_smul' c a := by
    ext1
    exact indicator_const_smul _ c _

theorem coefficient_restrict (h : U' ≤ U) (a : LocalSymbol U V W m) :
    (restrict h a).coefficient = ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrict_of_mem (h : U' ≤ U) (a : LocalSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∈ U') (ξ : CoordinateSpace n) :
    (restrict h a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  indicator_of_mem (mk_mem_prod hx (mem_univ ξ)) _

@[simp]
theorem restrict_self (a : LocalSymbol U V W m) : restrict le_rfl a = a :=
  ext_of_mem fun _ hx ξ => coefficient_restrict_of_mem le_rfl a hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext_of_mem fun x hx ξ => by
    rw [coefficient_restrict_of_mem _ _ hx, coefficient_restrict_of_mem _ _ (h' hx),
      coefficient_restrict_of_mem _ _ hx]

end Restrict

end LocalSymbol

namespace Symbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `ℝⁿ`, the local symbols are exactly the symbols on `ℝⁿ × ℝⁿ`: a symbol on
`ℝⁿ × ℝⁿ` is a local symbol on `⊤` with the same coefficient, and this is a linear equivalence. -/
def restrictTopEquiv :
    Symbol n V W m ≃ₗ[ℂ] LocalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { coefficient := a.coefficient
      contDiffOn_coefficient := a.contDiff_coefficient.contDiffOn
      coefficient_of_notMem := fun x hx => absurd (TopologicalSpace.Opens.mem_top x) hx
      exists_bound := fun K _ hK α β => a.exists_bound K hK α β }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a :=
    { coefficient := a.coefficient
      contDiff_coefficient := contDiffOn_univ.1 <| by
        simpa using a.contDiffOn_coefficient
      exists_bound := fun K hK α β => a.exists_bound K (by simp) hK α β }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coefficient_restrictTopEquiv_apply (a : Symbol n V W m) :
    (restrictTopEquiv a).coefficient = a.coefficient := (rfl)

@[simp]
theorem coefficient_restrictTopEquiv_symm_apply
    (a : LocalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a : Symbol n V W m).coefficient = a.coefficient := (rfl)

/-- The restriction of a symbol on `ℝⁿ × ℝⁿ` to the open set `U` of positions, extended by zero
at positions outside `U`: the restriction from `⊤` to `U` of the corresponding local symbol. It
satisfies the same estimates on the compact subsets of `U`. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    Symbol n V W m →ₗ[ℂ] LocalSymbol U V W m :=
  LocalSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

theorem coefficient_restrict (a : Symbol n V W m) :
    (a.restrict U).coefficient = ((U : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrict_of_mem (a : Symbol n V W m) {x : CoordinateSpace n} (hx : x ∈ U)
    (ξ : CoordinateSpace n) : (a.restrict U).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  LocalSymbol.coefficient_restrict_of_mem le_top (restrictTopEquiv a) hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : Symbol n V W m) :
    LocalSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalSymbol.restrict_restrict le_top h (restrictTopEquiv a)

/-- Restricting a symbol to all of `ℝⁿ` gives the corresponding local symbol on `⊤`. -/
@[simp]
theorem restrict_top (a : Symbol n V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  LocalSymbol.restrict_self (restrictTopEquiv a)

end Symbol

end TauCeti
