/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Pseudodifferential.Symbol
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Symbols on an open set of positions

For an open set `U ⊆ ℝⁿ` of positions, a (local) symbol of order `m` on `U × ℝⁿ` is a map
`a : ℝⁿ × ℝⁿ → (V →L[ℂ] W)` that is smooth on `U × ℝⁿ` and satisfies the Hörmander estimates

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{K,α,β} ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`

on every compact set `K ⊆ U`, where `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. These are the coefficients of
pseudodifferential operators in a chart: a symbol on a chart domain need not extend to a symbol
on all of `ℝⁿ`, and its estimates may degenerate at the boundary of `U`.

The class `TauCeti.LocalSymbol U V W m` fixes the value of the coefficient outside `U × ℝⁿ` to be
zero, which makes it extensional on the coefficient. It is a complex vector space, and it is
related to the class `TauCeti.Symbol n V W m` of symbols on all of `ℝⁿ` as follows:

* `TauCeti.Symbol.restrict U`: a symbol on `ℝⁿ` restricts to a symbol on `U`, and
  `TauCeti.LocalSymbol.restrict` restricts a symbol on `U` to a smaller open set `U' ⊆ U`; the
  restrictions are compatible (`Symbol.restrict_restrict`, `LocalSymbol.restrict_restrict`);
* `TauCeti.LocalSymbol.topEquiv`: symbols on `U = ℝⁿ` are exactly the symbols of `Symbol`, the
  inverse being the restriction to `ℝⁿ` (`Symbol.restrict_top`);
* `TauCeti.LocalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose support is a
  closed subset of `ℝⁿ` contained in `U`, a symbol on `U` extends by zero to a symbol on `ℝⁿ`.
  For a compactly supported cutoff the extension has compact spatial support
  (`LocalSymbol.hasCompactSpatialSupport_extend`), so it satisfies its estimates uniformly in the
  position (`Symbol.HasCompactSpatialSupport.isUniform`). Restricting the extension to an open
  set on which `ψ = 1` recovers the restriction of the original symbol
  (`LocalSymbol.restrict_extend_of_eqOn_one`).

The order inclusions `TauCeti.LocalSymbol.inclusion` commute with restriction and extension.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

/-- The class `S^m_{1,0}(U × ℝⁿ)` of symbols of order `m` on an open set `U` of positions, with
values in `V →L[ℂ] W`: maps `a` that are smooth on `U × ℝⁿ`, vanish for positions outside `U`, and
satisfy on every compact set `K ⊆ U` of positions and for all words `α`, `β` of coordinate indices
the estimate `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for some `C`, all `x ∈ K` and all
frequencies `ξ`, where `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)`.

The vanishing outside `U` is a value convention: no condition relates the values on `U` to the
values outside it. -/
@[ext]
structure LocalSymbol (U : Opens (CoordinateSpace n)) (V W : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a(x, ξ)` of the symbol at the position `x` and the frequency `ξ`, set to
  zero for positions outside `U`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient ((U : Set (CoordinateSpace n)) ×ˢ univ)
  coefficient_eq_zero : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → K ⊆ U → ∀ α β : List (Fin n),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

section Localization

/-! ### Computing mixed derivatives after a cutoff -/

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {a b : CoordinateSpace n × CoordinateSpace n → A} {U : Set (CoordinateSpace n)}
  {x : CoordinateSpace n}

/-- Multiplying a function by a cutoff equal to `1` near the position `x` does not change its
mixed derivatives at `x`. -/
private theorem mixedDeriv_eq_cutoff_smul {ρ : CoordinateSpace n → ℝ}
    (hρ : ∀ᶠ y in 𝓝 x, ρ y = 1) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = mixedDeriv α β (fun p => ρ p.1 • a p) x ξ :=
  mixedDeriv_congr_of_eventually
    (by filter_upwards [hρ] with y hy η using by rw [hy, one_smul]) α β ξ

/-- A function smooth on `U × ℝⁿ`, multiplied by a smooth cutoff whose support is a closed subset
of `ℝⁿ` contained in `U`, is smooth on all of `ℝⁿ × ℝⁿ`. -/
private theorem contDiff_cutoff_smul (ha : ContDiffOn ℝ ∞ a (U ×ˢ univ)) (hU : IsOpen U)
    {ρ : CoordinateSpace n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) :
    ContDiff ℝ ∞ fun p => ρ p.1 • a p := by
  refine ha.contDiff_smul_of_tsupport_subset (hU.prod isOpen_univ)
    (hρ.comp contDiff_fst).contDiffOn ?_
  refine (tsupport_comp_subset_preimage ρ continuous_fst).trans ?_
  rw [← prod_univ]
  exact prod_mono hρU subset_rfl

/-- There is a smooth cutoff, with support in `U`, equal to `1` near every point of a compact
set `K ⊆ U`. -/
private theorem exists_cutoff (hU : IsOpen U) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ ρ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ρ ∧ tsupport ρ ⊆ U ∧
      ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  obtain ⟨ρ, hρ, -, hKρ, -, hρU⟩ := hK.exists_contDiff_cutoff hU hKU
  exact ⟨ρ, hρ, hρU, fun x hx => mem_interior_iff_mem_nhds.1 (hKρ hx)⟩

/-- Mixed derivatives of functions smooth on `U × ℝⁿ` are additive at positions in `U`. -/
private theorem mixedDeriv_add_of_contDiffOn (ha : ContDiffOn ℝ ∞ a (U ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b (U ×ˢ univ)) (hU : IsOpen U) (hx : x ∈ U) (α β : List (Fin n))
    (ξ : CoordinateSpace n) :
    mixedDeriv α β (a + b) x ξ = mixedDeriv α β a x ξ + mixedDeriv α β b x ξ := by
  obtain ⟨ρ, hρ, hρU, hρx⟩ := exists_cutoff hU isCompact_singleton (singleton_subset_iff.2 hx)
  have hρx := hρx x rfl
  have h : (fun p => ρ p.1 • (a + b) p) = (fun p => ρ p.1 • a p) + fun p => ρ p.1 • b p := by
    funext p
    simp [smul_add]
  rw [mixedDeriv_eq_cutoff_smul hρx, mixedDeriv_eq_cutoff_smul (a := a) hρx,
    mixedDeriv_eq_cutoff_smul (a := b) hρx, h,
    mixedDeriv_add (contDiff_cutoff_smul ha hU hρ hρU) (contDiff_cutoff_smul hb hU hρ hρU)]

/-- Mixed derivatives of functions smooth on `U × ℝⁿ` commute with constant scalars at
positions in `U`. -/
private theorem mixedDeriv_const_smul_of_contDiffOn {R : Type*} [Semiring R] [Module R A]
    [SMulCommClass ℝ R A] [ContinuousConstSMul R A] (ha : ContDiffOn ℝ ∞ a (U ×ˢ univ))
    (hU : IsOpen U) (hx : x ∈ U) (c : R) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β (c • a) x ξ = c • mixedDeriv α β a x ξ := by
  obtain ⟨ρ, hρ, hρU, hρx⟩ := exists_cutoff hU isCompact_singleton (singleton_subset_iff.2 hx)
  have hρx := hρx x rfl
  have h : (fun p => ρ p.1 • (c • a) p) = c • fun p => ρ p.1 • a p := by
    funext p
    simp [smul_comm (ρ p.1) c]
  rw [mixedDeriv_eq_cutoff_smul hρx, mixedDeriv_eq_cutoff_smul (a := a) hρx, h,
    mixedDeriv_const_smul (contDiff_cutoff_smul ha hU hρ hρU)]

end Localization

namespace LocalSymbol

variable {U U' U'' : Opens (CoordinateSpace n)} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

theorem coefficient_injective :
    Function.Injective (coefficient : LocalSymbol U V W m → CoordinateSpace n × CoordinateSpace n →
      V →L[ℂ] W) :=
  fun _ _ h => LocalSymbol.ext h

/-- Two symbols on `U` are equal once their coefficients agree at all positions in `U`. -/
theorem ext_of_mem {a b : LocalSymbol U V W m}
    (h : ∀ x ∈ U, ∀ ξ, a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext p
  by_cases hp : p.1 ∈ U
  · exact h p.1 hp p.2
  · rw [a.coefficient_eq_zero p.1 hp p.2, b.coefficient_eq_zero p.1 hp p.2]

section Module

instance : Zero (LocalSymbol U V W m) where
  zero :=
    { coefficient := 0
      contDiffOn_coefficient := contDiffOn_const
      coefficient_eq_zero := fun _ _ _ => rfl
      exists_bound := fun _ _ _ α β => ⟨0, le_rfl, fun x _ ξ => by simp⟩ }

instance : Add (LocalSymbol U V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient.add b.contDiffOn_coefficient
      coefficient_eq_zero := fun x hx ξ => by
        simp [a.coefficient_eq_zero x hx ξ, b.coefficient_eq_zero x hx ξ]
      exists_bound := fun K hK hKU α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK hKU α β
        obtain ⟨D, hD, hb⟩ := b.exists_bound K hK hKU α β
        refine ⟨C + D, add_nonneg hC hD, fun x hx ξ => ?_⟩
        rw [mixedDeriv_add_of_contDiffOn a.contDiffOn_coefficient b.contDiffOn_coefficient
          U.isOpen (hKU hx), add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha x hx ξ) (hb x hx ξ)) }

instance : SMul ℂ (LocalSymbol U V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul c
      coefficient_eq_zero := fun x hx ξ => by simp [a.coefficient_eq_zero x hx ξ]
      exists_bound := fun K hK hKU α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK hKU α β
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x hx ξ => ?_⟩
        rw [mixedDeriv_const_smul_of_contDiffOn a.contDiffOn_coefficient U.isOpen (hKU hx),
          norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha x hx ξ) (norm_nonneg c) }

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
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (congrArg (a.coefficient + ·) (coefficient_neg b)).trans (sub_eq_add_neg _ _).symm

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

/-- The restriction of a symbol on `U` to a smaller open set `U' ⊆ U`: the coefficient is kept on
`U' × ℝⁿ` and set to zero elsewhere. -/
def restrict (h : U' ≤ U) : LocalSymbol U V W m →ₗ[ℂ] LocalSymbol U' V W m where
  toFun a :=
    { coefficient := ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient
      contDiffOn_coefficient := (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr
        fun p hp => indicator_of_mem hp _
      coefficient_eq_zero := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      exists_bound := fun K hK hKU' α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK (hKU'.trans h) α β
        refine ⟨C, hC, fun x hx ξ => ?_⟩
        rw [mixedDeriv_congr_of_eventually (b := a.coefficient) ?_]
        · exact ha x hx ξ
        filter_upwards [U'.isOpen.mem_nhds (hKU' hx)] with y hy η
        exact indicator_of_mem (by simpa using hy) _ }
  map_add' a b := by
    ext1
    exact indicator_add _ _ _
  map_smul' c a := by
    ext1
    exact indicator_const_smul _ c a.coefficient

@[simp]
theorem coefficient_restrict_of_mem (h : U' ≤ U) (a : LocalSymbol U V W m) {x : CoordinateSpace n}
    (hx : x ∈ U') (ξ : CoordinateSpace n) :
    (restrict h a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  indicator_of_mem (by simpa using hx) _

@[simp]
theorem coefficient_restrict_of_notMem (h : U' ≤ U) (a : LocalSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∉ U') (ξ : CoordinateSpace n) :
    (restrict h a).coefficient (x, ξ) = 0 :=
  (restrict h a).coefficient_eq_zero x hx ξ

@[simp]
theorem restrict_self (a : LocalSymbol U V W m) : restrict le_rfl a = a :=
  ext_of_mem fun _ hx ξ => coefficient_restrict_of_mem le_rfl a hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext_of_mem fun x hx ξ => by simp [hx, h' hx]

end Restrict

section Inclusion

/-- A symbol of order `m` on `U` is a symbol of every order `m' ≥ m` on `U`, since `⟨ξ⟩ ≥ 1`. -/
def inclusion (h : m ≤ m') : LocalSymbol U V W m →ₗ[ℂ] LocalSymbol U V W m' where
  toFun a :=
    { coefficient := a.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient
      coefficient_eq_zero := a.coefficient_eq_zero
      exists_bound := fun K hK hKU α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK hKU α β
        refine ⟨C, hC, fun x hx ξ => (ha x hx ξ).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
        exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith) }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : LocalSymbol U V W m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

theorem inclusion_injective (h : m ≤ m') :
    Function.Injective (inclusion (U := U) (V := V) (W := W) h) :=
  fun _ _ hab => LocalSymbol.ext (by simpa using congrArg LocalSymbol.coefficient hab)

theorem restrict_inclusion (h : m ≤ m') (hU : U' ≤ U) (a : LocalSymbol U V W m) :
    restrict hU (inclusion h a) = inclusion h (restrict hU a) :=
  ext_of_mem fun x hx ξ => by simp [hx]

end Inclusion

section Top

/-- Symbols on the whole space `U = ℝⁿ` of positions are the symbols on `ℝⁿ`. -/
def topEquiv : LocalSymbol (⊤ : Opens (CoordinateSpace n)) V W m ≃ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := a.coefficient
      contDiff_coefficient := by
        rw [← contDiffOn_univ, ← univ_prod_univ]
        exact a.contDiffOn_coefficient
      exists_bound := fun K hK α β => a.exists_bound K hK (subset_univ K) α β }
  invFun a :=
    { coefficient := a.coefficient
      contDiffOn_coefficient := a.contDiff_coefficient.contDiffOn
      coefficient_eq_zero := fun x hx => absurd (Opens.mem_top x) hx
      exists_bound := fun K hK _ α β => a.exists_bound K hK α β }
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_topEquiv (a : LocalSymbol (⊤ : Opens (CoordinateSpace n)) V W m) :
    (topEquiv a).coefficient = a.coefficient := (rfl)

@[simp]
theorem coefficient_topEquiv_symm (a : Symbol n V W m) :
    (topEquiv.symm a : LocalSymbol (⊤ : Opens (CoordinateSpace n)) V W m).coefficient =
      a.coefficient := (rfl)

end Top

end LocalSymbol

namespace Symbol

variable {U U' : Opens (CoordinateSpace n)} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

/-- The restriction of a symbol on `ℝⁿ` to the open set `U` of positions: the coefficient is kept
on `U × ℝⁿ` and set to zero elsewhere. -/
def restrict (U : Opens (CoordinateSpace n)) : Symbol n V W m →ₗ[ℂ] LocalSymbol U V W m :=
  LocalSymbol.restrict le_top ∘ₗ LocalSymbol.topEquiv.symm.toLinearMap

@[simp]
theorem coefficient_restrict_of_mem (a : Symbol n V W m) {x : CoordinateSpace n} (hx : x ∈ U)
    (ξ : CoordinateSpace n) : (restrict U a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  LocalSymbol.coefficient_restrict_of_mem le_top _ hx ξ

@[simp]
theorem coefficient_restrict_of_notMem (a : Symbol n V W m) {x : CoordinateSpace n} (hx : x ∉ U)
    (ξ : CoordinateSpace n) : (restrict U a).coefficient (x, ξ) = 0 :=
  (restrict U a).coefficient_eq_zero x hx ξ

/-- Restricting to the whole space of positions is the inverse of `LocalSymbol.topEquiv`. -/
theorem restrict_top (a : Symbol n V W m) : restrict ⊤ a = LocalSymbol.topEquiv.symm a :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : Symbol n V W m) :
    LocalSymbol.restrict h (restrict U a) = restrict U' a :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx, h hx]

theorem restrict_inclusion (h : m ≤ m') (a : Symbol n V W m) :
    restrict U (inclusion h a) = LocalSymbol.inclusion h (restrict U a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

end Symbol

namespace LocalSymbol

variable {U U' : Opens (CoordinateSpace n)} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

section Extend

variable {ψ : CoordinateSpace n → ℝ}

/-- The cut-off coefficient `ψ(x) a(x, ξ)` satisfies the symbol estimates on every compact set of
positions. -/
private theorem exists_bound_extend (a : LocalSymbol U V W m) (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (fun p => ψ p.1 • a.coefficient p) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- Near the compact set `L = K ∩ tsupport ψ ⊆ U`, replace `a` by the smooth function `b = ρ • a`.
  set L := K ∩ tsupport ψ
  have hL : IsCompact L := hK.inter_right (isClosed_tsupport ψ)
  have hLU : L ⊆ U := inter_subset_right.trans hψU
  obtain ⟨ρ, hρ, hρU, hρL⟩ := exists_cutoff U.isOpen hL hLU
  set b : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W := fun p => ρ p.1 • a.coefficient p
  have hb : ContDiff ℝ ∞ b := contDiff_cutoff_smul a.contDiffOn_coefficient U.isOpen hρ hρU
  have hab : ∀ x ∈ L, ∀ᶠ y in 𝓝 x, ∀ η, b (y, η) = a.coefficient (y, η) := fun x hx => by
    filter_upwards [hρL x hx] with y hy η
    simp [b, hy]
  -- Bounds for the derivatives of `ψ` and the mixed derivatives of `a` on `L`.
  choose B hB using fun i : ℕ => hL.exists_bound_of_continuousOn
    (hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) (m := i)).continuousOn
  choose C hC0 hC using fun γ : List (Fin n) => a.exists_bound L hL hLU γ β
  refine ⟨∑ i ∈ Finset.range (α.length + 1), (α.length.choose i : ℝ) * max (B i) 0 *
      ∑ w : Fin (α.length - i) → Fin n, C (List.ofFn w), Finset.sum_nonneg fun i _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => hC0 _), fun x hx ξ => ?_⟩
  by_cases hxψ : x ∈ tsupport ψ
  · have hxL : x ∈ L := ⟨hx, hxψ⟩
    have hψb : mixedDeriv α β (fun p => ψ p.1 • a.coefficient p) x ξ =
        coordinateDeriv α (fun y => ψ y • coordinateDeriv β (fun η => b (y, η)) ξ) x := by
      rw [mixedDeriv_congr_of_eventually (b := fun p => ψ p.1 • b p)
        (by filter_upwards [hab x hxL] with y hy η using by rw [hy]), mixedDeriv_def]
      congr 1
      funext y
      exact congrFun (coordinateDeriv_const_smul β
        (contDiff_infty.1 (hb.comp (contDiff_prodMk_right y)) _) (ψ y)) ξ
    rw [hψb]
    refine (norm_coordinateDeriv_smul_le hψ (contDiff_coordinateDeriv_slice hb β ξ) α x).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hψi : ‖iteratedFDeriv ℝ i ψ x‖ ≤ max (B i) 0 := (hB i x hxL).trans (le_max_left _ _)
    have hbi : ∑ w : Fin (α.length - i) → Fin n,
        ‖coordinateDeriv (List.ofFn w) (fun y => coordinateDeriv β (fun η => b (y, η)) ξ) x‖ ≤
          ∑ w : Fin (α.length - i) → Fin n,
            C (List.ofFn w) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
      Finset.sum_le_sum fun w _ => by
        rw [← mixedDeriv_def, mixedDeriv_congr_of_eventually (hab x hxL)]
        exact hC _ x hxL ξ
    calc _ ≤ (α.length.choose i : ℝ) * max (B i) 0 * ∑ w : Fin (α.length - i) → Fin n,
          C (List.ofFn w) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by gcongr
      _ = _ := by simp only [Finset.sum_mul, mul_assoc]
  · rw [mixedDeriv_eq_zero_of_eventually ?_ α β ξ, norm_zero]
    · exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun w _ => hC0 _)) (Real.rpow_pos_of_pos (by positivity) _).le
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxψ] with y hy η
    simp [hy]

/-- The extension by zero of the cut-off symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose
support is a closed subset of `ℝⁿ` contained in `U`: a symbol on `ℝⁿ`. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalSymbol U V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      contDiff_coefficient := contDiff_cutoff_smul a.contDiffOn_coefficient U.isOpen hψ hψU
      exists_bound := fun _ hK α β => a.exists_bound_extend hψ hψU hK α β }
  map_add' a b := by
    ext1
    funext p
    simp [smul_add]
  map_smul' c a := by
    ext1
    funext p
    simp [smul_comm (ψ p.1) c]

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem coefficient_extend (a : LocalSymbol U V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p := (rfl)

/-- The cut-off extension of the restriction of a symbol on `ℝⁿ` is its product with the
cutoff. -/
theorem coefficient_extend_restrict (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU (Symbol.restrict U a)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

theorem inclusion_extend (h : m ≤ m') (a : LocalSymbol U V W m) :
    Symbol.inclusion h (extend ψ hψ hψU a) = extend ψ hψ hψU (inclusion h a) :=
  Symbol.ext (funext fun p => by simp)

/-- For a compactly supported cutoff, the extension has compact spatial support. In particular it
satisfies the symbol estimates uniformly in the position
(`Symbol.HasCompactSpatialSupport.isUniform`). -/
theorem hasCompactSpatialSupport_extend (hψc : HasCompactSupport ψ) (a : LocalSymbol U V W m) :
    (extend ψ hψ hψU a).HasCompactSpatialSupport :=
  Symbol.hasCompactSpatialSupport_iff.2
    ⟨tsupport ψ, hψc, fun x hx ξ => by simp [image_eq_zero_of_notMem_tsupport hx]⟩

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalSymbol U V W m) : Symbol.restrict U' (extend ψ hψ hψU a) = restrict h a :=
  ext_of_mem fun x hx ξ => by simp [hx, show ψ x = 1 from hψ1 hx]

end Extend

end LocalSymbol

end TauCeti
