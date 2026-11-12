/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Classical symbols on an open set of positions

For an open set `U ⊆ ℝⁿ`, a *classical symbol of order `m` on `U × ℝⁿ`* is a local symbol
`a ∈ S^m_{1,0}(U × ℝⁿ)` (`TauCeti.LocalSymbol`) with an asymptotic expansion
`a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into homogeneous terms on `U`: each `a_{m-j}` is smooth on
`U × (ℝⁿ \ {0})` and positively homogeneous of degree `m - j` in `ξ`, and for every `N` the
remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a local symbol of order `m - N`. These are the symbols of
classical pseudodifferential operators in a chart of a manifold, whose domain is an open subset of
`ℝⁿ`, and the global class `TauCeti.ClassicalSymbol` is the case `U = ℝⁿ`.

As for local symbols, values outside the domain are a convention: the coefficients vanish at
positions outside `U`, and the homogeneous terms also vanish at `ξ = 0`.

The file develops:

* `TauCeti.LocalHomogeneousSymbol U V W m`: homogeneous symbols of degree `m` on `U`, with their
  vector space structure; the restriction `TauCeti.HomogeneousSymbol.restrict` of a homogeneous
  symbol on `ℝⁿ` and `TauCeti.LocalHomogeneousSymbol.restrict` to smaller open sets; the extension
  `TauCeti.LocalHomogeneousSymbol.extend` of the product with a smooth cutoff `ψ(x)` supported in
  `U` to a homogeneous symbol on `ℝⁿ`; and the cut-off term
  `TauCeti.LocalHomogeneousSymbol.cutoffSymbol χ a`, the local symbol `χ(ξ) a(x, ξ)` of order `m`;
* `TauCeti.LocalClassicalSymbol U V W m`, with an actual remainder symbol
  `TauCeti.LocalClassicalSymbol.remainder χ N` of order `m - N` for every frequency cutoff `χ`
  (`TauCeti.LocalClassicalSymbol.exists_remainder`);
* `TauCeti.LocalClassicalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `ℝⁿ` contained in `U`, a classical symbol on `U` extends by zero to
  a classical symbol on `ℝⁿ`, termwise;
* `TauCeti.LocalClassicalSymbol.term_eq_of_toLocalSymbol_eq` and
  `TauCeti.LocalClassicalSymbol.ext`: the homogeneous terms are determined by the local symbol;
* `TauCeti.ClassicalSymbol.restrict`: a classical symbol on `ℝⁿ` restricts to a classical symbol
  on `U`, with the restricted homogeneous terms; `TauCeti.LocalClassicalSymbol.restrict` restricts
  further to smaller open sets, and restrictions compose;
* `TauCeti.ClassicalSymbol.restrictTopEquiv`: over `U = ℝⁿ` restriction is a linear equivalence,
  so the local classical symbols on all of `ℝⁿ` are exactly the classical symbols;
* `TauCeti.LocalClassicalSymbol.principal`, the principal symbol, which commutes with restriction
  and extension.

A local classical symbol need not be the restriction of a classical symbol on `ℝⁿ`, since its
coefficient need not extend smoothly across the boundary of `U`; restricting the extension
`TauCeti.LocalClassicalSymbol.extend` to an open set on which the cutoff equals `1` recovers the
restriction of the original symbol (`TauCeti.LocalClassicalSymbol.restrict_extend_of_eqOn_one`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definitions 18.1.1
  and 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15) and (1.17).
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

/-- A homogeneous symbol of real degree `m` on an open set `U ⊆ ℝⁿ` of positions: a map
`a(x, ξ)` with values in `V →L[ℂ] W`, smooth on `U × (ℝⁿ \ {0})` and positively homogeneous of
degree `m` in the frequency. By convention the coefficient vanishes at positions outside `U` and
at the zero frequency. -/
@[ext]
structure LocalHomogeneousSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The value at a position and a frequency, set to `0` at positions outside `U`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  zero_covector : ∀ x, coefficient (x, 0) = 0
  contDiffOn_coefficient :
    ContDiffOn ℝ ∞ coefficient ((U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0})
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] LocalHomogeneousSymbol.zero_covector

namespace LocalHomogeneousSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : LocalHomogeneousSymbol U V W m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => LocalHomogeneousSymbol.ext h

/-- A homogeneous symbol on `U` is determined by its values at the positions of `U`. -/
theorem ext_of_mem {a b : LocalHomogeneousSymbol U V W m}
    (h : ∀ x ∈ U, ∀ ξ, a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext ⟨x, ξ⟩
  by_cases hx : x ∈ U
  · exact h x hx ξ
  · rw [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]

section Module

instance : Zero (LocalHomogeneousSymbol U V W m) where
  zero :=
    { coefficient := 0
      coefficient_of_notMem := fun _ _ _ => rfl
      zero_covector := fun _ => rfl
      contDiffOn_coefficient := contDiffOn_const
      homogeneous := fun _ _ _ _ => by simp }

instance : Add (LocalHomogeneousSymbol U V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      coefficient_of_notMem := fun x hx ξ => by
        simp [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]
      zero_covector := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.add b.contDiffOn_coefficient
      homogeneous := fun x ξ t ht => by
        simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht, smul_add] }

instance : SMul ℂ (LocalHomogeneousSymbol U V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      coefficient_of_notMem := fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ]
      zero_covector := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul c
      homogeneous := fun x ξ t ht => by simp [a.homogeneous x ξ t ht, smul_comm c] }

instance : Neg (LocalHomogeneousSymbol U V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (LocalHomogeneousSymbol U V W m) where
  sub a b := a + -b

instance : SMul ℕ (LocalHomogeneousSymbol U V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (LocalHomogeneousSymbol U V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : LocalHomogeneousSymbol U V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : LocalHomogeneousSymbol U V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : LocalHomogeneousSymbol U V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : LocalHomogeneousSymbol U V W m) :
    (-a).coefficient = -a.coefficient :=
  neg_one_smul ℂ a.coefficient

@[simp]
theorem coefficient_sub (a b : LocalHomogeneousSymbol U V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient := by
  rw [sub_eq_add_neg a.coefficient]
  exact congrArg (a.coefficient + ·) (coefficient_neg b)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : LocalHomogeneousSymbol U V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : LocalHomogeneousSymbol U V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (LocalHomogeneousSymbol U V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (LocalHomogeneousSymbol U V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

@[simp]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → LocalHomogeneousSymbol U V W m) :
    (∑ i ∈ s, f i).coefficient = ∑ i ∈ s, (f i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) f s

end Module

/-- Transport of a homogeneous symbol along an equality of degrees. -/
def castDegree (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    LocalHomogeneousSymbol U V W m' where
  coefficient := a.coefficient
  coefficient_of_notMem := a.coefficient_of_notMem
  zero_covector := a.zero_covector
  contDiffOn_coefficient := a.contDiffOn_coefficient
  homogeneous := h ▸ a.homogeneous

@[simp]
theorem coefficient_castDegree (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    (a.castDegree h).coefficient = a.coefficient := (rfl)

section Restrict

/-- The restriction of a homogeneous symbol on `U` to a smaller open set `U'`, extended by zero at
positions outside `U'`. -/
def restrict (h : U' ≤ U) :
    LocalHomogeneousSymbol U V W m →ₗ[ℂ] LocalHomogeneousSymbol U' V W m where
  toFun a :=
    { coefficient := ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      zero_covector := fun x => by by_cases hx : x ∈ U' <;> simp [hx]
      contDiffOn_coefficient := (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr
        fun p hp => indicator_of_mem (mk_mem_prod hp.1 (mem_univ p.2)) _
      homogeneous := fun x ξ t ht => by
        by_cases hx : x ∈ U' <;> simp [hx, a.homogeneous x ξ t ht] }
  map_add' a b := by
    ext1
    exact indicator_add' _ _ _
  map_smul' c a := by
    ext1
    exact indicator_const_smul _ c _

@[simp]
theorem coefficient_restrict_of_mem (h : U' ≤ U) (a : LocalHomogeneousSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∈ U') (ξ : CoordinateSpace n) :
    (restrict h a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  indicator_of_mem (mk_mem_prod hx (mem_univ ξ)) _

@[simp]
theorem coefficient_restrict_of_notMem (h : U' ≤ U) (a : LocalHomogeneousSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∉ U') (ξ : CoordinateSpace n) :
    (restrict h a).coefficient (x, ξ) = 0 :=
  (restrict h a).coefficient_of_notMem x hx ξ

@[simp]
theorem restrict_self (a : LocalHomogeneousSymbol U V W m) : restrict le_rfl a = a :=
  ext_of_mem fun _ hx ξ => coefficient_restrict_of_mem le_rfl a hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalHomogeneousSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext_of_mem fun x hx ξ => by
    rw [coefficient_restrict_of_mem _ _ hx, coefficient_restrict_of_mem _ _ (h' hx),
      coefficient_restrict_of_mem _ _ hx]

end Restrict

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `ℝⁿ`, the local homogeneous symbols are exactly the homogeneous symbols on
`ℝⁿ × ℝⁿ`: a homogeneous symbol is a local one on `⊤` with the same coefficient, and this is a
linear equivalence. -/
def restrictTopEquiv : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m ≃ₗ[ℂ]
    LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { coefficient := a.coefficient
      coefficient_of_notMem := fun x hx => absurd (TopologicalSpace.Opens.mem_top x) hx
      zero_covector := a.zero_covector
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp => hp.2
      homogeneous := a.homogeneous }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a :=
    { coefficient := a.coefficient
      zero_covector := a.zero_covector
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp =>
        ⟨TopologicalSpace.Opens.mem_top _, hp⟩
      homogeneous := a.homogeneous }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coefficient_restrictTopEquiv_apply
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (restrictTopEquiv a).coefficient = a.coefficient := (rfl)

@[simp]
theorem coefficient_restrictTopEquiv_symm_apply
    (a : LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a :
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m).coefficient =
        a.coefficient := (rfl)

/-- The restriction of a homogeneous symbol on `ℝⁿ × ℝⁿ` to the open set `U` of positions,
extended by zero at positions outside `U`. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ]
      LocalHomogeneousSymbol U V W m :=
  LocalHomogeneousSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

@[simp]
theorem coefficient_restrict_of_mem
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∈ U) (ξ : CoordinateSpace n) :
    (a.restrict U).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  LocalHomogeneousSymbol.coefficient_restrict_of_mem le_top (restrictTopEquiv a) hx ξ

@[simp]
theorem coefficient_restrict_of_notMem
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∉ U) (ξ : CoordinateSpace n) :
    (a.restrict U).coefficient (x, ξ) = 0 :=
  (a.restrict U).coefficient_of_notMem x hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    LocalHomogeneousSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalHomogeneousSymbol.restrict_restrict le_top h (restrictTopEquiv a)

/-- Restricting a homogeneous symbol to all of `ℝⁿ` gives the corresponding local homogeneous
symbol on `⊤`. -/
@[simp]
theorem restrict_top (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    a.restrict ⊤ = restrictTopEquiv a :=
  LocalHomogeneousSymbol.restrict_self (restrictTopEquiv a)

end HomogeneousSymbol

namespace LocalHomogeneousSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

section Extend

variable {ψ : CoordinateSpace n → ℝ}

/-- The cut-off coefficient `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose support is a closed
subset of `ℝⁿ` contained in `U`, is smooth at every point of `ℝⁿ × (ℝⁿ \ {0})`. -/
private theorem contDiffAt_cutoff_smul (a : LocalHomogeneousSymbol U V W m)
    (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) {p : CoordinateSpace n × CoordinateSpace n}
    (hp : p.2 ≠ 0) : ContDiffAt ℝ ∞ (fun q => ψ q.1 • a.coefficient q) p := by
  by_cases hx : p.1 ∈ U
  · have hmem : (U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0} ∈ 𝓝 p :=
      (U.isOpen.prod isOpen_compl_singleton).mem_nhds ⟨hx, hp⟩
    exact (hψ.comp contDiff_fst).contDiffAt.smul (a.contDiffOn_coefficient.contDiffAt hmem)
  · have h0 : (fun q => ψ q.1 • a.coefficient q) =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto p).eventually
        (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hψU h))] with q hq
      simp [hq]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- The extension by zero of the cut-off homogeneous symbol `ψ(x) a(x, ξ)`, for a smooth cutoff
`ψ` whose support is a closed subset of `ℝⁿ` contained in `U`: a homogeneous symbol on `ℝⁿ` of the
same degree. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalHomogeneousSymbol U V W m →ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      zero_covector := fun x => by simp
      contDiffOn_coefficient := fun _ hp => (a.contDiffAt_cutoff_smul hψ hψU hp).contDiffWithinAt
      homogeneous := fun x ξ t ht => by simp only [a.homogeneous x ξ t ht, smul_comm (ψ x)] }
  map_add' a b := HomogeneousSymbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := HomogeneousSymbol.ext <| funext fun p => by simp [smul_comm (ψ p.1) c]

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem coefficient_extend (a : LocalHomogeneousSymbol U V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p := (rfl)

/-- The cut-off extension of the restriction of a homogeneous symbol on `ℝⁿ` is its product with
the cutoff. -/
theorem coefficient_extend_restrict
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU (a.restrict U)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original homogeneous symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalHomogeneousSymbol U V W m) : (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext_of_mem fun x hx ξ => by simp [hx, (hψ1 hx).trans (Pi.one_apply x)]

end Extend

section CutoffSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m` on `U`, as a local
symbol of order `m` on `U`. -/
def cutoffSymbol : LocalHomogeneousSymbol U V W m →ₗ[ℂ] LocalSymbol U V W m where
  toFun a := LocalSymbol.ofCutoff (fun p => χ p.2 • a.coefficient p)
    (fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ])
    fun ψ hψ _ hψU => ⟨HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a), funext fun p => by
      simp only [HomogeneousSymbol.coefficient_cutoffSymbol, coefficient_extend]
      exact smul_comm _ _ _⟩
  map_add' a b := LocalSymbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := LocalSymbol.ext <| funext fun p => by simp [smul_comm (χ p.2) c]

@[simp]
theorem coefficient_cutoffSymbol (a : LocalHomogeneousSymbol U V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  congrFun (LocalSymbol.coefficient_ofCutoff _ _ _) p

theorem restrict_cutoffSymbol (h : U' ≤ U) (a : LocalHomogeneousSymbol U V W m) :
    LocalSymbol.restrict h (cutoffSymbol χ a) = cutoffSymbol χ (restrict h a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-- Extending the cut-off term of a homogeneous symbol on `U` gives the cut-off term of its
extension. -/
theorem extend_cutoffSymbol {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalHomogeneousSymbol U V W m) :
    LocalSymbol.extend ψ hψ hψU (cutoffSymbol χ a) =
      HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a) :=
  Symbol.ext <| funext fun p => by
    simp only [LocalSymbol.coefficient_extend, coefficient_cutoffSymbol,
      HomogeneousSymbol.coefficient_cutoffSymbol, coefficient_extend]
    exact smul_comm _ _ _

end CutoffSymbol

end LocalHomogeneousSymbol

/-- The cut-off term of the restriction of a homogeneous symbol on `ℝⁿ` is the restriction of its
cut-off term. -/
theorem HomogeneousSymbol.restrict_cutoffSymbol {U : TopologicalSpace.Opens (CoordinateSpace n)}
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {m : ℝ} (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (cutoffSymbol χ a).restrict U = LocalHomogeneousSymbol.cutoffSymbol χ (a.restrict U) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-! ### Classical symbols on an open set -/

/-- A classical symbol of order `m` on `U × ℝⁿ`, for an open set `U ⊆ ℝⁿ` of positions: a local
symbol `a` of order `m` on `U` together with homogeneous terms `a_{m-j}` on `U` of degree `m - j`
for `j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` is a local symbol of order `m - N`. The expansion then holds for every
cutoff (`TauCeti.LocalClassicalSymbol.exists_remainder`), and the terms are determined by the
symbol (`TauCeti.LocalClassicalSymbol.ext`). -/
structure LocalClassicalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The full symbol. -/
  toLocalSymbol : LocalSymbol U V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → LocalHomogeneousSymbol U V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`;
  use `TauCeti.LocalClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : LocalSymbol U V W (m - N), ∀ p,
      r.coefficient p =
        toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  {ψ : CoordinateSpace n → ℝ}

/-- The termwise cut-off extension of a classical symbol on `U`, as a classical symbol on `ℝⁿ`;
bundled linearly as `TauCeti.LocalClassicalSymbol.extend`. -/
private def extendAux (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)
    (a : LocalClassicalSymbol U V W m) : ClassicalSymbol n V W m where
  toSymbol := LocalSymbol.extend ψ hψ hψU a.toLocalSymbol
  term j := LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j)
  exists_remainder' := by
    obtain ⟨χ, hχ⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    obtain ⟨r, hr⟩ := hχ N
    refine ⟨LocalSymbol.extend ψ hψ hψU r, fun p => ?_⟩
    simp only [LocalSymbol.coefficient_extend, hr, LocalHomogeneousSymbol.coefficient_extend,
      smul_sub, Finset.smul_sum, smul_comm (ψ p.1)]

section Remainder

variable (a : LocalClassicalSymbol U V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` is a local symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : LocalSymbol U V W (m - N), ∀ p, r.coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  refine ⟨LocalSymbol.ofCutoff _ (fun x hx ξ => ?_) fun ψ hψ _ hψU =>
    ⟨(extendAux ψ hψ hψU a).remainder χ N, funext fun p => ?_⟩,
    fun p => congrFun (LocalSymbol.coefficient_ofCutoff _ _ _) p⟩
  · simp [a.toLocalSymbol.coefficient_of_notMem x hx ξ, (a.term _).coefficient_of_notMem x hx ξ]
  · simp only [ClassicalSymbol.coefficient_remainder, extendAux, LocalSymbol.coefficient_extend,
      LocalHomogeneousSymbol.coefficient_extend, smul_sub, Finset.smul_sum, smul_comm (ψ p.1)]

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` after `N` terms, a local
symbol of order `m - N`. -/
def remainder (N : ℕ) : LocalSymbol U V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

/-- The remainder after `N` terms, included in the local symbols of order `m`, is the full symbol
minus the first `N` cut-off terms. -/
theorem inclusion_remainder (N : ℕ) :
    LocalSymbol.inclusion (by simp) (a.remainder χ N) =
      a.toLocalSymbol - ∑ k ∈ Finset.range N,
        LocalSymbol.inclusion (by simp) (LocalHomogeneousSymbol.cutoffSymbol χ (a.term k)) :=
  LocalSymbol.ext <| funext fun p => by
    simp [LocalSymbol.coefficient_sum]

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols on `U` with the same full
symbol have the same homogeneous terms. -/
theorem term_eq_of_toLocalSymbol_eq {a b : LocalClassicalSymbol U V W m}
    (h : a.toLocalSymbol = b.toLocalSymbol) (j : ℕ) : a.term j = b.term j := by
  refine LocalHomogeneousSymbol.ext_of_mem fun x hx ξ => ?_
  -- Extend both expansions by a cutoff equal to `1` near `x`; the extended full symbols agree.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen
      (singleton_subset_iff.2 hx)
  have hext := congrArg (fun c : HomogeneousSymbol _ _ V W _ => c.coefficient (x, ξ))
    (ClassicalSymbol.term_eq_of_toSymbol_eq (a := extendAux ψ hψ hψU a)
      (b := extendAux ψ hψ hψU b) (by simp only [extendAux, h]) j)
  simpa [extendAux, (hψ1 x rfl).self_of_nhds] using hext

/-- A classical symbol on `U` is determined by its full symbol. -/
@[ext]
theorem ext {a b : LocalClassicalSymbol U V W m} (h : a.toLocalSymbol = b.toLocalSymbol) :
    a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toLocalSymbol_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

theorem toLocalSymbol_injective :
    Function.Injective (toLocalSymbol : LocalClassicalSymbol U V W m → LocalSymbol U V W m) :=
  fun _ _ => ext

end Uniqueness

/-! ### The vector space of classical symbols of order `m` on `U` -/

section Module

instance : Zero (LocalClassicalSymbol U V W m) where
  zero :=
    { toLocalSymbol := 0
      term _ := 0
      exists_remainder' := ⟨default, fun _ => ⟨0, fun p => by simp⟩⟩ }

instance : Add (LocalClassicalSymbol U V W m) where
  add a b :=
    { toLocalSymbol := a.toLocalSymbol + b.toLocalSymbol
      term j := a.term j + b.term j
      exists_remainder' := ⟨default, fun N => ⟨a.remainder default N + b.remainder default N,
        fun p => by
          simp only [LocalSymbol.coefficient_add, Pi.add_apply, coefficient_remainder,
            LocalHomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
          abel⟩⟩ }

instance : SMul ℂ (LocalClassicalSymbol U V W m) where
  smul c a :=
    { toLocalSymbol := c • a.toLocalSymbol
      term j := c • a.term j
      exists_remainder' := ⟨default, fun N => ⟨c • a.remainder default N, fun p => by
        simp only [LocalSymbol.coefficient_smul, Pi.smul_apply, coefficient_remainder,
          LocalHomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum, smul_comm c]⟩⟩ }

instance : Neg (LocalClassicalSymbol U V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (LocalClassicalSymbol U V W m) where
  sub a b := a + -b

instance : SMul ℕ (LocalClassicalSymbol U V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (LocalClassicalSymbol U V W m) where
  smul k a := (k : ℂ) • a

variable (a b : LocalClassicalSymbol U V W m) (c : ℂ) (j : ℕ)

@[simp]
theorem toLocalSymbol_zero : (0 : LocalClassicalSymbol U V W m).toLocalSymbol = 0 := (rfl)

@[simp]
theorem toLocalSymbol_add : (a + b).toLocalSymbol = a.toLocalSymbol + b.toLocalSymbol := (rfl)

@[simp]
theorem toLocalSymbol_smul : (c • a).toLocalSymbol = c • a.toLocalSymbol := (rfl)

@[simp]
theorem toLocalSymbol_neg : (-a).toLocalSymbol = -a.toLocalSymbol :=
  neg_one_smul ℂ a.toLocalSymbol

@[simp]
theorem toLocalSymbol_sub : (a - b).toLocalSymbol = a.toLocalSymbol - b.toLocalSymbol := by
  rw [sub_eq_add_neg a.toLocalSymbol]
  exact congrArg (a.toLocalSymbol + ·) (toLocalSymbol_neg b)

@[simp]
theorem toLocalSymbol_nsmul (k : ℕ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toLocalSymbol

@[simp]
theorem toLocalSymbol_zsmul (k : ℤ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toLocalSymbol

@[simp]
theorem term_zero : (0 : LocalClassicalSymbol U V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j :=
  neg_one_smul ℂ (a.term j)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j := by
  rw [sub_eq_add_neg (a.term j)]
  exact congrArg (a.term j + ·) (term_neg b j)

instance : AddCommGroup (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.addCommGroup _ toLocalSymbol_zero toLocalSymbol_add toLocalSymbol_neg
    toLocalSymbol_sub (fun a k => toLocalSymbol_nsmul a k) (fun a k => toLocalSymbol_zsmul a k)

instance : Module ℂ (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.module ℂ ⟨⟨toLocalSymbol, toLocalSymbol_zero⟩, toLocalSymbol_add⟩
    fun c a => toLocalSymbol_smul a c

end Module

/-! ### Extension by a cutoff -/

section Extend

/-- The extension by zero of the cut-off classical symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ`
whose support is a closed subset of `ℝⁿ` contained in `U`: a classical symbol on `ℝⁿ`, whose
homogeneous terms are the cut-off extensions of those of `a`. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalClassicalSymbol U V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun := extendAux ψ hψ hψU
  map_add' _ _ := ClassicalSymbol.ext (map_add (LocalSymbol.extend ψ hψ hψU) _ _)
  map_smul' c _ := ClassicalSymbol.ext (map_smul (LocalSymbol.extend ψ hψ hψU) c _)

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) (a : LocalClassicalSymbol U V W m)

@[simp]
theorem toSymbol_extend :
    (extend ψ hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol := (rfl)

@[simp]
theorem term_extend (j : ℕ) :
    (extend ψ hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) := (rfl)

end Extend

/-! ### Restriction to smaller open sets -/

section Restrict

/-- The restriction of a classical symbol on `U` to a smaller open set `U'`, termwise. -/
def restrict (h : U' ≤ U) : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalClassicalSymbol U' V W m where
  toFun a :=
    { toLocalSymbol := LocalSymbol.restrict h a.toLocalSymbol
      term j := LocalHomogeneousSymbol.restrict h (a.term j)
      exists_remainder' := ⟨default, fun N => ⟨LocalSymbol.restrict h (a.remainder default N),
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U' <;> simp [hx]⟩⟩ }
  map_add' _ _ := ext (map_add (LocalSymbol.restrict h) _ _)
  map_smul' c _ := ext (map_smul (LocalSymbol.restrict h) c _)

variable (a : LocalClassicalSymbol U V W m)

@[simp]
theorem toLocalSymbol_restrict (h : U' ≤ U) :
    (restrict h a).toLocalSymbol = LocalSymbol.restrict h a.toLocalSymbol := (rfl)

@[simp]
theorem term_restrict (h : U' ≤ U) (j : ℕ) :
    (restrict h a).term j = LocalHomogeneousSymbol.restrict h (a.term j) := (rfl)

@[simp]
theorem restrict_self : restrict le_rfl a = a :=
  ext (LocalSymbol.restrict_self _)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext (LocalSymbol.restrict_restrict _ _ _)

end Restrict

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `ℝⁿ`, the local classical symbols are exactly the classical symbols: a classical
symbol is a local classical symbol on `⊤` with the same full symbol and homogeneous terms, and
this is a linear equivalence. -/
def restrictTopEquiv :
    ClassicalSymbol n V W m ≃ₗ[ℂ]
      LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { toLocalSymbol := Symbol.restrictTopEquiv a.toSymbol
      term j := HomogeneousSymbol.restrictTopEquiv (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv (a.remainder default N), fun p => by simp⟩⟩ }
  map_add' _ _ := LocalClassicalSymbol.ext (map_add Symbol.restrictTopEquiv _ _)
  map_smul' c _ := LocalClassicalSymbol.ext (map_smul Symbol.restrictTopEquiv c _)
  invFun a :=
    { toSymbol := Symbol.restrictTopEquiv.symm a.toLocalSymbol
      term j := HomogeneousSymbol.restrictTopEquiv.symm (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv.symm (a.remainder default N), fun p => by simp⟩⟩ }
  left_inv a := ClassicalSymbol.ext (Symbol.restrictTopEquiv.symm_apply_apply a.toSymbol)
  right_inv a :=
    LocalClassicalSymbol.ext (Symbol.restrictTopEquiv.apply_symm_apply a.toLocalSymbol)

@[simp]
theorem toLocalSymbol_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) :
    (restrictTopEquiv a).toLocalSymbol = Symbol.restrictTopEquiv a.toSymbol := (rfl)

@[simp]
theorem term_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) (j : ℕ) :
    (restrictTopEquiv a).term j = HomogeneousSymbol.restrictTopEquiv (a.term j) := (rfl)

@[simp]
theorem toSymbol_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a : ClassicalSymbol n V W m).toSymbol =
      Symbol.restrictTopEquiv.symm a.toLocalSymbol := (rfl)

@[simp]
theorem term_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) (j : ℕ) :
    (restrictTopEquiv.symm a : ClassicalSymbol n V W m).term j =
      HomogeneousSymbol.restrictTopEquiv.symm (a.term j) := (rfl)

/-- The restriction of a classical symbol on `ℝⁿ` to the open set `U` of positions: the restriction
of its full symbol, with the restricted homogeneous terms. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    ClassicalSymbol n V W m →ₗ[ℂ] LocalClassicalSymbol U V W m :=
  LocalClassicalSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

variable (a : ClassicalSymbol n V W m)

@[simp]
theorem toLocalSymbol_restrict : (a.restrict U).toLocalSymbol = a.toSymbol.restrict U :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [restrict, hx]

@[simp]
theorem term_restrict (j : ℕ) : (a.restrict U).term j = (a.term j).restrict U :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ => by simp [restrict, hx]

@[simp]
theorem restrict_restrict (h : U' ≤ U) :
    LocalClassicalSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalClassicalSymbol.ext (by simp)

/-- Restricting a classical symbol to all of `ℝⁿ` gives the corresponding local classical symbol
on `⊤`. -/
@[simp]
theorem restrict_top : a.restrict ⊤ = restrictTopEquiv a :=
  LocalClassicalSymbol.restrict_self (restrictTopEquiv a)

/-- The cut-off extension of the restriction of a classical symbol on `ℝⁿ` is its product with the
cutoff. -/
theorem coefficient_toSymbol_extend_restrict {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (p : CoordinateSpace n × CoordinateSpace n) :
    (LocalClassicalSymbol.extend ψ hψ hψU (a.restrict U)).toSymbol.coefficient p =
      ψ p.1 • a.toSymbol.coefficient p := by
  simp [LocalSymbol.coefficient_extend_restrict hψ hψU]

end ClassicalSymbol

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original classical symbol. -/
theorem restrict_extend_of_eqOn_one {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (h : U' ≤ U) (hψ1 : EqOn ψ 1 U') (a : LocalClassicalSymbol U V W m) :
    ClassicalSymbol.restrict U' (extend ψ hψ hψU a) = restrict h a :=
  ext (by simp [LocalSymbol.restrict_extend_of_eqOn_one hψ hψU h hψ1])

/-! ### The principal symbol -/

section Principal

variable (a b : LocalClassicalSymbol U V W m)

/-- The principal symbol of a classical symbol of order `m` on `U`: its leading homogeneous term
`a_m`, of degree `m`. -/
def principal : LocalHomogeneousSymbol U V W m :=
  (a.term 0).castDegree (by simp)

theorem principal_def : a.principal = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  (rfl)

@[simp]
theorem principal_zero : (0 : LocalClassicalSymbol U V W m).principal = 0 :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_restrict (h : U' ≤ U) :
    (restrict h a).principal = LocalHomogeneousSymbol.restrict h a.principal :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ => by simp [hx]

@[simp]
theorem principal_extend {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) :
    (extend ψ hψ hψU a).principal = LocalHomogeneousSymbol.extend ψ hψ hψU a.principal :=
  HomogeneousSymbol.ext (funext fun p => by simp)

end Principal

end LocalClassicalSymbol

@[simp]
theorem ClassicalSymbol.principal_restrict {U : TopologicalSpace.Opens (CoordinateSpace n)}
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {m : ℝ} (a : ClassicalSymbol n V W m) :
    (a.restrict U).principal = a.principal.restrict U :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ => by simp [hx]

end TauCeti
