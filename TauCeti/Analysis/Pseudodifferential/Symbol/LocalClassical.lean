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

In a chart of a manifold the positions range over an open set `U ⊆ ℝⁿ`, and the symbols of the
operators there are the local symbols `TauCeti.LocalSymbol U V W m` of
`TauCeti.Analysis.Pseudodifferential.LocalSymbol`. This file restricts the classical symbols
`TauCeti.ClassicalSymbol n V W m` of `TauCeti.Analysis.Pseudodifferential.Symbol.Classical` to
such open sets.

A *local homogeneous symbol* of degree `m` on `U` (`TauCeti.LocalHomogeneousSymbol U E V W m`) is
a map `a(x, ξ)`, smooth on `U × (E \ {0})` and positively homogeneous of degree `m` in `ξ`. As for
`TauCeti.HomogeneousSymbol` and `TauCeti.LocalSymbol`, its values elsewhere are fixed by
convention: it vanishes at `ξ = 0` and at positions outside `U`, so it is determined by its values
on `U × (E \ {0})` (`TauCeti.LocalHomogeneousSymbol.ext_of_mem`).

A *local classical symbol* of order `m` on `U` (`TauCeti.LocalClassicalSymbol U V W m`) is a local
symbol `a` of order `m` together with local homogeneous terms `a_{m-j}` of degree `m - j` such
that for some frequency cutoff `χ` and every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a
local symbol of order `m - N`. Since the terms are only smooth on `U × (E \ {0})`, they need not be
restrictions of homogeneous symbols on `ℝⁿ` (for instance `ξ₁ / x₁` on the half-space `x₁ > 0`).

The main results are:

* `TauCeti.HomogeneousSymbol.restrict`, `TauCeti.LocalHomogeneousSymbol.restrict` and
  `TauCeti.LocalHomogeneousSymbol.extend`: restriction of homogeneous terms to open sets, and
  their extension by zero after multiplication by a cutoff;
  `TauCeti.HomogeneousSymbol.restrictTopEquiv` identifies the local homogeneous symbols on all of
  `X` with the homogeneous symbols;
* `TauCeti.ClassicalSymbol.restrict`: a classical symbol on `ℝⁿ` restricts to a classical symbol on
  `U`, termwise (`TauCeti.ClassicalSymbol.term_restrict`); `TauCeti.LocalClassicalSymbol.restrict`
  restricts further to smaller open sets, and restrictions compose
  (`TauCeti.LocalClassicalSymbol.restrict_restrict`, `TauCeti.ClassicalSymbol.restrict_restrict`);
* `TauCeti.ClassicalSymbol.restrictTopEquiv`: for `U = ℝⁿ` restriction is a linear equivalence
  (`TauCeti.ClassicalSymbol.restrict_top`), so the local classical symbols on all of `ℝⁿ` are
  exactly the classical symbols;
* `TauCeti.LocalClassicalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `ℝⁿ` contained in `U`, a classical symbol on `U` extends by zero to
  a classical symbol on `ℝⁿ` with terms `ψ(x) a_{m-j}(x, ξ)`; its restriction to an open set on
  which `ψ = 1` is the restriction of the original symbol
  (`TauCeti.LocalClassicalSymbol.restrict_extend_of_eqOn_one`);
* `TauCeti.LocalClassicalSymbol.exists_toLocalSymbol_eq_of_extend`: conversely, a local symbol with
  local homogeneous terms is classical as soon as all its compactly supported cut-off extensions are
  classical with the cut-off terms, so being classical is a local property of a symbol;
* `TauCeti.LocalClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff;
* `TauCeti.LocalClassicalSymbol.term_eq_of_toLocalSymbol_eq` and
  `TauCeti.LocalClassicalSymbol.ext`: the homogeneous terms are determined by the local symbol;
* the local classical symbols of order `m` on `U` form a complex vector space, termwise, and
  `TauCeti.LocalClassicalSymbol.principal` is the principal symbol, compatible with restriction
  and extension.

The proofs reduce to the classical symbols on `ℝⁿ`: near a compact set `K ⊆ U`, a local classical
symbol agrees with its extension by a cutoff equal to `1` near `K`, and
`TauCeti.LocalSymbol.exists_coefficient_eq_of_forall_isCompact` turns these comparisons into
statements on `U`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definitions 18.1.1
  and 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15) and (1.17).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-! ### Homogeneous symbols on an open set of positions -/

/-- A homogeneous symbol of real degree `m` on an open set `U` of positions: a map
`X × E → (V →L[ℂ] W)` of a position and a frequency that is smooth on `U × (E \ {0})` and
positively homogeneous of degree `m` in the frequency. By convention it vanishes at the zero
frequency and at positions outside `U`. -/
@[ext]
structure LocalHomogeneousSymbol {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : TopologicalSpace.Opens X) (E V W : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The value at a position and a frequency. -/
  coefficient : X × E → V →L[ℂ] W
  zero_covector : ∀ x, coefficient (x, 0) = 0
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient ((U : Set X) ×ˢ {ξ | ξ ≠ 0})
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] LocalHomogeneousSymbol.zero_covector

namespace LocalHomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {U U' U'' : TopologicalSpace.Opens X} {m m' : ℝ}

/-- A local homogeneous symbol is determined by its values at the positions of its domain and the
nonzero frequencies. -/
theorem ext_of_mem {a b : LocalHomogeneousSymbol U E V W m}
    (h : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext ⟨x, ξ⟩
  by_cases hx : x ∈ U
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · exact h x hx ξ hξ
  · rw [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]

/-! #### The vector space of local homogeneous symbols of a fixed degree -/

instance : Zero (LocalHomogeneousSymbol U E V W m) :=
  ⟨⟨0, fun _ ↦ rfl, fun _ _ _ ↦ rfl, contDiffOn_const, fun _ _ _ _ ↦ by simp⟩⟩

instance : Add (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun a b ↦ ⟨a.coefficient + b.coefficient, fun _ ↦ by simp,
    fun x hx ξ ↦ by simp [a.coefficient_of_notMem x hx, b.coefficient_of_notMem x hx],
    a.contDiffOn_coefficient.add b.contDiffOn_coefficient,
    fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht]⟩⟩

instance : Neg (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun a ↦ ⟨-a.coefficient, fun _ ↦ by simp, fun x hx ξ ↦ by simp [a.coefficient_of_notMem x hx],
    a.contDiffOn_coefficient.neg, fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht]⟩⟩

instance : Sub (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun a b ↦ ⟨a.coefficient - b.coefficient, fun _ ↦ by simp,
    fun x hx ξ ↦ by simp [a.coefficient_of_notMem x hx, b.coefficient_of_notMem x hx],
    a.contDiffOn_coefficient.sub b.contDiffOn_coefficient,
    fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht, smul_sub]⟩⟩

instance {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)] [SMulCommClass ℝ R (V →L[ℂ] W)]
    [ContinuousConstSMul R (V →L[ℂ] W)] : SMul R (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun c a ↦ ⟨c • a.coefficient, fun _ ↦ by simp,
    fun x hx ξ ↦ by simp [a.coefficient_of_notMem x hx], a.contDiffOn_coefficient.const_smul c,
    fun x ξ t ht ↦ by
      simp only [Pi.smul_apply, a.homogeneous x ξ t ht]
      exact (smul_comm (t ^ m) c _).symm⟩⟩

@[simp]
theorem coefficient_zero : (0 : LocalHomogeneousSymbol U E V W m).coefficient = 0 :=
  (rfl)

@[simp]
theorem coefficient_add (a b : LocalHomogeneousSymbol U E V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_neg (a : LocalHomogeneousSymbol U E V W m) :
    (-a).coefficient = -a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_sub (a b : LocalHomogeneousSymbol U E V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_smul {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (c : R)
    (a : LocalHomogeneousSymbol U E V W m) : (c • a).coefficient = c • a.coefficient :=
  (rfl)

theorem coefficient_injective :
    Function.Injective (coefficient : LocalHomogeneousSymbol U E V W m → X × E → V →L[ℂ] W) :=
  fun _ _ ↦ LocalHomogeneousSymbol.ext

instance : AddCommGroup (LocalHomogeneousSymbol U E V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun _ _ ↦ coefficient_smul _ _) (fun _ _ ↦ coefficient_smul _ _)

instance {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)] [SMulCommClass ℝ R (V →L[ℂ] W)]
    [ContinuousConstSMul R (V →L[ℂ] W)] : Module R (LocalHomogeneousSymbol U E V W m) :=
  coefficient_injective.module R
    { toFun := coefficient, map_zero' := coefficient_zero, map_add' := coefficient_add }
    coefficient_smul

@[simp]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → LocalHomogeneousSymbol U E V W m) :
    (∑ i ∈ s, f i).coefficient = ∑ i ∈ s, (f i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) f s

/-! #### Changing the degree -/

/-- Transport a local homogeneous symbol along an equality of degrees. -/
def castDegree (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    LocalHomogeneousSymbol U E V W m' where
  coefficient := a.coefficient
  zero_covector := a.zero_covector
  coefficient_of_notMem := a.coefficient_of_notMem
  contDiffOn_coefficient := a.contDiffOn_coefficient
  homogeneous := h ▸ a.homogeneous

@[simp]
theorem coefficient_castDegree (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    (a.castDegree h).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem castDegree_rfl (a : LocalHomogeneousSymbol U E V W m) : a.castDegree rfl = a :=
  (rfl)

@[simp]
theorem castDegree_zero (h : m = m') :
    (0 : LocalHomogeneousSymbol U E V W m).castDegree h = 0 :=
  (rfl)

@[simp]
theorem castDegree_add (h : m = m') (a b : LocalHomogeneousSymbol U E V W m) :
    (a + b).castDegree h = a.castDegree h + b.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_neg (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    (-a).castDegree h = -a.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_sub (h : m = m') (a b : LocalHomogeneousSymbol U E V W m) :
    (a - b).castDegree h = a.castDegree h - b.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_smul {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (h : m = m') (c : R)
    (a : LocalHomogeneousSymbol U E V W m) : (c • a).castDegree h = c • a.castDegree h :=
  (rfl)

/-! #### Restriction to smaller open sets -/

/-- The restriction of a local homogeneous symbol on `U` to a smaller open set `U'`, extended by
zero at positions outside `U'`. -/
def restrict (h : U' ≤ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] LocalHomogeneousSymbol U' E V W m where
  toFun a :=
    { coefficient := ((U' : Set X) ×ˢ univ).indicator a.coefficient
      zero_covector := fun x => by simp
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      contDiffOn_coefficient := (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr
        fun _ hp => indicator_of_mem (mk_mem_prod hp.1 (mem_univ _)) _
      homogeneous := fun x ξ t ht => by
        by_cases hx : x ∈ U'
        · simp [hx, a.homogeneous x ξ t ht]
        · simp [hx] }
  map_add' a b := by
    ext1
    exact indicator_add' _ _ _
  map_smul' c a := by
    ext1
    exact indicator_const_smul _ c _

theorem coefficient_restrict (h : U' ≤ U) (a : LocalHomogeneousSymbol U E V W m) :
    (restrict h a).coefficient = ((U' : Set X) ×ˢ univ).indicator a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrict_of_mem (h : U' ≤ U) (a : LocalHomogeneousSymbol U E V W m) {x : X}
    (hx : x ∈ U') (ξ : E) : (restrict h a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  indicator_of_mem (mk_mem_prod hx (mem_univ ξ)) _

@[simp]
theorem coefficient_restrict_of_notMem (h : U' ≤ U) (a : LocalHomogeneousSymbol U E V W m)
    {x : X} (hx : x ∉ U') (ξ : E) : (restrict h a).coefficient (x, ξ) = 0 :=
  (restrict h a).coefficient_of_notMem x hx ξ

@[simp]
theorem restrict_self (a : LocalHomogeneousSymbol U E V W m) : restrict le_rfl a = a :=
  ext_of_mem fun _ hx ξ _ => coefficient_restrict_of_mem le_rfl a hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalHomogeneousSymbol U E V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext_of_mem fun x hx ξ _ => by
    rw [coefficient_restrict_of_mem _ _ hx, coefficient_restrict_of_mem _ _ (h' hx),
      coefficient_restrict_of_mem _ _ hx]

@[simp]
theorem restrict_castDegree (h : U' ≤ U) (hm : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    restrict h (a.castDegree hm) = (restrict h a).castDegree hm :=
  (rfl)

/-! #### Extension by a cutoff -/

section Extend

variable {ψ : X → ℝ}

/-- The cut-off coefficient `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose support is a closed
subset of `X` contained in `U`, is smooth away from the zero frequency. -/
private theorem contDiffOn_cutoff_smul (a : LocalHomogeneousSymbol U E V W m)
    (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    ContDiffOn ℝ ∞ (fun p : X × E => ψ p.1 • a.coefficient p) {p | p.2 ≠ 0} := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hx : p.1 ∈ U
  · exact (hψ.comp contDiff_fst).contDiffAt.smul (a.contDiffOn_coefficient.contDiffAt
      ((U.isOpen.prod isOpen_compl_singleton).mem_nhds ⟨hx, hp⟩))
  · -- Outside `tsupport ψ` the cut-off coefficient vanishes near `p`.
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto p).eventually
      (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hψU h))] with q hq
    simp [hq]

/-- The extension by zero of the cut-off symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose
support is a closed subset of `X` contained in `U`: a homogeneous symbol on `X`. -/
def extend (ψ : X → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] HomogeneousSymbol X E V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      zero_covector := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_cutoff_smul hψ hψU
      homogeneous := fun x ξ t ht => by simp [a.homogeneous x ξ t ht, smul_comm (ψ x)] }
  map_add' a b := HomogeneousSymbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := HomogeneousSymbol.ext <| funext fun p => by simp [smul_comm (ψ p.1) c]

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem coefficient_extend (a : LocalHomogeneousSymbol U E V W m) (p : X × E) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p :=
  (rfl)

@[simp]
theorem extend_castDegree (hm : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    extend ψ hψ hψU (a.castDegree hm) = (extend ψ hψ hψU a).castDegree hm :=
  HomogeneousSymbol.ext <| funext fun p => by simp

end Extend

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {U U' : TopologicalSpace.Opens X} {m m' : ℝ}

/-- Over all of `X`, the local homogeneous symbols are exactly the homogeneous symbols: a
homogeneous symbol is a local homogeneous symbol on `⊤` with the same coefficient, and this is a
linear equivalence. -/
def restrictTopEquiv :
    HomogeneousSymbol X E V W m ≃ₗ[ℂ] LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens X) E V W m
    where
  toFun a :=
    { coefficient := a.coefficient
      zero_covector := a.zero_covector
      coefficient_of_notMem := fun x hx => absurd (TopologicalSpace.Opens.mem_top x) hx
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp => hp.2
      homogeneous := a.homogeneous }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a :=
    { coefficient := a.coefficient
      zero_covector := a.zero_covector
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun p hp =>
        mk_mem_prod (TopologicalSpace.Opens.mem_top p.1) hp
      homogeneous := a.homogeneous }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coefficient_restrictTopEquiv_apply (a : HomogeneousSymbol X E V W m) :
    (restrictTopEquiv a).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrictTopEquiv_symm_apply
    (a : LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens X) E V W m) :
    (restrictTopEquiv.symm a : HomogeneousSymbol X E V W m).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem restrictTopEquiv_castDegree (h : m = m') (a : HomogeneousSymbol X E V W m) :
    restrictTopEquiv (a.castDegree h) = (restrictTopEquiv a).castDegree h :=
  LocalHomogeneousSymbol.ext (by simp)

/-- The restriction of a homogeneous symbol on `X` to the open set `U` of positions, extended by
zero at positions outside `U`. -/
def restrict (U : TopologicalSpace.Opens X) :
    HomogeneousSymbol X E V W m →ₗ[ℂ] LocalHomogeneousSymbol U E V W m :=
  LocalHomogeneousSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

theorem coefficient_restrict (a : HomogeneousSymbol X E V W m) :
    (a.restrict U).coefficient = ((U : Set X) ×ˢ univ).indicator a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrict_of_mem (a : HomogeneousSymbol X E V W m) {x : X} (hx : x ∈ U)
    (ξ : E) : (a.restrict U).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  LocalHomogeneousSymbol.coefficient_restrict_of_mem le_top (restrictTopEquiv a) hx ξ

@[simp]
theorem coefficient_restrict_of_notMem (a : HomogeneousSymbol X E V W m) {x : X} (hx : x ∉ U)
    (ξ : E) : (a.restrict U).coefficient (x, ξ) = 0 :=
  (a.restrict U).coefficient_of_notMem x hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : HomogeneousSymbol X E V W m) :
    LocalHomogeneousSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalHomogeneousSymbol.restrict_restrict le_top h (restrictTopEquiv a)

/-- Restricting a homogeneous symbol to all of `X` gives the corresponding local homogeneous
symbol on `⊤`. -/
@[simp]
theorem restrict_top (a : HomogeneousSymbol X E V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  LocalHomogeneousSymbol.restrict_self (restrictTopEquiv a)

@[simp]
theorem restrict_castDegree (h : m = m') (a : HomogeneousSymbol X E V W m) :
    (a.castDegree h).restrict U = (a.restrict U).castDegree h :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

end HomogeneousSymbol

namespace LocalHomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {U U' : TopologicalSpace.Opens X} {m : ℝ}
  {ψ : X → ℝ}

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original symbol. -/
theorem restrict_extend_of_eqOn_one (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) (h : U' ≤ U)
    (hψ1 : EqOn ψ 1 U') (a : LocalHomogeneousSymbol U E V W m) :
    (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext_of_mem fun x hx ξ _ => by simp [hx, (hψ1 hx).trans (Pi.one_apply x)]

/-- The cut-off extension of the restriction of a homogeneous symbol on `X` is its product with
the cutoff. -/
theorem coefficient_extend_restrict (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)
    (a : HomogeneousSymbol X E V W m) (p : X × E) :
    (extend ψ hψ hψU (a.restrict U)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

end LocalHomogeneousSymbol

/-! ### Classical symbols on an open set of positions -/

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- A classical symbol of order `m` on an open set `U ⊆ ℝⁿ` of positions: a local symbol `a` of
order `m` on `U` together with local homogeneous terms `a_{m-j}` of degree `m - j` for
`j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` is a local symbol of order `m - N`. The expansion then holds for every
cutoff (`TauCeti.LocalClassicalSymbol.exists_remainder`), and the terms are determined by the
local symbol (`TauCeti.LocalClassicalSymbol.ext`). -/
structure LocalClassicalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The full local symbol. -/
  toLocalSymbol : LocalSymbol U V W m
  /-- The local homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → LocalHomogeneousSymbol U (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order
  `m - N`; use `TauCeti.LocalClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : LocalSymbol U V W (m - N), ∀ p,
      r.coefficient p =
        toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)}

section ExtendAux

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- The cut-off extension of a local classical symbol, before the vector space structure is
available; see `TauCeti.LocalClassicalSymbol.extend`. -/
private def extendAux (a : LocalClassicalSymbol U V W m) : ClassicalSymbol n V W m where
  toSymbol := LocalSymbol.extend ψ hψ hψU a.toLocalSymbol
  term j := LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j)
  exists_remainder' := by
    obtain ⟨χ, hχ⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    obtain ⟨r, hr⟩ := hχ N
    exact ⟨LocalSymbol.extend ψ hψ hψU r, fun p => by
      simp [hr, smul_sub, Finset.smul_sum, smul_comm (ψ p.1)]⟩

private theorem toSymbol_extendAux (a : LocalClassicalSymbol U V W m) :
    (extendAux hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol :=
  (rfl)

private theorem term_extendAux (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (extendAux hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) :=
  (rfl)

end ExtendAux

section Remainder

variable (a : LocalClassicalSymbol U V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a local classical symbol is a local symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : LocalSymbol U V W (m - N), ∀ p, r.coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  obtain ⟨r, hr⟩ := LocalSymbol.exists_coefficient_eq_of_forall_isCompact
    (f := fun p => a.toLocalSymbol.coefficient p -
      ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p)
    (fun x hx ξ => by
      simp [a.toLocalSymbol.coefficient_of_notMem x hx, (a.term _).coefficient_of_notMem x hx])
    fun K hKU hK => by
      -- Near `K`, the remainder agrees with that of the extension by a cutoff equal to `1` near
      -- `K`.
      obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hKU
      refine ⟨(extendAux hψ hψU a).remainder χ N, fun x hx => ?_⟩
      filter_upwards [hψ1 x hx] with y hy η
      simp [toSymbol_extendAux, term_extendAux, hy]
  exact ⟨r, fun p => congrFun hr p⟩

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a local classical symbol after `N` terms, a local
symbol of order `m - N`. -/
def remainder (N : ℕ) : LocalSymbol U V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two local classical symbols with the same local symbol
have the same homogeneous terms. -/
theorem term_eq_of_toLocalSymbol_eq {a b : LocalClassicalSymbol U V W m}
    (h : a.toLocalSymbol = b.toLocalSymbol) (j : ℕ) : a.term j = b.term j := by
  refine LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => ?_
  -- Compare the extensions by a cutoff equal to `1` near `x`, which are classical symbols on `ℝⁿ`
  -- with the same full symbol.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen (singleton_subset_iff.2 hx)
  have hext := ClassicalSymbol.term_eq_of_toSymbol_eq (a := extendAux hψ hψU a)
    (b := extendAux hψ hψU b) (by rw [toSymbol_extendAux, toSymbol_extendAux, h]) j
  have hx1 : ψ x = 1 := (hψ1 x rfl).self_of_nhds
  simpa [term_extendAux, hx1] using congrArg (fun c => c.coefficient (x, ξ)) hext

/-- A local classical symbol is determined by its local symbol. -/
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

/-! #### The vector space of local classical symbols of order `m` -/

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
  neg a :=
    { toLocalSymbol := -a.toLocalSymbol
      term j := -a.term j
      exists_remainder' := ⟨default, fun N => ⟨-a.remainder default N, fun p => by
        simp only [LocalSymbol.coefficient_neg, Pi.neg_apply, coefficient_remainder,
          LocalHomogeneousSymbol.coefficient_neg, smul_neg, Finset.sum_neg_distrib]
        abel⟩⟩ }

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
theorem toLocalSymbol_neg : (-a).toLocalSymbol = -a.toLocalSymbol := (rfl)

@[simp]
theorem toLocalSymbol_sub : (a - b).toLocalSymbol = a.toLocalSymbol - b.toLocalSymbol :=
  (sub_eq_add_neg _ _).symm

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
theorem term_neg : (-a).term j = -a.term j := (rfl)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.addCommGroup _ toLocalSymbol_zero toLocalSymbol_add toLocalSymbol_neg
    toLocalSymbol_sub (fun a k => toLocalSymbol_nsmul a k) (fun a k => toLocalSymbol_zsmul a k)

instance : Module ℂ (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.module ℂ ⟨⟨toLocalSymbol, toLocalSymbol_zero⟩, toLocalSymbol_add⟩
    fun c a => toLocalSymbol_smul a c

@[simp]
theorem toLocalSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → LocalClassicalSymbol U V W m) :
    (∑ i ∈ s, a i).toLocalSymbol = ∑ i ∈ s, (a i).toLocalSymbol :=
  map_sum (AddMonoidHom.mk' toLocalSymbol toLocalSymbol_add) a s

@[simp]
theorem term_sum {ι : Type*} (s : Finset ι) (a : ι → LocalClassicalSymbol U V W m) (j : ℕ) :
    (∑ i ∈ s, a i).term j = ∑ i ∈ s, (a i).term j :=
  map_sum (AddMonoidHom.mk' (fun a : LocalClassicalSymbol U V W m => a.term j)
    fun a b => term_add a b j) a s

end Module

/-! #### The principal symbol -/

section Principal

variable (a b : LocalClassicalSymbol U V W m)

/-- The principal symbol of a local classical symbol of order `m`: its leading homogeneous term
`a_m`, of degree `m`. -/
def principal : LocalHomogeneousSymbol U (CoordinateSpace n) V W m :=
  (a.term 0).castDegree (by simp)

theorem principal_def : a.principal = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  LocalHomogeneousSymbol.coefficient_castDegree _ _

@[simp]
theorem principal_zero : (0 : LocalClassicalSymbol U V W m).principal = 0 :=
  LocalHomogeneousSymbol.castDegree_zero _

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  LocalHomogeneousSymbol.castDegree_add _ _ _

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  LocalHomogeneousSymbol.castDegree_smul _ _ _

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  LocalHomogeneousSymbol.castDegree_neg _ _

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal := by
  simp [principal, LocalHomogeneousSymbol.castDegree_sub]

end Principal

/-! #### Restriction to smaller open sets -/

section Restrict

/-- The restriction of a local classical symbol on `U` to a smaller open set `U'`: the restriction
of the local symbol, with the restricted homogeneous terms. -/
def restrict (h : U' ≤ U) : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalClassicalSymbol U' V W m where
  toFun a :=
    { toLocalSymbol := LocalSymbol.restrict h a.toLocalSymbol
      term j := LocalHomogeneousSymbol.restrict h (a.term j)
      exists_remainder' := ⟨default, fun N => ⟨LocalSymbol.restrict h (a.remainder default N),
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U' <;> simp [hx]⟩⟩ }
  map_add' a b := ext (by simp)
  map_smul' c a := ext (by simp)

@[simp]
theorem toLocalSymbol_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).toLocalSymbol = LocalSymbol.restrict h a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (restrict h a).term j = LocalHomogeneousSymbol.restrict h (a.term j) :=
  (rfl)

@[simp]
theorem principal_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).principal = LocalHomogeneousSymbol.restrict h a.principal :=
  (rfl)

@[simp]
theorem restrict_self (a : LocalClassicalSymbol U V W m) : restrict le_rfl a = a :=
  ext (LocalSymbol.restrict_self a.toLocalSymbol)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalClassicalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext (LocalSymbol.restrict_restrict h h' a.toLocalSymbol)

end Restrict

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

/-- Over all of `ℝⁿ`, the local classical symbols are exactly the classical symbols: a classical
symbol on `ℝⁿ` is a local classical symbol on `⊤` with the same coefficients, and this is a linear
equivalence. -/
def restrictTopEquiv :
    ClassicalSymbol n V W m ≃ₗ[ℂ]
      LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { toLocalSymbol := Symbol.restrictTopEquiv a.toSymbol
      term j := HomogeneousSymbol.restrictTopEquiv (a.term j)
      exists_remainder' := ⟨default, fun N => ⟨Symbol.restrictTopEquiv (a.remainder default N),
        fun p => by simp⟩⟩ }
  map_add' _ _ := LocalClassicalSymbol.ext (map_add _ _ _)
  map_smul' _ _ := LocalClassicalSymbol.ext (map_smul _ _ _)
  invFun a :=
    { toSymbol := Symbol.restrictTopEquiv.symm a.toLocalSymbol
      term j := HomogeneousSymbol.restrictTopEquiv.symm (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv.symm (a.remainder default N), fun p => by simp⟩⟩ }
  left_inv a := ext (Symbol.restrictTopEquiv.symm_apply_apply a.toSymbol)
  right_inv a := LocalClassicalSymbol.ext (Symbol.restrictTopEquiv.apply_symm_apply a.toLocalSymbol)

@[simp]
theorem toLocalSymbol_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) :
    (restrictTopEquiv a).toLocalSymbol = Symbol.restrictTopEquiv a.toSymbol :=
  (rfl)

@[simp]
theorem term_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) (j : ℕ) :
    (restrictTopEquiv a).term j = HomogeneousSymbol.restrictTopEquiv (a.term j) :=
  (rfl)

@[simp]
theorem toSymbol_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a).toSymbol = Symbol.restrictTopEquiv.symm a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) (j : ℕ) :
    (restrictTopEquiv.symm a).term j = HomogeneousSymbol.restrictTopEquiv.symm (a.term j) :=
  (rfl)

/-- The restriction of a classical symbol on `ℝⁿ` to the open set `U` of positions: the restriction
of its full symbol, with the restricted homogeneous terms. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    ClassicalSymbol n V W m →ₗ[ℂ] LocalClassicalSymbol U V W m where
  toFun a :=
    { toLocalSymbol := a.toSymbol.restrict U
      term j := (a.term j).restrict U
      exists_remainder' := ⟨default, fun N => ⟨(a.remainder default N).restrict U,
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U <;> simp [hx]⟩⟩ }
  map_add' a b := LocalClassicalSymbol.ext (by simp)
  map_smul' c a := LocalClassicalSymbol.ext (by simp)

@[simp]
theorem toLocalSymbol_restrict (a : ClassicalSymbol n V W m) :
    (a.restrict U).toLocalSymbol = a.toSymbol.restrict U :=
  (rfl)

@[simp]
theorem term_restrict (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.restrict U).term j = (a.term j).restrict U :=
  (rfl)

@[simp]
theorem principal_restrict (a : ClassicalSymbol n V W m) :
    (a.restrict U).principal = a.principal.restrict U :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : ClassicalSymbol n V W m) :
    LocalClassicalSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalClassicalSymbol.ext (Symbol.restrict_restrict h a.toSymbol)

/-- Restricting a classical symbol to all of `ℝⁿ` gives the corresponding local classical symbol
on `⊤`. -/
@[simp]
theorem restrict_top (a : ClassicalSymbol n V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  LocalClassicalSymbol.ext (Symbol.restrict_top a.toSymbol)

end ClassicalSymbol

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

/-! #### Extension by a cutoff -/

section Extend

variable {ψ : CoordinateSpace n → ℝ}

/-- The extension by zero of the cut-off symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose
support is a closed subset of `ℝⁿ` contained in `U`: a classical symbol on `ℝⁿ`, with homogeneous
terms `ψ(x) a_{m-j}(x, ξ)`. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalClassicalSymbol U V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun := extendAux hψ hψU
  map_add' a b := ClassicalSymbol.ext <| by simp [toSymbol_extendAux]
  map_smul' c a := ClassicalSymbol.ext <| by simp [toSymbol_extendAux]

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem toSymbol_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_extend (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (extend ψ hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) :=
  (rfl)

@[simp]
theorem principal_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).principal = LocalHomogeneousSymbol.extend ψ hψ hψU a.principal :=
  HomogeneousSymbol.ext <| funext fun p => by simp

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalClassicalSymbol U V W m) : (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext (LocalSymbol.restrict_extend_of_eqOn_one hψ hψU h hψ1 a.toLocalSymbol)

end Extend

/-- **Being classical is a local property.** A local symbol `a` on `U` with local homogeneous terms
`t j` is classical, with these terms, as soon as for every compactly supported smooth cutoff `ψ`
with support in `U` the extension `ψ(x) a(x, ξ)` is a classical symbol on `ℝⁿ` with the terms
`ψ(x) t j (x, ξ)`. -/
theorem exists_toLocalSymbol_eq_of_extend (a : LocalSymbol U V W m)
    (t : (j : ℕ) → LocalHomogeneousSymbol U (CoordinateSpace n) V W (m - j))
    (h : ∀ (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U),
      HasCompactSupport ψ → ∃ c : ClassicalSymbol n V W m,
        c.toSymbol = LocalSymbol.extend ψ hψ hψU a ∧
          ∀ j, c.term j = LocalHomogeneousSymbol.extend ψ hψ hψU (t j)) :
    ∃ c : LocalClassicalSymbol U V W m, c.toLocalSymbol = a ∧ c.term = t := by
  refine ⟨⟨a, t, default, fun N => ?_⟩, rfl, rfl⟩
  obtain ⟨r, hr⟩ := LocalSymbol.exists_coefficient_eq_of_forall_isCompact
    (f := fun p => a.coefficient p -
      ∑ j ∈ Finset.range N, (default : FrequencyCutoff (CoordinateSpace n)) p.2 •
        (t j).coefficient p)
    (fun x hx ξ => by simp [a.coefficient_of_notMem x hx, (t _).coefficient_of_notMem x hx])
    fun K hKU hK => by
      -- Near `K`, use the remainder of the extension by a cutoff equal to `1` near `K`.
      obtain ⟨ψ, hψ, -, hψ1, hψc, hψU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hKU
      obtain ⟨c, hca, hct⟩ := h ψ hψ hψU hψc
      refine ⟨c.remainder default N, fun x hx => ?_⟩
      filter_upwards [hψ1 x hx] with y hy η
      simp [hca, hct, hy]
  exact ⟨r, fun p => congrFun hr p⟩

end LocalClassicalSymbol

end TauCeti
