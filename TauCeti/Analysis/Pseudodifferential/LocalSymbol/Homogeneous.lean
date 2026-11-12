/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Homogeneous symbols on an open set of positions

For an open set `U` of positions, a homogeneous symbol of degree `m` on `U` is a map `a(x, ξ)`
that is smooth on `U × (E \ {0})` and positively homogeneous of degree `m` in the frequency:
`a(x, t • ξ) = t ^ m • a(x, ξ)` for `t > 0`. These are the terms of the classical symbols on a
chart domain. As for `TauCeti.HomogeneousSymbol` at `ξ = 0`, and for `TauCeti.LocalSymbol`
outside the domain, values off `U × (E \ {0})` are fixed by a convention: the coefficient is `0`
at the zero frequency and at every position outside `U`, so the carrier
`TauCeti.LocalHomogeneousSymbol U E V W m` is extensional on its coefficient.

A homogeneous symbol on `U` need not be the restriction of one on the whole space (for instance
`1 / x₁` on the half-space `x₁ > 0`), so the local class is genuinely larger. The file compares
the two classes:

* `TauCeti.HomogeneousSymbol.restrictTopEquiv`: over the whole space, the local homogeneous
  symbols are exactly the homogeneous symbols;
* `TauCeti.HomogeneousSymbol.restrict` and `TauCeti.LocalHomogeneousSymbol.restrict`: a
  homogeneous symbol restricts to every open set of positions, and restrictions compose;
* `TauCeti.LocalHomogeneousSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed set contained in `U`, a homogeneous symbol on `U` extends by zero to a
  homogeneous symbol on the whole space, of the same degree; on an open set where `ψ = 1` the
  extension restricts back to the original symbol
  (`TauCeti.LocalHomogeneousSymbol.restrict_extend_of_eqOn_one`);
* `TauCeti.LocalHomogeneousSymbol.cutoffSymbol`: on `ℝⁿ`, the cut-off term `χ(ξ) a(x, ξ)` of a
  homogeneous symbol of degree `m` on `U` is a local symbol of order `m` on `U`, compatibly with
  restriction and with the cut-off terms `TauCeti.HomogeneousSymbol.cutoffSymbol` on `ℝⁿ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

/-- A homogeneous symbol of real degree `m` on an open set `U` of positions: a map
`X × E → (V →L[ℂ] W)` of a position and a frequency that is smooth on `U × (E \ {0})` and
positively homogeneous of degree `m` in the frequency. By convention it vanishes at the zero
frequency and at the positions outside `U`. -/
@[ext]
structure LocalHomogeneousSymbol (U : TopologicalSpace.Opens X) (E V W : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The value at a position and a frequency. -/
  coefficient : X × E → V →L[ℂ] W
  zero_covector : ∀ x, coefficient (x, 0) = 0
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient ((U : Set X) ×ˢ {ξ | ξ ≠ 0})
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] LocalHomogeneousSymbol.zero_covector

namespace LocalHomogeneousSymbol

variable {U U' U'' : TopologicalSpace.Opens X}

theorem coefficient_injective : Function.Injective
    (coefficient : LocalHomogeneousSymbol U E V W m → X × E → V →L[ℂ] W) :=
  fun _ _ h => LocalHomogeneousSymbol.ext h

/-- A homogeneous symbol on `U` is determined by its values at the positions of `U` and the
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

/-- The same symbol, regarded as a homogeneous symbol of an equal degree. -/
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

/-! ### The vector space of homogeneous symbols on `U` of a fixed degree -/

section Module

instance : Zero (LocalHomogeneousSymbol U E V W m) where
  zero := ⟨0, fun _ => rfl, fun _ _ _ => rfl, contDiffOn_const, fun _ _ _ _ => by simp⟩

instance : Add (LocalHomogeneousSymbol U E V W m) where
  add a b := ⟨a.coefficient + b.coefficient, fun _ => by simp,
    fun x hx ξ => by simp [a.coefficient_of_notMem x hx, b.coefficient_of_notMem x hx],
    a.contDiffOn_coefficient.add b.contDiffOn_coefficient,
    fun x ξ t ht => by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht]⟩

instance : SMul ℂ (LocalHomogeneousSymbol U E V W m) where
  smul c a := ⟨c • a.coefficient, fun _ => by simp,
    fun x hx ξ => by simp [a.coefficient_of_notMem x hx], a.contDiffOn_coefficient.const_smul c,
    fun x ξ t ht => by simp [a.homogeneous x ξ t ht, smul_comm c (t ^ m)]⟩

instance : Neg (LocalHomogeneousSymbol U E V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (LocalHomogeneousSymbol U E V W m) where
  sub a b := a + -b

instance : SMul ℕ (LocalHomogeneousSymbol U E V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (LocalHomogeneousSymbol U E V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : LocalHomogeneousSymbol U E V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : LocalHomogeneousSymbol U E V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : LocalHomogeneousSymbol U E V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : LocalHomogeneousSymbol U E V W m) :
    (-a).coefficient = -a.coefficient :=
  neg_one_smul ℂ a.coefficient

@[simp]
theorem coefficient_sub (a b : LocalHomogeneousSymbol U E V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (congrArg (a.coefficient + ·) (coefficient_neg b)).trans (sub_eq_add_neg _ _).symm

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : LocalHomogeneousSymbol U E V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : LocalHomogeneousSymbol U E V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (LocalHomogeneousSymbol U E V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (LocalHomogeneousSymbol U E V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

@[simp]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (a : ι → LocalHomogeneousSymbol U E V W m) :
    (∑ i ∈ s, a i).coefficient = ∑ i ∈ s, (a i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) a s

end Module

/-! ### Restriction to a smaller open set -/

section Restrict

/-- The restriction of a homogeneous symbol on `U` to a smaller open set `U'`, extended by zero at
positions outside `U'`. -/
def restrict (h : U' ≤ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] LocalHomogeneousSymbol U' E V W m where
  toFun a :=
    { coefficient := ((U' : Set X) ×ˢ univ).indicator a.coefficient
      zero_covector := fun x => by simp
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      contDiffOn_coefficient := (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr
        fun p hp => indicator_of_mem (mk_mem_prod hp.1 (mem_univ p.2)) _
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
theorem coefficient_restrict_of_mem (h : U' ≤ U) (a : LocalHomogeneousSymbol U E V W m)
    {x : X} (hx : x ∈ U') (ξ : E) : (restrict h a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
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
  ext_of_mem fun x hx ξ _ => by simp [hx, h' hx]

@[simp]
theorem restrict_castDegree (h : U' ≤ U) (hm : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    restrict h (a.castDegree hm) = (restrict h a).castDegree hm :=
  (rfl)

end Restrict

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {U U' : TopologicalSpace.Opens X}

/-- Over the whole space, the local homogeneous symbols are exactly the homogeneous symbols: a
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
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp => ⟨by simp, hp⟩
      homogeneous := a.homogeneous }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coefficient_restrictTopEquiv_apply (a : HomogeneousSymbol X E V W m) :
    (restrictTopEquiv a).coefficient = a.coefficient := (rfl)

@[simp]
theorem coefficient_restrictTopEquiv_symm_apply
    (a : LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens X) E V W m) :
    (restrictTopEquiv.symm a : HomogeneousSymbol X E V W m).coefficient = a.coefficient := (rfl)

/-- The restriction of a homogeneous symbol to the open set `U` of positions, extended by zero at
positions outside `U`: the restriction from `⊤` to `U` of the corresponding local homogeneous
symbol. -/
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

/-- Restricting a homogeneous symbol to the whole space gives the corresponding local homogeneous
symbol on `⊤`. -/
@[simp]
theorem restrict_top (a : HomogeneousSymbol X E V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  LocalHomogeneousSymbol.restrict_self (restrictTopEquiv a)

@[simp]
theorem restrict_castDegree (h : m = m') (a : HomogeneousSymbol X E V W m) :
    (a.castDegree h).restrict U = (a.restrict U).castDegree h :=
  LocalHomogeneousSymbol.ext (by simp [coefficient_restrict])

end HomogeneousSymbol

namespace LocalHomogeneousSymbol

variable {U U' : TopologicalSpace.Opens X}

/-! ### Extension by a cutoff -/

section Extend

variable {ψ : X → ℝ}

/-- The cut-off coefficient `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose support is a closed set
contained in `U`, is smooth at every nonzero frequency and every position: inside `U` both factors
are smooth, and off the support of `ψ` it vanishes nearby. -/
private theorem contDiffOn_cutoff_smul (a : LocalHomogeneousSymbol U E V W m)
    (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    ContDiffOn ℝ ∞ (fun p => ψ p.1 • a.coefficient p) {p | p.2 ≠ 0} := by
  intro p hp
  by_cases hpψ : p.1 ∈ tsupport ψ
  · have hpU : (U : Set X) ×ˢ {ξ | ξ ≠ 0} ∈ 𝓝 p :=
      (U.isOpen.prod isOpen_ne).mem_nhds ⟨hψU hpψ, hp⟩
    exact ((hψ.comp contDiff_fst).contDiffAt.smul
      (a.contDiffOn_coefficient.contDiffAt hpU)).contDiffWithinAt
  · have h0 : (fun q : X × E => ψ q.1 • a.coefficient q) =ᶠ[𝓝 p] fun _ => 0 :=
      ((continuous_fst.tendsto p).eventually
        (notMem_tsupport_iff_eventuallyEq.1 hpψ)).mono fun q hq => by simp [hq]
    exact (contDiffAt_const.congr_of_eventuallyEq h0).contDiffWithinAt

/-- The extension by zero of the cut-off symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose
support is a closed set contained in `U`: a homogeneous symbol on the whole space, of the same
degree. -/
def extend (ψ : X → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] HomogeneousSymbol X E V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      zero_covector := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_cutoff_smul hψ hψU
      homogeneous := fun x ξ t ht => by simp [a.homogeneous x ξ t ht, smul_comm (ψ x)] }
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
theorem coefficient_extend (a : LocalHomogeneousSymbol U E V W m) (p : X × E) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p :=
  (rfl)

/-- The cut-off extension of the restriction of a homogeneous symbol is its product with the
cutoff. -/
theorem coefficient_extend_restrict (a : HomogeneousSymbol X E V W m) (p : X × E) :
    (extend ψ hψ hψU (a.restrict U)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

@[simp]
theorem extend_castDegree (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    extend ψ hψ hψU (a.castDegree h) = (extend ψ hψ hψU a).castDegree h :=
  HomogeneousSymbol.ext (funext fun p => by simp)

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalHomogeneousSymbol U E V W m) :
    (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext_of_mem fun x hx ξ _ => by simp [hx, (hψ1 hx).trans (Pi.one_apply x)]

end Extend

end LocalHomogeneousSymbol

/-! ### The cut-off term on an open set of `ℝⁿ` -/

namespace LocalHomogeneousSymbol

variable {n : ℕ} {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

/-- Near a position of `U`, the cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol on `U` agrees
with the cut-off term of an extension of `a` to `ℝⁿ`. -/
private theorem exists_eventually_eq_cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n))
    (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m) {x : CoordinateSpace n}
    (hx : x ∈ U) :
    ∃ b : Symbol n V W m, ∀ᶠ y in 𝓝 x, ∀ ξ, b.coefficient (y, ξ) = χ ξ • a.coefficient (y, ξ) := by
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one
    U.isOpen (singleton_subset_iff.2 hx)
  refine ⟨HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a), ?_⟩
  filter_upwards [hψ1 x rfl] with y hy ξ
  simp [HomogeneousSymbol.coefficient_cutoffSymbol, hy]

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m` on an open set
`U ⊆ ℝⁿ`, as a local symbol of order `m` on `U`. -/
def cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n)) :
    LocalHomogeneousSymbol U (CoordinateSpace n) V W m →ₗ[ℂ] LocalSymbol U V W m where
  toFun a := LocalSymbol.ofEventuallyEq (fun p => χ p.2 • a.coefficient p)
    (fun x hx ξ => by simp [a.coefficient_of_notMem x hx])
    fun _ hx => exists_eventually_eq_cutoffSymbol χ a hx
  map_add' a b := by
    ext1
    funext p
    simp [smul_add]
  map_smul' c a := by
    ext1
    funext p
    simp [smul_comm (χ p.2) c]

variable (χ : FrequencyCutoff (CoordinateSpace n))

@[simp]
theorem coefficient_cutoffSymbol (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  congrFun (LocalSymbol.coefficient_ofEventuallyEq _ _ _) p

theorem cutoffSymbol_restrict (h : U' ≤ U)
    (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m) :
    cutoffSymbol χ (restrict h a) = LocalSymbol.restrict h (cutoffSymbol χ a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-- The cut-off term of the restriction of a homogeneous symbol on `ℝⁿ` is the restriction of its
cut-off term. -/
theorem cutoffSymbol_restrict_homogeneousSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    cutoffSymbol χ (a.restrict U) = (HomogeneousSymbol.cutoffSymbol χ a).restrict U :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx, HomogeneousSymbol.coefficient_cutoffSymbol]

/-- Cutting off in position and in frequency commute: the cut-off extension of the cut-off term
is the cut-off term of the cut-off extension. -/
theorem extend_cutoffSymbol {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m) :
    LocalSymbol.extend ψ hψ hψU (cutoffSymbol χ a) =
      HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a) :=
  Symbol.ext <| funext fun p => by
    simp [HomogeneousSymbol.coefficient_cutoffSymbol, smul_comm (ψ p.1) (χ p.2)]

end LocalHomogeneousSymbol

end TauCeti
