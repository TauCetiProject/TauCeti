/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Cutoff

/-!
# Homogeneous symbols on an open set of positions

In a chart of a manifold the symbols live on `U × ℝⁿ` for an open set `U ⊆ ℝⁿ` of positions
(`TauCeti.LocalSymbol`). This file restricts the homogeneous symbols of
`TauCeti/Analysis/Pseudodifferential/HomogeneousSymbol.lean`, the terms of a classical symbol, to
such open sets.

A *homogeneous symbol of degree `m` on `U`* (`TauCeti.LocalHomogeneousSymbol`) is a map
`a(x, ξ)`, smooth on `U × (E \ {0})` and positively homogeneous of degree `m` in the frequency.
As for `TauCeti.LocalSymbol`, its value at positions outside `U` is set to `0`, and as for
`TauCeti.HomogeneousSymbol` its value at the zero frequency is set to `0`; so it is determined by
its values on `U × (E \ {0})` (`TauCeti.LocalHomogeneousSymbol.ext_of_mem`). We prove:

* `TauCeti.HomogeneousSymbol.restrict` and `TauCeti.LocalHomogeneousSymbol.restrict`: restriction
  to smaller open sets of positions, compatible with composition;
  `TauCeti.HomogeneousSymbol.restrictTopEquiv` identifies the homogeneous symbols on all of `X`
  with those on `⊤`;
* `TauCeti.LocalHomogeneousSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `U`, a homogeneous symbol on `U` extends by zero to a homogeneous
  symbol on all positions;
* `TauCeti.LocalHomogeneousSymbol.cutoffSymbol`: for a frequency cutoff `χ`, the cut-off term
  `χ(ξ) a(x, ξ)` is a symbol of order `m` on `U`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace TauCeti

/-! ### Homogeneous symbols on an open set of positions -/

/-- A homogeneous symbol of real degree `m` on the open set `U` of positions: a map
`X × E → (V →L[ℂ] W)` of a position and a frequency that is smooth on `U × (E \ {0})` and
positively homogeneous of degree `m` in the frequency. By convention it vanishes at positions
outside `U` and at the zero frequency. -/
@[ext]
structure LocalHomogeneousSymbol {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : TopologicalSpace.Opens X) (E V W : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (m : ℝ) where
  /-- The value at a position and a frequency, set to `0` at positions outside `U`. -/
  coefficient : X × E → V →L[ℂ] W
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  zero_covector : ∀ x, coefficient (x, 0) = 0
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient ((U : Set X) ×ˢ {ξ | ξ ≠ 0})
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] LocalHomogeneousSymbol.zero_covector

namespace LocalHomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U U' U'' : TopologicalSpace.Opens X} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

theorem coefficient_injective :
    Function.Injective (coefficient : LocalHomogeneousSymbol U E V W m → X × E → V →L[ℂ] W) :=
  fun _ _ => LocalHomogeneousSymbol.ext

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

section Module

instance : Zero (LocalHomogeneousSymbol U E V W m) :=
  ⟨⟨0, fun _ _ _ => rfl, fun _ => rfl, contDiffOn_const, fun _ _ _ _ => by simp⟩⟩

instance : Add (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun a b => ⟨a.coefficient + b.coefficient,
    fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ],
    fun _ => by simp, a.contDiffOn_coefficient.add b.contDiffOn_coefficient,
    fun x ξ t ht => by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht]⟩⟩

instance : SMul ℂ (LocalHomogeneousSymbol U E V W m) :=
  ⟨fun c a => ⟨c • a.coefficient, fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ],
    fun _ => by simp, a.contDiffOn_coefficient.const_smul c, fun x ξ t ht => by
      simp only [Pi.smul_apply, a.homogeneous x ξ t ht]
      exact (smul_comm (t ^ m) c _).symm⟩⟩

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
    (a - b).coefficient = a.coefficient - b.coefficient := by
  rw [sub_eq_add_neg a.coefficient]
  exact congrArg (a.coefficient + ·) (coefficient_neg b)

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
theorem coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → LocalHomogeneousSymbol U E V W m) :
    (∑ i ∈ s, f i).coefficient = ∑ i ∈ s, (f i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) f s

end Module

/-- Transport a homogeneous symbol on `U` along an equality of degrees. -/
def castDegree (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    LocalHomogeneousSymbol U E V W m' where
  coefficient := a.coefficient
  coefficient_of_notMem := a.coefficient_of_notMem
  zero_covector := a.zero_covector
  contDiffOn_coefficient := a.contDiffOn_coefficient
  homogeneous := h ▸ a.homogeneous

@[simp]
theorem coefficient_castDegree (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    (a.castDegree h).coefficient = a.coefficient := (rfl)

section Restrict

/-- The restriction of a homogeneous symbol on `U` to a smaller open set `U'`, extended by zero at
positions outside `U'`. -/
def restrict (h : U' ≤ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] LocalHomogeneousSymbol U' E V W m where
  toFun a :=
    { coefficient := ((U' : Set X) ×ˢ univ).indicator a.coefficient
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      zero_covector := fun x => by
        by_cases hx : x ∈ U'
        · rw [indicator_of_mem (mk_mem_prod hx (mem_univ _)), a.zero_covector]
        · exact indicator_of_notMem (by simp [hx]) _
      contDiffOn_coefficient :=
        (a.contDiffOn_coefficient.mono (prod_mono h subset_rfl)).congr fun p hp =>
          indicator_of_mem (mk_mem_prod hp.1 (mem_univ _)) _
      homogeneous := fun x ξ t ht => by
        by_cases hx : x ∈ U'
        · simp only [indicator_of_mem (mk_mem_prod hx (mem_univ _)), a.homogeneous x ξ t ht]
        · simp only [indicator_of_notMem (show (x, _) ∉ (U' : Set X) ×ˢ univ by simp [hx]),
            smul_zero] }
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
  ext_of_mem fun x hx ξ _ => by
    rw [coefficient_restrict_of_mem _ _ hx, coefficient_restrict_of_mem _ _ (h' hx),
      coefficient_restrict_of_mem _ _ hx]

@[simp]
theorem restrict_castDegree (h : U' ≤ U) (hm : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    restrict h (a.castDegree hm) = (restrict h a).castDegree hm :=
  ext_of_mem fun x hx ξ _ => by simp [hx]

end Restrict

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U U' : TopologicalSpace.Opens X} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `X`, the homogeneous symbols on open sets of positions are exactly the homogeneous
symbols: a homogeneous symbol is a homogeneous symbol on `⊤` with the same coefficient, and this
is a linear equivalence. -/
def restrictTopEquiv :
    HomogeneousSymbol X E V W m ≃ₗ[ℂ] LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens X) E V W m
    where
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
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp => ⟨mem_univ _, hp⟩
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
positions outside `U`: the restriction from `⊤` to `U` of the corresponding homogeneous symbol on
`⊤`. -/
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

/-- Restricting a homogeneous symbol to all of `X` gives the corresponding homogeneous symbol on
`⊤`. -/
@[simp]
theorem restrict_top (a : HomogeneousSymbol X E V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  LocalHomogeneousSymbol.restrict_self (restrictTopEquiv a)

@[simp]
theorem restrict_castDegree {m' : ℝ} (h : m = m') (a : HomogeneousSymbol X E V W m) :
    (a.castDegree h).restrict U = (a.restrict U).castDegree h :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

end HomogeneousSymbol

namespace LocalHomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U U' : TopologicalSpace.Opens X} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

section Extend

variable {ψ : X → ℝ}

/-- The extension by zero of the cut-off homogeneous symbol `ψ(x) a(x, ξ)`, for a smooth cutoff
`ψ` whose support is a closed subset of `X` contained in `U`: a homogeneous symbol on all
positions. -/
def extend (ψ : X → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalHomogeneousSymbol U E V W m →ₗ[ℂ] HomogeneousSymbol X E V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      zero_covector := fun x => by simp
      contDiffOn_coefficient :=
        contDiffOn_smul_of_eventuallyEq_zero (U.isOpen.prod isOpen_ne)
          (fun _ _ => (hψ.comp contDiff_fst).contDiffAt) a.contDiffOn_coefficient
          fun p hp hpU => (continuous_fst.tendsto p).eventually
            (notMem_tsupport_iff_eventuallyEq.1 fun h => hpU ⟨hψU h, hp⟩)
      homogeneous := fun x ξ t ht => by
        simp only [a.homogeneous x ξ t ht]
        exact smul_comm (ψ x) (t ^ m) _ }
  map_add' a b := HomogeneousSymbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := HomogeneousSymbol.ext <| funext fun p => by simp [smul_comm (ψ p.1) c]

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem coefficient_extend (a : LocalHomogeneousSymbol U E V W m) (p : X × E) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p := (rfl)

/-- The cut-off extension of the restriction of a homogeneous symbol is its product with the
cutoff. -/
theorem coefficient_extend_restrict (a : HomogeneousSymbol X E V W m) (p : X × E) :
    (extend ψ hψ hψU (a.restrict U)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

@[simp]
theorem extend_castDegree {m' : ℝ} (h : m = m') (a : LocalHomogeneousSymbol U E V W m) :
    extend ψ hψ hψU (a.castDegree h) = (extend ψ hψ hψU a).castDegree h :=
  HomogeneousSymbol.ext <| funext fun p => by simp

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original homogeneous symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalHomogeneousSymbol U E V W m) : (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext_of_mem fun x hx ξ _ => by simp [hx, (hψ1 hx).trans (Pi.one_apply x)]

end Extend

section CutoffSymbol

variable {n : ℕ} {U U' : TopologicalSpace.Opens (CoordinateSpace n)}
  (χ : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m` on `U`, as a symbol of
order `m` on `U`. Near every compact set of positions it is the cut-off term of a cut-off extension
of `a`. -/
def cutoffSymbol :
    LocalHomogeneousSymbol U (CoordinateSpace n) V W m →ₗ[ℂ] LocalSymbol U V W m where
  toFun a := LocalSymbol.ofLocal (fun p => χ p.2 • a.coefficient p)
    (fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ]) fun K hKU hK => by
      obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hKU
      refine ⟨HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a), fun x hx => ?_⟩
      filter_upwards [hψ1 x hx] with y hy ξ
      simp [hy]
  map_add' a b := LocalSymbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := LocalSymbol.ext <| funext fun p => by simp [smul_comm (χ p.2) c]

@[simp]
theorem coefficient_cutoffSymbol (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p := by
  simp [cutoffSymbol]

@[simp]
theorem restrict_cutoffSymbol (h : U' ≤ U)
    (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m) :
    LocalSymbol.restrict h (cutoffSymbol χ a) = cutoffSymbol χ (restrict h a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-- The cut-off extension of a cut-off term is the cut-off term of the cut-off extension. -/
theorem extend_cutoffSymbol {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalHomogeneousSymbol U (CoordinateSpace n) V W m) :
    LocalSymbol.extend ψ hψ hψU (cutoffSymbol χ a) =
      HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a) :=
  Symbol.ext <| funext fun p => by simp [smul_comm (ψ p.1) (χ p.2)]

end CutoffSymbol

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {n : ℕ} {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Restriction commutes with taking the cut-off term. -/
@[simp]
theorem restrict_cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (cutoffSymbol χ a).restrict U = LocalHomogeneousSymbol.cutoffSymbol χ (a.restrict U) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

end HomogeneousSymbol

end TauCeti
