/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Cutoff

/-!
# Homogeneous symbols on an open set of positions

For an open set `U ⊆ ℝⁿ`, a homogeneous symbol of degree `m` on `U` is a map `a(x, ξ)`, smooth on
`U × (ℝⁿ \ {0})` and positively homogeneous of degree `m` in the frequency:
`a(x, t ξ) = t ^ m a(x, ξ)` for `t > 0`. These are the terms of the classical expansion of a symbol
on `U` (`TauCeti/Analysis/Pseudodifferential/LocalSymbol/Classical.lean`), as they arise in a
chart of a manifold. As for `TauCeti.HomogeneousSymbol` and `TauCeti.LocalSymbol`, values where
the symbol is not smooth are fixed by a convention: the coefficient is `0` at the zero frequency and
at every position outside `U`. So a homogeneous symbol on `U` is determined by its values on
`U × (ℝⁿ \ {0})` (`TauCeti.LocalHomogeneousSymbol.ext_of_mem`).

This file defines the class `TauCeti.LocalHomogeneousSymbol U V W m`, shows that it is a complex
vector space, and compares it with the homogeneous symbols on `ℝⁿ`:

* `TauCeti.HomogeneousSymbol.restrictTopEquiv`: the homogeneous symbols on `⊤` are the homogeneous
  symbols on `ℝⁿ`;
* `TauCeti.HomogeneousSymbol.restrict`: a homogeneous symbol on `ℝⁿ` restricts to `U`;
* `TauCeti.LocalHomogeneousSymbol.restrict`: a homogeneous symbol on `U` restricts to every smaller
  open set, and restrictions compose;
* `TauCeti.LocalHomogeneousSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `ℝⁿ` contained in `U`, a homogeneous symbol on `U` extends by zero
  to a homogeneous symbol on `ℝⁿ`; restricting the extension to an open set on which `ψ = 1`
  recovers the restriction of the original symbol
  (`TauCeti.LocalHomogeneousSymbol.restrict_extend_of_eqOn_one`);
* `TauCeti.LocalHomogeneousSymbol.cutoffSymbol χ a`: for a frequency cutoff `χ`, the cut-off term
  `χ(ξ) a(x, ξ)` is a symbol of order `m` on `U`. It commutes with restriction
  (`TauCeti.HomogeneousSymbol.restrict_cutoffSymbol`) and with extension
  (`TauCeti.LocalHomogeneousSymbol.extend_cutoffSymbol`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace TauCeti

variable {n : ℕ}

/-- A homogeneous symbol of degree `m` on `U × ℝⁿ`, for an open set `U ⊆ ℝⁿ` of positions, with
values in `V →L[ℂ] W`: a map `a(x, ξ)`, smooth on `U × (ℝⁿ \ {0})`, with
`a(x, t ξ) = t ^ m a(x, ξ)` for every `t > 0`. By convention the coefficient vanishes at the zero
frequency and at positions outside `U`. -/
@[ext]
structure LocalHomogeneousSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The value `a(x, ξ)` at the position `x` and the frequency `ξ`, set to `0` at positions
  outside `U` and at `ξ = 0`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  coefficient_of_notMem : ∀ x ∉ U, ∀ ξ, coefficient (x, ξ) = 0
  zero_covector : ∀ x, coefficient (x, 0) = 0
  contDiffOn_coefficient :
    ContDiffOn ℝ ∞ coefficient ((U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0})
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] LocalHomogeneousSymbol.zero_covector

namespace LocalHomogeneousSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : LocalHomogeneousSymbol U V W m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => LocalHomogeneousSymbol.ext h

/-- A homogeneous symbol on `U` is determined by its values at the positions of `U` and the nonzero
frequencies. -/
theorem ext_of_mem {a b : LocalHomogeneousSymbol U V W m}
    (h : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext ⟨x, ξ⟩
  by_cases hx : x ∈ U
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · exact h x hx ξ hξ
  · rw [a.coefficient_of_notMem x hx ξ, b.coefficient_of_notMem x hx ξ]

section mk'

/-- The homogeneous symbol of degree `m` on `U` defined by a function `f` that is smooth on
`U × (ℝⁿ \ {0})` and positively homogeneous of degree `m` there; its value at positions outside `U`
and at the zero frequency is set to zero, whatever `f` does there. -/
def mk' (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiffOn ℝ ∞ f ((U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0}))
    (hhom : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) :
    LocalHomogeneousSymbol U V W m where
  coefficient := ((U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0}).indicator f
  coefficient_of_notMem x hx ξ := indicator_of_notMem (by simp [hx]) _
  zero_covector x := indicator_of_notMem (by simp) _
  contDiffOn_coefficient := hf.congr fun _ hp => indicator_of_mem hp _
  homogeneous x ξ t ht := by
    by_cases hx : x ∈ U
    · rcases eq_or_ne ξ 0 with rfl | hξ
      · simp
      · rw [indicator_of_mem (mk_mem_prod hx (smul_ne_zero ht.ne' hξ)),
          indicator_of_mem (mk_mem_prod hx hξ), hhom x hx ξ hξ t ht]
    · simp [hx]

variable (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
  (hf : ContDiffOn ℝ ∞ f ((U : Set (CoordinateSpace n)) ×ˢ {ξ | ξ ≠ 0}))
  (hhom : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ))

@[simp]
theorem coefficient_mk'_of_mem {x : CoordinateSpace n} (hx : x ∈ U) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) : (mk' f hf hhom).coefficient (x, ξ) = f (x, ξ) :=
  indicator_of_mem (mk_mem_prod hx hξ) _

@[simp]
theorem coefficient_mk'_of_notMem {x : CoordinateSpace n} (hx : x ∉ U) (ξ : CoordinateSpace n) :
    (mk' f hf hhom).coefficient (x, ξ) = 0 :=
  (mk' f hf hhom).coefficient_of_notMem x hx ξ

/-- Rebuilding a homogeneous symbol on `U` from its own coefficient gives back the symbol. -/
@[simp]
theorem mk'_coefficient (a : LocalHomogeneousSymbol U V W m) :
    mk' a.coefficient a.contDiffOn_coefficient (fun x _ ξ _ t ht => a.homogeneous x ξ t ht) = a :=
  ext_of_mem fun _ hx _ hξ => coefficient_mk'_of_mem _ _ _ hx hξ

end mk'

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
        simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht] }

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
theorem coefficient_sum {ι : Type*} (s : Finset ι) (a : ι → LocalHomogeneousSymbol U V W m) :
    (∑ i ∈ s, a i).coefficient = ∑ i ∈ s, (a i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) a s

end Module

section CastDegree

variable {m' : ℝ}

/-- Transport a homogeneous symbol on `U` along an equality of degrees, for instance to identify
the degree `m - (0 : ℕ)` of a leading term with `m`. -/
def castDegree (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    LocalHomogeneousSymbol U V W m' where
  coefficient := a.coefficient
  coefficient_of_notMem := a.coefficient_of_notMem
  zero_covector := a.zero_covector
  contDiffOn_coefficient := a.contDiffOn_coefficient
  homogeneous := h ▸ a.homogeneous

@[simp]
theorem coefficient_castDegree (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    (a.castDegree h).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem castDegree_rfl (a : LocalHomogeneousSymbol U V W m) : a.castDegree rfl = a :=
  (rfl)

@[simp]
theorem castDegree_castDegree {m'' : ℝ} (h : m = m') (h' : m' = m'')
    (a : LocalHomogeneousSymbol U V W m) :
    (a.castDegree h).castDegree h' = a.castDegree (h.trans h') :=
  (rfl)

@[simp]
theorem castDegree_zero (h : m = m') :
    (0 : LocalHomogeneousSymbol U V W m).castDegree h = 0 :=
  (rfl)

@[simp]
theorem castDegree_add (h : m = m') (a b : LocalHomogeneousSymbol U V W m) :
    (a + b).castDegree h = a.castDegree h + b.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_smul (h : m = m') (c : ℂ) (a : LocalHomogeneousSymbol U V W m) :
    (c • a).castDegree h = c • a.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_neg (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    (-a).castDegree h = -a.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_sub (h : m = m') (a b : LocalHomogeneousSymbol U V W m) :
    (a - b).castDegree h = a.castDegree h - b.castDegree h :=
  (rfl)

end CastDegree

section Restrict

/-- The restriction of a homogeneous symbol on `U` to a smaller open set `U'`, extended by zero at
positions outside `U'`. -/
def restrict (h : U' ≤ U) :
    LocalHomogeneousSymbol U V W m →ₗ[ℂ] LocalHomogeneousSymbol U' V W m where
  toFun a :=
    { coefficient := ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient
      coefficient_of_notMem := fun x hx ξ => indicator_of_notMem (by simp [hx]) _
      zero_covector := fun x => by simp
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

theorem coefficient_restrict (h : U' ≤ U) (a : LocalHomogeneousSymbol U V W m) :
    (restrict h a).coefficient = ((U' : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient :=
  (rfl)

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
  ext_of_mem fun _ hx ξ _ => coefficient_restrict_of_mem le_rfl a hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalHomogeneousSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext_of_mem fun x hx ξ _ => by
    rw [coefficient_restrict_of_mem _ _ hx, coefficient_restrict_of_mem _ _ (h' hx),
      coefficient_restrict_of_mem _ _ hx]

@[simp]
theorem restrict_castDegree {m' : ℝ} (h : U' ≤ U) (hm : m = m')
    (a : LocalHomogeneousSymbol U V W m) :
    restrict h (a.castDegree hm) = (restrict h a).castDegree hm :=
  (rfl)

end Restrict

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `ℝⁿ`, the homogeneous symbols on an open set are exactly the homogeneous symbols
on `ℝⁿ × ℝⁿ`: a homogeneous symbol on `ℝⁿ × ℝⁿ` is a homogeneous symbol on `⊤` with the same
coefficient, and this is a linear equivalence. -/
def restrictTopEquiv : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m ≃ₗ[ℂ]
    LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { coefficient := a.coefficient
      coefficient_of_notMem := fun x hx => absurd (TopologicalSpace.Opens.mem_top x) hx
      zero_covector := a.zero_covector
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp => (mem_prod.1 hp).2
      homogeneous := a.homogeneous }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a :=
    { coefficient := a.coefficient
      zero_covector := a.zero_covector
      contDiffOn_coefficient := a.contDiffOn_coefficient.mono fun _ hp =>
        mk_mem_prod (TopologicalSpace.Opens.mem_top _) hp
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

@[simp]
theorem restrictTopEquiv_castDegree {m' : ℝ} (h : m = m')
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    restrictTopEquiv (a.castDegree h) = (restrictTopEquiv a).castDegree h :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem restrictTopEquiv_symm_castDegree {m' : ℝ} (h : m = m')
    (a : LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    restrictTopEquiv.symm (a.castDegree h) =
      (restrictTopEquiv.symm a :
        HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m).castDegree h :=
  HomogeneousSymbol.ext (by simp)

variable (U) in
/-- The restriction of a homogeneous symbol on `ℝⁿ` to the open set `U` of positions, extended by
zero at positions outside `U`: the restriction from `⊤` to `U` of the corresponding homogeneous
symbol on `⊤`. -/
def restrict : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ]
    LocalHomogeneousSymbol U V W m :=
  LocalHomogeneousSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

theorem coefficient_restrict (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (restrict U a).coefficient = ((U : Set (CoordinateSpace n)) ×ˢ univ).indicator a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_restrict_of_mem
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x : CoordinateSpace n}
    (hx : x ∈ U) (ξ : CoordinateSpace n) :
    (restrict U a).coefficient (x, ξ) = a.coefficient (x, ξ) :=
  LocalHomogeneousSymbol.coefficient_restrict_of_mem le_top (restrictTopEquiv a) hx ξ

@[simp]
theorem coefficient_restrict_of_notMem
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x : CoordinateSpace n}
    (hx : x ∉ U) (ξ : CoordinateSpace n) : (restrict U a).coefficient (x, ξ) = 0 :=
  (restrict U a).coefficient_of_notMem x hx ξ

@[simp]
theorem restrict_restrict (h : U' ≤ U)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    LocalHomogeneousSymbol.restrict h (restrict U a) = restrict U' a :=
  LocalHomogeneousSymbol.restrict_restrict le_top h (restrictTopEquiv a)

/-- Restricting a homogeneous symbol to all of `ℝⁿ` gives the corresponding homogeneous symbol on
`⊤`. -/
@[simp]
theorem restrict_top (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    restrict ⊤ a = restrictTopEquiv a :=
  LocalHomogeneousSymbol.restrict_self (restrictTopEquiv a)

/-- Restricting the homogeneous symbol on `⊤` corresponding to a homogeneous symbol on `ℝⁿ` gives
the restriction of that homogeneous symbol. -/
@[simp]
theorem restrict_restrictTopEquiv (h : U ≤ ⊤)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    LocalHomogeneousSymbol.restrict h (restrictTopEquiv a) = restrict U a :=
  (rfl)

@[simp]
theorem restrict_castDegree {m' : ℝ} (h : m = m')
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    restrict U (a.castDegree h) = (restrict U a).castDegree h :=
  LocalHomogeneousSymbol.ext (by simp [coefficient_restrict])

end HomogeneousSymbol

namespace LocalHomogeneousSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

section Extend

variable {ψ : CoordinateSpace n → ℝ}

/-- The extension by zero of the cut-off homogeneous symbol `ψ(x) a(x, ξ)`, for a smooth cutoff
`ψ` whose support is a closed subset of `ℝⁿ` contained in `U`: a homogeneous symbol on `ℝⁿ` of the
same degree. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalHomogeneousSymbol U V W m →ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m where
  toFun a :=
    { coefficient := fun p => ψ p.1 • a.coefficient p
      zero_covector := fun x => by simp
      contDiffOn_coefficient := contDiffOn_smul_of_eventuallyEq_zero (U.isOpen.prod isOpen_ne)
        (fun _ _ => (hψ.comp contDiff_fst).contDiffAt) a.contDiffOn_coefficient fun p hp hpU =>
          (continuous_fst.tendsto p).eventually
            (notMem_tsupport_iff_eventuallyEq.1 fun h => hpU ⟨hψU h, hp⟩)
      homogeneous := fun x ξ t ht => by simp [a.homogeneous x ξ t ht, smul_comm (ψ x)] }
  map_add' a b := HomogeneousSymbol.ext (funext fun p => by simp [smul_add])
  map_smul' c a := HomogeneousSymbol.ext (funext fun p => by simp [smul_comm (ψ p.1) c])

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

@[simp]
theorem coefficient_extend (a : LocalHomogeneousSymbol U V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU a).coefficient p = ψ p.1 • a.coefficient p := (rfl)

@[simp]
theorem extend_castDegree {m' : ℝ} (h : m = m') (a : LocalHomogeneousSymbol U V W m) :
    extend ψ hψ hψU (a.castDegree h) = (extend ψ hψ hψU a).castDegree h :=
  HomogeneousSymbol.ext (funext fun p => by simp)

/-- The cut-off extension of the restriction of a homogeneous symbol on `ℝⁿ` is its product with
the cutoff. -/
theorem coefficient_extend_restrict
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (extend ψ hψ hψU (HomogeneousSymbol.restrict U a)).coefficient p = ψ p.1 • a.coefficient p := by
  obtain ⟨x, ξ⟩ := p
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψU h)]

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original homogeneous symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalHomogeneousSymbol U V W m) :
    HomogeneousSymbol.restrict U' (extend ψ hψ hψU a) = restrict h a :=
  ext_of_mem fun x hx ξ _ => by simp [hx, (hψ1 hx).trans (Pi.one_apply x)]

/-- For a cutoff supported in a smaller open set `U' ⊆ U`, extending the restriction to `U'` is
extending the original homogeneous symbol. -/
@[simp]
theorem extend_restrict (h : U' ≤ U) (hψU' : tsupport ψ ⊆ U')
    (a : LocalHomogeneousSymbol U V W m) :
    extend ψ hψ hψU' (restrict h a) = extend ψ hψ (hψU'.trans h) a :=
  HomogeneousSymbol.ext (funext fun ⟨x, ξ⟩ => by
    by_cases hx : x ∈ U'
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport fun hy => hx (hψU' hy)])

end Extend

section CutoffSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m` on `U`, as a symbol
of order `m` on `U`. -/
def cutoffSymbol : LocalHomogeneousSymbol U V W m →ₗ[ℂ] LocalSymbol U V W m where
  toFun a := LocalSymbol.ofEventuallyEq (fun p => χ p.2 • a.coefficient p)
    (fun x hx ξ => by simp [a.coefficient_of_notMem x hx ξ]) fun x hx => by
      obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one
        U.isOpen (singleton_subset_iff.2 hx)
      refine ⟨HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a), ?_⟩
      filter_upwards [hψ1 x rfl] with y hy η
      simp [hy]
  map_add' a b := LocalSymbol.ext (funext fun p => by simp [smul_add])
  map_smul' c a := LocalSymbol.ext (funext fun p => by simp [smul_comm (χ p.2) c])

@[simp]
theorem coefficient_cutoffSymbol (a : LocalHomogeneousSymbol U V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  congrFun (LocalSymbol.coefficient_ofEventuallyEq _ _ _) p

/-- The cut-off term commutes with restriction to a smaller open set. -/
@[simp]
theorem restrict_cutoffSymbol (h : U' ≤ U) (a : LocalHomogeneousSymbol U V W m) :
    LocalSymbol.restrict h (cutoffSymbol χ a) = cutoffSymbol χ (restrict h a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-- The cut-off term commutes with the cut-off extension to `ℝⁿ`. -/
@[simp]
theorem extend_cutoffSymbol {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalHomogeneousSymbol U V W m) :
    LocalSymbol.extend ψ hψ hψU (cutoffSymbol χ a) =
      HomogeneousSymbol.cutoffSymbol χ (extend ψ hψ hψU a) :=
  Symbol.ext (funext fun p => by simp [smul_comm (ψ p.1)])

end CutoffSymbol

end LocalHomogeneousSymbol

/-- The cut-off term commutes with restriction from `ℝⁿ` to an open set. -/
@[simp]
theorem HomogeneousSymbol.restrict_cutoffSymbol {U : TopologicalSpace.Opens (CoordinateSpace n)}
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {m : ℝ} (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    Symbol.restrict U (cutoffSymbol χ a) =
      LocalHomogeneousSymbol.cutoffSymbol χ (HomogeneousSymbol.restrict U a) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

/-- The cut-off term commutes with the identification of homogeneous symbols on `ℝⁿ` with
homogeneous symbols on `⊤`. -/
@[simp]
theorem HomogeneousSymbol.restrictTopEquiv_cutoffSymbol {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
    (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    Symbol.restrictTopEquiv (cutoffSymbol χ a) =
      LocalHomogeneousSymbol.cutoffSymbol χ (HomogeneousSymbol.restrictTopEquiv a) :=
  LocalSymbol.ext (funext fun p => by simp)

/-- The cut-off term commutes with the identification of homogeneous symbols on `⊤` with
homogeneous symbols on `ℝⁿ`. -/
@[simp]
theorem HomogeneousSymbol.restrictTopEquiv_symm_cutoffSymbol {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
    (χ : FrequencyCutoff (CoordinateSpace n))
    (a : LocalHomogeneousSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    Symbol.restrictTopEquiv.symm (LocalHomogeneousSymbol.cutoffSymbol χ a) =
      cutoffSymbol χ (HomogeneousSymbol.restrictTopEquiv.symm a) :=
  Symbol.ext (funext fun p => by simp)

end TauCeti
