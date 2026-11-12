/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import TauCeti.Topology.ContinuousMap.Clopen

/-!
# Restriction of measures to clopen subsets

For a compact space `X`, a clopen subset `s` and a normed commutative ring `R`, a measure on `X`
restricts to a measure on `s` by integrating extensions by zero of test functions on `s`:
`restrictClopen s μ f = μ (zeroExtendClopen R s f)`. In the other direction, pushforward along the
inclusion `s ↪ X` (Mathlib's `AbstractMeasure.map (ContinuousMap.subtypeVal s)`) extends a measure
on `s` to `X`. Restriction is a left inverse of this extension, and extending the restriction of
`μ` integrates `f` to `μ (χ_s * f)`, where `χ_s` is the characteristic function of `s`.

Consequently a measure on `X` comes from a (necessarily unique) measure on `s` exactly when it
kills every test function vanishing on `s`, and the measures on `X` split as the product of the
measures on `s` and on its complement. These operations are what later restrict measures on
`ℤ_p` to residue classes and to the units.

All statements allow measures with values in a topological `R`-module `E`. No topology or norm is
installed on the measure carrier.

## Main definitions

* `AbstractMeasure.restrictClopen s`: the `R`-linear restriction `D(X, R) → D(s, R)`.
* `AbstractMeasure.clopenDecomposition s`: the `R`-linear equivalence
  `D(X, R) ≃ D(s, R) × D(sᶜ, R)` given by the two restrictions.

## Main results

* `AbstractMeasure.restrictClopen_map_subtype`: restriction after extension is the identity.
* `AbstractMeasure.map_subtype_restrictClopen_apply`: extension after restriction is
  multiplication of test functions by the characteristic function.
* `AbstractMeasure.restrictClopen_map_preimage`: restriction commutes with pushforward along `φ`
  when the source clopen is the preimage of the target clopen.
* `AbstractMeasure.existsUnique_map_subtype_iff`: a measure on `X` is the extension of a
  unique measure on `s` if and only if it kills every test function vanishing on `s`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.2,
  Definitions 3.7–3.8, and §3.5.3, Remark 3.31.
-/

public section

open TopologicalSpace ContinuousMap

namespace AbstractMeasure

variable {X Y R E : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
  [CompactSpace Y] [NormedCommRing R] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module R E] [ContinuousSMul R E]

/-- The restriction of a measure on `X` to a clopen subset `s`: it integrates a test function on
`s` against the original measure after extending it by zero. -/
noncomputable def restrictClopen (s : Clopens X) :
    AbstractMeasure X R E →ₗ[R] AbstractMeasure s R E where
  toFun μ := μ ∘L zeroExtendClopen R s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The restriction of `μ` integrates `f` to the integral of its extension by zero. -/
@[simp]
theorem restrictClopen_apply (s : Clopens X) (μ : AbstractMeasure X R E) (f : C(s, R)) :
    restrictClopen s μ f = μ (zeroExtendClopen R s f) :=
  (rfl)

/-- Restricting the extension of a measure on `s` recovers that measure. -/
@[simp]
theorem restrictClopen_map_subtype (s : Clopens X) (ν : AbstractMeasure s R E) :
    restrictClopen s (map (X := s) (subtypeVal (s : Set X)) ν) = ν := by
  ext f
  rw [restrictClopen_apply, map_apply]
  congr 1
  ext x
  rw [comp_apply, subtypeVal_apply]
  exact zeroExtendClopen_apply_mem s f x.2

/-- Extension of measures from a clopen subset is injective. -/
theorem map_subtype_injective (s : Clopens X) :
    Function.Injective (map (subtypeVal (s : Set X)) : AbstractMeasure s R E → _) :=
  Function.LeftInverse.injective (restrictClopen_map_subtype (R := R) (E := E) s)

/-- A measure supported on a clopen subset restricts to zero on a disjoint clopen subset. -/
theorem restrictClopen_map_subtype_of_disjoint {s t : Clopens X} (hst : Disjoint s t)
    (ν : AbstractMeasure t R E) : restrictClopen s (map (subtypeVal (t : Set X)) ν) = 0 := by
  refine toCLMEquiv.injective (ContinuousLinearMap.ext fun f ↦ ?_)
  have hzero : (zeroExtendClopen R s f).comp (subtypeVal (t : Set X)) = 0 := by
    ext x
    have hx : (x : X) ∉ s := fun hx ↦ (Clopens.coe_disjoint.2 hst).notMem_of_mem_right x.2 hx
    rw [comp_apply, subtypeVal_apply, zeroExtendClopen_apply_not_mem s f hx,
      ContinuousMap.zero_apply]
  rw [map_zero, _root_.zero_apply, coe_toCLMEquiv, restrictClopen_apply, map_apply,
    hzero, map_zero]

/-- Extending the restriction of `μ` to `s` integrates `f` to `μ (χ_s * f)`. -/
theorem map_subtype_restrictClopen_apply (s : Clopens X) (μ : AbstractMeasure X R E)
    (f : C(X, R)) :
    map (subtypeVal (s : Set X)) (restrictClopen s μ) f =
      μ ((LocallyConstant.charFn R s.isClopen : C(X, R)) * f) := by
  have hres : f.comp (subtypeVal (s : Set X)) = f.restrict s := by
    ext x
    rw [comp_apply, subtypeVal_apply, restrict_apply]
  rw [map_apply, restrictClopen_apply, hres, zeroExtendClopen_restrict]

/-- The restriction of a Dirac measure at a point of `s` is the Dirac measure at that point. -/
@[simp]
theorem restrictClopen_dirac_mem (s : Clopens X) {x : X} (hx : x ∈ s) :
    restrictClopen s (dirac R x) = dirac R ⟨x, hx⟩ := by
  ext f
  simp [hx]

/-- The restriction of a Dirac measure at a point outside `s` vanishes. -/
@[simp]
theorem restrictClopen_dirac_not_mem (s : Clopens X) {x : X} (hx : x ∉ s) :
    restrictClopen s (dirac R x) = 0 := by
  refine toCLMEquiv.injective (ContinuousLinearMap.ext fun f ↦ ?_)
  simp [hx]

/-- Restriction commutes with pushforward along `φ` when the source clopen is the preimage of the
target clopen. -/
theorem restrictClopen_map_preimage (φ : C(X, Y)) {s : Clopens X} {t : Clopens Y}
    (hst : (s : Set X) = φ ⁻¹' t) (μ : AbstractMeasure X R E) :
    restrictClopen t (map φ μ) =
      map ((φ.restrictPreimage t).comp (inclusion hst.subset)) (restrictClopen s μ) := by
  ext f
  rw [restrictClopen_apply, map_apply, map_apply, restrictClopen_apply]
  congr 1
  ext x
  by_cases hx : x ∈ s
  · have hφx : φ x ∈ t := (Set.ext_iff.1 hst x).1 hx
    rw [comp_apply, zeroExtendClopen_apply_mem t f hφx, zeroExtendClopen_apply_mem s _ hx]
    -- Both sides evaluate `f` at the point `φ x` of `t`; the subtype on the right is that of
    -- `restrictPreimage`, which simp cannot match against the clopen subtype `⟨x, hx⟩ : s`.
    rfl
  · have hφx : φ x ∉ t := fun h ↦ hx ((Set.ext_iff.1 hst x).2 h)
    rw [comp_apply, zeroExtendClopen_apply_not_mem t f hφx, zeroExtendClopen_apply_not_mem s _ hx]

/-- A measure is the sum of the extensions of its restrictions to `s` and to `sᶜ`. -/
theorem map_subtype_restrictClopen_add_compl (s : Clopens X) (μ : AbstractMeasure X R E) :
    map (subtypeVal (s : Set X)) (restrictClopen s μ) +
      map (subtypeVal ((sᶜ : Clopens X) : Set X)) (restrictClopen sᶜ μ) = μ := by
  ext f
  have hres (t : Clopens X) : f.comp (subtypeVal (t : Set X)) = f.restrict t := by
    ext x
    rw [comp_apply, subtypeVal_apply, restrict_apply]
  rw [_root_.add_apply, map_apply, map_apply, restrictClopen_apply, restrictClopen_apply, hres,
    hres, ← map_add, zeroExtendClopen_restrict_add_compl]

/-- Extending the restriction of `μ` to `s` recovers `μ` exactly when `μ` kills every test
function vanishing on `s`. -/
theorem map_subtype_restrictClopen_eq_self_iff (s : Clopens X) (μ : AbstractMeasure X R E) :
    map (subtypeVal (s : Set X)) (restrictClopen s μ) = μ ↔
      ∀ f : C(X, R), (∀ x : s, f x = 0) → μ f = 0 := by
  constructor
  · intro hμ f hf
    have hres : f.comp (subtypeVal (s : Set X)) = 0 := by
      ext x
      rw [comp_apply, subtypeVal_apply, ContinuousMap.zero_apply]
      exact hf x
    rw [← hμ, map_apply, hres, map_zero]
  · intro hμ
    have hcompl : map (subtypeVal ((sᶜ : Clopens X) : Set X)) (restrictClopen sᶜ μ) = 0 := by
      refine toCLMEquiv.injective (ContinuousLinearMap.ext fun f ↦ ?_)
      rw [map_zero, _root_.zero_apply, coe_toCLMEquiv, map_apply, restrictClopen_apply]
      refine hμ _ fun x ↦ zeroExtendClopen_apply_not_mem _ _ ?_
      simp [← SetLike.mem_coe]
    have hsum := map_subtype_restrictClopen_add_compl s μ
    rwa [hcompl, add_zero] at hsum

/-- A measure that is the extension of a measure on `s` is the extension of its restriction. -/
theorem eq_restrictClopen_of_map_subtype_eq {s : Clopens X} {μ : AbstractMeasure X R E}
    {ν : AbstractMeasure s R E} (h : map (subtypeVal (s : Set X)) ν = μ) :
    ν = restrictClopen s μ := by
  rw [← h, restrictClopen_map_subtype]

/-- A measure on `X` is the extension of a unique measure on the clopen subset `s` if and only if
it kills every test function vanishing on `s`; the measure on `s` is then `restrictClopen s μ`
(`eq_restrictClopen_of_map_subtype_eq`). -/
theorem existsUnique_map_subtype_iff (s : Clopens X) (μ : AbstractMeasure X R E) :
    (∃! ν : AbstractMeasure s R E, map (subtypeVal (s : Set X)) ν = μ) ↔
      ∀ f : C(X, R), (∀ x : s, f x = 0) → μ f = 0 := by
  rw [← map_subtype_restrictClopen_eq_self_iff]
  constructor
  · rintro ⟨ν, hν, -⟩
    rw [← eq_restrictClopen_of_map_subtype_eq hν, hν]
  · intro h
    exact ⟨restrictClopen s μ, h, fun ν hν ↦ eq_restrictClopen_of_map_subtype_eq hν⟩

/-- The decomposition of measures on `X` into their restrictions to a clopen subset `s` and to its
complement. The inverse recombines a pair by adding the two extensions. -/
noncomputable def clopenDecomposition (s : Clopens X) :
    AbstractMeasure X R E ≃ₗ[R] AbstractMeasure s R E × AbstractMeasure ↥sᶜ R E :=
  LinearEquiv.ofLinearMap ((restrictClopen s).prod (restrictClopen sᶜ))
    ((map (subtypeVal (s : Set X))).coprod (map (subtypeVal ((sᶜ : Clopens X) : Set X))))
    (LinearMap.ext fun ν ↦ by
      -- `Clopens.coe_compl` would turn `↑sᶜ` into `(↑s)ᶜ`, so that the restriction lemmas for the
      -- clopen `sᶜ` no longer match.
      simp [-Clopens.coe_compl, restrictClopen_map_subtype_of_disjoint disjoint_compl_right,
        restrictClopen_map_subtype_of_disjoint disjoint_compl_left])
    (LinearMap.ext (map_subtype_restrictClopen_add_compl s))

/-- The two components of the decomposition are the restrictions to `s` and to `sᶜ`. -/
@[simp]
theorem clopenDecomposition_apply (s : Clopens X) (μ : AbstractMeasure X R E) :
    clopenDecomposition s μ = (restrictClopen s μ, restrictClopen sᶜ μ) :=
  (rfl)

/-- The inverse decomposition adds the extensions of the two components. -/
@[simp]
theorem clopenDecomposition_symm_apply (s : Clopens X)
    (ν : AbstractMeasure s R E × AbstractMeasure ↥sᶜ R E) :
    (clopenDecomposition s).symm ν =
      map (subtypeVal (s : Set X)) ν.1 + map (subtypeVal ((sᶜ : Clopens X) : Set X)) ν.2 :=
  (rfl)

section Examples

/-- The clopen `{0}` of the two-point space. -/
private def zeroClopen : Clopens (Fin 2) := ⟨{0}, isClopen_discrete {0}⟩

private theorem zero_mem_zeroClopen : (0 : Fin 2) ∈ zeroClopen := rfl

private theorem one_not_mem_zeroClopen : (1 : Fin 2) ∉ zeroClopen := by simp [zeroClopen]

private theorem one_mem_compl_zeroClopen : (1 : Fin 2) ∈ zeroClopenᶜ := one_not_mem_zeroClopen

private theorem zero_not_mem_compl_zeroClopen : (0 : Fin 2) ∉ zeroClopenᶜ :=
  not_not_intro zero_mem_zeroClopen

-- Restricting `2δ₀ - 3δ₁` to `{0}` gives `2δ₀`.
example :
    restrictClopen zeroClopen (2 • dirac ℤ (0 : Fin 2) - 3 • dirac ℤ 1) =
      2 • dirac ℤ ⟨0, zero_mem_zeroClopen⟩ := by
  simp [restrictClopen_dirac_mem _ zero_mem_zeroClopen,
    restrictClopen_dirac_not_mem _ one_not_mem_zeroClopen]

-- Restricting `δ₁` to `{0}` gives zero.
example : restrictClopen zeroClopen (dirac ℤ (1 : Fin 2)) = 0 :=
  restrictClopen_dirac_not_mem _ one_not_mem_zeroClopen

-- Every measure restricts to zero on the empty clopen.
example (μ : D(Fin 2, ℤ)) : restrictClopen (⊥ : Clopens (Fin 2)) μ = 0 := by
  refine toCLMEquiv.injective (ContinuousLinearMap.ext fun f ↦ ?_)
  have hf : f = 0 := ContinuousMap.ext fun x ↦ (Set.notMem_empty (x : Fin 2) x.2).elim
  simp [hf]

-- The decomposition of `2δ₀ - 3δ₁` along `{0}` is `(2δ₀, -3δ₁)`.
example :
    clopenDecomposition zeroClopen (2 • dirac ℤ (0 : Fin 2) - 3 • dirac ℤ 1) =
      (2 • dirac ℤ ⟨0, zero_mem_zeroClopen⟩, -(3 • dirac ℤ ⟨1, one_mem_compl_zeroClopen⟩)) := by
  simp [restrictClopen_dirac_mem _ zero_mem_zeroClopen,
    restrictClopen_dirac_not_mem _ one_not_mem_zeroClopen,
    restrictClopen_dirac_mem _ one_mem_compl_zeroClopen,
    restrictClopen_dirac_not_mem _ zero_not_mem_compl_zeroClopen]

-- Recombining the unit Dirac measures on `{0}` and `{1}` gives `δ₀ + δ₁`.
example :
    (clopenDecomposition zeroClopen).symm
        (dirac ℤ ⟨0, zero_mem_zeroClopen⟩, dirac ℤ ⟨1, one_mem_compl_zeroClopen⟩) =
      dirac ℤ (0 : Fin 2) + dirac ℤ 1 := by
  rw [clopenDecomposition_symm_apply, map_dirac, map_dirac, subtypeVal_apply, subtypeVal_apply]

end Examples

end AbstractMeasure
