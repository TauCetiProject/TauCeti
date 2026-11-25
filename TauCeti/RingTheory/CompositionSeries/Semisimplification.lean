/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Multiplicity
public import TauCeti.RingTheory.SimpleModule.Basic

/-!
# The semisimplification of a module of finite length

Let `M` be a module of finite length over a ring `R`. For a composition series
`0 = M₀ < M₁ < ⋯ < Mₙ = M`, the product `∏ᵢ Mᵢ₊₁/Mᵢ` of its factors is semisimple, and by the
Jordan-Hölder theorem it contains every simple module as often as `M` does. Semisimple modules of
finite length are determined by these multiplicities
(`IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq`), so the product does not
depend on the series up to isomorphism. This is the **semisimplification** `M^ss` of `M`.

Applied to `R = k[Γ]` it is the semisimplification `V^ss` of a finite-dimensional representation
`V` of a monoid `Γ` over a field `k`: the direct sum of the Jordan-Hölder factors of `V`.

The semisimplification is computed by every composition series
(`nonempty_linearEquiv_seriesSemisimplification`), `M^ss ≅ M` exactly when `M` is semisimple
(`nonempty_linearEquiv_semisimplification_iff`), so `(M^ss)^ss ≅ M^ss`, and for a submodule `N`,
`M^ss ≅ N^ss × (M/N)^ss` (`nonempty_linearEquiv_semisimplification_prod_quotient`). A one-step
construction such as `soc(M) × M/soc(M)` is not semisimple in general (for a unipotent Jordan
block of size three), which is why the full composition series is used.

## Main definitions

* `TauCeti.seriesSemisimplification s`: the product of the factors `s i.succ / s i.castSucc` of a
  composition series `s`.
* `TauCeti.semisimplification R M`: the semisimplification of a module of finite length, the
  product of the factors of a chosen composition series from `⊥` to `⊤`.

## Main results

* `TauCeti.jordanHolderMultiplicity_seriesSemisimplification`: the product of the factors of a
  composition series of `M` has the multiplicities of `M`.
* `TauCeti.nonempty_linearEquiv_seriesSemisimplification`: any composition series computes
  `M^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_iff`: `M^ss ≅ M` iff `M` is semisimple.
* `TauCeti.nonempty_linearEquiv_semisimplification_semisimplification`: `(M^ss)^ss ≅ M^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_prod_quotient`: `M^ss ≅ N^ss × (M/N)^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_of_linearEquiv`: isomorphic modules have
  isomorphic semisimplifications.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### The factors of a composition series -/

/-- The product of the factors `s i.succ / s i.castSucc` of a composition series. It is
semisimple, each factor being simple by `TauCeti.isSimpleModule_subquotient`. -/
abbrev seriesSemisimplification (s : CompositionSeries (Submodule R M)) : Type v :=
  (i : Fin s.length) → ↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)

variable [IsNoetherian R M] [IsArtinian R M]

/-- The multiplicity of a simple module `S` in the factor of `s` at `i` is `1` if the factor is a
copy of `S` and `0` otherwise. -/
theorem jordanHolderMultiplicity_subquotient (s : CompositionSeries (Submodule R M))
    (i : Fin s.length) (S : Type w) [AddCommGroup S] [Module R S]
    [Decidable (IsCompositionFactorAt s i S)] :
    jordanHolderMultiplicity R (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))
      S = if IsCompositionFactorAt s i S then 1 else 0 := by
  split_ifs with h <;> rw [isCompositionFactorAt_iff] at h
  · exact jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S h.some
  · exact jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule S
      (not_nonempty_iff.1 h)

/-- **The factors of a composition series carry the multiplicities of the module**: the product
of the factors of a composition series of `M` from `⊥` to `⊤` contains every module as often
as `M` does. -/
theorem jordanHolderMultiplicity_seriesSemisimplification
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R (seriesSemisimplification s) S =
      jordanHolderMultiplicity R M S := by
  classical
  rw [jordanHolderMultiplicity_pi,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop,
    compositionMultiplicity_eq_sum_ite]
  exact Finset.sum_congr rfl fun i _ ↦ jordanHolderMultiplicity_subquotient s i S

variable (R M) in
/-- **The semisimplification `M^ss`** of a module of finite length: the product of the factors of a
composition series from `⊥` to `⊤`. By `TauCeti.nonempty_linearEquiv_seriesSemisimplification`
every such series gives an isomorphic module, so the choice below is immaterial. -/
noncomputable abbrev semisimplification : Type v :=
  seriesSemisimplification (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose

/-- The semisimplification has the Jordan-Hölder multiplicities of the module. -/
theorem jordanHolderMultiplicity_semisimplification (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R (semisimplification R M) S = jordanHolderMultiplicity R M S :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  jordanHolderMultiplicity_seriesSemisimplification _ h.1 h.2 S

/-- **The semisimplification does not depend on the composition series**: the product of the
factors of any composition series of `M` from `⊥` to `⊤` is isomorphic to `M^ss`. -/
theorem nonempty_linearEquiv_seriesSemisimplification (s : CompositionSeries (Submodule R M))
    (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    Nonempty (seriesSemisimplification s ≃ₗ[R] semisimplification R M) :=
  IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ by
    rw [jordanHolderMultiplicity_seriesSemisimplification s hbot htop,
      jordanHolderMultiplicity_semisimplification]

/-- A semisimple module of finite length is isomorphic to its semisimplification. -/
theorem nonempty_linearEquiv_semisimplification_of_isSemisimpleModule [IsSemisimpleModule R M] :
    Nonempty (semisimplification R M ≃ₗ[R] M) :=
  IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦
    jordanHolderMultiplicity_semisimplification S

/-- **`M^ss ≅ M` exactly when `M` is semisimple.** -/
theorem nonempty_linearEquiv_semisimplification_iff :
    Nonempty (semisimplification R M ≃ₗ[R] M) ↔ IsSemisimpleModule R M :=
  ⟨fun ⟨e⟩ ↦ IsSemisimpleModule.congr e.symm,
    fun _ ↦ nonempty_linearEquiv_semisimplification_of_isSemisimpleModule⟩

/-- The semisimplification is idempotent: `(M^ss)^ss ≅ M^ss`. -/
theorem nonempty_linearEquiv_semisimplification_semisimplification :
    Nonempty (semisimplification R (semisimplification R M) ≃ₗ[R] semisimplification R M) :=
  nonempty_linearEquiv_semisimplification_of_isSemisimpleModule

/-- Isomorphic modules of finite length have isomorphic semisimplifications. -/
theorem nonempty_linearEquiv_semisimplification_of_linearEquiv {N : Type w} [AddCommGroup N]
    [Module R N] [IsNoetherian R N] [IsArtinian R N] (e : M ≃ₗ[R] N) :
    Nonempty (semisimplification R M ≃ₗ[R] semisimplification R N) :=
  IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ by
    rw [jordanHolderMultiplicity_semisimplification, jordanHolderMultiplicity_semisimplification,
      jordanHolderMultiplicity_eq_of_linearEquiv e]

/-- **Semisimplification is additive in short exact sequences**: for a submodule `N` of `M`,
`M^ss ≅ N^ss × (M/N)^ss`. -/
theorem nonempty_linearEquiv_semisimplification_prod_quotient (N : Submodule R M) :
    Nonempty (semisimplification R M ≃ₗ[R]
      semisimplification R N × semisimplification R (M ⧸ N)) :=
  IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ by
    rw [jordanHolderMultiplicity_prod, jordanHolderMultiplicity_semisimplification,
      jordanHolderMultiplicity_semisimplification, jordanHolderMultiplicity_semisimplification,
      jordanHolderMultiplicity_eq_submodule_add_quotient N]

/-- The semisimplification of the zero module is zero. -/
instance subsingleton_semisimplification [Subsingleton M] :
    Subsingleton (semisimplification R M) := by
  have h := compositionSeries_length_eq_zero_of_subsingleton
    (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose
  refine ⟨fun x y ↦ funext fun i ↦ ?_⟩
  exact absurd i.isLt (by omega)

end TauCeti
