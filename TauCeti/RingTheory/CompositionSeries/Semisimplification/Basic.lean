/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteDimensional.ScalarTower
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
(`nonempty_linearEquiv_semisimplification_iff`), so `(M^ss)^ss ≅ M^ss`, and for a short exact
sequence `0 → A → M → B → 0`, `M^ss ≅ A^ss × B^ss`
(`nonempty_linearEquiv_semisimplification_prod_of_exact`). A one-step
construction such as `soc(M) × M/soc(M)` is not semisimple in general (for a unipotent Jordan
block of size three), which is why the full composition series is used.

## Main definitions

* `TauCeti.seriesSemisimplification s`: the product of the factors `s i.succ / s i.castSucc` of a
  composition series `s`.
* `TauCeti.semisimplification R M`: the semisimplification of a module of finite length, the
  product of the factors of a chosen composition series from `⊥` to `⊤`. For a `k`-algebra `R`
  it is a `k`-vector space (`TauCeti.semisimplification.instModule`), finite-dimensional when `M`
  is (`TauCeti.semisimplification.instFiniteDimensional`).

## Main results

* `TauCeti.jordanHolderMultiplicity_seriesSemisimplification`: the product of the factors of a
  composition series of `M` has the multiplicities of `M`.
* `TauCeti.nonempty_linearEquiv_seriesSemisimplification`: any composition series computes
  `M^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_iff`: `M^ss ≅ M` iff `M` is semisimple.
* `TauCeti.nonempty_linearEquiv_semisimplification_semisimplification`: `(M^ss)^ss ≅ M^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_prod_of_exact`: `M^ss ≅ A^ss × B^ss` for a
  short exact sequence `0 → A → M → B → 0`, and
  `TauCeti.nonempty_linearEquiv_semisimplification_prod_quotient`: `M^ss ≅ N^ss × (M/N)^ss`.
* `TauCeti.nonempty_linearEquiv_semisimplification_iff_jordanHolderMultiplicity_eq`:
  `M^ss ≅ N^ss` iff `M` and `N` have the same Jordan-Hölder multiplicities; in particular
  `TauCeti.nonempty_linearEquiv_semisimplification_of_linearEquiv`: isomorphic modules have
  isomorphic semisimplifications.
-/

public section

namespace TauCeti

universe u v w w'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### The factors of a composition series -/

/-- The product of the factors `s i.succ / s i.castSucc` of a composition series. It is
semisimple, each factor being simple by `TauCeti.isSimpleModule_subquotient`. -/
abbrev seriesSemisimplification (s : CompositionSeries (Submodule R M)) : Type v :=
  (i : Fin s.length) → ↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)

variable [IsNoetherian R M] [IsArtinian R M]

/-- **The factors of a composition series carry the multiplicities of the module**: the product
of the factors of a composition series of `M` from `⊥` to `⊤` contains every module as often
as `M` does. -/
theorem jordanHolderMultiplicity_seriesSemisimplification
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R (seriesSemisimplification s) S =
      jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_pi_eq_natCard,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop, compositionMultiplicity_def]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦
    (Nonempty.congr LinearEquiv.symm LinearEquiv.symm).trans isCompositionFactorAt_iff.symm

variable (R M) in
/-- **The semisimplification `M^ss`** of a module of finite length: the product of the factors of a
composition series from `⊥` to `⊤`. By `TauCeti.nonempty_linearEquiv_seriesSemisimplification`
every such series gives an isomorphic module, so the choice below is immaterial. It is a `def`
rather than an `abbrev`, so that it is used through the multiplicity lemma
`TauCeti.jordanHolderMultiplicity_semisimplification` instead of through the chosen series. Its
body is exposed only because the instances below, which Lean requires to be exposed, are
transferred from the chosen series. -/
@[expose] noncomputable def semisimplification : Type v :=
  seriesSemisimplification (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose

/-- The additive group structure of `M^ss`, that of the product of the factors. -/
noncomputable instance : AddCommGroup (semisimplification R M) :=
  inferInstanceAs (AddCommGroup (seriesSemisimplification _))

/-- The module structure of `M^ss`, that of the product of the factors. -/
noncomputable instance : Module R (semisimplification R M) :=
  inferInstanceAs (Module R (seriesSemisimplification _))

/-- The semisimplification is semisimple, as a product of simple modules. -/
instance : IsSemisimpleModule R (semisimplification R M) :=
  inferInstanceAs (IsSemisimpleModule R (seriesSemisimplification _))

/-- The semisimplification is Noetherian, as a finite product of simple modules. -/
instance : IsNoetherian R (semisimplification R M) :=
  inferInstanceAs (IsNoetherian R (seriesSemisimplification _))

/-- The semisimplification is Artinian, as a finite product of simple modules. -/
instance : IsArtinian R (semisimplification R M) :=
  inferInstanceAs (IsArtinian R (seriesSemisimplification _))

section Algebra

variable {k : Type*} [Field k] [Algebra k R] [Module k M] [IsScalarTower k R M]

/-- The `k`-vector space structure of the semisimplification of an `R`-module, for a
`k`-algebra `R`. -/
noncomputable instance semisimplification.instModule : Module k (semisimplification R M) :=
  inferInstanceAs (Module k (seriesSemisimplification _))

/-- The `k`- and `R`-actions on the semisimplification are compatible. -/
instance semisimplification.instIsScalarTower : IsScalarTower k R (semisimplification R M) :=
  inferInstanceAs (IsScalarTower k R (seriesSemisimplification _))

/-- The semisimplification of a finite-dimensional module is finite-dimensional. -/
instance semisimplification.instFiniteDimensional [FiniteDimensional k M] :
    FiniteDimensional k (semisimplification R M) :=
  inferInstanceAs (FiniteDimensional k (seriesSemisimplification _))

end Algebra

/-- The semisimplification has the Jordan-Hölder multiplicities of the module. -/
@[simp]
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

/-- **Two modules of finite length have isomorphic semisimplifications exactly when they have the
same Jordan-Hölder multiplicities.** It suffices to test the simple modules in the universe of
`R`. -/
theorem nonempty_linearEquiv_semisimplification_iff_jordanHolderMultiplicity_eq {N : Type w}
    [AddCommGroup N] [Module R N] [IsNoetherian R N] [IsArtinian R N] :
    Nonempty (semisimplification R M ≃ₗ[R] semisimplification R N) ↔
      ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
        jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S := by
  refine ⟨fun ⟨e⟩ S _ _ _ ↦ ?_, fun h ↦
    IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ ?_⟩
  · rw [← jordanHolderMultiplicity_semisimplification (M := M),
      jordanHolderMultiplicity_eq_of_linearEquiv e, jordanHolderMultiplicity_semisimplification]
  · rw [jordanHolderMultiplicity_semisimplification, jordanHolderMultiplicity_semisimplification,
      h S]

/-- Isomorphic modules of finite length have isomorphic semisimplifications. -/
theorem nonempty_linearEquiv_semisimplification_of_linearEquiv {N : Type w} [AddCommGroup N]
    [Module R N] [IsNoetherian R N] [IsArtinian R N] (e : M ≃ₗ[R] N) :
    Nonempty (semisimplification R M ≃ₗ[R] semisimplification R N) :=
  nonempty_linearEquiv_semisimplification_iff_jordanHolderMultiplicity_eq.mpr fun S _ _ _ ↦
    jordanHolderMultiplicity_eq_of_linearEquiv e S

/-- **Semisimplification is additive in short exact sequences**: for a short exact sequence
`0 → A → M → B → 0` of modules of finite length, `M^ss ≅ A^ss × B^ss`. -/
theorem nonempty_linearEquiv_semisimplification_prod_of_exact
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Nonempty (semisimplification R M ≃ₗ[R] semisimplification R A × semisimplification R B) :=
  IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ by
    rw [jordanHolderMultiplicity_prod, jordanHolderMultiplicity_semisimplification,
      jordanHolderMultiplicity_semisimplification, jordanHolderMultiplicity_semisimplification,
      jordanHolderMultiplicity_eq_add_of_exact f g hf hg hfg]

/-- For a submodule `N` of `M`, `M^ss ≅ N^ss × (M/N)^ss`. -/
theorem nonempty_linearEquiv_semisimplification_prod_quotient (N : Submodule R M) :
    Nonempty (semisimplification R M ≃ₗ[R]
      semisimplification R N × semisimplification R (M ⧸ N)) :=
  nonempty_linearEquiv_semisimplification_prod_of_exact N.subtype N.mkQ N.injective_subtype
    N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)

/-- The semisimplification of the zero module is zero. -/
instance subsingleton_semisimplification [Subsingleton M] :
    Subsingleton (semisimplification R M) :=
  have : IsEmpty (Fin (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose.length) := by
    rw [compositionSeries_length_eq_zero_of_subsingleton]
    infer_instance
  inferInstanceAs (Subsingleton (seriesSemisimplification _))

end TauCeti
