/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite
public import TauCeti.RepresentationTheory.Homological.TateCohomology.NakayamaRim
public import TauCeti.RepresentationTheory.Homological.TateCohomology.SplittingModule
import Mathlib.NumberTheory.Padics.LocalField
import TauCeti.Algebra.MonoidAlgebra.Exactness
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The Tate module of a finite layer

Let `L/K` be a finite Galois extension of `p`-adic fields with group `G = Gal(L/K)`, and let
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` be the `p`-adic completion of `Lˣ`, a `ℤ_p[G]`-module. The module
`Y = I_{G_K} / I_{G_L} I_{G_K}` of NSW (5.6.5) is a finitely generated `ℤ_p[G]`-module of
projective dimension at most one which is an extension

`0 → A(L) → Y → I_G → 0`

of the augmentation ideal `I_G` of `ℤ_p[G]` by `A(L)`. The integral decomposition
`Y ≃ M₀ ⊕ ℤ_p[G]^N` of the proof of NSW (7.4.1)
(`TauCeti.nonempty_linearEquiv_tameFrameModule_prod`) uses only these properties, so a **Tate
module** of the layer, `TauCeti.LayerTateModule`, is any module with exactly them; it is not
identified here with the quotient `I_{G_K} / I_{G_L} I_{G_K}`. (The name `TauCeti.TateModule` is
the `p`-adic Tate module `lim_n A[p^n]` of an abelian group.)

Projective dimension at most one is the theorem of Nakayama and Rim
(`Rep.projective_ker_of_isZero_res`): a cohomologically trivial representation has a projective
resolution of length one. So any cohomologically trivial extension of `I_G` by `A(L)` is a Tate
module of the layer (`TauCeti.LayerTateModule.nonempty_of_isZero`). The splitting module of a
class `u ∈ H²(G, A(L))` is such an extension once `u` satisfies Tate's hypotheses on the
`p`-subgroups of `G` (`TauCeti.LayerTateModule.nonempty_of_tateHypotheses`); the class of the
layer, carried to `A(L)` along local reciprocity, is one.

## Main definitions

* `TauCeti.LayerTateModule`: a finitely generated `ℤ_p[Gal(L/K)]`-module of projective dimension
  at most one which is an extension of the augmentation ideal by `A(L)`.

## Main results

* `TauCeti.LayerTateModule.nonempty_of_isZero`: a cohomologically trivial extension of the
  augmentation ideal by `A(L)` is a Tate module of the layer.
* `TauCeti.LayerTateModule.nonempty_of_tateHypotheses`: a class in `H²(Gal(L/K), A(L))`
  satisfying Tate's hypotheses on the `p`-subgroups gives a Tate module of the layer.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (5.6.5) and the
  proof of (7.4.1).
* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] (K : Type u) [Field K] [Algebra K L]

/-- **A Tate module of a layer** `L/K`: the properties of the module `Y = I_{G_K}/I_{G_L} I_{G_K}`
of NSW (5.6.5) that the integral decomposition in the proof of (7.4.1) consumes, without an
identification with that quotient. It is a finitely generated `ℤ_p[Gal(L/K)]`-module of
projective dimension at most one, together with an extension `0 → A(L) → Y → I_G → 0` of the
augmentation ideal `I_G` by the `p`-adic completion `A(L)` of `Lˣ`. -/
structure LayerTateModule where
  /-- The carrier `Y`. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier]
  /-- The inclusion of `A(L)`. -/
  ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] carrier
  /-- The projection onto the augmentation ideal. -/
  π : carrier →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
    RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))
  ι_injective : Function.Injective ι
  π_surjective : Function.Surjective π
  exact : LinearMap.ker π = LinearMap.range ι
  finite : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier
  /-- Projective dimension at most one: a quotient of a free module by a projective kernel. -/
  projdim : ∃ (n : ℕ) (f : (Fin n → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) →ₗ[MonoidAlgebra ℤ_[p]
      (L ≃ₐ[K] L)] carrier),
    Function.Surjective f ∧ Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker f)

attribute [instance] LayerTateModule.addCommGroup LayerTateModule.module

namespace LayerTateModule

variable {p L K}

/-- The inclusion of `A(L)` and the projection onto `I_G` form an exact sequence. -/
theorem exact_ι_π (Y : LayerTateModule p L K) : Function.Exact Y.ι Y.π :=
  LinearMap.exact_iff.mpr Y.exact

/-- **A cohomologically trivial extension of `I_G` by `A(L)` is a Tate module.** Let `L` be a
finite extension of `ℚ_p` and `K` a subfield with `Gal(L/K)` finite. Let `Y` be a representation
of `Gal(L/K)` over `ℤ_p` whose Tate cohomology vanishes on every subgroup in every degree, and
`0 → A(L) → Y → I_G → 0` an exact sequence of `ℤ_p[Gal(L/K)]`-modules. Then `Y` is finitely
generated, and by the theorem of Nakayama and Rim (`Rep.projective_ker_of_isZero_res`) it has
projective dimension at most one, so it is a Tate module of the layer. -/
theorem nonempty_of_isZero {L K : Type} [Field L] [Field K] [Algebra K L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Finite (L ≃ₐ[K] L)]
    (Y : Rep ℤ_[p] (L ≃ₐ[K] L))
    (hY : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (Rep.res S.subtype Y) n))
    {ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Y.ρ.asModule}
    {π : Y.ρ.asModule →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))}
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hιπ : Function.Exact ι π) :
    Nonempty (LayerTateModule p L K) := by
  have := Fintype.ofFinite (L ≃ₐ[K] L)
  -- `A(L)` is finitely generated: give `L` its local-field structure.
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[p] L)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have := padicCompletionUnits_module_finite p L hpL K
  -- `I_G` is generated by the finitely many `g - 1`.
  have : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))) := by
    rw [Module.Finite.iff_fg, MonoidAlgebra.ker_augmentation_eq_span]
    exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩
  have hfin : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) Y.ρ.asModule :=
    .of_exact hιπ hπ
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) Y.ρ.asModule
  have hker := Rep.projective_ker_of_isZero_res
    (fun _ ↦ PadicInt.isUnit_natCast_or_isMaximal_span) Y hY f hf
  exact ⟨{
    carrier := Y.ρ.asModule
    ι := ι
    π := π
    ι_injective := hι
    π_surjective := hπ
    exact := LinearMap.exact_iff.mp hιπ
    finite := hfin
    projdim := ⟨n, f, hf, hker⟩ }⟩

/-- **A degree-two class of `A(L)` satisfying Tate's hypotheses gives a Tate module.** Let `L` be
a finite extension of `ℚ_p` and `K` a subfield with `Gal(L/K)` finite, and let
`u ∈ H²(Gal(L/K), A(L))`. Suppose that for every `p`-subgroup `S` of `Gal(L/K)`,
`H¹(S, A(L)) = 0`, the restriction of `u` generates `H²(S, A(L))` as a `ℤ_p`-module, and
`H²(S, A(L))` has order `#S`. Then the splitting module of `u`, an extension
`0 → A(L) → Y → I_G → 0`, is cohomologically trivial
(`TauCeti.TateCohomology.isZero_res_splittingModule`; on `ℓ`-subgroups for `ℓ ≠ p` all
positive-degree group cohomology of a `ℤ_p`-module vanishes), so it is a Tate module of the
layer. -/
theorem nonempty_of_tateHypotheses {L K : Type} [Field L] [Field K] [Algebra K L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Finite (L ≃ₐ[K] L)]
    (u : groupCohomology (Rep.of (padicCompletionUnitsRepresentation p L K)) 2)
    (h1 : ∀ S : Subgroup (L ≃ₐ[K] L), IsPGroup p S →
      IsZero (groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 1))
    (hgen : ∀ S : Subgroup (L ≃ₐ[K] L), IsPGroup p S →
      ∀ x : groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2,
        ∃ r : ℤ_[p], r • groupCohomology.map S.subtype
          (𝟙 (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K)))) 2 u = x)
    (hcard : ∀ S : Subgroup (L ≃ₐ[K] L), IsPGroup p S →
      Nat.card (groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
        Nat.card S) :
    Nonempty (LayerTateModule p L K) := by
  let A := Rep.of (padicCompletionUnitsRepresentation p L K)
  -- On an `ℓ`-subgroup with `ℓ ≠ p`, everything vanishes: `#S` is a unit of `ℤ_p`.
  have hunit (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (S : Subgroup (L ≃ₐ[K] L))
      (hS : IsPGroup ℓ S) : IsUnit (Nat.card S : ℤ_[p]) := by
    obtain ⟨e, he⟩ := hS.exists_card_eq
    rw [he, Nat.cast_pow]
    exact (PadicInt.isUnit_natCast_of_coprime
      ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hℓ))).pow e
  have hsub (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (S : Subgroup (L ≃ₐ[K] L)) (hS : IsPGroup ℓ S)
      (n : ℕ) : Subsingleton (groupCohomology (Rep.res S.subtype A) (n + 1)) :=
    groupCohomology.subsingleton_of_isUnit_natCard _ (hunit ℓ hℓ S hS) n
  have hY := TateCohomology.isZero_res_splittingModule A u
    (fun ℓ _ S hS ↦ by
      by_cases hℓ : ℓ = p
      · subst hℓ
        exact h1 S hS
      · exact @ModuleCat.isZero_of_subsingleton _ _ _ (hsub ℓ hℓ S hS 0))
    (fun ℓ _ S hS x ↦ by
      by_cases hℓ : ℓ = p
      · subst hℓ
        exact hgen S hS x
      · exact ⟨0, @Subsingleton.elim _ (hsub ℓ hℓ S hS 1) _ _⟩)
    (fun _ _ S _ ↦ PadicInt.finite_quotient_span (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (fun ℓ _ S hS ↦ by
      by_cases hℓ : ℓ = p
      · subst hℓ
        obtain ⟨e, he⟩ := hS.exists_card_eq
        rw [hcard S hS, PadicInt.natCard_quotient_span (Nat.cast_ne_zero.mpr Nat.card_pos.ne'),
          PadicInt.valuation_natCast, he, padicValNat.prime_pow]
      · have := hsub ℓ hℓ S hS 1
        rw [Nat.card_unique (α := groupCohomology (Rep.res S.subtype A) 2),
          Ideal.span_singleton_eq_top.mpr (hunit ℓ hℓ S hS)]
        exact (Nat.card_unique).symm)
  -- The inclusion of `A(L)` and the projection to `I_G ⊆ ℤ_p[G]`, as `ℤ_p[G]`-linear maps.
  let ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (Rep.splittingModule A u).ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (Rep.splittingModuleIncl A u).hom
  let πΛ : (Rep.splittingModule A u).ρ.asModule →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) :=
    Representation.ofMulActionSelfAsModuleEquiv.toLinearMap ∘ₗ
      Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (Rep.splittingModuleProj A u ≫ Rep.augmentationι ℤ_[p] (L ≃ₐ[K] L)).hom
  have hπΛ (y : (Rep.splittingModule A u).ρ.asModule) :
      πΛ y = (Rep.augmentationι ℤ_[p] (L ≃ₐ[K] L)).hom (Rep.splittingModuleProj A u y) :=
    rfl
  have hmem (y : (Rep.splittingModule A u).ρ.asModule) :
      πΛ y ∈ RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)) := by
    rw [RingHom.mem_ker, hπΛ, ← Rep.augmentation_hom_apply, ← ConcreteCategory.comp_apply,
      Rep.augmentationι_comp_augmentation]
    -- The zero morphism of representations evaluates to `0`.
    rfl
  let π : (Rep.splittingModule A u).ρ.asModule →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)) :=
    πΛ.codRestrict _ hmem
  -- `0 → A(L) → Y → I_G → 0` is exact.
  have hse := Rep.splittingModuleSES_shortExact A u
  rw [Rep.splittingModuleSES_def] at hse
  have hι : Function.Injective ι := (Rep.mono_iff_injective _).1 hse.mono_f
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    have haug := Rep.augmentationSES_shortExact ℤ_[p] (L ≃ₐ[K] L)
    rw [Rep.augmentationSES_def] at haug
    have hexact := haug.exact.map (forget₂ (Rep ℤ_[p] (L ≃ₐ[K] L)) (ModuleCat ℤ_[p]))
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact
    obtain ⟨z, hz⟩ : ∃ z : Rep.augmentationIdeal ℤ_[p] (L ≃ₐ[K] L),
        (Rep.augmentationι ℤ_[p] (L ≃ₐ[K] L)).hom z = x :=
      (hexact x).1 ((Rep.augmentation_hom_apply _ _ x).trans hx)
    obtain ⟨y, rfl⟩ := (Rep.epi_iff_surjective _).1 hse.epi_g z
    exact ⟨y, Subtype.ext hz⟩
  have hιπ : Function.Exact ι π := by
    -- `ι` and `π` are the maps of the splitting-module sequence read on `ρ.asModule`, which is
    -- the underlying module of the representation by definition; `change` unfolds `ι`, `π`.
    intro (y : Rep.splittingModule A u)
    rw [← Subtype.coe_inj]
    change (Rep.augmentationι ℤ_[p] (L ≃ₐ[K] L)).hom (Rep.splittingModuleProj A u y) = 0 ↔
      ∃ a : A, Rep.splittingModuleIncl A u a = y
    rw [← map_zero (Rep.augmentationι ℤ_[p] (L ≃ₐ[K] L)).hom,
      (TauCeti.AugmentationIdeal.augmentationι_injective ℤ_[p] (L ≃ₐ[K] L)).eq_iff]
    exact (Rep.exact_iff_function_exact _).1 hse.exact y
  exact nonempty_of_isZero _ hY hι hπ hιπ

end LayerTateModule

end TauCeti
