/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Sheaves.Flasque
public import TauCeti.Algebra.Module.Injective.Noetherian

/-!
# The sheaf of an injective module over a Noetherian ring is flasque

Let `R` be a Noetherian ring and `I` an injective `R`-module. This file proves that the
quasi-coherent sheaf `I^~` on `Spec R` is flasque: every section of `I^~` over an open subset
extends to a global section (Hartshorne, *Algebraic Geometry*, Proposition III.3.4).

Flasque sheaves have no higher cohomology, and every `R`-module embeds into an injective one, so
this is the input for Serre's vanishing theorem `Hⁱ(Spec R, M^~) = 0` for `i > 0` on a Noetherian
affine scheme.

## Implementation notes

Every open subset of `Spec R` is a finite union of basic open subsets `D(g)`, and the proof
inducts on the number of them. Suppose that every section over `W = D(g₁) ∪ ⋯ ∪ D(gₙ)` extends,
and let `s` be a section over `D(f) ∪ W`. Subtracting an extension of `s|_W` reduces to the case
that `s` vanishes on `W`. Then `σ = s|_{D(f)}` is an element of `I_f` that vanishes on each
`D(f gᵢ)`, so it is killed by a power of every `gᵢ`: it lies in the `𝔞`-primary component
`Γ_𝔞(I_f)` for `𝔞 = (g₁, …, gₙ)`. By `Module.Injective.primaryComponent_map_surjective` it is the
image of some `u ∈ Γ_𝔞(I)`, which is Hartshorne's Lemma III.3.2 and Proposition III.3.3 combined.
The global section `u` restricts to `σ` on `D(f)` and to zero on each `D(gᵢ)`, so it extends `s`.

This induction on basic open subsets replaces the Noetherian induction on the support of `I^~` in
Hartshorne's proof.

## Main declarations

* `TauCeti.AlgebraicGeometry.isFlasque_tilde_of_injective`: `I^~` is flasque.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Proposition 3.4.
-/

public section

open CategoryTheory Opposite TopologicalSpace PrimeSpectrum

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [IsNoetherianRing R] [Module.Injective R M]

/-- `M^~` as a presheaf of `R`-modules. Its sections over `D(f)` are the localization `M_f`,
through `tilde.toOpen`. -/
local notation "𝓕" => TopCat.Sheaf.presheaf (modulesSpecToSheaf.obj (tilde M))

/-- The `R`-module of sections of `M^~` over `U`. -/
local notation "Γₘ(" U ")" =>
  (Prefunctor.obj (CategoryTheory.Functor.toPrefunctor 𝓕) (op U) : ModuleCat R)

/-- Restriction of sections of `M^~` along an inclusion `h : V ≤ U`. -/
local notation "res[" h "]" =>
  Prefunctor.map (CategoryTheory.Functor.toPrefunctor 𝓕) (Quiver.Hom.op (homOfLE h))

/-- A section of `M^~` over `D(f) ∪ D(g₁) ∪ ⋯ ∪ D(gₙ)` that vanishes on every `D(gᵢ)` is the
restriction of a global section. -/
private theorem exists_restrict_eq_of_restrict_eq_zero (f : R) (G : Finset R)
    {U : (Spec R).Opens} (hU : U = basicOpen f ⊔ ⨆ g ∈ G, basicOpen g) (s : Γₘ(U))
    (hs : ∀ g ∈ G, ∀ h : (basicOpen g : (Spec R).Opens) ≤ U, res[h] s = 0) :
    ∃ t : Γₘ(⊤), res[le_top] t = s := by
  classical
  have hDf : (basicOpen f : (Spec R).Opens) ≤ U := hU ▸ le_sup_left
  have hDg : ∀ g ∈ G, (basicOpen g : (Spec R).Opens) ≤ U := fun g hg ↦
    hU ▸ (le_iSup₂ (f := fun g (_ : g ∈ G) ↦ basicOpen g) g hg).trans le_sup_right
  let σ : Γₘ(basicOpen f) := res[hDf] s
  -- Write `σ = x / fᵏ` in `M_f`.
  obtain ⟨⟨x, _, k, rfl⟩, hk⟩ := IsLocalizedModule.surj (.powers f)
    (tilde.toOpen M (basicOpen f)).hom σ
  replace hk : f ^ k • σ = tilde.toOpen M (basicOpen f) x := hk
  -- `σ` vanishes on each `D(f g)`, so a power of `g` kills it.
  have hσ : σ ∈ Ideal.primaryComponent Γₘ(basicOpen f) (Submodule.span R ↑G) := by
    refine (Ideal.mem_primaryComponent_span_iff G).mpr fun g hg ↦ ?_
    have hfg : (basicOpen (f * g) : (Spec R).Opens) ≤ basicOpen f := basicOpen_mul_le_left f g
    have hgg : (basicOpen (f * g) : (Spec R).Opens) ≤ basicOpen g := basicOpen_mul_le_right f g
    have hσg : res[hfg] σ = 0 :=
      (TopCat.Presheaf.restrict_restrict (F := 𝓕) hfg hDf s).trans <|
        (TopCat.Presheaf.restrict_restrict (F := 𝓕) hgg (hDg g hg) s).symm.trans <|
        (congrArg (fun y ↦ res[hgg] y) (hs g hg (hDg g hg))).trans (map_zero _)
    have hx : tilde.toOpen M (basicOpen (f * g)) x = 0 := by
      have h₁ : res[hfg] (tilde.toOpen M (basicOpen f) x) =
          tilde.toOpen M (basicOpen (f * g)) x :=
        congr($(tilde.toOpen_res M _ _ (homOfLE hfg)) x)
      have h₂ : res[hfg] (f ^ k • σ) = f ^ k • res[hfg] σ := map_smul _ _ _
      rw [← h₁, ← hk, h₂, hσg, smul_zero]
      -- The two zeros are those of the sections over `D(f g)`, with `D(f g)` read once as an open
      -- subset of `Spec R` and once as an open subset of the prime spectrum; they agree by `rfl`.
      rfl
    obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalizedModule.eq_zero_iff (.powers (f * g))
      (tilde.toOpen M (basicOpen (f * g))).hom).mp hx
    replace hN : (f * g) ^ N • x = 0 := hN
    -- In any localization `φ : M → M_f`, `fᵏ σ = φ x` and `(f g)ᴺ x = 0` force `gᴺ σ = 0`.
    have key {M' : Type u} [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M')
        [IsLocalizedModule (.powers f) φ] {σ' : M'} (hk' : f ^ k • σ' = φ x) :
        g ^ N • σ' = 0 := by
      refine IsLocalizedModule.smul_injective φ
        ⟨f ^ (N + k), pow_mem (Submonoid.mem_powers f) (N + k)⟩ ?_
      simp only [Submonoid.mk_smul, smul_zero]
      rw [smul_smul, mul_comm, ← smul_smul, pow_add, mul_smul, hk', smul_smul, ← mul_pow,
        mul_comm g, ← map_smul, hN, map_zero]
    exact ⟨N, key (tilde.toOpen M (basicOpen f)).hom hk⟩
  -- Lift `σ` to an element `u` of `M` killed by a power of every `g ∈ G`.
  obtain ⟨⟨u, hu⟩, hu'⟩ := Module.Injective.primaryComponent_map_surjective
    (Submodule.span R (G : Set R)) (.powers f) (tilde.toOpen M (basicOpen f)).hom ⟨σ, hσ⟩
  replace hu' : tilde.toOpen M (basicOpen f) u = σ := congr(Subtype.val $hu')
  -- The global section `u` restricts to `σ` on `D(f)` and to zero on each `D(g)`.
  have hres (V : (Spec R).Opens) :
      res[(le_top : V ≤ ⊤)] (tilde.toOpen M ⊤ u) = tilde.toOpen M V u :=
    congr($(tilde.toOpen_res M _ _ (homOfLE le_top)) u)
  refine ⟨tilde.toOpen M ⊤ u,
    TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).2 fun p hp ↦ ?_⟩
  rw [unop_op, hU] at hp
  obtain hp | hp := Opens.mem_sup.mp hp
  · exact ⟨basicOpen f, hDf, hp,
      (TopCat.Presheaf.restrict_restrict (F := 𝓕) hDf le_top _).trans ((hres _).trans hu')⟩
  · obtain ⟨g, hp⟩ := Opens.mem_iSup.mp hp
    obtain ⟨hg, hp⟩ := Opens.mem_iSup.mp hp
    obtain ⟨N, hN⟩ := (Ideal.mem_primaryComponent_span_iff G).mp hu g hg
    refine ⟨basicOpen g, hDg g hg, hp,
      (TopCat.Presheaf.restrict_restrict (F := 𝓕) (hDg g hg) le_top _).trans <|
        (hres _).trans <| .trans ?_ (hs g hg (hDg g hg)).symm⟩
    exact (IsLocalizedModule.eq_zero_iff (.powers g) (tilde.toOpen M (basicOpen g)).hom).mpr
      ⟨⟨_, N, rfl⟩, hN⟩

/-- A section of `M^~` over a finite union of basic open subsets is the restriction of a global
section. -/
private theorem exists_restrict_eq_of_eq_iSup (G : Finset R) :
    ∀ {U : (Spec R).Opens}, U = ⨆ g ∈ G, basicOpen g → ∀ s : Γₘ(U),
      ∃ t : Γₘ(⊤), res[le_top] t = s := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    intro U hU s
    refine ⟨0, TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).2
      fun p hp ↦ ?_⟩
    rw [unop_op, hU] at hp
    obtain ⟨g, hp⟩ := Opens.mem_iSup.mp hp
    exact absurd (Opens.mem_iSup.mp hp).1 (Finset.notMem_empty g)
  | insert f G _ ih =>
    intro U hU s
    rw [Finset.iSup_insert] at hU
    have hW : (⨆ g ∈ G, basicOpen g : (Spec R).Opens) ≤ U := hU ▸ le_sup_right
    obtain ⟨t₁, ht₁⟩ := ih rfl (res[hW] s)
    obtain ⟨t₂, ht₂⟩ := exists_restrict_eq_of_restrict_eq_zero M f G hU
      (s - res[le_top] t₁) fun g hg h ↦ by
        have hgW : (basicOpen g : (Spec R).Opens) ≤ ⨆ g ∈ G, basicOpen g :=
          le_iSup₂ (f := fun g (_ : g ∈ G) ↦ (basicOpen g : (Spec R).Opens)) g hg
        rw [map_sub, sub_eq_zero]
        exact (TopCat.Presheaf.restrict_restrict (F := 𝓕) hgW hW s).symm.trans <|
          (congrArg (fun y ↦ res[hgW] y) ht₁.symm).trans <|
          (TopCat.Presheaf.restrict_restrict (F := 𝓕) hgW le_top t₁).trans
            (TopCat.Presheaf.restrict_restrict (F := 𝓕) h le_top t₁).symm
    exact ⟨t₁ + t₂, by rw [map_add, ht₂, add_sub_cancel]⟩

/-- **The sheaf of an injective module over a Noetherian ring is flasque** (Hartshorne,
*Algebraic Geometry*, Proposition III.3.4): if `R` is Noetherian and `M` is an injective
`R`-module, then every section of `M^~` over an open subset of `Spec R` extends to a larger open
subset. -/
instance isFlasque_tilde_of_injective : (tilde M).presheaf.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    -- The abelian presheaf of `M^~` and its presheaf of `R`-modules `𝓕` have the same restriction
    -- maps on underlying sections, so surjectivity can be checked on the latter.
    change Function.Surjective (Prefunctor.map (CategoryTheory.Functor.toPrefunctor 𝓕) i)
    intro s
    -- The open subset `V` is quasi-compact, hence a finite union of basic open subsets.
    obtain ⟨G, hG⟩ : ∃ G : Finset R, V.unop = ⨆ g ∈ G, basicOpen g := by
      obtain ⟨G, hG, e⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
        isTopologicalBasis_basic_opens isCompact_basicOpen _).mp
          ⟨NoetherianSpace.isCompact _, V.unop.isOpen⟩
      refine ⟨hG.toFinset, Opens.ext (e.trans ?_)⟩
      ext p
      simp only [Set.mem_iUnion, SetLike.mem_coe]
      constructor
      · rintro ⟨g, hg, hp⟩
        exact Opens.mem_iSup.mpr ⟨g, Opens.mem_iSup.mpr ⟨hG.mem_toFinset.mpr hg, hp⟩⟩
      · intro hp
        obtain ⟨g, hp⟩ := Opens.mem_iSup.mp hp
        obtain ⟨hg, hp⟩ := Opens.mem_iSup.mp hp
        exact ⟨g, hG.mem_toFinset.mp hg, hp⟩
    obtain ⟨t, rfl⟩ := exists_restrict_eq_of_eq_iSup M G hG s
    exact ⟨res[le_top] t,
      TopCat.Presheaf.restrict_restrict (F := 𝓕) (leOfHom i.unop) le_top t⟩

end AlgebraicGeometry

end TauCeti
