/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.ChainComplex
import TauCeti.Algebra.Homology.HomologicalComplex.Augmented
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.KoszulComplex.Comparison
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Square
import TauCeti.RingTheory.Regular.ProjectiveDimension

/-!
# Projective dimension over a local ring

Let `R` be a Noetherian local ring whose maximal ideal `𝔪` is an associated prime of `R`, that is,
of depth zero: some nonzero `s ∈ R` satisfies `𝔪 s = 0`. Then every finite `R`-module of finite
projective dimension is free. This is the depth-zero case of the Auslander–Buchsbaum formula
`pd M + depth M = depth R`.

The embedding `κ → R`, `1 ↦ s`, of the residue field stays injective after tensoring with a flat
module, so `κ ⊗ -` preserves injectivity of maps out of flat modules. For a presentation
`0 → K → F → M → 0` with `F` finite free and `K` free by induction on the projective dimension,
`κ ⊗ K → κ ⊗ F` is therefore injective, and `M` is free by Nakayama's lemma.

This is the base case of Serre's theorem that a Noetherian local ring whose residue field has
finite projective dimension is regular. The induction step is a change of rings for the residue
field: for a nonzerodivisor `x ∈ 𝔪 \ 𝔪²`, the residue field of `R ⧸ (x)` is a direct summand of
`𝔪 ⧸ x 𝔪`, so a bound `n + 1` for the projective dimension of the residue field of `R` gives the
bound `n` for that of `R ⧸ (x)`.

In the other direction, the projective dimension of the residue field `κ` of any Noetherian local
ring is at least the embedding dimension `dim_κ 𝔪/𝔪²` (Stacks 00OA). Lift a basis of `𝔪/𝔪²` to
`x₁, …, xₙ ∈ 𝔪` and compare the Koszul complex `K(x)` with a minimal finite free resolution `F` of
`κ` of length `d` along a chain map over `κ`. The comparison stays injective modulo `𝔪` in every
degree, and `Kₙ = ⋀ⁿ Rⁿ ≅ R` is nonzero modulo `𝔪`, so `Fₙ ≠ 0` and `n ≤ d`. Neither exactness of
`K(x)` nor regularity of `R` is used.

## Main results

* `LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes`: over a local
  ring of depth zero, `κ ⊗ -` preserves injectivity of linear maps out of flat modules.
* `Module.free_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes`: over a
  Noetherian local ring of depth zero, a finite module of finite projective dimension is free.
* `TauCeti.IsLocalRing.hasProjectiveDimensionLE_residueField_quotient`: for a nonzerodivisor
  `x ∈ 𝔪 \ 𝔪²`, if the residue field of `R` has projective dimension at most `n + 1`, then the
  residue field of `R ⧸ (x)` has projective dimension at most `n` over `R ⧸ (x)`.
* `TauCeti.IsLocalRing.finrank_cotangentSpace_le_of_hasProjectiveDimensionLE` and
  `TauCeti.IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_quotient_maximalIdeal`: the
  residue field of a Noetherian local ring has projective dimension at least `dim_κ 𝔪/𝔪²`
  (Stacks 00OA).

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 19.1 (the Auslander–Buchsbaum formula) and
  the proof of Theorem 19.2.
* [The Stacks Project, Lemma 10.110.3](https://stacks.math.columbia.edu/tag/00OA), the lower
  bound by the embedding dimension, via Koszul complexes and minimal resolutions.
-/

public section

universe v u

open CategoryTheory IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Over a local ring whose maximal ideal is an associated prime, tensoring with the residue
field preserves injectivity of linear maps out of flat modules. -/
theorem LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes
    (hm : maximalIdeal R ∈ associatedPrimes R R)
    {K F : Type*} [AddCommGroup K] [Module R K] [Module.Flat R K] [AddCommGroup F] [Module R F]
    {l : K →ₗ[R] F} (hl : Function.Injective l) :
    Function.Injective (l.lTensor (ResidueField R)) := by
  obtain ⟨-, ι, hι⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp hm
  -- `κ ⊗ K → κ ⊗ F → R ⊗ F` equals `κ ⊗ K → R ⊗ K → R ⊗ F`, injective as `K` is flat.
  have h := (Module.Flat.lTensor_preserves_injective_linearMap (M := R) l hl).comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := K) ι hι)
  rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.coe_comp] at h
  exact h.of_comp

/-- **Finite projective dimension in depth zero.** Over a Noetherian local ring whose maximal
ideal is an associated prime, a finite module of finite projective dimension is free. -/
theorem Module.free_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes
    [Small.{v} R] (hm : maximalIdeal R ∈ associatedPrimes R R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] [HasProjectiveDimensionLE M n] :
    Module.Free R M := by
  induction n generalizing M with
  | zero =>
    have : CategoryTheory.Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›
    have : Module.Projective R M := M.projective_of_module_projective
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    -- A presentation `0 → K → F → M → 0` with `F` finite free; `K` is free by induction.
    obtain ⟨F, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance ‹_›
    have := ih (ModuleCat.of R (LinearMap.ker f))
    exact Module.free_of_lTensor_residueField_injective _ f hf f.exact_subtype_ker_map
      (LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes hm
        (LinearMap.ker f).injective_subtype)

namespace TauCeti.IsLocalRing

open Ideal Pointwise

/-- **Change of rings for the residue field.** If the residue field of a local ring `R` has
projective dimension at most `n + 1` and `x ∈ 𝔪 \ 𝔪²` is a nonzerodivisor, then the residue
field of `R ⧸ (x)` has projective dimension at most `n` over `R ⧸ (x)`. Indeed `𝔪` has projective
dimension at most `n`, hence so does `𝔪 ⧸ x 𝔪` over `R ⧸ (x)`, and the residue field of
`R ⧸ (x)` is a direct summand of `𝔪 ⧸ x 𝔪`. This is the induction step of Serre's theorem. -/
theorem hasProjectiveDimensionLE_residueField_quotient {R : Type u} [CommRing R]
    [IsLocalRing R] [Small.{v} R] {n : ℕ} {x : R} (hxm : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) (hx : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ span {x})]
    [Small.{v} (R ⧸ span {x})]
    [HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (n + 1)] :
    HasProjectiveDimensionLE (ModuleCat.of (R ⧸ span {x})
      (Shrink.{v} ((R ⧸ span {x}) ⧸ maximalIdeal (R ⧸ span {x})))) n := by
  set I := span {x}
  set q := Ideal.Quotient.mk I
  -- The sequence `0 → 𝔪 → R → κ → 0` shows that `𝔪` has projective dimension at most `n`.
  have hS := ModuleCat.shortComplexOfConj_shortExact (Shrink.linearEquiv R (maximalIdeal R))
    (Shrink.linearEquiv R R) (Shrink.linearEquiv R (R ⧸ maximalIdeal R)) _ _
    (LinearMap.exact_subtype_mkQ (maximalIdeal R)) (maximalIdeal R).injective_subtype
    (maximalIdeal R).mkQ_surjective
  let M : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} (maximalIdeal R))
  have : HasProjectiveDimensionLE M n := hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance ‹_›
  -- `x` is regular on `𝔪 ⊆ R`, so `𝔪 ⧸ x 𝔪` has projective dimension at most `n` over `R ⧸ (x)`.
  have hreg : IsSMulRegular M x :=
    (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hx).of_injective
      ((maximalIdeal R).subtype ∘ₗ (Shrink.linearEquiv R (maximalIdeal R)).toLinearMap)
      ((maximalIdeal R).injective_subtype.comp (Shrink.linearEquiv R _).injective)
  have := ModuleCat.hasProjectiveDimensionLE_quotient_smul_top hx n M hreg
  -- The residue field of `R ⧸ (x)` is a retract of `𝔪 ⧸ x 𝔪`.
  obtain ⟨i, r, hri⟩ := exists_comp_eq_id_of_notMem_sq hxm hx2
  let e₁ : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R ⧸ I]
      (maximalIdeal R ⧸ I • (⊤ : Submodule R (maximalIdeal R))) :=
    (Submodule.Quotient.equiv _ _ (Shrink.linearEquiv R (maximalIdeal R)) (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := I))
  let e₂ : Shrink.{v} ((R ⧸ I) ⧸ maximalIdeal (R ⧸ I)) ≃ₗ[R ⧸ I]
      (R ⧸ I) ⧸ (maximalIdeal R).map q :=
    (Shrink.linearEquiv (R ⧸ I) _).trans (Submodule.quotEquivOfEq _ _
      (map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective).symm)
  let ret : Retract (ModuleCat.of (R ⧸ I) (Shrink.{v} ((R ⧸ I) ⧸ maximalIdeal (R ⧸ I))))
      (ModuleCat.of (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :=
    { i := ModuleCat.ofHom (e₁.symm.toLinearMap ∘ₗ i ∘ₗ e₂.toLinearMap)
      r := ModuleCat.ofHom (e₂.symm.toLinearMap ∘ₗ r ∘ₗ e₁.toLinearMap)
      retract := by
        ext y
        simpa using congr(e₂.symm ($hri (e₂ y))) }
  exact ret.hasProjectiveDimensionLT (n + 1)

/-- **The projective dimension of the residue field bounds the embedding dimension** (Stacks,
Lemma 10.110.3 (00OA)). If the residue field `κ` of a Noetherian local ring `R` has projective
dimension at most `d`, then `dim_κ 𝔪/𝔪² ≤ d`. -/
@[stacks 00OA]
theorem finrank_cotangentSpace_le_of_hasProjectiveDimensionLE {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R] {d : ℕ}
    [HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) d] :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ d := by
  set n := Module.finrank (ResidueField R) (CotangentSpace R)
  set 𝔪 := maximalIdeal R
  have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ 𝔪)) d :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R (Shrink.{v} (R ⧸ 𝔪))) (N := ModuleCat.of R (R ⧸ 𝔪))
      (Shrink.linearEquiv R (R ⧸ 𝔪)) d
  -- Lift a basis of `𝔪/𝔪²` to `x₁, …, xₙ ∈ 𝔪`; `φ` is the functional of the Koszul complex `K(x)`.
  let v := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose x hx using fun i ↦ 𝔪.toCotangent_surjective (v i)
  let b := Pi.basisFun R (Fin n)
  let φ : Module.Dual R (Fin n → R) := Fintype.linearCombination R fun i ↦ (x i : R)
  have hφb (i : Fin n) : φ (b i) = x i := by simp [φ, b]
  have hφm (y : Fin n → R) : φ y ∈ 𝔪 := by
    simp only [φ, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (x i).2
  have hφ (i : Fin n) : φ (b i) ∈ 𝔪 := hφm (b i)
  have hli : LinearIndependent (R ⧸ 𝔪) fun i ↦ 𝔪.toCotangent ⟨φ (b i), hφ i⟩ := by
    have : (fun i ↦ 𝔪.toCotangent ⟨φ (b i), hφ i⟩) = v :=
      funext fun i ↦ (congrArg 𝔪.toCotangent (Subtype.ext (hφb i))).trans (hx i)
    rw [this]
    exact v.linearIndependent
  -- A minimal finite free resolution `F` of `κ`, zero above degree `d`.
  obtain ⟨F, hFfree, hFzero, hFmin⟩ :=
    ModuleCat.exists_projectiveResolution_finite_free_minimal (ModuleCat.of R (R ⧸ 𝔪)) ‹_›
  rw [ChainComplex.isMinimal_iff_range_d_succ_le, ringJacobson_eq_maximalIdeal] at hFmin
  have (k : ℕ) : Module.Free R (F.complex.X k) := (hFfree k).2
  have (k : ℕ) : Projective ((koszulComplex φ).X k) := by
    rw [koszulComplex_X]
    exact ModuleCat.projective_of_categoryTheory_projective _
  -- The augmentation `K₀ = R → κ` vanishes on the image of `K₁`, as the `xᵢ` lie in `𝔪`.
  let ε : (koszulComplex φ).X 0 ⟶ ModuleCat.of R (R ⧸ 𝔪) :=
    ModuleCat.ofHom (𝔪.mkQ ∘ₗ (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap)
  have hε : (koszulComplex φ).d 1 0 ≫ ε = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, koszulComplex_d_apply φ 0 z, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero 𝔪).mpr
      ((zeroEquiv_koszulDifferential_zero φ z).symm ▸ hφm _)
  -- The comparison map `α : K(x) → F` over `κ`.
  let α := (koszulComplex φ).liftToAugmented (F.π.f 0) F.complex_d_comp_π_f_zero F.exact₀
    F.exact_succ ε hε
  -- In degree `0`, `α` lies over the augmentation `ε`, so it is injective modulo `𝔪`; here `K₀`
  -- is `⋀⁰ Rⁿ` by definition of `koszulComplex`.
  have hα0 : (𝔪 • ⊤ : Submodule R (F.complex.X 0)).comap (α.f 0).hom ≤ 𝔪 • ⊤ :=
    (α.f 0).hom.comap_smul_top_le_of_comp_eq_mkQ_zeroEquiv (F.π.f 0).hom
      congr(($(ChainComplex.liftToAugmented_f_zero_comp (koszulComplex φ) (F.π.f 0)
        F.complex_d_comp_π_f_zero F.exact₀ F.exact_succ ε hε)).hom)
  -- If `d < n`, then `Fₙ = 0`, but `α` is injective modulo `𝔪` on `⋀ⁿ Rⁿ ≅ R`.
  by_contra! hlt
  have hα := b.comap_smul_top_le_of_hom_koszulComplex φ hφ hli hFmin α hα0 n
  let c := b.exteriorPower n
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  have := ModuleCat.isZero_iff_subsingleton.mp (hFzero n hlt)
  have hs : c s ∈ (𝔪 • ⊤ : Submodule R (⋀[R]^n (Fin n → R))) :=
    hα <| Submodule.mem_comap.mpr <| by convert zero_mem (𝔪 • ⊤ : Submodule R (F.complex.X n))
  have h1 := c.mem_smul_top_iff.mp hs s
  rw [c.repr_self, Finsupp.single_eq_same] at h1
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- **The projective dimension of the residue field is at least the embedding dimension**
(Stacks, Lemma 10.110.3 (00OA)): for a Noetherian local ring `R` with residue field `κ`,
`dim_κ 𝔪/𝔪² ≤ pd_R κ`. -/
@[stacks 00OA]
theorem finrank_cotangentSpace_le_projectiveDimension_quotient_maximalIdeal {R : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R] :
    (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤
      projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) := by
  set κ := ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))
  induction h : projectiveDimension κ using WithBot.recBotCoe with
  | bot =>
    have : Nontrivial κ := (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).nontrivial_congr.mpr
      inferInstance
    exact absurd (ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff κ).mp h))
      (not_subsingleton κ)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe d =>
      have : HasProjectiveDimensionLE κ d := (projectiveDimension_le_iff κ d).mp h.le
      exact_mod_cast finrank_cotangentSpace_le_of_hasProjectiveDimensionLE.{v}

end TauCeti.IsLocalRing
