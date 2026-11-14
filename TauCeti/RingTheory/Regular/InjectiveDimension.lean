/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.RingTheory.Flat.NonZeroDivisors

/-!
# Injective dimension along the quotient by a nonzerodivisor

Let `x` be a nonzerodivisor of a commutative ring `R`, and let `M` be an `R`-module on which `x` is
regular. Reducing `M` modulo `x` lowers any positive bound on the injective dimension by one:

```text
id_{R ⧸ (x)} (M ⧸ x M) + 1 ≤ id_R M.
```

In particular, if `M` has injective dimension at most `n + 1` over `R`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`; if `M` is injective over `R`, it is divisible by
`x` and `M ⧸ x M` is zero. Applied to `M = R`, this is the change-of-rings step showing that the
quotient of an Iwanaga–Gorenstein commutative ring by a nonzerodivisor is again
Iwanaga–Gorenstein, with self-injective dimension lowered by one.

For an ideal `I` of `R` and an injective `R`-module `E`, the `I`-torsion submodule
`Submodule.torsionBySet R E I ≅ Hom_R(R ⧸ I, E)` is injective over `R ⧸ I`: any `R`-linear map out
of an `R ⧸ I`-module automatically lands in the `I`-torsion submodule. When `I = (x)` for a
nonzerodivisor `x`, every injective `R`-module `E` has surjective multiplication by `x`. Along an
injective copresentation `0 → C → E → C' → 0` of a module `C` on which multiplication by `x` is
surjective, multiplication by `x` stays surjective on `C'` and the `x`-torsion submodules form a
short exact sequence `0 → K(C) → K(E) → K(C') → 0` over `R ⧸ (x)`, so `K(C)` has injective
dimension at most `id_R C` over `R ⧸ (x)`. Finally, for an `x`-regular module `M`, an injective
copresentation `0 → M → E → C → 0` gives a short exact connecting sequence
`0 → K(E) → K(C) → M ⧸ x M → 0` over `R ⧸ (x)`, shifting the injective dimension bound by one.

## Main results

* `ModuleCat.injective_torsionBySet_of_injective`: for an ideal `I` of `R` and an injective
  `R`-module `E`, the `I`-torsion submodule of `E` is injective over `R ⧸ I`.
* `ModuleCat.surjective_smul_of_injective`: an injective `R`-module is divisible by every
  nonzerodivisor of `R`.
* `ModuleCat.hasInjectiveDimensionLE_torsionBy_of_surjective_smul`: if `x` is a nonzerodivisor and
  multiplication by `x` is surjective on `C`, then the `x`-torsion submodule of `C` has injective
  dimension over `R ⧸ (x)` at most that of `C` over `R`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_smul_top_of_succ`: **Rees's reduction bound**: if `x`
  is a nonzerodivisor regular on an `R`-module `M` of injective dimension at most `n + 1`, then
  `M ⧸ x M` has injective dimension at most `n` over `R ⧸ (x)`.
* `ModuleCat.injectiveDimension_quotient_smul_top_add_one_le`:
  `injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M` for an `x`-regular module `M`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_span_singleton_of_succ`: if `R` has self-injective
  dimension at most `n + 1`, then `R ⧸ (x)` has self-injective dimension at most `n`.

No finiteness or locality is assumed: the bounds hold for all modules.

## References

* D. Rees, *A theorem of homological algebra*, Proc. Cambridge Philos. Soc. **52** (1956), 605–610.
* H. Matsumura, *Commutative Ring Theory*, Section 18, Lemma 2 preceding Theorem 18.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.1, Lemma 3.1.16.
-/

public section

universe v u

open CategoryTheory Ideal Pointwise

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- For an ideal `I` of `R` and an injective `R`-module `E`, the `I`-torsion submodule of `E` is an
injective `R ⧸ I`-module: extending an `R ⧸ I`-linear map along an `R ⧸ I`-monomorphism in
`ModuleCat R` automatically lands in the `I`-torsion submodule because `I` annihilates the source.
-/
theorem injective_torsionBySet_of_injective (I : Ideal R) (E : ModuleCat.{v} R) [Injective E] :
    Injective (of (R ⧸ I) (Submodule.torsionBySet R E I)) where
  factors {Y₁ Y₂} f g _ := by
    let F := restrictScalars.{v} (Ideal.Quotient.mk I)
    have hg : Mono (F.map g) := inferInstance
    let ι : F.obj (of (R ⧸ I) (Submodule.torsionBySet R E I)) ⟶ E :=
      ofHom (X := F.obj (of (R ⧸ I) (Submodule.torsionBySet R E I)))
        { toFun := fun z ↦ (z : Submodule.torsionBySet R E I).1
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    let ψ : F.obj Y₂ ⟶ E := Injective.factorThru (F.map f ≫ ι) (F.map g)
    have hψ : ∀ y : F.obj Y₂, ψ y ∈ Submodule.torsionBySet R E I := fun y ↦ by
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨r, hr⟩
      have hy : r • y = 0 := by
        rw [restrictScalars.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
        exact zero_smul _ _
      exact (ψ.hom.map_smul r y).symm.trans (by rw [hy, map_zero])
    let ψQ : Y₂ →ₗ[R ⧸ I] Submodule.torsionBySet R E I :=
      { toFun := fun y ↦ ⟨ψ y, hψ y⟩
        map_add' := fun a b ↦ Subtype.ext (ψ.hom.map_add a b)
        map_smul' := fun s y ↦ by
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
          exact Subtype.ext (ψ.hom.map_smul r y) }
    refine ⟨ofHom ψQ, hom_ext (LinearMap.ext fun y ↦ Subtype.ext ?_)⟩
    exact ConcreteCategory.congr_hom (Injective.comp_factorThru (F.map f ≫ ι) (F.map g)) y

/-- For an element `x` of `R` and an injective `R`-module `E`, the `x`-torsion submodule of `E` is
an injective `R ⧸ (x)`-module. -/
theorem injective_torsionBy_of_injective (x : R) (E : ModuleCat.{v} R) [Injective E] :
    Injective (of (R ⧸ span {x}) (Submodule.torsionBy R E x)) :=
  Injective.of_iso (LinearEquiv.toModuleIso (R := R ⧸ span {x})
    { __ := LinearEquiv.ofEq _ _ (Submodule.torsionBySet_ideal_span_singleton_eq x)
      map_smul' := fun s _ ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        rfl })
    (injective_torsionBySet_of_injective (span {x}) E)

variable [Small.{v} R]

/-- An injective `R`-module is divisible by every nonzerodivisor `x` of `R`. -/
theorem surjective_smul_of_injective {x : R} (hx : x ∈ nonZeroDivisors R)
    (E : ModuleCat.{v} R) [Injective E] :
    Function.Surjective (fun y : E ↦ x • y) := fun y ↦ by
  let S := of R (Shrink.{v} R)
  let e := Shrink.linearEquiv.{v} R R
  let μ : S ⟶ S := ofHom (e.symm.toLinearMap ∘ₗ LinearMap.lsmul R R x ∘ₗ e.toLinearMap)
  have hμ_inj : Function.Injective μ := fun a b hab ↦
    e.injective ((Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hx) (e.symm.injective hab))
  have : Mono μ := (ModuleCat.mono_iff_injective μ).mpr hμ_inj
  let f : S ⟶ E := ofHom (LinearMap.toSpanSingleton R E y ∘ₗ e.toLinearMap)
  let ψ : S ⟶ E := Injective.factorThru f μ
  refine ⟨ψ (e.symm 1), ?_⟩
  have h1 := ConcreteCategory.congr_hom (Injective.comp_factorThru f μ) (e.symm 1)
  simp only [comp_apply, μ, f, hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.lsmul_apply, LinearMap.toSpanSingleton_apply, e.apply_symm_apply, one_smul] at h1
  rw [map_smul e.symm x 1, LinearMap.map_smul] at h1
  exact h1

/-- Reducing an injective `R`-module modulo a nonzerodivisor `x` yields the zero module. -/
theorem isZero_quotient_smul_top_of_injective {x : R} (hx : x ∈ nonZeroDivisors R)
    (E : ModuleCat.{v} R) [Injective E] :
    Limits.IsZero (of (R ⧸ span {x}) (E ⧸ span {x} • (⊤ : Submodule R E))) := by
  have : Subsingleton (E ⧸ span {x} • (⊤ : Submodule R E)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.ideal_span_singleton_smul, eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := surjective_smul_of_injective hx E y
    exact Submodule.smul_mem_pointwise_smul z x ⊤ trivial
  exact ModuleCat.isZero_of_subsingleton _

omit [Small.{v} R] in
/-- The `R ⧸ (x)`-linear map on `x`-torsion submodules induced by an `R`-linear map. -/
private noncomputable def mapTorsionBy (x : R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Submodule.torsionBy R M x →ₗ[R ⧸ span {x}] Submodule.torsionBy R N x :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((f ∘ₗ (Submodule.torsionBy R M x).subtype).codRestrict (Submodule.torsionBy R N x) fun y ↦ by
      rw [Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.coe_subtype, ← f.map_smul,
        Submodule.smul_coe_torsionBy, map_zero])

omit [Small.{v} R] in
@[simp]
private theorem coe_mapTorsionBy_apply (x : R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (y : Submodule.torsionBy R M x) :
    (mapTorsionBy x f y : N) = f y :=
  rfl

omit [Small.{v} R] in
/-- Along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` in which multiplication by `x` is
surjective on `X₁`, the `x`-torsion submodules form a short exact sequence over `R ⧸ (x)`. -/
private theorem exists_torsionBy_shortExact {x : R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (hX₁ : Function.Surjective (fun y : S.X₁ ↦ x • y)) :
    ∃ T : ShortComplex (ModuleCat.{v} (R ⧸ span {x})),
      T.ShortExact ∧
      T.X₁ = of (R ⧸ span {x}) (Submodule.torsionBy R S.X₁ x) ∧
      T.X₂ = of (R ⧸ span {x}) (Submodule.torsionBy R S.X₂ x) ∧
      T.X₃ = of (R ⧸ span {x}) (Submodule.torsionBy R S.X₃ x) := by
  have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  let fK := mapTorsionBy x S.f.hom
  let gK := mapTorsionBy x S.g.hom
  have hfg0 : gK ∘ₗ fK = 0 := LinearMap.ext fun y ↦ Subtype.ext (hSex.apply_apply_eq_zero y.1)
  have hfK_inj : Function.Injective fK := fun a b hab ↦
    Subtype.ext (hf_inj (congrArg Subtype.val hab))
  have hgK_surj : Function.Surjective gK := fun z ↦ by
    obtain ⟨y, hy⟩ := hg_surj z.1
    obtain ⟨c, hc⟩ := (hSex (x • y)).mp ((S.g.hom.map_smul x y).trans
      ((congrArg (x • ·) hy).trans (Submodule.smul_coe_torsionBy x z)))
    obtain ⟨c₀, rfl⟩ := hX₁ c
    refine ⟨⟨y - S.f.hom c₀, ?_⟩, Subtype.ext ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, ← S.f.hom.map_smul, hc, sub_self]
    · simp [gK, hy, hSex.apply_apply_eq_zero c₀]
  have hexK : Function.Exact fK gK := fun y ↦ ⟨fun hy ↦ by
    obtain ⟨c, hc⟩ := (hSex y.1).mp (congrArg Subtype.val hy)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    rw [Submodule.mem_torsionBy_iff]
    exact hf_inj (by rw [S.f.hom.map_smul, hc, Submodule.smul_coe_torsionBy, map_zero]),
    by rintro ⟨a, rfl⟩; exact LinearMap.congr_fun hfg0 a⟩
  exact ⟨shortComplexOfCompEqZero fK gK hfg0,
    shortComplex_shortExact _ hexK hfK_inj hgK_surj, rfl, rfl, rfl⟩

/-- If `x` is a nonzerodivisor of `R` and multiplication by `x` is surjective on an `R`-module `C`
of injective dimension at most `n`, then the `x`-torsion submodule of `C` has injective dimension at
most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_torsionBy_of_surjective_smul {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (C : ModuleCat.{v} R) (hC : Function.Surjective (fun y : C ↦ x • y))
    [HasInjectiveDimensionLE C n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (Submodule.torsionBy R C x)) n := by
  induction n generalizing C with
  | zero =>
    have : Injective C := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have := injective_torsionBy_of_injective x C
    exact injective_iff_hasInjectiveDimensionLT_one.mp this
  | succ n ih =>
    let S : ShortComplex (ModuleCat.{v} R) :=
      ShortComplex.mk (Injective.ι C) (Limits.cokernel.π (Injective.ι C))
        (Limits.cokernel.condition _)
    have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι C)
    have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under C))
    have hC'_surj : Function.Surjective (fun z : S.X₃ ↦ x • z) := fun z ↦ by
      obtain ⟨y, rfl⟩ := hg_surj z
      obtain ⟨y₀, hy₀⟩ := surjective_smul_of_injective hx S.X₂ y
      exact ⟨S.g.hom y₀, (S.g.hom.map_smul x y₀).symm.trans (congrArg S.g.hom hy₀)⟩
    have : HasInjectiveDimensionLE S.X₃ n :=
      hS.hasInjectiveDimensionLT_X₃ (n + 1)
        (hasInjectiveDimensionLT_of_ge S.X₂ 1 (n + 1) (by omega)) ‹_›
    have := ih S.X₃ hC'_surj
    have := injective_torsionBy_of_injective x S.X₂
    obtain ⟨T, hT, hX₁, hX₂, hX₃⟩ := exists_torsionBy_shortExact hS hC
    rw [← hX₁]
    have : HasInjectiveDimensionLE T.X₃ n := hX₃ ▸ ‹_›
    have : Injective T.X₂ := hX₂ ▸ ‹_›
    exact hT.hasInjectiveDimensionLT_X₁ (n + 1) ‹_›
      (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))

omit [Small.{v} R] in
/-- The snake-lemma connecting homomorphism `torsionBy R S.X₃ x →ₗ[R ⧸ (x)] S.X₁ ⧸ (x) S.X₁`
associated to a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of `R`-modules. -/
private theorem exists_connectingHom {x : R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) :
    ∃ δ : Submodule.torsionBy R S.X₃ x →ₗ[R ⧸ span {x}]
        S.X₁ ⧸ span {x} • (⊤ : Submodule R S.X₁),
      ∀ (y : S.X₂) (hy : S.g.hom y ∈ Submodule.torsionBy R S.X₃ x) (m : S.X₁),
        S.f.hom m = x • y → δ ⟨S.g.hom y, hy⟩ = Submodule.Quotient.mk m := by
  have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  let P : Submodule R S.X₂ := (Submodule.torsionBy R S.X₃ x).comap S.g.hom
  let eM : S.X₁ ≃ₗ[R] LinearMap.range S.f.hom := LinearEquiv.ofInjective S.f.hom hf_inj
  let mulX : P →ₗ[R] LinearMap.range S.f.hom :=
    (LinearMap.lsmul R S.X₂ x ∘ₗ P.subtype).codRestrict (LinearMap.range S.f.hom) fun y ↦
      (hSex (x • y.1)).mp ((S.g.hom.map_smul x y.1).trans y.2)
  let qP : P →ₗ[R] Submodule.torsionBy R S.X₃ x :=
    (S.g.hom ∘ₗ P.subtype).codRestrict (Submodule.torsionBy R S.X₃ x) fun y ↦ y.2
  have hqP_surj : Function.Surjective qP := fun z ↦ by
    obtain ⟨y, hy⟩ := hg_surj z.1
    exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact z.2⟩, Subtype.ext hy⟩
  let toQuot : P →ₗ[R] S.X₁ ⧸ span {x} • (⊤ : Submodule R S.X₁) :=
    (span {x} • (⊤ : Submodule R S.X₁)).mkQ ∘ₗ eM.symm.toLinearMap ∘ₗ mulX
  have hker : LinearMap.ker qP ≤ LinearMap.ker toQuot := fun y hy ↦ by
    obtain ⟨m, hm⟩ := (hSex y.1).mp (congrArg Subtype.val hy)
    have hmul : eM.symm (mulX y) = x • m := eM.injective <| Subtype.ext <| by
      rw [eM.apply_symm_apply, map_smul, SetLike.val_smul, LinearEquiv.ofInjective_apply, hm]
      rfl
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, hmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul m x ⊤ trivial
  let δR : Submodule.torsionBy R S.X₃ x →ₗ[R] S.X₁ ⧸ span {x} • (⊤ : Submodule R S.X₁) :=
    (LinearMap.ker qP).liftQ toQuot hker ∘ₗ
      (qP.quotKerEquivOfSurjective hqP_surj).symm.toLinearMap
  refine ⟨LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective δR,
    fun y hy m hm ↦ ?_⟩
  let yP : P := ⟨y, hy⟩
  have hsymm : (qP.quotKerEquivOfSurjective hqP_surj).symm (qP yP) =
      Submodule.Quotient.mk yP :=
    (qP.quotKerEquivOfSurjective hqP_surj).injective
      ((qP.quotKerEquivOfSurjective hqP_surj).apply_symm_apply (qP yP))
  have hqPy : (⟨S.g.hom y, hy⟩ : Submodule.torsionBy R S.X₃ x) = qP yP := rfl
  rw [LinearMap.extendScalarsOfSurjective_apply, hqPy, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, hsymm, Submodule.liftQ_apply]
  dsimp only [toQuot, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.mkQ_apply]
  congr 1
  exact eM.injective <| Subtype.ext <| by
    rw [eM.apply_symm_apply, LinearEquiv.ofInjective_apply, hm]
    rfl

omit [Small.{v} R] in
/-- For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` with `x` regular on `S.X₁` and
multiplication by `x` surjective on `S.X₂`, the connecting homomorphism fits into a short exact
sequence `0 → torsionBy S.X₂ → torsionBy S.X₃ → S.X₁ ⧸ (x) S.X₁ → 0` over `R ⧸ (x)`. -/
private theorem exists_connectingShortExact {x : R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (hX₁ : IsSMulRegular S.X₁ x)
    (hX₂ : Function.Surjective (fun y : S.X₂ ↦ x • y)) :
    ∃ T : ShortComplex (ModuleCat.{v} (R ⧸ span {x})),
      T.ShortExact ∧
      T.X₁ = of (R ⧸ span {x}) (Submodule.torsionBy R S.X₂ x) ∧
      T.X₂ = of (R ⧸ span {x}) (Submodule.torsionBy R S.X₃ x) ∧
      T.X₃ = of (R ⧸ span {x}) (S.X₁ ⧸ span {x} • (⊤ : Submodule R S.X₁)) := by
  have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  obtain ⟨δ, hδ⟩ := exists_connectingHom (x := x) hS
  let gK := mapTorsionBy x S.g.hom
  have hgK_inj : Function.Injective gK := fun a b hab ↦ Subtype.ext <| by
    obtain ⟨m, hm⟩ := (hSex (a.1 - b.1)).mp (by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val hab)
    have hxm : x • m = 0 := hf_inj (by
      rw [S.f.hom.map_smul, hm, smul_sub, Submodule.smul_coe_torsionBy,
        Submodule.smul_coe_torsionBy, sub_self, map_zero])
    exact sub_eq_zero.mp (hm.symm.trans (by rw [hX₁ (hxm.trans (smul_zero x).symm), map_zero]))
  have hcomp0 : δ ∘ₗ gK = 0 := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hgy : gK y = ⟨S.g.hom y.1, (gK y).2⟩ := rfl
    rw [hgy]
    exact (hδ y.1 (gK y).2 0 (by rw [map_zero, Submodule.smul_coe_torsionBy])).trans
      (Submodule.Quotient.mk_zero _)
  have hδ_surj : Function.Surjective δ := fun q ↦ by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, hy⟩ := hX₂ (S.f.hom m)
    have hxy : x • y = S.f.hom m := hy
    have hy' : S.g.hom y ∈ Submodule.torsionBy R S.X₃ x := by
      rw [Submodule.mem_torsionBy_iff, ← S.g.hom.map_smul, hxy]
      exact hSex.apply_apply_eq_zero m
    exact ⟨⟨S.g.hom y, hy'⟩, hδ y hy' m hxy.symm⟩
  have hex : Function.Exact gK δ := fun c ↦ ⟨fun hc ↦ by
    obtain ⟨y, hy⟩ := hg_surj c.1
    have hy' : S.g.hom y ∈ Submodule.torsionBy R S.X₃ x := hy.symm ▸ c.2
    obtain ⟨m, hm⟩ := (hSex (x • y)).mp ((S.g.hom.map_smul x y).trans hy')
    have hc_eq : (⟨S.g.hom y, hy'⟩ : Submodule.torsionBy R S.X₃ x) = c := Subtype.ext hy
    have hmk : (Submodule.Quotient.mk m : S.X₁ ⧸ span {x} • (⊤ : Submodule R S.X₁)) = 0 := by
      rw [← hδ y hy' m hm, hc_eq]
      exact hc
    rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hmk
    obtain ⟨m₀, -, rfl⟩ := hmk
    refine ⟨⟨y - S.f.hom m₀, ?_⟩, Subtype.ext ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, ← hm, S.f.hom.map_smul, sub_self]
    · simp [gK, hy, hSex.apply_apply_eq_zero m₀],
    by rintro ⟨a, rfl⟩; exact LinearMap.congr_fun hcomp0 a⟩
  exact ⟨shortComplexOfCompEqZero gK δ hcomp0,
    shortComplex_shortExact _ hex hgK_inj hδ_surj, rfl, rfl, rfl⟩

/-- **Rees's change-of-rings bound for injective dimension.** If `x` is a nonzerodivisor of `R`
which is regular on an `R`-module `M` of injective dimension at most `n + 1`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top_of_succ {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    [HasInjectiveDimensionLE M (n + 1)] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (Injective.ι M) (Limits.cokernel.π (Injective.ι M))
      (Limits.cokernel.condition _)
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι M)
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
  have hC_surj : Function.Surjective (fun z : S.X₃ ↦ x • z) := fun z ↦ by
    obtain ⟨y, rfl⟩ := hg_surj z
    obtain ⟨y₀, hy₀⟩ := surjective_smul_of_injective hx S.X₂ y
    exact ⟨S.g.hom y₀, (S.g.hom.map_smul x y₀).symm.trans (congrArg S.g.hom hy₀)⟩
  have : HasInjectiveDimensionLE S.X₃ n :=
    hS.hasInjectiveDimensionLT_X₃ (n + 1)
      (hasInjectiveDimensionLT_of_ge S.X₂ 1 (n + 1) (by omega)) ‹_›
  have := hasInjectiveDimensionLE_torsionBy_of_surjective_smul hx n S.X₃ hC_surj
  have := injective_torsionBy_of_injective x S.X₂
  obtain ⟨T, hT, hX₁, hX₂, hX₃⟩ :=
    exists_connectingShortExact hS hM (surjective_smul_of_injective hx S.X₂)
  have : HasInjectiveDimensionLE T.X₂ n := hX₂ ▸ ‹_›
  have : Injective T.X₁ := hX₁ ▸ ‹_›
  exact hX₃ ▸ hT.hasInjectiveDimensionLT_X₃ (n + 1) ‹_›
    (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))

/-- **Change of rings for injective dimension, by reduction.** If `x` is a nonzerodivisor of `R`
which is regular on an `R`-module `M` of injective dimension at most `n`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  rcases n with _ | n
  · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have := (isZero_quotient_smul_top_of_injective hx M).hasInjectiveDimensionLT_zero
    exact hasInjectiveDimensionLT_of_ge _ 0 1 (by omega)
  · have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM
    exact hasInjectiveDimensionLT_of_ge _ (n + 1) (n + 2) (by omega)

/-- **Rees's inequality for injective dimension.** For a nonzerodivisor `x` of `R` that is regular
on `M`, reducing `M` modulo `x` satisfies
`injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M`. -/
theorem injectiveDimension_quotient_smul_top_add_one_le {x : R} (hx : x ∈ nonZeroDivisors R)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) :
    injectiveDimension (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) + 1 ≤
      injectiveDimension M := by
  induction hd : injectiveDimension M using WithBot.recBotCoe with
  | bot =>
    have := (hasInjectiveDimensionLT_zero_iff_isZero M).mpr
      ((injectiveDimension_eq_bot_iff M).mp hd)
    have : Injective M :=
      injective_iff_hasInjectiveDimensionLT_one.mpr
        (hasInjectiveDimensionLT_of_ge M 0 1 (by omega))
    rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
    exact bot_le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      have : HasInjectiveDimensionLE M n := (injectiveDimension_le_iff M n).mp hd.le
      rcases n with _ | n
      · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
        rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
        exact bot_le
      · have hQ := (injectiveDimension_le_iff _ n).mpr
          (hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM)
        exact (add_le_add_left hQ 1).trans_eq (by norm_cast)

omit [CommRing R] [Small.{v} R] in
/-- The quotient `S ⧸ (x) • ⊤` of `S` by `(x) • ⊤` is `S ⧸ (x)` as an `S ⧸ (x)`-module. -/
private noncomputable def quotientSMulTopSelfIso {S : Type u} [CommRing S] (x : S) :
    of (S ⧸ span {x}) (S ⧸ span {x} • (⊤ : Submodule S S)) ≅
      of (S ⧸ span {x}) (S ⧸ span {x}) :=
  LinearEquiv.toModuleIso (R := S ⧸ span {x})
    { __ := Submodule.quotEquivOfEq _ _ (by ext a; simp [Ideal.mem_span_singleton])
      map_smul' := fun s m ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rfl }

omit [CommRing R] [Small.{v} R] in
/-- If `x` is a nonzerodivisor of `S` and the regular module `S` has injective dimension at most
`n + 1`, then the regular module of `S ⧸ (x)` has injective dimension at most `n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton_of_succ {S : Type u} [CommRing S]
    {x : S} (hx : x ∈ nonZeroDivisors S) (n : ℕ)
    [HasInjectiveDimensionLE (of S S) (n + 1)] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n (of S S)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  exact hasInjectiveDimensionLT_of_iso (quotientSMulTopSelfIso x) (n + 1)

omit [CommRing R] [Small.{v} R] in
/-- If `x` is a nonzerodivisor of `S` and the regular module `S` has injective dimension at most
`n`, then the regular module of `S ⧸ (x)` has injective dimension at most `n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton {S : Type u} [CommRing S]
    {x : S} (hx : x ∈ nonZeroDivisors S) (n : ℕ)
    [HasInjectiveDimensionLE (of S S) n] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  rcases n with _ | n
  · have : Injective (of S S) := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have hZ := (isZero_quotient_smul_top_of_injective hx (of S S)).of_iso
      (quotientSMulTopSelfIso x).symm
    have := hZ.hasInjectiveDimensionLT_zero
    exact hasInjectiveDimensionLT_of_ge _ 0 1 (by omega)
  · have := hasInjectiveDimensionLE_quotient_span_singleton_of_succ hx n
    exact hasInjectiveDimensionLT_of_ge _ (n + 1) (n + 2) (by omega)

end ModuleCat
