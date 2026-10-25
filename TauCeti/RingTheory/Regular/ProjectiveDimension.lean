/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Regular.Category
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.Algebra.Module.Projective.Quotient
import TauCeti.RingTheory.QuotSMulTop

/-!
# Projective dimension along the quotient by a nonzerodivisor

Let `x` be a nonzerodivisor of a commutative ring `R`. A module `L` over `R ⧸ (x)` is also an
`R`-module, and its projective dimension grows by at most one:

```text
pd_R L ≤ pd_{R ⧸ (x)} L + 1.
```

In the other direction, reducing an `R`-module `M` on which `x` is regular does not increase the
projective dimension:

```text
pd_{R ⧸ (x)} (M ⧸ x M) ≤ pd_R M.
```

A projective `R ⧸ (x)`-module is a retract of `G ⧸ x G` for a projective `R`-module `G`, and
`0 → G → G → G ⧸ x G → 0`, the first map being multiplication by `x`, shows that `G ⧸ x G` has
projective dimension at most one over `R`. Dimension shifting along a projective presentation over
`R ⧸ (x)` then gives the bound in general, because restriction of scalars is exact.

This is the change-of-rings step in the induction proving that every module over a regular local
ring of dimension `d` has projective dimension at most `d`: there `x` is a parameter and
`R ⧸ (x)` is regular of dimension `d - 1`.

For the reduction, a projective presentation `0 → K → P → M → 0` stays short exact modulo `x`,
because `x` is regular on `M`; the reduction of the projective module `P` is projective over
`R ⧸ (x)`, and `x` is again regular on `K ⊆ P`, so induction on the projective dimension applies.
This is the change-of-rings step in Serre's theorem that a Noetherian local ring whose residue
field has finite projective dimension is regular.

## Main results

* `ModuleCat.hasProjectiveDimensionLT_restrictScalars_of_projective`: a projective
  `R ⧸ (x)`-module has projective dimension at most one over `R`.
* `ModuleCat.hasProjectiveDimensionLE_restrictScalars_quotient`: if an `R ⧸ (x)`-module has
  projective dimension at most `n`, then it has projective dimension at most `n + 1` over `R`.
* `ModuleCat.hasProjectiveDimensionLE_of_isScalarTower_quotient`: the same bound for an
  `R`-module carrying a compatible `R ⧸ (x)`-module structure.
* `ModuleCat.hasProjectiveDimensionLE_quotient_smul_top`: if `x` is regular on an `R`-module `M`
  of projective dimension at most `n`, then `M ⧸ x M` has projective dimension at most `n` over
  `R ⧸ (x)`.

No finiteness or locality is assumed: the bounds hold for all modules.

## References

* H. Matsumura, *Commutative Ring Theory*, Section 19, the lemmas preceding Theorem 19.2.
-/

public section

universe v u

open CategoryTheory Ideal Pointwise

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R] {x : R}

/-- A projective module over `R ⧸ (x)`, for a nonzerodivisor `x`, has projective dimension at
most one over `R`. -/
theorem hasProjectiveDimensionLT_restrictScalars_of_projective (hx : x ∈ nonZeroDivisors R)
    (P : ModuleCat.{v} (R ⧸ span {x})) [Projective P] :
    HasProjectiveDimensionLT ((restrictScalars.{v} (Ideal.Quotient.mk (span {x}))).obj P) 2 := by
  let I := span {x}
  let F := restrictScalars.{v} (Ideal.Quotient.mk I)
  -- A projective `R`-module `G` surjecting onto `P`, and the quotient `Q = G ⧸ x G`.
  let G := Projective.over (F.obj P)
  let p : G ⟶ F.obj P := Projective.π (F.obj P)
  have hp : Function.Surjective p := (ModuleCat.epi_iff_surjective p).mp inferInstance
  have : Module.Projective R G := G.projective_of_module_projective
  -- `p` kills `I • ⊤`, so it factors through the `R ⧸ I`-module `Q`.
  have hker : I • (⊤ : Submodule R G) ≤ LinearMap.ker p.hom := by
    rw [Submodule.smul_le]
    intro r hr g _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [LinearMap.mem_ker, map_smul, restrictScalars.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x))]
    exact zero_smul _ _
  let Q := G ⧸ I • (⊤ : Submodule R G)
  let qR : Q →ₗ[R] F.obj P := Submodule.liftQ (I • (⊤ : Submodule R G)) p.hom hker
  let q : of (R ⧸ I) Q ⟶ P := ofHom
    { toFun := qR
      map_add' := map_add qR
      map_smul' := fun s m ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, map_smul, restrictScalars.smul_def,
          RingHom.id_apply, Ideal.Quotient.algebraMap_eq] }
  have hq : Epi q := by
    refine (ModuleCat.epi_iff_surjective q).mpr fun y ↦ ?_
    obtain ⟨g, hg⟩ := hp y
    refine ⟨Submodule.Quotient.mk g, ?_⟩
    exact (Submodule.liftQ_apply (I • ⊤) p.hom (h := hker) g).trans hg
  -- `P` is a retract of `Q`, so `F.obj P` is a retract of `F.obj Q ≅ G ⧸ x G`.
  let ret : Retract P (of (R ⧸ I) Q) :=
    ⟨Projective.factorThru (𝟙 P) q, q, Projective.factorThru_comp _ _⟩
  -- `G ⧸ x G` has projective dimension at most one over `R`.
  have hreg : IsSMulRegular G x := Module.Flat.isSMulRegular_of_nonZeroDivisors hx
  have hQ : HasProjectiveDimensionLT (F.obj (of (R ⧸ I) Q)) 2 := by
    have : HasProjectiveDimensionLT (of R (G ⧸ x • (⊤ : Submodule R G))) 2 :=
      hreg.smulShortComplex_shortExact.hasProjectiveDimensionLT_X₃ 1
      (inferInstance : HasProjectiveDimensionLT G 1) (inferInstance : HasProjectiveDimensionLT G 2)
    exact hasProjectiveDimensionLT_of_iso
      ((Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm).toModuleIso
        ≪≫ (restrictScalarsAlgebraMapIso (S := R ⧸ I) Q).symm) 2
  exact (ret.map F).hasProjectiveDimensionLT 2

/-- **Change of rings for projective dimension.** If `x` is a nonzerodivisor of `R` and an
`R ⧸ (x)`-module `L` has projective dimension at most `n`, then `L` has projective dimension at
most `n + 1` as an `R`-module. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient (hx : x ∈ nonZeroDivisors R) (n : ℕ)
    (L : ModuleCat.{v} (R ⧸ span {x})) [HasProjectiveDimensionLE L n] :
    HasProjectiveDimensionLE ((restrictScalars.{v} (Ideal.Quotient.mk (span {x}))).obj L)
      (n + 1) := by
  induction n generalizing L with
  | zero =>
    have : Projective L := projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›
    exact hasProjectiveDimensionLT_restrictScalars_of_projective hx L
  | succ n ih =>
    -- Dimension shifting along a projective presentation `0 → K → P → L → 0` over `R ⧸ (x)`,
    -- which restriction of scalars carries to a short exact sequence over `R`.
    have hS := L.shortExact_projectiveShortComplex
    have : HasProjectiveDimensionLE L.projectiveShortComplex.X₁ n :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance ‹_›
    have hSR := hS.map_of_exact (restrictScalars.{v} (Ideal.Quotient.mk (span {x})))
    have : HasProjectiveDimensionLT
        (L.projectiveShortComplex.map (restrictScalars.{v} (Ideal.Quotient.mk (span {x})))).X₂ 2 :=
      hasProjectiveDimensionLT_restrictScalars_of_projective hx L.projectiveShortComplex.X₂
    exact hSR.hasProjectiveDimensionLT_X₃ (n + 2) (ih _)
      (hasProjectiveDimensionLT_of_ge _ 2 (n + 3) (by omega))

/-- **Change of rings for projective dimension**, for an `R`-module with a compatible
`R ⧸ (x)`-module structure: if its projective dimension over `R ⧸ (x)` is at most `n`, then its
projective dimension over `R` is at most `n + 1`. -/
theorem hasProjectiveDimensionLE_of_isScalarTower_quotient (hx : x ∈ nonZeroDivisors R) (n : ℕ)
    (L : Type v) [AddCommGroup L] [Module R L] [Module (R ⧸ span {x}) L]
    [IsScalarTower R (R ⧸ span {x}) L] [HasProjectiveDimensionLE (of (R ⧸ span {x}) L) n] :
    HasProjectiveDimensionLE (of R L) (n + 1) :=
  have := hasProjectiveDimensionLE_restrictScalars_quotient hx n (of (R ⧸ span {x}) L)
  hasProjectiveDimensionLT_of_iso (restrictScalarsAlgebraMapIso (S := R ⧸ span {x}) L) (n + 2)

/-- **Change of rings for projective dimension, by reduction.** If `x` is a nonzerodivisor of `R`
which is regular on an `R`-module `M` of projective dimension at most `n`, then `M ⧸ x M` has
projective dimension at most `n` over `R ⧸ (x)`. -/
theorem hasProjectiveDimensionLE_quotient_smul_top (hx : x ∈ nonZeroDivisors R) (n : ℕ)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›
    have : Module.Projective R M := M.projective_of_module_projective
    have : Module.Projective (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M)) :=
      .quotient_smul_top _ Ideal.Quotient.mk_surjective (Ideal.mk_ker (I := span {x})).ge
        fun _ _ ↦ rfl
    exact projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
  | succ n ih =>
    -- Reduce a projective presentation `0 → K → P → M → 0` modulo `x`.
    have hS := M.shortExact_projectiveShortComplex
    let S := M.projectiveShortComplex
    have : Module.Projective R S.X₂ := S.X₂.projective_of_module_projective
    have : Module.Projective (R ⧸ span {x}) (S.X₂ ⧸ span {x} • (⊤ : Submodule R S.X₂)) :=
      .quotient_smul_top _ Ideal.Quotient.mk_surjective (Ideal.mk_ker (I := span {x})).ge
        fun _ _ ↦ rfl
    have hK : IsSMulRegular S.X₁ x :=
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hx).of_injective S.f.hom hS.injective_f
    have : HasProjectiveDimensionLE S.X₁ n :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance ‹_›
    have := ih S.X₁ hK
    have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    have hex := (span {x}).mapQSMulTop_exact hSex hS.surjective_g
    have hT := shortComplex_shortExact
      (shortComplexOfCompEqZero ((span {x}).mapQSMulTop S.f.hom) ((span {x}).mapQSMulTop S.g.hom)
        (LinearMap.ext fun k ↦ hex.apply_apply_eq_zero k)) hex
      (mapQSMulTop_span_singleton_injective hSex hS.injective_f hM)
      ((span {x}).mapQSMulTop_surjective hS.surjective_g)
    exact hT.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance
      (hasProjectiveDimensionLT_of_ge _ 1 _ (by omega))

end ModuleCat
