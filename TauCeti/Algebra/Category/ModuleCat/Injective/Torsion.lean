/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.Algebra.Module.Injective.Hom

/-!
# Torsion and divisibility of injective modules

For an ideal `I` of a commutative ring `R` and an injective object `E` of `ModuleCat R`,
`Submodule.torsionBySet R E I` is injective in `ModuleCat (R ⧸ I)`
(`ModuleCat.injective_torsionBySet_of_injective`, `ModuleCat.injective_torsionBy_of_injective`).
When `R` is small relative to the module universe, `E` is divisible by every `x ∈ nonZeroDivisors R`
(`ModuleCat.surjective_smul_of_injective`), so `E ⧸ (x) • ⊤` vanishes
(`ModuleCat.isZero_quotient_smul_top_of_injective`).

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
injective `R ⧸ I`-module. -/
theorem injective_torsionBySet_of_injective (I : Ideal R) (E : ModuleCat.{v} R) [Injective E] :
    Injective (of (R ⧸ I) (Submodule.torsionBySet R E I)) where
  factors {Y₁ Y₂} f g _ := by
    let F := restrictScalars.{v} (algebraMap R (R ⧸ I))
    have : F.Full := (algebraMap R (R ⧸ I)).full_restrictScalars Quotient.mk_surjective
    let e := restrictScalarsAlgebraMapIso (R := R) (S := R ⧸ I) (Submodule.torsionBySet R E I)
    let sub : of R (Submodule.torsionBySet R E I) ⟶ E :=
      ofHom (Submodule.torsionBySet R E I).subtype
    have : Mono sub := (mono_iff_injective sub).mpr (Submodule.torsionBySet R E I).injective_subtype
    let ι : F.obj (of (R ⧸ I) (Submodule.torsionBySet R E I)) ⟶ E := e.hom ≫ sub
    let ψ : F.obj Y₂ ⟶ E := Injective.factorThru (F.map f ≫ ι) (F.map g)
    have hψ (y : F.obj Y₂) : ψ y ∈ Submodule.torsionBySet R E I := by
      rw [Submodule.mem_torsionBySet_iff]; rintro ⟨r, hr⟩
      have hy : r • y = 0 := by
        rw [restrictScalars.smul_def, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem.mpr hr,
          zero_smul]; rfl
      exact (ψ.hom.map_smul r y).symm.trans (by rw [hy, map_zero])
    let ψR : F.obj Y₂ ⟶ F.obj (of (R ⧸ I) (Submodule.torsionBySet R E I)) :=
      ConcreteCategory.ofHom (ψ.hom.codRestrict (Submodule.torsionBySet R E I) hψ) ≫ e.inv
    have hψR : ψR ≫ ι = ψ := by
      dsimp only [ψR, ι]; rw [Category.assoc, Iso.inv_hom_id_assoc]
      exact hom_ext (LinearMap.ext fun _ ↦ rfl)
    refine ⟨F.preimage ψR, F.map_injective ?_⟩
    rw [F.map_comp, F.map_preimage, ← cancel_mono ι, Category.assoc, hψR, Injective.comp_factorThru]

/-- For `x : R` and an injective `R`-module `E`, `Submodule.torsionBy R E x` is injective over
`R ⧸ (x)`. -/
theorem injective_torsionBy_of_injective (x : R) (E : ModuleCat.{v} R) [Injective E] :
    Injective (of (R ⧸ span {x}) (Submodule.torsionBy R E x)) :=
  Injective.of_iso (((LinearEquiv.ofEq _ _
    (Submodule.torsionBySet_ideal_span_singleton_eq x)).extendScalarsOfSurjective
    Quotient.mk_surjective).toModuleIso) (injective_torsionBySet_of_injective (span {x}) E)

variable [Small.{v} R]

/-- An injective `R`-module is divisible by every nonzerodivisor `x` of `R`. -/
theorem surjective_smul_of_injective {x : R} (hx : x ∈ nonZeroDivisors R)
    (E : ModuleCat.{v} R) [Injective E] : Function.Surjective (fun y : E ↦ x • y) := fun y ↦ by
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  obtain ⟨f, hf⟩ := (TauCeti.exists_linearMap_apply_eq_iff_forall_smul_eq_zero
    (S := R) (M := R) (Q := E) (a := x) (x := y)).mpr fun s hs ↦ by
      rw [smul_eq_mul] at hs; rw [mem_nonZeroDivisors_iff_right.mp hx s hs, zero_smul]
  exact ⟨f 1, by dsimp only; rw [← f.map_smul, smul_eq_mul, mul_one, hf]⟩

/-- Reducing an injective `R`-module modulo a nonzerodivisor `x` yields the zero module. -/
theorem isZero_quotient_smul_top_of_injective {x : R} (hx : x ∈ nonZeroDivisors R)
    (E : ModuleCat.{v} R) [Injective E] :
    Limits.IsZero (of (R ⧸ span {x}) (E ⧸ span {x} • (⊤ : Submodule R E))) := by
  have : Subsingleton (E ⧸ span {x} • (⊤ : Submodule R E)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.ideal_span_singleton_smul, eq_top_iff]
    intro y _; obtain ⟨z, rfl⟩ := surjective_smul_of_injective hx E y
    exact Submodule.smul_mem_pointwise_smul z x ⊤ trivial
  exact isZero_of_subsingleton _

end ModuleCat
