/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.RingTheory.Flat.CategoryTheory
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension under `Tor`-acyclic base change and homological epimorphisms

Let `f : P →+* R` be a homomorphism of commutative rings.

If a `P`-module `N` is `Tor`-acyclic with respect to `R`, meaning `Torᵢ^P(N, R) = 0` for all
`i > 0`, then extension of scalars along `f` does not increase its projective dimension:
`pd_R (R ⊗[P] N) ≤ pd_P N` (`ModuleCat.projectiveDimension_extendScalars_le`). Indeed `R ⊗[P] -`
preserves projectives as a left adjoint of the exact functor `restrictScalars f`, and for a
projective presentation `0 → K → Q → N → 0` the vanishing of `Tor₁^P(N, R)` keeps
`0 → R ⊗[P] K → R ⊗[P] Q → R ⊗[P] N → 0` exact while dimension shifting makes `K` again
`Tor`-acyclic with respect to `R`.

When `f` is a homological epimorphism—that is, `restrictScalars f` is full (for instance when `f`
is surjective, `RingHom.full_restrictScalars`) and `Torᵢ^P(R, R) = 0` for all `i > 0`—every
`R`-module `M` satisfies `Torᵢ^P(M, R) = 0` for all `i > 0`
(`ModuleCat.isZero_Tor_restrictScalars`), by induction on `i` using a free `R`-module presentation
of `M` and the counit isomorphism `R ⊗[P] M ≅ M`. Combining the two results yields
`pd_R M ≤ pd_P M` (`ModuleCat.projectiveDimension_le_restrictScalars`).

## Main results

* `ModuleCat.hasProjectiveDimensionLT_extendScalars`: for a `P`-module `N` with
  `Tor_{i+1}^P(N, R) = 0` for all `i`, extension of scalars along `f : P →+* R` preserves
  `HasProjectiveDimensionLT _ n`.
* `ModuleCat.projectiveDimension_extendScalars_le`: `pd_R (R ⊗[P] N) ≤ pd_P N` under the same
  `Tor`-vanishing hypothesis.
* `ModuleCat.isZero_Tor_restrictScalars`: if `restrictScalars f` is full and
  `Tor_{i+1}^P(R, R) = 0` for all `i`, then `Tor_{i+1}^P(M, R) = 0` for every `R`-module `M`.
* `ModuleCat.hasProjectiveDimensionLT_of_restrictScalars` and
  `ModuleCat.projectiveDimension_le_restrictScalars`: under the same hypotheses, `pd_R M ≤ pd_P M`
  for every `R`-module `M`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), proof of Proposition 11.31.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

universe u

variable {P R : Type u} [CommRing P] [CommRing R] (f : P →+* R)

/-- **Base change preserves projective dimension bounds under `Tor`-acyclicity.** If
`Tor_{i+1}^P(N, R) = 0` for all `i` and `N` has projective dimension less than `n` over `P`, then
`R ⊗[P] N` has projective dimension less than `n` over `R`. -/
theorem hasProjectiveDimensionLT_extendScalars {n : ℕ} (N : ModuleCat.{u} P)
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj N).obj
      ((restrictScalars f).obj (of R R))))
    (hN : HasProjectiveDimensionLT N n) :
    HasProjectiveDimensionLT ((extendScalars f).obj N) n := by
  have : PreservesColimitsOfSize.{0, 0} (extendScalars.{u, u, u} f) :=
    (extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : (extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{u, u, u} f)
  induction n generalizing N with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hN ⊢
    exact (IsZero.iff_id_eq_zero _).2
      (by rw [← (extendScalars f).map_id, hN.eq_of_src (𝟙 N) 0, (extendScalars f).map_zero])
  | succ n ih =>
    cases n with
    | zero =>
      have : Projective N := projective_iff_hasProjectiveDimensionLT_one.mpr hN
      exact projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
    | succ n =>
      let S := ShortComplex.mk (kernel.ι (Projective.π N)) (Projective.π N) (kernel.condition _)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel _))
          inferInstance inferInstance
      have : Module.Projective P S.X₂ := (Projective.over N).projective_of_module_projective
      have : Module.Flat P S.X₂ := Module.Flat.of_projective
      -- The kernel `S.X₁` is again `Tor`-acyclic with respect to `R` and has smaller projective
      -- dimension.
      have hTorK : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj S.X₁).obj
          ((restrictScalars f).obj (of R R))) := fun i ↦
        hS.isZero_Tor_X₁ _ (ModuleCat.isZero_Tor_succ_of_flat S.X₂ _ i) (hTor (i + 1))
      have hK' : HasProjectiveDimensionLT ((extendScalars f).obj S.X₁) (n + 1) :=
        ih S.X₁ hTorK ((hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).1 hN)
      -- Vanishing of `Tor₁^P(N, R)` keeps `R ⊗[P] S.f` a monomorphism, so `R ⊗[P] S` is short
      -- exact.
      have hmono_tensor : Mono (S.f ▷ (restrictScalars f).obj (of R R)) :=
        hS.mono_whiskerRight_of_isZero_Tor_one _ (hTor 0)
      have hmono_res : Mono ((restrictScalars f).map ((extendScalars f).map S.f)) := by
        have hnat : (restrictScalars f).map ((extendScalars f).map S.f) ≫
            (extendRestrictScalarsIsoTensorRight f).hom.app S.X₂ =
            (extendRestrictScalarsIsoTensorRight f).hom.app S.X₁ ≫
              (S.f ▷ (restrictScalars f).obj (of R R)) :=
          (extendRestrictScalarsIsoTensorRight f).hom.naturality S.f
        have hfac : (restrictScalars f).map ((extendScalars f).map S.f) =
            (extendRestrictScalarsIsoTensorRight f).hom.app S.X₁ ≫
              (S.f ▷ (restrictScalars f).obj (of R R)) ≫
              (extendRestrictScalarsIsoTensorRight f).inv.app S.X₂ := by
          rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app]
          exact (Category.comp_id _).symm
        rw [hfac]
        infer_instance
      have hmono : Mono ((extendScalars f).map S.f) :=
        (restrictScalars f).mono_of_mono_map hmono_res
      have hcok := CokernelCofork.mapIsColimit _ hS.gIsCokernel (extendScalars.{u, u, u} f)
      have hS' : (S.map (extendScalars.{u, u, u} f)).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcok) hmono
          (epi_of_isColimit_cofork hcok)
      have hP₂' : Projective (S.map (extendScalars.{u, u, u} f)).X₂ :=
        (inferInstance : Projective ((extendScalars.{u, u, u} f).obj (Projective.over N)))
      exact (hS'.hasProjectiveDimensionLT_X₃_iff n hP₂').2 hK'

/-- **Base change does not increase projective dimension under `Tor`-acyclicity**: if
`Tor_{i+1}^P(N, R) = 0` for all `i`, then `pd_R (R ⊗[P] N) ≤ pd_P N`. -/
theorem projectiveDimension_extendScalars_le (N : ModuleCat.{u} P)
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj N).obj
      ((restrictScalars f).obj (of R R)))) :
    projectiveDimension ((extendScalars f).obj N) ≤ projectiveDimension N :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ ↦
    hasProjectiveDimensionLT_extendScalars f N hTor

/-- A free `R`-module restricts to a direct sum of copies of `R` over `P`, so it inherits the
vanishing of `Tor` against `R`. -/
private theorem isZero_Tor_restrictScalars_finsupp {ι : Type u} {k : ℕ}
    (hTor : IsZero (((Tor (ModuleCat.{u} P) k).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj (of R R)))) :
    IsZero (((Tor (ModuleCat.{u} P) k).obj ((restrictScalars f).obj (of R (ι →₀ R)))).obj
      ((restrictScalars f).obj (of R R))) :=
  let e : (restrictScalars f).obj (of R (ι →₀ R)) ≃ₗ[P] (ι →₀ (restrictScalars f).obj (of R R)) :=
    { toFun := id, invFun := id, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  IsZero.of_iso (isZero_Tor_finsupp _ hTor) (((Tor (ModuleCat.{u} P) k).mapIso e.toModuleIso).app _)

/-- **Modules over a homological epimorphism are `Tor`-acyclic.** If `restrictScalars f` is full
(for instance when `f : P →+* R` is surjective) and `Tor_{i+1}^P(R, R) = 0` for all `i`, then
`Tor_{i+1}^P(M, R) = 0` for every `R`-module `M` and every `i`. -/
theorem isZero_Tor_restrictScalars [(restrictScalars.{u} f).Full]
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj (of R R))))
    (M : ModuleCat.{u} R) (i : ℕ) :
    IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj ((restrictScalars f).obj M)).obj
      ((restrictScalars f).obj (of R R))) := by
  induction i generalizing M with
  | zero =>
    let q : of R (M →₀ R) ⟶ M := ofHom (Finsupp.linearCombination R id)
    have hq : Epi q := (ModuleCat.epi_iff_surjective q).2 fun m ↦ ⟨Finsupp.single m 1, by simp [q]⟩
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel _))
        inferInstance inferInstance
    have hSR : (S.map (restrictScalars.{u} f)).ShortExact := hS.map_of_exact (restrictScalars f)
    -- The counit `R ⊗[P] (-) ≅ id` identifies `S.f ⊗[P] R` with the monomorphism `S.f`.
    have hmono_ext : Mono ((extendScalars f).map ((restrictScalars f).map S.f)) := by
      have hnat : (extendScalars f).map ((restrictScalars f).map S.f) ≫
          (extendRestrictScalarsAdj.{u, u, u} f).counit.app S.X₂ =
          (extendRestrictScalarsAdj.{u, u, u} f).counit.app S.X₁ ≫ S.f :=
        (extendRestrictScalarsAdj.{u, u, u} f).counit.naturality S.f
      have hfac : (extendScalars f).map ((restrictScalars f).map S.f) =
          (extendRestrictScalarsAdj.{u, u, u} f).counit.app S.X₁ ≫ S.f ≫
            inv ((extendRestrictScalarsAdj.{u, u, u} f).counit.app S.X₂) := by
        rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have : Mono S.f := hS.mono_f
      rw [hfac]
      infer_instance
    have hmono_tensor :
        Mono (((restrictScalars f).map S.f) ▷ (restrictScalars f).obj (of R R)) := by
      have hnat : (restrictScalars f).map ((extendScalars f).map ((restrictScalars f).map S.f)) ≫
          (extendRestrictScalarsIsoTensorRight f).hom.app ((restrictScalars f).obj S.X₂) =
          (extendRestrictScalarsIsoTensorRight f).hom.app ((restrictScalars f).obj S.X₁) ≫
            (((restrictScalars f).map S.f) ▷ (restrictScalars f).obj (of R R)) :=
        (extendRestrictScalarsIsoTensorRight f).hom.naturality ((restrictScalars f).map S.f)
      have hfac : ((restrictScalars f).map S.f) ▷ (restrictScalars f).obj (of R R) =
          (extendRestrictScalarsIsoTensorRight f).inv.app ((restrictScalars f).obj S.X₁) ≫
            (restrictScalars f).map ((extendScalars f).map ((restrictScalars f).map S.f)) ≫
            (extendRestrictScalarsIsoTensorRight f).hom.app ((restrictScalars f).obj S.X₂) := by
        rw [hnat, Iso.inv_hom_id_app_assoc]
      rw [hfac]
      infer_instance
    have hinj : Function.Injective
        (((restrictScalars f).map S.f).hom.rTensor ((restrictScalars f).obj (of R R))) := by
      simpa [ModuleCat.hom_whiskerRight] using (ModuleCat.mono_iff_injective _).1 hmono_tensor
    exact hSR.isZero_Tor_one_X₃ _ (isZero_Tor_restrictScalars_finsupp f (hTor 0)) hinj
  | succ i ih =>
    let q : of R (M →₀ R) ⟶ M := ofHom (Finsupp.linearCombination R id)
    have hq : Epi q := (ModuleCat.epi_iff_surjective q).2 fun m ↦ ⟨Finsupp.single m 1, by simp [q]⟩
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel _))
        inferInstance inferInstance
    have hSR : (S.map (restrictScalars.{u} f)).ShortExact := hS.map_of_exact (restrictScalars f)
    exact hSR.isZero_Tor_succ_X₃ _ (isZero_Tor_restrictScalars_finsupp f (hTor (i + 1))) (ih S.X₁)

/-- **Projective dimension transfer along a homological epimorphism.** If `restrictScalars f` is
full (for instance when `f : P →+* R` is surjective) and `Tor_{i+1}^P(R, R) = 0` for all `i`, then
every `R`-module whose restriction to `P` has projective dimension less than `n` also has
projective dimension less than `n` over `R`. -/
theorem hasProjectiveDimensionLT_of_restrictScalars [(restrictScalars.{u} f).Full]
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj (of R R))))
    (M : ModuleCat.{u} R) {n : ℕ}
    (hM : HasProjectiveDimensionLT ((restrictScalars f).obj M) n) :
    HasProjectiveDimensionLT M n :=
  have : HasProjectiveDimensionLT ((restrictScalars.{u} f ⋙ extendScalars.{u, u, u} f).obj M) n :=
    hasProjectiveDimensionLT_extendScalars f ((restrictScalars f).obj M)
      (isZero_Tor_restrictScalars f hTor M) hM
  hasProjectiveDimensionLT_of_iso (asIso ((extendRestrictScalarsAdj.{u, u, u} f).counit.app M)) n

/-- **Projective dimension bound along a homological epimorphism**: if `restrictScalars f` is full
and `Tor_{i+1}^P(R, R) = 0` for all `i`, then `pd_R M ≤ pd_P M` for every `R`-module `M`. -/
theorem projectiveDimension_le_restrictScalars [(restrictScalars.{u} f).Full]
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj (of R R))))
    (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ ↦
    hasProjectiveDimensionLT_of_restrictScalars f hTor M

end ModuleCat
