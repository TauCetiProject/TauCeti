/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels

/-!
# Uniqueness of fpqc descent for module morphisms

Morphisms into a quasi-coherent module are determined by their pullbacks along an fpqc
covering family, on arbitrary schemes. The source module need not be quasi-coherent.
Isomorphisms of quasi-coherent modules can also be detected on such a family.

The argument uses `Scheme.Modules.isSheaf_bigPresheaf_comp_forget_fpqcTopology`: sections of the
target module on the big site form an fpqc sheaf. Equality of sections can therefore be checked
on a covering sieve, including after pulling that sieve back to any open subscheme.

## References

* The Stacks Project, Proposition 35.5.2 (023T), descent of quasi-coherent modules.
* The Stacks Project, Lemma 35.8.1 (023M), fpqc descent of sections.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- Morphisms into a quasi-coherent module are equal if their pullbacks along an fpqc
covering family are equal. No quasi-coherence assumption on the source is required. -/
theorem Hom.ext_of_fpqc {S : Scheme.{u}} {M N : S.Modules} [N.IsQuasicoherent]
    (φ ψ : M ⟶ N) {ι : Type v} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Sieve.ofArrows X f ∈ Scheme.fpqcTopology S)
    (h : ∀ i, (pullback (f i)).map φ = (pullback (f i)).map ψ) : φ = ψ := by
  have hR {T : Scheme.{u}} (g : T ⟶ S) (hg : Sieve.ofArrows X f g) :
      (pullback g).map φ = (pullback g).map ψ := by
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff X f g).1 hg
    let e := pullbackComp a (f i)
    apply (cancel_epi (e.hom.app M)).1
    rw [← e.hom.naturality φ, ← e.hom.naturality ψ]
    exact congrArg (fun k ↦ (pullback a).map k ≫ e.hom.app N) (h i)
  apply hom_ext _ _
  intro U
  ext s
  apply (bijective_pullbackSectionsLE_ι N U ⊤ rfl).injective
  rw [← Scheme.Hom.pullbackSectionsLE_naturality,
    ← Scheme.Hom.pullbackSectionsLE_naturality]
  let T : Over S := Over.mk U.ι
  let R : Sieve T := (Sieve.overEquiv T).symm ((Sieve.ofArrows X f).pullback U.ι)
  have hR' : R ∈ (fpqcTopology.over S) T :=
    fpqcTopology.overEquiv_symm_mem_over T _ (fpqcTopology.pullback_stable U.ι hf)
  apply (isSheaf_bigPresheaf_comp_forget_fpqcTopology N _ hR').isSeparatedFor.ext
  intro V g hg
  rw [Sieve.overEquiv_symm_iff, Sieve.pullback_apply] at hg
  have hg' : Sieve.ofArrows X f V.hom := (Over.w g) ▸ hg
  -- Here `T.hom` is `U.ι` by `Over.mk_hom`, so `t` is a global section of `T.hom^* M`.
  let t := U.ι.pullbackSectionsLE M U ⊤ (by simp) s
  exact (bigPresheaf_presheaf_comp_forget_map_apply N g _).trans <|
    (bigSectionsRestrict_naturality φ g t).trans <|
    (congrArg (fun k : (pullback V.hom).obj M ⟶ (pullback V.hom).obj N ↦
      k.app ⊤ (bigSectionsRestrict M g t)) (hR V.hom hg')).trans <|
    (bigSectionsRestrict_naturality ψ g t).symm.trans
      (bigPresheaf_presheaf_comp_forget_map_apply N g _).symm

/-- A morphism of quasi-coherent modules is an isomorphism if it becomes an isomorphism
on every member of an fpqc covering family. The schemes need not be affine. -/
theorem Hom.isIso_of_fpqc {S : Scheme.{u}} {M N : S.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    {ι : Type v} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Sieve.ofArrows X f ∈ Scheme.fpqcTopology S)
    (h : ∀ i, IsIso ((pullback (f i)).map φ)) : IsIso φ := by
  have : Mono φ := Abelian.mono_of_kernel_ι_eq_zero φ
    (Hom.ext_of_fpqc (Limits.kernel.ι φ) 0 f hf fun i ↦ by
      have := h i
      rw [Functor.map_zero, ← cancel_mono ((pullback (f i)).map φ)]
      simp [← Functor.map_comp])
  have : (Limits.cokernel φ).IsQuasicoherent := isQuasicoherent_cokernel φ
  have : Epi φ := Abelian.epi_of_cokernel_π_eq_zero φ
    (Hom.ext_of_fpqc (Limits.cokernel.π φ) 0 f hf fun i ↦ by
      have := h i
      rw [Functor.map_zero, ← cancel_epi ((pullback (f i)).map φ)]
      simp [← Functor.map_comp])
  exact isIso_of_mono_of_epi φ

end AlgebraicGeometry.Scheme.Modules
